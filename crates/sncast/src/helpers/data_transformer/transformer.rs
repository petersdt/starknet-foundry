// TODO remove that
#![allow(dead_code, unused_imports, unused_variables)]

use crate::handle_rpc_error;
use crate::helpers::data_transformer::sierra_abi::parse_expr;
use anyhow::{anyhow, bail, Context, Result};
use cairo_felt::Felt252;
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileKind, FileLongId, VirtualFile};
use cairo_lang_parser::utils::{get_syntax_root_and_diagnostics, SimpleParserDatabase};
use cairo_lang_syntax::node::ast::PathSegment::Simple;
use cairo_lang_syntax::node::ast::{
    ArgClause, ArgList, Expr, ExprInlineMacro, ExprPath, FunctionWithBody, ModuleItem,
    OptionStructArgExpr, PathSegment, Statement, StatementExpr, StructArg, SyntaxFile,
    WrappedArgList,
};
use cairo_lang_syntax::node::db::SyntaxGroup;
use cairo_lang_syntax::node::helpers::GetIdentifier;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{SyntaxNode, Terminal, Token, TypedSyntaxNode};
use conversions::byte_array::ByteArray;
use conversions::serde::serialize::{BufferWriter, CairoSerialize, SerializeToFeltVec};
use conversions::u256::CairoU256;
use conversions::FromConv;
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::cast::ToPrimitive;
use regex::Regex;
use smol_str::SmolStr;
use starknet::core::types::contract::{
    AbiConstructor, AbiEntry, AbiEnum, AbiFunction, AbiNamedMember, AbiStruct, StateMutability,
};
use starknet::core::types::{
    BlockId, BlockTag, ContractClass, LegacyContractAbiEntry, LegacyFunctionAbiEntry,
    LegacyStructAbiEntry, LegacyTypedParameter,
};
use starknet::macros::felt;
use starknet::providers::jsonrpc::HttpTransport;
use starknet::providers::{JsonRpcClient, Provider};
use starknet_crypto::FieldElement;
use std::any::Any;
use std::collections::HashSet;
use std::fmt::Debug;
use std::io;
use std::io::Write;
use std::ops::{Add, Deref, Sub};
use std::sync::Arc;

fn __iter_node(node: &SyntaxNode, db: &SimpleParserDatabase, spaces: usize) {
    let kind = node.kind(db);
    let text = node.text(db).unwrap_or("00000000000".parse().unwrap());
    let spaces_string = " ".to_string().repeat(spaces * 2);
    println!("{spaces_string}{kind}");
    println!("{spaces_string}{text}");
    println!("                         ");
    io::stdout().flush().expect("TODO: panic message");
    let children = db.get_children(node.clone());
    for i in children.iter() {
        __iter_node(i, db, spaces + 1);
    }
}

#[derive(Debug)]
pub(crate) struct CalldataStructField {
    value: AllowedCalldataArguments,
    abi_type: String,
}

impl CalldataStructField {
    pub fn new(value: AllowedCalldataArguments, abi_type: AbiType) -> Self {
        Self { value, abi_type }
    }
}

#[derive(Debug)]
pub(crate) struct CalldataStruct(Vec<CalldataStructField>);

impl CalldataStruct {
    pub fn new(arguments: Vec<CalldataStructField>) -> Self {
        Self(arguments)
    }
}

#[derive(Debug)]
pub(crate) struct CalldataArrayMacro(Vec<AllowedCalldataArguments>);

impl CalldataArrayMacro {
    pub fn new(arguments: Vec<AllowedCalldataArguments>) -> Self {
        Self(arguments)
    }
}

#[derive(Debug)]
pub(crate) struct CalldataEnum {
    position: usize,
    argument: Option<Box<AllowedCalldataArguments>>,
}

impl CalldataEnum {
    pub fn new(position: usize, argument: Option<Box<AllowedCalldataArguments>>) -> Self {
        Self { position, argument }
    }
}

#[derive(Debug)]
pub(crate) enum CalldataSingleArgument {
    // felt252
    // i8 - i128
    // u8 - u128
    // u256
    // TODO u512
    // bool
    // shortstring
    // string (ByteArray)
    Felt(FieldElement),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    U256(CairoU256),
    Bool(bool),
    ByteArray(ByteArray),
}

fn single_value_parsing_error_msg(
    value: &String,
    parsing_type: String,
    append_message: Option<String>,
) -> String {
    let mut message = format!(
        r#"Failed to parse value "{}" into type "{}""#,
        value, parsing_type
    );
    if let Some(append_msg) = append_message {
        message += append_msg.as_str();
    }
    message
}

macro_rules! parse_with_type {
    ($id:ident, $type:ty) => {
        $id.parse::<$type>()
            .context(single_value_parsing_error_msg(
                &$id,
                stringify!($type).to_string(),
                None,
            ))?
    };
}
impl CalldataSingleArgument {
    pub(crate) fn try_new(type_str_with_path: String, value: String) -> Result<Self> {
        // TODO add all corelib types
        let type_str = type_str_with_path
            .split("::")
            .last()
            .context("Couldn't parse parameter type from ABI")?;
        match type_str {
            "u8" => Ok(Self::U8(parse_with_type!(value, u8))),
            "u16" => Ok(Self::U16(parse_with_type!(value, u16))),
            "u32" => Ok(Self::U32(parse_with_type!(value, u32))),
            "u64" => Ok(Self::U64(parse_with_type!(value, u64))),
            "u128" => Ok(Self::U128(parse_with_type!(value, u128))),
            "u256" => {
                let num: BigUint =
                    value
                        .clone()
                        .as_str()
                        .parse()
                        .context(single_value_parsing_error_msg(
                            &value,
                            type_str_with_path,
                            None,
                        ))?;
                let num_bytes = num.to_bytes_be();
                if num_bytes.len() > 32 {
                    bail!(single_value_parsing_error_msg(
                        &value,
                        "u256".to_string(),
                        Some(": number too large to fit in 32 bytes".to_string())
                    ))
                }

                let mut result = [0u8; 32];
                let start = 32 - num_bytes.len();
                result[start..].copy_from_slice(&num_bytes);

                Ok(Self::U256(CairoU256::from_bytes(&result)))
            }
            "i8" => Ok(Self::I8(parse_with_type!(value, i8))),
            "i16" => Ok(Self::I16(parse_with_type!(value, i16))),
            "i32" => Ok(Self::I32(parse_with_type!(value, i32))),
            "i64" => Ok(Self::I64(parse_with_type!(value, i64))),
            "i128" => Ok(Self::I128(parse_with_type!(value, i128))),
            // TODO check if bytes31 is actually a felt
            // (e.g. alexandria_data_structures::bit_array::BitArray uses that)
            // https://github.com/starkware-libs/cairo/blob/bf48e658b9946c2d5446eeb0c4f84868e0b193b5/corelib/src/bytes_31.cairo#L14
            // There is `bytes31_try_from_felt252`, which means it isn't always a valid felt?
            "felt252" | "felt" | "ContractAddress" | "ClassHash" | "bytes31" => {
                let felt = FieldElement::from_dec_str(value.as_str()).context(
                    single_value_parsing_error_msg(&value, type_str_with_path, None),
                )?;
                Ok(Self::Felt(felt))
            }
            "bool" => Ok(Self::Bool(parse_with_type!(value, bool))),
            "ByteArray" => Ok(Self::ByteArray(ByteArray::from(value.as_str()))),
            _ => {
                bail!(single_value_parsing_error_msg(
                    &value,
                    type_str_with_path.clone(),
                    Some(format!(": unsupported type {}", type_str_with_path))
                ))
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct CalldataTuple(Vec<AllowedCalldataArguments>);

impl CalldataTuple {
    pub fn new(arguments: Vec<AllowedCalldataArguments>) -> Self {
        Self(arguments)
    }
}

#[derive(Debug)]
pub(crate) enum AllowedCalldataArguments {
    Struct(CalldataStruct),
    ArrayMacro(CalldataArrayMacro),
    Enum(CalldataEnum),
    // TODO rename to BasicType or smth
    SingleArgument(CalldataSingleArgument),
    Tuple(CalldataTuple),
}

impl CairoSerialize for CalldataSingleArgument {
    // https://docs.starknet.io/architecture-and-concepts/smart-contracts/serialization-of-cairo-types/
    fn serialize(&self, output: &mut BufferWriter) {
        match self {
            CalldataSingleArgument::Felt(value) => value.serialize(output),
            CalldataSingleArgument::I8(value) => value.serialize(output),
            CalldataSingleArgument::I16(value) => value.serialize(output),
            CalldataSingleArgument::I32(value) => value.serialize(output),
            CalldataSingleArgument::I64(value) => value.serialize(output),
            CalldataSingleArgument::I128(value) => value.serialize(output),
            CalldataSingleArgument::U8(value) => value.serialize(output),
            CalldataSingleArgument::U16(value) => value.serialize(output),
            CalldataSingleArgument::U32(value) => value.serialize(output),
            CalldataSingleArgument::U64(value) => value.serialize(output),
            CalldataSingleArgument::U128(value) => value.serialize(output),
            CalldataSingleArgument::U256(value) => value.serialize(output),
            CalldataSingleArgument::Bool(value) => value.serialize(output),
            CalldataSingleArgument::ByteArray(value) => value.serialize(output),
        };
    }
}

impl CairoSerialize for CalldataStructField {
    // Every argument serialized in order of occurrence
    fn serialize(&self, output: &mut BufferWriter) {
        self.value.serialize(output);
    }
}

impl CairoSerialize for CalldataStruct {
    // https://docs.starknet.io/architecture-and-concepts/smart-contracts/serialization-of-cairo-types/#serialization_of_structs
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataTuple {
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataArrayMacro {
    // https://docs.starknet.io/architecture-and-concepts/smart-contracts/serialization-of-cairo-types/#serialization_of_arrays
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.len().serialize(output);
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataEnum {
    // https://docs.starknet.io/architecture-and-concepts/smart-contracts/serialization-of-cairo-types/#serialization_of_enums
    fn serialize(&self, output: &mut BufferWriter) {
        self.position.serialize(output);
        if self.argument.is_some() {
            self.argument.as_ref().unwrap().serialize(output);
        }
    }
}
impl CairoSerialize for AllowedCalldataArguments {
    fn serialize(&self, output: &mut BufferWriter) {
        match self {
            AllowedCalldataArguments::Struct(value) => value.serialize(output),
            AllowedCalldataArguments::ArrayMacro(value) => value.serialize(output),
            AllowedCalldataArguments::Enum(value) => value.serialize(output),
            AllowedCalldataArguments::SingleArgument(value) => value.serialize(output),
            AllowedCalldataArguments::Tuple(value) => value.serialize(output),
        }
    }
}

type AbiType = String;
type ArrayType = String;
#[derive(Debug)]
pub enum LegacyFunctionArgument {
    Felt,
    Array(ArrayType),
    Other(AbiType),
}

pub type ArgumentName = String;

fn check_arg_names_equal(
    struct_args_with_values: &[(ArgumentName, Expr)],
    matching_struct_abi_definition: &LegacyStructAbiEntry,
) -> bool {
    struct_args_with_values
        .iter()
        .map(|(arg_name, _)| arg_name.clone())
        .collect::<HashSet<ArgumentName>>()
        != matching_struct_abi_definition
            .members
            .iter()
            .map(|x| x.name.clone())
            .collect::<HashSet<ArgumentName>>()
}

fn find_legacy_abi_fn(
    abi: &[LegacyContractAbiEntry],
    fn_name: String,
) -> Option<&LegacyFunctionAbiEntry> {
    abi.iter().find_map(|abi_entry| {
        if let LegacyContractAbiEntry::Function(legacy_fn) = abi_entry {
            if legacy_fn.name == fn_name {
                return Some(legacy_fn);
            }
        }
        None
    })
}

/// Finds ABI constructor and turns it into [`AbiFunction`] to simplify whole flow later
/// ([`AbiConstructor`] has less fields, but both have `name` and `inputs`)
fn find_new_abi_constructor(abi: &[AbiEntry], fn_name: &str) -> Option<AbiFunction> {
    let maybe_constructor = abi.iter().find_map(|interface_item| {
        if let AbiEntry::Constructor(constructor) = interface_item {
            return Some(constructor);
        }
        None
    });
    maybe_constructor.map(|constructor| AbiFunction {
        name: constructor.name.clone(),
        inputs: constructor.inputs.clone(),
        outputs: vec![],
        state_mutability: StateMutability::View,
    })
}

fn find_new_abi_fn(abi: &Vec<AbiEntry>, fn_name: &String) -> Option<AbiFunction> {
    if fn_name == "constructor" {
        return find_new_abi_constructor(abi, fn_name);
    }
    let interfaces: Vec<&Vec<AbiEntry>> = abi
        .iter()
        .filter_map(|abi_entry| {
            if let AbiEntry::Interface(interface) = abi_entry {
                return Some(&interface.items);
            }
            None
        })
        .collect();
    interfaces.into_iter().flatten().find_map(|interface_item| {
        if let AbiEntry::Function(func) = interface_item {
            if func.name == *fn_name {
                return Some(func.clone());
            }
        }
        None
    })
}

fn find_legacy_abi_structs(
    struct_name: &String,
    abi: &[LegacyContractAbiEntry],
) -> Vec<LegacyStructAbiEntry> {
    abi.iter()
        .filter_map(|abi_entry| {
            if let LegacyContractAbiEntry::Struct(legacy_struct) = abi_entry {
                if legacy_struct.name == *struct_name {
                    return Some(legacy_struct);
                }
            }
            None
        })
        .cloned()
        .collect()
}

/// Parses input calldata and puts inside wrapper Cairo code to allow parsing by [`SimpleParserDatabase`]
fn parse_input_calldata(input_calldata: String, db: &SimpleParserDatabase) -> Result<SyntaxNode> {
    let input_calldata = input_calldata
        .strip_prefix("{")
        .context("Couldn't parse input calldata, missing {")?
        .strip_suffix("}")
        .context("Couldn't parse input calldata, missing }")?;

    let temporary_code = Arc::new(format!(
        "fn __WRAPPER_FUNC_TO_PARSE__() {{ ({input_calldata}); }}"
    ));
    let virtual_file = db.intern_file(FileLongId::Virtual(VirtualFile {
        parent: None,
        name: "parser_input".into(),
        content: temporary_code.clone(),
        code_mappings: Default::default(),
        kind: FileKind::Module,
    }));
    let (node, diagnostics) =
        get_syntax_root_and_diagnostics(db, virtual_file, temporary_code.as_str());

    match diagnostics.check_error_free() {
        Ok(_) => Ok(node),
        Err(_) => {
            bail!(
                "Invalid Cairo expression found in input calldata:\n{}",
                diagnostics.format(db)
            )
        }
    }
}

/// Traverses through AST to get parenthesised expression with calldata
fn get_input_expr_between_parentheses(node: SyntaxNode, db: &SimpleParserDatabase) -> Expr {
    let syntax_file = SyntaxFile::from_syntax_node(db, node);
    let module_item_list = syntax_file.items(db);
    let function_with_body = module_item_list
        .elements(db)
        .into_iter()
        .filter_map(|x| match x {
            ModuleItem::FreeFunction(f) => Some(f),
            _ => None,
        })
        .collect::<Vec<FunctionWithBody>>()
        .pop()
        .expect("Failed to parse wrapper calldata function");
    let expr_block = function_with_body.body(db);
    let statement_list = expr_block.statements(db);
    let statement_expr = statement_list
        .elements(db)
        .into_iter()
        .filter_map(|x| match x {
            Statement::Expr(expr) => Some(expr),
            _ => None,
        })
        .collect::<Vec<StatementExpr>>()
        .pop()
        .expect("Failed to parse wrapper calldata function");
    statement_expr.expr(db)
}

/// Gets input expression artificially put between parentheses in [`parse_input_calldata`]
fn get_expr_list(parsed_node: SyntaxNode, db: &SimpleParserDatabase) -> Vec<Expr> {
    let statement_list_node = get_input_expr_between_parentheses(parsed_node, db);
    // TODO remove comment
    // Possibilities:
    // 123 - ExprParenthesized ( TerminalLiteralNumber )
    // 123, 123 - ExprListParenthesized ( ExprList )
    // (123) - ExprParenthesized ( ExprParenthesized )
    // (123, 123) - ExprParenthesized ( ExprListParenthesized )
    // 123, (123) - ExprListParenthesized ( ExprList )
    match statement_list_node {
        // List of arguments - function accepts more than one argument
        Expr::Tuple(list_of_args) => list_of_args.expressions(db).elements(db),
        // Single argument between parentheses
        Expr::Parenthesized(single_arg) => {
            vec![single_arg.expr(db)]
        }
        _ => {
            unreachable!(
                "Due to construction of the wrapper function, other possibilities are not possible"
            )
        }
    }
}

pub async fn transform_input_calldata(
    input_calldata: String,
    function_name: &String,
    class_hash: FieldElement,
    client: &JsonRpcClient<HttpTransport>,
) -> Result<Vec<FieldElement>> {
    let db = SimpleParserDatabase::default();

    // TODO handle when parsing fails and fn __WRAPPER_FUNC_TO_PARSE__() is printed to stderr
    let parsed_node = parse_input_calldata(input_calldata, &db)?;
    let contract_class = client
        .get_class(BlockId::Tag(BlockTag::Latest), class_hash)
        .await
        .map_err(handle_rpc_error)
        .unwrap();

    //TODO remove that
    // __iter_node(&parsed_node, &db, 2);

    let arguments_expr_list = get_expr_list(parsed_node, &db);

    match contract_class {
        ContractClass::Sierra(sierra_class) => {
            let abi: Vec<AbiEntry> = serde_json::from_str(sierra_class.abi.as_str())
                .context("Couldn't deserialize ABI received from chain")?;
            let called_function = find_new_abi_fn(&abi, function_name).context(format!(
                r#"Function "{}" not found in ABI of the contract"#,
                function_name
            ))?;

            if called_function.inputs.len() != arguments_expr_list.len() {
                bail!(
                    "Invalid number of arguments, passed {}, expected {}",
                    arguments_expr_list.len(),
                    called_function.inputs.len()
                )
            }

            let parsed_exprs = called_function
                .inputs
                .iter()
                .zip(arguments_expr_list)
                .map(|(param, arg)| parse_expr(arg, param.r#type.clone(), &abi, &db))
                .collect::<Result<Vec<AllowedCalldataArguments>>>()?;

            Ok(parsed_exprs
                .iter()
                .flat_map(|args| args.serialize_to_vec())
                .map(FieldElement::from_)
                .collect::<Vec<FieldElement>>())
        }
        ContractClass::Legacy(legacy_class) => {
            todo!("Finish adding legacy ABI handling");

            // TODO is this valid?                                      vvv
            // let abi = legacy_class.abi.expect("Can't send a transaction without ABI");
            // let called_function = find_legacy_abi_fn(&abi, function_name.clone()).context(format!("Function {} not found in ABI of the contract", function_name))?;
            // let parsed_called_function_arguments = parse_legacy_fn_arguments(called_function);
            // // parse_expr_legacy_abi()
            // // TODO should it be here? or should chain validate if args list is of a valid length
            // if called_function.inputs.len() != arguments_expr_list.len() {
            //     bail!("Invalid number of arguments, passed {}, expected {}", arguments_expr_list.len(), called_function.inputs.len())
            // };
            // bail!("Not implemented yet")
        }
    }
}

mod tests {
    use super::*;
    use conversions::string::TryFromHexStr;
    use conversions::IntoConv;
    use num_bigint::ToBigUint;
    use num_traits::{One, Pow};
    use shared::rpc::create_rpc_client;
    use starknet::macros::felt;
    use starknet::providers::sequencer::models::ContractAddresses;
    use std::ops::Sub;

    // https://sepolia.starkscan.co/class/0x05cf2011fdcab16c211fd0f249a3decf3475886a7e020ba10f3b001f1eed8119#code
    const DATA_TRANSFORMER_TEST_CLASS_HASH: &str =
        "0x05cf2011fdcab16c211fd0f249a3decf3475886a7e020ba10f3b001f1eed8119";

    // 2^128 + 3
    const BIG_NUMBER: &str = "340282366920938463463374607431768211459";

    fn u128s_to_felts(vec: Vec<u128>) -> Vec<FieldElement> {
        vec.into_iter().map(FieldElement::from).collect()
    }

    #[tokio::test]
    async fn test_invalid_input() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            " 0x1 }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains("Couldn't parse input calldata, missing {"));

        //////////////

        let output = transform_input_calldata(
            "{ 0x1".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains("Couldn't parse input calldata, missing }"));

        //////////////

        let output = transform_input_calldata(
            "0x1".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains("Couldn't parse input calldata, missing {"));
    }
    #[tokio::test]
    async fn test_function_not_found() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            "{ 0x1 }".to_string(),
            &"nonexistent_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Function "nonexistent_fn" not found in ABI of the contract"#));
    }
    #[tokio::test]
    async fn test_invalid_suffix() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            "{ 1_u10 }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;
        dbg!(&output);

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Failed to parse value "1" into type "u10": unsupported type"#));
    }
    #[tokio::test]
    async fn test_number_suffix() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            "{ 1_u256 }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        // TODO not sure about that behaviour, simple_fn accepts felt252
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![1, 0]);

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_invalid_cairo_expression() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            "{ aaa: }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains("Invalid Cairo expression found in input calldata:"));
    }
    #[tokio::test]
    async fn test_invalid_arg_number() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            "{ 0x1, 0x2, 0x3 }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains("Invalid number of arguments, passed 3, expected 1"));
    }
    #[tokio::test]
    async fn test_simple_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn simple_fn(self:@T, a: felt252);
            "{ 0x1 }".to_string(),
            &"simple_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![0x1]);

        assert_eq!(output.unwrap(), expected_output);
    }

    #[tokio::test]
    async fn test_u256_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn u256_fn(self:@T, a: u256);
            format!("{{ {} }}", BIG_NUMBER),
            &"u256_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![3, 1]);

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_signed_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn signed_fn(self:@T, a: i32);
            "{ -1 }".to_string(),
            &"signed_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = vec![Felt252::from(-1).into_()];

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_signed_fn_overflow() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        // i32max = 2147483647
        let output = transform_input_calldata(
            // fn signed_fn(self:@T, a: i32);
            "{ 2147483648 }".to_string(),
            &"signed_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Failed to parse value "2147483648" into type "i32""#));
    }
    #[tokio::test]
    async fn test_unsigned_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        // u32max = 4294967295
        let output = transform_input_calldata(
            // fn unsigned_fn(self:@T, a: u32);
            "{ 4294967295 }".to_string(),
            &"unsigned_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![4294967295]);

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_tuple_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn tuple_fn(self:@T, a: (felt252, u8, Enum));
            "{ (123, 234, Enum::Three(NestedStructWithField {a: SimpleStruct {a: 345}, b: 456 })) }".to_string(),
            &"tuple_fn".to_string(),
            contract_address,
            &client
        ).await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![123, 234, 2, 345, 456]);

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_complex_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn complex_fn(self: @T, arr: Array<Array<felt252>>, one: u8, two: i16, three: ByteArray, four: (felt252, u32), five: bool, six: u256);
            r#"{ array![array![0,1,2], array![3,4,5,6,7]], 8, 9, "ten", (11, 12), true, 13 }"#
                .to_string(),
            &"complex_fn".to_string(),
            contract_address,
            &client,
        )
        .await;
        dbg!(&output);

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![
            2, 3, 0, 1, 2, 5, 3, 4, 5, 6, 7, 8, 9, 0, 7628142, 3, 11, 12, 1, 13, 0,
        ]);

        assert_eq!(output.unwrap(), expected_output);
    }
    #[tokio::test]
    async fn test_simple_struct_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn simple_struct_fn(self: @T, a: SimpleStruct);
            "{ SimpleStruct {a: 0x12} }".to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![0x12]);

        assert_eq!(output.unwrap(), expected_output);
    }

    #[tokio::test]
    async fn test_simple_struct_fn_invalid_struct_arg() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn simple_struct_fn(self: @T, a: SimpleStruct);
            r#"{ SimpleStruct {a: "string"} }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Failed to parse value "string" into type "core::felt252""#))
    }
    #[tokio::test]
    async fn test_simple_struct_fn_invalid_struct_name() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn simple_struct_fn(self: @T, a: SimpleStruct);
            r#"{ InvalidStructName {a: "string"} }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(r#"Invalid argument type, expected "data_tranformer_contract::SimpleStruct", got "InvalidStructName""#))
    }
    #[tokio::test]
    async fn test_simple_struct_fn_invalid_arg() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn simple_struct_fn(self: @T, a: SimpleStruct);
            r#"{ 0x1 }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(
            r#"Failed to parse value "1" into type "data_tranformer_contract::SimpleStruct""#
        ));

        let output = transform_input_calldata(
            r#"{ "string_argument" }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(r#"Failed to parse value "string_argument" into type "data_tranformer_contract::SimpleStruct""#));

        let output = transform_input_calldata(
            r#"{ 'shortstring' }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(r#"Failed to parse value "shortstring" into type "data_tranformer_contract::SimpleStruct""#));

        let output = transform_input_calldata(
            r#"{ true }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(
            r#"Failed to parse value "true" into type "data_tranformer_contract::SimpleStruct""#
        ));

        let output = transform_input_calldata(
            r#"{ array![0x1, 2, 0x3, 04] }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(
            r#"Invalid argument type, expected "data_tranformer_contract::SimpleStruct", got array"#
        ));

        let output = transform_input_calldata(
            r#"{ (1, array![2], 0x3) }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(
            r#"Invalid argument type, expected "data_tranformer_contract::SimpleStruct", got tuple"#
        ));

        let output = transform_input_calldata(
            r#"{ My::Enum }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(
            r#"Invalid argument type, expected "data_tranformer_contract::SimpleStruct", got "My""#
        ));

        let output = transform_input_calldata(
            r#"{ core::path::My::Enum(10) }"#.to_string(),
            &"simple_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(r#"Invalid argument type, expected "data_tranformer_contract::SimpleStruct", got "core::path::My""#));
    }

    #[tokio::test]
    async fn test_nested_struct_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn nested_struct_fn(self: @T, a: NestedStructWithField);
            r#"{ NestedStructWithField { a: SimpleStruct { a: 0x24 }, b: 96 } }"#.to_string(),
            &"nested_struct_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_ok());

        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![0x24, 96]);

        assert_eq!(output.unwrap(), expected_output);
    }

    // enum Enum
    // One,
    // #[default]
    // Two: u128,
    // Three: NestedStructWithField

    #[tokio::test]
    async fn test_enum_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn enum_fn(self: @T, a: Enum);
            r#"{ Enum::One }"#.to_string(),
            &"enum_fn".to_string(),
            contract_address,
            &client,
        )
        .await;
        assert!(output.is_ok());

        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![0]);

        assert_eq!(output.unwrap(), expected_output);

        /////////////

        let output = transform_input_calldata(
            r#"{ Enum::Two(128) }"#.to_string(),
            &"enum_fn".to_string(),
            contract_address,
            &client,
        )
        .await;
        assert!(output.is_ok());

        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![1, 128]);

        assert_eq!(output.unwrap(), expected_output);

        /////////////

        let output = transform_input_calldata(
            r#"{ Enum::Three(NestedStructWithField { a: SimpleStruct { a: 123 }, b: 234 }) }"#
                .to_string(),
            &"enum_fn".to_string(),
            contract_address,
            &client,
        )
        .await;
        assert!(output.is_ok());

        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![2, 123, 234]);

        assert_eq!(output.unwrap(), expected_output);
    }

    #[tokio::test]
    async fn test_enum_fn_invalid_variant() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn enum_fn(self: @T, a: Enum);
            r#"{ Enum::Four }"#.to_string(),
            &"enum_fn".to_string(),
            contract_address,
            &client,
        )
        .await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Couldn't find variant "Four" in enum "Enum""#))
    }

    #[tokio::test]
    async fn test_complex_struct_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        // struct ComplexStruct
        //     a: NestedStructWithField,
        //     b: felt252,
        //     c: u8,
        //     d: i32,
        //     e: Enum,
        //     f: ByteArray,
        //     g: Array<felt252>,
        //     h: u256,
        //     i: (i128, u128),

        let output = transform_input_calldata(
            // fn complex_struct_fn(self: @T, a: ComplexStruct);
            r#"{ ComplexStruct {a: NestedStructWithField { a: SimpleStruct { a: 1 }, b: 2 }, b: 3, c: 4, d: 5, e: Enum::Two(6), f: "seven", g: array![8, 9], h: 10, i: (11, 12) } }"#.to_string(),
            &"complex_struct_fn".to_string(),
            contract_address,
            &client
        ).await;
        assert!(output.is_ok());

        // 1 2 - a: NestedStruct
        // 3 - b: felt252
        // 4 - c: u8
        // 5 - d: i32
        // 1 6 - e: Enum
        // 0 495623497070 5 - f: string (ByteArray)
        // 2 8 9 - g: array!
        // 10 0 - h: u256
        // 11 12 - i: (i128, u128)
        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![
            1,
            2,
            3,
            4,
            5,
            1,
            6,
            0,
            495623497070,
            5,
            2,
            8,
            9,
            10,
            0,
            11,
            12,
        ]);

        assert_eq!(output.unwrap(), expected_output);
    }

    // TODO add similar test but with enums
    //  - take existing contract code
    //  - find/create a library with an enum
    //  - add to project as a dependency
    //  - create enum with the same name in your contract code
    #[tokio::test]
    async fn test_external_struct_fn_ambiguity() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn external_struct_fn(self:@T, a: BitArray, b: bit_array::BitArray);
            "{ BitArray { bit: 23 }, BitArray { data: array![0], current: 1, read_pos: 2, write_pos: 3 } }".to_string(),
            &"external_struct_fn".to_string(),
            contract_address,
            &client
        ).await;

        assert!(output.is_err());
        assert!(output.unwrap_err().to_string().contains(r#"Found more than one struct "BitArray" in ABI, please specify a full path to the struct"#))
    }

    #[tokio::test]
    async fn test_external_struct_fn_invalid_path() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn external_struct_fn(self:@T, a: BitArray, b: bit_array::BitArray);
            "{ something::BitArray { bit: 23 }, BitArray { data: array![0], current: 1, read_pos: 2, write_pos: 3 } }".to_string(),
            &"external_struct_fn".to_string(),
            contract_address,
            &client
        ).await;

        assert!(output.is_err());
        assert!(output
            .unwrap_err()
            .to_string()
            .contains(r#"Struct "something::BitArray" not found in ABI"#))
    }
    #[tokio::test]
    async fn test_external_struct_fn() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement =
            FieldElement::try_from_hex_str(DATA_TRANSFORMER_TEST_CLASS_HASH).unwrap();

        let output = transform_input_calldata(
            // fn external_struct_fn(self:@T, a: BitArray, b: bit_array::BitArray);
            "{ data_tranformer_contract::BitArray { bit: 23 }, alexandria_data_structures::bit_array::BitArray { data: array![0], current: 1, read_pos: 2, write_pos: 3 } }".to_string(),
            &"external_struct_fn".to_string(),
            contract_address,
            &client
        ).await;

        assert!(output.is_ok());

        let expected_output: Vec<FieldElement> = u128s_to_felts(vec![23, 1, 0, 1, 2, 3]);

        assert_eq!(output.unwrap(), expected_output);
    }
}
