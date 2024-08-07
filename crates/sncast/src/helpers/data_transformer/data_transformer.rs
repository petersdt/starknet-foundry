// TODO remove that
#![allow(dead_code, unused_imports, unused_variables)]

use std::any::Any;
use std::collections::HashSet;
use std::fmt::Debug;
use crate::handle_rpc_error;
use anyhow::{anyhow, bail, Context, Result};
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileKind, FileLongId, VirtualFile};
use cairo_lang_parser::utils::{get_syntax_root_and_diagnostics, SimpleParserDatabase};
use cairo_lang_syntax::node::ast::PathSegment::Simple;
use cairo_lang_syntax::node::ast::{ArgClause, ArgList, Expr, ExprInlineMacro, ExprPath, FunctionWithBody, ModuleItem, OptionStructArgExpr, PathSegment, Statement, StatementExpr, StructArg, SyntaxFile, WrappedArgList};
use cairo_lang_syntax::node::db::SyntaxGroup;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{SyntaxNode, Terminal, Token, TypedSyntaxNode};
use itertools::Itertools;
use starknet::core::types::contract::{AbiEntry, AbiEnum, AbiFunction, AbiNamedMember, AbiStruct};
use starknet::core::types::{BlockId, BlockTag, ContractClass, LegacyContractAbiEntry, LegacyFunctionAbiEntry, LegacyStructAbiEntry, LegacyTypedParameter};
use starknet::providers::jsonrpc::HttpTransport;
use starknet::providers::{JsonRpcClient, Provider};
use starknet_crypto::FieldElement;
use std::io;
use std::io::Write;
use std::ops::{Add, Deref, Sub};
use std::sync::Arc;
use cairo_felt::Felt252;
use cairo_lang_syntax::node::helpers::GetIdentifier;
use smol_str::SmolStr;
use regex::Regex;
use starknet::macros::felt;
use conversions::byte_array::ByteArray;
use conversions::FromConv;
use conversions::serde::serialize::{BufferWriter, CairoSerialize, SerializeToFeltVec};
use conversions::u256::CairoU256;

fn parse_input_calldata_test(input_calldata: String) {
    let simple_db = SimpleParserDatabase::default();
    let input_calldata = Arc::new(input_calldata);
    let virtual_file = simple_db.intern_file(FileLongId::Virtual(VirtualFile {
        parent: None,
        name: "parser_input".into(),
        content: input_calldata.clone(),
        code_mappings: Default::default(),
        kind: FileKind::Module,
    }));
    // TODO: after 2.7.0(?) change that into db.parse_virtual
    // let test = db.file_syntax(db.intern_file(file));
    // dbg!(&test);

    // let mut diagnostics = DiagnosticsBuilder::default();
    // let syntax_file = Parser::parse_file(&simple_db, &mut diagnostics, virtual_file, input_calldata.as_str());
    // let syntax_file_items_elements = syntax_file.items(&simple_db).elements(&simple_db);
    // let last_elem_func = syntax_file_items_elements.last().unwrap();

    // if let ModuleItem::FreeFunction(f) = syntax_file_items_elements[1].clone() {
    //     let body = f.body(&simple_db);
    //     let args = f.declaration(&simple_db).signature(&simple_db).parameters(&simple_db);
    //     dbg!(&args);
    // }
    // dbg!(&syntax_file);
    // let test: Arc<Vec<SyntaxNode>> = simple_db.get_children(syntax_file.as_syntax_node());
    // dbg!();
    let (node, diagnostics) =
        get_syntax_root_and_diagnostics(&simple_db, virtual_file, input_calldata.as_str());
    // if diagnostics.check_error_free().is_ok() { Ok(node) } else { Err(diagnostics) }
    let errors = diagnostics.format(&simple_db);
    println!("==============\n{}\n==============\n", errors);
    // dbg!(&node.width(&simple_db));
    // dbg!(&node.span(&simple_db));
    // dbg!(&node.kind(&simple_db));
    // dbg!(&node.text(&simple_db));
    // dbg!(&node.span_without_trivia(&simple_db));
    // dbg!(&node.green_node(&simple_db));
    // dbg!(&node.get_terminal_token(&simple_db));
    // dbg!(&node.get_text(&simple_db));
    // let mut preorder = node.preorder(&simple_db);
    // dbg!(&preorder.next());
    // dbg!(&preorder.next());
    // dbg!(&preorder.next());
    // dbg!(&node.clone().get_text_without_trivia(&simple_db));
    // let typed_syntax_node = TypedSyntaxNode::from_syntax_node(&simple_db, node.clone());
    // let element_list = ModuleItemList::from_syntax_node(&simple_db, node.clone());
    // let children = simple_db.get_children(node.clone());
    // let child = &children.iter().next().unwrap().green_node(&simple_db);
    // dbg!(child.children());
    iter_node(&node, &simple_db, 0);
    // let descendants = node.descendants(&simple_db).collect_vec();
    // for i in node.descendants(&simple_db) {
    //     dbg!(&i.kind(&simple_db));
    //     dbg!(&i.text(&simple_db).unwrap_or("\t\t\terror".parse().unwrap()));
    // }
    dbg!();
}

fn iter_node(node: &SyntaxNode, db: &SimpleParserDatabase, spaces: usize) {
    let kind = node.kind(db);
    let text = node
        .text(db)
        .unwrap_or("00000000000".parse().unwrap());
    let spaces_string = " ".to_string().repeat(spaces * 2);
    println!("{spaces_string}{kind}");
    println!("{spaces_string}{text}");
    println!("                         ");
    io::stdout().flush().expect("TODO: panic message");
    let children = db.get_children(node.clone());
    for i in children.iter() {
        iter_node(i, db, spaces + 1);
    }
}

// TODO add support for impls? should it be done?
// TODO fix external structs - not sure if this is necessary since we don't add them to code tho
fn parse_input_calldata(
    input_calldata: String,
    db: &SimpleParserDatabase,
) -> Result<SyntaxNode> {
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
    // TODO ugly, fix that
    match diagnostics.check_error_free() {
        Ok(_) => Ok(node),
        Err(_) => {
            // TODO improve error message
            // maybe Err(x) could be used?
            bail!("Invalid Cairo expression found in input calldata:\n{}", diagnostics.format(db))
            // Err(anyhow!(format!(
            //     "Invalid Cairo expression found in input calldata:\n{}",
            //     diagnostics.format(db)
            // )))
        }
    }
}

#[derive(Debug)]
pub(crate) struct CalldataStructField {
    value: AllowedCalldataArguments,
    abi_type: String,
}

impl CalldataStructField {
    pub fn new(value: AllowedCalldataArguments, abi_type: AbiType) -> Self {
        Self {value, abi_type}
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
        Self{position, argument}
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
    Felt252(Felt252),
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
    ByteArray(ByteArray)
}

macro_rules! parse_with_type {
    ($id:ident, $type:ty) => {
        $id.parse::<$type>().context(format!("Failed to parse {} into {}", $id, stringify!($type)))?
    }
}
impl CalldataSingleArgument {
    pub(crate) fn try_new(type_str_with_path: String, value: String) -> Result<Self> {
        let type_str = type_str_with_path.split("::").last().context("Couldn't parse parameter type from ABI")?;
        // TODO check suffixes, like ..._u8 etc.
        match type_str {
            "u8" => {
                Ok(Self::U8(parse_with_type!(value, u8)))
            },
            "u16" => {
                Ok(Self::U16(parse_with_type!(value, u16)))
            },
            "u32" => {
                Ok(Self::U32(parse_with_type!(value, u32)))
            },
            "u64" => {
                Ok(Self::U64(parse_with_type!(value, u64)))
            },
            "u128" => {
                Ok(Self::U128(parse_with_type!(value, u128)))
            },
            "u256" => {
                Ok(Self::U256(CairoU256::from_bytes(value.as_bytes())))
            },
            "i8" => {
                Ok(Self::I8(parse_with_type!(value, i8)))
            },
            "i16" => {
                Ok(Self::I16(parse_with_type!(value, i16)))
            },
            "i32" => {
                Ok(Self::I32(parse_with_type!(value, i32)))
            },
            "i64" => {
                Ok(Self::I64(parse_with_type!(value, i64)))
            },
            "i128" => {
                Ok(Self::I128(parse_with_type!(value, i128)))
            },
            "felt252" | "felt" => {
                Ok(Self::Felt252(Felt252::from_bytes_be(value.as_bytes())))
            },
            "bool" => {
                Ok(Self::Bool(parse_with_type!(value, bool)))
            },
            "ByteArray" => {
                Ok(Self::ByteArray(ByteArray::from(value.as_str())))
            }
            _ => {
                // TODO add more meaningful message
                bail!("Unsupported type")
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
    // TODO validate if all arguments for the macro invocation are the same type
    ArrayMacro(CalldataArrayMacro),
    Enum(CalldataEnum),
    // TODO rename to BasicType or smth
    SingleArgument(CalldataSingleArgument),
    Tuple(CalldataTuple),
}

impl CairoSerialize for CalldataSingleArgument {
    fn serialize(&self, output: &mut BufferWriter) {
        match self {
            CalldataSingleArgument::Felt252(value) => value.serialize(output),
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
    fn serialize(&self, output: &mut BufferWriter) {
        self.value.serialize(output);
    }
}

impl CairoSerialize for CalldataStruct {
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataTuple {
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataArrayMacro{
    fn serialize(&self, output: &mut BufferWriter) {
        self.0.len().serialize(output);
        self.0.iter().for_each(|field| field.serialize(output));
    }
}

impl CairoSerialize for CalldataEnum {
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


// fn find_input_expr_between_parentheses(node: SyntaxNode, db: &SimpleParserDatabase) -> SyntaxNode {
//     TODO fix this heuristic? or add a comment explaining that
//     let module_item_list = &db.get_children(node)[0];
//     let function_with_body = &db.get_children(module_item_list.clone())[0];
//     let expr_block = &db.get_children(function_with_body.clone())[3];
//     let statement_list = &db.get_children(expr_block.clone())[1];
//     let statement_expr = &db.get_children(statement_list.clone())[0];
//     TODO assert that this is ExprListParenthesized/ExprParenthesized if heuristic stays
//     123 - ExprParenthesized ( TerminalLiteralNumber )
//     123, 123 - ExprListParenthesized ( ExprList )
//     (123) - ExprParenthesized ( ExprParenthesized )
//     (123, 123) - ExprParenthesized ( ExprListParenthesized )
//     123, (123) - ExprListParenthesized ( ExprList )
//     db.get_children(statement_expr.clone())[1].clone()
// }
fn find_input_expr_between_parentheses(node: SyntaxNode, db: &SimpleParserDatabase) -> Expr {
    //  or find if it is possible to use some methods on given nodes
    let syntax_file = SyntaxFile::from_syntax_node(db, node);
    let module_item_list = syntax_file.items(db);
    let function_with_body = module_item_list.elements(db).into_iter().filter_map(|x| match x {
        ModuleItem::FreeFunction(f) => Some(f),
        _ => None
    }).collect::<Vec<FunctionWithBody>>().pop().unwrap();
    let expr_block = function_with_body.body(db);
    let statement_list = expr_block.statements(db);
    let statement_expr = statement_list.elements(db).into_iter().filter_map(|x| match x {
        Statement::Expr(expr) => Some(expr),
        _ => None
    }).collect::<Vec<StatementExpr>>().pop().unwrap();
    statement_expr.expr(db)
}

fn resolve_name_with_module_path(node: SyntaxNode, simple_db: &SimpleParserDatabase) -> Vec<SmolStr>{
    let expr_path_node = simple_db
        .get_children(node)
        .iter()
        .find(|x| x.kind(simple_db) == SyntaxKind::ExprPath)
        // TODO ensure by types that this function can be called only on those SyntaxKinds that
        // can have ExprPath
        .expect("[WIP] This syntax node doesn't have ExprPath as one of its children")
        .clone();
    // TODO can type safety be ensured here?
    let expr_path = ExprPath::from_syntax_node(simple_db, expr_path_node);
    // two possibilities here: PathSegmentWithGenericArgs and PathSegmentSimple
    // it's not possible to specify generic args when using as module specification
    // TODO check if it is true
    expr_path.elements(simple_db).iter().filter_map(|p| match p {
        Simple(segment) => {
            Some(segment.ident(simple_db).token(simple_db).text(simple_db))
        }
        _ => {
            None
        }
    }).collect()
}

pub type ArgumentName = String;

//TODO rename to find or sth else
fn parse_enum_expr_path<'a>(enum_variant: &String, enum_path: &[String],  abi: &'a [AbiEntry], db: &SimpleParserDatabase) -> Result<(usize, &'a AbiNamedMember)>{
    let enum_path_with_colons = enum_path.join("::");

    let enums = abi.iter().filter_map(|abi_entry| {
        if let AbiEntry::Enum(abi_enum) = abi_entry {
            Some(abi_enum)
        } else {
            None
        }
    }).collect::<Vec<&AbiEnum>>();
    let enums_from_abi: Vec<&AbiEnum> = enums
        .iter()
        .cloned()
        .filter(|&x| x.name == enum_path_with_colons || x.name.split("::").last() == enum_path.last().map(String::as_str))
        .collect();
    if enums_from_abi.len() > 1 {
        bail!("Found more than one enum with name {} in ABI, please specify a full path to the enum", enum_path_with_colons)
    } else if enums_from_abi.is_empty() {
        bail!("Enum with name {} not found in ABI", enum_path_with_colons)
    }
    let enum_abi_definition = enums_from_abi.first().expect("All other possible cases have been handled");

    let position_and_enum_variant = enum_abi_definition
        .variants
        .iter()
        .find_position(|variant| variant.name == *enum_variant)
        .context(format!("Couldn't find variant {} in enum {}", enum_variant, enum_path_with_colons))?;
    Ok(position_and_enum_variant)
}



fn arg_list_to_exprs(arg_list: ArgList, db: &SimpleParserDatabase) -> Result<Vec<Expr>> {
    let arguments = arg_list.elements(db);
    if arguments.iter().map(|arg| arg.modifiers(db).elements(db)).any(|mod_list| !mod_list.is_empty()) {
        // TODO better message
        bail!("Cannot use ref/mut modifiers")
    }
    arguments.iter().map(|arg| match arg.arg_clause(db) {
        ArgClause::Unnamed(unnamed_arg) => Ok(unnamed_arg.value(db)),
        ArgClause::Named(_) | ArgClause::FieldInitShorthand(_) => {
            // tODO better message
            bail!("Neither named args nor named arguments/field init shorthand are supported")
        }
    }).collect::<Result<Vec<Expr>>>()
}

fn parse_expr_path_to_path_elements(expr_path: ExprPath, db: &SimpleParserDatabase) -> Result<Vec<String>> {
    expr_path.elements(db).iter().map(|p| match p {
        Simple(segment) => {
            Ok(segment.ident(db).token(db).text(db).to_string())
        }
        PathSegment::WithGenericArgs(_) => bail!("Cannot use generic args when specifying struct/enum path")
    }).collect::<Result<Vec<String>>>()
}

// TODO param_type can possibly be a reference, check that
fn parse_expr(expr: Expr, param_type: String, abi: &Vec<AbiEntry>, db: &SimpleParserDatabase) -> Result<AllowedCalldataArguments> {
    match expr {
        Expr::StructCtorCall(expr_struct_ctor_call) => {
            // let arg_struct_name = parse_expr_path_to_path_elements(expr_struct_ctor_call.path(db), db)?
//                 .last()
//                 .expect("Invalid struct name");
//
//             let matching_structs_vec_from_abi = find_legacy_abi_structs(arg_struct_name, abi);
//             let matching_struct_abi_definition = validate_matching_structs(&matching_structs_vec_from_abi, param)?;
//
//             let struct_args = expr_struct_ctor_call.arguments(db).arguments(db).elements(db);
//
//             let struct_args_with_values = get_struct_args_with_values(&struct_args, db).context("Found invalid expression in struct argument")?;
//
            let struct_path: Vec<String> = parse_expr_path_to_path_elements(expr_struct_ctor_call.path(db), db)?;

            let struct_path_joined = struct_path.clone().join("::");
            let structs = abi.iter().filter_map(|abi_entry| {
                if let AbiEntry::Struct(abi_struct) = abi_entry {
                    Some(abi_struct)
                } else {
                    None
                }
            }).collect::<Vec<&AbiStruct>>();
            // TODO stinky, refactor that
            let structs_from_abi: Vec<&AbiStruct> = structs
                .iter()
                .cloned()
                .filter(|&x| x.name == struct_path_joined || x.name.split("::").last() == struct_path.last().map(String::as_str))
                .collect();
            if structs_from_abi.len() > 1 {
                bail!("Found more than one struct with name {} in ABI, please specify a full path to the struct", struct_path_joined)
            } else if structs_from_abi.len() == 0 {
                bail!("Struct with name {} not found in ABI", struct_path_joined)
            }
            let struct_abi_definition = structs_from_abi.first().expect("All other possible cases have been handled");

            let struct_args = expr_struct_ctor_call.arguments(db).arguments(db).elements(db);

            let struct_args_with_values = get_struct_args_with_values(&struct_args, db).context("Found invalid expression in struct argument")?;

            if struct_args_with_values.len() != struct_abi_definition.members.len() {
                bail!("Invalid number of struct arguments in struct {} , expected {}, found {}", struct_path_joined, struct_abi_definition.members.len(), struct_args.len())
            }

            // validate if all arguments' names have corresponding names in abi
            if struct_args_with_values
                .iter()
                .map(|(arg_name, _)| arg_name.clone())
                .collect::<HashSet<ArgumentName>>() != struct_abi_definition.members.iter().map(|x| x.name.clone()).collect::<HashSet<ArgumentName>>() {
                // TODO add message which arguments are invalid
                bail!("Arguments in constructor invocation do not match struct arguments in ABI")
            }

            dbg!(&struct_args_with_values);

            let fields = struct_args_with_values.into_iter().map(|(arg_name, expr)| {
                let abi_entry = struct_abi_definition.members.iter()
                    .find(|&abi_member| abi_member.name == arg_name)
                    .expect("Arg name should be in ABI - it is checked before with HashSets");
                Ok(CalldataStructField { value: parse_expr(expr, abi_entry.r#type.clone(), abi, db)?, abi_type: abi_entry.r#type.clone()})
            }).collect::<Result<Vec<CalldataStructField>>>()?;

            Ok(AllowedCalldataArguments::Struct(CalldataStruct(fields)))
        }
        Expr::Literal(literal_number) => {
            // TODO consider turning that into a number (to simplify CairoSerialize later?)
            let (value, _) = literal_number.numeric_value_and_suffix(db).context(format!("Couldn't parse value: {}", literal_number.text(db)))?;
            // TODO handle the suffix from the number
            Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value.to_string())?))
        }
        Expr::ShortString(terminal_short_string) => {
            let value = terminal_short_string.string_value(db).context("Invalid shortstring passed as an argument")?;
            Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
        }
        Expr::String(terminal_string) => {
            let value = terminal_string.string_value(db).context("Invalid string passed as an argument")?;
            Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
        }
        Expr::False(terminal_false) => {
            let value = terminal_false.token(db).text(db).to_string();
            Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
        }
        Expr::True(terminal_true) => {
            let value = terminal_true.token(db).text(db).to_string();
            Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
        }
        // enum?
        Expr::Path(enum_expr_path) => {
            let enum_path_with_variant = parse_expr_path_to_path_elements(enum_expr_path, db)?;
            let (enum_variant_name, enum_path) = enum_path_with_variant.split_last().unwrap();
            let (enum_position, enum_variant) = parse_enum_expr_path(enum_variant_name, enum_path, abi, db)?;
            if enum_variant.r#type != "()".to_string() {
                bail!("Couldn't find variant {} in enum {}", enum_variant_name, enum_path.join("::"))
            }

            Ok(AllowedCalldataArguments::Enum(CalldataEnum{
                position: enum_position,
                argument: None,
            }))
            // tODO nice message when A {a:a} is treated as path
        }
        // Enum::Variant(10)
        Expr::FunctionCall(enum_expr_path_with_value) => {
            let enum_path_with_variant = parse_expr_path_to_path_elements(enum_expr_path_with_value.path(db), db)?;
            let (enum_variant_name, enum_path) = enum_path_with_variant.split_last().unwrap();
            let (enum_position, enum_variant) = parse_enum_expr_path(enum_variant_name, enum_path, abi, db)?;

            // When creating an enum with variant, there can be only one argument. Parsing the
            // argument inside ArgList (enum_expr_path_with_value.arguments(db).arguments(db)),
            // then popping from the vector and unwrapping safely.
            let expr = arg_list_to_exprs(enum_expr_path_with_value.arguments(db).arguments(db), db)?.pop().unwrap();
            let parsed_expr = parse_expr(expr, enum_variant.r#type.clone(), abi, db)?;

            Ok(AllowedCalldataArguments::Enum(CalldataEnum{position: enum_position, argument: Some(Box::new(parsed_expr))}))
        }
        // array![]
        Expr::InlineMacro(expr_inline_macro) => {
            // TODO improve error message
            let parsed_exprs = parse_inline_macro_expr(expr_inline_macro, db)?;

            let array_elem_type_regex = Regex::new(".*<(.*)>").unwrap();
            let abi_argument_type = array_elem_type_regex.captures(param_type.as_str())
                .context(format!("Argument of invalid type passed, expected {}, got array", param_type))?
                .get(1)
                // TODO better message
                .context(format!("Couldn't parse array element type from the ABI array parameter: {}", param_type))?
                .as_str();

            let arguments = parsed_exprs.into_iter().map(|arg| parse_expr(arg, abi_argument_type.to_string(), abi, db)).collect::<Result<Vec<AllowedCalldataArguments>>>()?;
            Ok(AllowedCalldataArguments::ArrayMacro(CalldataArrayMacro(arguments)))
        }
        Expr::Tuple(expr_list_parenthesized) => {
             let tuple_types_regex = Regex::new(r#"\(([^)]+)\)"#).unwrap();
             let tuple_types = tuple_types_regex.captures(param_type.as_str())
                 .context(format!("Argument of invalid type passed, expected {}, got a tuple", param_type))?
                 .iter()
                 .skip(1)
                 // TODO?
                 .map(|x| x.unwrap().as_str().to_owned())
                 .collect::<Vec<String>>();
             let parsed_exprs = expr_list_parenthesized.expressions(db).elements(db)
                 .into_iter()
                 .zip(tuple_types)
                 .map(|(expr, single_param)| parse_expr(expr, single_param, abi, db))
                 .collect::<Result<Vec<_>>>()?;
             Ok(AllowedCalldataArguments::Tuple(CalldataTuple(parsed_exprs)))
         }
        _ => {
            // TODO add more meaningful message, listing all possible expressions or pointing out
            // why this node is invalid.
            bail!("Unsupported expression")
        }
        // other possibilities are:
        // Expr::Binary(_) => {} - generics
        // Expr::Parenthesized(_) => {} - (single_value)
        //  Expr::Unary(_) => {}
        //  Expr::Block(_) => {}
        //  Expr::Match(_) => {}
        //  Expr::If(_) => {}
        //  Expr::Loop(_) => {}
        //  Expr::While(_) => {}
        //  Expr::ErrorPropagate(_) => {}
        //  Expr::FieldInitShorthand(_) => {}
        //  Expr::Indexed(_) => {}
        //  Expr::FixedSizeArray(_) => {}
        //  Expr::Missing(_) => {}
    }
}

fn get_struct_args_with_values(struct_args: &Vec<StructArg>, db: &SimpleParserDatabase) -> Result<Vec<(ArgumentName, Expr)>> {
    struct_args.iter().map(|elem| {
        match elem {
            // Holds info about parameter and argument in struct creation, e.g.:
            // in case of "Struct { a: 1, b: 2 }", two separate StructArgSingle hold info
            // about "a: 1" and "b: 2" respectively.
            StructArg::StructArgSingle(whole_arg) => {
                match whole_arg.arg_expr(db) {
                    // TODO add comment
                    // dunno what that is
                    // probably case when there is Struct {a, b} and there are variables a and b
                    OptionStructArgExpr::Empty(_) => {
                        bail!("Single arg, used {ident}, should be {ident}: value", ident = whole_arg.identifier(db).text(db))
                    }
                    // Holds info about the argument, e.g.: in case of "a: 1" holds info
                    // about ": 1"
                    OptionStructArgExpr::StructArgExpr(arg_value_with_colon) => {
                        Ok((whole_arg.identifier(db).text(db).to_string(), arg_value_with_colon.expr(db)))
                    }
                }
            }
            // TODO add more meaningful message
            // the part with dots in Struct { ..smth }
            StructArg::StructArgTail(struct_arg_tail) => {
                bail!("..value is not allowed")
            }
        }
    }).try_collect()
}

fn check_arg_names_equal(struct_args_with_values: &Vec<(ArgumentName, Expr)>, matching_struct_abi_definition: &LegacyStructAbiEntry) -> bool {
    struct_args_with_values
        .iter()
        .map(|(arg_name, _)| arg_name.clone())
        .collect::<HashSet<ArgumentName>>() != matching_struct_abi_definition.members.iter().map(|x| x.name.clone()).collect::<HashSet<ArgumentName>>()

}
fn parse_inline_macro_expr(expr_inline_macro: ExprInlineMacro, db: &SimpleParserDatabase) -> Result<Vec<Expr>>{
    match expr_inline_macro.path(db).elements(db).iter().last().expect("Macro must have a name") {
        Simple(simple) => {
            let macro_name = simple.ident(db).text(db);
            if macro_name != "array" {
                bail!("Invalid macro name: only array![] macro is supported, found {}!", macro_name)
            }
        }
        PathSegment::WithGenericArgs(_) => bail!("Invalid path specified: generic args in array![] macro not supported"),
    };

    let macro_arg_list = match expr_inline_macro.arguments(db) {
        WrappedArgList::BracketedArgList(args) => {
            // TODO arglist parsing here
            args.arguments(db)
        }
        WrappedArgList::ParenthesizedArgList(_) | WrappedArgList::BracedArgList(_) =>
            bail!("`array` macro supports only square brackets: array![]"),
        WrappedArgList::Missing(_) => unreachable!("If any type of parentheses is missing, then diagnostics have been reported and whole flow should have already been terminated.")
    };
    arg_list_to_exprs(macro_arg_list, db)
}

// fn parse_expr_legacy_abi(expr: Expr, param_type: LegacyFunctionArgument, abi: &Vec<LegacyContractAbiEntry>, db: &SimpleParserDatabase) -> Result<AllowedCalldataArguments> {
//     match expr {
//         Expr::StructCtorCall(expr_struct_ctor_call) => {
//             let struct_param_type = match param_type {
//                 LegacyFunctionArgument::Other(other_type) => other_type,
//                 LegacyFunctionArgument::Array(array_param_type) => bail!("Expected array type: {}, found struct argument", array_param_type.strip_suffix("*".)),
//                 LegacyFunctionArgument::Felt => bail!("Expected type: felt, found struct argument")
//             };
//             let arg_struct_name = parse_expr_path_to_path_elements(expr_struct_ctor_call.path(db), db)?
//                 .last()
//                 .expect("Invalid struct name");
//
//             let matching_structs_vec_from_abi = find_legacy_abi_structs(arg_struct_name, abi);
//             let matching_struct_abi_definition = validate_matching_structs(&matching_structs_vec_from_abi, param)?;
//
//             let struct_args = expr_struct_ctor_call.arguments(db).arguments(db).elements(db);
//
//             let struct_args_with_values = get_struct_args_with_values(&struct_args, db).context("Found invalid expression in struct argument")?;
//
//             if struct_args_with_values.len() != matching_struct_abi_definition.members.len() {
//                 bail!("Invalid number of struct arguments in struct {} , expected {}, found {}", arg_struct_name, matching_struct_abi_definition.members.len(), struct_args.len())
//             }
//
//             // validate if all arguments' names have corresponding names in abi
//             if !check_arg_names_equal(&struct_args_with_values, matching_struct_abi_definition) {
//                 // TODO add message which arguments are invalid
//                 bail!("Arguments in constructor invocation do not match struct arguments in ABI")
//             }
//
//             dbg!(&struct_args_with_values);
//
//             let fields = struct_args_with_values.into_iter().map(|(arg_name, expr)| {
//                 let abi_entry = matching_struct_abi_definition.members.iter()
//                     .find(|&abi_member| abi_member.name == arg_name)
//                     .expect("Arg name should be in ABI - it is checked before with HashSets");
//                 Ok(CalldataStructField { value: parse_expr_legacy_abi(expr, abi_entry.r#type.clone(), abi, db)?, abi_type: abi_entry.r#type.clone()})
//             }).collect::<Result<Vec<CalldataStructField>>>()?;
//
//             Ok(AllowedCalldataArguments::Struct(CalldataStruct(fields)))
//         }
//         Expr::Literal(literal_number) => {
//             let (value, suffix) = literal_number.numeric_value_and_suffix(db).context(format!("Couldn't parse value: {}", literal_number.text(db)))?;
//             if suffix.is_some() {
//                 // TODO maybe only a warning here and default to felt?
//                 bail!("Cannot use suffixes in numbers when calling legacy contracts, only felts are allowed")
//             }
//             Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new("felt".to_string(), value.to_string())?))
//         }
//         Expr::ShortString(terminal_short_string) => {
//             let value = terminal_short_string.string_value(db).context("Invalid shortstring passed as an argument")?;
//             Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new("felt".to_string(), value)?))
//         }
//         // array![] - in this case arr_len: felt, arr: felt*
//
//         Expr::InlineMacro(expr_inline_macro) => {
//             // TODO improve error message
//             let array_param_type = match param_type {
//                 LegacyFunctionArgument::Array(array_param_type) => array_param_type,
//                 LegacyFunctionArgument::Other(other_type) => bail!("Expected type: {}, found array![] argument", other_type),
//                 LegacyFunctionArgument::Felt => bail!("Expected type: felt, found array![] argument")
//             };
//             let parsed_exprs = parse_inline_macro_expr(expr_inline_macro, db)?;
//
//             let array_elem_type_regex = Regex::new(".*<(.*)>").unwrap();
//             let abi_argument_type = array_elem_type_regex.captures(array_param_type.as_str())
//                 .context(format!("Argument of invalid type passed, expected {}, got array", array_param_type))?
//                 .get(1)
//                 // TODO better message
//                 .context(format!("Couldn't parse array element type from the ABI array parameter: {}", array_param_type))?
//                 .as_str();
//
//             let arguments = parsed_exprs.into_iter().map(|arg| parse_expr_legacy_abi(arg, abi_argument_type.to_string(), abi, db)).collect::<Result<Vec<AllowedCalldataArguments>>>()?;
//             Ok(AllowedCalldataArguments::ArrayMacro(CalldataArrayMacro(arguments)))
//         }
//         Expr::Parenthesized(expr_parenthesized) => {
//             // i think in cairo0 it was possible to use tuples with single element as a type in
//             // a param
//             todo!();
//             parse_expr(expr_parenthesized.expr(db), param_type, structs, db)
//         }
//         Expr::Tuple(expr_list_parenthesized) => {
//             // TODOtuples: into one function that accepts a fn (parse_expr/parse_expr_legacy_abi)
//             let tuple_types_regex = Regex::new(r#"\(([^)]+)\)"#).unwrap();
//             let tuple_types = tuple_types_regex.captures(param_type.as_str())
//                 .context(format!("Argument of invalid type passed, expected {}, got a tuple", param_type))?
//                 .iter()
//                 .skip(1)
//                 // TODO?
//                 .map(|x| x.unwrap().as_str().to_owned())
//                 .collect::<Vec<String>>();
//             let parsed_exprs = expr_list_parenthesized.expressions(db).elements(db)
//                 .into_iter()
//                 .zip(tuple_types)
//                 .map(|(expr, single_param)| parse_expr_legacy_abi(expr, single_param, abi, db))
//                 .collect::<Result<Vec<_>>>()?;
//             Ok(AllowedCalldataArguments::Tuple(CalldataTuple(parsed_exprs)))
//         }
//         _ => {
//             // TODO add more meaningful message, listing all possible expressions or pointing out
//             // why this node is invalid.
//             bail!("Unsupported expression")
//         }
//         // Expr::String(terminal_string) => {
//         //     let value = terminal_string.string_value(db).context("Invalid string passed as an argument")?;
//         //     Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
//         // }
//         // Expr::False(terminal_false) => {
//         //     let value = terminal_false.token(db).text(db).to_string();
//         //     Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
//         // }
//         // Expr::True(terminal_true) => {
//         //     let value = terminal_true.token(db).text(db).to_string();
//         //     Ok(AllowedCalldataArguments::SingleArgument(CalldataSingleArgument::try_new(param_type, value)?))
//         // }
//         // // enum?
//         // Expr::Path(enum_expr_path) => {
//         //     let enum_path_with_variant = enum_expr_path.elements(db).iter().map(|path_segment| {
//         //         match path_segment {
//         //             PathSegment::Simple(simple) => Ok(simple.ident(db).text(db).to_string()),
//         //             // tODO better message, show the argument
//         //             PathSegment::WithGenericArgs(_) => bail!("Cannot use generic args when specifying enum path")
//         //         }
//         //     }).collect::<Result<Vec<String>>>()?;
//         //     let (enum_variant_name, enum_path) = enum_path_with_variant.split_last().unwrap();
//         //     let (enum_position, enum_variant) = parse_enum_expr_path(enum_variant_name, enum_path, abi, db)?;
//         //     if enum_variant.r#type != "()".to_string() {
//         //         bail!("Couldn't find variant {} in enum {}", enum_variant_name, enum_path.join("::"))
//         //     }
//         //
//         //     Ok(AllowedCalldataArguments::Enum(CalldataEnum{
//         //         position: enum_position,
//         //         argument: None,
//         //     }))
//         //     // tODO nice message when A {a:a} is treated as path
//         // }
//         // // Enum::Variant(10)
//         // Expr::FunctionCall(enum_expr_path_with_value) => {
//         //     let enum_path_with_variant = enum_expr_path_with_value.path(db).elements(db).iter().map(|path_segment| {
//         //         match path_segment {
//         //             PathSegment::Simple(simple) => Ok(simple.ident(db).text(db).to_string()),
//         //             // tODO better message, show the argument
//         //             PathSegment::WithGenericArgs(_) => bail!("Cannot use generic args when specifying enum path")
//         //         }
//         //     }).collect::<Result<Vec<String>>>()?;
//         //     let (enum_variant_name, enum_path) = enum_path_with_variant.split_last().unwrap();
//         //     let (enum_position, enum_variant) = parse_enum_expr_path(enum_variant_name, enum_path, abi, db)?;
//         //
//         //     // When creating an enum with variant, there can be only one argument. Parsing the
//         //     // argument inside ArgList (enum_expr_path_with_value.arguments(db).arguments(db)),
//         //     // then popping from the vector and unwrapping safely.
//         //     let expr = arg_list_to_exprs(enum_expr_path_with_value.arguments(db).arguments(db), db)?.pop().unwrap();
//         //     let parsed_expr = parse_expr(expr, enum_variant.r#type.clone(), abi, db)?;
//         //
//         //     Ok(AllowedCalldataArguments::Enum(CalldataEnum{position: enum_position, argument: Some(Box::new(parsed_expr))}))
//         // }
//         // other possibilities are:
//         // Expr::Binary(_) => {
//         // TODO remove that
//         //     error: Plugin diagnostic: `starknet::interface` functions don't support parameters that depend on the trait's generic param type.
//         //     error: Plugin diagnostic: Contract entry points cannot have generic arguments
//         // }
//
//         //  Expr::Unary(_) => {}
//         //  Expr::Block(_) => {}
//         //  Expr::Match(_) => {}
//         //  Expr::If(_) => {}
//         //  Expr::Loop(_) => {}
//         //  Expr::While(_) => {}
//         //  Expr::ErrorPropagate(_) => {}
//         //  Expr::FieldInitShorthand(_) => {}
//         //  Expr::Indexed(_) => {}
//         //  Expr::FixedSizeArray(_) => {}
//         //  Expr::Missing(_) => {}
//     }
// }
fn find_legacy_abi_fn(abi: &Vec<LegacyContractAbiEntry>, fn_name: String) -> Option<&LegacyFunctionAbiEntry> {
    abi.iter().find_map(|abi_entry| {
        if let LegacyContractAbiEntry::Function(legacy_fn) = abi_entry {
            if legacy_fn.name == fn_name {
                return Some(legacy_fn);
            }
        }
        None
    })
}

fn validate_matching_structs<'a>(matching_structs: &'a Vec<LegacyStructAbiEntry>, struct_name: &String) -> Result<&'a LegacyStructAbiEntry>{
    if matching_structs.len() > 1 {
        // TODO what happens when there's ambiguity with a struct from a dependency?
        // can that even be the case?
        bail!("Found more than one struct with name {} in ABI", struct_name)
    } else if matching_structs.len() == 0 {
        bail!("Struct with name {} not found in ABI", struct_name)
    }
    matching_structs.first().ok_or_else(|| anyhow!("Failed to find struct in legacy ABI"))
}

fn find_new_abi_fn(abi: &Vec<AbiEntry>, fn_name: String) -> Option<&AbiFunction> {
    let interfaces: Vec<&Vec<AbiEntry>> = abi.iter().filter_map(|abi_entry| {
        if let AbiEntry::Interface(interface) = abi_entry {
            return Some(&interface.items)
        }
        None
    }).collect();
    interfaces.into_iter().flatten().find_map(|interface_item| {
        if let AbiEntry::Function(func) = interface_item {
            if func.name == fn_name {
                return Some(func)
            }
        }
        None
    })
}

fn find_legacy_abi_structs(struct_name: &String, abi: &Vec<LegacyContractAbiEntry>) -> Vec<LegacyStructAbiEntry> {
    abi.iter().filter_map(|abi_entry| {
        if let LegacyContractAbiEntry::Struct(legacy_struct) = abi_entry {
            if legacy_struct.name == *struct_name {
                return Some(legacy_struct);
            }
        }
        None
    }).cloned().collect()
}

fn find_new_abi_struct(abi: &Vec<AbiEntry>, struct_name: String) -> Vec<AbiStruct> {
    abi.iter().filter_map(|abi_entry| {
        if let AbiEntry::Struct(r#struct) = abi_entry {
            if r#struct.name == *struct_name {
                return Some(r#struct);
            }
        }
        None
    }).cloned().collect()
}

fn get_expr_list(parsed_node: SyntaxNode, db: &SimpleParserDatabase) -> Vec<Expr> {
    let statement_list_node = find_input_expr_between_parentheses(parsed_node, db);
    // 123 - ExprParenthesized ( TerminalLiteralNumber )
    // 123, 123 - ExprListParenthesized ( ExprList )
    // (123) - ExprParenthesized ( ExprParenthesized )
    // (123, 123) - ExprParenthesized ( ExprListParenthesized )
    // 123, (123) - ExprListParenthesized ( ExprList )
    match statement_list_node {
        Expr::Tuple(list_of_args) => {
            // list of arguments - function accepts more than one argument
            list_of_args.expressions(db).elements(db)
        }
        Expr::Parenthesized(single_arg) => {
            vec![single_arg.expr(db)]
        }
        _ => {
            unreachable!("Due to construction of the wrapper function, other possibilities are not possible")
        }
    }
}

type AbiType = String;
type ArrayType = String;
#[derive(Debug)]
enum LegacyFunctionArgument {
    Felt,
    Array(ArrayType),
    Other(AbiType),
}


pub async fn transform_input_calldata(
    input_calldata: String,
    function_name: String,
    class_hash: FieldElement,
    client: &JsonRpcClient<HttpTransport>,
) -> Result<Vec<FieldElement>> {
    let db = SimpleParserDatabase::default();
    let parsed_node = parse_input_calldata(input_calldata, &db)?;
    let contract_class = client.get_class(BlockId::Tag(BlockTag::Latest), class_hash).await.map_err(handle_rpc_error).unwrap();

    iter_node(&parsed_node, &db, 2);
    let arguments_expr_list = get_expr_list(parsed_node, &db);

    match contract_class {
        ContractClass::Sierra(sierra_class) => {
            // TODO remove .expect() and change into pattern matching or smth
            let abi: Vec<AbiEntry> = serde_json::from_str(sierra_class.abi.as_str()).expect("Couldn't deserialize ABI received from chain");
            // dbg!(&abi);
            let called_function = find_new_abi_fn(&abi, function_name.clone()).context(format!("Function {} not found in ABI of the contract", function_name))?;
            // dbg!(&called_function);
            // TODO should it be here? or should chain validate if args list is of a valid length
            //  it's like frontend validation
            if called_function.inputs.len() != arguments_expr_list.len() {
                bail!("Invalid number of arguments, passed {}, expected {}", arguments_expr_list.len(), called_function.inputs.len())
            }

            let parsed_exprs = called_function.inputs.iter()
                .zip(arguments_expr_list)
                .map(|(param, arg)| parse_expr(arg, param.r#type.clone(), &abi, &db))
                .collect::<Result<Vec<AllowedCalldataArguments>>>()?;

            Ok(parsed_exprs.iter().flat_map(|args| args.serialize_to_vec()).map(FieldElement::from_).collect::<Vec<FieldElement>>())
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

fn parse_legacy_fn_arguments(called_function: &LegacyFunctionAbiEntry) -> Vec<LegacyFunctionArgument> {
    // Parses types from legacy ABI function - finds any arrays (arrayname_len: type, arrayname: type*)
    // and concatenates them into one type.
    let mut parsed_arguments = Vec::new();

    let mut first_iterator = called_function.inputs.iter();
    let mut second_iterator = called_function.inputs.iter();
    if let None = second_iterator.next() {
        // Argument list is empty
        return parsed_arguments
    }
    let mut iter = first_iterator.zip(second_iterator);
    // Sliding window :^)
    while let Some((fst, snd)) = iter.next() {
        if fst.name == snd.name.clone() + "_len" && fst.r#type == "felt" {
            let re = Regex::new(r#"[^*]+\*+"#).unwrap();
            let snd_type_captures = re.captures(snd.r#type.as_str().clone());

            if let None = snd_type_captures {
                // When first is a_len: felt, second is a: type (no stars meaning no array)
                parsed_arguments.push(LegacyFunctionArgument::Felt);
                continue
            } else {
                // When first argument is a_len: felt, second argument is a: type* (any number of stars)
                parsed_arguments.push(LegacyFunctionArgument::Array(snd.r#type.clone()));
                // We skip additional entry in iterator since we covered two entries at once
                iter.next();
                continue
            }
        } else {
            match fst.r#type.as_str() {
                "felt" => parsed_arguments.push(LegacyFunctionArgument::Felt),
                _ => parsed_arguments.push(LegacyFunctionArgument::Other(fst.r#type.clone()))
            }
        }
    }
    // Case when last two parameters don't represent an array
    // let (first_iterator, _): (core::slice::Iter<LegacyTypedParameter>, _) = iter.unzip();
    // if let Some(last) = first_iterator.next() {
    //     match last.r#type.as_str() {
    //         "felt" => parsed_arguments.push(LegacyFunctionArgument::Felt),
    //         _ => parsed_arguments.push(LegacyFunctionArgument::Other(last.r#type.clone()))
    //     }
    // }
    parsed_arguments
}

mod tests {
    use std::ops::Sub;
    use starknet::macros::felt;
    use starknet::providers::sequencer::models::ContractAddresses;
    use super::*;
    use shared::rpc::create_rpc_client;

    #[tokio::test]
    async fn test_adding_structs() {
        let input_calldata = "C { a: 234 }".to_string();
        // let legacy_clshsh = starknet::macros::felt!("0x028d1671fb74ecb54d848d463cefccffaef6df3ae40db52130e19fe8299a7b43");
        // let new_clshsh = starknet::macros::felt!("0x685cf8bf3f0b7ed74c9f237057ac816e76a2e6707cbf197607e8de05faedd2e");

        //external struct
        // let new_clshsh = starknet::macros::felt!("0x05ffa2ecae0cc90e3e0aa24eb3de193f071ebeed47e1f760ea2b5e78ab3d29c2");
        // A B
        let new_clshsh = starknet::macros::felt!(
            "0x0594944329306a24e6ef729812fdf0dcaccfaeca535256e554aa602218660216"
        );
        // starknet::macros::felt!("0x0234bdb2d5bfa39bec20a520101236c8b0e58a4e8b547c34ee9f9167cd690ba7");
        // let new_clshsh = starknet::macros::felt!("0x05a4da9af3ee415b9fa38a88bd80cefde5633ccd8123d79a87aa13863d8e10ad"),
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let temporary_code = format!("fn __WRAPPER_FUNC_TO_PARSE() {{ ({input_calldata}); }}");
        // parse(input_calldata, new_clshsh, &client).await;
        // dbg!(add_structs_from_abi_to_code(temporary_code).await);
    }

    // #[test]
    // fn test_parse_input_calldata() {
    //     // parse_input_calldata_test("struct SomeStruct { field: felt252 } SomeStruct { field: 0x1 }".to_string());
    //     // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { (a: { a: 252 } ); } struct A { a: felt252, }".to_string());
    //     // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { (A { a: 252 } ); }".to_string());
    //     // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { ( path::to::A<3> { a: array![1, \"a\", 'b'] }, 1, array![2] ); }".to_string());
    //     // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { ( core::macros::array![1, \"a\", 'b'] ); }".to_string());
    //     // let input_calldata = "My::Struct::Variant{a:1, b:array![], c:(1,2_u32, '3', \"4\")}".to_string();
    //     let input_calldata = "1, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999993618502788666131213697322783095070105623107215331596699973092056135872020480000000000000000_u256,'3',\"4\", (5, 6), true, array![7, 8_u32], Module::Nine{ten:11}".to_string();
    //     parse_input_calldata_test(format!{"fn __WRAPPER_FUNC_TO_PARSE__() {{ ( {input_calldata} ); }}"}.to_string());
    //     let db = SimpleParserDatabase::default();
    //     let parsed_node = parse_input_calldata(input_calldata, &db).unwrap();
    //     let parsed_calldata_arguments = get_parsed_calldata_arguments(parsed_node, &db);
    //     dbg!(&parsed_calldata_arguments);
    // }

    #[tokio::test]
    async fn test_flow() {
        let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let contract_address: FieldElement = felt!("0x0303f22f63f97d6e602da6444782f991239cf543d44cc9b9b874291552ade465");
        let input_calldata = "B { a: A{a:1}, b: 1234 }".to_string();
        let fn_name = "b_fn".to_string();

        let output = transform_input_calldata(input_calldata, fn_name, contract_address, &client).await.unwrap();
        dbg!(&output);
        let serialized: Vec<Felt252> = output.iter().flat_map(|x| x.serialize_to_vec()).collect();
        dbg!(&serialized);
    }
    #[tokio::test]
    async fn test_legacy_abi() {
        // let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let client = create_rpc_client("https://free-rpc.nethermind.io/mainnet-juno").unwrap();
        let class_hash_legacy: FieldElement = felt!("0x0157d87bdad1328cbf429826a83545f6ffb6505138983885a75997ee2c49e66b");
        let contract = client.get_class(BlockId::Tag(BlockTag::Latest), class_hash_legacy).await.unwrap();
        if let ContractClass::Legacy(legacy) = contract {
            // dbg!(legacy.clone().abi.unwrap());
            for entry in &legacy.abi.clone().unwrap() {
                match entry {
                    LegacyContractAbiEntry::Function(func) => {
                        dbg!(&func.name);
                        dbg!(parse_legacy_fn_arguments(func));
                    }
                    LegacyContractAbiEntry::Event(_) => {continue}
                    LegacyContractAbiEntry::Struct(_) => {continue}
                }
            }
        }
    }

    #[test]
    fn felt_test() {
        let felt = Felt252::new(0);
        let other = felt.sub(Felt252::new(1));
        dbg!(other);
    }
}
// SyntaxKind::TerminalLiteralNumber
// SyntaxKind::TerminalShortString
// SyntaxKind::TerminalString
// SyntaxKind::ExprListParenthesized - tuple
// SyntaxKind::TerminalTrue | SyntaxKind::TerminalFalse
// SyntaxKind::ExprPath - MyEnum::A
// SyntaxKind::ExprBinary - A<3>{}
