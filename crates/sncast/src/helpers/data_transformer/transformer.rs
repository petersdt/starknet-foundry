use crate::handle_rpc_error;
use anyhow::{bail, Context, Result};
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileKind, FileLongId, VirtualFile};
use cairo_lang_parser::utils::{get_syntax_root_and_diagnostics, SimpleParserDatabase};
use cairo_lang_syntax::node::ast::{
    Expr, FunctionWithBody, ModuleItem, Statement, StatementExpr, SyntaxFile,
};
use cairo_lang_syntax::node::{SyntaxNode, TypedSyntaxNode};
use starknet::core::types::contract::{AbiEntry, AbiFunction, StateMutability};
use starknet::core::types::{BlockId, BlockTag, ContractClass};
use starknet::providers::jsonrpc::HttpTransport;
use starknet::providers::{JsonRpcClient, Provider};
use starknet_crypto::FieldElement;
use std::sync::Arc;

/// Finds ABI constructor and turns it into [`AbiFunction`] to simplify whole flow later
/// ([`AbiConstructor`] has less fields, but both have `name` and `inputs`)
fn find_new_abi_constructor(abi: &[AbiEntry]) -> Option<AbiFunction> {
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

fn find_new_abi_fn(abi: &[AbiEntry], fn_name: &String) -> Option<AbiFunction> {
    if fn_name == "constructor" {
        return find_new_abi_constructor(abi);
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

            todo!();
        }
        ContractClass::Legacy(_legacy_class) => {
            todo!("Finish adding legacy ABI handling");
        }
    };
    todo!()
}
