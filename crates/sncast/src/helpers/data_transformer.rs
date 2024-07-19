// TODO remove that
#![allow(dead_code, unused_imports, unused_variables)]

use crate::handle_rpc_error;
use anyhow::{anyhow, Context, Error, Result};
use cairo_lang_diagnostics::{DiagnosticsBuilder, Maybe};
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileKind, FileLongId, VirtualFile};
use cairo_lang_parser::utils::get_syntax_root_and_diagnostics;
use cairo_lang_parser::{parser::Parser, utils::SimpleParserDatabase};
use cairo_lang_syntax::node::ast::PathSegment::Simple;
use cairo_lang_syntax::node::ast::{ModuleItem, ModuleItemList, StatementList};
use cairo_lang_syntax::node::db::SyntaxGroup;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{SyntaxNode, TypedSyntaxNode};
use itertools::Itertools;
use shared::rpc::create_rpc_client;
use starknet::core::types::contract::{AbiEntry, AbiStruct};
use starknet::core::types::{
    BlockId, BlockTag, CompressedLegacyContractClass, ContractClass, LegacyContractAbiEntry,
    LegacyStructAbiEntry,
};
use starknet::providers::jsonrpc::HttpTransport;
use starknet::providers::{JsonRpcClient, Provider};
use starknet_crypto::FieldElement;
use std::io;
use std::io::Write;
use std::ops::Add;
use std::sync::Arc;

#[tokio::test]
async fn fetch_abi_test() {
    // let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
    let client = create_rpc_client("https://starknet-mainnet.public.blastapi.io/rpc/v0_7").unwrap();
    let class = client
        .get_class(
            BlockId::Tag(BlockTag::Latest),
            // starknet::macros::felt!("0x685cf8bf3f0b7ed74c9f237057ac816e76a2e6707cbf197607e8de05faedd2e"),
            // starknet::macros::felt!("0x0234bdb2d5bfa39bec20a520101236c8b0e58a4e8b547c34ee9f9167cd690ba7"),
            starknet::macros::felt!(
                "0x05a4da9af3ee415b9fa38a88bd80cefde5633ccd8123d79a87aa13863d8e10ad"
            ),
        )
        .await
        .map_err(handle_rpc_error)
        .unwrap();
    dbg!(&class);
    if let ContractClass::Sierra(cls) = class {
        let loaded_abi: Vec<AbiEntry> = serde_json::from_str(cls.abi.as_str()).unwrap();
        println!();
    }
    let legacy_class = client
        .get_class(
            BlockId::Tag(BlockTag::Latest),
            starknet::macros::felt!(
                "0x028d1671fb74ecb54d848d463cefccffaef6df3ae40db52130e19fe8299a7b43"
            ),
        )
        .await
        .map_err(handle_rpc_error)
        .unwrap();
    dbg!(&legacy_class);
}

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
    dbg!(&node.kind(&simple_db));
    dbg!(&node.text(&simple_db));
    // dbg!(&node.span_without_trivia(&simple_db));
    // dbg!(&node.green_node(&simple_db));
    // dbg!(&node.get_terminal_token(&simple_db));
    // dbg!(&node.get_text(&simple_db));
    let mut preorder = node.preorder(&simple_db);
    dbg!(&preorder.next());
    // dbg!(&preorder.next());
    // dbg!(&preorder.next());
    dbg!(&node.clone().get_text_without_trivia(&simple_db));
    // let typed_syntax_node = TypedSyntaxNode::from_syntax_node(&simple_db, node.clone());
    let element_list = ModuleItemList::from_syntax_node(&simple_db, node.clone());
    let children = simple_db.get_children(node.clone());
    let child = &children.iter().next().unwrap().green_node(&simple_db);
    dbg!(child.children());
    iter_node(&node, &simple_db, 0);
    // let descendants = node.descendants(&simple_db).collect_vec();
    // for i in node.descendants(&simple_db) {
    //     dbg!(&i.kind(&simple_db));
    //     dbg!(&i.text(&simple_db).unwrap_or("\t\t\terror".parse().unwrap()));
    // }
    dbg!();
}

fn iter_node(node: &SyntaxNode, simple_db: &SimpleParserDatabase, spaces: usize) {
    let kind = node.kind(simple_db);
    let text = node
        .text(simple_db)
        .unwrap_or("00000000000".parse().unwrap());
    let spaces_string = " ".to_string().repeat(spaces * 2);
    println!("{spaces_string}{kind}");
    println!("{spaces_string}{text}");
    println!("                         ");
    io::stdout().flush().expect("TODO: panic message");
    let children = simple_db.get_children(node.clone());
    for i in children.iter() {
        iter_node(i, simple_db, spaces + 1);
    }
}

// TODO add support for impls? should it be done?
// TODO fix external structs - not sure if this is necessary since we don't add them to code tho
fn parse_input_calldata(
    input_calldata: String,
    simple_db: &SimpleParserDatabase,
) -> Result<SyntaxNode> {
    let temporary_code = Arc::new(format!(
        "fn __WRAPPER_FUNC_TO_PARSE__() {{ ({input_calldata}); }}"
    ));
    let virtual_file = simple_db.intern_file(FileLongId::Virtual(VirtualFile {
        parent: None,
        name: "parser_input".into(),
        content: temporary_code.clone(),
        code_mappings: Default::default(),
        kind: FileKind::Module,
    }));
    let (node, diagnostics) =
        get_syntax_root_and_diagnostics(simple_db, virtual_file, temporary_code.as_str());
    // TODO ugly, fix that
    match diagnostics.check_error_free() {
        Ok(_) => Ok(node),
        Err(_) => {
            // TODO improve error message
            Err(anyhow!(format!(
                "Invalid Cairo expression found in input calldata:\n{}",
                diagnostics.format(simple_db)
            )))
        }
    }
}

fn find_expr_list_parenthesized(node: SyntaxNode, simple_db: &SimpleParserDatabase) -> SyntaxNode {
    // TODO fix this heuristic? or add a comment explaining that
    let module_item_list = &simple_db.get_children(node)[0];
    let function_with_body = &simple_db.get_children(module_item_list.clone())[0];
    let expr_block = &simple_db.get_children(function_with_body.clone())[3];
    let statement_list = &simple_db.get_children(expr_block.clone())[1];
    let statement_expr = &simple_db.get_children(statement_list.clone())[0];
    // TODO assert that this is ExprListParenthesized if heuristic stays
    simple_db.get_children(statement_expr.clone())[1].clone()
}

struct CalldataStructField {
    field_name: String,
    value: AllowedCalldataArguments,
}

struct CalldataStruct {
    name: String,
    // TODO don't forget to validate if length of fields is the same as number of args in struct
    fields: Vec<CalldataStructField>,
}

enum AllowedCalldataArguments {
    Struct(CalldataStruct),
    // TODO validate if all arguments for the macro invocation are the same type
    ArrayMacro(Vec<String>),
    SingleArgument(String),
}

fn get_parsed_calldata_arguments(parsed_node: SyntaxNode, simple_db: &SimpleParserDatabase) {
    let statement_list_node = find_expr_list_parenthesized(parsed_node, simple_db);
    dbg!(&statement_list_node.kind(simple_db));
    // will be in form TerminalLParen, Terminalxxx/ExprList, TerminalRParen
    let calldata_arguments = simple_db.get_children(statement_list_node);
    let expr_between_parentheses = &calldata_arguments[1];
    match expr_between_parentheses.kind(simple_db) {
        SyntaxKind::ExprList => {
            // TODO add map with parsing function after step_by
            let arguments: Vec<&SyntaxNode> = simple_db
                .get_children(expr_between_parentheses.clone())
                .iter()
                .step_by(2)
                .collect();
        }
        // TODO add other allowed kinds - string literals (long, cairostring), numbers
        // TODO add array![] - check its name during validation
        _ => {}
    }
    for i in calldata_arguments.iter() {
        dbg!(&i.kind(simple_db));
    }
}

async fn transform_input_calldata(
    input_calldata: String,
    contract_address: FieldElement,
    client: &JsonRpcClient<HttpTransport>,
) -> Result<()> {
    let simple_db = SimpleParserDatabase::default();
    // parse
    let parsed_node = parse_input_calldata(input_calldata, &simple_db)?;

    // get StatementList from fn body
    //  get all args from it
    let parsed_calldata_arguments = get_parsed_calldata_arguments(parsed_node, &simple_db);

    //  check them against abi
    //
    Ok(())
}

mod tests {
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

    #[test]
    fn test_parse_input_calldata() {
        // parse_input_calldata_test("struct SomeStruct { field: felt252 } SomeStruct { field: 0x1 }".to_string());
        // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { (a: { a: 252 } ); } struct A { a: felt252, }".to_string());
        // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { (A { a: 252 } ); }".to_string());
        // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { ( A { a: array![1, \"a\", 'b'] }, 1, array![2] ); }".to_string());
        let input_calldata = "C { a: 234 }".to_string();
        let simple_db = SimpleParserDatabase::default();
        let parsed_node = parse_input_calldata(input_calldata, &simple_db).unwrap();
        let parsed_calldata_arguments = get_parsed_calldata_arguments(parsed_node, &simple_db);
    }
}
