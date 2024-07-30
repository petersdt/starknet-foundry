// TODO remove that
#![allow(dead_code, unused_imports, unused_variables)]

use std::any::{Any, TypeId};
use std::env::args;
use std::fmt::format;
use crate::handle_rpc_error;
use anyhow::{anyhow, bail, Context, Error, Result};
use cairo_lang_diagnostics::{DiagnosticsBuilder, Maybe};
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileKind, FileLongId, VirtualFile};
use cairo_lang_parser::utils::get_syntax_root_and_diagnostics;
use cairo_lang_parser::{parser::Parser, utils::SimpleParserDatabase};
use cairo_lang_syntax::node::ast::PathSegment::Simple;
use cairo_lang_syntax::node::ast::{ArgClause, Expr, ExprInlineMacro, ExprList, ExprListParenthesized, ExprParenthesized, ExprPath, FunctionWithBody, ModuleItem, ModuleItemList, OptionStructArgExpr, PathSegment, Statement, StatementExpr, StatementList, StructArg, SyntaxFile, TerminalLiteralNumber, TerminalShortString, TerminalString, WrappedArgList};
use cairo_lang_syntax::node::db::SyntaxGroup;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{SyntaxNode, Token, TypedSyntaxNode};
use itertools::Itertools;
use shared::rpc::create_rpc_client;
use starknet::core::types::contract::{AbiEntry, AbiFunction, AbiNamedMember, AbiStruct};
use starknet::core::types::{BlockId, BlockTag, CompressedLegacyContractClass, ContractClass, FlattenedSierraClass, LegacyContractAbiEntry, LegacyFunctionAbiEntry, LegacyStructAbiEntry, LegacyTypedParameter, U256};
use starknet::providers::jsonrpc::HttpTransport;
use starknet::providers::{JsonRpcClient, Provider};
use starknet_crypto::FieldElement;
use std::io;
use std::io::Write;
use std::ops::{Add, Deref, Sub};
use std::sync::Arc;
use cairo_felt::{Felt252, felt_str};
use cairo_vm::types::errors::program_errors::ProgramError::Parse;
use smol_str::SmolStr;
use url::form_urlencoded::parse;
use regex::Regex;
use serde::Serialize;
use conversions::byte_array::ByteArray;
use conversions::serde::serialize::{BufferWriter, CairoSerialize, SerializeToFeltVec};
use conversions::u256::CairoU256;
use crate::response::structs::Felt;

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
struct CalldataStructField {
    field_name: String,
    value: AllowedCalldataArguments,
}

#[derive(Debug)]
struct CalldataStruct {
    name_with_module_path: Vec<String>,
    // TODO don't forget to validate if length of fields is the same as number of args in struct
    fields: Vec<CalldataStructField>,
}

#[derive(Debug)]
struct CalldataArrayMacro {
    // TODO remove name and validate that while parsing the tree
    name_with_module_path: Vec<String>,
    arguments: Vec<AllowedCalldataArguments>
}

#[derive(Debug)]
struct CalldataEnum {
    name_with_module_path: Vec<String>,
    argument: Option<Box<AllowedCalldataArguments>>,
}

#[derive(Debug)]
struct CalldataSingleArgument {
}

#[derive(Debug)]
enum AllowedCalldataArguments {
    Struct(CalldataStruct),
    // TODO validate if all arguments for the macro invocation are the same type
    ArrayMacro(CalldataArrayMacro),
    Enum(CalldataEnum),
    // TODO rename to BasicType or smth
    SingleArgument(String),
    Tuple(Vec<AllowedCalldataArguments>),
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

fn parse_expr(expr: Expr, db: &SimpleParserDatabase) -> Result<AllowedCalldataArguments> {
    match expr {
        Expr::StructCtorCall(expr_struct_ctor_call) => {
            // two possibilities here: PathSegmentWithGenericArgs and PathSegmentSimple
            // it's not possible to specify generic args when using as module specification
            // TODO check if it is true
            let name_with_module_path = expr_struct_ctor_call.path(db).elements(db).iter().filter_map(|p| match p {
                Simple(segment) => {
                    Some(segment.ident(db).token(db).text(db).to_string())
                }
                _ => {
                    None
                }
            }).collect();
            let arguments_list = expr_struct_ctor_call.arguments(db).arguments(db);

            if arguments_list.elements(db).iter().any(|elem|
                match elem {
                    StructArg::StructArgSingle(arg_single) => {
                        match arg_single.arg_expr(db) {
                            OptionStructArgExpr::Empty(optionstructarexpr) => {
                                dbg!(&elem);
                                dbg!(&arg_single);
                                dbg!(&optionstructarexpr);
                                // bail!("Invalid expression ");
                                true
                            }
                            OptionStructArgExpr::StructArgExpr(struct_arg_expr) => {
                                false
                            }
                        }
                    }
                    StructArg::StructArgTail(arg_tail) => {
                        // bail!("Invalid expression ");
                        true
                    }
                }
            ) {
                bail!("Invalid expression ");
            }


            let fields = arguments_list.elements(db).iter().filter_map(|arg|
                match arg {
                    StructArg::StructArgSingle(arg_single) => {
                        match arg_single.arg_expr(db) {
                            OptionStructArgExpr::Empty(_) => None,
                            OptionStructArgExpr::StructArgExpr(struct_arg_expr) => {
                                Some(CalldataStructField { field_name: arg_single.identifier(db).token(db).text(db).to_string(), value: parse_expr(struct_arg_expr.expr(db), db).unwrap()})
                            }
                        }
                    }
                    StructArg::StructArgTail(_) => None
                }

            ).collect();
            Ok(AllowedCalldataArguments::Struct(CalldataStruct {name_with_module_path, fields }))
        }
        Expr::Literal(literal_number) => {
            // TODO consider turning that into a number (to simplify CairoSerialize later?)
            Ok(AllowedCalldataArguments::SingleArgument(literal_number.token(db).text(db).to_string()))
        }
        Expr::ShortString(terminal_short_string) => {
            Ok(AllowedCalldataArguments::SingleArgument(terminal_short_string.token(db).text(db).to_string()))
        }
        Expr::String(terminal_string) => {
            Ok(AllowedCalldataArguments::SingleArgument(terminal_string.token(db).text(db).to_string()))
        }
        Expr::False(terminal_false) => {
            Ok(AllowedCalldataArguments::SingleArgument(terminal_false.token(db).text(db).to_string()))
        }
        Expr::True(terminal_true) => {
            Ok(AllowedCalldataArguments::SingleArgument(terminal_true.token(db).text(db).to_string()))
        }
        Expr::Parenthesized(expr_parenthesized) => {
            parse_expr(expr_parenthesized.expr(db), db)
        }
        Expr::Path(expr_path) => {
            // enum?
            todo!("Finish adding enums");
        }
        Expr::FunctionCall(_) => {
            // Enum::Variant(10)
            todo!("Finish adding enums with arguments");
        }
        Expr::Binary(_) => {
            // generics (enums and structs)
            todo!("Finish adding generics");
        }
        // array![]
        Expr::InlineMacro(expr_inline_macro) => {
            match expr_inline_macro.arguments(db) {
                WrappedArgList::BracketedArgList(arg_list_bracketed) => {
                    // TODO fix that only items without ref/mut are accepted and are ArgClause::Unnamed
                    let arg_list_elements = arg_list_bracketed.arguments(db).elements(db);
                    if arg_list_elements.iter().any(|arg|
                        !arg.modifiers(db).elements(db).is_empty() || match arg.arg_clause(db) {
                            ArgClause::Unnamed(_) => false,
                            ArgClause::Named(_) | ArgClause::FieldInitShorthand(_) => true
                        }
                    ) {
                        bail!("`array` macro does not support named args, ")
                    }
                    let arguments = arg_list_elements.iter().filter_map(|arg| match arg.arg_clause(db) {
                        ArgClause::Unnamed(arg_clause_unnamed) => {
                            parse_expr(arg_clause_unnamed.value(db), db).ok()
                        },
                        ArgClause::Named(_) | ArgClause::FieldInitShorthand(_) => None
                    }).collect();
                    let name_with_module_path = expr_inline_macro.path(db).elements(db).iter().filter_map(|p| match p {
                        Simple(segment) => {
                            Some(segment.ident(db).token(db).text(db).to_string())
                        }
                        _ => {
                            None
                        }
                    }).collect();
                    Ok(AllowedCalldataArguments::ArrayMacro(CalldataArrayMacro { name_with_module_path, arguments } ))
                }
                WrappedArgList::ParenthesizedArgList(_) | WrappedArgList::BracedArgList(_) => {
                    bail!("Macro `array` does only support square brackets: array![]")
                }
                WrappedArgList::Missing(_) => {
                    unreachable!("If any type of parentheses is missing, then diagnostics have been reported and whole flow should have already been terminated.")
                }
            }
        }
         Expr::Tuple(expr_list_parenthesized) => {
             let parsed_exprs = expr_list_parenthesized.expressions(db).elements(db).into_iter().map(|expr| parse_expr(expr, db)).collect::<Result<Vec<_>>>()?;
             Ok(AllowedCalldataArguments::Tuple(parsed_exprs))
         }

        _ => {
            // TODO add more meaningful message, listing all possible expressions or pointing out
            // why this node is invalid.
            bail!("Unsupported expression")
        }
        // other possibilities are:
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

// fn parse_node(node: SyntaxNode, db: &SimpleParserDatabase) -> Result<AllowedCalldataArguments> {
//     // ExprPath jako nazwa danej rzeczy (macro, struct,)
//     match node.kind(db) {
//         SyntaxKind::ExprStructCtorCall => {
//             // TODO handle PathSegmentSimple (path::to::A),
//             // generics and combination of both
//             let node_name_with_modules = resolve_name_with_module_path(node.clone(), db);
//
//         },
//         SyntaxKind::ExprInlineMacro => {
//             // even though module name is parsed here, we only allow for array! macro later on
//             let name_with_module_path = resolve_name_with_module_path(node.clone(), db);
//             let expr_inline_macro = ExprInlineMacro::from_syntax_node(db, node);
//             let arguments = match expr_inline_macro.arguments(db) {
//                 // TODO can it be done nicer?
//                 WrappedArgList::BracketedArgList(args) => {
//                     args.arguments(db)
//                 }
//                 WrappedArgList::ParenthesizedArgList(args) => {
//                     args.arguments(db)
//                 }
//                 WrappedArgList::BracedArgList(args) => {
//                     args.arguments(db)
//                 }
//                 WrappedArgList::Missing(_) => {
//                     unreachable!("If any type of parentheses is missing, then diagnostics have been reported and whole flow should have already been terminated.")
//                 }
//             }.deref().elements(db);
//             // TODO fix that
//             if arguments.iter().any(|arg|
//                 arg.modifiers(db).deref().elements(db).is_empty() ||
//                     match arg.arg_clause(db) {
//                         ArgClause::Named(_) => false,
//                         _ => true
//                     }
//             ) {
//                 bail!("Using modifiers (mut, ref) or named arguments in array! is forbidden");
//             }
//             // Arg type
//             //TODO map to ArgClause::Unnamed and get .value(simple_db)
//             Ok(AllowedCalldataArguments::ArrayMacro(CalldataMacro { name_with_module_path, arguments: arguments.iter().map() }))
//         }
//         SyntaxKind::TerminalLiteralNumber => {
//             Ok(AllowedCalldataArguments::SingleArgument(TerminalLiteralNumber::from_syntax_node(db, node).token(db).text(db).to_string()))
//         }
//         SyntaxKind::TerminalShortString => {
//             Ok(AllowedCalldataArguments::SingleArgument(TerminalShortString::from_syntax_node(db, node).token(db).text(db).to_string()))
//         }
//         SyntaxKind::TerminalString => {
//             Ok(AllowedCalldataArguments::SingleArgument(TerminalString::from_syntax_node(db, node).token(db).text(db).to_string()))
//         }
//         SyntaxKind::ExprListParenthesized => {
//             // tuple
//             let expr_list_parenthesized = ExprListParenthesized::from_syntax_node(db, node);
//             let expressions = expr_list_parenthesized.expressions(db).elements(db).map
//
//
//         }
//         SyntaxKind::TerminalTrue => {
//             Ok(AllowedCalldataArguments::SingleArgument("true".to_string()))
//         }
//         SyntaxKind::TerminalFalse => {
//             Ok(AllowedCalldataArguments::SingleArgument("false".to_string()))
//         }
//         // TODO add enums
//         _ => {
//             // TODO add more meaningful message, listing all possible expressions or pointing out
//             // why this node is invalid.
//             bail!("Unsupported expression")
//         }
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

fn find_legacy_abi_struct(abi: &Vec<LegacyContractAbiEntry>, struct_name: String) -> Option<&LegacyStructAbiEntry> {
    abi.iter().find_map(|abi_entry| {
        if let LegacyContractAbiEntry::Struct(legacy_struct) = abi_entry {
            if legacy_struct.name == struct_name {
                return Some(legacy_struct);
            }
        }
        None
    })
}

fn find_new_abi_fn(abi: &Vec<AbiEntry>, fn_name: String) -> Option<&AbiFunction> {
    abi.iter().find_map(|abi_entry| {
        if let AbiEntry::Function(func) = abi_entry {
            if func.name == fn_name {
                return Some(func);
            }
        }
        None
    })
}

fn find_new_abi_struct(abi: &Vec<AbiEntry>, struct_name: String) -> Option<&AbiStruct> {
    abi.iter().find_map(|abi_entry| {
        if let AbiEntry::Struct(r#struct) = abi_entry {
            if r#struct.name == struct_name {
                return Some(r#struct);
            }
        }
        None
    })
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


// TODO rename this function to parse_calldata_args or smth, get_... doesn't work here
fn get_parsed_calldata_arguments(parsed_node: SyntaxNode, contract_class: ContractClass, db: &SimpleParserDatabase) -> Result<Vec<AllowedCalldataArguments>> {
    // let statement_list_node = find_input_expr_between_parentheses(parsed_node, db);
    //
    // // dbg!(&statement_list_node.as_syntax_node().kind(db));
    // dbg!(&statement_list_node);
    // // will be in form TerminalLParen, Terminalxxx/ExprList, TerminalRParen
    // let calldata_arguments = db.get_children(statement_list_node.as_syntax_node());
    // let expr_between_parentheses = calldata_arguments[1].clone();
    // for i in calldata_arguments.iter() {
    //     dbg!(&i.kind(db));
    // }
    //
    // match expr_between_parentheses.kind(db) {
    //     // 123 - ExprParenthesized ( TerminalLiteralNumber )
    //     // 123, 123 - ExprListParenthesized ( ExprList )
    //     // (123) - ExprParenthesized ( ExprParenthesized )
    //     // (123, 123) - ExprParenthesized ( ExprListParenthesized )
    //     // 123, (123) - ExprListParenthesized ( ExprList )
    //     SyntaxKind::ExprListParenthesized => {
    //         let expr_list_parenthesized = ExprListParenthesized::from_syntax_node(db, expr_between_parentheses);
    //         let parsed_exprs = expr_list_parenthesized.expressions(db).elements(db).into_iter().map(|expr| parse_expr(expr, db)).collect::<Result<Vec<_>>>()?;
    //         Ok(ParsedCalldataArgument::Single(AllowedCalldataArguments::Tuple(parsed_exprs)))
    //     }
    //     SyntaxKind::ExprList => {
    //         let expr_list = ExprList::from_syntax_node(db, expr_between_parentheses);
    //         let args_list = expr_list.elements(db).into_iter().map(|expr| parse_expr(expr, db)).collect::<Result<Vec<_>>>()?;
    //         Ok(ParsedCalldataArgument::List(args_list))
    //     }
    //     // TODO add other allowed kinds - string literals (long, cairostring), numbers
    //     // TODO add array![] - check its name during validation
    //
    //     // TODO move that to the branch below
    //     // and add all possible SyntaxKinds we'll support to the branch below
    //     SyntaxKind::ExprParenthesized => {
    //         let expr_parenthesized = ExprParenthesized::from_syntax_node(db, expr_between_parentheses);
    //         let parsed_expr = parse_expr(expr_parenthesized.expr(db), db)?;
    //         Ok(ParsedCalldataArgument::Single(parsed_expr))
    //         // expr_parenthesized.expr(db)
    //         // TODO add map with parsing function after step_by
    //         // let arguments: Vec<&SyntaxNode> = simple_db
    //         //     .get_children(expr_between_parentheses.clone())
    //         //     .iter()
    //         //     .step_by(2)
    //         //     .collect();
    //     }
    //     _ => {
    //         Ok(ParsedCalldataArgument::Single(parse_expr(Expr::from_syntax_node(db, expr_between_parentheses), db)?))
    //     }
    // }
    let statement_list_node = find_input_expr_between_parentheses(parsed_node, db);
    // 123 - ExprParenthesized ( TerminalLiteralNumber )
    // 123, 123 - ExprListParenthesized ( ExprList )
    // (123) - ExprParenthesized ( ExprParenthesized )
    // (123, 123) - ExprParenthesized ( ExprListParenthesized )
    // 123, (123) - ExprListParenthesized ( ExprList )
    let args = match statement_list_node {
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
    };


    let parsed_args = match statement_list_node {
        Expr::Tuple(list_of_args) => {
            // list of arguments - function accepts more than one argument
            let parsed_args = list_of_args.expressions(db).elements(db).into_iter().map(|expr| parse_expr(expr, db)).collect::<Result<Vec<_>>>()?;
            Ok(parsed_args)
        }
        Expr::Parenthesized(single_arg) => {
            // single argument - function accepts only one argument
            let parsed_arg = parse_expr(single_arg.expr(db), db)?;
            Ok(vec![parsed_arg])
        }
        _ => {
            unreachable!("Due to construction of the wrapper function, other possibilities are not possible")
        }
    };
    parsed_args
}


macro_rules! match_serialize_branch {
    ($id:ident, $type:ty) => {
        // TODO add error message
        //                       vvv
        Ok($id.parse::<$type>().unwrap().serialize_to_vec())
    }
}
fn serialize_single_value(value_type: &String, value: String) -> Result<Vec<Felt252>> {
    // felt252
    // i8 - i128
    // u8 - u128
    // u256
    // TODO u512
    // bool
    // shortstring
    // string (ByteArray)

    //TODO check suffixes, like ..._u8 etc.
    // "8".parse::<u32>().as_ref().map(SerializeToFeltVec::serialize_to_vec);
    let proper_value_type = value_type.split("::").last().unwrap();
    match proper_value_type {
        "u8" => {
            match_serialize_branch!(value, u8)
        },
        "u16" => {
            match_serialize_branch!(value, u16)
        },
        "u32" => {
            match_serialize_branch!(value, u32)
        },
        "u64" => {
            match_serialize_branch!(value, u64)
        },
        "u128" => {
            match_serialize_branch!(value, u128)
        },
        "i8" => {
            match_serialize_branch!(value, i8)
        },
        "i16" => {
            match_serialize_branch!(value, i16)
        },
        "i32" => {
            match_serialize_branch!(value, i32)
        },
        "i64" => {
            match_serialize_branch!(value, i64)
        },
        "i128" => {
            match_serialize_branch!(value, i128)
        },
        "u256" => {
            Ok(CairoU256::from_bytes(value.as_bytes()).serialize_to_vec())
        },
        "felt252" => {
            Ok(felt_str!(value).serialize_to_vec())
        },
        "bool" => {
            match_serialize_branch!(value, bool)
        },
        "ByteArray" => {
            Ok(ByteArray::from(value.as_str()).serialize_to_vec())
        }
        _ => {
            // TODO add more meaningful message
            bail!("Unsupported type")
        }
    }
    // Ok(vec![])
    // najpierw na Felt252
    // pozniej FieldElement::from_() do FieldElement i to do calla w cascie
}

async fn validate_against_abi(parsed_calldata: Vec<AllowedCalldataArguments>, function_name: String, contract_address: FieldElement, client: &JsonRpcClient<HttpTransport>, ) -> Result<()>{
    let class = client
        .get_class(
            BlockId::Tag(BlockTag::Latest),
            contract_address
        )
        .await
        .map_err(handle_rpc_error)
        .unwrap();
    match class {
        ContractClass::Sierra(sierra_class) => {
            let loaded_abi: Vec<AbiEntry> = serde_json::from_str(sierra_class.abi.as_str()).unwrap();
            let function_from_abi = match loaded_abi.iter().find(|x|
                if let AbiEntry::Function(abi_func) = x {
                    abi_func.name == function_name
                } else {
                    false
                }
            ) {
                Some(AbiEntry::Function(abi_fn)) => {
                    abi_fn
                },
                // TODO maybe include into the last branch? if something bad
                Some(_) => unreachable!("It shouldn't be reached no matter what"),
                None => {
                    bail!("Function with name {} not found in contract ABI", function_name)
                }
            };
            if parsed_calldata.len() != function_from_abi.inputs.len() {
                bail!("Invalid length of input calldata, expected {}, got {}", function_from_abi.inputs.len(), parsed_calldata.len())
            }
            let serialized_values: Vec<Felt252> = vec![];
            for (parameter, argument) in function_from_abi.inputs.iter().zip(parsed_calldata) {
                match argument {
                    AllowedCalldataArguments::Struct(struct_arg) => {
                        let struct_from_abi = match loaded_abi.iter().find(|x|
                            if let AbiEntry::Struct(abi_struct) = x {

                                // TODO do postfix validation
                                abi_struct.name == struct_arg.name_with_module_path
                            } else {
                                false
                            }
                        ) {
                            Some(AbiEntry::Struct(abi_struct)) => {
                                abi_struct
                            },
                            Some(_) => unreachable!("It shouldn't be reached no matter what"),
                            None => {
                                bail!("Struct with name {} not found in contract ABI", struct_arg.name_with_module_path.last().unwrap())

                            }
                        };
                        // 1. check if name is valid
                        // 2.

                    }
                    AllowedCalldataArguments::ArrayMacro(array_arg) => {
                        let re = Regex::new("(.*)<(.*)>").unwrap();
                        if let Some(caps) = re.captures(parameter.r#type.as_str()) {

                        }
                    }
                    AllowedCalldataArguments::Enum(enum_arg) => {
                        todo!();
                    }
                    AllowedCalldataArguments::SingleArgument(single_arg) => {
                        serialize_single_value(&parameter.r#type, single_arg);
                    }
                    AllowedCalldataArguments::Tuple(tuple_arg) => {

                    }
                }
            }

        }
        ContractClass::Legacy(legacy_class) => {
            // if legacy_class.abi.is_none() {
            //     // TODO what in case when ABI is not found, but the whole contract is valid?
            //     // improve error msg
            //     bail!("ABI not available")
            // }
            let loaded_abi = legacy_class.abi.context("ABI not available").unwrap();
            let function_from_abi = match loaded_abi.iter().find(|x|
                if let LegacyContractAbiEntry::Function(abi_func) = x {
                    abi_func.name == function_name
                } else {
                    false
                }
            ) {
                Some(LegacyContractAbiEntry::Function(abi_fn)) => {
                    abi_fn
                },
                _ => {
                    bail!("Function with name {} not found in contract ABI", function_name)
                }
            };

        }
    }
    Ok(())
}

// trait CommonAbiTrait<Entry, Fn, Struct> {
//     fn abi(&self) -> Vec<Entry>;
//     fn find_func(&self, func_name: String) -> Option<&Fn>;
//     fn find_struct(&self, struct_name: String) -> Option<&Struct>;
// }
//
// impl CommonAbiTrait<AbiEntry, AbiFunction, AbiStruct> for FlattenedSierraClass {
//     fn abi(&self) -> Vec<AbiEntry> {
//         serde_json::from_str(self.abi.as_str()).unwrap()
//     }
//     fn find_func(&self, func_name: String) -> Option<&AbiFunction> {
//         match self.abi().iter().find(|x|
//             if let AbiEntry::Function(abi_func) = x {
//                 abi_func.name == func_name
//             } else {
//                 false
//             }
//         ) {
//             Some(AbiEntry::Function(abi_fn)) => {
//                 Some(abi_fn)
//             },
//             // TODO maybe include into the last branch? if something bad
//             Some(_) => unreachable!("It shouldn't be reached no matter what"),
//             None => None
//         }
//     }
// }


async fn transform_input_calldata(
    input_calldata: String,
    function_name: String,
    contract_address: FieldElement,
    client: &JsonRpcClient<HttpTransport>,
) -> Result<()> {
    let db = SimpleParserDatabase::default();
    // parse
    let parsed_node = parse_input_calldata(input_calldata, &db)?;
    let contract_class = client.get_class(BlockId::Tag(BlockTag::Latest), contract_address).await.map_err(handle_rpc_error).unwrap();
    let arguments_expr_list = get_expr_list(parsed_node, &db);

    match contract_class {
        ContractClass::Sierra(sierra_class) => {
            // TODO remove .expect() and change into pattern matching or smth
            let abi: Vec<AbiEntry> = serde_json::from_str(sierra_class.abi.as_str()).expect("Couldn't deserialize ABI received from chain");
            let called_function = find_new_abi_fn(&abi, function_name).context(format!("Function {} not found in contract with address {}", function_name, contract_address))?;

            // TODO should it be here? or should chain validate if args list is of a valid length
            if called_function.inputs.len() != arguments_expr_list.len() {
                bail!("Invalid number of arguments, passed {}, expected {}", arguments_expr_list.len(), called_function.inputs.len())
            }

            let structs = abi.iter().filter_map(|abi_entry| {
                if let AbiEntry::Struct(abi_struct) = abi_entry {
                    Some(abi_struct)
                } else {
                    None
                }
            }).collect::<Vec<&AbiStruct>>();


        }
        ContractClass::Legacy(legacy_class) => {
            // TODO is this valid?                                      vvv
            let abi = legacy_class.abi.expect("Can't send a transaction without ABI");
            let called_function = find_legacy_abi_fn(&abi, function_name).context(format!("Function {} not found in contract with address {}", function_name, contract_address))?;

            // TODO should it be here? or should chain validate if args list is of a valid length
            if called_function.inputs.len() != arguments_expr_list.len() {
                bail!("Invalid number of arguments, passed {}, expected {}", arguments_expr_list.len(), called_function.inputs.len())
            }
        }
    }

    // get StatementList from fn body
    //  get all args from it
    let parsed_calldata_arguments = get_parsed_calldata_arguments(parsed_node, &db);

    //  check them against abi
    // TODO validate structs with the same name, but with multiple imported ones
    // e.g. mod1::A and mod2::A, then "A { a: 123 }" is ambiguous (maybe check by arguments?)
    Ok(())
}

mod tests {
    use std::ops::Sub;
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
        // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { ( path::to::A<3> { a: array![1, \"a\", 'b'] }, 1, array![2] ); }".to_string());
        // parse_input_calldata_test("fn __WRAPPER_FUNC_TO_PARSE__() { ( core::macros::array![1, \"a\", 'b'] ); }".to_string());
        // let input_calldata = "My::Struct::Variant{a:1, b:array![], c:(1,2_u32, '3', \"4\")}".to_string();
        let input_calldata = "1, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999993618502788666131213697322783095070105623107215331596699973092056135872020480000000000000000_u256,'3',\"4\", (5, 6), true, array![7, 8_u32], Module::Nine{ten:11}".to_string();
        parse_input_calldata_test(format!{"fn __WRAPPER_FUNC_TO_PARSE__() {{ ( {input_calldata} ); }}"}.to_string());
        let db = SimpleParserDatabase::default();
        let parsed_node = parse_input_calldata(input_calldata, &db).unwrap();
        let parsed_calldata_arguments = get_parsed_calldata_arguments(parsed_node, &db);
        dbg!(&parsed_calldata_arguments);
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
