use std::collections::HashSet;
use anyhow::{bail, Context, Result};
use cairo_lang_parser::utils::SimpleParserDatabase;
use cairo_lang_syntax::node::ast::{ArgClause, ArgList, Expr, ExprInlineMacro, ExprPath, OptionStructArgExpr, PathSegment, StructArg, WrappedArgList};
use cairo_lang_syntax::node::ast::PathSegment::Simple;
use cairo_lang_syntax::node::{Terminal, Token};
use itertools::Itertools;
use regex::Regex;
use starknet::core::types::contract::{AbiEntry, AbiEnum, AbiNamedMember, AbiStruct};
use crate::helpers::data_transformer::data_transformer::{AllowedCalldataArguments, ArgumentName, CalldataArrayMacro, CalldataEnum, CalldataSingleArgument, CalldataStruct, CalldataStructField, CalldataTuple};

fn parse_expr_path_to_path_elements(expr_path: ExprPath, db: &SimpleParserDatabase) -> anyhow::Result<Vec<String>> {
    expr_path.elements(db).iter().map(|p| match p {
        Simple(segment) => {
            Ok(segment.ident(db).token(db).text(db).to_string())
        }
        PathSegment::WithGenericArgs(_) => bail!("Cannot use generic args when specifying struct/enum path")
    }).collect::<anyhow::Result<Vec<String>>>()
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
    }).collect()
}

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
fn parse_expr(expr: Expr, param_type: String, abi: &Vec<AbiEntry>, db: &SimpleParserDatabase) -> anyhow::Result<AllowedCalldataArguments> {
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
                Ok(CalldataStructField::new(parse_expr(expr, abi_entry.r#type.clone(), abi, db)?, abi_entry.r#type.clone()))
            }).collect::<Result<Vec<CalldataStructField>>>()?;

            Ok(AllowedCalldataArguments::Struct(CalldataStruct::new(fields)))
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

            Ok(AllowedCalldataArguments::Enum(CalldataEnum::new(
                enum_position,
                None,
            )))
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

            Ok(AllowedCalldataArguments::Enum(CalldataEnum::new(enum_position, Some(Box::new(parsed_expr)))))
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

            let arguments = parsed_exprs.into_iter().map(|arg| parse_expr(arg, abi_argument_type.to_string(), abi, db)).collect::<anyhow::Result<Vec<AllowedCalldataArguments>>>()?;
            Ok(AllowedCalldataArguments::ArrayMacro(CalldataArrayMacro::new(arguments)))
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
                .collect::<anyhow::Result<Vec<_>>>()?;
            Ok(AllowedCalldataArguments::Tuple(CalldataTuple::new(parsed_exprs)))
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
