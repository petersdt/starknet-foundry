use crate::helpers::data_transformer::transformer::LegacyFunctionArgument;
use regex::Regex;
use starknet::core::types::LegacyFunctionAbiEntry;

fn parse_legacy_fn_arguments(
    called_function: &LegacyFunctionAbiEntry,
) -> Vec<LegacyFunctionArgument> {
    // Parses types from legacy ABI function - finds any arrays (arrayname_len: type, arrayname: type*)
    // and concatenates them into one type.
    let mut parsed_arguments = Vec::new();

    let mut first_iterator = called_function.inputs.iter();
    let mut second_iterator = called_function.inputs.iter();
    if second_iterator.next().is_none() {
        // Argument list is empty
        return parsed_arguments;
    }
    let mut iter = first_iterator.zip(second_iterator);
    // Sliding window :^)
    while let Some((fst, snd)) = iter.next() {
        if fst.name == snd.name.clone() + "_len" && fst.r#type == "felt" {
            let re = Regex::new(r#"[^*]+\*+"#).unwrap();
            let snd_type_captures = re.captures(snd.r#type.as_str());

            if snd_type_captures.is_none() {
                // When first is a_len: felt, second is a: type (no stars meaning no array)
                parsed_arguments.push(LegacyFunctionArgument::Felt);
                continue;
            } else {
                // When first argument is a_len: felt, second argument is a: type* (any number of stars)
                parsed_arguments.push(LegacyFunctionArgument::Array(snd.r#type.clone()));
                // We skip additional entry in iterator since we covered two entries at once
                iter.next();
                continue;
            }
        } else {
            match fst.r#type.as_str() {
                "felt" => parsed_arguments.push(LegacyFunctionArgument::Felt),
                _ => parsed_arguments.push(LegacyFunctionArgument::Other(fst.r#type.clone())),
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

mod tests {
    #[allow(dead_code, unused_imports, unused_variables)]
    use super::*;
    use shared::rpc::create_rpc_client;
    use starknet::core::types::{
        BlockId, BlockTag, ContractClass, FieldElement, LegacyContractAbiEntry,
    };
    use starknet::macros::felt;
    use starknet::providers::Provider;

    #[tokio::test]
    async fn test_legacy_abi() {
        // let client = create_rpc_client("http://188.34.188.184:7070/rpc/v0_7").unwrap();
        let client = create_rpc_client("https://free-rpc.nethermind.io/mainnet-juno").unwrap();
        let class_hash_legacy: FieldElement =
            felt!("0x0157d87bdad1328cbf429826a83545f6ffb6505138983885a75997ee2c49e66b");
        let contract = client
            .get_class(BlockId::Tag(BlockTag::Latest), class_hash_legacy)
            .await
            .unwrap();
        if let ContractClass::Legacy(legacy) = contract {
            // dbg!(legacy.clone().abi.unwrap());
            for entry in &legacy.abi.clone().unwrap() {
                match entry {
                    LegacyContractAbiEntry::Function(func) => {
                        dbg!(&func.name);
                        dbg!(parse_legacy_fn_arguments(func));
                    }
                    LegacyContractAbiEntry::Event(_) => continue,
                    LegacyContractAbiEntry::Struct(_) => continue,
                }
            }
        }
    }
}
