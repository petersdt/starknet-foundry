use clap::Parser;
use docs::validation::{
    assert_valid_snippet, extract_snippets_from_directory, get_parent_dir,
    print_skipped_snippet_message, print_success_message, SnippetType,
};
use forge::Cli;
use shared::test_utils::output_assert::assert_stdout_contains;

use super::common::runner::{setup_package, test_runner};

#[test]
fn test_docs_snippets() {
    let root_dir = get_parent_dir(2);
    let docs_dir = root_dir.join("docs/src");

    let snippet_type = SnippetType::forge();

    let snippets = extract_snippets_from_directory(&docs_dir, &snippet_type)
        .expect("Failed to extract command snippets");

    for snippet in &snippets {
        let args = snippet.to_command_args();
        let mut args: Vec<&str> = args.iter().map(String::as_str).collect();

        if snippet.config.ignored.unwrap_or(false) {
            print_skipped_snippet_message(snippet);
            continue;
        }

        let parse_result = Cli::try_parse_from(args.clone());
        let err_message = if let Err(err) = &parse_result {
            err.to_string()
        } else {
            String::new()
        };

        assert_valid_snippet(parse_result.is_ok(), snippet, &err_message);

        // Remove "snforge" from the args
        args.remove(0);

        // Remove "test" from the args
        args.retain(|element| element != &"test");

        if let Some(snippet_output) = &snippet.output {
            let package_name = snippet
                .config
                .package_name
                .clone()
                .or_else(|| snippet.capture_package_from_output())
                .expect("Cannot find package name in command output or snippet config");

            let temp = setup_package(&package_name);
            let output = test_runner(&temp).args(args).assert();

            assert_stdout_contains(output, snippet_output);
        }
    }

    print_success_message(snippets.len(), snippet_type.as_str());
}