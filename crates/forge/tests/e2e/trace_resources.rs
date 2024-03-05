use assert_fs::TempDir;
use forge_runner::build_trace_data::TRACE_DIR;
use std::collections::HashMap;
use std::fs;

use trace_data::DeprecatedSyscallSelector::{
    CallContract, Deploy, EmitEvent, GetBlockHash, GetExecutionInfo, Keccak, LibraryCall,
    SendMessageToL1, StorageRead, StorageWrite,
};
use trace_data::{
    CallTrace as ProfilerCallTrace, ExecutionResources as ProfilerExecutionResources,
};

use crate::e2e::common::runner::{setup_package, test_runner};

#[test]
fn trace_resources_call() {
    assert_resources_for_test("test_call", check_call);
}

#[test]
fn trace_resources_deploy() {
    assert_resources_for_test("test_deploy", check_deploy);
}

#[test]
fn trace_resources_l1_handler() {
    assert_resources_for_test("test_l1_handler", check_l1_handler);
}

#[test]
fn trace_resources_lib_call() {
    assert_resources_for_test("test_lib_call", check_libcall);
}

#[test]
#[ignore] // TODO(#1657)
fn trace_resources_failed_call() {
    assert_resources_for_test("test_failed_call", |_| ());
}

#[test]
#[ignore] // TODO(#1657)
fn trace_resources_failed_lib_call() {
    assert_resources_for_test("test_failed_lib_call", |_| ());
}

fn assert_resources_for_test(
    test_name: &str,
    check_not_easily_unifiable_syscalls: fn(&ProfilerCallTrace),
) {
    let temp = setup_package("trace_resources");
    let snapbox = test_runner();
    snapbox
        .current_dir(&temp)
        .arg(test_name)
        .arg("--save-trace-data")
        .assert()
        .success();

    let call_trace = deserialize_call_trace(test_name, &temp);
    check_vm_resources_and_easily_unifiable_syscalls(&call_trace);
    // test Deploy, CallContract and LibraryCall syscalls as their counts cannot be unified as easily as the rest
    check_not_easily_unifiable_syscalls(&call_trace);
}

fn deserialize_call_trace(test_name: &str, temp_dir: &TempDir) -> ProfilerCallTrace {
    let trace_data = fs::read_to_string(
        temp_dir
            .join(TRACE_DIR)
            .join(format!("tests::{test_name}::{test_name}.json")),
    )
    .unwrap();
    serde_json::from_str(&trace_data).expect("Failed to parse call trace")
}

fn check_vm_resources_and_easily_unifiable_syscalls(
    call_trace: &ProfilerCallTrace,
) -> (&ProfilerExecutionResources, isize) {
    let mut child_resources = vec![];
    for call in &call_trace.nested_calls {
        child_resources.push(check_vm_resources_and_easily_unifiable_syscalls(call));
    }

    let mut sum_child_resources = ProfilerExecutionResources::default();
    let mut sum_child_storage_writes = 0;
    for (resource, storage_writes) in child_resources {
        sum_child_resources += resource;

        sum_child_storage_writes += storage_writes;
    }

    let current_resources = &call_trace.cumulative_resources;
    assert!(current_resources.gt_eq_than(&sum_child_resources));

    let current_storage_writes = call_trace.used_l1_resources.storage_writes;
    assert!(current_storage_writes >= sum_child_storage_writes);

    let resource_diff = current_resources - &sum_child_resources;
    assert_correct_diff_for_builtins_and_easily_unifiable_syscalls(&resource_diff);
    assert_l2_l1_messages(call_trace);

    let storage_writes_diff = current_storage_writes - sum_child_storage_writes;
    assert_l1_resources(call_trace, storage_writes_diff);

    (current_resources, current_storage_writes)
}

fn assert_correct_diff_for_builtins_and_easily_unifiable_syscalls(
    resource_diff: &ProfilerExecutionResources,
) {
    for syscall in [
        EmitEvent,
        GetBlockHash,
        GetExecutionInfo,
        StorageWrite,
        StorageRead,
        SendMessageToL1,
        Keccak,
    ] {
        assert_eq!(
            *resource_diff
                .syscall_counter
                .get(&syscall)
                .unwrap_or_else(|| panic!("Expected resource diff to contain {syscall:?}")),
            1,
            "Incorrect diff for {syscall:?}"
        );
    }

    for builtin in [
        "poseidon_builtin",
        "ec_op_builtin",
        "bitwise_builtin",
        "pedersen_builtin",
    ] {
        assert_eq!(
            *resource_diff
                .vm_resources
                .builtin_instance_counter
                .get(builtin)
                .unwrap_or_else(|| panic!("Expected resource diff to contain {builtin:?}")),
            1,
            "Incorrect diff for {builtin:?}"
        );
    }
}

fn assert_l1_resources(call_trace: &ProfilerCallTrace, storage_writes_diff: isize) {
    assert_eq!(
        call_trace.used_l1_resources.l2_l1_message_sizes.len(),
        1,
        "Every call should have one message"
    );
    assert_eq!(
        call_trace.used_l1_resources.l2_l1_message_sizes,
        vec![2],
        "Message should have payload of length 2"
    );
    assert!(
        storage_writes_diff <= 1,
        "Every call should have at most one storage write"
    );
}

// When sth fails in the functions below and you didn't change anything in the cairo code it is a BUG.
// If you changed the corresponding cairo code count the expected occurrences of syscalls manually first, then assert them.
// TL;DR: DON't mindlessly change numbers to fix the tests if they ever fail.
fn check_call(test_call_trace: &ProfilerCallTrace) {
    assert_not_easily_unifiable_syscalls(test_call_trace, 14, 8, 1);

    let regular_call = &test_call_trace.nested_calls[1];
    assert_not_easily_unifiable_syscalls(regular_call, 2, 1, 0);

    let from_proxy = &regular_call.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);

    let with_libcall = &test_call_trace.nested_calls[2];
    assert_not_easily_unifiable_syscalls(with_libcall, 2, 0, 1);

    let from_proxy = &with_libcall.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);

    let call_two = &test_call_trace.nested_calls[3];
    assert_not_easily_unifiable_syscalls(call_two, 3, 2, 0);

    let from_proxy = &call_two.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);

    let from_proxy_dummy = &call_two.nested_calls[1];
    assert_not_easily_unifiable_syscalls(from_proxy_dummy, 1, 0, 0);

    let from_proxy = &test_call_trace.nested_calls[4];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);
}

fn check_deploy(test_call_trace: &ProfilerCallTrace) {
    assert_not_easily_unifiable_syscalls(test_call_trace, 14, 4, 0);

    for deploy_proxy in &test_call_trace.nested_calls {
        assert_not_easily_unifiable_syscalls(deploy_proxy, 2, 1, 0);

        let from_proxy = &deploy_proxy.nested_calls[0];
        assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);
    }
}

fn check_l1_handler(test_call_trace: &ProfilerCallTrace) {
    assert_not_easily_unifiable_syscalls(test_call_trace, 8, 3, 0);

    let handle_l1 = &test_call_trace.nested_calls[1];
    assert_not_easily_unifiable_syscalls(handle_l1, 3, 2, 0);

    let regular_call = &handle_l1.nested_calls[0];
    assert_not_easily_unifiable_syscalls(regular_call, 2, 1, 0);

    let from_proxy = &regular_call.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);
}

fn check_libcall(test_call_trace: &ProfilerCallTrace) {
    assert_not_easily_unifiable_syscalls(test_call_trace, 11, 3, 5);

    let regular_call = &test_call_trace.nested_calls[0];
    assert_not_easily_unifiable_syscalls(regular_call, 2, 1, 0);

    let from_proxy = &regular_call.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);

    let with_libcall = &test_call_trace.nested_calls[1];
    assert_not_easily_unifiable_syscalls(with_libcall, 2, 0, 1);

    let call_two = &test_call_trace.nested_calls[2];
    assert_not_easily_unifiable_syscalls(call_two, 3, 2, 0);

    let from_proxy = &call_two.nested_calls[0];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);

    let from_proxy_dummy = &call_two.nested_calls[1];
    assert_not_easily_unifiable_syscalls(from_proxy_dummy, 1, 0, 0);

    let from_proxy = &test_call_trace.nested_calls[3];
    assert_not_easily_unifiable_syscalls(from_proxy, 1, 0, 0);
}

fn assert_not_easily_unifiable_syscalls(
    call: &ProfilerCallTrace,
    deploy_count: usize,
    call_contract_count: usize,
    library_call_count: usize,
) {
    let syscall_counter = &call.cumulative_resources.syscall_counter;

    let expected_counts: HashMap<_, _> = [
        (Deploy, deploy_count),
        (CallContract, call_contract_count),
        (LibraryCall, library_call_count),
    ]
    .into_iter()
    .filter(|(_key, val)| *val > 0)
    .collect();

    for key in [Deploy, CallContract, LibraryCall] {
        assert_eq!(
            syscall_counter.get(&key).copied(),
            expected_counts.get(&key).copied(),
            "Incorrect count for {key:?}"
        );
    }
}
