# `deploy`
Deploy a contract to Starknet.

## Required Common Arguments — Passed By CLI or Specified in `snfoundry.toml`

* [`url`](./common.md#--url--u-rpc_url)
* [`account`](./common.md#--account--a-account_name)

## `--class-hash, -g <CLASS_HASH>`
Required.

Class hash of contract to deploy.

## `--constructor-calldata, -c <CONSTRUCTOR_CALLDATA>`
Optional.

Calldata for the contract constructor, represented by a Cairo-like expression.
Supported argument types:

| Argument type                       | Valid expressions                                                  |
|-------------------------------------|--------------------------------------------------------------------|
| numerical value (felt, u8, i8 etc.) | `0x1`, `2_u8`, `-3`                                                |
| shortstring                         | `'value'`                                                          |
| string (ByteArray)                  | `"value"`                                                          |
| boolean value                       | `true`, `false`                                                    |
| struct                              | `Struct { field_one: 0x1 }`, `path::to::Struct { field_one: 0x1 }` |
| enum                                | `Enum::One`, `Enum::Two(123)`, `path::to::Enum::Three`             |
| array                               | `array![0x1, 0x2, 0x3]`                                            |
| tuple                               | `(0x1, array![2], Struct { field: 'three' })`                      |

## `--salt, -s <SALT>`
Optional.

Salt for the contract address.

## `--unique, -u`
Optional.

If passed, the salt will be additionally modified with an account address.

## `--max-fee, -m <MAX_FEE>`
Optional.

Max fee for the transaction. If not provided, max fee will be automatically estimated.

## `--nonce, -n <NONCE>`
Optional.

Nonce for transaction. If not provided, nonce will be set automatically.
