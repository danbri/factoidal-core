# Ethereum wallet (Lean 4)

Building, signing and encoding Ethereum transactions, key handling and ABI
encoding, in repository-owned pure Lean 4. It is a stand-alone Lake package,
like `../evm-cleanroom` and `../ethereum-consensus`.

Goal and constraints: [issue 725](https://github.com/danbri/factoidal-core/issues/725)
(independent implementation; reference libraries only as test oracles).

| Area | Modules |
|---|---|
| Transactions and signing | `EthereumWallet/Tx*`, `EthereumWallet/Sign*` |
| Keys (BIP-39, BIP-32, keystore) | `EthereumWallet/Keys*` |
| ABI, EIP-712, contract calls | `EthereumWallet/Abi*`, `EthereumWallet/Eip712*`, `EthereumWallet/Calls*` |

No network code here: RPC goes through the shared host network path
([issue 1176](https://github.com/danbri/factoidal-core/issues/1176)) when it lands.
Nothing in this package sends a transaction to a public network.

## ABI, EIP-712 and contract calls

`EthereumWallet/Abi` is the Solidity ABI: type grammar, encoding, a strict
decoder that accepts only canonical encodings (`decodeArgsAt_sound`,
`decodeArgs_encodeArgs`), selectors, calldata and event logs.
`EthereumWallet/Eip712` is a bounded JSON reader, EIP-712 typed data and the
EIP-191 `personal_sign` digest. `EthereumWallet/Calls` has builders and
"what this does" summaries for ERC-20, ERC-721, WETH9, Uniswap v3
SwapRouter02 and Permit2, pinned mainnet and Sepolia addresses with their
sources, and `CREATE`/`CREATE2` address prediction.

```
lake build EthereumWallet.AbiAxioms wallet-abi-vectors
.lake/build/bin/wallet-abi-vectors builtin --dangerously-enable-pure-keccak-on-messages
.lake/build/bin/wallet-abi-vectors bench 2000
```

The flag accepts, for this test tool only, that message data is hashed by the
pure Lean Keccak-256 (see `skills/lean-risk-flags`). Differential cases come
from `scripts/abi-oracle` (ethers and viem, test oracles only; CI runs them).
Design note and the list of warnings:
`docs/designissues/2026-11-27-wallet-misleading-signing-cases.md`.
