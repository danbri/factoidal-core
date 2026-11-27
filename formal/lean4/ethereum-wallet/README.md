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
