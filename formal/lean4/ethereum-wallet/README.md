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
| ABI, EIP-712, contract calls | `EthereumWallet/Abi*`, `EthereumWallet/Eip712*` |

No network code here: RPC goes through the shared host network path
([issue 1176](https://github.com/danbri/factoidal-core/issues/1176)) when it lands.
Nothing in this package sends a transaction to a public network.

## Keys

Modules, rules, the constant-time and secret-lifetime notes, and what is proved or only
tested: the header of [`EthereumWallet/Keys.lean`](EthereumWallet/Keys.lean).

- Off by default: entry points that take a secret ask for the risk token of
  `EthereumWallet/Keys/Risk.lean`; the executables need
  `--dangerously-enable-variable-time-secrets`.
- No AES in the tree (repository rule): keystore v3 passwords can be checked, plaintext
  recovery needs an AES-128-CTR provider, which is an open decision.
- Tests: `lake exe wallet-keys-tests --dangerously-enable-variable-time-secrets` and
  `lake exe wallet-keystore-tests --dangerously-enable-variable-time-secrets [--medium|--full]`
  (`--full` needs 1 GiB: CI only). Vectors and the BIP-39 wordlist:
  `third_party/testing/ethereum-wallet/PROVENANCE.md`; `scripts/gen-keys-data.py --check`.
- CI: `.github/workflows/ethereum-wallet-keys.yml`.
