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

## Transactions and signing

| Module | What |
|---|---|
| `Tx.lean` | unsigned transactions of kinds 0 to 4, RLP encoding, signing payload and hash, signed envelope, EIP-7702 authorization hash, admission rules |
| `SignSecp.lean` | secret-scalar base multiplication on the shared secp256k1 arithmetic, verification, addresses, the timing risk token |
| `SignRfc6979.lean` | RFC 6979 nonces on HMAC-SHA-256 |
| `Sign.lean` | `signHash`: ECDSA, low `s`, recovery self-check |
| `TxDecode.lean` | reading a signed transaction back through the admission decoder |
| `TxSign.lean` | `signTransaction`, `signAuthorization`, round-trip theorems |
| `SignTests.lean` | build-time `#guard` tests |
| `SignMain.lean` | the `eth-wallet-sign` tool: sign JSON with a test key, vector suites, timing |

Signing is **not constant-time**; callers pass `Risk.Accepted .variableTimeSigning`.
What is proved, what is tested, and the timing analysis:
[design record](../../../docs/designissues/2026-11-27-ethereum-wallet-signing.md).

Reused in place (see `lakefile.toml`): `EVMCleanroom.CanonicalRLP`, `Keccak`,
`SignedTransaction`, `Precompiles.Secp256k1` from `../evm-cleanroom`;
`L4Factoidal.Crypto.SHA2` and `Hmac`.

```sh
lake build EthereumWallet eth-wallet-sign
R=--dangerously-enable-variable-time-signing
# The key below is the published EIP-155 example key. Never use a key that holds funds.
.lake/build/bin/eth-wallet-sign sign $R --test-key-hex 4646464646464646464646464646464646464646464646464646464646464646 tx.json
.lake/build/bin/eth-wallet-sign tx-vectors $R vectors/eest-prague-signing.json --affine 25
.lake/build/bin/eth-wallet-sign rfc6979-vectors $R ../../../third_party/bitcoinjs-lib-fixtures/ecdsa.json
.lake/build/bin/eth-wallet-sign wycheproof ../../../third_party/wycheproof/ecdsa_secp256k1_sha256_p1363_test.json
.lake/build/bin/eth-wallet-sign bench $R 300
```

`tx.json` uses the JSON-RPC field names: `type`, `chainId`, `nonce`, `gasPrice`
or `maxFeePerGas` and `maxPriorityFeePerGas`, `gas`, `to`, `value`, `input`,
`accessList`, `maxFeePerBlobGas`, `blobVersionedHashes`, `authorizationList`.

CI: `.github/workflows/ethereum-wallet.yml`. Each area lists its theorems in
`scripts/theorems/<area>.txt` for the axiom audit and adds its steps in its
own block of the workflow.
