# EELS state-test replay — narrow verified-machine bridge

This module executes **real, published Ethereum Execution Layer Specifications
(EELS) state-test fixtures**. It is an independently auditable first slice of
transaction replay, **not** a complete Ethereum execution-client implementation.

## Evidence as of 19 November 2026

Fixture source (EthereumJS mirror of EELS-generated tests):

- [EIP-7623 Prague state tests](https://github.com/ethereumjs/execution-spec-tests-fixtures/blob/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json)
- Repository commit: `3c4287ae3aea1f45af9288629834f0584fcde69a`.
- Exact fixture SHA-256:
  `9afff783c1365a2743662353b88f8938d6171fa764184902053ad20ec3539cd4`.
- Four out of six fixture cases **executed and passed**; zero failed; two
  classified unsupported. Every pass checks the computed Merkle state root
  against the fixture's published `post.Prague[0].hash`, and checks the
  complete expected account set (nonces, balances, empty code/storage).
- The two unsupported transactions involve EIP-4844 blob fees and EIP-7702
  authorisation/delegated code. They are not silently counted as successes.
- The expected empty-logs hash is checked for these no-code executions.
  General receipt/log generation remains unsupported.

## Which computation is performed where?

**Lean 4, actual executable semantics**

- `EVMCleanroom.run` executes a real (empty) bytecode frame.
  `EELSBridge.empty_code_halts_without_spending_gas` proves the exact
  machine-level zero-gas termination case used here.
- `TxAccounting` calculates intrinsic gas, access-list gas, the Prague
  EIP-7623 calldata floor, EIP-1559 effective fee price, charged gas,
  sender balance/nonce updates, miner priority-fee reward and base-fee burn.
- Theorems `settle_charged_bounded`, `sender_balance_conservation`,
  `sender_nonce_advances`, and `fee_conservation` are checked during
  the normal Lean build. These are theorems of the model, **not yet a
  formal proof of equivalence with EELS**.

**Unverified JavaScript host / trusted library boundary**

- EthereumJS decodes the signed RLP transaction and recovers its sender,
  checking the signed fields against the published fixture input.
- The host extracts the pre-state and invokes Lean's opcode execution and
  fee accounting. Independent JS arithmetic spot-checks intrinsic gas and
  conservation conditions.
- EthereumJS `Account` and Merkle Patricia trie serialization constructs
  the computed state root. **EthereumJS runTx is not used to execute the
  candidate transaction**; this is genuinely driven by the Lean result.
- The host then compares roots and expected account contents with EELS.
  The full source-to-root path is **not formally verified in Lean**.

No Ethereum mainnet transaction, existing deployed Solidity bytecode,
transaction-level exceptional rollback or dynamically executed contract
storage is supported by this slice.

## Reproduction

From `formal/lean4/evm-cleanroom/`:

```sh
lake build

# The CI workflow installs a separately pinned npm dependency resolution:
npm install --prefix scripts/eels --ignore-scripts --no-audit --no-fund
printf '2f5caf7dd31ee1d2b36290788e509110955005c28302ed0f038dadbc2bf6c6c7  scripts/eels/package-lock.json\n' |
  sha256sum --check

mkdir -p .lake/eels
curl --fail --location --silent --show-error \
  'https://raw.githubusercontent.com/ethereumjs/execution-spec-tests-fixtures/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json' \
  -o .lake/eels/eip7623.json
printf '9afff783c1365a2743662353b88f8938d6171fa764184902053ad20ec3539cd4  .lake/eels/eip7623.json\n' |
  sha256sum --check

node scripts/eels/run-lean-state-tests.mjs \
  --fixture .lake/eels/eip7623.json \
  --out .lake/eels/lean-state-results.json

node scripts/eels/selftest.mjs \
  .lake/eels/eip7623.json .lake/eels/negative-controls
```

The self-test deliberately changes an expected EELS state root and an
expected sender balance. The replay runner must reject both, with exact
negative-control reports. CI archives the fixture, the result JSON, these
counterexamples and the generated dependency lock. The lockfile is currently
**validated by a fixed SHA-256 in CI but not committed**; commit it as a
separate reproducibility improvement before claiming a fully hermetic build.

## Acceptance boundaries

| Criterion | Current status |
|---|---|
| Machine-executable official fixture transactions | 4 supported |
| Source/provenance pinned and validated by SHA-256 | Yes |
| Signed envelope and sender independently checked | Yes, via EthereumJS |
| Lean EVM frame execution | Yes, empty-code only |
| Lean-calculated balances, nonce and fees | Yes, limited EIP-7623 type 0/1/2 |
| Published post-account and state-root comparison | Yes, four cases |
| Negative tampering controls | Yes, two |
| Lean proof of machine/fee arithmetic properties | Yes, model-relative |
| Formal refinement of fee semantics to EELS | No |
| Nonempty contract-code EELS cases | No |
| Blob fee/authorisation tx variants | No |
| Receipt/log serialization and arbitrary state changes | No |
| Real historical mainnet transaction replay | No |

See [../../ROADMAP.md](../../ROADMAP.md) and
[../../SOUNDNESS.md](../../SOUNDNESS.md). The next meaningful boundary is a
published fixture with **nonempty contract code and a real persistent
storage change**, followed by exception/rollback and receipt fidelity.
