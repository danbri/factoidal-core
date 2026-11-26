# Independent Lean authentication of execution witnesses

Tracking: [issue #1043](https://github.com/danbri/factoidal-core/issues/1043).
Execution predecessor: [PR #870](https://github.com/danbri/factoidal-core/pull/870),
commit `40c3f0335501677d782df566ef7fd1e8a5cc4ad5`.
Full-client criteria remain [#725](https://github.com/danbri/factoidal-core/issues/725)
and the execution subgoal [#652](https://github.com/danbri/factoidal-core/issues/652).

## Problem and change

The ordered transaction runner already computed successor state, receipts and
cumulative gas from one starting inventory. Its decoded input path still let
the caller assert every account balance, nonce and storage value. Comparing
execution with another client could not remove that input trust boundary.

The new authenticated path derives that inventory from account and storage
proofs under the supplied parent header's state root. It then calls the actual
existing transaction-list runner with exactly the derived inventory. No
separate host-supplied balance, nonce, presence flag or slot value is accepted
in this schema. Bytecode is supplied, but its Keccak digest must equal the
code hash decoded from the proved account leaf.

All new production parsing, proof traversal and admission are independent Lean
code. The package adds no external Lake dependency, FFI, client subprocess or
proof-verifier wrapper. Existing EthereumJS packages are used only by the test
harness to build and check independent expectations. The original decoded
mode remains available with its original trust boundary.

## Specification and model

The implementation follows the byte/list encoding and trie commitments in
the [Yellow Paper, appendices B–D](https://ethereum.github.io/yellowpaper/paper.pdf),
the [RLP specification](https://ethereum.org/developers/docs/data-structures-and-encoding/rlp/),
the [Merkle Patricia trie description](https://ethereum.org/developers/docs/data-structures-and-encoding/patricia-merkle-trie/),
and the account/storage proof structure of
[EIP-1186](https://eips.ethereum.org/EIPS/eip-1186).
The model and refusal boundaries were recorded in issue #1043 before code.
This is a bounded secure-key verifier and a dedicated transport; it is not
an implementation of the entire `eth_getProof` RPC response schema.

The test inputs pin `ethereum/tests` commit
`c67e485ff8b5be9abc8ad15345ec21aa22e290d9`: 28 valid RLP cases, 26 invalid
RLP cases and three secure-trie root fixtures. Their exact Git blob and
SHA-256 identities are checked by `scripts/witness/oracle.mjs`.
The retained historical fixture is the existing mainnet block 46,146 parent
state proof bundle; its decoded SHA-256 is
`9c9286d7c9500aca5426b7bf44bc74b19f84d2b16761dfb10ea7948bbef17924`.

### Canonical RLP

`CanonicalRLP.decode` consumes exactly one recursively canonical RLP item.
It rejects truncated items, overlong length forms, leading zero length bytes,
nonminimal single-byte encodings and trailing input. An explicit stack of
source ranges validates nested lists. Advertised lengths are checked against
the actual input before extraction; no recursively allocated syntax tree is
needed. Returned child views retain their exact original encodings.

`CanonicalRLP.scalar` separately checks unsigned integer minimality and the
requested width. Empty bytes encode integer zero. The raw byte `00` is valid
RLP byte-string data, but is refused as an integer zero. Account nonce and
balance widths in this admitted execution profile are 8 and 32 bytes.

### Secure-trie paths

`MPT.lookup` accepts a 32-byte root, an already hashed 32-byte key and a bag of
encoded proof nodes. Account admission hashes the exact 20-byte big-endian
address; storage admission hashes the exact 32-byte big-endian slot key.

The root is always a hash reference, including a short root node. A non-root
child shorter than 32 encoded bytes must be an embedded RLP list; a longer
child is referenced by its 32-byte hash. Hex-prefix decoding checks flags and
even-path padding. Extensions consume a nonempty path, including a valid
one-nibble path. A secure leaf must match the remaining key length.

Each resolved hashed node carries a proof that its actual bytes hash to the
requested digest. Each traversal hop retains the actual decoder and path
selection equations. Successful traversal returns a finite path relation
from that reference and key to the returned value or absence.

Nonmembership is established by the exact empty-trie commitment, an empty
branch child, or a proved path divergence. A missing hash reference, malformed
node or failed decoder produces an explicit refusal. Proof bags may be
unordered or contain repeated or unused nodes. Every supplied node is charged
to the budget; only referenced nodes need be decoded. Global normalization
of unvisited subtrees and branch occupancy is outside this path checker.

### Account and execution linkage

A present account must decode to exactly `[nonce, balance, storageRoot,
codeHash]`, with two 32-byte commitments. The supplied code hashes to the
decoded code commitment. Each requested storage key is checked under that
same account's proved storage root. A present storage leaf contains a
canonical nonzero word; proved nonmembership yields zero. Account addresses
and per-account storage keys must be unique.

Standalone admission preserves a proved present account with zero balance,
zero nonce and empty code. The current executor cannot represent that
presence distinction correctly, so authenticated execution returns
`indeterminate` with reason `authenticated-empty-account-profile`. It does
not silently convert the account into absence. An absent account with a
storage request is likewise an explicitly unsupported profile.

`runAuthenticated` obtains the root from field 3 of the same parent header
passed to `TransactionList.run`. Admission failure produces an indeterminate
result with no transaction index or accepted partial state. Successful
admission replaces the starting inventory before execution. Existing list
checks still validate the admitted parent/child relationship and exact final
gas counters.

The parent state is not generally the state immediately before transaction
zero of a canonical Cancun block. [EIP-4788 block processing](https://eips.ethereum.org/EIPS/eip-4788#block-processing)
performs its beacon-root system operation first. This runner does not yet
perform that operation. Its synthetic reference fixtures have no code at the
beacon-root address, so the reference operation has no effect. The evidence
therefore establishes authenticated execution of those supplied lists, not
general canonical Cancun block replay from a parent root.

## Development proofs and native execution

The durable [runtime architecture decision](designissues/2026-11-25-ethereum-runtime-boundary.md)
records the build/execution boundary and the gates that preserve it.

Lean elaboration, proof construction, kernel checking and the axiom audit
belong to development and CI. The execution architecture is an ahead-of-time
compiled native program. Processing an account witness means hashing bytes,
decoding RLP and following a trie path; it does not mean asking Lean to find
or check a mathematical proof for that request. These Ethereum protocol
witnesses and the Lean theorems about their verifier are different objects.

The theorem fields in `CheckedNode`, `Hop` and the returned path subtype are
propositions, erased by the compiler. Computational checks and data remain:
for example, comparing a computed digest with the requested digest still
runs. Proof erasure does not erase the protocol validation itself or prove
that the chosen data representation is efficient.

A native dependency audit found that the previous umbrella `Lean.Data.Json`
import pulled in JSON quotation elaboration. It also exposed a broader
bootstrap issue: the pinned compiler's [`emitMainFn`](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Compiler/LCNF/EmitC.lean)
selects `lean_initialize()` when any `Lean.*` module occurs in the runtime
import closure. That initializes the full Lean library and C++ kernel even
when the only requested library is JSON. Narrowing the JSON imports alone
did not remove this behavior; the intermediate result is retained.

The transport uses the narrower parser and basic JSON codec imports. The
two reviewed witness/list build configurations additionally select
`lean_initialize_runtime_module()` with the explicit C compilation argument
`-Dlean_initialize=lean_initialize_runtime_module`. This is startup build
glue, using the same runtime initializer as the existing repository-owned
`Wasm/l4_shim.c`. It does not replace the generated Ethereum functions, alter
the pinned compiler or introduce a new runtime implementation dependency.
Generated module initialization, argument handling, task setup and execution
remain in place.

This selection is valid only for the reviewed closure that needs ordinary
runtime services. It must not be applied indiscriminately to executables
using Lean expression checking or elaboration APIs. Source/import allowlists
and a native symbol/initializer gate enforce that boundary, alongside full
before/after replay. Compiler correctness, C compilation and initialization
remain explicit trusted build/runtime obligations; a kernel proof of a Lean
function does not certify startup glue. The runtime evidence records actual
before/after artifacts. Dynamic syscall tracing was unavailable because the
execution environment denied `ptrace`; no successful syscall trace is claimed.

Lean's ordinary runtime remains part of the executable, including its value
representations, arithmetic, arrays, I/O and reference-counted memory
management. The pinned compiler and runtime remain in the trusted computing
base. Neither proving the source nor removing unintended elaborator imports
establishes full-node throughput, memory scalability or compiler correctness.

## Native input schemas

All hexadecimal fields are complete bytes, with an optional `0x` prefix.
Output hex is lowercase without the prefix. Addresses, storage keys and
transaction quantities use the existing decimal-string transport.
Unknown fields are refused in the top-level requests, proof-bearing account
and storage objects, and list entries. The retained decoded transaction and
access-list parsers still ignore additional field names. Duplicate JSON
member names are refused throughout the authenticated request, including
duplicates spelled with JSON Unicode escapes. The duplicate guard is per
object; independent objects may use the same field names.

### Standalone state admission

Use `evm-transaction-list --dangerously-enable-unverified-keccak
--state-witness FILE` with:

```json
{
  "schemaVersion": 1,
  "stateRoot": "<32 bytes of hex>",
  "accounts": [{
    "address": "193",
    "codeHex": "00",
    "accountProof": ["<encoded node hex>"],
    "storage": [{"key": "0", "proof": ["<encoded node hex>"]}]
  }]
}
```

The placeholders above describe the shape; they are not a valid proof.
Success has status `authenticated` and the derived account list. A proof or
profile refusal has status `refused`, a classification and a reason. Schema
or transport errors use `inputError` and exit status 2.

### Authenticated ordered list

Use `evm-transaction-list --dangerously-enable-unverified-keccak
--authenticated-transaction-list FILE` with `schemaVersion: 2`, the existing
`parentHeader`, `childHeader` and `transactions` fields, and `accounts` in the
proof-bearing shape above. There is no separate `stateRoot` field: the parent
header supplies it. Transactions retain the prior decoded envelope and fuel
schema, including the paired blob fields for type 3.

An executed result has the same receipts, gas totals and final account
observations as the original list path, with response `schemaVersion: 2`.
Those final observations are not a Lean-computed post-state root. Rejection
and indeterminate outcomes retain the existing first-index conventions.

### Direct primitive checks

`evm-witness-proof --rlp FILE` accepts
`{"schemaVersion":1,"encoding":"c0"}` and optionally `integerBytes`.
It reports the payload, list status, encoded immediate children for a list,
and a decimal integer if requested. RLP alone requires no hash opt-in.

`evm-witness-proof --dangerously-enable-unverified-keccak --mpt-proof FILE`
accepts `schemaVersion: 1`, `root`, `key` and `proof`. The key is already
hashed. Success reports `present` with `valueHex`, or `absent` with no value.
A malformed proof reports `refused`/`invalid`; a resource refusal reports
`refused`/`resource`. Neither result is an Ethereum block-invalid verdict.

## Resource and trust boundaries

| Boundary | Local limit or assumption |
| --- | --- |
| RLP item / supplied proof node | 4,096 encoded bytes |
| RLP list nesting | 64 lists |
| Nodes in one proof bag | 128 |
| Secure path traversal | 65 visits for a 64-nibble key |
| Account inventory | 1,024 accounts |
| Storage inventory | 4,096 requested keys per account; 16,384 total |
| Witness node inventory | 65,536 total supplied nodes |
| Supplied code | 1 MiB per account |
| Aggregate proof bytes and code | 16 MiB, checked before hashing |
| JSON input | 2 MiB for primitive requests; 16 MiB for witness/list requests |
| JSON member names | 256 encoded bytes each; 256 members per object |
| Existing JSON lexical guard | Depth 64, numeric-token length 96, exponent magnitude 78 |
| Hash semantics | Explicit acceptance of the repository's experimental Keccak |

Transport and semantic budgets apply together. For example, hexadecimal
expansion can reach the JSON byte limit before the decoded witness byte
limit. These are implementation refusal limits, not Ethereum consensus
maxima or a proof of total process memory use. Build and tests use an
additional process memory cap and a shared compiler lock.

The root is supplied, not chosen by an independently verified consensus
client. Collision resistance and full refinement of Keccak, RLP and the trie
model to an independently formalized Ethereum specification remain open.
Signed envelope authentication, post-state trie updates, transaction and
receipt roots, complete fork/opcode/system-operation coverage, networking
and execution/consensus integration remain required for the full goal.

## Proof inventory

| Module | New checked statements | Principal boundary |
| --- | ---: | --- |
| `CanonicalRLP` | 8 | Bounds, whole-input consumption, retained bytes and scalar interpretation |
| `MPT` | 6 | Exact hash/inline binding, checked finite path, public lookup and preflight refusal |
| `WitnessAdmissionProofs` | 18 | Actual account/storage lookup, code commitment, inventory coverage/count and runner linkage |

The 32 additions preserve the existing 292 active claim records. Their
statements deliberately distinguish operational composition from normative
refinement. No new axiom, `sorry`, `native_decide`, `unsafe`, FFI, or imported
Ethereum implementation is used. Actual `#print axioms` output, source pins
and a closed theorem inventory are enforced by the dedicated checker.

## Reproduction

Use the repository-pinned Lean 4.33.1. Start in `formal/lean4`; every Lake
invocation below names the isolated package explicitly. Coordinate the lock
with other compiler jobs on a shared machine.

```sh
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=32768 MIMALLOC_ARENA_RESERVE=64M
ulimit -v 4194304
flock /tmp/ethereum-mpt-lean.lock lake -d evm-cleanroom -f lakefile-witness.toml build \
  EVMCleanroom.CanonicalRLPTests EVMCleanroom.WitnessAdmissionProofs \
  evm-witness-proof evm-transaction-list
cd evm-cleanroom
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/witness/run.mjs --output /tmp/mpt-native-results.json
node scripts/witness/transaction-lists.mjs --output /tmp/mpt-authenticated-lists.json
```

The first harness checks complete native responses against the independent
primitive/witness corpus and falsifies its comparator. The second constructs
fresh authenticated prestates for all 36 retained ordered-list fixtures and
compares actual native output. For the 30 executed fixtures, the original
decoded request is first reconstructed byte-for-byte and checked against its
retained SHA-256 before re-anchoring the parent root. The retained Geth and
EthereumJS execution results are dated evidence; these scripts do not claim
to rerun those execution clients. The external library constructs/checks
tries and recovers the retained signatures only as a test oracle.

The optional baseline comparison uses a separately built checkout of the
predecessor commit, without sharing compiled Lean artifacts. The final
evidence index records exact native hashes, invocation counts, refusals,
actual axiom transcripts and the scope of the generated-C recursion audit.
