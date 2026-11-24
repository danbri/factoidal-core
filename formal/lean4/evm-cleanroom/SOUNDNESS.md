# Soundness and trust boundaries — Lean EVM cleanroom seed

**2026-11-22. This record covers the restricted Lean EVM model.**

This document is a claim ledger. It distinguishes Lean theorems about the
*implemented model*, executable regression checks, and facts still requiring
independent specification refinement.

## The executable boundary

- `Word` is a natural-number residue below `2^256`; `word` reduces
  arbitrary naturals modulo that modulus.
- `Stack` carries a proof that its list has at most 1,024 items.
- `State` contains code, program counter, stack, gas, halt status, a coarse
  opcode profile, sparse functional memory, account-local storage, and
  bounded views for calldata, the last child buffer and terminal output.
- `planStep` calculates the next program counter, stack, gas cost and halt
  bit, or refuses a locally invalid instruction.
- `commit` checks the stack limit and available gas; `step` either rejects
  a plan or applies it through this one controlled boundary. Planned
  memory changes are applied only after a successful gas check.
- `Core.run` is fuel-limited and reports `stepLimit` if fuel is exhausted.
  `Frame.run` settles single-frame RETURN, REVERT and exceptional halts.
  `CallOpcode.run` uses a world journal and an explicit continuation list
  for the supported nested CALL path. The shared fuel budget is a simulation
  limit on interpreter dispatches, including synthetic STOP past the code end.

## Machine-checked properties

The following declarations compile with Lean 4.33.1 and are explicitly
exposed to the axiom audit in the dedicated workflow:

| Claim | Theorem(s) | Qualification |
|---|---|---|
| Bounded EVM word and stack | `word_bounded`, `commit_stack_bounded` | Bounds of modeled values |
| Modular addition commutes | `word_add_comm` | Other algebraic laws not claimed here |
| Successful commit has exact gas debit | `commit_gas_exact`, `commit_gas_nonincreasing` | Cost value comes from the interpreter |
| Successful step does not change code or fork | `step_code_unchanged`, `step_profile_unchanged` | Only on successful modeled transitions |
| Successful step has exact gas bill | `step_has_exact_bill`, `step_gas_nonincreasing` | No Ethereum-pricing correctness proof |
| Finite traces preserve code and do not generate gas | `Trace.code_unchanged`, `Trace.gas_nonincreasing` | Trace is the locally defined transition relation |
| Billed traces conserve all spent gas | `BilledTrace.gas_exact`, `BilledTrace.toTrace` | Bill constructed from opcode plans |
| Successful *actual runs* correspond to these traces and bills | `run_toTrace`, `Trace.canBill`, `run_has_exact_bill` | Bridges the fuel-limited executable driver, not EELS |
| All successful actual runs preserve code and never increase gas | `run_code_unchanged`, `run_gas_nonincreasing` | Derived from the preceding bridge |
| A PUSH1 payload is never a jump destination, for **any** payload byte | `push1_payload_not_jumpdest`, `push1_following_jumpdest` | Local PUSH1 semantics |
| Accepted JUMPDESTs occur **exactly** at in-bounds decoded opcode boundaries, for **arbitrary bytecode** including PUSH1–32 immediate skipping | `validJumpdest_sound`, `validJumpdest_complete`, `scanJumpdest_sound`, `ForwardPath.scan_accepts`, `opcodeWidth_bounds` | Local soundness and completeness; decoder and relation share opcode-width definition, so independent EELS equivalence remains unproved |
| Memory expands monotonically; byte stores preserve the high-water mark; stores can be read back at allocated addresses | `Memory.expand_monotone`, `Memory.writeByte_preserves_words`, `Memory.writeWord_preserves_words`, `Memory.readByte_after_write`, `Memory.readByte_write_other`, `Memory.empty_expand_zero` | About sparse functional byte semantics, not a proof of all MLOAD/MSTORE effects |
| EVM memory cost is monotone | `MemoryGas.cost_monotone` | Mathematical memory pricing only |
| Memory expansion cannot be undercharged by subdivision | `MemoryGas.expansion_path_independent`, `MemoryGas.ExpansionTrace.exact_total` | Every finite monotone allocation sequence in the pricing model |
| Empty memory access costs no expansion gas at any offset | `MemoryGas.zero_length_access_free` | Including offset `2^256-1` |
| Bounded byte views and sparse copy overlays | `ByteView.readByte_inside`, `ByteView.readByte_outside`, `Memory.readByte_expandedCopy_inside`, `Memory.readByte_copyFrom_outside` | Copy semantics at arbitrary mathematical addresses with the indicated memory allocation |
| Actual bytecode copy and return-buffer boundary | `step_callDataCopy`, `step_codeCopy`, `step_returnDataCopy_readByte`, `step_returnDataCopy_outOfBounds` | Funded steps with the specified operands and admitted profile where applicable |
| CALL scheduling, output and child checkpoints | `CallOpcode.schedule_exact`, `CallOpcode.resumeCall_observations`, `CallOpcode.resumeChild_revert`, `CallOpcode.resumeChild_exception` | Model-level facts about the named scheduler and resumption functions |
| Public CALL runner preserves the entry world on parent failure | `CallOpcode.run_parent_revert_atomic`, `CallOpcode.run_parent_exception_atomic` | Any completed outcome of the indicated kind, including after successful child work |

The core gas equations are:

```
successful step:  output.gas + plan.gasCost = input.gas

successful run:   output.gas + Σ(plan.gasCost) = input.gas

memory cost(w):   3*w + floor(w*w / 512), w = count of 32-byte words

memory expansion from a to b:
                 cost(max(a,b)) - cost(a)
```

`EVMCleanroom/Tests.lean` and `MemoryGas.lean` also contain executable
`#guard` examples. The overflow cases are adapted from the official
`execution-spec-tests` `addFiller.yml` **expected outcomes**, not a
claim that we execute or pass the whole Ethereum state-test fixture.

The CI workflow `.github/workflows/evm-cleanroom.yml` uses
`leanprover/lean-action@v1` with `axiom-audit: true`. The theorem files
include `#print axioms` declarations. A passing check verifies the
stated Lean propositions against Lean's formal environment, within the
auditor's configured standard axiom allowlist. It does **not** verify
Lean's kernel, code generation, deployed binaries, external dependencies
or EELS semantics.

Byte-view construction stores a backing function and a size. `CALLDATALOAD`
requests 32 reads at mathematical offsets. Each nonempty copy creates one
functional range overlay and does work independent of the numeric byte
count, apart from arithmetic on the encoded naturals. A zero-length copy
returns the existing memory. Reads can traverse older writes and memory
snapshots, so dispatch fuel and CALL depth limits do not bound every host
read or establish a host stack-use bound. The CLI reports at most 4,096
bytes of each observed window and marks truncated observations.

`KECCAK256` checks gas before the memory read and limits work to the host
input cap, bounding the number of 136-byte blocks processed. The theorems
cover the view, the dispatch and the local Ethereum padding. The pure
implementation requires an explicit experimental opt-in in executable
runs. Independent cryptographic refinement and constant-time operation
remain open. Each `LOG0`–`LOG4` adds a single immutable data view with its
address and ordered topics after the stack, gas and static checks. The
standalone rollback proofs cover the exact entry log list.
[Hash and log claim boundary](../../../docs/20261122-evm-hash-log-boundary.md)

The witness-limited transaction theorems cover actual admission, escrow
and settlement. Reverting and exceptional outcomes restore the execution
checkpoint's slot values and logs before fee settlement. The host supplies
signature recovery, header context and account and storage authentication.
The reached-account and reached-slot checks prove refusal when the
specified witness is absent. These checks operate on the provided witness
set. They leave independent verification of its roots to the replay host.
[Transaction proofs](EVMCleanroom/CallTransactionProofs.lean) ·
[World-aware witness checks](EVMCleanroom/CallOpcode.lean)

## Genuine EELS state-test execution (scoped)

On 19 November 2026 the historical Prague runner matched **four of six**
published EIP-7623 state-test roots. The two unsupported cases at that
checkpoint required blob fees and EIP-7702 authorisation.

The active evidence ledger records **six Prague EIP-7623 roots** for the
restricted type-0 through type-4 envelope runner and **six Cancun roots**
for the nonempty PUSH0 contract fixture. The Cancun count covers six
executed fork cases in a fixture with 24 cases across all its forks. The
Prague runner handles empty-code execution and restricted transaction fee,
nonce and balance settlement. Theorems
`empty_code_halts_without_spending_gas`,
`TxAccounting.settle_charged_bounded`,
`TxAccounting.sender_balance_conservation`,
`TxAccounting.sender_nonce_advances` and
`TxAccounting.fee_conservation` are machine checked against the Lean model.

Signed-envelope parsing and MPT serialisation use EthereumJS. The host
constructs account sets and maps fixture fields. Specification refinement of
transaction execution is open. The restricted Frontier transfer replay
has its own historical evidence.
[Fixture runners](scripts/eels/README.md) ·
[Active evidence ledger](evidence/active-claim-manifest-v2.json) ·
[Frontier replay](README.md#authenticated-historical-frontier-replay)

## External checks (not proof of conformance)

CI now runs an externally callable Lean bytecode executable, checks success,
stack underflow, out-of-gas and exact-STOP fuel exhaustion behaviour. The
`run_toTrace` theorem was updated to cover halting on the last fuel step.

The CI additionally parses a genuine published EELS-generated state-test
fixture (Shanghai/PUSH0, from an EthereumJS mirror pinned by SHA) and
reports **zero executed state tests** in that *preflight-only* job. The
scoped Prague and Cancun replay jobs execute cases and compare state roots.

A different CI step executes 14 supported bytecode scenarios in the actual
Lean interpreter and compares **gas deductions only** to the static opcode
charges in EELS Prague `vm/gas.py` at
`1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653`.
That step must pass to keep the PR green. A separate runner exercises
six MLOAD/MSTORE/MSTORE8/MSIZE scenarios and extreme-offset refusal,
comparing *actual* Lean results with EELS-derived dynamic memory pricing
and expected byte contents. Both external checks are narrow: they do not
establish a formal refinement theorem or execute full state tests. The external EELS file is an independently maintained reference,
while selection of our 14 scenarios remains our responsibility.

## Independent execution differential evidence

The draft PR now checks the *actual* Lean executable against the independently
maintained **EthereumJS EVM 10.1.3** using **Prague** rules and a committed
integrity-pinned npm lockfile (SHA-256
`cc95a62e125486d2de9a28cb5fc61c098b955aa22c2dd0b3dc0b19f2df770425`).

[CI run 44626646466](https://github.com/danbri/factoidal-core/actions/runs/44626646466)
compared **10,000 synthetic bytecode cases**, **9,733 distinct exact
execution inputs**, with **zero disagreements and oracle execution errors**.
The corpus includes **2,775 expected exceptional cases**; for those
the compared property is **exception category only**, not gas-burn,
rollback, frame post-state or receipt equivalence.

Successful cases compare gas remaining, program counter, halted flag, full
stack, memory allocation size, and all allocated memory bytes up to a
**4,096-byte explicit observation cap**. The runner refuses to count
truncated-memory results as full matches. The corpus hash is
`610012bd5b278c5e4d08545560beed11910e01c0233ad8f9c9a4c9a52e0a2efb`,
seed `20261119`. Complete cases, expected and observed outputs,
dependency versions and any mismatches are retained as CI artifacts.

The differential result covers the recorded bytecode cases. Synthetic
tests may miss entire opcode families, and the formal invariants concern
the local semantics. The official fixture passes come from the separate
scoped state-test replays described above.
See [differential methodology](scripts/differential/README.md) and
[roadmap](ROADMAP.md).

The byte and nested CALL comparisons run separate fixtures through the
Lean CLI, EthereumJS and a pinned Geth build. Each report records its
client-specific set of observations. EthereumJS labels some returndata
bounds exceptions `out of gas`. The fixture checks the corresponding Lean
diagnostic separately, and the comparison records the raw oracle labels.
The Shanghai Geth fixture requires a prewarmed parent. Its comparison
leaves out raw-cold parent, static-entry, nonzero-depth and Osaka cases.
The EthereumJS matrix and explicit Lean boundary tests cover those cases
within the limits recorded in the evidence.
[Byte-opcode differential](scripts/differential/byte-copy.mjs) ·
[Nested CALL differential](scripts/differential/call-data.mjs)

## Remaining proof and execution boundaries

1. **EELS refinement.** Opcode, gas, exception and journal theorems
   concern the local model. Reference refinement remains open.
2. **Fork selection.** `preShanghai`, `shanghaiPlus`, `cancunPlus` and `osaka` select
   subsets of opcode behaviour. Chain replay requires fork-exact
   transaction context, address prewarming and gas schedules.
3. **World and chain scope.** The functional world carries accounts, slots,
   warmth and a signed refund counter for the supported frame operations.
   The CALL family and identity precompile have bounded executable paths.
   CREATE, the other precompiles, complete transaction/block validation,
   receipts, networking and consensus remain open under
   https://github.com/danbri/factoidal-core/issues/725.
4. **Compiler and deployment scope.** Guarded execution checks the bytes
   of a Solidity compiler fixture and selected provider captures. Compiler
   correctness and deployed-contract properties need separate proofs.
5. **Runtime trust.** Kernel, compiler, host execution, resource exhaustion
   and implementation side channels remain trust boundaries.
6. **JUMPDEST reference behaviour.** The local soundness and completeness
   statements use the same `opcodeWidth` as the scanner. Comparison with
   independently specified instruction boundaries remains open.
7. **Provenance.** The project independently implements public specification
   descriptions. A formal clean-room provenance audit remains open.

## Cancun BLOBHASH integration boundary

`BlobCall.prepare` now preserves its validated, ordered versioned-hash list
through the internal fee-accounting request and into actual frame entry.
`validated_entry_blobHashes` relates successful header/blob preparation and
the actual value-transfer result to the executing frame's exact list and its
six-word bound. Core step theorems cover lookup, zero outside the full-width
index range, three-gas charging, underflow, out-of-gas and context preservation.
The actual CALL-family entry theorems carry the world's list into child frames.
They do not assume that an arbitrary externally constructed parent frame is
consistent with its world, or that a newly entered empty stack already holds
an index. The ordinary transaction entry always supplies an empty list.

The 38 guards and signed synthetic two-client matrix are tests. The matrix
binds both reference executions to identical signed bytes; Lean still receives
decoded inputs and synthetic witnesses. Signature recovery, receipt and trie
encoding, compiler/runtime, and the experimental Keccak implementation remain
trust boundaries. Hash access neither verifies a KZG proof nor makes blob
bodies available. Coarse older opcode profiles return a local fork refusal;
that is not a proof of fork-exact invalid-opcode behaviour. Prague transaction
execution and full block-inventory validation remain unfinished.

The selected theorem ledger and dedicated audit record actual compiler output,
source pins and falsification controls. Neither establishes a full Ethereum
refinement proof. Reproduction, exact counts and remaining work are recorded in
`docs/20261124-evm-blobhash-integration.md` at the repository root.

## Highest-value next proof obligations

1. Establish a *separate*, independently authored EELS-compatible state-transition
   denotation, identify matching fork configurations, then prove
   `step_refines_reference` **per covered opcode**, including precise
   success and failure conditions.
2. Pin upstream reference commits and run actual generated
   `execution-spec-tests` vectors and metamorphic differential tests.
3. Establish opcode-level EELS refinement for implemented memory reads,
   writes and expansion charges, including exception and rollback semantics.
4. Independently check the shared opcode-width semantics and JUMPDEST
   behaviour against EELS. Local soundness and completeness have both
   been proved for all finite bytecode arrays.
5. Extend the supported account and CALL slice to CREATE, the remaining
   precompiles and fork-exact environment and gas rules. The identity
   integration record is `docs/20261123-evm-identity-integration.md` at the
   repository root; its tests and local implementation theorems do not
   establish general EELS refinement.
6. If/when optimized implementations are introduced, prove they refine
   the independent simple-step specification rather than proving only
   self-consistency of the optimized code.

## Upstream sources

- EELS: https://github.com/ethereum/execution-specs
- Official fixture source:
  https://github.com/ethereum/execution-spec-tests/blob/main/tests/static/state_tests/VMTests/vmArithmeticTest/addFiller.yml
- Yellow Paper: https://ethereum.github.io/yellowpaper/paper.pdf
- Independent EVM/Yul semantics:
  https://github.com/NethermindEth/EVMYulLean
