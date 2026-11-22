# Lean 4 EVM — independently authored, machine-checked seed

**Restricted Lean 4 EVM prototype.** This stand-alone project
executes selected opcode, frame, transaction and block replay cases. Full
execution, fork coverage, Ethereum peer networking and consensus, and formal
refinement to EELS remain open.
[Full Lean Ethereum execution and consensus goal, #725](https://github.com/danbri/factoidal-core/issues/725) ·
[Execution-layer milestones](ROADMAP.md#execution-layer-subgoal)

The original proof record covers the initial interpreter and its trust
boundaries. The active evidence ledger records subsequent claims with their
source revisions, checks and limitations.
[Original proof scope](SOUNDNESS.md) ·
[PR #642 (initial interpreter proofs)](https://github.com/danbri/factoidal-core/pull/642) ·
[Active evidence ledger](evidence/active-claim-manifest-v2.json)

The code is isolated under `formal/lean4/evm-cleanroom` and uses the same
Lean 4.33.1 release as Factoidal without depending on its large Lean library.

## Build and inspect

```sh
cd formal/lean4/evm-cleanroom
lake build
lake env lean EVMCleanroom/Proofs.lean
lake env lean EVMCleanroom/MemoryGas.lean
lake env lean EVMCleanroom/Tests.lean
```

The dedicated GitHub Actions workflow
[`evm-cleanroom.yml`](../../../.github/workflows/evm-cleanroom.yml)
builds the default library and runs an axiom audit.
`#guard` executes examples during the Lean build; `#print axioms`
reports theorem dependencies. These are distinct forms of evidence.

## Published EELS state-test replay

- **Prague.** Six of six official EIP-7623 fixture cases reproduced the
  published state roots, with zero failures and zero unsupported cases. They
  cover protected and unprotected type-0 transactions and one envelope each
  of types 1–4. Lean executes the empty-code frame and computes the restricted
  fee, balance, nonce and EIP-7702 delegation updates. The blob fixture has
  zero excess blob gas. The authorisation fixture covers a single new
  authority and its delegation state. The host uses EthereumJS for signed
  transaction decoding, sender recovery and account-trie serialization.
  [Prague CI evidence at `ff3251d`](https://github.com/danbri/factoidal-core/actions/runs/44940731780)
- **Cancun.** Six of six official `test_push0_contracts` cases reproduced
  the published state roots for nonempty bytecode, storage changes and
  stack-overflow rollback. The same fixture contains 18 cases for other forks
  that this gate leaves unexecuted.
  [Fixture and prior Cancun CI evidence](CONTRACT_EELS.md)

Axiom-audited Lean theorems cover zero-gas empty-code termination, exact
sender debit accounting, gas bounds, nonce advancement and fee conservation
relative to the model. The EthereumJS trie and specification correspondence
remain outside those proofs.

The Prague evidence run rejected nine tampered fixture controls and six
tampered result-ledger controls. Fixture and dependency digests are pinned
in the [workflow](../../../.github/workflows/evm-cleanroom.yml).

## Authenticated historical Frontier replay

The restricted replay of Ethereum mainnet block **46,147** checks the signed
transaction, header and published transaction and receipt commitments. Pinned
account paths authenticate the transfer prestate against parent block 46,146's
state root. Lean settles the transfer and miner fee. A separate 5 ETH Frontier
reward is applied to reach the final block state. The Lean-driven replay with
an EthereumJS trie host and the independent Python checker both reproduced
the receipt's intermediate state root and the final block state root. The
evidence ledger records the exact hashes, proof mutations and subsequent
Keccak padding fix. The published headers and canonical chain selection
remain external inputs.
[Historical CI run at `e59416f5`](https://github.com/danbri/factoidal-core/actions/runs/44995444945) ·
[Evidence ledger](evidence/active-claim-manifest-v2.json)

## Calldata and bounded CALL execution

`evm-subset --frame-call HEX CALLDATA_HEX GAS FUEL` executes one frame with ABI
input. `CALLDATALOAD` reads a zero-padded big-endian word at the full-width
offset and `CALLDATASIZE` gives the input size. `CALLDATACOPY` and `CODECOPY`
pad reads beyond their source with zeros. `CODESIZE` reports the current code
length. `RETURNDATASIZE` reports the last child buffer size and `RETURNDATACOPY`
checks the full source range, even for zero bytes. Frame output includes exact
gas and stack words, allocated memory, return or revert bytes, and truncation
flags for the 4,096-byte observation limit. The standalone calldata matrix
has 331 independent Shanghai EthereumJS cases.
[Calldata differential](scripts/differential/calldata.mjs)

`evm-subset --call-opcode PARENT_HEX CHILD_HEX GAS FUEL` executes the `CALL`
opcode against a fixture world. The parent and child addresses are `0xc1` and
`0xc3`. Optional account and entry-context fields set the balances, child
nonce, read-only flag, opcode profile and depth. The optional third runtime
is at `0xc4`. The default fixture starts with cold addresses. The final
optional field prewarms the parent. Run the command without arguments to
see the positional fields.

The `CALL` dispatcher shares a simulation fuel budget across frames and
checks depth before child entry. It charges for both memory windows before
forwarding gas, retains the caller's original storage snapshot, and passes
child input as an immutable view of caller memory. A returning or reverting
child publishes its full output to the caller's last-child buffer. The caller
copies only the bytes that fit the paid output window. The journal retains a
successful child's changes and restores the caller's checkpoint after a child
failure. The JSON fields `parentMemory*`, `returnData*` and `returnBytes*`
report bounded snapshots of parent memory, the last-child buffer and the
parent's terminal output respectively. Precompiles and unsupported
instructions produce an indeterminate result when reached.
[CALL implementation](EVMCleanroom/CallOpcode.lean) ·
[Byte copy proofs](EVMCleanroom/ByteCopyProofs.lean) ·
[Byte-opcode differential](scripts/differential/byte-copy.mjs) ·
[Nested CALL differential](scripts/differential/call-data.mjs) ·
[Run evidence](../../../docs/20261122-evm-call-data-nesting.md)

`evm-subset --pure-frame-call HEX CALLDATA_HEX GAS FUEL` starts a read-only,
zero-value frame and checks each fetched opcode before dispatch. This lets
the interpreter run a compiler-produced Solidity runtime with its metadata
intact and refuse context-dependent instructions if execution reaches them.
The ordinary `--frame-call` command is also available.
[Solidity fixture and reproduction](scripts/differential/fixtures/solidity-pure/README.md)

The read-only RPC tool resolves the provider's canonical block hash for
Ethereum mainnet, Ethereum Sepolia, Polygon PoS Amoy, Polygon PoS mainnet or
OP Sepolia and records provider assertions. Its optional local comparison covers halt kind and
complete return or revert bytes for the admitted bytecode subset. Synthetic
code overrides are labelled in the evidence. The separate mainnet witness
gate binds the captured SwapRouter runtime to its pinned header's state root.
Provider observations supply canonical chain selection and the capture leaves
transaction execution and consensus unverified.
[RPC capture commands, Ethereum L1 calls and proof scope](scripts/rpc/README.md) ·
[Direct deployed OP Sepolia call](../../../docs/20261122-evm-solidity-deployed-call.md#direct-deployed-runtime-comparison)

## External executable interface and first official-fixture integration

The CLI executes **only the currently supported opcode subset** with supplied
bytecode, gas and step fuel. Its version-2 JSON output encodes gas, program
counters, memory sizes and 256-bit words as **lossless decimal strings**:

```sh
cd formal/lean4/evm-cleanroom
lake exe evm-subset 600260030100 100 10
# {"schemaVersion":2,"status":"ok","gasRemaining":"91","pc":"6","halted":true,"stack":["5"],"memorySizeBytes":"0","memoryWord0":"0","memoryObservedBytes":"0","memoryTruncated":false,"memoryHex":""}
```

Machine input errors are distinct from EVM execution errors. This interface
does **not** decode signed transactions or access account state, and the
counter used for execution fuel is a harness limit, *not* Ethereum gas.

The standalone `scripts/eels-state-preflight.mjs` checks the envelope of
**genuine published EELS state-test JSON**. CI downloads a version-pinned
Shanghai/PUSH0 fixture from the EthereumJS mirror, identifies its test
vectors, pre-state accounts and expected post-state/log hashes, then
deliberately reports **zero executed / zero conformance passes**.
The **preflight** still correctly reports zero executed cases; the separate
EELS replay tool described above now executes a restricted official subset.
Parsing alone is never counted as an execution pass.

A separate `scripts/check-eels-gas.mjs` test executes **14 actual Lean
bytecode programs** and compares their measured gas deductions with the
opcode gas tiers from EELS Prague's `vm/gas.py`, pinned to execution-specs
commit `1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653`. This is
real *external reference checking of static opcode gas costs*, not official
state-test consumption, transaction replay, or a general EVM semantics proof.
The CI assertion requires all 14 cases to match. A further
`check-eels-memory.mjs` script exercises six memory-opcode cases against
the pinned EELS memory-gas formula and compares observed memory size,
word contents and gas. These are independent **narrow reference checks**,
not a formal semantics refinement or an executed official state-test fixture.

### Independent execution differential gate

The [differential laboratory](scripts/differential/README.md) now compares
the Lean executable with the independently maintained **EthereumJS EVM 10.1.3**
under **Prague** rules. The reference and every transitive npm dependency
are pinned by a committed integrity-checked `package-lock.json`; CI uses
`npm ci`, not fresh dependency resolution.

[Passing 10,000-case CI run](https://github.com/danbri/factoidal-core/actions/runs/44626646466)
(seed `20261119`, corpus SHA-256
`610012bd5b278c5e4d08545560beed11910e01c0233ad8f9c9a4c9a52e0a2efb`):

- **10,000 compared / 10,000 matched**; **9,733 unique execution inputs**;
  **2,775 matching deliberately exceptional outcomes**.
- The comparison includes **complete memory bytes up to 4,096 allocated
  bytes**, with explicit observed-length and truncation flags; truncated
  snapshots cannot count as full matches.
- The other observables are result status, exact error category (on errors),
  gas remaining, program counter, halted flag, complete stack and allocated
  memory size. All large values use exact decimal strings.
- Complete input JSONL, generated SHA-256, exact dependency lock, report and
  counterexamples are archived as CI artifacts.

These are **single-frame synthetic bytecode experiments**, not historical
mainnet transactions or official EELS-generated state-test executions.
Only the *error category*, not state/rollback/gas-burn equivalence, is
currently compared on exceptional executions. Shared semantic mistakes
remain possible despite agreement between the two implementations.

See [ROADMAP.md](ROADMAP.md) for acceptance gates G0–G6, real mainnet witness
requirements, deployed-contract verification and independent review.
See [issues #649–#652](https://github.com/danbri/factoidal-core/issues/649)
for tracked implementation milestones.

## Reading order

1. [`EVMCleanroom/Core.lean`](EVMCleanroom/Core.lean): bounded 256-bit
   words, 1,024-element stack, local state, instruction planning, gas
   charging, restricted opcode dispatch and fuel-limited `run`.
2. [`EVMCleanroom/Proofs.lean`](EVMCleanroom/Proofs.lean): helper and
   whole-step theorems, arbitrarily long execution traces, exact cost-labelled
   traces, a bridge from actual `run` executions to those traces, and
   a universal PUSH1 jump-target boundary lemma.
3. [`EVMCleanroom/JumpProofs.lean`](EVMCleanroom/JumpProofs.lean) and
   [`EVMCleanroom/JumpCompleteness.lean`](EVMCleanroom/JumpCompleteness.lean):
   declarative instruction boundaries, forward decoding paths and general
   **soundness and completeness** theorems. For arbitrary bytecode arrays,
   the locally accepted JUMPDEST positions are exactly the in-bounds
   decoded boundaries holding opcode 0x5b, skipping PUSH1..32 immediates.
   The relation and decoder share the opcode-width function; independent
   EELS equivalence is not yet proved.
4. [`EVMCleanroom/Memory.lean`](EVMCleanroom/Memory.lean): sparse
   zero-filled byte memory, big-endian reads/writes, read-after-write and noninterference proofs, and a theorem that 32-byte writes cannot change allocation size.
5. [`EVMCleanroom/MemoryGas.lean`](EVMCleanroom/MemoryGas.lean): independent
   EVM memory-expansion price model, monotonicity and path-independence
   proofs for *arbitrarily many* memory-growth events, and zero-length
   memory-access corner cases.
6. [`EVMCleanroom/Tests.lean`](EVMCleanroom/Tests.lean): executable
   regression vectors and 256-bit arithmetic edge cases derived from
   official Ethereum execution-specification test expectations.
7. [`SOUNDNESS.md`](SOUNDNESS.md): exact trusted boundary and missing
   conformance theorem.

## Interpreter design

`planStep : State → Except Error Plan` calculates effects but cannot
commit state updates. `step` accepts those plans only through
`commit`, which enforces the stack bound and gas charge. A supported
instruction can therefore be reasoned about as two separate obligations:

- Its planned effects and price match the corresponding EVM specification.
  **This remains to be independently established.**
- Every successfully committed plan preserves code and fork profile,
  enforces bounded stack, and deducts exactly its declared price.
  **This is already machine checked.**

`run_toTrace`, `Trace.canBill` and `run_has_exact_bill` connect the
real fuel-limited interpreter to its formal trace semantics and prove that
all successful executions have a reconstructible exact gas bill.

Memory pricing uses the EELS formula

```text
C_mem(words) = 3 * words + floor(words² / 512)
```

Theorem `MemoryGas.ExpansionTrace.exact_total` proves that any finite,
non-shrinking allocation sequence incurs exactly the same total
memory-expansion gas as expanding directly to its final size. A zero-length
access never grows memory, even at offset `2^256 - 1`.

**MLOAD, MSTORE, MSTORE8 and MSIZE are now executable**, including dynamic
memory-expansion gas and zero-initialised sparse byte storage. Plans prepare
functional memory changes, which are applied only following successful gas
charging. This does not prove EELS equivalence or world-state rollback.

## Opcode coverage

`STOP`, `ADD`, `MUL`, `SUB`, unsigned `DIV`, `SDIV`, `SMOD`, `ADDMOD`, `MULMOD`, `LT`, `GT`, `SLT`, `EQ`, `ISZERO`,
`AND`, `OR`, `XOR`, `NOT`, `BYTE`, `SHL`, `SHR`, `SAR`, `CLZ`, `ADDRESS`, `CALLVALUE`,
`CALLDATALOAD`, `CALLDATASIZE`, `CALLDATACOPY`, `CODESIZE`, `CODECOPY`,
`RETURNDATASIZE`, `RETURNDATACOPY`, `SELFBALANCE`, `POP`,
`JUMP`, `JUMPI`, `PC`, `GAS`, `JUMPDEST`, `MLOAD`, `MSTORE`, `MSTORE8`, `MSIZE`,
`PUSH0`, `PUSH1..32`, `DUP1..16`, `SWAP1..16`, `SLOAD`, `SSTORE`.
A separate `Frame.run` handles `RETURN` and `REVERT` and `CallOpcode.run`
handles the restricted `CALL` path.

`PUSH0` is gated by the coarse pre-/post-Shanghai profiles. The pre-Shanghai
profile leaves activation of `SHL`, `SHR`, `RETURNDATASIZE` and
`RETURNDATACOPY` indeterminate. `CLZ` requires the Osaka profile. Unsupported
opcodes return explicit errors.

The arithmetic tests include expected values from the official
[execution-spec-tests `addFiller.yml`](https://github.com/ethereum/execution-spec-tests/blob/main/tests/static/state_tests/VMTests/vmArithmeticTest/addFiller.yml).
They compare local stack results with those published expectations; they
do **not** run complete official account-state fixtures.

## Next proof milestone

A second, separately developed EELS/EthLib-compatible transition
semantics is needed, followed by a theorem of the following shape
(for exactly specified fork profiles and admitted opcodes):

```text
Lean interpreter step(s) = success(s')
      ⇒ EELS-compatible transition(s, s')
```

It must account for both success and exceptional outcomes, including
gas burn, rollback and state effects. Differential tests against pinned
official fixtures should support the proof effort but must not be
misrepresented as proofs.

After that: independently reviewed EELS memory-opcode refinement,
JUMPDEST conformance to EELS, external semantic refinement of the new
storage/frame slices and nested CALL checkpoints, contract
creation, receipts, fork transitions and ultimately a full execution client.

Sources: [EELS](https://github.com/ethereum/execution-specs),
[EthLib](https://github.com/ethereum/EthLib),
[Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf),
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean).

No Ethereum client or existing EVM formalization source code was copied
into this seed. No legal clean-room certification has been performed.
