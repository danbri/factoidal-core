# Lean 4 EVM — independently authored, machine-checked seed

**Status: prototype, not a complete Ethereum Virtual Machine or mainnet
client.** This stand-alone project develops a deliberately restricted EVM
interpreter and checks its internal correctness properties in Lean 4.
Correctness with respect to Ethereum's external specifications is the next,
separate obligation.

Read **[SOUNDNESS.md](SOUNDNESS.md)** before making any security or
compatibility claim. It is an explicit ledger of theorem scope, tested
examples, trusted boundaries and missing proof obligations.

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
Until transaction execution and state-root comparison exist, the entire
fixture denominator remains unsupported. A parsed fixture is not a passed
fixture.

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

`STOP`, `ADD`, `MUL`, `SUB`, unsigned `DIV`, `POP`,
`JUMP`, `JUMPI`, `PC`, `GAS`, `JUMPDEST`, `MLOAD`, `MSTORE`, `MSTORE8`, `MSIZE`,
`PUSH0`, `PUSH1..32`, `DUP1..16`, `SWAP1..16`.

`PUSH0` is gated by a coarse pre-/post-Shanghai profile. Unsupported
opcodes return explicit errors rather than executing as NOPs.

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
RETURN/REVERT, JUMPDEST conformance to EELS, storage and gas refunds,
nested calls, contract creation, account state, receipts, fork transitions
and ultimately a full execution client.

Sources: [EELS](https://github.com/ethereum/execution-specs),
[EthLib](https://github.com/ethereum/EthLib),
[Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf),
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean).

No Ethereum client or existing EVM formalization source code was copied
into this seed. No legal clean-room certification has been performed.
