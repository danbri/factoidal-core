# Soundness and trust boundaries — Lean EVM cleanroom seed

**Status: 2026-11-19. This is a restricted EVM model, not a verified
Ethereum client.**

This document is a claim ledger. It distinguishes Lean theorems about the
*implemented model*, executable regression checks, and facts still requiring
independent specification refinement.

## The executable boundary

- `Word` is a natural-number residue below `2^256`; `word` reduces
  arbitrary naturals modulo that modulus.
- `Stack` carries a proof that its list has at most 1,024 items.
- `State` contains bytecode, program counter, stack, gas, halted flag,
  a coarse pre-/post-Shanghai profile and sparse functional byte memory.
- `planStep` calculates the next program counter, stack, gas cost and halt
  bit, or refuses a locally invalid instruction.
- `commit` checks the stack limit and available gas; `step` either rejects
  a plan or applies it through this one controlled boundary. Planned
  memory changes are applied only after a successful gas check.
- `run` is fuel-limited and reports `stepLimit` if fuel is exhausted.
  Errors discard the local state in the result type. No transaction
  rollback or exceptional-halt gas-consumption rules are represented.

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
| Memory expands monotonically; byte stores preserve the high-water mark; stores can be read back at allocated addresses | `Memory.expand_monotone`, `Memory.writeByte_preserves_words`, `Memory.readByte_after_write`, `Memory.empty_expand_zero` | About sparse functional byte semantics, not a proof of all MLOAD/MSTORE effects |
| EVM memory cost is monotone | `MemoryGas.cost_monotone` | Mathematical memory pricing only |
| Memory expansion cannot be undercharged by subdivision | `MemoryGas.expansion_path_independent`, `MemoryGas.ExpansionTrace.exact_total` | Every finite monotone allocation sequence; not yet connected to opcodes |
| Empty memory access costs no expansion gas at any offset | `MemoryGas.zero_length_access_free` | Including offset `2^256-1` |

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

## External checks (not proof of conformance)

CI now runs an externally callable Lean bytecode executable, checks success,
stack underflow, out-of-gas and exact-STOP fuel exhaustion behaviour. The
`run_toTrace` theorem was updated to cover halting on the last fuel step.

The CI additionally parses a genuine published EELS-generated state-test
fixture (Shanghai/PUSH0, from an EthereumJS mirror pinned by SHA) and
deliberately reports **zero executed state tests and zero conformance passes**.
No post-state root, account effect or receipt is compared by that parser.

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

## What is not established

1. **No Ethereum specification equivalence.** There is no theorem of the
   form `step_lean ≈ step_EELS`, no EELS differential-test runner, and
   no complete opcode semantics. A perfectly proved wrong price or wrong
   opcode result remains a wrong Ethereum implementation.
2. **No complete gas or exception model.** Byte-addressed memory,
   MLOAD/MSTORE/MSTORE8/MSIZE and expansion pricing are implemented, but
   not formally refined to EELS. State rollback, exceptional gas burning,
   refunds, warm/cold storage access and calls remain outside the model.
3. **No complete protocol fork model.** The profile gates only PUSH0.
   Correct execution of the historical chain requires every relevant
   hard-fork transition, including other gas and opcode changes.
4. **No world-state or chain semantics.** Accounts, storage, transaction
   validity, roots, receipts, precompiles, nested calls, cryptography,
   fork choice, networking and consensus clients are not implemented.
5. **No compiler verification.** We do not compile Solidity/Yul, and
   cannot infer validity of Solidity contracts or Ethereum transactions.
6. **No production-security guarantee.** IO, resource exhaustion,
   implementation side channels, peer attacks and host-runtime behaviour
   remain unmodelled. The program uses Lean's trusted runtime to execute.
7. **JUMPDEST soundness is internal, not external conformance.**
   `validJumpdest_sound` proves every locally accepted jump target is a
   declarative instruction boundary with opcode `0x5b`, for arbitrary
   byte arrays and PUSH1–32 immediate widths. But the declarative
   boundary relation shares `opcodeWidth` with the executable scanner;
   *completeness* of the scanner is now also proved (in
   `JumpCompleteness.lean`), but independent refinement to EELS remains
   unproved.
8. **No strict legal clean-room certification.** Implementation files were
   independently written from public specification descriptions, not
   copied from existing clients or Lean EVM formalizations. The project
   has not undergone a formal clean-room provenance audit.

## Highest-value next proof obligations

1. Establish a *separate* EELS/EthLib-compatible state-transition
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
5. Extend the state to accounts, storage, calls, return/revert data,
   exceptional-halting semantics and fork-parameterized gas.
6. If/when optimized implementations are introduced, prove they refine
   the independent simple-step specification rather than proving only
   self-consistency of the optimized code.

## Upstream sources

- EELS: https://github.com/ethereum/execution-specs
- Official fixture source:
  https://github.com/ethereum/execution-spec-tests/blob/main/tests/static/state_tests/VMTests/vmArithmeticTest/addFiller.yml
- Ethereum Lean library:
  https://github.com/ethereum/EthLib
- Yellow Paper: https://ethereum.github.io/yellowpaper/paper.pdf
- Independent EVM/Yul semantics:
  https://github.com/NethermindEth/EVMYulLean
