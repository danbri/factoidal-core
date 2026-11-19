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
- `State` contains bytecode, program counter, stack, gas, halted flag and
  a coarse pre-/post-Shanghai profile.
- `planStep` calculates the next program counter, stack, gas cost and halt
  bit, or refuses a locally invalid instruction.
- `commit` checks the stack limit and available gas; `step` either rejects
  a plan or applies it through this one controlled boundary.
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
| A PUSH1 payload is not a jump destination for **any** payload byte | `push1_payload_not_jumpdest`, `push1_following_jumpdest` | General PUSH1 lemma, not a proof of full PUSH1–32 decoder correctness |
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

## What is not established

1. **No Ethereum specification equivalence.** There is no theorem of the
   form `step_lean ≈ step_EELS`, no EELS differential-test runner, and
   no complete opcode semantics. A perfectly proved wrong price or wrong
   opcode result remains a wrong Ethereum implementation.
2. **No complete gas or exception model.** Memory expansion prices are
   formalized separately but `MLOAD`/`MSTORE` and memory bytes are absent.
   State rollback, exceptional gas burning, refunds, warm/cold storage
   access and calls remain outside the model.
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
7. **No full JUMPDEST soundness/completeness result.** The generic theorem
   currently covers a PUSH1 payload. A theorem for arbitrary PUSH1–32
   streams remains a separate obligation.
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
3. Integrate byte-addressed memory and the proven expansion function
   into MLOAD/MSTORE/MSTORE8, with proved expansion/rollback accounting.
4. Prove the jump-destination parser sound and complete for *all*
   bytecode sequences including all PUSH1–32 immediate widths.
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
