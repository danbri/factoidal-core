# Clean-room EVM in Lean 4 (initial seed)

**Prototype. This is not a complete Ethereum implementation.** The goal is to
start a genuinely independent executable semantics, with small machine-checked
proofs and a test harness, then refine it against the Ethereum Execution Layer
Specifications (EELS).

This is a **standalone Lake project**, under `formal/lean4/evm-cleanroom`, pinned
to the same Lean 4.33.1 toolchain as Factoidal. It does not modify or depend on
the large `L4Factoidal` build.

## Run

```sh
cd formal/lean4/evm-cleanroom
lake build
lake env lean EVMCleanroom/Tests.lean
lake env lean EVMCleanroom/Proofs.lean
```

The `#guard` cases run inside Lean. The four printed `#print axioms`
commands make assumptions inspectable.

## Implemented subset

* A 256-bit bounded natural word type with modular arithmetic.
* A 1024-element bounded stack (the limit is a proof field).
* A bytecode array, instruction pointer, gas, and a halted state.
* `STOP`, `ADD`, `MUL`, `SUB`, unsigned `DIV`, `POP`, `JUMP`, `JUMPI`,
  `PC`, `GAS`, `JUMPDEST`, `PUSH0`, `PUSH1..32`, `DUP1..16`, `SWAP1..16`.
* `PUSH0` is gated by a deliberately coarse pre-/post-Shanghai profile.
* Instruction-gas charging, stack underflow/overflow checks, bad-jump checking,
  including exclusion of `JUMPDEST` bytes inside PUSH immediates.
* Proof declarations: modular addition commutativity, word/stack bounds,
  gas nonincrease and code immutability for successful `commit` calls.

Unsupported opcodes fail explicitly. `Except Error State` is *not* a model of
transaction-level rollback or exceptional-halt gas consumption.

## Major omissions

Memory and memory-expansion gas, storage and gas refunds, warm/cold accesses,
precompiles, environmental opcodes, logs, calldata, calls, contract creation,
REVERT, return-data, transactions/receipts/account state, cryptography,
state tries, external consensus, network protocols, execution Engine API,
EOF and historical fork handling. There is **no EELS differential conformance
claim** or mainnet-compatibility claim.

Theorem statements are about the *local implementation*, not yet an
equivalence proof with the Ethereum Yellow Paper, EELS, Solidity or real
execution clients. The proof files require a successful Lean build to count as
machine checked. No external axioms or `sorry` are intended.

## Follow-on steps

1. Obtain passing Lean CI and audit each `#print axioms`.
2. Prove per-opcode `step` preservation, not only the shared commit helper.
3. Differentially compare every covered opcode against pinned EELS-generated
   official fixtures and add adversarial boundary cases.
4. Define EVM memory, gas expansion and transactional state semantics
   precisely before implementing additional opcodes.
5. Prove a future optimised implementation refines this simple semantics.

References:
- https://github.com/ethereum/execution-specs (CC0)
- https://github.com/ethereum/EthLib
- https://ethereum.org/developers/docs/evm/opcodes/
- https://ethereum.github.io/yellowpaper/paper.pdf

No client or formalisation implementation code was copied. The new files should
follow the parent repository's licensing policy.
