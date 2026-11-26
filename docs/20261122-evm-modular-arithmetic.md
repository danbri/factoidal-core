# EVM modular arithmetic execution increment

Parent: https://github.com/danbri/factoidal-core/issues/652
Base: https://github.com/danbri/factoidal-core/pull/740 at `c33266528063272b900a8ceb0dfa34f6b365e3e7`.

## Obligations specified before code

1. The executable ADDMOD and MULMOD helpers use unbounded mathematical
   addition/multiplication *before* reducing modulo the third 256-bit word.
   A zero modulus yields zero; the result is a valid 256-bit EVM word.
2. The *actual* Core.step dispatch pops the two operands and the modulus
   in that order, requests eight gas, and uses the shared checked commit.
   Stack underflow or insufficient gas cannot commit.
3. The reached-opcode guard admits these two context-free operations without
   admitting environmental, storage, precompile or nested-call operations.
4. Independent Shanghai EthereumJS comparisons cover zero moduli, full-width
   high-bit operands, exact gas, short stack, and two ordinary outcomes.

## Implemented source

`EVMCleanroom/Core.lean`: ADDMOD (0x08) and MULMOD (0x09), full-precision
helpers, common ternary dispatcher, and actual-step correspondence theorems.
`EVMCleanroom/ModularProofs.lean`: mathematical word-value specifications.
`EVMCleanroom/Frame.lean`: guarded instruction admission.
`EVMCleanroom/Tests.lean`: executable boundary guards.
`scripts/differential/solidity-pure.mjs`: 100 new oracle comparisons,
including four fault cases, on top of the retained 83 comparisons.

All source claims require **fresh CI** on the new head. The previous
checkpoint's green tests do not validate this patch. The selected 60-theorem
manifest remains the existing separate audit set; the new theorems are
compiled and printed but are not yet independently expert-reviewed.
The proof kernel/compiler, EthereumJS reference implementation and fork
selection remain trust boundaries.

## Still missing

This closes neither signed division/remainder, SAR, EXP and SHA3,
nor CALL/CODE/RETURNDATA byte-window copying, nested journals, CREATE,
precompiles, fork-complete state/transaction/block rules, Engine API or
independent assurance. The separate measured tail regression stays in
https://github.com/danbri/factoidal-core/issues/739.
