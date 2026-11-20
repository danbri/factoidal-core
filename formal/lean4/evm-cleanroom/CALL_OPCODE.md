# First actual Lean EVM CALL bytecode and parent-level atomic rollback

**Scope (20 November 2026):** a restricted depth-one, zero-value `CALL` implementation in `EVMCleanroom/OpcodeCall.lean`, stacked on PRs #662 (EIP-150 child scheduler), #668 (active assurance) and #661 (6/6 official nonempty EELS state roots). Not full Ethereum CALL semantics.

## Execution boundary

- `OpcodeCall.run` drives the parent's real bytecode, including its actual opcode `0xf1`. The 7 EVM stack arguments are consumed top-first (gas, address, value, input offset/size, output offset/size). Only **value=0 and four zero input/output words** are accepted.
- The target is a distinct regular account (no precompiles, self-CALL or invalid 160-bit address). Callee runs the previously supported `Frame.run` instruction subset: `STOP`, memory, storage, `RETURN`, `REVERT`, arithmetic, jumps, etc., but cannot itself issue CALL.
- Account cold/warm charging uses EIP-2929 before EIP-150 forwarding; unused child gas returns to parent. Successful children push 1; REVERT or exceptional children push 0; child failure alone does not exceptional-halt the parent. The parent's subsequent bytecode executes normally.
- Parent top-level exceptional failure rolls back the *entire* entry world, including successful child effects. Simulation fuel exhaustion and unsupported instructions are **unsupported**, never mislabelled consensus-invalid.
- CLI: `lake exe evm-subset --call-opcode 5f5f5f5f5f60c3617530f100 600160005500 195 50000 30 30` should return status `stopped`, success flag 1, child slot0=1 and remaining gas 25278.

## Machine-checked theorem, exact scope

`EVMCleanroom.OpcodeCall.run_exception_world_atomic`: for **any restricted input parent/child bytecode, parent fuel and child fuel, and every account address and storage key**, if `OpcodeCall.run` returns an exceptional **parent** outcome, then the result exposes the same account map and original storage snapshot as at call entry, the same refund, and the same storage-slot warmth. The parent call address is warm, reflecting the parent entry effect.

This property is enforced by the executable `settleParent` checkpoint barrier and proved about the actual `run` function; it is *not* an independent EELS semantic-refinement theorem. It depends on Lean's `propext` and no `sorryAx` in the initial CI proof; the strengthened version is subject to the latest CI. `CallGas.schedule_conserves` and `CallGas.resumed_gas_exact` separately prove the EIP-150 budget law for any admitted numbers.

## Independent client verification

`scripts/differential/call-opcode.mjs` executes **identical complete parent bytecode containing `0xf1` and identical child bytecode** using the pinned EthereumJS Cancun reference and Lean. Five cases: successful child SSTORE, child REVERT, child exceptional INVALID, empty child, and parent INVALID after an otherwise successful child (full outer rollback). Compare actual gas remaining, CALL stack success flag and child persistent storage. The first three inherited CI jobs and new five-case comparison passed at [run 44743999711](https://github.com/danbri/factoidal-core/actions/runs/44743999711).

## Explicit gaps

Arbitrary nested depth/reentrancy; CALL with value, stipends or new accounts; account address warming initialization from transaction envelope; calldata, memory expansion/copy and returndata; other call-family opcodes; precompiles; caller/contract context; gas refund caps; logs/receipts; fork-dependent changes; state-root authentication and actual EELS CALL-state fixture execution; mainnet block replay; independent spec refinement. The current trusted components include Lean compiler/runtime, EthereumJS test oracle and fixture/host wiring. No blanket Ethereum correctness claim follows.