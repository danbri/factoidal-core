# Calldata, return bytes and bounded nested CALL

The Lean EVM passes caller memory to an entered child as an immutable
byte view. A successful RETURN or a REVERT gives the caller the complete
child buffer. The caller writes `min(outputSize, childOutput.size)` bytes
into its paid output window, preserving the rest of memory. STOP, an
exceptional child and a CALL that fails its balance or depth check leave
the last-child buffer empty.
[Nested CALL and byte windows, #744](https://github.com/danbri/factoidal-core/issues/744) ·
[Full Lean Ethereum execution and consensus goal, #725](https://github.com/danbri/factoidal-core/issues/725)

## Implementation boundary

`CALLDATALOAD` still reads 32 big-endian bytes with zero padding at all
mathematical offsets. The added `CALLDATACOPY`, `CODESIZE` and `CODECOPY`
instructions use actual frame input and code. `RETURNDATASIZE` and
`RETURNDATACOPY` are admitted in the Shanghai-plus and Osaka profiles.
The coarse pre-Shanghai profile cannot select the EIP-211 activation point
and returns `unsupportedFork` for those two opcodes. `RETURNDATACOPY` checks
gas before comparing `source + length` with the return buffer size. A
zero-length read at the end succeeds and one past the end fails. Copy gas
is three plus three per ceiling-rounded 32-byte word and memory expansion.
[Core dispatcher](../formal/lean4/evm-cleanroom/EVMCleanroom/Core.lean) ·
[EIP-211](https://eips.ethereum.org/EIPS/eip-211)

The CALL continuation list shares one instruction-dispatch fuel budget
across frames. The depth guard runs before child entry. CALL prices the
larger memory-window endpoint before the EIP-150 cap, and keeps the value
stipend separate from charged forwarding. Each suspended caller commits its
current slot values, warmth and aggregate refund into its local world
before marking the target warm and taking the child checkpoint. A child
failure restores that saved world, preserving the caller's own target
warm-up and undoing that child's successful descendants. Successful
children keep their effects. Resumption projects the current world back
into the caller, including storage written through a self-call, while
preserving transaction-original slot values. A parent REVERT or exception
restores the parent entry world.
[CALL dispatcher and proofs](../formal/lean4/evm-cleanroom/EVMCleanroom/CallOpcode.lean)

Byte-view and copy-overlay creation use a fixed number of fields per operation
and allocate no byte array sized by an EVM length or offset. Each nonempty
copy adds one range overlay and zero-length copies preserve the existing
memory value. Reads can traverse accumulated functional writes and views.
Dispatch fuel and EVM depth bound their respective counters. Host resource
use of long overlay chains remains an open property. The CLI limits each
observed byte window to 4,096 bytes and emits the total size and a truncation
flag.
[Byte-view and memory definitions](../formal/lean4/evm-cleanroom/EVMCleanroom/Memory.lean) ·
[CLI and model scope](../formal/lean4/evm-cleanroom/README.md#calldata-and-bounded-call-execution)

## Evidence

The published implementation commit and local tested checkout have the same
Git tree, `7d2cbe6bbd1ccf1bb1abd3fb485d415c1f7bf944`. The clean native build
completed 51 jobs with Lean 4.33.1. Separate elaboration checked 96 selected
theorems across 17 source files. The active ledger verified 74 source pins
and rejected all three axiom-report mutations. All four ledger test groups
passed, including the fresh Cancun replay report controls.
[Published implementation](https://github.com/danbri/factoidal-core/commit/f9fec7cbc5213aef53c19b0561efd21abba7db0c)

The theorem inventory records the checked statements, their
sources and the actual axiom sets. The proofs cover view bounds, copy
non-interference and paid byte visibility, core dispatch, CALL scheduling and
resumption, and restoration of the caller and parent worlds in the named
failure handlers. The audit includes the four ADDMOD and MULMOD statements
from the preceding revision.
[Active evidence ledger](../formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json) ·
[Soundness boundaries](../formal/lean4/evm-cleanroom/SOUNDNESS.md)

- EthereumJS and Geth each matched all 124 standalone byte-opcode cases.
  EthereumJS matched all 122 CALL cases. Geth matched its 112 Shanghai
  CALL cases, which exclude five static-entry, three nonzero-depth, one
  Osaka and one raw-cold-parent fixture. Three separate precompile and
  fork refusals held, as did the full-depth simulation-fuel boundary.
  The reports retain the raw EthereumJS exception labels and identify
  where fixture expectations use Lean's EELS-style diagnostics.
  [Byte-opcode results](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-byte/byte-opcodes.json) ·
  [Nested CALL results](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-byte/call-nesting.json)
- The retained checks matched 10,000 raw bytecode cases, 331 calldata
  cases, 183 guarded Solidity cases and 330 prior CALL cases. All 42
  offline RPC tests passed. The six Prague and six Cancun fixture roots
  matched, and the restricted Frontier replay reproduced both published
  roots with the independent checker.
  [Retained execution results](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-byte/retained-summary.json) ·
  [State replay results](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-byte/state-replay-summary.json)

## Native timing

The paired Linux measurements cover process launch, execution and JSON
output. The 10,000-case batch produced byte-identical output. Its median
rose from 154.794 to 163.367 ms across 11 pairs. Nearest-rank p95, p99 and
maximum all rose from 181.091 to 199.809 ms. The range widened from
30.600 to 46.189 ms.

Across 160 pairs per CLI fixture, ABI frame median rose from 4.733 to
4.782 ms. Its p99 fell from 18.484 to 16.637 ms and its maximum rose
from 20.236 to 38.203 ms. The zero-window CALL median rose from 4.504
to 4.630 ms and p95 rose from 5.883 to 6.163 ms. Its p99 fell from
11.506 to 10.190 ms. The measurements vary by fixture and include process
startup. They show an observed raw-batch slowdown and a wider tail.
[Timing method and raw samples](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-byte/TIMING.md) ·
[Performance follow-up, #739](https://github.com/danbri/factoidal-core/issues/739)

The broader goal still requires fork-exact execution, the other call
variants, CREATE, precompiles, full transaction and block execution,
authenticated replay, persistent state, Engine API integration, and
execution and consensus networking. It also requires Lean beacon-state
transitions, fork choice, fork-indexed SSZ and BLS rules, and acceptance
testing and independent review of the integrated execution and consensus
layers.
[Ethereum roadmap](../formal/lean4/evm-cleanroom/ROADMAP.md)
