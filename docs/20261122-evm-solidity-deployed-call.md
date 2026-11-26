# Guarded Solidity execution and a deployed OP Sepolia call

Issue #736 adds a checked execution path for the bytecode of a reproducibly
compiled Solidity contract and a direct comparison with one deployed
implementation call. The base integration was published at
`be578f90d8711fe7701ce4bfa7a3f5fff2e756a0` and passed its execution,
state-replay and dedicated Frontier CI gates. Those results belong to
PR #737. Local validation of the new combined source passed at
`c8622a21827186ef6b9e922ca8c1b85b7e7e719f`. Hosted CI is pending.
[Issue #736](https://github.com/danbri/factoidal-core/issues/736) ·
[Base PR #737](https://github.com/danbri/factoidal-core/pull/737) ·
[Base EVM CI](https://github.com/danbri/factoidal-core/actions/runs/45013925419) ·
[Base Frontier CI](https://github.com/danbri/factoidal-core/actions/runs/45013925491)

## Guarded execution

`evm-subset --pure-frame-call HEX CALLDATA_HEX GAS FUEL` starts a read-only
frame with call value zero. The interpreter checks the opcode fetched at the
current program counter. Unreachable metadata and PUSH immediates do not enter
the instruction policy. A reached context-dependent opcode such as ADDRESS,
SLOAD, GAS or CALL yields an explicit policy refusal before dispatch. The RPC
client sends an explicit zero value and requires the frame's comparison
context marker. The existing `--frame-call` retains its ordinary dispatch
and output schema.

The Lean refinement theorem establishes that any conclusive guarded run
equals the ordinary frame run from the same state and fuel, including its
memory, gas, return or revert window, and checkpoint. A separate theorem
checks early instruction refusal. The signed comparison theorem relates
the executable SLT helper to two's-complement strict order on every
256-bit word. Dispatcher and context theorems cover stack underflow,
the three-gas SLT charge, zero-value CALLVALUE and preservation of the
read-only, zero-value context by successful core steps.
[Selected theorem declarations and actual axiom sets](../formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json)

## Reproducible runtime and differential tests

The `ge(uint256,uint256)` fixture pins solc
`0.8.30+commit.73712a01.Emscripten.clang`, the compiler and source digests,
Shanghai, optimisation with 200 runs, and the via-IR pipeline. The complete
123-byte runtime includes the compiler's metadata and has SHA-256
`43157a6981862c97757f117321f1281aff96d1b08eb8298be8b934f102b8219e`.
The runtime executes SLT for an ABI bounds check and CALLVALUE to enforce
zero value. The unsigned comparison in the function uses values on either
side of the 256-bit sign boundary.
[Compiler inputs and reproduction command](../formal/lean4/evm-cleanroom/scripts/differential/fixtures/solidity-pure/README.md)

The combined source's EthereumJS 10.1.3 Shanghai gate matched
83 of 83 cases, including 67 signed arithmetic and fault cases. The
compiled function's selected successful call uses 158 gas and fails when
given 157. Five reached-opcode policy refusals and one ordinary-frame
compatibility control ran separately. The offline RPC suite on the
guarded binary and compiler fixture passed 42 of 42 tests, with zero
skips. These are observations on fixed inputs. Compiler correctness
and an invariant for the deployed contract remain open.

## Combined local validation

Lean 4.33.1 completed 48 build jobs. The axiom audit matched all 60
selected printed axiom sets across 14 theorem source files, and the ledger
verified 62 source blobs. All four ledger test groups passed without skips.
The axiom audit rejected three deliberately incorrect expectations.
Scoped premerge ran three checks with zero failures, skipped three checks,
and completed in 18.3 seconds.

| Retained gate | Observed result |
| --- | --- |
| Calldata and CALL repair | 331 calldata matches, five CALL matches and the separate precompile boundary check |
| Storage, frames and call scheduling | 136 storage, 13 frame, 4 scheduler and 102 scheduler-boundary matches |
| Opcode CALL, value and context | 330 opcode, 450 value and 128 context matches |
| Osaka CLZ and synthetic corpus | 1,022 CLZ matches and 10,000 raw-bytecode matches, plus three corpus comparator controls |
| Prague state replay | Six published roots matched, nine fixture mutations and six ledger mutations refused |
| Cancun state replay | Six published roots matched, four mutations refused and 18 other-fork cases unexecuted |
| Authenticated Frontier replay | Both roots reproduced through Lean/EthereumJS and independent Python. The gates checked 24 Keccak known-answer vectors and refused six proof mutations and ten synthetic MPT mutations. |

In 16 paired native timings of a 70,000-instruction fixture, the JSON
outputs were identical. Median elapsed time was 16.37 ms before the change
and 16.44 ms after it. The observed ranges were 15.60–18.05 ms before
and 15.45–22.96 ms after, widening the spread from 2.45 to 7.51 ms.
With 16 samples per version, the nearest-rank p95 and p99 both select
the maximum, which increased from 18.05 to 22.96 ms. The observed tail
regression warrants follow-up. Individual samples were not retained, and
this comparison is limited to the local fixture.
[Timing follow-up, #739](https://github.com/danbri/factoidal-core/issues/739)

## Direct deployed-runtime comparison

On 22 November 2026 the OP Sepolia provider returned the full 7,848-byte
runtime for the Jovian GasPriceOracle implementation at
`0x4f1db3c6abd250ba86e0928471a8f7db3afd88f1`, at block **51,771,054**
with provider-reported hash
`0x4fa96dd7ac9bac264d2dcad1399e5b2ed422cd8bd21a6d1fb56c51f928407bbe`.
Its Keccak-256
`0xe9fc7c96c4db0d6078e3d359d7e8c982c350a513cb2c31121adf5e1e8a446614`
matches the code hash specified by the OP Stack Jovian deployment spec.
A JavaScript hash check and the independent Python Keccak routine each
computed that digest from the saved provider code.
The spec records the source build pin
`773798a67678ab28c3ef7ee3405f25c04616af19`.
[OP Stack deployment specification](https://specs.optimism.io/protocol/jovian/derivation.html#gaspriceoracle-deployment)

The call addressed the implementation directly, supplied value zero and
selector `0x313ce567` for `decimals()`, and used the provider's runtime
without a code override. The provider's return bytes and the guarded local
frame returned the same ABI word, `6`. The comparison covers that one
selector and result. Block identity, canonicality and the deployed runtime
are provider assertions, and the code hash check pins the observed bytes to
the published digest. This capture supplies neither an authenticated state
proof nor a contract invariant.
[Exact call and runtime evidence](../formal/lean4/evm-cleanroom/scripts/rpc/evidence/op-sepolia-jovian-decimals-51771054.json)

Two separate calls ran the locally compiled `ge` runtime as a **synthetic
code override**, on OP Sepolia block **51,771,081** and Polygon PoS block
**97,759,492**. Both providers and the local guarded interpreter returned
ABI `1` for `ge(2^255 + 1, 2^255)`. The 42-test offline RPC suite replays
these two observations and the deployed implementation observation without
contacting the providers.
[OP Sepolia override capture](../formal/lean4/evm-cleanroom/scripts/rpc/evidence/op-sepolia-solidity-ge-51771081.json) ·
[Polygon PoS override capture](../formal/lean4/evm-cleanroom/scripts/rpc/evidence/polygon-solidity-ge-97759492.json)
