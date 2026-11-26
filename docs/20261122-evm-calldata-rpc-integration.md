# EVM calldata, CALL and read-only RPC integration

Local validation passed on source commit
`cbcedb8b470c470f1a82b3e4fa9323e28c178339`. Remote CI for the integration
is pending. The working branch was assembled in a shallow checkout at
merge `b1fcf16a656007689b1fd66dcfdb17a4f05540a8`, with authenticated
Frontier replay parent `840c997996619808a961638e94a7b772f738539e` and
value-CALL and context parent `6ede61776c4cd27b18af22e7165250e12ae6e4e9`.
Earlier results retain their original source and CI attribution.
[Implementation tracker](https://github.com/danbri/factoidal-core/issues/734) ·
[Active evidence ledger](../formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json)

`--frame-call` runs one frame with calldata. It reports gas, stack and
bounded memory and return or revert bytes. The core reads 32-byte
big-endian calldata words with zero padding, supports full-width offsets,
and executes unsigned comparisons, bitwise operations and logical shifts.
Observations are limited to 4,096 bytes each for memory and return data,
with the total lengths and truncation reported. If both gas and stack
operands are insufficient, Lean can report `stackUnderflow` while
EthereumJS reports out of gas. Both exceptionally halt with zero gas and
empty return data. The RPC comparator requires complete observations.
[Executable subset](../formal/lean4/evm-cleanroom/README.md)

The parent CALL runner resumes from the child's resulting world, preserving
successful self-CALL storage writes. The child inherits its opcode profile
and a zero-value child inherits the caller's static flag. Precompile
destinations return an explicit indeterminate outcome. The independent
oracle's zero-gas identity precompile call returns failure, so the precompile
fixture checks the unsupported boundary separately. The retained 330-case
matrix also verifies that an EthereumJS child can load a supplied byte while
Lean reports indeterminate for the nonempty CALL input window.
[CALL repair proofs and reproducers](20261122-evm-call-boundaries.md)

## Local validation

Lean 4.33.1 completed 47 build jobs. The live axiom audit matched all 51
selected theorem axiom sets in 13 source files. The active ledger checked
54 source blobs and all four ledger test groups, including the fresh
Cancun replay, passed with no skips. The proofs cover the executable
model and rely on the Lean kernel, compiler and runtime. The independent
comparisons below exercise the listed inputs.

| Gate | Observed result |
| --- | --- |
| New calldata and unsigned word operations | 331/331 matches, 3 negative controls, 8 malformed CLI inputs refused, 1 fuel-limit check |
| New CALL boundary regressions | 16 Lean guards, 5/5 EthereumJS matches, 1 separate unsupported precompile boundary |
| New read-only RPC tests | 34/34 offline tests with the compiled Lean comparator, zero skips |
| Retained synthetic raw-bytecode corpus | 10,000/10,000 matches and 3 comparator controls |
| Retained storage and frame oracle suites | 136/136 storage and 13/13 frame matches |
| Retained CALL oracle suites | 4/4 scheduler, 102/102 scheduler boundaries, 330/330 opcode, 450/450 value CALL and 128/128 context matches |
| Retained Osaka CLZ | 1,022/1,022 oracle matches with fork, gas and stack boundary checks |
| Retained official Prague state roots | 6/6 matched, 9 fixture mutations and 6 result-ledger mutations refused |
| Retained official Cancun state roots | 6/6 matched, 4 mutations refused, 18 other-fork cases unexecuted |
| Retained Frontier mainnet block 46,147 | Both intermediate transaction and final block state roots reproduced with the Lean/EthereumJS path and independent Python. Included 24 Keccak known-answer vectors, 6 Python proof mutations and 10 synthetic MPT mutations. |

## Provider captures

Two live providers and the local frame runner returned the same full
32 bytes for synthetic bytecode that loads, stores and returns calldata.
Both captures use a code override at an address whose provider-reported
deployed code is empty. The evidence includes the provider's block and
chain assertions, and the OP Sepolia record also preserves a type-`0x7e`
deposit transaction and receipt. The offline suite replays both saved
records through the capture validator and compiled Lean comparator.

| Network | Chain ID | Block | Provider-reported block hash |
| --- | ---: | ---: | --- |
| OP Sepolia | 11155420 | 51,770,430 | `0x89d9d64ddd5a2633d5cde0af78f08d3202eb142da1abb32a4f351ccb748f7967` |
| Polygon PoS mainnet | 137 | 97,758,671 | `0xb3d1960600ab25877def36b54ffab17790f36ed254d32e4e74872f2811da2491` |

Polygon Amoy chain ID `80002` and block reads succeeded at block
53,520,858. The provider returned JSON-RPC error code `1` for the
override `eth_call`, leaving the comparison unverified. The capabilities
checked here cover read-only provider capture and a restricted standalone
frame. Ethereum and Polygon node completeness, consensus, transaction
replay for the RPC captures, and state-root or deployed-contract
authentication remain open.
[OP Sepolia capture](../formal/lean4/evm-cleanroom/scripts/rpc/evidence/op-sepolia-51770430.json) ·
[Polygon PoS capture](../formal/lean4/evm-cleanroom/scripts/rpc/evidence/polygon-97758671.json)

## Timing scope

The scoped CALL interpreter microbenchmark used 30 batches of 2,000
executions after warm-up. The ordinary no-CALL fixture's median moved from
33.676 to 32.653 µs, with p95 moving from 35.865 to 36.517 µs. The CALL
fixture's median moved from 55.036 to 57.031 µs, p95 from 56.690 to
66.549 µs, and p99 from 57.919 to 68.239 µs. These are batch averages
from the Linux interpreter. Native execution, Wasm and live RPC latency
have no comparable before-and-after benchmark in this record.
[Full timing table and method](20261122-evm-call-boundaries.md)
