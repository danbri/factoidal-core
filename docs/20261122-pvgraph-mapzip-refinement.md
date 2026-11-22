# PVGraph map/zip lowering: source-bound proof and execution checks

Date: 2026-11-22. Tracking:
[#802](https://github.com/danbri/factoidal-core/issues/802).
Design and remaining assumptions:
[emitted-plan refinement](designissues/2026-11-22-pvgraph-mapzip-refinement.md).

## Change

The shipping `GpuPlan.compile?` now structurally validates its actual JSON
candidate against `GraphJson.decodeCertified?` and the original raw graph.
The five operations `u32.map.add`, `u32.map.mul`, `u32.map.xor`,
`u32.zip.add` and `u32.zip.xor` select an actual four-binding WGSL kernel.
The same public API, reference evaluator and CPU fallback remain in use.
Other GPU operations keep their existing paths.

`MapZipCompileRefinement.compiled_mapzip` connects successful shipping
compilation to the actual indexed step, original node/ports/parameter,
buffer IDs, config, output allocation size, selected shader bytes and
rounded dispatch. Its concrete parser/interpreter reads those bytes and
stores; its conclusion is the existing `GraphWords.execute` result for
the complete logical output prefix. It does not assume the semantic
conclusion or identify correctness by a hash. Padded invocations write
nothing; arbitrary invocation order preserves the result and spare
physical output words. A separate zero-count lemma covers arbitrary
physical input dummy contents.

The proof is per step. Whole-graph GPU execution, the other shader
operators, mutable caller inputs across awaits, host binding/readback,
Lean/Wasm compilation, WGSL driver and device execution remain outside
it. Physical source buffers may alias each other; output must be fresh.

## Local observations

The final source composition, parsed lane/grid and compiler-certificate
theorems compiled under pinned Lean 4.33.1. Individual actual axiom reports
use only `propext`, `Classical.choice` and `Quot.sound`. The source hygiene
audit found no new escape hatch; the existing partial-definition count
remained 163. A default Lake proof target and a fresh-source CI job make
these modules part of the checked build.

`Harness.MapZipPlanTests` passed 215 controls with zero failures. These
include 155 mutations of actual accepted candidate JSON/source bytes;
source graph and external-shape drift; independent fixed overflow/high-bit
results in forward and reverse lane order; short physical allocation
refusals; empty input/output dummy storage; dispatch limits; and unequal
zip refusal. Its output is one JSON record per control, followed by the
explicit pass/fail/total inventory.

The native fixture harness emitted all 61 intended cases. On the actual
WebGPU lane, all 59 eligible cases matched complete Lean outputs and the
two unequal-zip cases were refused. The observed adapter was **llvmpipe
LLVM 19.1.7, a software Vulkan adapter**. This includes the 25 new
one-operation boundary cases (five operations at 0, 1, 63, 64 and 65
words) and preserves the 34 earlier eligible cases. It is device API
execution evidence, not a physical-GPU speed measurement or proof.

The separate source-control runner passed all three controls. Its fresh
17-module unmodified proof closure compiled. Changing the emitted addition
to multiplication failed the concrete `parse_source` theorem with the
expected AST mismatch; bypassing shipping validation failed
`compile_checked` with the missing certificate goal. Full source and
actual-compiler hashes/logs were retained. Resource failures and unrelated
compiler errors do not count as proof refusals, and repository files were
unchanged. CI retains these separately from runtime/device evidence.

## Measured validation cost

The timing harness compared `compileCandidate?` and shipping `compile?`
on the same source, with 31 alternating samples per graph size and input
lengths alternating between 64 and 65 words. It checked complete returned
JSON equality outside the timed interval.

| Map nodes | Candidate median | Checked median | Checked/candidate |
| ---: | ---: | ---: | ---: |
| 0 | 0.080890 ms | 0.168450 ms | 2.08× |
| 1 | 0.138929 ms | 0.304176 ms | 2.19× |
| 32 | 2.566458 ms | 6.156863 ms | 2.40× |
| 120 | 19.835104 ms | 50.070180 ms | 2.52× |

These are Lean command-line evaluation timings. They exclude JSON
serialisation, WebGPU work and application startup; they are not compiled
native-C, browser or end-to-end application measurements. The structural
validator currently repeats graph admission and traverses plan metadata;
the measured overhead is retained rather than hidden behind an old binary
or an unmeasured speed claim.

## Existing ASK image separation

This change does not enter the recorded ASK guest's producing closure.
A read-only comparison matched all 874 recorded Lean sources, 897 C
inputs, 144 headers, 874 generated and compiled module pairs, the pinned
compilers/runtime archive/fence-lowering script and the five reviewed
guest files. No ASK image was rebuilt or proof produced for this GDSL
change. The existing guest image keeps its own reviewed source provenance.

## Remaining scope

The S-expression authoring parser remains a usability milestone. It would
not establish shader assurance. Extending the present emitted-plan and
parsed-source proof to another actual kernel is a separate theorem task.
The broader obligations stay in #707/#715; this work claims only the
five-operator per-step boundary agreed in #802.
