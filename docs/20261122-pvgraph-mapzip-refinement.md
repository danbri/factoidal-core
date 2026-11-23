# PVGraph map/zip lowering: source-bound proof and execution checks

Date: 2026-11-22. Tracking:
[#802](https://github.com/danbri/factoidal-core/issues/802).
Source review: [PR 807](https://github.com/danbri/factoidal-core/pull/807).
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

At the recorded source checkpoint below, the composition, parsed lane/grid
and compiler-certificate theorems compiled under pinned Lean 4.33.1.
Individual actual axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`. The source hygiene
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

## Fresh focused Wasm and device results

The `core-plus-registry-test` Wasm profile passed all 61 cases through the
actual `pvgraphAdmit`, `pvgraphEvaluate` and `pvgraphGpuPlan` API: 59 plans
and complete outputs exactly matched native Lean, and both unequal-zip
cases were refused by evaluation and planning. The emitted Wasm fixture
stream was byte-for-byte identical to the native stream. Running those
fresh Wasm-authored plans on llvmpipe again passed all 59 eligible cases,
with the same two pre-device refusals.

Evidence was captured from clean local source
`b4b6044bcfa58ed5c3c89aa60e5120bec82fc888`, tree
`da4fd80e6591c4c2d9e7129bdcbe90cd079fa7e3`, identical to PR 807's initial
published source tree. The later evidence documentation changes no
runtime-producing input.

| Artifact | Identity |
| --- | --- |
| Focused Wasm | 10,227,619 bytes; SHA-256 `12810b88f0be52d385b5ca6728d9adafc0bd85b3f3d89fe9ae96f36c90244b5d` |
| Native and Wasm fixture streams | Both SHA-256 `0001fac0d1c3406fac8cd35896e11639e4e02d27f94a7fb319b22e08c2fee15e` |
| Wasm API evidence | SHA-256 `b0babaa75c29f2e2b81a49177b637cd7b9bb532c270b1b19e4d09e82470db841` |
| Wasm-plan device evidence | SHA-256 `ec5a0b456f3e032fc8177141f07a8cb6cf9644c71f8748b5ccc86e15b8e72263` |

Of the 556 project modules in this focused producing closure, 23 changed
or dependent C modules were regenerated from source; 533 cached modules
matched recursive source/dependency fingerprints. The build freshly
compiled 888 runtime C units and 586 project/HACL/FFI C units. Its standard
32-bit literal conversion affected 138 sites in 46 files. Linking used
25 pinned C++ runtime objects with the checked string-list witness. These
cache and runtime-object facts are part of the evidence, not a claim that
every input was rebuilt from nothing.

This is a newly linked focused test profile exercising the changed public
operations. It is not the complete shipped Wasm artifact, a release
publication or evidence of physical-GPU performance. The independent
full-artifact CI and remaining compiler/host/device assumptions still
apply.

## Executable bound correction on 2026-11-23

Final runtime review found that the executable `StepMatches` decision used
`step.constant < UInt32.size`. Its unrewritten generated `MapZipPlan.c`
allocated `lean_cstr_to_nat("4294967296")` at the comparison and passed it
to `lean_nat_dec_lt`, whose two arguments are borrowed, without releasing
that temporary. On wasm32 this literal needs an allocated natural number.
The focused artifact recorded above was protected by its 32-bit literal
rewrite; the shipping `formal/lean4/Wasm/build-wasm.sh` does not apply that
rewrite. Its successful execution checks therefore did not establish that
the shipping build avoided this allocation leak.

The source now explicitly imports `L4Factoidal.NatBounds` and uses its
existing `@[reducible, noinline] L4Factoidal.two32` in that executable
proposition. This is the repository's shared persistent-bound convention;
`NatBounds` already proves `two32 = UInt32.size` by `rfl`, so the logical
bound is definitionally unchanged. No custom runtime or unsafe code is
added.

This amendment was checked by source and existing generated-C inspection
only while the private proof held the build resources. The proof, native,
Wasm, device and timing results in this note describe the earlier recorded
checkpoint. Lean CI and a fresh unrewritten C/Wasm inspection, execution
checks and timing refresh for the amended source are pending; they are
not claimed by the earlier artifact's results.

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
