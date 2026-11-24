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

## Historical local observations

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

## Historical focused Wasm and device results

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

The initial amendment was inspected while the private proof held the build
resources. After those resources were released, all corrected-source checks
below ran on clean local commit `63791fda986b8cd2ba8fae6ca1467d9bcd6209e8`,
tree `e41c625df45be237a5ed4b2835a7ca8411c4afe0`. It has the same tree as the
published [40ec158c source checkpoint](https://github.com/danbri/factoidal-core/commit/40ec158c3a0e8625468d238fb8724da8519f1dcb).
The runtime source remained unchanged through timing. The later audit and
documentation changes do not change a runtime-producing input.

### Corrected-source proof and execution results

The focused Lake build passed all 44 jobs. Fresh-source controls passed
all three cases: the unmodified 18-module closure compiled, the actual
addition-to-multiplication source mutation failed `parse_source`, and
bypassing shipping validation failed `compile_checked`. The baseline's
40 individual axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. Resource/import failures are excluded from negative-control
success. The native suite again passed all 215 controls.

Both standard Lake C and the separate focused C were inspected before any
literal rewriting. `MapZipPlan.c` reads the shared `two32` global and calls
the `NatBounds` initializer; it contains no inline allocation of
`4294967296`. `NatBounds.c` creates that value once and marks it persistent.
The two C-generation paths use different symbol prefixes and have separate
hashes; neither is substituted for the other.

| Unrewritten C input | SHA-256 |
| --- | --- |
| Standard Lake `MapZipPlan.c` | `e9a53b9dcd1ca37592137c01dddb08f356e0f68b2e9c31e59a371980649af25c` |
| Standard Lake `NatBounds.c` | `8d54948638c38749cab1e5a6f77ca0f1eda3b6deb42f35e04c705001bc885e36` |
| Focused `MapZipPlan.c` | `463c194dd5e9e28764970b72d8fc198c74de0d90c5fd7dc2eccf9c40d4d7a0a8` |
| Focused `NatBounds.c` | `8f7b3880f488c35dd91dbd906380146a2650f39f6c3b342430fce853d9301d66` |

The focused closure regenerated 15 modules with changed recursive
dependency fingerprints and matched 541 cached modules, for 556 total.
Only `MapZipPlan.c` changed generated C bytes against the preserved prior
manifest. The unchanged Wasm helper freshly compiled all 888 runtime C
units and checked 586 project/HACL/FFI inputs, retaining its existing
content/flags object cache. Its standard conversion rewrote 137 literal
sites in 45 files; the corrected `MapZipPlan` bound needed no rewrite.
Linking retained 25 pinned C++ runtime objects and the checked string-list
witness. This is not an entirely cold toolchain build.

The new focused Wasm passed all 61 API cases using Deno: 59 complete
native/Wasm plan and output matches, plus two matching evaluation/planning
refusals. Native and Wasm fixture bytes are identical. Each fixture set was
then executed separately through WebGPU: 59 eligible cases passed and the
two pre-device refusals were retained in each run. Both runs used **llvmpipe
LLVM 19.1.7, software Vulkan**, not a physical GPU.

| Corrected-source evidence | Identity |
| --- | --- |
| Focused Wasm, `core-plus-registry-test` | 10,227,649 bytes; SHA-256 `5c24a5c52d681f4a3245466a0774b7b1138e5942bf956a5a05c1a2ea7e49001b` |
| Native and Wasm fixture streams | Both SHA-256 `0001fac0d1c3406fac8cd35896e11639e4e02d27f94a7fb319b22e08c2fee15e` |
| Fresh-source control results | SHA-256 `4c3bee84b45034d43145e84bc79ed2821055c216737e2451b859ada95c628239` |
| Wasm API evidence | SHA-256 `46a1cf6688a603c279eb23e7c94996e1ea148398922a16651b0f9991e01337bd` |
| Native-plan device evidence | SHA-256 `486f93b613c619ace8b9aa185ce0598586e884e9b9772238896cfbc59506bd7a` |
| Wasm-plan device evidence | SHA-256 `b5d5664ca925c3d4ef344618ca2774f80cbbfbcc888f1dbb292181399903d33f` |

All six native/API/device/timing stderr files were empty. Earlier artifacts
and failed launch attempts remain preserved with their own source identity;
they are not relabelled as corrected-source results.

## Measured validation cost

### Historical initial checkpoint

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

### Corrected-source checkpoint on 2026-11-23

The same harness ran once on clean `63791fda`, under the build and timing
locks, CPU affinity 0, one Lean worker and a 4 GiB address-space cap. Each
graph size has 31 retained samples; measurement order and 64/65-word input
length alternate. Complete plan equality and JSON serialisation remain
outside the measured interval.

All values below are milliseconds. Quantiles use nearest rank,
`sorted[ceil(p * 31)]` with one-based indexing: p50 is sample 16, p95 is
sample 30, and p99 is sample 31, equal to the maximum. **p99 is coarse with
31 samples.** The last column gives the observed min–max spread.

| Map nodes | Path | p50 | p95 | p99 | Maximum | Min–max |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | candidate | 0.079765 | 0.137847 | 0.165287 | 0.165287 | 0.077440–0.165287 |
| 0 | checked | 0.175715 | 0.249356 | 0.260584 | 0.260584 | 0.161193–0.260584 |
| 1 | candidate | 0.144492 | 0.296287 | 0.339699 | 0.339699 | 0.134050–0.339699 |
| 1 | checked | 0.321869 | 0.395938 | 0.444045 | 0.444045 | 0.292882–0.444045 |
| 32 | candidate | 2.676671 | 2.949793 | 3.341051 | 3.341051 | 2.523381–3.341051 |
| 32 | checked | 6.274084 | 7.456497 | 8.397160 | 8.397160 | 6.093176–8.397160 |
| 120 | candidate | 19.851426 | 21.939530 | 34.732150 | 34.732150 | 19.306297–34.732150 |
| 120 | checked | 51.061245 | 53.327316 | 54.018286 | 54.018286 | 48.557794–54.018286 |

The checked/candidate p50 ratios were 2.20×, 2.23×, 2.34× and 2.57×.
The zero-map graph also pays this validator's metadata/admission cost;
the result is recorded rather than claiming zero overhead. These are
command-line Lean evaluation timings, not native-C, browser, WebGPU or
application measurements. The historical and corrected runs occurred at
different times; no performance change is attributed to the bound fix
from that comparison alone.

The [four complete sets of raw samples](evidence/20261123-pvgraph-mapzip-two32-timing.jsonl)
are retained in Git, SHA-256
`417cba77497211261ca04982ccb39106b976df81c66112c9442f9648e0d20397`.
Each record identifies its map-node count and contains all candidate and
checked nanosecond samples, so the table can be recomputed.

## Shipping CI checkpoint and audit repair

The published `40ec158c` source has a distinct full-shipping Wasm result.
[Full Lean/Wasm and device CI](https://github.com/danbri/factoidal-core/actions/runs/45088092946/job/137411172326)
passed with the ordinary `formal/lean4/Wasm/build-wasm.sh`: 33,293,864-byte
Wasm, SHA-256
`aa3801b328fcf932c7cf5d355419ad9dabbf62f8fc3feb7d8692f00a9917f3f3`.
Its retained evidence ZIP has SHA-256
`1c9292b640466d11fd73f1c39bd54ae0f8cf48d46b2f169484ac3ddbf8e394d6`.
The existing 16 CPU/20 WebGPU public-API cases, six runtime tests and 23
browser checks passed on llvmpipe LLVM 20.1.2, again a software adapter.
The existing GDSL/SPARQL hub 17 and query 42 cases also passed. These are
separate suite inventories from the local 61-case map/zip fixture replay;
the CI ZIP did not retain unrewritten C.

The [map/zip source-refinement CI](https://github.com/danbri/factoidal-core/actions/runs/45088093061/job/137411172977)
also passed. The complete core snapshot had 24 passing checks and one
failure: [the full Lean corpus job](https://github.com/danbri/factoidal-core/actions/runs/45088092933/job/137411175454)
compiled, then the recursion gate found `Calc_simpWith` under
`Rendering/CssValues/Numeric.lean`; the allowlist still named `Calc_simp`.
This failure is not a passing full-corpus verdict.

A separate two-file repair updates that exact worker entry, and corrects
the existing `Calc_type` and `Calc_css` reason text to calculation-tree
nesting. It introduces no wildcard exemption or unproved 64-frame bound,
and leaves `Calc_depth` unchanged. The scanner's two Lean children now
run from `formal/lean4`, after caller-relative `LEAN_PATH` and output paths
are resolved. No rendering implementation or runtime source changes.

Scoped repair checks passed 13 recursion-audit controls, 31 synthetic
`csimp` controls, all seven actually compiled safety-scanner fixtures,
and byte-identical nonempty absolute/relative NatBounds scan JSON.
The real-build `csimp` cases were explicitly not requested locally; their
full-corpus C prerequisites were absent. The first scanner attempt with a
4 GiB address-space cap failed while importing
`Lean/Meta/Tactic/FunInd.olean.private`, before classification. A single
approved serial retry with a 6 GiB cap passed; the maximum recorded RSS
was 2,032,136 KiB (about 1.94 GiB). The initial failure remains in the
record. No source or page/runtime admission limit was changed for that
retry.

## Remaining landing gates

The final evidence and audit-repair head needs its own applicable core CI
and the independently checked current-main integration/premerge gates.
The repository's `ci-runner` and `github-and-prs` rules also require the
Linux jobs of `danbri/factoidal-builds` `build.yml`, dispatched for the
**exact final public PR head**. The focused and full-GDSL core jobs do not
replace that broader gate.

That external run is outstanding at this documentation checkpoint. The
available connector has no workflow-dispatch operation and the CLI/browser
sessions are signed out; secure sign-in is needed to dispatch it. This is
a capability limitation, not an approval-review rejection or test failure.
The record does not claim the PR is merge-ready or fully integrated.

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
