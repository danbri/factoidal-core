# PVGraph map/zip: actual emitted-plan and shader refinement

Date: 2026-11-22. Tracking:
[#802](https://github.com/danbri/factoidal-core/issues/802), within
[#707](https://github.com/danbri/factoidal-core/issues/707),
[#715](https://github.com/danbri/factoidal-core/issues/715) and the
[#513 theorem pipeline](https://github.com/danbri/factoidal-core/issues/513).

## Scope and source boundary

The public JSON PVGraph API, independent application, Lean/Wasm evaluator
and automatic CPU fallback already exist. This change closes a specific
lowering gap for `u32.map.add`, `u32.map.mul`, `u32.map.xor`, `u32.zip.add`
and `u32.zip.xor`. It adds no alternative graph language or operator registry.

`GpuPlan.compileCandidate?` produces the existing JSON plan. The shipping
`GpuPlan.compile?` returns that candidate only after `MapZipPlan.validate?`
has decoded the actual serialised graph with `GraphJson.decodeCertified?`
and checked its actual emitted fields. Failed validation is an explicit
planning error. The validator never evaluates a reference result and never
accepts answer equality as evidence of a correct translation.

The five operations select the new `mapZip` shader from the plan's existing
`shaders` object. It has the host's existing four bindings: source A at 0,
source B at 1, fresh output at 2 and config at 3. All five arms remain in
the same shader, so binding 1 is statically present even for a map. Scans,
tuple searches, scalar operations, subtraction and segment expansion keep
their existing shaders and paths. No JavaScript operator implementation is
introduced; the host already transports arbitrary plan-selected shader keys.

## What is checked and proved

| Layer | Concrete fact |
| --- | --- |
| Actual serialisation | Certified decode of the original JSON; raw and decoded node counts agree, so their zipped traversal cannot discard a node. |
| Source and wiring | Each covered raw node ID/operator, registered signature, input port (`x` or `a`/`b`), source node and literal `out` port match the actual indexed plan step. |
| Shapes and allocation | Both declared source lengths equal the logical output length; the output name is fresh among preceding allocations; step names are unique. |
| Parameters and packet | The real raw coefficient agrees with the step coefficient and its exact five config words; every represented coefficient/count is in range. |
| Shader selection | The actual selected key is `mapZip`, and its complete source string equals the canonical source consumed by the parser theorem. |
| Dispatch | The actual workgroup count is `max(1, ceil(words/64))`, at most 65,535; every invocation ID fits u32 without wrap. |
| Parsed execution | Storage declarations, workgroup dimensions, guards, conditions, read/write addresses and arithmetic are parsed from the complete WGSL bytes and interpreted over bounded arrays. |
| Reference result | `compiled_mapzip` derives the existing `GraphWords.execute` result for the logical output prefix of every covered step, for every permutation of the actual rounded launch. |

Input and named graph-output descriptors are also structurally checked
against their source nodes. The per-step theorem does not turn those
checks into a whole-graph GPU execution theorem.

The proof chain is:
`GpuPlan.compile_checked` → `MapZipPlan.Checked.node_step` →
`MapZipCompileRefinement.step_refines` →
`MapZipGrid.run_source_grid` → `MapZipRefinement.run_source_lane` →
`GraphWords.execute`. Its entry point, `compiled_mapzip`, takes successful
shipping compilation and the actual certified decode/raw-node membership;
its conclusion contains the actual indexed JSON candidate, its structural
relation and the resulting shader-to-reference equality.

`runJsonGrid?` reads that candidate's actual shader key, buffer names and
config before executing the parsed source. It does not select a mathematical
primitive by an assumed tag or delegate execution to `GraphWords`. Exact
source equality confines the certificate to the fixed canonical shader; it
is not the semantic proof itself. Changing arithmetic in that source breaks
the concrete parse theorem. The shared lexer has a deliberately limited
token model: parser success for an arbitrary other string, including a
split `= =` token, is not a WGSL validity claim and cannot pass the shipping
exact-source check.

Wrapping u32 arithmetic, XOR, storage bindings, bounds and global invocation
geometry follow the dated
[WGSL Candidate Recommendation Draft, 21 October 2026](https://www.w3.org/TR/2026/CRD-WGSL-20261021/):
§6.2.3 and §8.8 for arithmetic, §8.10 for XOR, §8.5.3 for invalid
out-of-bounds references and §13.3.1.1.4 for invocation IDs.

## Host and physical execution assumptions

The theorem uses immutable logical input arrays corresponding to the named
bound buffers, a separate destination array with at least the logical word
count, and a physical-lane ordering which is a permutation of the declared
launch. Applying it to a device requires that the host uploads those words
and config, binds a fresh output allocation, submits that dispatch and
reads the specified logical prefix. Sources A and B may alias each other;
the physical output must not alias an input. The existing host creates a
new destination, but that allocation/transport implementation is tested,
not proved by this theorem.

For logical length zero the host allocates one physical word. The grid
theorem permits the spare output word and preserves it. `run_empty_lane`
also proves that arbitrary physical input dummy contents are never read
when the packet count is zero. For nonempty inputs, each parsed read and
write checks the actual finite-array bound.

Inputs are uploaded after asynchronous operations in the current host.
The theorem's snapshots describe the words actually bound; it makes no
promise about a caller mutating a JavaScript array across those awaits.
Lean compilation, Wasm execution, browser ABI, WGSL compiler, driver and
physical hardware remain outside the Lean theorem. Whole-graph scheduling,
readback plumbing and the other shader branches remain separate obligations.

## Reproducible checks

`PVGraphMapZipProofs` is a default Lake proof target. The proof/parser
closure is not imported into the shipped Wasm runtime. The dedicated GDSL
workflow also invokes the existing fresh-source, warning-as-error theorem
gate and requires individual actual axiom reports. The accepted axiom set
is `propext`, `Classical.choice` and `Quot.sound`.

`lake exe pvgraph-mapzip-check` runs `Harness.MapZipPlanTests`. Starting
with real accepted plans, it mutates shader arithmetic, bindings, indices,
guard, workgroup size, equality token, selected key, source IDs, opcode,
coefficient/config, lengths, workgroups, destination and graph-output
descriptors. It also changes the source graph and external shape bindings,
and requires the unchanged plan to be refused. Every mutation checks that
it actually changed the candidate. Fixed independent u32 arrays test
wrapping/high-bit results under forward and reverse lane orders, short
physical allocation refusal and empty physical dummy buffers.

`python3 tools/check-mapzip-source-drift.py --output NEW_DIRECTORY`
performs three isolated fresh source controls. The unmodified closure
must compile with actual allowed axiom reports. Replacing the emitted
map addition by multiplication must fail `parse_source`. Removing the
shipping call to the validator must fail `compile_checked`. A timeout,
missing dependency or unrelated compiler failure is an error, not a
successful negative control. The runner leaves repository source and
build artifacts untouched and saves all source hashes and compiler logs.

`Harness.PVGraphGpuDevice` and `tools/pvgraph-gpu-device-smoke.mjs` retain
all earlier device cases and add one-operation cases for all five covered
operators at lengths 0, 1, 63, 64 and 65, with independent overflow/high-bit
inputs, plus two unequal-zip refusals. Native/Wasm/device observations and
source/artifact hashes are recorded separately from theorem checking.

`tools/pvgraph-wasm-fixtures.mjs` transports those same native cases through
the actual `pvgraphAdmit`, `pvgraphEvaluate` and `pvgraphGpuPlan` Wasm API.
It requires complete native/Wasm plan and output equality, or matching
refusal, then emits the Wasm-authored fixture stream for the device runner.
It implements no graph evaluator in JavaScript. With a freshly built loader
whose profile contains those operations:

```sh
node tools/pvgraph-wasm-fixtures.mjs path/to/l4factoidal.js native-fixtures.jsonl wasm-fixtures.jsonl "$(git rev-parse HEAD)"
deno run -A --no-config --no-npm --unstable-webgpu tools/pvgraph-gpu-device-smoke.mjs wasm-fixtures.jsonl "$(git rev-parse HEAD)"
```

The output fixture path must be new. The helper records loader/Wasm identity,
source provenance and both fixture hashes. A focused Wasm profile is labelled
separately from the complete shipped runtime; the existing full-artifact CI
remains an independent gate rather than being folded into the 22-minute GPU
job.

`Harness.PVGraphPlanTiming` compares the unvalidated candidate producer
and shipping checked compiler on the same final source, with 31 alternating
samples for 0, 1, 32 and 120 map nodes. Whole JSON equality is checked outside
the timed interval. It measures added validation cost in that command-line
runtime; it excludes serialisation, GPU work and end-to-end application time.
No old cached executable is used as an alleged equivalent baseline.
