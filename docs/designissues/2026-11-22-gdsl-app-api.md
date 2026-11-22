# GDSL applications through the public API

Date: 2026-11-22

Tracking: [GDSL application integration](https://github.com/danbri/factoidal-core/issues/741).

## Public boundary

The package exposes GDSL independently of RDF and SPARQL through
[`@factoidal/core/gdsl`](../../npm/factoidal/gdsl.mjs), with
[TypeScript declarations](../../npm/factoidal/gdsl.d.ts).
Applications use the same canonical `gdsl/0.2` PVGraph, registered operators
and typed scalar/buffer links as the engine's other GDSL consumers.

- `createPVGraphWasm(loadEngine)` creates a builder. Its `input`, `op` and
  `output` methods collect authoring commands; `build()` sends them to
  Lean/Wasm for construction and admission.
- `builder.admit(pvgraph)` checks a supplied canonical document in Lean.
  `builder.evaluate(pvgraph, bindings)` executes the reference semantics.
- `runPVGraph({pvgraph, bindings, loadEngine, ...})` requests a Lean-owned
  GPU plan and executes it through the resource transport. It can return
  `gpu-observed` or `lean-reference`; the result records the reason,
  dispatch count and available phase timings.
- `createGsslResidentSession()` permits explicit session reuse. It is a
  lower-level resource API; it does not admit PVGraphs or define operator
  semantics.

`loadEngine` comes from `@factoidal/core` in Node, or
`@factoidal/core/browser` in a browser. The runtime must expose
`pvgraphBuild`, `pvgraphAdmit`, `pvgraphEvaluate` and `pvgraphGpuPlan`.
Missing exports produce a refusal. The host contains no second PVGraph
operator evaluator.

## Local deployment and an independent application

The [Hub example source](../web/hub/gdsl-app/README.md) uses same-origin
`npm/factoidal/gdsl.mjs` and `npm/factoidal/browser.js`. The browser module
locates its own `l4-assets/`; `setAssetsUrl()` can change that directory
before the first engine load. Matching assets are installed through
`tools/fetch-builds.sh` or the normal Wasm build. npm publication is a
separate release step and is not required for this application.

The example's **Download standalone HTML** action includes the current
inputs, execution options and the actual `buildSignalMixer` recipe. Place
that HTML beside `vendor/factoidal/`, containing the repository package
and its installed runtime, and serve the directory from localhost or
HTTPS. The copied JavaScript module uses the same relative public imports.
It has no dependency on Hub UI modules. Preserve the package directory
structure, including `lib/`, `l4-assets/` and package metadata.

The generic computation has two input buffers and three operators:

1. `u32.map.mul` multiplies A by a scalar gain parameter.
2. `u32.zip.add` adds B element by element.
3. `u32.scan.sum` computes inclusive prefix sums of the mixed buffer.

The named outputs are `mixed` and `cumulative`. Arithmetic wraps modulo
`2^32`; inputs must have equal lengths, and empty buffers are valid.
For A = `[2,3,5]`, B = `[1,4,1]`, gain = 3, the results are `[7,13,16]`
and `[7,20,36]`. The same DOM-free recipe is imported by the application
and the automated runner. The UI displays returned values and exports a
run report; it does not calculate those operator results itself.

## Execution selection and refusals

`runPVGraph` selects execution for a **whole PVGraph**. Its automatic mode
uses the reference evaluator for an ineligible operator, small workload,
or device execution failure. It does not divide one PVGraph into CPU and
GPU regions. The separate [mixed SPARQL planner](2026-11-22-mixed-gpu-sparql.md)
can select individual joins within a larger query.

The public `minWords` default is 1,024. The Hub sets it to zero so that
small examples exercise WebGPU when available. This threshold is not a
measured speed estimate. `requireGPU: true` refuses instead of returning a
CPU result. `verifyWithLean: true`, the default, compares complete GPU
outputs with the Lean/Wasm reference for the same input.

The shipping loader throws an `Error` with an `.envelope` member when
Lean returns a refusal. The GDSL runner previously inspected only a
returned `{ok:false}` value. As a result, an automatic run containing
`u32.reduce.sum` threw before it could select the reference evaluator.
The repair recognises the existing GPU-fragment refusal in either form.
Malformed documents, invalid bindings, unrelated exceptions and required
GPU refusals remain errors. Six runtime tests cover these distinctions,
including a malformed shape that the CPU evaluator rejects after fallback.

Scan has a GPU plan. Reduction currently causes whole-PVGraph reference
execution. Four existing example recipes contain a reduction, so their
automatic runs exercise this refusal boundary; the new mixer uses only
GPU-eligible operations. Broader execution profiles remain tracked by
[the integration issue](https://github.com/danbri/factoidal-core/issues/741).

## Bounds and assurance

The editor permits 4,096 words per input. The underlying buffer capacity
is 4,194,240 words, subject to plan, allocation and transport limits.
[`Wasm/Ops/PVGraph.lean`](../../formal/lean4/Wasm/Ops/PVGraph.lean)
checks `utf8ByteSize` in `parseBounded`: each JSON argument is limited to
8 MiB before parsing. This includes the reference evaluator's bindings
argument, so the word capacity alone is not a promise that every such
buffer fits through the JSON ABI.

The [GDSL specification](../specs/gdsl-0.2.md) describes the pure model and
its proofs. This integration changes the host refusal handling and adds
an application; it adds no new Lean theorem or operator semantics.
Compiler, Wasm host, ABI, WGSL compiler, driver and device behaviour remain
execution boundaries. Per-input comparison and software-adapter tests
establish observations, not physical-device correctness or GPU speedup.

## Validation record

The checks used the installed web release from core commit
[`e0666850902b16471c3299bde30944aa389604ec`](https://github.com/danbri/factoidal-core/commit/e0666850902b16471c3299bde30944aa389604ec),
[release `build-e0666850902b-web`](https://github.com/danbri/factoidal-builds/releases/tag/build-e0666850902b-web).
The Wasm SHA-256 was
`4688ddc7cf486b50982e783ad892336a1ff7bf8b4b7021e6fc5a9778f59b8ae8`.
The host source changes were uncommitted at this measurement; the runner
records HEAD, dirty state, every changed source hash and the actual Wasm
hash. Those records do not label a modified checkout as the release tree.

| Check | Result |
| --- | --- |
| GDSL/GSSL Hub, builder, resource and transport host tests | 45 passed; zero failures or skips |
| Documentation examples | 42 passed; 39 executed and three browser examples checked for syntax; zero failures or skips |
| Host-purity lint | 72 passed; zero failures |
| `node tools/gdsl-app-smoke.mjs` | 16 cases passed; zero failures or skips |
| Same runner with Deno WebGPU and `--require-gpu` | 20 cases passed; zero failures or skips, using SwiftShader |

The device cases cover the default mixer, empty inputs, u32 overflow, and
65-word and 4,097-word hierarchical scans. All complete outputs matched
the reference. The shared session retained zero tracked buffer bytes and
zero resources after the runs. The five existing recipes also passed
their automatic-mode checks. Physical-GPU performance was not measured.

The local browser harness could not launch Chromium: its process-singleton
socket creation failed with `EPERM`, before any page loaded. Linux CI browser checks and checks of the published
page are pending in
[issue 741](https://github.com/danbri/factoidal-core/issues/741); the Node
and Deno results above are not browser-rendering results. The full npm
suite was not rerun locally because `ensure-test-env.sh --check` reported
seven missing external fixture sets. No external fixtures were changed.
