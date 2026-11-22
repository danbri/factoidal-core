# GDSL 0.2 — PVGraph

**Experimental specification · updated 22 November 2026**

GDSL (GpuDomainSpecificLanguage) describes typed, acyclic dataflow
computations using **PVGraph**. RDF `Graph` has separate semantics and
is not an alias for PVGraph.

## 1. Implementation and authority

Every GDSL domain uses the same canonical PVGraph document, typed
operator/port/link representation, operator registry, admission procedure
and reference semantics.

**Lean 4 defines the language.** Lean code constructs, checks and
interprets PVGraph; the runtime API compiles those operations to WebAssembly.
JavaScript is a host binding that marshals calls into Lean/Wasm. An
S-expression reader is planned in Lean/Wasm. Neither host notation defines
independent PVGraph operator semantics.

The three entry points are:

| Entry point | Role |
|---|---|
| Lean 4 `PVGraph.Builder` | Static definitions, compile-time checks, reusable proofs |
| JavaScript `createPVGraphWasm(loadEngine)` | Dynamic construction through Lean/Wasm |
| S-expressions | Planned Lean/Wasm parser for a human-readable, canonical interchange notation |

No JavaScript PVGraph parser, checker or reference evaluator is part of
the API. A missing or outdated Wasm module is an error, not a reason to
execute a second implementation. The published web runtime built from
[`e0666850902b`](https://github.com/danbri/factoidal-builds/releases/tag/build-e0666850902b-web)
includes the builder, admission, reference evaluator and GPU planner.
The [independent-app Hub example](https://danbri.github.io/factoidal/web/hub/gdsl-app/)
uses those exports through local modules; npm publication is a separate step.

## 2. Canonical representation

The versioned `gdsl/0.2` document has exactly `version`, `nodes` and
`links`. Nodes contain `id`, `op`, `params`. Each link names a
source output port and destination input port and a scalar/buffer type:

```json
{
  "version":"gdsl/0.2",
  "nodes":[
    {"id":"values","op":"core.input",
     "params":{"name":"values","type":"buffer<u32>"}},
    {"id":"scale","op":"u32.map.mul","params":{"value":3}},
    {"id":"answer","op":"core.output",
     "params":{"name":"result","type":"buffer<u32>"}}
  ],
  "links":[
    {"from":{"node":"values","port":"out"},
     "to":{"node":"scale","port":"x"},
     "kind":"buffer","type":"u32"},
    {"from":{"node":"scale","port":"out"},
     "to":{"node":"answer","port":"in"},
     "kind":"buffer","type":"u32"}
  ]
}
```

The implemented core types are `scalar<u32>` and `buffer<u32>`.
Scalar-to-buffer conversion requires an explicit operator. Links are
directed forward in topological order; an input port has exactly one
producer; output ports may fan out. There are no implicit casts, cycles,
effects or unregistered operators in this profile.

The checker requires unique valid IDs, valid parameter schemas,
complete and type-correct port bindings, named inputs and outputs,
registered operator signatures and version/resource limits. Core
bounds: at most 128 nodes, 384 links and 4,194,240 u32 words per input
buffer. Execution also checks operation-specific shapes and resource bounds.
The Wasm JSON ABI separately limits each argument to 8 MiB of UTF-8 text
before parsing (`Wasm/Ops/PVGraph.lean`, `parseBounded`). Reference input
bindings must fit that limit; buffer capacity alone is not a transport guarantee.

## 3. Lean authoring

```lean
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

def scaled : Lean.Json := build do
  let xs ← input "values"
  let ys ← mapMul xs 3 (some "scale")
  output "result" ys (some "answer")

#guard (match PVGraph.admit? scaled with
  | .ok _ => true
  | .error _ => false)
```

`Wire .scalar` and `Wire .buffer` provide Lean-level typing for common
operators. A builder returns a document; **admission is a separate
check**, performed by `PVGraph.admit?` or `buildAndAdmit?`, and returns
a proof-bearing result. A generic `op` may describe a registered
domain operator, but admission must establish its signature and
semantics; an arbitrary name is not an assumption of correctness.

## 4. JavaScript host binding

```js
import {createPVGraphWasm} from "@factoidal/core/gdsl";
import {loadEngine} from "@factoidal/core/browser";

const g = await createPVGraphWasm(loadEngine);
const xs = g.input("values");
const scaled = g.op("u32.map.mul",{x:xs},{value:3},
  {resultType:"buffer<u32>",id:"scale"});
g.output("result",scaled,{id:"answer"});
const program = await g.build();
const outputs = await g.evaluate(program,{values:[2,3,5]});
// outputs.result === [6,9,15]
```

The host binding queues commands; Lean/Wasm constructs and admits the
canonical document and evaluates it. Caller-supplied `resultType` is
untrusted and must agree with Lean's operator registry. The ABI exports
`pvgraphBuild`, `pvgraphAdmit` and `pvgraphEvaluate`.

The same JavaScript binding works in browsers and other hosts whose
Factoidal engine supports these exports.

### Using local browser modules in another app

Serve the package's browser files from your app, preserving their directory
layout: `browser.js`, `gdsl.mjs`, `lib/` and matching `l4-assets/`.
Import `./vendor/factoidal/gdsl.mjs` and `./vendor/factoidal/browser.js`
instead of the package specifiers above. `loadEngine()` resolves its assets
relative to `browser.js`. If assets are elsewhere, call the browser module's
`setAssetsUrl()` before the first engine load. Use HTTP on localhost or HTTPS.

`createPVGraphWasm(loadEngine)` constructs and checks a program;
`g.evaluate(pvgraph, bindings)` executes its reference semantics on the CPU;
`runPVGraph({pvgraph, bindings, loadEngine})` requests an eligible GPU plan
and otherwise uses that same reference. The JavaScript builder is a command
binding, not arbitrary JavaScript compiled for the GPU. No Lean compiler is
needed in an app that consumes the prebuilt runtime. Authoring and checking
new Lean theorems still uses the Lean toolkit.

The [copyable signal-mixer app](https://danbri.github.io/factoidal/web/hub/gdsl-app/)
contains a complete local-loading example and the exact PVGraph it builds.

## 5. S-expression notation

A textual notation uses exactly the same nodes, parameters, ports and
links. It must not introduce application-specific language constructs.

```scheme
(pvgraph gdsl/0.2
  (node values core.input
    (param name "values") (param type "buffer<u32>"))
  (node scale u32.map.mul (param value 3))
  (node answer core.output
    (param name "result") (param type "buffer<u32>"))
  (link values out scale x buffer u32)
  (link scale out answer in buffer u32))
```

Parsing is to be implemented by Lean/Wasm and is **not currently
exported**. It need not run inside the Lean elaborator; Lean source
programs use typed constructors directly, while dynamic text is parsed
at runtime.

## 6. Built-in operators

| Operator | Inputs | Output | Semantics |
|---|---|---|---|
| `core.input` | Host binding | Declared | Named input |
| `core.output` | `in:T` | `out:T` | Named result |
| `u32.map.add` | `x:buffer` | Buffer | Add constant |
| `u32.map.mul` | `x:buffer` | Buffer | Multiply constant |
| `u32.map.xor` | `x:buffer` | Buffer | XOR constant |
| `u32.zip.add` | `a,b:buffer` | Buffer | Elementwise add |
| `u32.zip.xor` | `a,b:buffer` | Buffer | Elementwise XOR |
| `u32.scan.sum` | `x:buffer` | Buffer | Inclusive prefix sum |
| `u32.reduce.sum` | `x:buffer` | Scalar | Reduction sum |
| `u32.scalar.const` | None | Scalar | Constant |
| `u32.scalar.add` | `a,b:scalar` | Scalar | Scalar add |
| `u32.broadcast` | `value:scalar,shape:buffer` | Buffer | Repeat to shape |

Arithmetic is exact modulo `2^32`. Reduction, scan, broadcast and
zip have explicit buffer semantics. Equal-length arrays are required
by `zip`; empty buffers have defined results.

The same operators support signal, glyph-advance, motion, pixel and
scalar-broadcast examples. Domain semantics must be introduced through
registered operators with separately checked contracts, never by
creating a second GDSL parser or evaluator.

## 7. GPU fast path

`runPVGraph({pvgraph,bindings,loadEngine})` asks the Lean/Wasm engine
for a shape-checked `pvgraphGpuPlan`. Lean selects the supported
`u32` map/zip/scalar-add/broadcast operations, hierarchical parallel scans
and indexed tuple operations, their numeric kernel tags, buffer shapes,
and dispatch sizes. The host submits the engine's WGSL kernels to WebGPU,
retains intermediate buffers, and reads named outputs.
No JavaScript operator registry or reference evaluator exists.

`GpuFastPath` proves the pure kernel model agrees with the actual
Lean `GraphWords.execute` semantics and that the whole admitted
PVGraph interpreter has the same result under that model. The per-lane
dispatch also has disjoint writes and schedule-independent results.
The `GpuPlan` and fixed shader are **not yet a verified WGSL compiler**;
a correct GPU driver is an explicit implementation assumption. Device
testing compares complete WebGPU outputs with native Lean outputs,
including high-bit arithmetic, zero-length buffers, fanout and broadcast.

The GPU branch refuses operations outside its fragment, including
`u32.reduce.sum`; `u32.scan.sum` uses a hierarchical parallel GPU plan.
`runPVGraph` falls back for the **whole PVGraph** to the same Lean/Wasm
evaluator, never JavaScript arithmetic. This API does not split one PVGraph
between CPU and GPU. SPARQL's higher-level mixed planner is separate.
`requireGPU:true` fails when no admitted device execution can run.
Malformed programs, invalid bindings and unexpected planning exceptions
remain errors in automatic mode. Both returned and thrown Lean refusal
envelopes are handled by the host binding.

The default `minWords:1024` avoids GPU startup for small programs;
`minWords:0` is useful for an explicit device demonstration. By default,
`verifyWithLean:true` compares the complete GPU result with a fresh reference
evaluation. Its extra CPU work is included in total wall time. The comparison
is evidence about the observed input and result, not a proof of the device.
Input capacity is 4,194,240 u32 words per buffer, with a 512 MiB aggregate
transport budget and the device's own limits. The benchmark
`tools/pvgraph-wasm-gpu-bench.mjs`
measures end-to-end Lean/Wasm versus WebGPU, including transfer and
readback. The name *fast path* describes its intended role, not an
unmeasured universal speedup.

## 8. Relationship with Factoidal Dataflow

`L4Factoidal.Dataflow.Stage` and `Dataflow.Graph` are the original
**application-level orchestration and contract layer**, connecting
readers, RDF datasets, SPARQL evaluators, reasoners, stores and writers.
They have typed wires, error propagation, stage guarantees, and named IO
assumptions. That `Graph` is distinct from both RDF `Graph` and PVGraph.

PVGraph is an **internal computation program**, currently carrying
scalar and buffer words between small typed GPU-eligible operations. A
Dataflow stage may use PVGraph to implement part of its run function;
it does not replace the stage, its semantic contract or RDF data model.

`GpuDomainSpecificLanguage.DataflowAdapter` exposes
`referenceStage` and `modeledFastStage` with the same exact-result
contract, proved to return the same success or error for every request.
A physical GPU-backed `Stage` still requires a separate soundness
witness at the device boundary. RDF/SPARQL specialisation must also
prove its encoding, active-graph identity, row multiplicities and
ordering; a u32 buffer alone denotes none of those things.

## 9. Assurance and execution boundary

`GraphAdmission` checks whole-program structure and typed links.
`GraphJson.decodeCertified?` admits the actual serialized document,
not a separately handwritten mathematical proxy. `GraphWords` and
`GraphEvaluate` supply pure Lean u32 semantics. Proofs include
uniqueness, complete port binding, typed edges, registered core
signatures and selected length/shape invariants. CI compiles the
modules and checks actual exported Lean builder behaviour.

Lean's proofs are about Lean definitions. They do **not** prove
correctness of the Lean-to-Wasm compiler, Wasm host runtime or
JavaScript ABI. GPU lowering and WGSL/driver/hardware execution require
further refinement and observational tests. The low-level
`@factoidal/core/gpu-resident` session is a separate resource API,
not a certified PVGraph GPU executor.

The assured SPARQL GPU fast path remains subject to
[issue #691](https://github.com/danbri/factoidal-core/issues/691).

## Source

- [PVGraph Lean builders](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/PVGraphBuilder.lean)
- [Lean admission](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphJson.lean)
- [Lean reference evaluation](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphEvaluate.lean)
- [Wasm operations](../../formal/lean4/Wasm/Ops/PVGraph.lean)
- [JavaScript binding](../../npm/factoidal/lib/gdsl-wasm-builder.mjs)
- [Cross-domain examples](../../npm/factoidal/lib/gdsl-examples.mjs)
