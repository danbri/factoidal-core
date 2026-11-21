# GDSL 0.2 — PVGraph

**Experimental specification · 21 November 2026**

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
execute a second implementation. The Lean/Wasm export is present in
source but must be included in a new Wasm build for browser/npm use.

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
bounds: at most 128 nodes, 384 links and 4,096 u32 words per buffer.

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
import {loadEngine} from "@factoidal/core/browser.js";

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

## 7. Assurance and execution boundary

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
