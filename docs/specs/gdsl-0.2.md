# GDSL 0.2 — one typed PVGraph dataflow language

**Editor's draft · 21 November 2026 · experimental · not a W3C specification**

This draft supersedes the separate-domain-syntax proposal in GSSL 0.1.
The name **GDSL** abbreviates **GpuDomainSpecificLanguage**; existing
\`L4Factoidal.GpuDomainSpecificLanguage\` and GSSL-labeled low-level
implementation modules retain their names for compatibility.

## 1. Non-negotiable interoperability rule

**Every GDSL domain uses the same canonical PVGraph dataflow document, node/edge
representation, type vocabulary, registry protocol, parser, checker,
interpreter, provenance and device boundary.**

A domain may introduce *registered operators* (for glyph shaping, images,
physics, SPARQL, etc.) that declare their precise typed ports, parameters
and denotations. It may **not** introduce another GDSL syntax, different
link semantics, a privately reinterpreted type system, or an application-
specific GPU memory manager and still call itself GDSL-compatible.

This standardizes the computation framework, not the meaning of every
operator. RDF, glyph, image and simulation semantics belong to operator
contracts. A GPUBuffer itself denotes no domain object.

## 2. Canonical graph document

Version 0.2 has exactly three top-level properties:

\`\`\`json
{
  "version": "gdsl/0.2",
  "nodes": [
    {"id":"samples","op":"core.input",
     "params":{"name":"samples","type":"buffer<u32>"}},
    {"id":"multiply","op":"u32.map.mul","params":{"value":3}},
    {"id":"bias","op":"u32.map.add","params":{"value":5}},
    {"id":"mix","op":"u32.zip.add","params":{}},
    {"id":"answer","op":"core.output",
     "params":{"name":"result","type":"buffer<u32>"}}
  ],
  "links": [
    {"from":{"node":"samples","port":"out"},
     "to":{"node":"multiply","port":"x"},"kind":"buffer","type":"u32"},
    {"from":{"node":"samples","port":"out"},
     "to":{"node":"bias","port":"x"},"kind":"buffer","type":"u32"},
    {"from":{"node":"multiply","port":"out"},
     "to":{"node":"mix","port":"a"},"kind":"buffer","type":"u32"},
    {"from":{"node":"bias","port":"out"},
     "to":{"node":"mix","port":"b"},"kind":"buffer","type":"u32"},
    {"from":{"node":"mix","port":"out"},
     "to":{"node":"answer","port":"in"},"kind":"buffer","type":"u32"}
  ]
}
\`\`\`

A node is a **single-assignment operator instance** with an explicit
registered \`op\` identifier and named parameter values. A link connects a
named source output port to one destination input port. No operand is
smuggled into an application-specific AST.

### 2.1 Link types

The first implemented profile supports exactly:

- \`kind: "scalar", type: "u32"\` (a single unsigned 32-bit value)
- \`kind: "buffer", type: "u32"\` (a bounded ordered sequence of u32 words)

The matching port types are \`scalar<u32>\` and \`buffer<u32>\`.
**The kind is semantic**, not just a drawing convention. A scalar-to-
buffer edge is invalid. A named \`u32.broadcast\` node can perform
the transformation explicitly. There are no implicit casts.

Future domain atoms (e.g. packed RGBA, glyph runs, u64-lanes, float
matrices, structs) must extend the **same grammar for type names** and
share the same port/link API, not create a new link language.
Events, streams, futures, effects and device-to-device transfers are
future link-kind profiles, **not implemented** in this pure 0.2 graph.

### 2.2 Admission invariants

The shared \`checkPVGraph\` rejects:

- Duplicate node IDs, unknown operators or unrecognized parameters;
- missing, duplicate, mistyped or mismatched source/destination ports;
- links to absent nodes, cyclic/forward references or ambiguous writes;
- anything other than acyclic topological order (source node must
  precede target node in \`nodes\`);
- graphs with no named input or output;
- invalid \`uint32\` operands or overly large graph documents.

Each input has exactly one producer; an output can fan out to many
consumers. \`core.output\` nodes and \`core.input\` nodes participate
in the **same node model**.

The checker is presently a bounded, tested JavaScript implementation,
not a machine-checked Lean refinement of the serialized format.

## 3. Two notations, **not** two DSLs

### 3.1 JavaScript computational PVGraph constructor

\`\`\`js
import { PVGraph, runPVGraphCPU, toPVSexpr } from "@factoidal/core/gdsl";

const g = PVGraph();
const samples = g.input("samples");
const multiply = g.op("u32.map.mul", {x:samples}, {value:3},
  {id:"multiply"});
const bias = g.op("u32.map.add", {x:samples}, {value:5},
  {id:"bias"});
const mixed = g.op("u32.zip.add", {a:multiply,b:bias}, {},
  {id:"mix"});
g.output("result",mixed);

const program = g.build();  // a single checked PVGraph document
const {outputs} = runPVGraphCPU(program,{samples:[2,3,5,7]});
console.log(outputs.result); // [13,17,25,33]
console.log(toPVSexpr(program));
\`\`\`

### 3.2 S-expressions

The complete version 0.2 grammar consists of \`gdsl\`, \`node\`,
\`param\` and \`link\`. **Domain-specific operators are names, not
extra language constructs**.

\`\`\`scheme
(pvgraph gdsl/0.2
  (node samples core.input
    (param name "samples")
    (param type "buffer<u32>"))
  (node multiply u32.map.mul (param value 3))
  (node bias u32.map.add (param value 5))
  (node mix u32.zip.add)
  (node answer core.output
    (param name "result")
    (param type "buffer<u32>"))

  (link samples out multiply x buffer u32)
  (link samples out bias x buffer u32)
  (link multiply out mix a buffer u32)
  (link bias out mix b buffer u32)
  (link mix out answer in buffer u32))
\`\`\`

\`toPVSexpr(graph)\` and \`fromPVSexpr(text)\` round-trip one
\`{version,nodes,links}\` document. The same operators and typed links
apply to every domain profile. Source text is a program **description**,
not host JavaScript to evaluate.

### 3.3 The one API

\`\`\`text
PVGraph(registry?)      PVGraph constructor; add input, op, output
checkPVGraph(document)   structural and type admission
toPVSexpr(document)      emit common notation
fromPVSexpr(text)        parse and admit common notation
runPVGraphCPU(pvgraph, inputs)  reference interpreter and per-node trace
runPVGraphGPU(pvgraph, inputs, {admission,session?})
                        fixed-kernel WebGPU backend
createOperatorRegistry(extensions)
                        trusted domain operator registration
\`\`\`

A domain adapter MUST use \`createOperatorRegistry\` and provide
operator name, typed input/output declarations, parameters and an
execution semantics. A GPU implementation requires **additional**
source-level lowering evidence, not merely an extension name.

## 4. Implemented universal operators

| Name | Input ports | Output | Meaning |
|---|---|---|---|
| \`core.input\` | — | declared type | Named host binding |
| \`core.output\` | \`in:T\` | \`out:T\` | Named result |
| \`u32.map.add\` | \`x:buffer\` | buffer | Add constant modulo 2³² |
| \`u32.map.mul\` | \`x:buffer\` | buffer | Multiply constant modulo 2³² |
| \`u32.map.xor\` | \`x:buffer\` | buffer | XOR constant |
| \`u32.zip.add\` | \`a,b:buffer\` | buffer | Elementwise addition |
| \`u32.zip.xor\` | \`a,b:buffer\` | buffer | Elementwise XOR |
| \`u32.scan.sum\` | \`x:buffer\` | buffer | Inclusive prefix sum |
| \`u32.reduce.sum\` | \`x:buffer\` | scalar | Sum modulo 2³² |
| \`u32.scalar.const\` | — | scalar | Constant |
| \`u32.scalar.add\` | \`a,b:scalar\` | scalar | Scalar addition |
| \`u32.broadcast\` | \`value:scalar,shape:buffer\` | buffer | Repeat value to buffer length |

The \`map\`, \`zip\`, \`scan\`, \`reduce\` and \`broadcast\`
operations are **common computation constructs**, not the private
syntax of an RDF or image domain.

For the bounded implementation:

- Buffers contain at most 4,096 words.
- Graphs contain at most 128 nodes and 384 links.
- Missing data, unequal zip lengths, wrong types or unknown
  operators are rejected.
- Empty buffers have defined map/scan/reduce semantics.
- Buffer order and multiplicity are preserved by operations that
  preserve them. The \`reduce\` result is a scalar.
- Arithmetic uses exact u32 wraparound, not imprecise host numbers.

The \`u32.scan.sum\` and \`u32.reduce.sum\` GPU backend are
**sequential single-invocation reference kernels** in this version.
Their presence is not a speedup claim.

## 5. The same graph has several executors

### CPU

\`runPVGraphCPU\` interprets each admitted node in topological order,
preserves named input/output types, and provides a per-node trace.
A domain operator's CPU semantics comes from its registered
implementation, not from arbitrary code embedded in a graph document.

### WebGPU

\`runPVGraphGPU\` accepts the **same graph** but only lowers the
whitelisted common built-in operations. It runs a single trusted
WGSL source with a fixed opcode parameter, uses the already implemented
\`@factoidal/core/gpu-resident\` device session, retains intermediate
GPUBuffer objects between nodes and reads back only named outputs.

It refuses unknown operators. Domain-specific device lowering is
not silently invented. Source code admitted by the graph parser
does not permit WGSL injection.

The result status is **\`observed-not-proven\`**. The compiled WGSL,
browser/driver and hardware are not established correct by these tests.

### Other backends (planned)

Lean native, Lean/Wasm, Vulkan/Metal and other execution environments
must consume the same typed graph or a separately proved encoding of it.
They MUST NOT introduce an incompatible graph model.

## 6. Five cross-domain examples

All examples are built with the **same JavaScript constructor**,
serializable in the **same S-expression format**, checked by the
**same type verifier**, and evaluated on **both CPU and actual WebGPU**.

1. **Signal interference loom:** fan-out into multiplier and offset,
   XOR-zip them, prefix-scan the result and reduce intensity.
2. **Glyph pen positioning:** cumulative glyph advances and line
   width. This is real basic numeric work; actual font shaping and
   script-specific glyph selection remain future operators.
3. **Particle motion:** vector of positions plus scaled velocities,
   followed by a checksum.
4. **Pixel channel mask:** XOR packed pixel words and reduce a checksum.
   This is not colour-management correctness or rendering.
5. **Scalar-to-buffer broadcast:** constant scalar wired to a
   broadcast operator and then elementwise added.

These examples deliberately share computation primitives.
The specialized knowledge belongs to the values and to future
operator registrations, **not to alternative DSL syntaxes**.

## 7. Formal methods and trust boundary

The previous \`L4Factoidal.Paralliverse.Program\` Lean language
provides typed \`identity/prim/seq/prod/fanout/map\` programs and a
proven pure map-fusion theorem. \`GpuDomainSpecificLanguage\`
has the generic primitive-agreement theorem. Both remain valid.

**However**, the new explicit, named graph/edge representation is not
definitionally identical to that older tree AST. A formalization of
the graph's ports, edges, topological admission and evaluation—and
a checked translation to those older typed programs—is a necessary
follow-up. We do **not** inherit proofs merely by reusing their names.

Likewise, the existing Lean \`GpuKernel.Resident\` planner and
Veil GPU protocol describe no-reupload, memory budgets and fences,
but do not automatically prove the new JavaScript graph interpreter
or WGSL driver correct.

What current CI establishes: syntax round trips, type-rejection
cases, independent arithmetic reference tests, and actual
Mesa/Deno WebGPU results for five graph examples, plus empty and
high-bit cases and resource reuse. This is **test evidence**, not
universal refinement or a verified compiler.

### 7.1 Whole-graph Lean checker and independent interpreter

The initial `Graph.linksAdmitted_sound` statement covered only
individual typed, forward-only edges. The subsequent core-profile
`GraphAdmission` module introduces a complete finite, executable
checker for the shared graph model. Its independently audited theorems
cover unique node IDs, a single producer for each destination port,
all declared inputs connected, correct typed/forward edges, and
registered common `u32` operator signatures.

`GraphWords` is an independent executable Lean interpretation of the
ten shared `u32` primitives. It establishes map-length preservation,
inclusive-scan length preservation and broadcast shape preservation
without assuming GPU runtime behaviour. Inputs and outputs are
distinguished as `scalar` versus `buffer`.

`GraphJson.decode?` parses the **actual** `gdsl/0.2`
`{version,nodes,links}` JSON document into the Lean graph model;
it checks exact object fields, valid identifiers, complete operator
parameter schemas, bounded sizes and input/output names. An unrelated
`GraphEvaluate.evaluate?` then evaluates this admitted JSON
graph, using the Lean primitive interpreter and following the actual
named typed links.

The CI corpus checks two independent cross-language paths:

- **Graph admission:** 99 common JSON graphs, 11 accepted and 88
  rejected identically by JavaScript and native Lean.
- **Executable semantics:** 96 same-JSON-graph-and-input cases, 89
  accepted with exactly equal outputs and 7 rejected by both.
  Cases include signal processing, font advances, motion, pixel
  words, scalar/buffer broadcasting, mismatched zip shapes, empty
  inputs and high unsigned values.

These are **real native Lean executions**, not a JavaScript reimplementation
branded as a proof. However, they remain *differential tests*:
there is not yet a theorem showing `fromPVSexpr` and the JavaScript
`checkPVGraph/runPVGraphCPU` refine their Lean counterparts for every
possible input, nor a theorem that WGSL and the driver implement this
Lean interpreter.

The Lean JSON bridge currently admits the **shared core operator
registry**, not arbitrary domain-specific extensions. Each extension
needs a checked signature and corresponding semantics before
receiving the same assurance.

### 7.2 Native-Lean-admitted PVGraph GPU execution (development profile)

The exported `runPVGraphGPU` operation now **fails closed** unless it
receives an opaque `PVGraphLeanAdmission` minted by
`admitPVGraphWithLean` in the same process. A caller cannot authorize
execution using a Boolean flag, object literal, or content hash alone.
The admission binds the canonical PVGraph and exact named input words,
checks the source document with the actual native Lean
`GraphJson.decodeCertified?` model, evaluates it through
`GraphEvaluate.evaluate?`, and requires that the independently
computed Lean output agrees with the JavaScript reference.

```js
import {
  PVGraph, admitPVGraphWithLean, runPVGraphGPU
} from "@factoidal/core/gdsl";

const pv = PVGraph();
const xs = pv.input("words");
const squared = pv.op("u32.map.mul", {x:xs}, {value:2});
pv.output("answer",squared);
const program = pv.build();
const bindings = {words:[1,2,3,4]};

// Requires this source checkout's Lean 4 toolkit (lake), not static Pages.
const admission = await admitPVGraphWithLean(program,bindings);
const observation = await runPVGraphGPU(program,bindings,{admission});
```

The native toolkit and matching Lean source checkout are presently
mandatory. A separately installed npm package without those sources
fails closed. The browser-only static Hub can still show PVGraph,
S-expressions and the JavaScript CPU reference, but it **cannot**
perform admitted PVGraph GPU execution without a future Lean/Wasm or
other explicitly trusted native bridge. Its separate original
low-level WebGPU diagnostic is *not* a certified PVGraph execution.

The GPU runner snapshots its typed inputs and checks that exact snapshot,
avoiding a JavaScript mutation between asynchronous verification and
GPU upload. It compares the final device readback to the native Lean
result. The session, WGSL compiler, driver and hardware remain trusted;
**native Lean approval does not prove WGSL refinement**.
No general runtime program verifier is claimed.

## 8. Integer width is an execution encoding

Global/long-lived 64-bit identifiers can pass through a
\`(low32,high32)\` representation on portable WebGPU, or through a
checked dense-u32 mapping, as separately implemented in GSSL.

**Neither width is the definition of the common graph language.**
A future \`buffer<u64>\` or \`buffer<id64>\` atom uses the same
typed ports and dataflow links and requires explicit operator and
backend admission. Shardborough/RDF semantics do not get built into
the universal operator set.

## 9. Release policy

- The **exploratory GDSL Hub** may expose its checked common graph
  syntax, reference CPU evaluation and experimental WebGPU observation,
  with explicit source provenance and limitations.
- The **assured SPARQL accelerator** remains separate and blocked by
  issue #691 until WGSL/kernel refinement, authenticated data,
  shipping evaluator integration, W3C conformance and performance
  evidence are established.
- Specialized "SPARQL worklet" protocols, cluster scheduling,
  network access and authorization are **outside the GDSL language**.
  Any later SPARQL plan or operation *inside GDSL* must conform to
  the same graph syntax, ports and link kinds.

## 10. Source index

- [Canonical graph, JS builder, S-expressions, verifier, CPU](../../npm/factoidal/lib/gdsl-graph.mjs)
- [Single common WGSL backend](../../npm/factoidal/lib/gdsl-webgpu.mjs)
- [All five builder examples](../../npm/factoidal/lib/gdsl-examples.mjs)
- [Generic GPU-resident device API](../../npm/factoidal/lib/gpu-resident.mjs)
- [Lean typed composition theorem](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage.lean)
- [Whole-graph Lean admission theorems](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphAdmission.lean)
- [Shared Lean u32 semantics](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphWords.lean)
- [Exact-JSON Lean graph decoder](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphJson.lean)
- [Independent Lean JSON-graph evaluator](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/GraphEvaluate.lean)
- [Actual JS vs Lean admission and semantics CI](https://github.com/danbri/factoidal-core/actions/runs/44944066469/job/136967365524)
- [Existing GPU residency model](../../formal/lean4/L4Factoidal/GpuKernel/Resident.lean)
- [GDSL issue and domain release gate](https://github.com/danbri/factoidal-core/issues/691)
