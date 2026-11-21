# GDSL universal graph and GPU-resident execution

Updated 21 November 2026. **[GDSL 0.2](specs/gdsl-0.2.md) is the current architecture.**
The earlier proposal here for separately designed "SPARQL worklets" is no
longer part of the GDSL language specification. It is an optional future
planner/executor idea outside GDSL and must not create an alternative DSL.

## One base across every application

All GDSL applications use one canonical graph document
`{version:"gdsl/0.2", nodes, links}`, and the same:

- Typed, named op nodes with registered operator signatures.
- Explicit port-to-port links, currently `scalar<u32>` and `buffer<u32>`.
- Topological, acyclic graph validation and parameter checking.
- JavaScript graph-constructor notation and one S-expression grammar.
- Reference CPU evaluator and a common WebGPU device executor.
- Generic GPU-resident resource management and bounded inspection.
- Provenance and honest status distinctions: structural/type admission,
  pure semantic theorem, actual device test, and trusted compiler/driver.

**The GPU is not inherently an RDF store.** A buffer represents whatever
an admitted operator says it represents. A future font, simulation, image
or RDF operation is an operator in the **same GDSL graph**. It does not
get to invent its own dataflow nodes, parser, links, scheduler or API.

## Layers

```text
  JavaScript constructors      S-expressions
            \                   /
          canonical GDSL typed graph
                   |
          shared graph checker
                   |
           CPU interpreter  ---- common semantic reference
                   |
   optional same-graph GPU executor
                   |
    bounded resident buffers + pipelines + fences + readback
                   |
              WebGPU device
```

The current browser workbench uses a fixed, whitelisted, trusted WGSL
operator kernel for u32 graph nodes. It does **not** compile arbitrary
GDSL source into a verified GPU program.

## Resource lifecycle

`@factoidal/core/gpu-resident` is the generic execution resource API.
It retains versioned buffers, compiled pipelines and GPU intermediates
between invocations and even between unrelated GDSL graphs. A write
invalidates a cached host version. Submissions are serialized and awaited.
Explicit `inspect` takes a bounded CPU-visible snapshot through a staging
buffer. The API manages WebGPU objects, not guaranteed physical VRAM
placement or arbitrary external-process memory access.

The existing Lean `GpuKernel.Resident` theorems describe no-reupload,
bounded budgets and steady-state reuse. The Veil GPU protocol describes
version/fence/readback invariants. Those formal results are target
contracts, not an automatic machine-checked proof of the JavaScript
runtime, shader compiler or GPU execution.

## Independent use cases, shared operators

- Signal interference: fanout, map, zip XOR, prefix scan, reduction.
- Glyph widths: add tracking, inclusive scan, scalar total.
- Motion update: multiply velocity, zip-add position and reduction.
- Pixel words: XOR channel mask and checksum.
- Broadcasting: a scalar node, explicit buffer-shape link and zip-add.

Each example runs under the same `PVGraph()`, `toPVSexpr()`,
`fromPVSexpr()`, `checkPVGraph()`, `runPVGraphCPU()` and `runPVGraphGPU()`
vocabulary, not a language with its own planner.

## What remains outside the GDSL specification

Correlated SPARQL evaluation, `LATERAL`, `SERVICE`, remote workers,
transport, XMPP and MCP bindings, authentication and distributed
scheduling are applications and deployment concerns. Some may later
be represented by registered operators or separate host effects, but
**none changes the GDSL core graph language**.

The fully assured SPARQL GPU fastpath remains gated by
[issue #691](https://github.com/danbri/factoidal-core/issues/691).
The universal graph/CPU/WebGPU checker needs its own formal Lean
refinement before general compiler correctness can be claimed.

Source: [GDSL 0.2 specification](specs/gdsl-0.2.md).
