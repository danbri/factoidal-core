# GDSL PVGraph and GPU resource management

The [GDSL 0.2 specification](specs/gdsl-0.2.md) defines the shared
typed dataflow language. Lean 4 defines the PVGraph operators, type
admission, reference interpreter and canonical document. JavaScript
calls the compiled Lean/Wasm API; application domains register operators
against the same typed ports and links.

**The GPU is not inherently an RDF store.** A GPU buffer contains words
whose interpretation is determined by the operator contract. A glyph
layout, particle simulation, image processing pipeline or SPARQL plan
uses the same PVGraph schema.

## Execution layers

```text
Lean 4 PVGraph constructors + checker + pure semantics
                       |
                compiled Wasm API
                       |
            JS thin host binding
                       |
          PVGraph application program
                       |
       checked GPU lowering (not implemented)
                       |
           WebGPU device and buffers
```

The Lean/Wasm builder and evaluator are the PVGraph API.
There is **no independent JavaScript PVGraph checker or evaluator**.
The GDSL GPU lowering is not presently a public assured executor.

## Generic GPU residency

`@factoidal/core/gpu-resident` is a lower-level device resource API.
It retains allocated buffers and compiled pipelines across passes,
skips unchanged host uploads where safe, serializes submissions, and
offers explicit bounded staging-buffer readback. It manages WebGPU
resources, not guaranteed dedicated VRAM allocation or arbitrary
external-process memory access.

The pure Lean `GpuKernel.Resident` theorems describe bounded abstract
residency plans. The host implementation, shader compiler, GPU driver
and hardware remain additional trust boundaries. The fixed-kernel
WebGPU diagnostic in the Hub is a resource test, not a PVGraph
program or a proof of GPU refinement.

## Shared computations

Signal interference, glyph advances, motion updates, pixel-word
transforms and scalar broadcasting can be expressed using the same
`map`, `zip`, `scan`, `reduce` and `broadcast` operators.
The Lean semantics apply independently of the application domain.

Distributed scheduling, network effects, XMPP/MCP, service calls and
SPARQL-specific planning belong to their application and runtime
layers; they do not change the PVGraph syntax or operator contracts.

The assured SPARQL GPU fast path is still gated by
[issue #691](https://github.com/danbri/factoidal-core/issues/691).
