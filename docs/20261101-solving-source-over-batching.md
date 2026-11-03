# Solving: ordered source-over batches

The first executable Solving proof target is ordered paint composition. The
shared `NativeGraphics.PremultipliedLayer` stores premultiplied RGB and alpha.
`overOpaque` applies one source-over operation to an opaque backdrop. The SVG
CPU reference now uses this shared operation for each element after combining
its fill and stroke and applying element opacity once.

`compositeOpaqueLayers_append` proves:

```text
compose background (first ++ second)
= compose (compose background first) second
```

The recursive proof preserves the same order of Float operations. It permits a
backend to divide an ordered sequence into chunks without changing the CPU
reference result. It does not permit reordering layers, reassociating Float
expressions, or combining layers using a different arithmetic model.

## Evidence and remaining obligations

The modified `Graphics.lean` and `SVG.lean` compiled with Lean 4.33.1 from
`formal/lean4/`, including the new theorem. Compilation covered the updated SVG
sampling source. This is kernel-checked Lean evidence for the theorem and the
source dependency; no native or WASM executable was rebuilt, and no pixel suite
was run in this change.

This result is not yet a batching optimization or a backend-equivalence proof.
The opaque CPU backdrop is the only destination covered. WGSL still performs
its own fragment arithmetic. GPU f32 precision, color-space behavior, shader
execution, alpha-bearing intermediate surfaces, isolated groups and clip/cull
semantics need separate definitions and proofs. A future fast path must preserve
the shared layer semantics and report measured cost as well as its proof.

The wider scene design and its cross-producer objectives are in
[`designissues/2026-11-01-svg-scene-compositor.md`](designissues/2026-11-01-svg-scene-compositor.md).
