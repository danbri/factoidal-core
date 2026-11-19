# Paralliverse v0.1 engineering handoff

**Status:** design and scope agreement (2026-11-18), not an implementation or proof claim.  
**Tracking issue:** [#604](https://github.com/danbri/factoidal-core/issues/604).  
**Existing GPU roadmap:** [#398](https://github.com/danbri/factoidal-core/issues/398).

## Executive decision

Create a **pure Lean 4, ahead-of-time, theorem-backed parallel computation utility** within `factoidal-core` for now. Its design, semantics and public API must not depend on Foafnaut, SVG, DOM, HTML, rendering, or a particular GPU host. It may later be extracted into a separate Lake package.

**Naming.** Paralliverse names both the library and its static parallel DSL. The public Lean entry point is `L4Factoidal.Paralliverse`, and the component lives under `formal/lean4/L4Factoidal/Paralliverse/`.

For v0.1, **static compile-time compilation and proofs only**. The ordinary executable Lean 4 function is the specification and CPU fallback; the GPU implementation is a separately built, optional fast path with machine-checked correctness claims over a formally defined model. The CPU implementation must continue to compile and run in environments without WebGPU.

Do not change Foafnaut's default renderer or destabilise the browser to implement this. Consumer integration is separate, opt-in work that follows independent verification, benchmarks and fallback testing.

## Motivation and first workload

A representative consumer is variable-length, paint-order-sensitive packing. Foafnaut's `labs/demos/foafnaut/SVG.lean` currently contains:

- `binPieces`, `Primitive.tileListing` for spatial binning;
- `tilesOfListingsRows` and `tilesOfListingsRef` for packing tile entries and lists in paint order.

These are **test workloads**, not library dependencies. Stable ordering matters: atomic append to each tile can yield the right *set* of entries but a different order, potentially changing rendering.

First standalone workload: **count → exclusive prefix scan → stable scatter**, producing a contiguous array that matches straightforward sequential concatenation exactly. It is useful in sparse arrays, relational/spatial indexing, WebNN tensor packing, and graphics.

A [plain JavaScript + WGSL experiment](https://stable-gpu-packing.hatchable.site/) illustrates the idea, including a large-array benchmark, but is **not** the Lean implementation and provides **no formal proof**. As at creation of this document, the hosted automated browser could test its CPU path but did not expose a usable WebGPU adapter; don't treat that as GPU validation.

## Static build model

```text
Ordinary Lean 4 function (source + executable CPU implementation)
        |
        +-----------> CPU build + tests (works without GPU tooling)
        |
        +-----------> eligible static extraction / explicit DSL program
                                  |
                          parallel DSL semantics
                                  |
                         equivalence + safety proofs
                                  |
                      target-subset semantics / WGSL lowering
                                  |
                         WGSL artifacts + GPU tests

At runtime: checked preconditions and device support
             | supported -> precompiled GPU fast path
             | otherwise -> original compiled CPU function
```

The first implementation may use an **explicit embedded DSL** rather than automatic recognition of arbitrary `Lean.Expr` definitions. Source recognition is valuable, but not required for v0.1. If supplied as a DSL program, its semantic correspondence to the ordinary Lean function **must be proved**, not merely asserted.

What can vary at runtime: data values, input lengths within admitted limits, hardware features (subject to explicit checks) and dispatch configurations covered by proofs. What does **not** vary in v0.1: the set of GPU programs, their source, and their proofs after compilation.

This is a scope decision, **not** a permanent identification of code with static build time. Later recognition of preserved Lean code, runtime plugins, new computation graphs, or a WASM-hosted Lean compiler remains possible and out of scope.

## Required theorem chain

Use a simple **ordinary Lean reference function** `packSpec` with unambiguous mathematical meaning, including empty input and zero counts.

Define a parallel DSL with independently specified semantics. Desired schematic obligations:

1. **Functional equivalence:** `evalDSL packProgram input = packSpec input` for every admitted input.
2. **Scan correctness:** exclusive offsets are prefix sums; the final offset equals the total output size.
3. **Stable ordering:** the packed output preserves item order and per-item local order, **including duplicates and empty segments**.
4. **Memory safety:** every read/write lies within its allocated region; output segments from distinct items are disjoint.
5. **Concurrency:** every permitted scheduling/interleaving under the model yields the same output, or the specification clearly states and discharges the relevant memory-model hypotheses.
6. **Numeric agreement:** `Nat`-based semantics and `u32` WGSL semantics agree when checked overflow conditions hold.
7. **Lowering correctness:** generated target-subset semantics refines the DSL semantics. The existing code-generation/printer equivalence gap cannot be hidden by labelling it “proved”.

A useful schematic target statement is:

```lean
-- Illustrative shape, not claimed to typecheck:
theorem packParallel_correct (xs : Array Nat) (h : Admissible xs) :
    evalDSL packProgram xs = packSpec xs := by
  ...
```

For concurrent GPU execution, prefer an *all permitted executions* refinement relation over modelling one deterministic execution schedule. Also distinguish safety, termination/progress, and functional correctness.

**Proofs must compile in Lean.** Do not count `sorry`, hidden axioms, untrusted SMT results, differential tests, or samples as machine-checked proof of the named obligation. Document explicit hypotheses and remaining trusted components.

## Trust boundary and backends

Separate these layers:

1. Kernel-checked Lean proof about the ordinary reference and DSL.
2. Kernel-checked proof (if implemented) about lowering to formal **WGSL subset semantics**.
3. Actual WGSL parser, translation to SPIR-V / MSL / HLSL / DXIL, and command submission.
4. Vendor driver and hardware execution.

The present in-repo `GpuKernel.Expr` proves that its `Nat` and wrapping `u32` meanings coincide under `Fits`, but explicitly **does not prove** its WGSL text printer matches the target language. This is a gap to address, not a reason to claim existing end-to-end compilation correctness.

The present `GpuKernel.Race` handles permutation independence for disjoint writes and some commutative atomics, **not workgroup-barrier semantics or shared workgroup memory**. The proposed scan requires barriers and a multi-dispatch hierarchy; extend the model or mark the unsupported part as an explicit assumption until it is covered.

Backend-specific translation validation or verified lowering for SPIR-V, MSL and HLSL/DXIL is future work; none should be conflated with a proof about GPU drivers. CUDA/PTX would be a separate backend rather than an assumed WebGPU route.

## Initial source layout

Keep the implementation under the generic `L4Factoidal.Paralliverse` namespace. Existing reusable modules:

- `GpuKernel/Expr.lean` — restricted arithmetic IR, `Nat` and `u32` meanings;
- `GpuKernel/Race.lean` — pure write-footprint model and scheduling-independent results;
- `GpuKernel/Gather.lean` — first (bounded, simple) compute/gather workload and WGSL emission;
- `GpuKernel/Resident.lean` — GPU residency model (orthogonal to pure packing);
- `Par/Chunked.lean` — CPU task chunking and proved equality to sequential `Array.map`.

The initial word-packing specification, staged model and proofs live in `Paralliverse/StaticPack.lean`, with an isolated CPU fixture runner in `Harness/ParalliverseCpu.lean`. Candidate later modules include `Paralliverse/DSL.lean`, `Paralliverse/Scan.lean`, `Paralliverse/StableScatter.lean`, and `Paralliverse/Pipeline.lean`. Keep their imports independent of Foafnaut.

For the first pass, use core Lean only and the repository's existing Lean toolchain; don't introduce Mathlib or upgrade the browser's toolchain merely to establish the prototype.

## Acceptance gates

- [ ] Ordinary Lean CPU specification is executable and builds without GPU tooling.
- [ ] Static parallel DSL program with clear sequential semantics.
- [ ] Kernel-checked proof of equivalence for **all admitted inputs**, not only examples.
- [ ] Bounds, overflow, stable order and disjoint write claims have precise checked hypotheses.
- [ ] Multi-workgroup scan and dispatch barriers are modelled or clearly listed as assumed/not verified.
- [ ] Generated WGSL is validated with a real shader compiler; its semantics/proof status is accurate.
- [ ] GPU-required test lane **fails or marks incomplete** when no GPU adapter is available. CPU-only success is not GPU success.
- [ ] Differential tests cover zero, one, full/dense, sparse, boundary-size, capacity-limit, and adversarial ordering cases.
- [ ] Benchmarks reuse allocations/pipelines, warm up, and report separately CPU, GPU compute, host encode/submit, uploads/readback and complete end-to-end cost. Timestamp-query availability and any CPU/GPU ratio's meaning must be disclosed.
- [ ] Runtime admission failures and absent/lost devices select the original CPU implementation.
- [ ] Default Foafnaut rendering and release paths are not changed.
- [ ] New utility has an extraction-friendly API and is independently testable.

Recommended order: **reference semantics → DSL/equivalence → memory/ordering proofs → explicit GPU execution model → code generation/validation → differential testing → warmed benchmarks → opt-in consumer**.

A simple `O(tiles × primitives)` gather is acceptable as a correctness oracle, not an assumed competitive GPU algorithm. Efficient count/scan/scatter deserves independent proof and measurement.

## Deferred questions (deliberately not v0.1 requirements)

- Reifying/recognising general elaborated Lean definitions (`Lean.Expr`, Qq, LCNF) and proof that extraction preserves source semantics.
- Running Lean compilation or proof checking at application runtime; a WASM-hosted Lean compiler; late plugins or runtime-generated graphs.
- Preserved, versioned semantic artifacts for long-lived later specialisation; runtime interpretation of arbitrary content.
- Floating-point geometry and exact cross-device floating-point semantics.
- Compiler validation for all WGSL backends and native hardware correctness.
- General dynamic parallelisation, tensor/array programming, arbitrary loops and higher-order functions beyond the narrow initial DSL.

The distinction between *data* and *code* is not foundational: interpreted input can itself describe programs. The relevant dimensions are expressiveness of the admitted language, the properties that can be stated, and the obligations decidable or tractable enough to discharge automatically. Fuel can make an evaluator total without making the underlying unbounded program terminating.

## Existing work, prior measurements and related issues

- [Issue #398](https://github.com/danbri/factoidal-core/issues/398) — retained GPU scene and compute binning roadmap.
- [Issue #450](https://github.com/danbri/factoidal-core/issues/450) — heavy glyph stroke geometry bottleneck.
- [PR #473](https://github.com/danbri/factoidal-core/pull/473) — kernel expressions, bounds/race proofs and GPU differential harness.
- [PR #490](https://github.com/danbri/factoidal-core/pull/490) — proved parallel CPU chunk map.
- [PR #503](https://github.com/danbri/factoidal-core/pull/503) — per-cell/per-row edge and stroke lists.
- [Issue #498](https://github.com/danbri/factoidal-core/issues/498), [PR #494](https://github.com/danbri/factoidal-core/pull/494) — separate Lean/Veil system transition models.
- [`SVGRaster.lean`](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGRaster.lean), [`2026-11-16-incremental-equals-full.md`](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-16-incremental-equals-full.md) — current differential tests and proof gaps.

Potential background approaches: typed DSL/deep embedding, SOACs (Futhark), Accelerate's stratified `Acc`/`Exp` design, `Lean.Expr`/Qq source recognition, proof-producing transformations and translation validation. These are **research precedents**, not implementation dependencies.

## Hand-off for Codex

> Implement issue #604 in small proof-checked increments, using this document as the architecture scope. Build the ordinary Lean CPU specification first; prove stable packing in a generic utility namespace; preserve the original CPU fallback. Keep generated WGSL and all tests separate from Foafnaut. Do not overclaim verified code generation or GPU execution. Identify missing theorems and hardware gaps explicitly, and report exact build/test commands and results. Avoid changes to existing browser rendering and avoid new heavyweight dependencies.

This document is an agreed **plan**, not a claim that the requested theorem chain or GPU implementation has already been achieved.
