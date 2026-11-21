# GSSL 0.1 — GpuDomainSpecificLanguage
**Editor's draft · 21 November 2026 · experimental · not a Web standard**

Source of truth: `formal/lean4/L4Factoidal/GpuDomainSpecificLanguage.lean`,
`formal/lean4/L4Factoidal/Paralliverse/Program.lean`,
`formal/lean4/L4Factoidal/GpuKernel/Resident.lean`,
`npm/factoidal/lib/gpu-resident.mjs`.

**This is a language and host-runtime specification, not a claim that
arbitrary programs can already be compiled to WGSL.** The current
application-independent Lean core is real and theorem-backed. The bounded
WebGPU runtime is real and tested. A general verified lowering between them
is **not yet implemented**. Sections below explicitly identify
implemented, theorem-backed, tested and proposed requirements.

## 1. Scope

GSSL (GpuDomainSpecificLanguage; sometimes abbreviated "GDSL" in discussion)
is a **workload-independent family of typed pure computations**, with a
potential bounded GPU execution profile. It is intended to serve the
Foafnaut browser (e.g. text, image, layout, glyph and DOM workloads), SPARQL
and other domain languages. A GPU buffer is a computational resource, not
intrinsically an RDF graph, a SPARQL answer, a DOM, or a persisted store.

The specification separates:

1. **GSSL Core** — finite typed composition and a mathematical denotation.
2. **Kernel Profile** — proposed bounded parallel primitives and their
   abstract memory semantics (not yet a general source compiler).
3. **Host/Device Profile** — real experimental WebGPU resident buffers,
   dispatch, fences, source fingerprints and explicit inspection.
4. **Domain adapters/worklets** — optional independently typed languages
   that lower to GSSL or invoke a GSSL executor, with additional contracts.

A SPARQL worklet is a *proposed internal query-plan task*, not a browser
standard `Worklet` API. Its RDF/SPARQL semantics stay above GSSL.

## 2. Status vocabulary

| Mark | Meaning |
|---|---|
| **PROVED** | The named Lean theorem exists, compiles and has an axiom audit. Its hypotheses remain part of the result. |
| **TESTED** | Executable fixture/differential evidence exists, including actual WebGPU where stated. Not a universal theorem. |
| **IMPLEMENTED** | Source API exists; the listed guarantee may remain a host obligation. |
| **PROPOSED** | A normative design target; do not advertise it as existing functionality. |

No `sorry`, `admit` or assumed GPU correctness is supplied by this draft.
The physical browser, shader compiler, runtime, driver and device lie
outside the present Lean semantic proof boundary.

## 3. GSSL Core (Lean model, PROVED)

Let `Atom : Type` denote domain-specific atomic type names. A type shape is:

```text
Shape α ::= scalar α
          | pair (Shape α) (Shape α)
          | list (Shape α)
```

`Shape.Value base` interprets each `scalar a` as `base a`, each
`pair a b` as a product, and each `list a` as a finite Lean list.

A domain provides a **typed signature**
`Signature Atom := Shape Atom → Shape Atom → Type` and a
**pure primitive interpretation**
`PrimitiveEval base sig`.

The current abstract syntax is:

```text
Program sig a b ::=
    identity                     // a → a
  | prim op                      // sig a b
  | seq f g                      // a → b → c
  | prod f g                     // (a,c) → (b,d)
  | fanout f g                   // a → (b,c)
  | map f                        // list a → list b
```

This is an *abstract syntax tree*, not a defined text grammar. A domain
parser for arbitrary strings is an **extra adapter**, not part of Core.
The constructors contain primitive symbols, **not** arbitrary Lean
function literals.

### 3.1 Reference semantics

For an interpretation `ops`, `Program.eval base ops` is defined by
structural recursion:

- `identity` returns its input.
- `prim op` applies `ops op`.
- `seq f g` evaluates `g (f x)`.
- `prod f g` evaluates its respective pair components.
- `fanout f g` evaluates both on the same input and returns a pair.
- `map f` applies `f` to each element in original list order.

Empty lists stay empty; duplicate values are preserved by `map`.
This **does not** imply that all domain operations preserve duplicates:
domain semantics come from the primitive signature.

### 3.2 Established theorems

- `Paralliverse.Program.eval_fuseMaps` — pure map fusion preserves the
  denotation of every well-typed program.
- `Paralliverse.Program.runCPU_eq_eval` — a task-based CPU interpreter
  agrees with the reference when its primitive implementations agree.
- `GpuDomainSpecificLanguage.eval_eq_of_primitive_agreement` —
  agreement on every primitive entails agreement of entire programs.

**Crucial quantifier:** these results do **not** assert that arbitrary
WGSL implementations agree on primitives. A GPU compiler needs separate
lowering and backend refinement evidence before using those theorems.

## 4. Kernel Profile (PROPOSED general form)

A finite kernel should carry enough information to reject unsafe or
unsupported execution **before** submitting GPU work:

```text
KernelSpec {
  inputShapes : typed buffer shapes,
  outputShapes : typed buffer shapes,
  readSet : finite names of readable resources,
  writeSet : finite names of writable resources,
  workItems : bounded nonnegative dimensions,
  scratchBytes : finite size,
  synchronization : explicit barriers / pass ordering,
  primitive : admitted symbol or expression,
  semantics : CPU-independent pure reference,
}
```

An accepted kernel must have an independently checked relation
`lower(kernel)` to its pure semantics, including:

1. Every memory access lies within its allocated resource.
2. Conflicting writes have a specified and valid synchronization
   discipline; no unmodelled data races.
3. Arithmetic overflows and `u32`/two-lane `u64` operations have
   the specified semantics, not host-number rounding.
4. Output shape, order and multiplicity are preserved when the
   operation requires them.
5. Unsupported features, excessive allocation and insufficient
   capabilities **refuse**, rather than silently fall back to a
   different semantics.

The intended library includes select/filter, stable compaction,
exclusive scan, scatter, bounded map, reduction, equality-join and
future stencil/image operations. **Not all of these exist as a unified
GSSL kernel AST, and no general Lean→WGSL lowering is currently
certified.** Existing GSSL BGP kernels are *particular* WGSL programs
with pure-model theorems and device differential tests.

## 5. Integer and resource representations

**IMPLEMENTED/PROVED for particular adapters:**

- `u32`: direct 32-bit words, including wrap modulo `2^32` in
  explicit word operations.
- `u64-lanes`: a `UInt64` is exactly `(low32, high32)`;
  equality compares **both** halves. This works with WebGPU's
  concrete `u32` type; the October 2026 WGSL spec has no
  concrete `u64` scalar.
- `dense32-snapshot`: a *different* mode with a reversible,
  query/snapshot-local integer dictionary, not a truncating cast.
- Shardborough SBM11 uses 64-bit tagged IDs; its dictionary-scoped
  equality and round-trip theorems apply to those **source IDs**.
  It is one adapter, not the GSSL global data model.

See `L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes`,
`Storage.Sbm11.TermIdTheorems` and the experimental WebGPU tests.
A 64-bit ID must not be converted through JavaScript `Number` or
truncated to `u32`.

## 6. Host/Device Profile (IMPLEMENTED and TESTED)

The experimental module `@factoidal/core/gpu-resident` exposes
`createGsslResidentSession` with the following operations:

| Operation | Host-observable behavior |
|---|---|
| `allocate(id, bytes)` | Create a named bounded storage buffer; refuse invalid sizes/budget. |
| `upload(id, typedArray)` | Copy exact bytes; use SHA-256 to avoid a redundant unchanged host upload. |
| `compile(id, trustedWGSL)` | Compile and retain a named pipeline; refuse reported source errors. |
| `dispatch({kernel,bindings,writes,workgroups})` | Bind existing resources, submit one compute pass and await completion. |
| `inspect(id,{offsetWords,countWords})` | Explicit bounded staging copy and CPU-visible readback of selected words. |
| `release(id)`, `close()` | Resource release, no implicit indefinite retention. |
| `status()` | Observable uploads, reused uploads, pipeline count, submissions, readbacks, tracked bytes/versions. |

Resources remain owned by the session across **multiple compute passes**
and can be reused by independent application workloads.

The current host executes serially; it disallows concurrent mutation,
readback and destruction while a pass is outstanding. A GPU write
invalidates the retained host-side content hash; a subsequent identical
host upload is not treated as a cache hit if a shader may have changed
the buffer. The caller is responsible for supplying a **complete and
correct `writes` set** for trusted WGSL; this is not proved by the
host implementation.

`usedBytes` is the sum of the host's retained WebGPU buffer allocations.
It is **not** proof that those allocations occupy physical dedicated
VRAM. A backend may place or migrate memory.

### 6.1 Debug and inspection

`inspect` reads at most `inspectMaxWords` (default 256) contiguous
`u32` words, using a staging buffer. Diagnostics are observational and
not a semantic proof. There is no implicit full-buffer export, no
cross-origin raw GPU memory access, and no automatic network access.

A higher-level renderer may use same-device resources directly, but
this experimental API does not yet expose a general render pipeline.
An external process needs an authorized host bridge or explicit copy;
it cannot directly map another origin's arbitrary `GPUBuffer`.

### 6.2 Versions, fences and lifetime

The pure model `GpuKernel.Resident` proves that a finite abstract
residency plan stays within a byte budget, avoids reuploading the same
version and has no uploads for an unchanged frame that fits.

`formal/veil/FoafnautModels/GpuProtocol.lean` models versions, fences,
no use-after-free and safe readback ordering with SMT reconstruction.

**Neither existing theorem proves the JavaScript resource manager or a
physical WebGPU driver.** A future host refinement must cover partial
allocation, failed queue submission, device loss, replacement, and
concurrent render/compute workloads.

## 7. Domain adapters / proposed worklets

A domain adapter must specify:

- Its own source grammar and typing, if it accepts text.
- A lowering to `Program` or an admitted `KernelSpec`.
- A reference semantics in domain terms, including errors and ordering.
- Soundness of that lowering, plus any equality/encoding assumptions.
- Snapshot, permission, resource and effect boundaries.

A SPARQL worklet, for example, is a proposed logical query-plan task
with typed bindings and a selected execution environment. It might
call native Lean, Wasm, a Web Worker, or GSSL. An intermediary GPU buffer
can hold anything its kernel defines; **it is not necessarily an RDF
store, graph or query result**. SERVICE, XMPP, file I/O and other host
effects remain outside GPU kernels.

A browser `AudioWorklet` is a different standardized execution feature;
"GSSL worklet" is not a claim of a new browser API.

## 8. Proof/evidence hierarchy

1. **Type admission**: the program is constructed from typed
   `Program` nodes, or a domain parser was separately checked.
2. **Pure denotation**: a theorem about `Program.eval` or a domain
   operator's model, such as map fusion.
3. **Representation refinement**: explicit finite-codebook, memory,
   integer-width and payload round-trip theorems.
4. **Kernel refinement**: source-level WGSL matches abstract buffer
   operations. **General form not discharged**.
5. **Device observation**: an actual GPU returned the expected data on
   recorded cases (CI, adapter and source commit supplied).
6. **Host/runtime trust**: WebGPU implementation, compiler, driver,
   scheduler and physical hardware are named trusted components unless
   their behavior is separately verified.
7. **Application conformance**: external test corpus, differential
   execution, snapshot validity and end-to-end performance for each
   domain. A GPU test does not automatically imply W3C SPARQL conformance.

The status of #4–#7 cannot be inferred from #1–#3. In particular,
`observed-not-proven` is the correct experimental result label
from the generic resident GPU runtime. "GPU was involved" is a
testable execution claim, **not** a theorem about the device.

## 9. GSSL Hub publication profiles

Two independently gated public experiences:

**Exploratory GSSL Workbench (acceptable now, if labeled accurately):**

- Runs at least two genuine WebGPU passes using a resource retained on
  the GPU between them; reports actual CPU reference and GPU readback.
- Gives a bounded diagnostic view of the intermediate buffer.
- Exposes actual submission, upload, pipeline and readback counts.
- Refuses or explains unavailable WebGPU; never silently fabricates
  a GPU answer.
- Clearly labels the arithmetic example as a fixed WGSL kernel and
  the CPU reference as a JavaScript example, not a general GSSL compiler.
- Points to this draft and the implementation's test/proof boundaries.

**Assured GSSL/SPARQL Lab (NOT ready; release gate #691):**

- Actual trusted source snapshot and memory layout;
- proved WGSL lowering for admitted fragment;
- authenticated GPU result/freshness and shipping evaluator seam;
- independent W3C/differential evidence;
- reproducible hardware and end-to-end cost evidence.

The public exploratory workbench must not claim those properties.

## 10. Minimal example (experimental device profile)

```js
import {createGsslResidentSession} from "@factoidal/core/gpu-resident";

const device = await createGsslResidentSession({byteBudget: 1 << 20});
await device.upload("source", new Uint32Array([2, 3, 5, 7]));
device.allocate("temporary", 16);
device.allocate("output", 16);
await device.compile("affine", trustedWGSL); // actual WGSL provided elsewhere
await device.dispatch({
  kernel: "affine",
  bindings: [{binding:0,id:"source"}, {binding:1,id:"temporary"}],
  writes: ["temporary"], workgroups:[1,1,1],
});
await device.dispatch({
  kernel: "affine",
  bindings: [{binding:0,id:"temporary"}, {binding:1,id:"output"}],
  writes: ["output"], workgroups:[1,1,1],
});
const observed = await device.inspect("output", {countWords:4});
device.close();
```

The intermediate stays GPU-backed between dispatches. This example
depends on the caller's `trustedWGSL` being compatible with those
bindings and the declared write set. The host doesn't statically
prove that compatibility.

## 11. Open design decisions before a normative GSSL 1.0

- A first-class **typed buffer and effect IR**, including read/write
  capabilities, shapes, workgroup barriers, overflow rules and bounds.
- Machine-checked lowering from that IR to finite WGSL source.
- A reusable checked admission procedure for kernel capabilities
  and memory limits, independent of SPARQL.
- Source-to-device proof/certification boundary with honest hardware
  assumptions; compositional treatment of CPU/GPU segments.
- Explicit resource ownership, cancellation, eviction and GPU/CPU
  scheduling across Foafnaut application worklets.
- Selection/cost policies for direct-u64-lanes vs dense-u32 adapters
  based on warm end-to-end benchmarks.
- Debugging and visualization hooks with bounded memory disclosure,
  rather than an unrestricted GPU memory debugger.
- A compatibility and versioning policy for signatures and kernel
  contracts, plus a conformance corpus of standalone GSSL programs.

## 12. Source/evidence index

- [Typed core and map-fusion theorem](../../formal/lean4/L4Factoidal/Paralliverse/Program.lean)
- [Typed CPU interpreter](../../formal/lean4/L4Factoidal/Paralliverse/ProgramCPU.lean)
- [Generic primitive-agreement theorem](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage.lean)
- [Resident planner model](../../formal/lean4/L4Factoidal/GpuKernel/Resident.lean)
- [GPU protocol model](../../formal/veil/FoafnautModels/GpuProtocol.lean)
- [Generic WebGPU session](../../npm/factoidal/lib/gpu-resident.mjs)
- [Node + actual software-WebGPU evidence](https://github.com/danbri/factoidal-core/actions/runs/44928731718/job/136920456421)
- [64-bit SBM11 representation](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/Sbm11U64Lanes.lean)
- [SPARQL-specific release gates](https://github.com/danbri/factoidal-core/issues/691)
- [Proposed SPARQL worklet contract](https://github.com/danbri/factoidal-core/issues/698)

As of this draft, there is **no general GSSL parser, verified WGSL
compiler, or fully conformant GPU SPARQL evaluator**.
