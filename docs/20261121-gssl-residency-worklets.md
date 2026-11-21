# GSSL residency and the proposed SPARQL worklet boundary

21 November 2026. Experimental host implementation: `tools/gssl-gpu-resident.mjs`.
No assured Hub lab and no shipping SPARQL GPU fast-path are claimed.

## Separate execution resource from application semantics

**The GPU is not an RDF store by default.** In GSSL, its state is a collection
of typed GPU buffers, textures (future extension), compiled pipelines, versioned
input artifacts and outputs. That state can represent any admitted computation:
BGP integer relations, glyphs, an SVG tile bin, a graph adjacency slice,
physics state, or a temporary matrix. A storage buffer does not come with
RDF term, named-graph or SPARQL bag semantics.

A **SPARQL worklet**, as used here, is an *application-level proposed unit of
query-plan work*: it has a selected query fragment, source/snapshot identity,
typed inputs and outputs, a failure/cancellation policy, and one or more
possible executors (native Lean, Wasm, Web Worker, a separate process, or a
GPU pass through GSSL). There is no general Web-standard SPARQL Worklet API
implemented by this module. Do not confuse it with the browser's standardized
AudioWorklet or with a GPU compute shader. A GPU kernel cannot directly
parse SPARQL, perform network I/O, or expose an arbitrary memory handle
to a separate web origin.

The proposed layering is:

    SPARQL planner / logical worklet (typed bindings + query semantics)
                  |               other domain DSLs (SVG, DOM, text)
                  v                     |
          admitted GSSL program/plan <--+
                  |
      resource binding / task scheduling
                  |
      GSSL GPU-resident session  (host: buffers, pipeline, fence, readback)
                  |
        WebGPU compute/renderer device

A worklet can be a CPU task with no GPU buffers. Several worklets may reuse
the same device/session, or a worklet can invoke a sequence of shaders whose
intermediate outputs never return to the host. A SPARQL *result* is one possible
typed output of a worklet, not the expected meaning of GPU residency.

## What is shipped in this experimental increment

`createGsslResidentSession` is an application-neutral execution resource.
Its API provides:

- `upload(name, typedArray)`: SHA-256 versioned exact-byte upload, skips
  unchanged buffers, refuses unaligned values; GPU writes invalidate the
  host's content hash.
- `allocate(name, byteLength)` and `release(name)`: explicit tracked
  storage lifetime, fixed session byte budget and no silent evictions.
- `compile(name, trustedWGSL)`: checked shader compilation and exact-source
  pipeline cache. Shader correctness is **not** established by compiling it.
- `dispatch({kernel,bindings,writes,workgroups})`: a serial compute pass
  using previously stored buffers. `writes` must name every resource that
  the trusted shader may mutate; this is a caller obligation. The API awaits
  the WebGPU submission fence before permitting reuse or debugging.
- `inspect(name,{offsetWords,countWords})`: bounded, explicit staging
  copy and mapping of selected `u32` words from an initialized resident
  buffer. The rest stays on the GPU; no automatic exports.
- `status()`, `close()`: resource counters and deterministic disposal.
  A caller-supplied GPUDevice is borrowed by default, not destroyed.

One device may execute many unrelated workloads. There is no RDF graph
parameter or SPARQL engine reference in the generic session. Buffers are
normally private to the same device and JS execution context. Exposing
selected data to another process requires the owning host to copy it out
and transport the bytes through an authorized protocol. Cross-origin
GPUBuffer inspection is not provided.

The Node tests use a deterministic device mock to cover upload reuse, write
invalidation, fences/busy refusal, resource caps, bounded readback,
compilation failure and close. A separate real Mesa/Deno WebGPU run
executes two successive affine compute passes over the same input and
inspects the final and intermediate buffers. That is an observed runtime
result, not a theorem about general shader behavior.

## Formal correspondence already available

Factoidal has an application-independent Lean module
`GpuKernel.Resident.lean`. It establishes:
`plan_noReupload`, `plan_budget`, `plan_keeps_needed`,
`plan_steady`, over abstract key/version/byte entries. It does not
make the JavaScript session automatically proof-carrying.

`formal/veil/FoafnautModels/GpuProtocol.lean` models versions,
submission numbers/fences, no use-after-free, no write-while-read and
readback only after completion. Again, these formal properties are a
target contract; there is not yet a machine-checked refinement from
this particular host implementation to the model. The session
serializes access and awaits `queue.onSubmittedWorkDone()` as
a conservative initial enforcement strategy.

A future worklet runner should *make those formal obligations explicit*
at the resource boundary: shape/size, content versions, read/write sets,
buffer usage, fences, deterministic rejection, and a worklet-specific
semantic theorem where applicable. It should not require every worklet
to use SPARQL or to store its state in RDF.

## Example: OPTIONAL SPARQL acceleration

Suppose a planner creates a logical worklet for one BGP fragment.
It can encode selected term IDs as 64-bit values (two `u32` lanes)
or use a checked dense-u32 table. The worklet references input and
scratch/output buffer IDs in the resident session, dispatches a
join kernel, and receives an *observed* output buffer. Only a separate
SPARQL refinement theorem plus source-snapshot checks justify
interpreting those words as SPARQL solution mappings.

Correlated `LATERAL` and `SERVICE` patterns are different questions:
they may create many related worklet tasks or network requests, with
binding scope and failure semantics defined by the query language.
They do not turn a GPU session into a persistent triple store, nor
provide proof of arbitrary WGSL output. GPU acceleration should only
be selected for an admitted subfragment and retain a CPU fallback.

## Remaining caveats and near-term improvements

1. A generic trusted-program manifest with typed buffer shapes and
   declared read/write sets, whose lowerings are independently checked.
2. A host-to-Lean refinement proof for allocation, versions, fences
   and diagnostics; safe device-loss handling and failure poisoning.
3. Optional cross-domain reuse, bounded eviction, GPU render-pass
   integration and controlled observability; explicit ownership if
   buffers are shared with an external component.
4. Comparison on a hardware adapter with warmed pipelines and uploads,
   without over-interpreting one Mesa software-adapter timing.
5. SPARQL worklet scheduling/selection at a separate planner layer,
   retaining graph/version identity and algebra semantics.
6. All end-to-end GSSL SPARQL assurance gates in issue #691.

No new Hub app or assured-lab claim is made by the generic residency PR.
