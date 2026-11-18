# The presenter, its hosts, and linked engine instances

Date: 2026-11-17. Status: design, with the first spec built (`L4Factoidal/Presenter/Spec.lean`).

## Problem

Foafnaut already draws in layers: Lean gives a chrome layer and a page layer for a band of page
rows, and a scroll inside the band only runs the composite again with a new offset
(`layer_compositor.ts`). But on the Mac the composite runs on the same Deno thread as the
engine's turns. A 7.9 s script turn (BBC News) therefore holds every scroll for 7.9 s, and
long-article scroll p95 is 1.5 to 2.5 s against a 16.7 ms target
(skills/perceived-performance). Other browsers keep scrolling on a compositor thread while
scripts run. That is the largest gap in how Foafnaut feels.

Two ways to give the composite its own thread were on the table on 2026-11-16: a non-blocking
Deno binding, or a present path owned by `native_window.m`. This design does not choose
between them. Every host runs one presenter step written in Lean, and each host only has to
show that its mailbox is the channel the spec names. Stage 1 can then ship today on Deno, and
stage 2 moves to `native_window.m` with a small, checked change.

## The interface

`L4Factoidal.Presenter` (Spec.lean, imports nothing from the engine, so a native host can link it alone):

| Name | What it is |
|---|---|
| `LayerFrame` | id, `bandTop`, `bandHeight`, `keepFrom`, `keepTo` of a finished frame (the textures are host handles, not part of any decision) |
| `State` | view height, scroll, the frame shown, the scroll last asked for |
| `Input` | `scrollTo y`, `resize h`, `frame f`, `vsync` |
| `Output` | `present frameId offset`, `needBand scroll` |
| `step : State → Input → State × List Output` | the only presenter decision |
| `offsetOf` | the composite offset; replaces `clampOffset` in `layer_compositor.ts`, which the host then no longer computes |
| `LatestWins`, `LastRequestSeen`, `Mailbox` | the channel contracts a host's mailbox must meet |

A host provides four operations and decides nothing:

```
postFrame(f: LayerFrame, textures)   engine side: publish into the latest-wins slot
takeInputs(): Input[]                presenter side: window events and display ticks, in order
present(frameId, offset)             presenter side: run the composite plan Lean already gave
requestBand(scroll)                  presenter side: publish into the engine's request slot
```

The presenter loop on every host: drain inputs, call `step` for each (one op on the engine
dylib or Wasm, `presenterStep`, pure), carry out the outputs. The engine loop: take the latest
request, lay out and draw the band, `postFrame`.

## Hosts

| Stage | Presenter thread | Engine thread | Mailbox | Cost to switch |
|---|---|---|---|---|
| 0 (now) | Deno main thread | the same thread | none: calls in sequence | — |
| 1 (today) | Deno main thread: window, GPU device, composite only | a Deno `Worker` loading the same engine dylib (`Deno.dlopen` works in workers with `--allow-ffi`) | `SharedArrayBuffer` slots for frame and request; layer pixels uploaded to GPU textures by the presenter, or written by the worker into a shared buffer | new worker entry, slot code, host contract ops `presenterStep` and `postFrame` |
| 2 | a present thread in `native_window.m` (CAMetalLayer, display link) | Deno main thread | C atomics in `native_window.m` with the same slot layout | the slot code moves into C; `step` is the same compiled Lean |
| Hub | the page's main thread (OffscreenCanvas composite) | the existing `browser-worker.mjs` | `postMessage`, or `SharedArrayBuffer` where cross-origin isolated | adopt `presenterStep` in place of its own offset arithmetic |

The GPU limit of 2026-11-16 (Deno cannot create a window surface in a worker, and
`onSubmittedWorkDone` blocks) shapes stage 1. The surface and the composite stay on the main
thread. The engine leaves the main thread instead, which Deno does allow. Layer raster that
needs the GPU either runs on the presenter in bounded slices (each plan is already a command
list) or moves to CPU raster in the worker for stage 1 (the GPU path equals CPU raster on all
1,044 svg reftest pages).

## Theorems

Proved in Spec.lean today:

- `step_scroll_kept`: a scroll the shown frame keeps asks the engine nothing. The presenter
  answers it alone, whatever the engine is doing.
- `offsetOf_le`: the offset stays inside the band.
- `step_shown_mono`: the frame shown never goes back to an older one; late frames are dropped.
- `step_vsync`: a tick presents exactly the shown frame and changes no state.
- `ask_once`: no duplicate band requests.

Wishlist, in order:

1. **Host equivalence.** Two hosts whose mailboxes satisfy `Mailbox` and which call the same
   `step` present the same outputs for the same interleaving of inputs and posted frames. This
   is a refinement proof over `run` and is mostly bookkeeping once `Mailbox` is fixed.
2. **The single-thread host is a special case.** With a synchronous engine (every `needBand` is
   answered before the next input), `run` presents what stage 0 presents. The existing pixel
   tests (`frame_cost_test`, `scroll_layers_check`, `partial_frame_test`, the GPU/CPU raster
   diffs) stay the oracle for stages 1 and 2.
3. **Convergence.** Once input stops and the engine answers the last request, the presented
   frame equals stage 0's frame for that scroll.
4. **Latency bound.** In a Veil model (dickory `labs/veil`, next to the parallel pages pipeline
   model): a scroll inside the kept band is presented within one tick of the next `vsync`,
   whatever the length of the engine's turn. This is the property people feel.
5. **Mailbox implementations.** Stage 1: the `SharedArrayBuffer` slot (sequence number plus
   seqlock) meets `LatestWins` and `LastRequestSeen`; tested by a stress test with random
   interleavings and checked against a TLA-style model. Stage 2: the same for the C atomics.
6. **Consistency.** No presented picture mixes two frames: the textures and the offset of a
   `present` come from one `LayerFrame`. This holds by construction in the slot layout and is
   stated as a host-contract property.
7. **Bounds.** Slots hold one frame and one request. Memory is bounded by two frames' textures
   plus the one being drawn, and that bound is checked in the host contract.
8. **Host contract.** `presenterStep` is a `query` op, `postFrame` a `state` op; both are listed in
   `HostContract.ops`, and trace checks (`host-trace.mjs`) cover the presenter loop too.

Later inputs that extend `Input` the same way: pinch zoom (a scale on the composite), momentum
phases, scroll anchoring (`keepFrom`/`keepTo` shift with the anchor), and fixed or sticky
layers (more than one page layer per frame).

## Linked instances

The same pattern serves several engine instances that work together: windows of one browser,
widgets embedded in a page, frames, a form spread across several pages. On the web platform
each instance is a Wasm build of the engine in its own worker; natively, a session in the
dylib.

Interface:

| Name | What it is |
|---|---|
| `Instance` | id, origin, role (`page`, `widget`, `formModel`, `dataStore`, `presenter`) |
| `Link` | a typed channel between two instances: its message schema (checked by Lean on both ends), its direction, and its delivery contract (`LatestWins`, FIFO, request/response) |
| `System` | instances plus links; its behaviour is the product of each instance's `step` with the links' delivery contracts |

A whole-system property is then proved assume-guarantee: each instance is proved against the
contracts of its links, and each link implementation is proved against its contract once.

Enterprise form filling with XForms and the web data stack (`L4Factoidal/XForms`, SHACL,
JSON-LD, the RDF store), as an example:

- The **form model** instance holds the XForms instance data, binds and model item properties
  (`XForms.Model.step`, built and measured 2026-11-14). It is the only writer of the data.
- Each **page** or **widget** instance shows part of the form. It sends `setValue` requests over a
  FIFO link and receives refreshes over a `LatestWins` link.
- The **data store** instance validates and keeps submissions (SHACL shapes, provenance).

Wishlist for that system:

1. **Widget refinement.** A widget never commits a value the model's `type`, `constraint`,
   `required` or `readonly` properties reject; it can only propose. This is proved against
   `XForms.Model.step`.
2. **Cross-page consistency.** After every page's requests have been delivered and refreshed,
   every page shows the model's current instance data (convergence, as wishlist item 3 above).
3. **Submission integrity.** A submission is the serialisation of the model's instance data at
   one recalculated state. It validates against its SHACL shape, or the data store refuses it
   with the shape's report. A retry with the same key is applied once.
4. **Drafts.** A restored draft equals the model state that was saved: a round trip of the
   instance data through client storage.
5. **Non-interference across origins.** An instance's outputs depend only on its own inputs and
   the messages its links let in. A widget from another origin learns nothing of the form
   beyond the bound nodes the model sends it. This is the same statement shape as the PageCanvas
   taint theorems.
6. **Host independence.** The same theorem as wishlist item 1 above, per instance: the system
   behaves the same in Foafnaut native, on the Hub, and in another browser running the Wasm
   build.

## Order of work

1. Stage 1 on Deno: the engine in a worker, the presenter on the main thread calling
   `presenterStep`, `SharedArrayBuffer` slots, host contract ops, the stress test, and timings
   (scroll p95 on the realpages snapshots, before and after, with the engine busy). Wishlist
   items 1, 2 and 8.
2. The Veil latency model (wishlist item 4), next to the parallel pages pipeline model.
3. The Hub adopts `presenterStep`.
4. Stage 2 in `native_window.m`, when Deno's limits bite (for example a display-link `vsync`, or
   presenting while Deno's thread is in a long FFI call).
5. Linked instances: the form model / page / data store split for XForms, starting from the
   existing XForms engine and its test suite.
