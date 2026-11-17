# Presenter stage 1 worknote

The presenter uses `L4Factoidal.Presenter.step` through a separate pure C entry point.
The generic document entry point has process-global mutable engine state, so the main
thread must not call that entry while the worker runs. The pure entry is initialised
before starting the worker and never reads the document state.

The existing Deno engine worker already owns layout and script execution. Worker mode
also requests the existing Lean CPU raster sections. The main thread uploads those
pixels and runs the Lean composite shader. It retains the window, surface and GPU device.
Inline mode retains the existing engine worker, GPU raster and host placement as the oracle.

Frames use one bounded shared byte slot. Requests use one shared scalar slot. Each
publication has a 64-bit sequence and a seqlock. Reads return busy rather than spin
while the writer is paused. Completed reads correspond to one stable publication;
at quiescence they return the final publication. Eventual delivery assumes the reader
continues polling. The JavaScript implementation is tested, not formally proved.
Frame payloads include the request identifier, metadata and binary typed-array sections.
An over-capacity publication refuses before it changes the slot.

Validation so far:

- Mailbox and frame transport: 6 Deno tests pass, including random schedules and real workers.
- Deno typecheck: run_html.ts and native_html_worker.ts pass.
- Shared Lean lock refuses local builds because this sandbox cannot inspect processes.
- Engine and pixel checks, native ABI concurrency, real-page timings: not yet run.
- Transport microbenchmark under the timing lock, 10 MiB, five runs after warmup:
  publication 22.70–24.51 ms; read/copy 20.59–21.54 ms. This is a transport-only result,
  not scroll latency. Large frame copies can exceed one display interval.

The theorem work and its proof boundary are in `20261117-presenter-theorems.md`.

Further checks: timing-analysis and host-contract source checks bring the local total to
12 passing tests. The cloud Lean job on 0b0d20fd0 found one failed rewrite in
stage0Request_refines; the state argument now explicitly includes the recorded request.
The repaired proof awaits compilation. Worker integration tests now exercise native/Wasm
byte parity, publication ordering and presenter calls during a real BubblePopJS turn.
They await rebuilt engines. Publication IDs are preserved through the host; stale
prefetches are checked by Lean before installation. Queued shifts check that their
textures remain installed before presenting.

Follow-up concurrency review found a final-request wake race and a queued old-prefetch
installation race. Wake generations now trigger another read after an older reply; two
deterministic tests cover final publication and termination. Draw acceptance runs inside
the GPU queue before texture changes, using the pure Lean presenter. Frame decode errors
reject the waiting call. Scroll latency is not settled against a frame drawn before the
latest requested scroll. The test script now schedules inline/worker variants of cost,
prefetch, partial-frame, scroll-pixel and sweep checks; these await rebuilt engines.

Baseline correction: the design table describes stage 0 as a synchronous engine on the
main thread, but the checked-in baseline already calls startCompileWorker for layout and
scripts (main-thread Wasm is the check/failure path). `--presenter=inline` preserves that
actual baseline; it does not introduce an artificial main-thread script stall. The
synchronous refinement theorem states its synchronous hypothesis explicitly. Before/after
timings must compare the existing worker/GPU path with the new worker CPU/SAB/presenter path.

Validation environment: setup-host.sh installed the already SHA-256-verified a5f53231e321
Wasm assets and compiled native_window.m. Inline fixture cost/prefetch checks pass 20/20
on that released runtime (not a validation of the new engine). A locked timing-harness
smoke run using installed c91b7d21d0a9 native engine exited 2 with `GPU BLOCKED: native
HTML adapter unavailable in this launch context`, before drawing or collecting any of
the 120 scheduled inputs. No before/after latency claim follows from it. The three
frozen snapshots were downloaded from factoidal-builds commit 3f998c4580cd.

Assurance review: a superseded idle-check frame now retries after quiet time instead of
ending the browser. The synchronous theorem does not establish a literal refinement of
the asynchronous host trace: the host inspects the Lean placement before GPU work and
records the shown frame afterwards; intervening input can change that latter state.
Resize reaches the presenter with the new layer viewport, and a prefetched publication
is held until selected. Pixel/ordering tests must check this host boundary separately.
The 128 MiB slot bounds a publication, not total retained host frame memory.

Queued-frame acceptance now also checks the actually installed texture frame with Lean.
This covers an abandoned draw whose textures were installed before the caller recorded
them. A pure-presenter regression test covers that gap between installed and recorded
frames; it awaits the rebuilt engine. Host and test typechecks pass.
