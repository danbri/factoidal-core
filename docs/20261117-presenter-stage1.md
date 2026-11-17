# Presenter stage 1 worknote

The presenter uses `L4Factoidal.Presenter.step` through a separate pure C entry point.
The generic document entry point has process-global mutable engine state, so the main
thread must not call that entry while the worker runs. The pure entry is initialised
before starting the worker and never reads the document state.

The existing Deno engine worker already owns layout and script execution. Worker mode
also requests the existing Lean CPU raster sections. The main thread uploads those
pixels and runs the Lean composite shader. It retains the window, surface and GPU device.
Inline mode retains the synchronous engine and the existing GPU raster as the oracle.

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
