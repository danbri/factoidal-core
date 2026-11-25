# Foafnaut: threads, tabs, processes, DNS and HTTP connections (2026-11-24)

Status: proposal. Owner question, 2026-11-24, verbatim: "how can we improve our app thru being
more than single threaded? GPU aside, how can we have multiple tabs, windows, proxesses? How can
we have s helper process speculatively do basic dns lookups in advance just in case? Make use of
advanced http pipelining protocol options etc.?"

Nothing here is measured yet. Section 1 is read from the code at `origin/main` `f2215619`.
Sections 2 to 7 are proposals; each says what to measure before it lands.

## 1. What runs where today

Desktop window (`labs/demos/foafnaut/run_html.ts`):

- Main thread: Cocoa window, input queue, GPU, and small Wasm calls (hit tests, address bar).
- One engine worker (`native_html_worker.ts`): one ordered queue for every slow Lean call, for
  all tabs. Reason recorded in the frame pipeline record: the held font is Lean runtime state that
  is not shared between threads.
- Tabs: an array in `run_html.ts`. All tabs are in one process and use the one engine worker.
  A slow page in tab 1 delays a click in tab 2.
- Lean task pool: the native library starts Lean's task manager with one thread fewer than the
  CPUs, at most 6 (`web_render_shim.c`, `FOAFNAUT_LEAN_THREADS`). One engine path uses it: the SVG
  tile listing (`SVG.lean`, `Par.mapChunksAbove`). The Wasm build has no task manager, so
  `Task.spawn` runs at once on the calling thread.
- Dedicated workers (`WasmVM/Hosts/LeanJSWorkers.lean`): each has its own realm, heap and event
  loop, but scheduling is "interleaved on one thread, deterministically".

Network (`labs/demos/foafnaut/native_net.ts`, `Net/PageFetch.lean`):

- The engine decides each request; the host moves bytes.
- For a page that is not local, each transfer starts with a resolve-only request
  (`Deno.resolveDns`); `Egress.choose` refuses special-purpose addresses and pins one address.
- Each request gets a new HTTP client. For `https`, the client goes through a loopback tunnel that
  accepts one connection. So every request pays a new TCP connection and a new TLS handshake. No
  connection is reused, and HTTP/2 multiplexing never carries more than one request.
- No DNS cache in our code. Each transfer resolves again.
- The Veil model `formal/veil/FoafnautModels/HttpConnections.lean` already states the contract a
  connection pool must keep (pool key, stream limit, response to its owner, close fails pending
  requests, HTTP/2 flow control window). No pool implements it yet.

## 1a. Related work already in the tree (added 2026-11-25)

There is no single tracking issue for threads and processes. The pieces:

- https://github.com/danbri/factoidal-core/pull/490 (merged 2026-11-16; Lean task manager,
  parallel SVG tile listing, `HostPipeline` model with trace checks in `test.sh`). Measured on an
  Apple M1: the task pool gives 5 to 10% of a first frame (Spinal Tap 161 to 156 ms). The host
  pipeline change in the same PR gave the large gain: article scroll input latency p50 880 ms to
  47 ms. Cost recorded there: a first version gave the tasks every retained item; Lean marked all
  captured values as shared between threads, and engine p50 went from 40 to 49.6 ms. Pass a task
  only the data it changes.
- Same PR, recorded limit: with Deno 2.9 a window surface cannot be made in a worker
  (`raw-window-metal`: "can only access NSView on the main thread"). Off screen, a GPU device in a
  worker works (main thread's longest gap 37 ms against 73 ms).
- https://github.com/danbri/factoidal-core/pull/600 (open; presenter: one proved compositor
  `step` for every host, design for threaded scrolling, `Presenter/Spec.lean`).
- https://github.com/danbri/factoidal-core/pull/418 (merged; page `Worker` API, execution
  interleaved on one thread).
- https://github.com/danbri/factoidal-core/issues/498 (Veil models). Its `FramePipeline` model
  already has pages on several engine workers (2 pages, 2 workers, 3,726 states checked; a worker
  holds one page, a page one worker). So section 3 below implements a design that is already
  modelled.
- https://github.com/danbri/factoidal-core/issues/398 (GPU retained scene, glyph atlas, compute
  binning). It is a GPU issue; its comments hold the threading notes of PR 490.
- Paralliverse (`L4Factoidal/Paralliverse/`, project
  https://github.com/danbri/factoidal-core/issues/604): typed static `Program`s whose CPU
  interpreter runs every list map through `Par.mapChunks`, with one compositional theorem
  (`ProgramCPU.lean`) for every program and every worker count, and a GPU word-map path.
- GDSL 0.2 and PVGraph (`docs/specs/gdsl-0.2.md`, `docs/designissues/2026-11-22-gdsl-app-api.md`,
  https://github.com/danbri/factoidal-core/issues/741): typed acyclic dataflow graphs with Lean
  reference semantics and a Lean-owned GPU plan.

## 2. What Lean gives for concurrency

- Pure code: `Task.spawn f` has the meaning `⟨f ()⟩` in the logic. A parallel map has the meaning
  of the sequential map by definition, and `Par.mapChunks_eq` proves that chunking changes nothing.
  Parallel work over pure functions needs no new correctness proof, only measurement.
- Cost in pure code: a value that two threads can see is marked multi-threaded, and its reference
  count changes become atomic. Measure the work per chunk against this cost
  (`mapChunksAbove` already skips small inputs).
- `IO` code: `IO.asTask` (with `Task.Priority.dedicated` for a long-lived thread), `IO.Promise`,
  `Std.Mutex`, `Std.Channel`. The logic says nothing about interleaving here. Concurrent `IO`
  behaviour needs a model (section 6).
- Wasm: Lean's wasm runtime has no threads. Threads in the Hub need wasm threads
  (`SharedArrayBuffer`, so the page must be cross-origin isolated with COOP and COEP headers) and a
  Lean runtime built for them. Until then, the Hub gets parallelism only from more Web Workers,
  each with its own wasm instance.

## 3. One engine worker per tab (first step for tabs and windows)

A document is a Lean value, so it can live in its own worker.

- Change: one engine worker per tab (and so per window), not one for all. The main thread routes
  input to the worker of the tab it belongs to. The existing request rules (queue bound, deadline,
  terminate on abort, generation numbers, from the renderer worker record) apply per worker.
- Gains: a busy tab does not delay another tab; a stuck page is terminated without loss of the
  other tabs; background tabs can get a lower step budget or be paused.
- Cost: each worker loads the engine and its own fonts (the held font is per thread). Measure
  start time and resident memory per extra worker before the change; if the font cost is large,
  share the font bytes (immutable) and parse once per worker, or move the font to a value passed in.
- Measure: input latency in tab B while tab A loads a heavy page (`native-html-input-latency`),
  before and after.

Dedicated workers of a page can move to their own threads in the same way, because each is
already a separate session value. The deterministic interleaving then becomes one possible order.
The structured clone in `JS/Clone.lean` is already the only thing that crosses.

## 4. Processes

Inside one process, Lean already separates sessions: one session cannot name another session's
heap (origin isolation record, section 2, item 5). A process boundary adds protection against
faults in the trusted base, which Lean's types do not cover: the Lean runtime in C, `@[extern]`
code, the GPU driver, and resource exhaustion (a page that takes all memory kills only its process).

Proposal, after section 3 lands and is measured:

- A browser process: window, input, GPU, the address bar, the tab list, bookmarks, history.
- A network process: DNS, connections, TLS (sections 5 and 6). It is the only process that opens a
  socket.
- Renderer processes: one per site (scheme and registrable domain), started with
  `Deno.Command` and talking through pipes with the same messages the worker uses. A renderer
  process has no network and no file access (Deno permissions: no `--allow-net`, no
  `--allow-read` beyond its engine files).
- Precedent: Quark (Jang, Tatlock, Lerner, USENIX Security 2012), a proved kernel with one
  sandboxed engine process per tab. Our kernel would be the browser and network processes, with
  their decisions in Lean.
- Measure: process start time (engine load, prelude snapshot), memory per process, and the cost of
  moving a frame's bytes through a pipe against a worker transfer.

## 5. Connection reuse, HTTP/2 and HTTP/1.1 pipelining

This is the step with the most probable gain for real pages, because today every request opens a
new connection.

- Pool: keep one HTTP client per pool key, as `HttpConnections.lean` defines it: origin, network
  partition (top-level site) and pinned address. Reuse it while the DNS answer is valid. For
  `https`, the tunnel must accept more than one connection for that key, or be replaced by a
  connector that dials the pinned address and checks the certificate against the name.
- HTTP/2: Deno's client negotiates it by ALPN when a connection is reused. With a pool, many
  requests to one origin share one connection with multiplexed streams.
- HTTP/1.1 pipelining (several requests sent before the first response): do not implement.
  Chrome and Firefox removed it or keep it off, because of head-of-line blocking and proxies that
  corrupt pipelined responses. HTTP/2 multiplexing replaces it.
- HTTP/3 (QUIC): not in Deno's `fetch` as far as this record knows; check before any plan.
- `<link rel=preconnect>` and `103 Early Hints`: open a pooled connection early, under the same
  pool key and the same egress rules.
- Measure: the realpages survey (`skills/realpages-survey`) first frame and load time, with
  connection count per page, before and after.

## 6. DNS cache and speculative resolution

A helper (a worker, or later the network process) that resolves names before a request needs them.

Which names: hosts of links in the visible part of the page, of the link under the pointer, of
the address bar text while the user types, of `<link rel=dns-prefetch>` and `preconnect`, and of
frequent history entries at start.

Rules, so that it keeps the existing guarantees:

- A cached answer goes through `Egress.choose` like a fresh one. The pin of a transfer is decided
  once; a later cache update does not move a request in flight (the DNS rebinding rule stays).
- Keep each answer only for its TTL. `Deno.resolveDns` does not return the TTL today
  (to check); without it, use a short fixed lifetime and say so.
- Partition the cache by top-level site, as Chrome and Firefox do, so one site cannot learn from
  timing whether another site resolved a name.
- Privacy: each speculative lookup tells the resolver about a link the user did not follow. Chrome
  and Firefox do not prefetch the names of anchors on `https` pages unless the page sets
  `X-DNS-Prefetch-Control: on`; do the same. Off in a private window. A setting turns it all off.
- Cost: probing is costed work (capability planner rule, owner 2026-10-12). Bound the number of
  lookups per page and per second, and record hits and misses so the gain can be measured.
- Measure: time from click to first response byte, with and without, on the realpages set.

## 7. Models and theorems (Lean and Veil, in the TLA+ style)

The project already uses Veil for system models: `HttpConnections`, `Glue` (per-page event
loops as components), `FramePipeline`, `GpuProtocol`. Add, before each implementation:

- `DnsCache`: an entry is used only within its lifetime and only in its partition; a transfer's
  pin never changes after the first answer; every used address passed the egress check.
- Section 3: check the implementation against the existing `FramePipeline` model (it already has
  several engine workers) by the trace checker that issue 498 lists as next. Later a
  `SiteProcesses` model (section 4): a renderer receives only bytes for its own site; terminating
  one worker or process fails only its own requests.
- The pool implementation is checked against `HttpConnections` by a differential trace test: the
  host records its connection events, and Lean checks the trace against the model's transitions,
  as `HostContract/Trace.lean` does for the host contract.

Veil checks safety invariants. Liveness ("every request completes or fails") needs a different
method; say so where a claim needs it.

## 8. Order proposed

1. Connection pool and HTTP/2 (section 5), with the realpages measurement.
2. DNS cache, then speculative resolution (section 6), with its privacy rules.
3. One engine worker per tab (section 3).
4. Data-parallel engine work (image decode, glyph raster, shaping of independent runs, style of
   independent subtrees), at the places a profile names. Write it as a Paralliverse `Program` where
   the work is a typed map, so the CPU refinement theorem covers it and the same program can later
   go to the GPU word-map path or a PVGraph; use bare `Par.mapChunks` only where the work does not
   fit a `Program`. PR 490 shows the expected size of this gain is small until a profile says
   otherwise.
5. Processes per site (section 4).

Each step gets an issue with its measurement command before work starts.
