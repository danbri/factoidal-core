# Foafnaut: threads, tabs, processes, DNS and HTTP connections (2026-11-24)

Status: proposal. Tracking: https://github.com/danbri/factoidal-core/issues/1031 (umbrella). Owner question, 2026-11-24, verbatim: "how can we improve our app thru being
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

## 0. Priority: desktop gestures, answered at once (owner, 2026-11-25)

Owner, verbatim: "Think of user as having likely many desktop habits learned over years with
Chrome, Firefox, Safari et al." "I keep trying to command-click or CTRL-click to get a contextual
menu on a link, or open that link in a new tab, so i can do two things at once." "I keep trying
to highlight code or text or URLs from a page to copy or otherwise act on via buffer". "We should
ensure all of these gut-powered interaction attempts are honoured INSTANTLY thanks to having a UX
thread that isn't trying to run 100 JS jobs in finely sliced parallel. Make this a priority."

Found in the code (`origin/main` `34c12a74`):

- `native_window.m` `sendPointer` queues kind, x and y only. Pointer events carry no modifier keys
  and no click count (key events do carry modifiers).
- Command-click therefore follows the link in the same tab, and Control-click is a plain click.
- A right click (kind 13) opens only the address-bar menu. There is no menu for a link, image,
  selection or page.
- No word selection on double click, no line or paragraph selection on triple click.
- Copy asks the engine worker (`document.selectedText`), which has one queue for all slow Lean
  calls, page script turns included.

Rule: a gesture that a desktop browser answers at once (link click with modifiers, context menu,
selection, copy) is answered from the frame already on screen, on the main thread or in an input
lane that comes before script turns. It never waits for page scripts. The meaning of each gesture
is decided in Lean (the key table and `WebShell` already do this for keys and the address bar).
Work list: https://github.com/danbri/factoidal-core/issues/1031.

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

### 2a. Lean's own concurrency against what we built (2026-11-25)

Owner, 2026-11-25, verbatim: "Gemini tells me we've been overengineering lean on lean, and lean
comes with lean compiler/interpreter setup already", then "I was thinking more about threads,
multiprocess etc., But yes we did fart around with Enscripten in a few places, eg. looking at Lean
for verifying plugins or wasm untrusted code or managing across processes."

What Lean gives natively, on native builds: threads (`Task.spawn`, `IO.asTask`, the dedicated
priority), `IO.Promise`, `Std.Mutex`, `Std.Channel`, and subprocesses (`IO.Process.spawn`). Use in
our Lean code, counted by files on `main` (`formal/lean4/L4Factoidal`, `formal/lean4/Harness`,
`labs/demos/foafnaut`, 2026-11-25): `Task.spawn` 5, `IO.asTask` 10, `IO.Process.spawn` 6,
`IO.Promise` 2, `Std.Mutex` 0, channels 0. The native engine starts Lean's task manager
(`web_render_shim.c`, `FOAFNAUT_LEAN_THREADS`).

Where we use something else, and the reason recorded for it:
- Wasm (the Hub, the npm package): Lean's wasm runtime has no threads (section 2), so parallel
  work there needs Web Workers, each with its own module. Lean threads cannot replace them until
  the runtime is built for wasm threads.
- Desktop host: Deno owns the window, the GPU and the event loop, and calls the engine through
  FFI. One engine worker per tab is a Deno worker because the held font is Lean runtime state
  that is not shared between threads (section 1). Lean tasks inside one engine instance are the
  alternative to measure (section 3).
- Isolation (untrusted code, keys): threads share memory, so they give no isolation. A separate
  process (`IO.Process.spawn` or the host's) or a separate isolate (a Deno or Web Worker) does.
  The Tor client is in a Deno worker for this reason, and because Arti is Rust, not Lean.

Open question (not measured): which of our worker and Emscripten paths could become Lean tasks or
`IO.Process` children on native builds with no loss. Measure before changing.

Inventory of these paths (step 1, nothing measured): `2026-11-25-lean-native-concurrency-audit.md`.

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

### 3a. Landed on branch `wip/1031-worker-per-tab` (2026-11-25): what was built and measured

Built (`labs/demos/foafnaut/native_html_tabs.ts`, wired in `run_html.ts`):

- One engine worker per tab. A navigation's calls go to the worker of its tab, also after
  another tab is shown (`AsyncLocalStorage`); a script session's calls go to the worker that
  holds the session (session numbers are mapped per worker); other calls go to the shown tab's
  worker. Closing a tab ends its worker. Each worker keeps the queue rules of
  `native_html_queue.ts`.
- Each worker loads its own engine. The native library holds one engine state (`web_render_shim.c`,
  static `engine`), so a second `dlopen` of the same file would share it between threads. Each
  worker after the first loads its own copy of the library file (removed after load).
- Cap: 8 live workers (`--engine-workers N`). A tab opened at the cap shares the worker of the
  tab shown least recently. Sharing keeps that tab's script sessions and held images; stopping
  the worker would lose them and cost a start when the tab is shown again. At the cap the Veil
  model's `worker_one_page` (`FramePipeline.lean`) does not hold for the shared worker.
- Spare: after the first frame, one worker starts with no tab and lays out the start page; the
  next new tab takes it, and another starts 2 s later. Reason: a new engine's first layout of the
  start page took about 0.9 s, against 0.04 s on a warm engine. `--no-spare-engine-worker`.
- `--one-engine-worker` keeps the old mode through the same code.
- Trace: `native-html-engine-worker` (start time, library copy time, warm-up time, resident
  memory before and after, shared, ended), `native-html-tab-first-frame`; perf summary:
  `engineWorkers`, `tabFirstFrame`, `processRssMB`.

Measured on the Linux rig (Xvfb, software Vulkan, released native engine, 4 vCPU), 5 runs per
mode, medians of the per-run values. Software Vulkan draws each frame in 300 to 600 ms, so input
latency includes that draw.

- (a) Tab A loads a 2.4 MB page (20,000 table rows); 300 ms later tab B opens and gets 21 key
  presses 300 ms apart. Input latency in tab B, p50: one worker 407 ms, per tab 413 ms, per tab
  without spare 414 ms. p95: one worker 2,037 ms, per tab 691 ms, without spare 1,331 ms. Tab B
  first frame: one worker 1,875 ms, per tab 664 ms, without spare 1,317 ms.
- (b) Seven new tabs in a row (8 tabs): process resident memory at exit, one worker 689 MB, per tab
  1,596 MB, so about 130 MB for each extra worker. A worker start (library copy and engine load)
  236 ms median; the spare's warm-up layout 476 ms. New tab first frame: one worker 397 ms
  (p95 724), per tab 926 ms (p95 1,166): tabs opened 1 s apart outrun the spare, and each new tab
  waits for a cold engine.
- (c) One tab, resize sweep (7 sizes): frame total p50 one worker 568 ms, per tab 586 ms; layout
  p50 245 and 253 ms. The difference is inside the run-to-run spread (526 to 684 ms).

Not done: a worker that dies still sends every tab to the main thread (as before), not only its
own tabs; a background tab gets no lower step budget; the Hub has one engine instance; the
Veil model has no shared worker at the cap.

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
- Tor (added 2026-11-25): the pool key needs a route (`direct address` or `tor isolationToken`)
  in place of the pinned address. See
  [2026-11-25-foafnaut-tor-onion-routing.md](2026-11-25-foafnaut-tor-onion-routing.md) section 4.

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

0. Section 0 (owner priority).
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

## 3b. Parallel image decode and word shaping (measured 2026-11-25)

Profile of the first compile (first layout and frame build), `perf record --call-graph dwarf`,
threads 0. Share of samples per phase:

| Page | First compile | Image decode | Style | Text shaping | Scene | Tiles | Layout | Parse |
|---|---|---|---|---|---|---|---|---|
| en.m.wikipedia stub | 822 ms | 44.9% | 34.0% | 9.4% | 4.0% | 3.6% | 2.6% | 1.1% |
| developer.mozilla.org display | 2,622 ms | 9.3% | 52.1% | 24.4% | 5.1% | 1.5% | 6.9% | 0.2% |
| bbc.co.uk article | 3,908 ms | 67.7% | 10.3% | 5.0% | 2.7% | 5.9% | 8.1% | 0 |
| docs.python.org tutorial | 345 ms | 7.3% | 8.3% | 43.8% | 18.5% | 10.5% | 8.3% | 0.6% |
| en.wikipedia United States | 12,833 ms | 22.5% | 39.9% | 23.1% | 7.2% | 0.9% | 5.4% | 0.1% |

Style (`CSS.computeAllWith`) follows the inheritance chain and is not cut into tasks yet.

Changed: `WebRender.decodesFor` decodes each file in its own task (from 2 files;
`decodesFor_eq`: parallel equals sequential). `SfntProfile.rememberPar` shapes the words the memo
does not hold in 8 chunks (from 64 words; `rememberPar_eq`).

Measured with `realpages/engine_par_bench.ts` on the Linux cloud VM (4 vCPU, shared), 6
interleaved runs per page, medians in ms; "base" is the engine before the change, both with the
default thread pool. The scene hash is the same in every run of every configuration.

| Page | First, base | First, new | Ratio | Relayout, base | Relayout, new | Ratio |
|---|---|---|---|---|---|---|
| en.m.wikipedia stub | 764 | 683 | 0.89 | 316 | 292 | 0.92 |
| developer.mozilla.org | 2,557 | 2,492 | 0.97 | 1,702 | 1,568 | 0.92 |
| bbc.co.uk article | 4,019 | 2,802 | 0.70 | 1,517 | 1,488 | 0.98 |
| docs.python.org tutorial | 253 | 333 | 1.32 | 152 | 135 | 0.89 |
| en.wikipedia United States | 12,520 | 11,572 | 0.92 | 7,713 | 6,871 | 0.89 |

Geometric mean: first compile 0.94, relayout 0.92. The python page's first compile is slower; the
new library at threads 0 gives 344 ms on that page too, so the cost is not the threads alone.
Open: find it, and the style phase.
