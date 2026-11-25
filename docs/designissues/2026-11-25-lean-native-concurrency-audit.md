# Lean native concurrency: audit of worker, process and Emscripten paths (2026-11-25)

Owner, 2026-11-25, verbatim: "1 yes". This answered the proposal to audit "which of our worker and
Emscripten paths could become Lean tasks or IO.Process children on native builds with no loss.
Measure before changing." The question comes from section 2a of
`2026-11-24-foafnaut-concurrency-and-network.md` (tracking:
https://github.com/danbri/factoidal-core/issues/1031, threads, tabs, processes, DNS and HTTP).

Status: inventory only (step 1). No code changed. No speed result is claimed. Every line number is
read from `main` on 2026-11-25. Each row says what a measurement needs. Nothing here is measured.

## Method (repeat it with these commands, from the repository root)

1. Web and Deno workers:
   `grep -rnE 'new (Shared)?Worker\(' --include=*.ts --include=*.mjs --include=*.js --include=*.njk --include=*.html . | grep -v node_modules | grep -v third_party`
   and `grep -rln worker_threads` over the same file types.
2. Child processes started by hosts:
   `grep -rnE 'Deno\.Command|child_process|spawn\(' ... labs/demos/foafnaut tools docs/web npm/factoidal/bin npm/factoidal/lib npm/textnaut/bin`.
   Files under `tests/` and `*test*` were counted as one group (rows 30 and 31), not row by row.
3. Lean side: `grep -rnE 'Task\.spawn|IO\.asTask|IO\.Promise|Std\.Mutex|Std\.Channel|IO\.Process\.(spawn|output)|Task\.Priority' formal/lean4 --include=*.lean`,
   then a read of each file head for its recorded reason.
4. Emscripten: `grep -rilE 'emscripten|emcc|emsdk' tools formal/lean4 labs docs/designissues skills npm`.
5. Plugins and untrusted wasm: `grep -rilE plugin docs/designissues`, and
   `grep -rniE 'untrusted wasm|verifying plugin|plugin.*wasm|wasm.*plugin' docs/designissues`.
6. Reasons: quoted from the file head or from the design record named in the row. "No reason
   recorded" means no comment or record states one.

What the method cannot see: a worker started through a wrapper that hides the word `Worker`, and
an Emscripten use in a file the word list does not name. Rows 30 and 31 are groups, so their
counts are lower bounds.

## Rows

Targets: native desktop (Foafnaut with Deno), wasm Hub (browser), npm/Node, CI tool.
"Native Lean replacement" means `Task.spawn`, `IO.asTask` or `IO.Process.spawn`.

### A. Foafnaut native desktop and its lab

1. `labs/demos/foafnaut/native_html_compile.ts:40` (one per tab, `native_html_tabs.ts`). A Deno
   Worker holds the Lean HTML engine (a dylib or the wasm). All slow Lean calls run there, so the
   main thread keeps the window, input and GPU. Reason recorded: "all Lean calls stay on this one
   thread" (`native_html_worker.ts:1-7`); "the native library keeps one engine state per loaded
   copy, so each worker after the first loads its own copy" (`native_html_tabs.ts` header);
   held font is Lean runtime state not shared between threads (2026-11-24 record, section 1).
   Target: native desktop (and Hub with the wasm). Replacement: `IO.asTask` with
   `Task.Priority.dedicated` per tab, only after the engine state is per session and not per
   loaded copy. Would be lost: Deno ownership of the FFI call and of worker termination; the
   queue rules (lanes, deadline, generation numbers) now written in TypeScript; and the worker
   has no way to be stopped in the middle of a native call, which a Lean task does not have
   either. Measure first: `tabFirstFrame` and `engineWorkers` (`native-html-engine-worker`
   trace: start ms, `copyMs`, `rssBeforeMB`, `rssAfterMB`), `processRssMB`, input latency p50 and
   p95 in tab B (`--perf-summary`; `tools/native-frame-report.py`); compare `--engine-workers N`
   and `--one-engine-worker`. Section 3a of the 2026-11-24 record has the baseline: about 130 MB
   per extra worker, worker start 236 ms median.

2. `labs/demos/foafnaut/web-render/engine.mjs:10` (`createEngine`). A Web Worker runs the Lean
   renderer wasm. Reason: "Terminating this worker interrupts synchronous WASM, which cannot
   receive a cancel message" (`engine-worker.mjs:1-2`; `2026-11-04-renderer-worker.md`: a
   deadline terminates the worker). Target: wasm Hub (lab). Replacement: none; the wasm runtime
   has no threads (`Wasm/build-wasm.sh:264`). Lost if removed: preemption by terminate, the
   queue and byte bounds. Measure: not a replacement candidate, so only the deadline tests in
   `web-render/tests/engine-worker.test.mjs`.

3. `labs/demos/foafnaut/web-render/script-engine/session.mjs:26` (worker file `worker.mjs`). A
   Worker runs QuickJS-NG (WASI reactor) for page scripts on the Hub. Reason recorded: "use the
   unmodified QuickJS-NG 0.18.0 WASI reactor in a dedicated worker for the browser MVP"
   (`2026-11-03-script-engine-architecture.md`, itself marked superseded for the desktop by
   BubblePopJS on 2026-11-09). A host watchdog terminates it. Target: wasm Hub; lab tests on
   Node. Replacement: none for a wasm guest (needs the worker as the isolate and the watchdog).
   Measure: not a candidate.

4. `labs/demos/foafnaut/tor-wasm/deno/tor-host.ts:24` (worker `tor-worker.ts`). A Deno Worker with
   narrow permissions (net, read of the module only; write, env, run, ffi, sys, import off) runs
   the Arti (Tor) wasm and gives it TCP. Reason: isolation by permission, and Arti is Rust, not
   Lean (2026-11-24 record, section 2a). Target: native desktop (experimental). Replacement:
   a Lean task would share the process and have all its permissions: isolation lost. An
   `IO.Process.spawn` child would keep isolation only with an OS sandbox that Deno
   permissions give today. Measure: not a candidate.

5. `labs/demos/foafnaut/native_state.ts:16` (`webStateCall`). A Deno child process runs
   `web-state` (a Lean program) with JSON lines on pipes, one request at a time. Reason: no
   reason recorded in the file; header says Lean decides, this file starts the server and
   carries bytes. Target: native desktop. Replacement: the child is already a Lean program in its
   own process. A Lean `IO.Process.spawn` helps only if the host were Lean. Lost: nothing to
   gain. Measure: not a candidate. (To look at later: the cost of one JSON line round trip, no
   metric exists.)

6. `labs/demos/foafnaut/native_state.ts:62`. A Deno child process runs `factoidal lws-serve` (the
   Node host of the Lean LWS engine) on 127.0.0.1. Reason: no reason recorded beyond "the server,
   unchanged" (header). Target: native desktop. Replacement: none now; the LWS server host is
   Node code that calls the wasm. Measure: not a candidate.

### B. Wasm Hub pages (browser)

All use a Web Worker with its own wasm instance. The Hub build has no threads: "the Hub gets
parallelism only from more Web Workers, each with its own wasm instance" (2026-11-24 record,
section 2), and `Wasm/build-wasm.sh:264` records why: "NO -pthread: a pthread build needs
SharedArrayBuffer, which needs COOP/COEP response headers that GitHub Pages does not send."
Native replacement: none on the Hub, because a Lean task needs a Lean runtime with threads.

7. `docs/web/hub/foafnaut/browser.mjs:54` (`browser-worker.mjs`): the browser loop; falls back
   to the page thread when a sandboxed guest has an opaque origin (the same file, comment above
   line 54).
8. `docs/web/hub/html-webgpu/app.mjs:2` (`worker.mjs`): "keeps Lean compilation and GPU readback
   off the editing thread".
9. `docs/web/hub/textnaut/engine.mjs:9` (`engine-worker.mjs`): one shared engine worker per page,
   started on first request, "answered one at a time, in order".
10. `docs/web/hub/paralliverse/app.mjs:136` and `docs/web/hub/paralliverse/bgp-studio.mjs:232`
    (`worker.mjs`, `bgp-worker.mjs`): CPU runtime of the Lean parallel programs; "NOT an SBM11
    block worker, GPU query, remote process or Kubernetes cluster" (`bgp-worker.mjs:5`).
11. `docs/web/hub/data-compositor/app.mjs:94`: runs the published npm core in a worker. No reason
    recorded.
12. `docs/web/hub/epub/app.mjs:71`: opens an EPUB in Lean wasm in a worker. No reason recorded.
13. `docs/web/hub/wasm-stack.njk:74`: a Blob worker that measures the call stack depth of wasm in
    a worker against the main thread. It is a measurement, not a feature.
14. `labs/demos/foafnaut/browser-webgpu/app.mjs:17`: lab page, worker for the Lean renderer. No
    reason recorded.

For rows 7 to 14: Target wasm Hub. Lost if replaced: nothing can replace them in the browser.
Measure: not candidates. A native desktop build that reuses one of these pages would be row 1.

### C. npm package and Node

15. `npm/factoidal/bin/serve.mjs:415` (`listenOnWorker`, `serve-worker.mjs`): a Node worker thread
    runs the SPARQL server so the main thread is free. Reason: `resourceLimits.stackSizeMb` (the
    wasm engine needs a deep stack, see row 17). Target: npm/Node. Replacement: none; the engine
    is wasm inside the worker. Measure: not a candidate.

16. `npm/factoidal/lib/sync-http-node.mjs:47`: a Node worker does `fetch`; the calling thread waits
    on `Atomics.wait`. Reason recorded: "The engine is inside WebAssembly and asks for bytes
    synchronously; Node's fetch is asynchronous." Target: npm/Node. Replacement: none (the
    wasm engine calls the host synchronously). A native Lean binary would use a socket
    directly. Measure: not a candidate.

17. `npm/factoidal/bin/store-worker-host.mjs:245` and `npm/factoidal/bin/pack-host.mjs:290`
    (workers `store-worker.mjs`, `pack-worker.mjs`). Node worker threads with a large stack.
    Reason recorded: "the defect this file exists for": the pack fold recurses one frame per
    term, and on the default Node 22 or Deno 2 stack it overflows above about 0.25 MB of Turtle
    (`pack-host.mjs` header, issue https://github.com/danbri/factoidal/issues/649). A wasm
    instance and an opened store handle "do not cross a thread boundary"
    (`2026-09-05-store-handle-call-stack.md`). Under Deno the command re-executes itself with
    `--v8-flags=--stack-size`. Target: npm/Node and Deno. Replacement: a native Lean binary has
    its own stack setting (`LEAN_STACK_SIZE_KB`), so the worker is a wasm-only need. Measure: not
    a candidate for the npm package; the native route is `l4block-shard-pack`.

18. `npm/textnaut/bin/textnaut.mjs:92`: a Node launcher starts Deno (`spawn(deno, [...])`) with
    read, ffi, net and env permissions. Reason: Textnaut runs on Deno; the launcher installs Deno
    if absent (same file, line 53). Target: npm/Node. Replacement: none (a Lean `IO.Process.spawn`
    would need a Lean launcher). Measure: not a candidate.

### D. Lean code (already native or modelled)

19. `formal/lean4/L4Factoidal/WasmVM/Hosts/LeanJSWorkers.lean` (header lines 1-25). Page dedicated
    workers are Lean sessions with their own realm and heap, "interleaved on one thread,
    deterministically". Reason recorded: "the engine is a pure Lean value per session; one thread
    ... works the same in the Wasm engine, which has no threads"
    (`2026-11-09-dedicated-workers.md`, "Why not a real thread first"). Section 3b of the
    2026-11-24 record says dedicated workers "can move to their own threads in the same way".
    Target: native desktop and Hub. Replacement: `IO.asTask` per worker on native only. Lost:
    determinism of the order of tasks, on which the `EventLoop.Agents` theorems rest; the Hub
    behaviour (no threads) would then differ from native. Measure first: script turn time and
    input latency of a page with workers (`workers_test.ts` pages; `--perf-summary`
    script-turn fields); the cost of one `pump`.

20. `formal/lean4/Harness/WorkerPool.lean:142` (`IO.asTask ... Task.Priority.dedicated`), with
    `IO.Promise` at lines 94 and 65. A per-session worker pool for the SBM11 harness. Native
    Lean already. Reason: a parked Lean pool thread starts 50 to 120 microseconds after wake-up
    (header). Target: native CI tool and server. No change. Measure: `l4pool-bench`
    (`Harness/WorkerPoolBench.lean`).

21. `formal/lean4/L4Factoidal/Par/Chunked.lean:32` and
    `formal/lean4/L4Factoidal/Storage/Sbm11/ParallelJoin.lean:135` (`Task.spawn`). Native Lean
    already. Wasm runs the task at once on the calling thread, with the same result
    (`Par.mapChunks_eq`). The native host sizes Lean's pool in
    `labs/demos/foafnaut/web_render_shim.c:31-53` (`FOAFNAUT_LEAN_THREADS`, at most 6). No change.
    Measure: engine p50 in `--perf-summary`; `FOAFNAUT_LEAN_THREADS=0` against default.

22. `formal/lean4/Harness/XmppServe.lean:154` (`Std.Mutex`) and `:406` (`IO.asTask`
    `pollMailbox`); `formal/lean4/Harness/Sbm11Query.lean` (`Std.Mutex`, `IO.Promise`,
    `IO.asTask` at lines 201-205, 541, 832-841). Native Lean already. No change.

23. `formal/lean4/L4Factoidal/XProc31/ProcessSteps.lean:15-17` and `Runner.lean:379` use
    `IO.Process.spawn` with `IO.asTask` dedicated for pipes. `L4Factoidal/Rendering/LeanFontShape.lean:40`
    uses `IO.Process.output` to call the native `font-shape` helper (HarfBuzz) as a differential
    oracle. `Harness/ProtocolLive.lean:96` spawns a child. `WasmVM/Bench/QuickJS.lean:292`,
    `Bench/HarfBuzz.lean:100` and `Bench/Test262.lean:42` spawn reference engines for comparison.
    Native Lean already. No change.

24. `formal/lean4/L4Factoidal/Paralliverse/*` with `Wasm/build-paralliverse.sh` (a separate Hub
    CPU module) and `docs/web/hub/paralliverse/worker.mjs`. The Lean library is pure; the Hub
    runs it in rows 10's worker, one wasm per worker. Native: `Par.mapChunks` is available.
    Target: Hub and native. Measure: "ProgramCPU for every program and every worker count"
    (2026-11-24 record, section 1a).

### E. Emscripten

Emscripten is the compiler that makes wasm. It is not a run-time on native builds. Native builds
use `leanc`/Lake. So a "native replacement" applies to the run-time worker around the wasm, not to
`emcc`.

25. `formal/lean4/Wasm/build-wasm.sh:88-90, 264, 278` (flags `-DLEAN_EMSCRIPTEN -fwasm-exceptions`,
    no `-pthread`). Builds the one Lean wasm for the Hub and npm. Reason: GitHub Pages cannot send
    COOP and COEP. Target: wasm Hub, npm/Node. Replacement: none; this is the wasm target.
    Measure: not a candidate. If threads in wasm are wanted, measure `wasm threads` as a
    separate proposal (needs cross-origin isolation).

26. `tools/lean-wasm-exe.sh:12-42`: builds a wasm executable "from the SAME generated C as the
    native executable, by emcc". Target: CI tool (wasm test of CLI). Replacement: none. Not a
    candidate.

27. `tools/deploy/build-units.py:29-71` and `tools/deploy/plan-units.mjs`: split the wasm into
    units with cached `emcc`. Target: wasm Hub. Not a candidate.

28. `tools/wasmvm/build-quickjs.sh:71`, `build-harfbuzz.sh:50`, `build-media.sh:70`: compile
    QuickJS, HarfBuzz, Opus, Vorbis and VP8 to wasm. The Lean WasmVM
    (`formal/lean4/L4Factoidal/WasmVM/`) then runs them (HarfBuzz for font shaping, media decoders,
    the QuickJS guest). Here Lean already verifies and runs untrusted wasm without an Emscripten
    run-time: Emscripten is only the build step, "Emscripten 6.0.8 (/opt/homebrew/bin/emcc)"
    (`2026-11-07-wasmvm-engine.md`). Target: native desktop and Hub, CI tool. Replacement: none
    needed. Measure: the WasmVM benchmarks in that record ("Measurements" section).

29. `labs/demos/foafnaut/web_render_shim.c` (`__EMSCRIPTEN__` branch, line 53 starts the native
    task manager only outside Emscripten). Target: native desktop and wasm. Already native
    Lean tasks where threads exist. No change.

### F. CI and test tools

30. Many `labs/demos/foafnaut/hub_*_check.mjs` scripts (for example `hub_cpu_check.mjs:50`,
    `hub_net_check.mjs:68`) start headless Chrome with `node:child_process` `spawn`;
    `labs/demos/foafnaut/realpages/survey.ts:72` and `snapshot.ts:64` start Deno or Chrome with
    `Deno.Command`; `labs/demos/foafnaut/{spinal_bisect,pipeline_trace_check,gpu_kernel_diff,
    realpages_check,native_net_window_check,daily_use_check}.ts` start Deno children; `npm/*/test/*`
    and `deploy/lws-replica/*.test.mjs` start CLI children and `openssl`, `caddy`, `npm`.
    Reason: they drive an outside program (Chrome, Deno, openssl) and measure it. Target: CI tool.
    Replacement: `IO.Process.spawn` is possible only for a Lean-written driver; no gain. Not
    candidates.

31. Test workers: `tests/browser-wpt/testharness-run.ts:212`, `tests/store-http/r2-open-profile.mjs:29`,
    `tools/wasmvm/quickjs/host-reference.mjs:18`, `labs/demos/foafnaut/workers_test.ts`,
    `labs/demos/foafnaut/origin_isolation_test.ts:259`, `labs/demos/foafnaut/web-render/tests/*`,
    `npm/factoidal/test/*` (rows `new Worker(` in test code). They test the worker paths above,
    or the page `Worker` API of the page-script engine. Not candidates.

### G. Plugins and untrusted wasm

32. No design record on plugins or on verifying plugins exists. `grep -rilE plugin docs/designissues`
    finds `2026-07-05-docs-hub-plan.md`, `2026-11-14-input-webdriver.md`, `2026-11-14-dom-html.md`
    (about browser plugin APIs, not our plugin system) and the 2026-11-24 record, which quotes
    the owner line only. What exists for untrusted wasm: the Lean WasmVM (row 28), the font
    policy that refuses the `Wasm` OpenType table until that engine exists
    (https://github.com/danbri/factoidal/issues/1244, CLAUDE.md, 2026-11-03 and 2026-11-05), and
    `Net` and origin isolation (`2026-11-16-origin-isolation.md`, which says one process holds all
    origins of a page, theorem T3). No path found that a Lean `IO.Process.spawn` child would
    replace. The question of a plugin isolation design (a process per plugin) is not answered by
    any record. Undecided; see "Could not decide".

## Candidates

A Candidate is a row where a native Lean replacement looks possible. None is proved to lose
nothing. Each needs the measurement in its row first.

- Row 1: engine worker per tab on native desktop as a Lean task per tab, after the engine state
  is made per session. Conditional: the loaded-copy rule, Deno-owned termination.
- Row 19: page dedicated workers as `IO.asTask` on native. Conditional: gives up deterministic
  interleaving unless the model is shown to hold for the threaded form.
- Rows 20 to 23 and 29: already native Lean (tasks, promises, mutexes, `IO.Process`). Nothing to
  replace. They are the base the two candidates would use.

## Keep

- Rows 2, 3, 7 to 14, 25 to 27: Hub and wasm. No threads in the wasm runtime. A Web Worker is the
  only parallelism and the only way to terminate synchronous wasm.
- Row 4 (Tor worker): isolation by Deno permissions, and the code is Rust (Arti).
- Rows 5 and 6: child processes that already run a Lean or Node program in their own process. A
  Lean replacement gains nothing while the host is Deno.
- Rows 15 to 18: npm and Node. The wasm engine needs a large stack, a synchronous host call, or
  a worker that owns its store handle. Native Lean builds have their own stack setting.
- Row 28: Emscripten is the compiler for guest wasm that the Lean WasmVM runs. No replacement for
  a C or C++ to wasm compiler.
- Rows 30 and 31: test drivers of outside programs.

## Could not decide

- Whether the engine state held in the native library per loaded copy (rows 1) can be made per
  session without a change to `web_render_shim.c` and its Lean state. The record names the
  constraint but not the cause. A read of the shim and the Lean engine is the next step.
- Whether `Task.Priority.dedicated` threads can run a long engine call that must be stopped on a
  deadline. A Lean task cannot be killed. Row 2 shows why this is needed on the Hub.
- Whether a plugin isolation design is wanted (row 32). No record says so.
- The size of the Emscripten uses in files the word list does not name (see Method).
