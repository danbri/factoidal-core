# Foafnaut engine sessions: one library, one engine state per tab (2026-11-26)

Tracking: https://github.com/danbri/factoidal-core/issues/1031 (threads, tabs, processes, DNS and
HTTP). Row 1 of `2026-11-25-lean-native-concurrency-audit.md` is this work. Section 3 of
`2026-11-24-foafnaut-concurrency-and-network.md` has the baseline it starts from (one engine
worker per tab, each with its own copy of the native library: about 130 MB for each extra worker,
worker start 236 ms median, on the Linux rig).

Owner brief for the night of 2026-11-25, in short: find all global engine state; give each tab
an engine session in one loaded library; run each session on its own Lean dedicated task with a
request queue; make a runaway page stoppable; measure each stage against a build of the same
base, and land a stage as the default only if it measures better.

Branch: `wip/engine-sessions`, from `origin/main` `1553ce0b`.

## 1. Inventory: global state of the native engine (stage 1)

Read on `1553ce0b`. Method: the C files that `build-web-render.sh --native` links
(`web_render_shim.c`, `formal/lean4/ffi/hacl_webcrypto.c`, the HACL\* units), and a walk of the
import closure of the engine (the `CORE` and `LAB_MODULES` lists of `build-web-render.sh`, 642
modules) for `initialize`, `builtin_initialize`, `unsafeBaseIO`, `unsafeIO`, `@[extern`,
`Task.spawn`, `IO.asTask`, `IO.Promise` and `Std.Mutex`. The Lean runtime parts are read from the
Lean 4.33.1 sources (`src/runtime/thread.cpp`, `object.cpp`, `io.cpp`, `stack_overflow.cpp`).
What the method cannot see: state inside `Init` and `Std` that the walk does not cover (only
`L4Factoidal` and lab modules were read), and global state that a C library keeps behind a call
the engine makes (none found in the HACL\* units, which keep no static data).

### 1a. The C shim (`labs/demos/foafnaut/web_render_shim.c`)

1. `web_render_shim.c:15` `static lean_object *engine`: the one engine state of the library
   (`WebDocument.Engine`, issue 390). Every call that keeps state passes it and takes the next
   state back (`next_state`, line 17). This is why a second tab needs a second copy of the
   library file today (`native_html_tabs.ts:100-101`).
2. `web_render_shim.c:47-64` `ready()`: starts the Lean runtime, the task manager and the
   module initialisers once, and makes `engine`. The flag `initialized` (line 48) is a plain
   `static int`: two threads that call first at the same time both start the runtime. Today only
   one thread calls each loaded copy, so this does not happen.
3. `web_render_shim.c:31-45, 53` `pool_size()`, `pool_threads`: the size of Lean's task pool,
   one per process (`FOAFNAUT_LEAN_THREADS`, at most 6). With 0, there is no task manager, and
   every `Task.spawn` runs at once on the calling thread.

### 1b. Lean state that outlives a call

4. `WebDocument.lean:281` `initialize shapedKept`: words shaped outside the font memo, by font
   key, text, size and direction, at most 16,384 (then the table starts again). Written by
   `shapeKeptImpl` (line 283, `unsafe`, `unsafeBaseIO`), the implementation of `shapeKept`
   (line 297). The value is a pure function of its key (`SfntProfile.shapeFresh`), so a table
   shared by sessions gives the same answers. Its `get` and `modify` are of one family of ref
   operations (exchange with null, then put back), so two threads can not lose each other's
   writes (`skills/lean4-performance`, "Values that two threads can reach"). Cost to measure:
   the ref is a global, so its table is marked multi-threaded and every insert copies the bucket
   array.
5. `WebDocument.lean:1616` `initialize keptPageRef`: the last two page layer answers
   (`KeptPage`, with the scene, boxes, face, answer and retained layer). Read and written by
   `pageArtifactImpl` (line 1644, `unsafe`), the implementation of `pageArtifact` (line 1715).
   It is per document state: with two tabs in one library, the tabs take each other's slots, and
   the retained compile of one tab uses the other tab's last layer as its base. That base is
   only a reuse hint (leaves are reused by object identity or by `WebPaint.samePrimitive`), and
   its `damage.base` number never matches the host's own, so answers stay correct; the cost is
   lost reuse. Two threads that use it at once mix `get` with `set`, which can lose a write.
6. `WebDocument.lean:1619` `initialize pageWorkRef`: counts of page layers made and kept, read
   by op `frameWork` through `pageWork` (line 1630, `opaque`, `unsafe` implementation at line
   1624). Per document.
7. `WebDocument.lean:1621` `initialize pageIdRef`: the answer number of `damage.id`. Per
   document.
8. `formal/lean4/L4Factoidal/XSD11/Load.lean:81` `initialize schemaCache`: XML schemas read
   from files, once per process (`loadSchemaCached`). A memo of files; `get` and `modify` only.
   The page engine does not read schemas from files; it is in the closure through the XSLT and
   XPath modules.

No other `initialize` or `builtin_initialize` is in the closure (the third one in the formal
tree, `WasmVM/Bench/Sample.lean:30`, is not in it). The lab's three `unsafe` and three
`@[implemented_by]` declarations (the `baseline` of `LabHygiene.lean`) are items 4 to 6.

### 1c. C code linked into the library

9. `formal/lean4/ffi/hacl_webcrypto.c:388` `static uint64_t l4w_wiped_total`: bytes zeroed by
   `wipe` (`Crypto/WebHacl.lean:446`), for tests (`wipedSoFar`, line 449). A plain `+=` from two
   threads is a data race. The HACL\* units keep no static state.

### 1d. The engine state that is already a value

10. `WebDocument.lean:3563` `structure Engine`: held fonts, web fonts and images (`Holds`,
    line 1773; the "held font" of the frame pipeline record is `holds.font`), script sessions
    (`WebScripts.Held`: the QuickJS guest module, the page's script session, the BubblePopJS
    realm), the layout memo, painted frames, kept trees and sheets, subresource transfers, frame
    counts, accessibility regions. It is an ordinary Lean value; nothing in it is global.
    Two engines in one process do not share any of it.

### 1e. Lean runtime state of the process

11. The task manager (`lean_init_task_manager_using`, `object.cpp`): one per process. Its pool
    runs the engine's `Task.spawn` work: `L4Factoidal/Par/Chunked.lean:32` (used by the SVG
    tile listing, `SVG.lean:3683`; image decode, `WebRender.lean:535`; word shaping,
    `WebDocument.lean:2636`, `SfntProfile.rememberPar`), `WasmVM/Binary/Decode.lean:612` and
    `WasmVM/Valid.lean:1245`. A dedicated task (`Task.Priority.dedicated`) gets a thread of its
    own outside the pool (`spawn_dedicated_worker`), with Lean's thread stack size (1 GB
    reserved on 64-bit, `LEAN_DEFAULT_THREAD_STACK_SIZE` in `thread.cpp`) and the stack
    information that the overflow check reads.
12. Threads that Lean did not start: `lean_initialize_thread` is empty in Lean 4.33.1
    (`thread.cpp:54`). Objects are allocated by mimalloc (`LEAN_MIMALLOC`, `lean.h:484`), which
    makes a heap for each thread on its first allocation and takes frees from other threads.
    So a Deno thread may call the engine with no set-up. `lean_finalize_thread` runs the thread
    finalisers; the engine registers none.
13. Persistent objects: the values of closed terms and of `initialize` declarations, made by the
    module initialisers in `ready()` and marked persistent. Their reference counts are not
    changed, so threads share them with no cost. They include large data such as the
    BubblePopJS realm (`LeanJSRealmData.lean`, made by `build-web-render.sh`). Each copy of the
    library makes all of them again today.
14. A ref that a global reaches, or that a task closure reaches, is multi-threaded: values put
    in it are marked multi-threaded, and are then copied on each change, never changed in place
    (`io.cpp`, `ref_maybe_mt`; `skills/lean4-performance`).
15. The stack overflow handler (`stack_overflow.cpp`): installed only when the signal action is
    the default one. Deno 2.9.4 catches SIGSEGV and SIGBUS before it loads the library (read
    from `SigCgt` in `/proc/self/status` on Linux), so in the desktop host Lean installs
    nothing. The check reads the stack of the current thread, so it is not per library copy.

### 1f. What the host assumes

16. `native_html_engine.ts:153`: "Every call must come from one thread; no nonblocking FFI."
17. `native_html_tabs.ts:95-104`: each worker after the first copies the library file, so that
    it has its own `engine` (item 1).
18. `native_html_worker.ts`: the worker holds the engine and runs one call at a time; a Lean
    call can not be stopped.

### 1g. What a Deno worker costs without an engine

Measured 2026-11-26 on the Linux cloud VM (4 vCPU), one process, six workers started in a row,
each importing `native_html_engine.ts`, `native_html_fonts.ts` and `native_html_queue.ts` and
loading no engine: 11.6 MB of resident memory and 26 to 48 ms of start for each worker. With the
Wasm engine loaded in each worker the cost was about 77 MB and 324 to 470 ms each. So most of the
130 MB of an extra worker of the native path is the library copy and its engine, not the worker.

## 2. Decisions

D1. A session is the engine state of one tab: `web_session_new` makes one, `web_session_free`
ends it, and each call that keeps state takes the session (`web_session_*`). The library is
loaded once. The old calls stay, on a session of their own, for the Wasm build and for hosts
that do not know sessions. Reason: item 1 is the only C global; the Lean engine is already a
value (item 10).

D2. Items 5 to 7 become fields of `Engine`, so each session has its own. Reason: they are per
document state. Measured by the lab hygiene count (`LabHygiene.lean`, builds of the base and
of the branch): `unsafe` 3 to 2, `@[implemented_by]` 3 to 2, `opaque` 5 to 1 (the three
`initialize` cells and `pageWork` are gone). Until 2026-11-26 this line said "two `unsafe`, two
`@[implemented_by]`, one `opaque`", written before the build.

D3. Item 4 stays one table for the process, shared by all sessions. Reason: its values are a
pure function of the key, so sharing gives the same answers, and its ref operations are of one
family. Its cost (item 14) is measured separately; moving it into `Engine` needs the layout to
take it as state, which is a larger change in `Rendering.Layout`.

D4. Item 8 stays: a memo of files, ref operations of one family, not on the page path.

D5. Item 9 becomes an atomic add.

D6. `ready()` runs once for the process (`pthread_once`).

## 3. Stage 2: engine sessions in one library

What was built (`wip/engine-sessions`):

- C shim (`web_render_shim.c`): a `web_session` holds an engine value and a mutex.
  `web_session_new` and `web_session_free` make and end one; `web_session_call`,
  `web_session_call_bin`, `web_session_font_call_bin`, `web_session_image_call_bin` and
  `web_session_hit` take it. The calls with no session argument use a default session made at
  start, so the Wasm build and the tests that call the old exports are unchanged. The
  runtime, the task pool and the module initialisers start once (`pthread_once`).
- Lean: `WebDocument.KeptPages` is the field `Engine.pages`; `pageArtifact` and `layersJSON`
  take it and give the next one; op `frameWork` reads its counts.
- Host: `--engine-mode sessions` (run_html.ts): one engine worker per tab, as before, but every
  worker opens the one library and makes an engine session of its own; no copy of the library
  file. A library from before sessions falls back to copies. `--engine-mode copies` is the mode
  of 2026-11-25. `native_html_worker.ts` takes `end`: it drops the calls that have not started,
  frees its session after the call in progress, and closes.

Why sessions on two threads are safe, and what that rests on:

1. One thread at a time touches an engine value: a session's calls hold its mutex. A value that
   a later call takes on another thread is ordered after the earlier call by that mutex
   (release, then acquire), so its non-atomic reference counts are changed by one thread at a
   time.
2. What sessions share: persistent constants (their counts are never changed); the shaped-word
   table and the schema memo (items 4 and 8: their values are multi-threaded, with atomic
   counts, and each ref is used with one family of operations); the task pool (its own locks);
   mimalloc (a heap per thread, and frees from other threads).
3. C state: the start-up (`pthread_once`) and the wipe counter (atomic).
4. Trusted, not shown here: Lean's runtime in C and C++ under concurrent use, the C compiler, and
   that the walk of section 1 found all global state (it did not read `Init` and `Std`).
   `engine_sessions_test.ts` runs three sessions on three threads and compares every answer
   with one session alone, byte for byte: a race would show as a different answer or a crash.
   A pass does not show that there is none.

## 4. Stage 3: a session on its own Lean task

What was built:

- `WebSession.lean`: a `Session` is an inbox (`IO.Ref (Array Job)`), a wake promise
  (`IO.Ref (Option (IO.Promise Unit))`), a closing flag and a count of calls answered. `start`
  runs `serve` with `IO.asTask` at `Task.Priority.dedicated`: a thread of its own, outside the
  task pool, with Lean's thread stack. `serve` makes the engine value itself and keeps it, so it
  is never shared between threads (a value that two threads can reach is marked multi-threaded
  and copied on every change). A caller (`call`) adds a job with a promise, wakes the task, and
  waits for the promise. `close` sets the flag; the task answers the jobs it has and ends.
- No lost wake-up: `serve` finds the inbox empty, publishes a new wake promise, then looks at
  the inbox and the flag again before it waits. A job or a `close` that came before the
  promise was published is seen by the second look; one that comes after it takes the
  promise and resolves it. Each ref is used only with `modify` and `modifyGet`, which exclude
  each other; `get` or `set` beside them can lose a write (`skills/lean4-performance`).
- C shim: `web_session_new_task` makes a session whose calls go to its task (NULL in the Wasm
  build, and with no task pool, `FOAFNAUT_LEAN_THREADS=0`, where a task would run on the
  calling thread and never return); `web_session_close` stops it taking calls. The same
  `web_session_*` calls submit to the task and wait on the calling thread.
- Host: `--engine-mode tasks`: no engine worker. Each tab's client (`native_engine_tasks.ts`)
  keeps the lanes of the engine worker (gesture, input, ordinary, low) and one call of the
  session in flight, and calls through Deno's nonblocking FFI (`loadHTMLSession` in
  `native_html_engine.ts`). A library with no task sessions falls back to `sessions`.
- The remote engine calls are written once (`remoteMethods` over a small kernel), for the
  engine on the calling thread and for the session engine, so the two can not read an answer
  differently. The synchronous engine gives the same answers as before the change on 22
  calls (Wasm engine, a differential run on 2026-11-26).

D7. How the host waits: Deno's nonblocking FFI. Deno runs the call on a thread of its blocking
pool, which waits for the task's answer, and resolves a promise on the main thread's event
loop. Reasons: it needs no polling (a polled completion queue adds up to one loop period to
each answer, and the loop sleeps up to 100 ms when idle), no call from a Lean thread into
JavaScript (a callback needs an `@[extern]` or a C thread that waits, and the lab's `extern`
count may not rise without the owner), and no engine worker. A call waits on a pool thread,
not on a Lean thread: the session's own thread runs the engine.

D8. Lanes stay in TypeScript, per session, with one call in flight. Reason: the order rules
(gesture first, input before ordinary, one low request that a newer one replaces) are those of
`native_html_queue.ts`, tested by `native_html_queue_test.ts`; moving them into Lean is a
separate change. The Lean inbox takes any number of calls in arrival order.

D9. On the main thread now, and in the worker before: the checks and the JSON text of each
request, the reading of each answer, and the fallback-font choice of a page with characters
above ASCII (`font-coverage.mjs` reads every character of the source). This is measured as
the main thread's pump gap and as input latency (section 5).

## 4a. Stage 4: stopping a session

Built: `WebWasm.Machine.canceled` (in the engine, `IO.checkCanceled`: the cancellation of the
Lean task that runs the call; never on a thread that Lean did not start, never in `Id`). A
render checks it before its layout and again before its paint (`WebDocument.answerWith`), and
throws "engine call canceled". `WebSession.cancel` (C `web_session_cancel`) closes the session
and cancels its task (`IO.cancel`); `serve` refuses each call it has not started once its task is
canceled; when `serve` ends it takes the inbox away (`none`) and refuses what was left in it,
so no caller waits for good. The task client (`native_engine_tasks.ts`) cancels its session when
its tab is closed, then frees it when no call is in flight.

What a cancel guarantees, for a task session:

1. No call of the session starts after the cancel: a call not started is answered with an error
   at once.
2. The call in progress stops at its next check (before its layout, or after it and before its
   paint) and answers an error.
3. Other sessions are not changed: each has its own task, inbox and state.
4. The session's engine state is dropped (its task ends): a canceled tab needs a new session.

What it does not do:

- Stop a layout in progress: the layout is one pure function, so it runs to its end. Its time
  is bounded by the page's size and the engine's limits (16 MiB of source, `maxSourceBytes`),
  not by the cancel. Expected failure and issue:
  https://github.com/danbri/factoidal-core/issues/1135.
- Stop a page script within one slice: a BubblePopJS turn is bounded by the step budget the host
  gives (`sliceSteps`), and the host stops sending turns; the check is between calls.
- Anything for direct sessions (per-tab workers, `--engine-mode sessions` and `copies`): a
  worker's call runs to its end, as before; ending the worker frees the session after it.

Script isolation is unchanged: page scripts run in BubblePopJS (a value of the session) or in
QuickJS-NG inside WasmVM; the Tor client stays in its Deno worker with narrow permissions.

D10. One build carries stages 2 to 4. Each stage is measured by its own mode in one run of one
build (`copies` is the base behaviour, `sessions` is stage 2, `tasks` is stages 3 and 4), against
a build of the base. Reason: a native build takes about 20 minutes on this machine, and modes of
one build compared in one run share every other variable.

## 5. Measurement method

Command (repeatable, no person needed): `labs/demos/foafnaut/tools/engine_sessions_bench.py`
with one `--config NAME=LAB:ENGINE[:MODE]` for each side. Each scenario runs N times for each
configuration, the configurations interleaved, each run under
`flock /tmp/foafnaut-timing.lock`, in a window under Xvfb with Mesa software Vulkan (the Linux
rig, `tools/foafnaut-linux-rig/setup.sh`). Both sides are local builds of one base,
`origin/main` `1553ce0b`: the base in a second worktree with its own host, the branch in this
checkout, built on the same machine with the same flags (`build-web-render.sh --native`,
ccache). The Wasm engine of the main thread (small calls) is the released one for both sides.

Scenarios: `heavy` (tab A navigates to a page of 20,000 table rows, 2.4 MB; 300 ms later tab B
opens and gets 21 keys 150 ms apart from each other's text event, each a key press that the host
stamps and its text into the address field), `tabs` (seven new tabs 1 s apart), `one` (the start
page only, the memory base for `tabs`), `status` (`pages/status.html`, the resize sweep: seven
Lean frames), `rex` (`pages/particle-rex.html` for 8 s). Numbers: input latency from the host's
stamp (event queued) to the frame presented (`native-html-input-latency`), tab first frame
(`native-html-tab-first-frame`: tab shown to its first frame presented), process resident memory
at exit, engine start (`native-html-engine-worker`, `ms` less `warmMs`), frame total.

Evidence limits: Linux only (no Mac was available); software Vulkan draws a frame in 300 to 600
ms, so frame and latency numbers include that draw and are not comparable with a Mac; a 4-vCPU
cloud machine with other tenants.

## 6. Measured (2026-11-26, one run of the command above)

Machine: Linux cloud VM, 4 vCPU, Xvfb, Mesa software Vulkan. Base: a local build of
`origin/main` `1553ce0b` with its own host (worktree). Branch: a local build of
`wip/engine-sessions` `578f74a8` (the Lean and C of stages 2 to 4), host at `0ba44e22`.
5 runs per configuration, interleaved, each under the timing lock. Median, worst run in
brackets, coefficient of variation (CV) where it matters. `copies` is the branch in the base's
mode: its numbers are the control for the base.

| Number | base | copies | sessions | tasks |
|---|---|---|---|---|
| Tab B input latency p50, tab A loading 2.4 MB, ms | 398 (417) | 392 (397) | 387 (399) | 371 (391) |
| Tab B input latency p95, same, ms | 1,324 (1,367) | 1,367 (1,401) | 1,151 (1,184) | 1,059 (1,178) |
| Tab B first frame, tab A loading, ms | 1,406 (1,509) | 1,213 (1,400) | 1,443 (1,467) | 1,346 (1,444) |
| New tab first frame p50, 7 new tabs, ms | 746 (920) | 703 (763) | 634 (800) | 641 (845) |
| New tab first frame p95, 7 new tabs, ms | 984 (1,015) | 991 (1,002) | 922 (997) | 874 (971) |
| Engine start, per extra engine, ms | 127 (129) | 143 (149) | 43 (49) | 4.2 (4.5) |
| Resident memory added by an engine start, MB | 105 (146) | 107 (119) | 28 (47) | 1.1 (4.5) |
| Process resident memory at exit, 8 tabs, MB | 1,481 (1,505) | 1,463 (1,505) | 1,008 (1,051) | 808 (834) |
| Process resident memory at exit, 1 tab, MB | 771 (787) | 779 (799) | 717 (721) | 662 (667) |
| Resident memory per extra tab, MB | 101 | 98 | 42 | 21 |
| Frame total p50, status.html resize sweep, ms | 691 (751) | 658 (700) | 654 (704) | 677 (746) |
| Frame total p95, same, ms | 2,812 (2,986) | 2,740 (2,876) | 2,719 (2,923) | 2,640 (2,989) |
| Timer turns in 8 s, particle-rex.html | 99 (102) | 97 (101) | 93 (99) | 98 (101) |
| Engine time per timer turn p50, same, ms | 61 (65) | 62 (66) | 66 (72) | 62 (65) |
| Call beyond the engine per turn p50, same, ms | 7.1 (7.9) | 7.3 (7.5) | 7.7 (8.0) | 5.3 (5.4) |
| Page canvas present p50, same, ms | 7.1 (7.4) | 7.1 (7.2) | 7.1 (7.4) | 7.3 (7.5) |
| Main thread pump gap p95, heavy, ms | 234 (241) | 234 (236) | 232 (238) | 234 (243) |

Resident memory per extra tab is (8 tabs - 1 tab) / 7 of the medians. The Particle Rex rows
are from a second run of that scenario only (the first run's driver did not read the timer turn
and canvas fields); its other numbers agreed with the first run.

Reading (tasks against base): memory per extra tab 21 against 101 MB (CV about 0.02), engine
start 4.2 against 127 ms, tab B input latency p50 371 against 398 ms (CV 0.022 and 0.024) and
p95 1,059 against 1,324 ms (CV 0.06 and 0.07). The two new tab first frame rows of the table
are withdrawn: see the correction below. Frames: status.html p50 677 against 691 ms (CV 0.06 both), Particle
Rex turns 98 against 99 and canvas present p50 7.3 against 7.1 ms (CV 0.016 and 0.024): no
change beyond the spread. The call beyond the engine per timer turn falls by 1.8 ms: no worker
message each way.

Correction, 2026-11-26, found in the confirmation run (section 6a): the two new tab first frame
rows count only the tabs that drew before the next tab opened, 1 s later. `run_html.ts` times one
shown tab (`tabShown`); a newer tab replaces it, so a tab slower than about 1 s is not counted.
Tabs counted in this run: base 19 of 35, copies 20, sessions 24, tasks 27. The rows compare
different sets of tabs, and the mode with more slow tabs looks faster. Until this correction,
this section and the first report said "new tab first frame p95 874 against 984 ms" as a gain.
The count itself is a measure: the new tabs that drew before the next one opened, 1 s later
(the last tab of a run always counts), 27 of 35 (tasks) against 19 of 35 (base). Section 6a measures every tab (tabs 3 s apart:
`tabs-spaced` in `engine_sessions_bench.py`).

Checks on the branch library: `engine_sessions_test.ts` 7 of 7 pass and its expected failure
(https://github.com/danbri/factoidal-core/issues/1135) is recorded; the 28 demo pages of
`pages/manifest.json` give the same bytes from the base and the branch library (a frame, a
scrolled frame, both layers, and the page layer kept for a chrome-only frame, 1600 by 1200,
text 150 percent), with equal `frameWork` counts (28 pages made, 28 kept). A short call on
tab B was answered in 25 ms while tab A's 1.8 s layout ran (test 5).

D11. The default stays `--engine-mode copies` (a worker and a library copy per tab); `tasks` and
`sessions` are options. Rule, from the owner's brief for the night of 2026-11-25: "Changing the
default from workers to Lean tasks: land it as default only if it measures better on
tabFirstFrame, memory per tab and tab-B input latency with no frame regression; otherwise land it
behind a flag and report." Against the `main` it lands on (`7285ab37`, section 6b), `tasks` is
better on memory per tab (23 against 109 MB) and engine start (4.5 against 165 ms), but not on
the first frame of a tab: with every new tab counted, p50 565 against 560 ms and p95 1,369
against 1,269 ms (worse in each of 3 runs), and the first frame of tab B while tab A loads a large
page 1,424 against 1,122 ms; tab B input latency p50 360 against 372 ms but p95 1,187 against
1,135 ms. History of this decision: on 2026-11-26 it first said `tasks` was the default, on the
numbers of section 6, whose new tab rows counted only fast tabs (withdrawn, see the correction
there); section 6a (against `b7286ac7`) showed the new tab gain only at p50; section 6b shows
none, against a `main` whose own frames had become faster. Why `tasks` gives later first frames
is not known; a check with a larger Lean task pool (6 threads; the sessions share one pool, a
library copy has its own) did not remove it (section 6b).

D12. The library pins itself (`RTLD_NODELETE`) before its first task session starts
(`pin_once` in `web_render_shim.c`), and makes no task session when it can not. Reason: a
session's task runs on a thread of its own, which the host can not stop or wait for, so a
`dlclose` of the last handle would unload code that the thread still runs. Deno closes its
library handles when its runtime ends. Seen 2026-11-26 on the first full `test.sh` run after the
build: `engine_sessions_test.ts` passed its 8 tests and then ended with a segmentation fault (exit
139) on every run, 6 of 6. gdb: a session task thread in `lean_dec_ref_cold` (freeing its engine
state at the end of `WebSession.serve`) while a Deno thread was in `_dl_close_worker`. With the
pin: 20 of 20 runs exit 0. The worker modes (`copies`, `sessions`) are unchanged: they start no
task session, so their libraries are not pinned and a closed tab's copy is still unloaded.

### 6a. After the rebase onto `main` `b7286ac7`

71 commits reached `main` during the night. Two of them (issue
https://github.com/danbri/factoidal-core/issues/1124, stages A and B) changed the state this work
moves into sessions: a kept page layer has a `layoutOff` flag, `Engine` has kept chrome layers,
kept answers with no layers and kept layout sections, and a layers answer can carry its boxes,
glyph runs and links as binary sections. The merge keeps all of these in `Engine` (per session)
and `Engine.pages` for the kept page layers. In the host, the layout sections of a bytes answer are
placed by one function (`placedAnswer`) for the engine on this thread and for a task session, and
`compileLayers` asks for them through the shared `remoteMethods` (`Kernel.layoutSections`).

The merged build: the Lean and C of `wip/engine-sessions` on `b7286ac7`. The build process was
stopped by a tool time limit after it linked `web-render-native` and before the library; the
library was then linked by the script's own link command from that build's 665 objects, and the
script's last two steps ran (`check-budget.mjs`: `default.html` and `status.html` pass;
`write-witness.py`). Hygiene counts of that build: lab 55 modules, 2 unsafe, 2 implemented_by, 1
partial def, 0 extern, 1 opaque.

On the merged library: `engine_sessions_test.ts` 9 of 9 on 3 runs, each exit 0 (test 9 is new: a
task session's layers answer decodes to the same boxes, glyph runs, links, pixel data, tile words
and layer places as the engine on this thread); `layout_sections_test.ts` (issue 1124) 2 of 2,
directly and through an engine worker.

Byte comparison against a build of `main` `b7286ac7` (same machine, its own lab tree), through the
merged host code, on the 28 HTML demo pages of `pages/manifest.json` that the app does not refuse:
a frame, a scrolled frame, and two layers answers (the second kept the page layer), 1600 by 1200,
text 150 percent, with the decoded layout sections of each layers answer. `main`'s library
against the merged library on this thread: 28 of 28 the same. The merged library on this thread
against the same library through a task session (`loadHTMLSession`): 28 of 28 the same. The
`frameWork` counts of the three are equal (28 layouts, 84 kept, 38,939 primitives compiled, 28
page layers made, 28 given again). A first run of the task session showed 3 pages different
(the 3 with images): the harness had sent the pages' image loads to the engine on this thread
only. With them sent to the session as well (as the host does: `imageLoad`, `webFontLoad` and
`fontFaces` are remote calls of the tab's engine), all 28 are the same. Window screenshots (`--offscreen --shot`)
of the 3 pages with images from the host in `tasks` and `copies` mode are the same bytes.

Confirmation measurement against that build, with the command of section 5: `base` is
`main` `b7286ac7` with its own host (its default, a worker and a library copy per tab); `copies`
and `tasks` are the merged build. Median (worst run); 3 runs per mode, and 5 for `tabs-spaced`.

| Number | base | copies | tasks |
|---|---|---|---|
| New tab first frame p50, 7 tabs 3 s apart, every tab counted, ms | 631 (700) | 630 (685) | 596 (652) |
| New tab first frame p95, same, ms | 1,492 (1,744) | 1,602 (1,800) | 1,494 (1,823) |
| New tabs that drew before the next one opened, 7 tabs 1 s apart, of 21 | 11 | 11 | 15 |
| Resident memory per extra tab, MB | 99 | 103 | 17 |
| Engine start per extra engine, ms | 139 (141) | 134 (153) | 4.1 (4.3) |
| Tab B input latency p50, tab A loading 2.4 MB, ms | 388 (391) | 379 (390) | 377 (377) |
| Tab B input latency p95, same, ms | 1,369 (1,441) | 1,211 (1,358) | 1,150 (1,162) |
| Tab B first frame, tab A loading, ms | 1,379 (1,664) | 1,316 (1,427) | 1,553 (1,639) |
| Frame total p50, status.html resize sweep, ms | 632 (681) | 643 (677) | 656 (676) |
| Frame total p95, same, ms | 2,722 (2,927) | 2,873 (2,964) | 2,796 (2,810) |
| Timer turns in 8 s, particle-rex.html | 167 (168) | 170 (170) | 174 (177) |
| Page canvas present p50 and p95, same, ms | 6.9, 11 | 6.8, 11 | 7.0, 9.1 |

Spread: coefficient of variation of the new tab p50 0.069 (base) and 0.041 (tasks), of the p95
0.069 and 0.11; of the tab B input p95 0.078 and 0.05; of the status.html p50 0.037 and 0.03; of
the tab B first frame 0.12 and 0.075. Tab B first frame, tab A loading, over both runs (8 runs a
mode): median 1,393 ms (base) and 1,392 ms (tasks), the same. The new tab p50 gain (35 ms) is
smaller than one spread of the base at 5 runs.

Per tab, one run of each mode (`native-html-tab-first-frame`): the first new tab opens the start
page again (`index.html`, 2,791 primitives, a script session of 539 ms): 1,107 ms (base) and 1,041
ms (tasks); the second is the first `newtab.html` after start, with 1.27 s of layout: 1,615 and
1,592 ms; the third to seventh take 553 to 671 ms (base) and 546 to 600 ms (tasks). The p95 of
every mode is that second tab; why its first layout takes four times the later ones is not known
(it is not the engine start: a task session starts in 4 ms).

### 6b. After the rebase onto `main` `7285ab37`

22 more commits reached `main` while section 6a was measured. Stage C of issue
https://github.com/danbri/factoidal-core/issues/1124 lets the host name the page answer it holds
(`have:{page:id}`, the answer's `damage.id`); the engine keeps its last page answers whole
(`Engine.pagesSent`) and answers the page `{"kept":id}` or as a patch against that answer. The
merge keeps `pagesSent` in `Engine` beside `pages`, and `layersJSON` takes the session's kept page
layers and the held page and gives back both the new kept page layers and the answer to keep.

D13. The host names a held page answer only for the document on screen (`run_html.ts`: `have`
only when `current.document` is the frame's document). Reason: page answer ids are counted by
each engine (`KeptPages.lastId`; before this work, a cell per library copy), and in the modes
`copies`, `sessions` and `tasks` each tab has an engine of its own. After a tab switch the frame
on screen is the other tab's; its id can name a different page in this tab's engine, which then
answers it kept, and the host shows the other tab's page. Test 10 of `engine_sessions_test.ts`
checks the cause: the first page answers of two sessions have one id, and a session answers the
other's id as kept. This hazard came with stage C, before this work landed, and holds for the
`copies` mode as well.

`main` `7285ab37` did not build: `SVG.lean` line 3676, an application type mismatch, since commit
`f957d56f` (issue 1124): in namespace `NativeSVG` the bare name `LinearContour` is not
`NativeSVGPath.LinearContour`. The branch qualifies the two lines as the rest of the file does
(commit "Foafnaut SVG.lean: edgeYs takes NativeSVGPath.LinearContour"). The build of `main` for the
byte comparison has the same two-line change.

Tests of this build (the Lean and C of the branch on `7285ab37`, with the two `SVG.lean` lines):
`engine_sessions_test.ts` 10 of 10 on 3 runs, each exit 0; `layout_sections_test.ts` 3 of 3
(its stage C test: kept and patched page answers made whole equal the whole answers);
`test.sh --skip-build` 13 checks, 10 passed, 54 of 54 demo pages, the 3 failed as in section 6
(engine modules that need Emscripten, IPv6); the 26 pure test files one at a time, 19 passed, 7
can not load an engine module, none failed. Byte comparison as in section 6a against the build
of `main` `7285ab37`: `main` against the merged library 28 of 28 the same, the merged library on
this thread against a task session 28 of 28 the same, equal `frameWork` counts. Tab switch in the
host (three tabs: the start page, the start page again, the new tab page; then back to the first;
`main`, merged `tasks`, merged `copies`): each showed the start page again (2,791 primitives). The
ids did not meet in these runs, so the hazard of D13 was not seen end to end; test 10 shows it in
the engine.

Confirmation against the build of `main` `7285ab37` (with the two `SVG.lean` lines), 3 runs a
mode, median (worst): base is `main` with its own host (`copies`), tasks is the merged build.

| Number | base | tasks |
|---|---|---|
| New tab first frame p50, 7 tabs 3 s apart, every tab counted, ms | 560 (586) | 565 (574) |
| New tab first frame p95, same, ms | 1,269 (1,304) | 1,369 (1,447) |
| Tab B first frame, tab A loading 2.4 MB, ms | 1,122 (1,373) | 1,424 (2,052) |
| Tab B input latency p50, same, ms | 372 (376) | 360 (367) |
| Tab B input latency p95, same, ms | 1,135 (1,335) | 1,187 (2,072) |
| Resident memory per extra tab, MB | 109 | 23 |
| Engine start per extra engine, ms | 165 (170) | 4.5 (6.0) |
| Frame total p50, status.html resize sweep, ms | 611 (614) | 631 (636) |
| Timer turns in 8 s, particle-rex.html | 233 (236) | 246 (252) |
| Page canvas present p50 and p95, particle-rex.html, ms | 5.5, 7.0 | 5.5, 7.0 |

Single runs: new tab p95 base 1,235, 1,269 and 1,304 ms, tasks 1,341, 1,369 and 1,447 ms; tab B
first frame base 1,083, 1,122 and 1,373 ms, tasks 1,140, 1,424 and 2,052 ms. Against `b7286ac7`
(section 6a) `main` gave 1,492 ms new tab p95 and 1,379 ms tab B first frame: `main`'s own
frames became faster between the two, `tasks`' less. A check of the shared Lean task pool
(`tasks` with `FOAFNAUT_LEAN_THREADS=6`, 3 runs): tab B first frame 989, 1,548 and 1,589 ms, new
tab p95 1,312, 1,351 and 1,413 ms, so a larger pool did not bring them to `main`'s. These numbers
decide D11.

Evidence limits: Linux only; no Mac was available, so macOS (the product's main platform) is
not measured, and the macOS link (the exported symbol list) is not built here. Software Vulkan
frames dominate the latency numbers. The numbers above are of the library before D12; D12 adds
one `dlopen` call at the first task session and changes only whether the library can be
unloaded.

`labs/demos/foafnaut/test.sh --skip-build` on this machine, branch with D12: 13 checks, 9
passed, 4 failed. Passed: `engine_sessions_test.ts` (8 tests, the expected failure recorded),
`emoji_pixels_test.ts`, `gpu_kernel_diff.ts` (3 of 3 cases equal), and the coordinate, status
page, demo page source and Spinal Tap snapshot checks; `wasm/build.sh --check` and
`pipeline_trace_check.ts` pass by printing NOT RUN (no wabt here; the window library is macOS
only). Failed, and the same on the base build (`origin/main` `1553ce0b`, same machine):
`check-demo-pages.py`, 53 of 54 pages, `particle-rex.html` refused ("unsupported external HTML
stylesheet without supplied resource transport"); the `native_net` tests, 16 of 17, one server
can not listen on IPv6 here ("Address family not supported by protocol"). Failed because this
machine has no Emscripten, so `build-engines.sh` did not make `.build/engines/*.mjs`: `deno
check` and `deno test` of the pure tests as one run. Run one file at a time instead: 19 of the 26
pure test files pass on the branch and on the base; the other 7 can not load an engine module
(`foafnaut-engine.mjs`, `demos-engine.mjs` and five others), and none of those 7 imports a file
this work changed. `deno check` of `run_html.ts`, the changed modules, `engine_sessions_test.ts`
and the 19 files passes. NOT RUN here: `native_html_test.ts` and the other tests that need the
Wasm engine (Emscripten), the macOS window library or `lake build frame-cost-cases`. One run of
the browser with no `--engine-mode` option per scenario (tabs, heavy, rex), with the library of
D12, while `tasks` was the default (before D11 was changed, section 6b): each exits 0 in mode
`tasks`.
