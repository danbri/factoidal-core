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
document state. This removes two `unsafe`, two `@[implemented_by]`, one `opaque` and three
`initialize` cells from the lab.

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

(Measurements and stage 4 are added below as they land.)
