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

(Stages 2 to 4, their measurements and further decisions are added below as they land.)
