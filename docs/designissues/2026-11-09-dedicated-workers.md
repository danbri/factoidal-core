# Dedicated workers in Foafnaut (2026-11-09)

Status: built on BubblePopJS (native engine). QuickJS-NG: off (`Worker` undefined).
Hub (Wasm engine): follows BubblePopJS on the Hub (the bpwasm work); the code is the same Lean.

## Why

Every WPT `.any.js` test also runs in a dedicated worker (`.any.worker.html`, about 94,000
subtests on wpt.fyi), through testharness.js's `fetch_tests_from_worker`. Before this work
none of them ran.

## What a page gets

- `new Worker(url, {type: 'classic', name})`: same-origin URL (or `data:`/`blob:`),
  resolved against the document's base URL by Lean's URL parser. `type: 'module'` is a
  `NotSupportedError` (module scripts are not in the engine yet).
- `worker.postMessage(message, transfer | {transfer})`, `terminate()`, `onmessage`,
  `onmessageerror`, `onerror`, and the same as `addEventListener` events.
- In the worker: `self` (a `DedicatedWorkerGlobalScope`, which inherits from
  `WorkerGlobalScope` and `EventTarget`), `name`, `location` (`WorkerLocation`),
  `navigator` (`WorkerNavigator`), `postMessage`, `close`, `importScripts`, `onmessage`,
  `onmessageerror`, `onerror` and the other `WorkerGlobalScope` handlers, `origin`,
  `isSecureContext`; and the APIs exposed to workers that this engine has: timers,
  `queueMicrotask`, `structuredClone`, `reportError`, `console`, `atob`/`btoa`,
  TextEncoder/TextDecoder (and the streams if present), URL, URLSearchParams, `crypto`
  (SubtleCrypto, CryptoKey), `performance`, WebAssembly, DOMException, events,
  AbortController/AbortSignal, Blob/File/FileReader/fetch when present.
- No DOM: every other global of the window is deleted from the worker's scope when it is
  made (an allow list, `workerGlobals` in prelude.js, plus the language's own globals as
  the realm had them before the prelude ran).

## Design

### One realm, heap and event loop per worker

A worker is a `LeanJS.Session` of its own (`WasmVM/Hosts/LeanJSWorkers.lean`): a copy of
the page realm with the prelude (`WebScripts.Held.leanBase`, decoded once from the
build-time snapshot; a copy of a Lean value is shared until written), whose global object
the prelude's section workers turns into a `DedicatedWorkerGlobalScope`; a host with an
empty arena (no DOM), its own `EventLoop.State`, script clock, Web API state with its own
entropy (fresh from the operating system's generator for each worker, as each page's is:
nothing of the page's seed reaches a worker, so `crypto.getRandomValues` and generated keys
of one agent tell nothing of another's), and its own step budget. Starting a worker therefore costs no prelude run: the realm is already made.

The prelude is shared, not duplicated: the worker realm runs the same prelude.js (the same
snapshot), then `api.worker(url, name)` makes it a worker scope. All event code, timers,
the structured clone of basics, and the Web APIs are the window's.

### Messages: the structured clone in Lean

`JS/Clone.lean`: StructuredSerialize and StructuredDeserialize of HTML §2.7 over the
BubblePopJS heap. Values become bytes in one realm and a value in the other; nothing else
crosses. Primitives, wrapper objects, Date, RegExp, ArrayBuffer (transfer detaches the
sender's), typed arrays, DataView, Map, Set, Error, Array, plain objects; identity and
cycles are kept. DataCloneError for Symbols, functions, Proxy, WeakMap/WeakSet, Promise,
SharedArrayBuffer, detached buffers. Known limit: an accessor property is read as
`undefined` (the walk is over the heap, it does not run getters). Theorems:
`natOf_natBytes` (the number codec's round trip), `unzig_zig`.

The page reaches it as `n.serialize`/`n.deserialize` (`NativeX.cloneSerialize`,
`cloneDeserialize`), and importScripts runs a classic script with `n.runScript`
(`NativeX.classicScript`: GlobalDeclarationInstantiation, so top-level `let`/`const` of
one imported script are seen by the next). These are engine built-ins, not host natives,
since they walk the heap; QuickJS-NG has none of them, so its prelude leaves `Worker`
undefined (a missing op turns the feature off).

### Ordering: agents (`EventLoop/Agents.lean`)

HTML runs each worker in an agent with its own event loop. The model: a system of agents,
each with a loop, an inbox and a closed flag; `post a b m` queues a task (source
`postedMessage`) on `b` and appends `(a, m)` to its inbox; the task's step takes the
inbox's first entry; `terminate b` empties `b`'s queues and closes it. Theorems:

- `channel_prefix`: on each channel `a → b`, the messages delivered are a prefix of the
  messages posted, in order (per-channel FIFO), whatever else happens;
- `step_isolated`, `post_other`, `take_other`, `terminate_other`, `step_own`: an agent's
  step changes no other agent, and depends only on its own state;
- `terminated_no_step`: after `terminate b`, `b` runs no task again.

The code keeps the model's shape: each message is one task (`eventHandle`) on the
receiver's loop plus one inbox entry; inbox and same-source tasks are both FIFO. The
inbox of the code is a queue with its own theorems (`LeanJS.WorkerHost.push_pending`,
`take_pending`, `push_head`, `take_head`): the events not yet taken are a list that a
message appends to and a delivery task takes the first of. A
worker's runs (`runTo`) take only the worker's value, so they cannot read or write the
page's session; the page gets only events (bytes) from them.

### Scheduling: interleaved on one thread

Natively and on the Hub, workers run on the page's thread, interleaved, deterministically:

- after each microtask checkpoint of the page (`engine.runJobs`), `pump` hands the page's
  asks (create, post, terminate) to the workers, starts workers whose scripts came, and
  runs each worker's tasks that are due at the page's clock;
- a worker's next timer arms one page timer (`wakeHandle`) at its due time, so the page's
  own `advance` and `settle` stop there and the workers run then;
- a worker's messages to the page are page tasks; the page runs them in its own loop.

Why not a real thread first: the engine is a pure Lean value per session; one thread
gives deterministic tests (WPT results do not depend on timing), needs no locks around
the session map, and works the same in the Wasm engine, which has no threads. A worker
that computes for long delays the page by up to its budget per pump (below); a thread per
worker is the follow-up when a page needs parallel speed, and the session values make it
possible (a worker's run takes and returns only its own value).

### Budgets

Each worker run has a page run's steps (`workerBudget`); all workers together get one
page run's steps per pump (`pumpSteps`), then wait for the page's next turn, so a worker
cannot starve its page; one worker run delays the page at most as long as one of the
page's own runs can. (Until 2026-11-11 a worker run had an eighth of that: a run that
stops at the budget is lost, not resumed, so a test that runs thousands of subtests in its
start script, such as encoding/api-invalid-label.any.worker.html, stopped before `done()`
and timed out.) A worker whose runs stop at the budget three times, or
whose heap passes 4 M objects, is stopped and an error goes to its Worker object. At most
16 workers per page; a worker's console lines join the page's (`[worker N] ...`).

### Scripts: fetched by the embedder, runs undone when one is missing

The engine fetches nothing. A turn whose workers wait lists `fetches: [{id, url, kind}]`
(`kind` `worker` or `script`), and `settle` stops there; the embedder answers with the
action `fetched` (`results: [{id, status, url, contentType, source}]`; status 0, a status
that is not 2xx, or a type that is not a JavaScript MIME type is a network error, as HTML's
strict worker fetches say). `importScripts` is synchronous: when a run needs a script not
fetched yet, the run is undone (the worker's state before the task is kept; sessions are
values) and runs again when the script comes. So that a test's start does not run once per
imported script, the string literals of `importScripts(...)` in a worker's script are
fetched with it (a hint; what runs is decided by `importScripts`).

### Requests: XMLHttpRequest and fetch in a worker (2026-11-12)

A worker of a page whose embedder turned the network on (`network:true`) has
`XMLHttpRequest`, `fetch`, `Headers`, `Response`, `FormData` and `Blob` (the classes of the
window, from the same prelude; `responseXML` and the response type `"document"` are
window-only, XHR §4.6). Every decision is Lean's, as for the page
(`docs/designissues/2026-11-11-page-network.md`):

- Each worker has its own `Net.Xhr.State` (`LeanJSWorkers.workerNet`), whose policy is its
  owner's for the worker's URL (`PageFetch.Page.forWorker`): the owner's origin (a `data:`
  worker: opaque, `"null"`), and always the owner's local-address, mixed-content and
  `hostCors` rules. Theorems: `forWorker_origin` (the owner's origin or `"null"`, never
  another), `forWorker_policy`, `forWorker_mayConnect`, `forWorker_not_data`,
  `workerHost_net_page`, `workerHost_net_enabled`. CORS, preflights, redirects, forbidden
  fields and methods, the DNS pin and `data:` URLs are `PageFetch`'s, unchanged.
- The host knows only the page. A worker's requests join the page's `netRequests` with an
  id from the page's own numbering (`Workers.routes` maps it back), so no host changed;
  `forwardNet` changes a request's id and nothing else (`routeWire_same`). The host's
  answers (action `net`) to them go to the worker (`giveNet`): its `Net.Xhr.give`, and the
  object's callback a task on the worker's networking source. Requests of a worker that is
  terminated or closes go to the host's `netCancels` (`dropRoutes`).
- Sync requests (allowed in workers, XHR §4.5.2) use the undo of the worker's own run, as
  `importScripts` does: the run that needs an answer is undone (the worker's state before
  the task is kept), the request goes to the host as an ordinary page request, and the task
  runs again with the answers so far (`Worker.syncCache`; phase `syncing`, or `starting`
  with `syncWait` for a worker's top-level script). The page is not undone and does not
  wait: only that worker does. The redone run is the same run (the same clock, random
  numbers and order), so the `k`-th sync request takes the `k`-th answer.
- `settle` stops while a worker's request is at the host (`Agents.waits`).

Measured 2026-11-12 (native engine, BubblePopJS, WPT fea36e49 through wptserve; the
`.any.worker.html` variants of every `.any.js` in `xhr/` and `fetch/` whose globals include
a dedicated worker: 260 pages): 51 of 2,512 subtests before, 1,547 of 2,829 after (`xhr/`
49/268 -> 347/411, the same as its window variants; `fetch/` 2/2,244 -> 1,200/2,418). Window
variants of the same files: 1,441/2,905 -> 1,445/2,905, no subtest lost.

Not done or open:

- A sync request's `timeout` in a worker (the run sees the answer at once, on the virtual
  clock).
- `xhr/xhr-timeout-longtask.any.worker.html` times out (its window variant passes): a busy
  loop on `performance.now()` in a worker; not a request issue.
- No proof that the realm's scripts cannot change a worker's policy after it is made: no
  op of `Net.Xhr.op` writes `State.page` (by reading of the code; a theorem `op_page` is
  the follow-up).
- QuickJS-NG: no `Worker` there, so nothing to do until it has one.
- The Wasm engine (Hub) runs the same Lean; not built or run for this change.

### Pages without workers pay nothing

Nothing new on the start path: no new work at page start, first frame, scroll or input.
The `Worker` class is in the snapshot. A page that makes no worker pays one check of an
empty array per microtask checkpoint (`LeanJSWorkers.pump`).

## Left out, and what they would need

- Module workers (`type: 'module'`): module scripts in BubblePopJS.
- Nested workers (a Worker inside a worker): an agent tree in place of the page's list.
- MessageChannel/MessagePort transfer: ports as agents' channels in `Agents`, and a port
  table per realm.
- SharedWorker: one agent shared by several pages of an origin: a process-wide map of
  workers by (origin, URL, name) outside one page's session, and ports.
- ServiceWorker: a registration store, the fetch event on every page load (the network
  path of the engine and the Hub's fetch), lifetimes and update checks; much larger.
- SharedArrayBuffer and Atomics.wait across agents: a real shared memory between agents
  (and threads).
- Getters during serialization, and platform objects (Blob, File, ImageData, CryptoKey)
  in messages: their serialization steps.
