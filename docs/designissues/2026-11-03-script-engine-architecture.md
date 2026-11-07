# JavaScript engine and Lean DOM boundary

Decision, 3 November 2026: use the unmodified QuickJS-NG 0.18.0 WASI
reactor in a dedicated worker for the browser MVP. Keep the Lean arena and
the QuickJS heap in separate WebAssembly memories. Exchange bounded node
projections, typed mutation commands and event messages. A timeout destroys
the worker and its script state.

## Modules and ownership

```text
HTML and supplied CSS bytes
        |
        v
Lean WebDocument / WebRenderScript ---- element projection ---> QuickJS worker
        ^                                                    |
        |          checked setTextContent/setAttribute        |
        +----------------------------------------------------+
        |
Lean DOM -> CSS -> font requests -> layout -> scene -> WebGPU transport
        ^
        +--- picked source node <--- Lean hit testing <--- pointer coordinates
```

`WebRenderScript.lean` discovers script elements, projects connected element
handles, validates command objects and calls the existing `DOM.Dom` mutation
functions. It does not parse HTML a second time. `WebDocument.lean` reparses
the unchanged source and replays the cumulative command history for each
inspect, font request and render operation. This gives one repeatable arena
for the MVP. Replacing replay with a retained Lean document handle is a later
performance change behind the same command types.

The source files in `labs/demos/foafnaut/web-render/script-engine/` have these
roles:

| File | Responsibility |
| --- | --- |
| `quickjs.mjs` | Check the reactor hash, instantiate WASI, own runtime/context/value lifetimes, set engine budgets. |
| `guest.mjs` | Install the small script API inside QuickJS; queue provisional DOM commands. |
| `worker.mjs` | Execute classic script turns and click callbacks in that engine. |
| `session.mjs` | Own worker lifetime, validate messages, serialize turns, enforce the host watchdog. |
| `fetch-reactor.mjs` | Download or read the pinned binary, check SHA-256, install it under ignored `.build/`. |

Neither the host JavaScript runtime nor the guest projection owns document
layout. Page source is passed to `JS_Eval` in the QuickJS WASM instance.
The host does not call JavaScript `eval` or `Function` on page source.

## MVP API and limits

`createScriptSession()` creates a session. `start({nodes,sources,budgetMs})`
creates a new worker, installs the projection, then evaluates the ordered
classic sources in one QuickJS context. Top-level lexical bindings persist
across scripts and click turns. `dispatch({type:'click',nodeId})` invokes a
registered callback. Both calls return `{commands,listeners,logs,defaultPrevented}`.
`reset()` rejects outstanding work and terminates the worker.

Click events are cancelable and expose `preventDefault()` and a read-only
`defaultPrevented` flag. The flag belongs to that event; retaining an old event
cannot cancel a later click. An `onclick` property handler returning `false`
also cancels its event; an `addEventListener` return value does not. Cancellation
is validated message metadata, not a Lean DOM mutation command.

After a listener turn, the host applies commands and renders again. An anchor
follows its updated Lean-emitted link target unless the event was cancelled.
This requires the same anchor to remain in the rendered link regions; removing
or hiding it reports an unsupported default action. General activation steps
and event propagation are outside this profile. Counter examples cancel their
anchor action explicitly.

Node projections have `{id,tagName,attributes,textContent}`. IDs are Lean
arena indexes, not browser DOM nodes or raw memory addresses. Commands are:

```json
{"op":"setTextContent","nodeId":4,"value":"Clicks: 1"}
{"op":"setAttribute","nodeId":5,"name":"data-clicked","value":"yes"}
```

Lean checks command shape, duplicate fields, target existence and element
type. It delegates attribute-name validity and mutation semantics to
`DOM.Arena`. A failed command list returns no changed arena. The host also
validates the worker result before any commands enter the document request.
A guest exception discards that turn's queued commands and resets the VM.

The binding supports `getElementById`, simple `#id` `querySelector`,
`textContent`, `getAttribute`, `setAttribute`, `onclick`, `addEventListener`
for `click`, and bounded `console.log`. Script discovery reports a Lean
`kind` of `classic`, `module` or `data`. Data scripts remain inert. Module
execution is outside this profile. The demo runs scripts after document
preparation; it does not implement parser-blocking script scheduling,
`async`/`defer` order, general event propagation/activation, timers, modules,
Promise jobs, network APIs, arbitrary selectors or WebIDL conversions.

The guest stores a provisional element projection so simple scripts can read
their own writes. It is not a complete live DOM. In particular, parent text
and child references are not refreshed after subtree mutations. The Lean
arena remains authoritative. A future synchronous DOM binding needs
generation-checked handles, request/response operations and a specified
event loop; the current API must not be described as general DOM support.

Budgets: 16 MiB of QuickJS runtime allocation, 512 KiB maximum engine stack,
1 MiB total script source, 64 scripts, 16,384 projected elements, 2 MiB of
projection JSON, 256 commands per script turn, 4,096 replayed commands per
document, 64 KiB per mutation string and 32 log entries per turn. The normal
execution deadline is 100 ms; accepted values are 1–1,000 ms. Startup has a
5 second watchdog. A script-turn watchdog expires after the budget plus
500 ms. Browser suspension or a busy host can delay timers; these are
execution controls, not real-time guarantees.

## Engine artifact and interruption

The pinned upstream asset is 1,560,132 bytes:

- [QuickJS-NG 0.18.0 release](https://github.com/quickjs-ng/quickjs/releases/tag/v0.18.0).
- [Reactor binary](https://github.com/quickjs-ng/quickjs/releases/download/v0.18.0/qjs-wasi-reactor.wasm).
- SHA-256: `8afa5d73287af5573613e15d5e633e91d8e096b40676f424f104087bc1416678`.

The [upstream build](https://github.com/quickjs-ng/quickjs/blob/v0.18.0/CMakeLists.txt)
uses the WASI reactor execution model, exports the C API and allocation
functions, and exports a growable function table. The adapter adds a typed,
41-byte WASM trampoline to that table for `JS_SetInterruptHandler`. The host
callback checks a deadline. This avoids recompiling QuickJS. Its stack and
allocation limits use the engine API; all result values and C strings are
freed. The runtime has no installed `std` or `os` modules. Filesystem and
stdio WASI calls return errors; no directory, socket, process environment or
host object is granted. Clock access is available to the runtime.

If a turn does not return, the host terminates the worker. This also covers
engine traps or an engine path that fails to poll its interrupt callback.
The next start creates a fresh WASM instance. A WASM sandbox and these
budgets are useful boundaries; they do not constitute a proof of engine or
binding correctness.

QuickJS-NG has the permissive MIT terms in its
[source header](https://github.com/quickjs-ng/quickjs/blob/v0.18.0/quickjs.h).
Keep upstream notices when distributing its binary. The binary is a fetched
dependency, not a repository source artifact; do not commit it.

## Separate instances and shared memory

Separate WASM instances are compatible with this architecture. Each module
can own its memory and allocator. They can exchange copied bytes through the
host, or call imported functions with an explicit ABI. A pointer is meaningful
only in the memory that owns it. Sharing a compiled `WebAssembly.Module`
does not share the state of its instances. The [WASM module
specification](https://webassembly.github.io/spec/core/syntax/modules.html)
defines memories, imports and exports separately.

| Arrangement | Benefit | Required work or cost |
| --- | --- | --- |
| Separate workers and heaps, command messages | Independent cancellation, simple ownership, no shared allocator | Copies and asynchronous turns; limited synchronous DOM API. This is the MVP. |
| Separate instances in one worker, imported calls | Synchronous callbacks to Lean, same typed boundary | Reentrancy/lifetime rules; a stuck engine also stalls that worker's Lean instance. |
| Shared byte buffer for messages only | Fewer copies for large payloads | Versioned ring buffer, bounds checks, atomics and cancellation protocol. Lean/QuickJS objects still stay private. |
| One linear memory for both runtimes | Potential direct byte access | Both binaries must import compatible memory; partition data, stacks and allocators; define growth and lifetime rules. Does not make Lean and JS heap objects compatible. |

The existing Lean Emscripten module and upstream WASI reactor define their
own memories. Passing the same JavaScript memory object does not retrofit
sharing. Rebuilding to import one memory still leaves independent allocator,
global-data, stack, reference-counting and GC rules. Sharing whole heaps
would also let a QuickJS memory defect damage Lean state, weakening the
chosen failure boundary. No measured MVP cost justifies that change.

A true cross-worker shared memory adds browser deployment conditions.
Emscripten documents the [COOP/COEP requirement for
SharedArrayBuffer](https://emscripten.org/docs/porting/pthreads.html).
The present worker/message path needs no shared memory or isolation headers.
First measure projection and command-copy costs. If they dominate, a shared
transport buffer can be added without sharing runtime heaps.

## VerifiedJS assessment

Research inspected [BasisResearch/VerifiedJS](https://github.com/BasisResearch/VerifiedJS)
at main commit
[`b6eabd76a1eab6573c0d422db8142869133eabb4`](https://github.com/BasisResearch/VerifiedJS/commit/b6eabd76a1eab6573c0d422db8142869133eabb4)
(2 April 2026). It is relevant research: Lean source, inspectable compiler
passes, interpreters, and conditional preservation theorems.

Its [README](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/README.md)
targets ES2020 but reports runtime and language gaps. Treat that status as a
development report, not a conformance result. Source inspection gives a more
precise distinction: [Wasm/Lower.lean](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/VerifiedJS/Wasm/Lower.lean)
contains implemented call/property helpers, while `__rt_getGlobal` still
returns boxed `undefined`. Thus the README's broad claim that call/property
helpers are placeholders is stale. There is no usable `document` host binding
in that helper path.

The [end-to-end theorem](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/VerifiedJS/Proofs/EndToEnd.lean)
starts with Flat/Core/ANF programs, excludes reachable `forIn`/`forOf`, and
requires well-formedness and memory hypotheses. Its preservation conclusion
does not establish that arbitrary browser JavaScript implements ECMAScript.
The [elaboration theorem](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/VerifiedJS/Proofs/ElaborateCorrect.lean)
uses `Source.Behaves` defined through elaboration; this is not an independent
ECMAScript source-semantics validation.

Its [Lake configuration](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/lakefile.lean)
requires Mathlib, and the [toolchain](https://github.com/BasisResearch/VerifiedJS/blob/b6eabd76a1eab6573c0d422db8142869133eabb4/lean-toolchain)
is Lean 4.29.0-rc6. We did not build it or claim fresh Test262 results.
The root directory has no LICENSE file and the [GitHub repository
metadata](https://api.github.com/repos/BasisResearch/VerifiedJS) reports
`license:null`; reuse terms need clarification before vendoring.

Measured results, 7 November: [VerifiedJS for page scripts](2026-11-07-verifiedjs-page-scripts.md).

Keep VerifiedJS as an optional compiler backend experiment. To replace
QuickJS in this browser profile it must first run the same script/click
fixture, implement explicit host bindings, pass boundary and interruption
tests, and identify the exact theorem and assumptions for that code path.

## Reproduction and evidence

From the repository root:

```sh
node labs/demos/foafnaut/web-render/script-engine/fetch-reactor.mjs
node --test labs/demos/foafnaut/web-render/script-engine/session.test.mjs
```

An existing local reactor can be the fetch helper's first argument. Its hash
is checked before installation. On 3 November, the real upstream reactor
passed 10 Node worker tests: engine execution/isolation and hash refusal;
ordered scripts and click commands; infinite-loop interruption and restart;
hard worker termination before the cooperative deadline; allocation failure
and exception discard; malformed-command refusal; reset during startup.
`WebRenderScript.lean` and its separate guards also elaborated successfully.
The integration fixture is `web-render/fixtures/scripted.html`. Browser/GPU
integration evidence belongs in the main MVP worknote after its rebuilt Lean
artifact is tested.
