# Terminable browser renderer execution

The foreground renderer API now transfers data to a separate Web Worker.
`engine-core.mjs` contains the previous Lean ABI implementation, and only
`engine-worker.mjs` imports it. HTML parsing, computed styles, document commands,
font-data validation, layout and link/node picking still run in Lean WASM.
The foreground no longer executes those synchronous `ccall` operations.

A busy synchronous WASM call cannot process a cancellation message. Stop and
superseding input therefore terminate its worker. The next operation creates a
fresh instance. The app calls `engine.abortPending` from `abortRender`, and the
document client passes its operation/lifetime signal as a separate transport
argument. Transport controls do not enter Lean document options. Text-scale
options retain their existing representation.

## Request and lifetime rules

The default client has one worker, one active request, at most eight active or
queued requests, and a 24MiB aggregate argument budget. Arguments are captured
as immutable JSON before enqueue. A caller cannot enlarge queued work by
changing its original options after the byte count is recorded. Each request
has a 30-second deadline measured from enqueue, including queue wait.

A queued abort or deadline removes only that request. An active abort or active
deadline terminates the worker and rejects its pending generation. Module
initialization failure, a worker error or a WASM trap also resets the generation.
A normal unsupported-input/profile error leaves a healthy worker available.
Replies must match the current worker, generation and request ID. A late reply
from a terminated worker cannot resolve a newer request.

The public async methods retain their argument order and return values:
`compile`, `compileWithFontData`, `inspectDocument`, `documentFontRequests`,
`compileDocument`, `fontRequests`, `compileFont`, `hitLink` and `hitNode`.
An optional final `{signal,timeoutMs}` argument controls transport. For example:

```js
await engine.compileDocument(html, width, height, documentOptions, {signal});
await engine.inspectDocument(html, documentOptions, {signal});
```

`createEngine` permits an isolated host/test client with a worker factory,
module URL and bounds. Its module URL is a trusted host setting; page content
and guest scripts do not supply it. `abortPending` permits later recovery.
`dispose` ends the client. The shared module facade can create a new client
when it is used after disposal.

## Retained hit metadata

A compiled scene crosses to the foreground once. The worker retains only its
link/box metadata, with at most eight entries and an 8MiB JSON-size bound. The
foreground records opaque handles in a WeakMap. Repeated link/node picking sends
the handle rather than the shader or paint data. After worker reset or cache
eviction, the client registers only link/box metadata and retries the pick.
The existing Lean picker still determines the result.

The server and development package inventories include `engine-core.mjs` and
`engine-worker.mjs`. Their source bytes are covered by the host package manifest.
The renderer module and its neighboring WASM keep their existing URL mapping.
Existing same-origin worker CSP applies.

## Scope and checks

The QuickJS worker retains its separate Lean DOM instance and watchdog. The
WebGPU transport/render-plan layer and native font broker are unchanged by this
change. Browser presentation and network/font I/O have their own lifetimes.

Fourteen Node22 tests execute the real renderer WASM and compare complete
artifacts with the direct ABI. They cover HTML, RDF, document commands and CSS,
text-scale option transfer, actual supplied font records, aliases, Lean picking,
metadata eviction, immutable queued inputs, separate count/byte bounds, queued
and active cancellation/deadlines, a nonreturning worker, CPU-bound Lean
interruption, stale replies, initialization failures and recovery. The actual
font records are external test input; no font file is bundled.

The browser harness additionally checks foreground heartbeat, active abort,
nonreturning-worker timeout and recovery through the same API. Its automated
runner is `web-render/tests/check-browser-worker.mjs`. The application browser
checks remain required to qualify the integrated navigation/scene behavior.
See [the validation worknote](../20261104-renderer-worker.md) for measured
results and current browser evidence.
