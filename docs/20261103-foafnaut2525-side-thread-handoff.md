# foafnaut2525 side-conversation handoff

> Note, 2026-11-09: This handoff is of 3 November and is superseded. Current state:
> [Foafnaut handoff](designissues/2026-11-09-foafnaut-handoff.md) and
> [skills/foafnaut/SKILL.md](../skills/foafnaut/SKILL.md).

3 November 2026. This records the substantive requests, findings and proposals
from the owner's `/btw` conversation. It is a summary, not a verbatim
transcript. The main agent should read it before reporting current status.

## Scope and evidence date

The side conversation initially inspected existing work, created the explicitly
requested issue below, and updated documentation. A subsequent explicit
request authorized the [timed WPT baseline and cache cleanup](20261103-browser-wpt-baseline.md):
new local test runners and measurements are recorded there. The owner's
subsequent foundation-work request authorized local implementation:
[parser diagnostics, tokenizer, JS/DOM and text-size progress](20261103-browser-foundations-progress.md).
That work includes local native CLI/WASM rebuilds and an original SVG Tiny
admission baseline. It did not start a native app implementation, publish a
release, contact Apple, or submit a DMA complaint. The main thread owns
integration and release coordination.

Most browser observations were at host source `b578816b0`, with renderer
artifacts from `63a73ff4a`. Live ports, process state, free disk, CI and
artifact availability can change. Recheck them; do not present these earlier
observations as a new status review. Existing coordination is in
`/tmp/factoidal-overnight-coordinator.md`; this side thread did not edit it.

The companion [runtime maturity record](designissues/2026-11-03-foafnaut2525-runtime-maturity.md)
covers JS/DOM/event-loop gaps, guest WASM, proof attestation, XSLT and Apple
distribution, including the nonprofit/DMA discussion. It is linked from the
`lean4-wasm-export` and `build-and-test` skills and the worknote index.

## Owner's requested product

- A standalone application named `foafnaut2525`, including the FOAFNaut
  graph demo. A macOS application is the first requested delivery; iPhone
  and iPad are also wanted. A renderer CLI or an external-browser development
  bundle must not be reported as that application.
- Reuse Factoidal LWS locally without requiring an HTTP client/server loop.
- Support broader HTML/CSS/SVG, actual external standards suites and visible
  failures, rather than a handful of selected demo files.
- Improve resilience: catch and log failures, then try bounded input
  simplification to obtain a useful page. Preserve the original source.
- Add JS, a defined browser event loop, sandboxed guest WASM and a shader
  playground; distinguish formally checked properties from implementation
  language and sandboxing claims.
- Add classic XML stylesheet loading and an `XSLTProcessor`-compatible
  interface, reusing existing Lean XSLT implementations.

## Demos and native-renderer assurance

Earlier successful HTTP checks found the frozen HTML bundle on
`http://127.0.0.1:8099/`, a mutable HTML host on port 8102, and the SVG
comparison gallery on port 8097. These are historical reachability checks.

The RDF view in the HTML renderer is Lean N-Triples parsing, a Lean DOM view
of subject/predicate/object rows, and the shared layout/scene path. It is
not the FOAFNaut node-and-edge diagram. Source:
`labs/demos/foafnaut/WebRenderRDF.lean` and
`formal/lean4/L4Factoidal/Rendering/RdfView.lean`; record:
[Lean RDF renderer](20261103-lean-rdf-renderer.md).

The native renderer inspected at
`labs/demos/foafnaut/.build/web-render/web-render-native` was Mach-O ARM64,
SHA-256 `ee90a9317456104a6104f9219cfe536774fad9aa6888f94cfa18e6a1e7e3c7de`.
Its dynamic-library declarations were libc++ and libSystem. A tiny native
CPU render with loader tracing showed no WebKit, WebCore, Blink, Chromium,
JavaScriptCore, AppKit or Electron match. Source/build inspection also
identified Lean-generated C. This is evidence about that CLI, not a proof
of every future app dependency or a verified native GPU window.

The CLI emits scene JSON; `--pixels` adds CPU RGB data. It does not open a
browser window. A 16x16 CPU probe completed; a 128x96 probe timed out after
30 seconds. The main coordinator had also recorded native Deno WebGPU
returning no devices while Chrome Metal worked. Recheck the native GPU
route before giving a delivery estimate. The side discussion's rough
one-to-two-day alpha estimate was conditional, not a scheduled build or
release commitment.

## Standards-test evidence and requested harness behavior

The SVG gallery's four visible examples are not the full external harness.
The separate `source/factoidal-svg-corpus-overnight` checkout contains WPT
corpus work. The earlier full report is
`/tmp/factoidal-overnight-corpus-curves-web-wasm-ready/run.json`, with capture
details in its `capture/report.json`.

That 3 November 00:46-00:49 UTC run covered 601 relations: 29 match,
21 mismatch, 264 unsupported, 30 rejected and 257 unavailable. It used
older renderer artifacts; it is not a conformance result for the later
qualified browser engines. It covers 322 SVG and 279 HTML relations.
The need is both broader passing coverage and a visible results UI.

The owner supplied Chromium's
[text-test baseline guidance](https://chromium.googlesource.com/chromium/src/+/66.0.3343.2/docs/testing/writing_layout_tests.md#Text-Test-Baselines).
Use assertion/text results for DOM and layout contracts, reftests for paint,
and actual/expected/diff artifacts. Keep PASS, FAIL, CRASH, TIMEOUT and
UNSUPPORTED distinct. Known-failure baselines detect changes; they do not
make failures passes. Native/WASM agreement is a useful consistency check,
not an independent standards oracle. Any input-repair mode must be separate
from unchanged-input conformance runs.

## HTTPS, crashes and proposed recovery

HTTPS transport already exists in the Node resource broker. Earlier calls
through the live 8099 broker retrieved HTTPS bytes from example.org,
info.cern.ch and w3.org with HTTP 200. The broker uses the host TLS stack;
this does not establish a Lean TLS implementation.

Feeding the unchanged retrieved bytes into the native CLI exposed limited
rendering support: example.org's `light-dark()` CSS color, CERN's `ul`, and
the W3C page's external stylesheet requirement. The last CLI result does not
prove the browser path lacks external CSS fetching: it has a separate
resource transport. No exact owner-reported crash was reproduced here.

Source inspection found synchronous renderer `ccall` execution on the host
UI thread. An AbortController cannot interrupt a CPU-bound call there.
QuickJS has a separate worker and watchdog. Moving rendering behind a
terminable boundary is a proposed response to freezes, not a measured fix.

Proposed fallback: preserve original bytes and diagnostics; retry in a fresh
bounded execution context; first remove the identified unsupported
declaration, then apply explicit layout/font simplifications if needed.
Limit attempts and total time, retain useful text and links, and label the
result as adapted. A blank image is not success. Save the transform log and
source identity. The owner also suggested an optional HTTP page-simplifying
proxy producing classic HTML; it could be an in-process adapter. None of
this recovery/proxy work was implemented by the side conversation.

## Embedded LWS and native architecture proposal

`npm/factoidal/lws/server.mjs` already separates `openLwsStorage(options)`
from the HTTP listener; it exposes `step(request)`, `close()`, `handle` and
`engine`. The Lean WASM operations include `lwsOpen`, `lwsStep` and
`lwsClose` in `formal/lean4/Wasm/Ops/Lws.lean`. Reuse those local operations
and persistence while retaining authorization boundaries. Do not add a
loopback server solely to access storage in the application.

The proposed native shell owns the window, input, GPU presentation and host
I/O. Lean owns document/layout/scene semantics and the local application
model. Existing AppKit/CAMetalLayer work is in
`labs/demos/foafnaut/native_window.m`; its Deno adapter is macOS-specific.
The [mobile library proposal](designissues/2026-10-29-mobile-native-library.md)
describes Lean-generated C and a native ABI; it is not an implemented iOS
app. Mobile needs its own host UI, touch/input and packaging.

The owner also asked for a fresh Lean UX using the word "litttering".
Whether this means lettering/text editing or freely arranging notes, links,
RDF and visual experiments was not clarified. Reuse existing Lean
drag/pin/select/edit controls where appropriate; do not assume a completed
HTML UI is required for the first native workspace.

## Issue and repository changes from this side conversation

Created https://github.com/danbri/factoidal/issues/1232
(scripts must observe their own DOM mutations immediately; define layout
query behavior). The issue includes source-derived stale ancestor and
detached-node regression targets. Those examples were not reported as a
fresh execution of QuickJS tests.

Local documentation changes, not committed or pushed by this side thread:

- This handoff and the companion runtime maturity record.
- Links in `docs/worknotes-index.md`, `skills/lean4-wasm-export/SKILL.md`
  and `skills/build-and-test/SKILL.md`.

Both modified skills passed the skill validator; the maturity note's local
links resolved and `git diff --check` passed. These are documentation checks,
not runtime tests. An unrelated untracked `zzz` appeared in the checkout;
it was not created, read, staged or changed by this side thread.

## Main-thread review requested next

Read this handoff and the maturity record, then inspect current repository,
CI, coordinator and actual artifact state. Report the available demo and
native binary, latest full external-suite results, native-app progress,
JS/event-loop/WASM/XSLT implementation status and the next releasable
checkpoint. Distinguish checked artifacts from plans and old reports.
Review these documentation changes for inclusion in the next coherent
checkpoint without staging unrelated files.
