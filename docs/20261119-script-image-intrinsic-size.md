# Intrinsic layout dimensions for 1x image element requests

Tracking: [image dimensions637](https://github.com/danbri/factoidal-core/issues/637).
Candidate branch: `wip/wpt-imgsize-closeout`, based on tested source
`7d4794f49f5d85f6755cde79afa7e52e30c62af0`.
No commit, push, cloud dispatch or local Lean build was made by this worker.

## Source gap and selected change

The actual image-element request receives dimensions from `Net.Xhr.imageRaw`.
The realm uses them for `naturalWidth` and `naturalHeight`. When the renderer has no
decoded `Picture` for that element, layout has no request dimensions and uses its
alt-text path. An empty alt string can give a zero-sized box even after load.

The saved branch `wip/wptbulk4-imgsize` ends at
`5bb0a6332527ce106b982b38f5940afdf7ac6610`: three distinct commits and154 behind
this tested ancestor. The selected part carries dimensions through `Node.natural`,
`Command.setNatural`, DomOps163, both command JSON forms and command replay, then
selects them in `Layout.blankReplaced`. The existing prelude forwards the dimensions
read by the engine; it gains no image parser or sizing algorithm.

The other part of the saved change adjusts canvas CORS cleanliness. It is excluded.
Image adoption/fragment insertion in saved `wip/wptbulk4-imgadopt` is also separate.
This patch does not obtain or paint image pixels.

The old saved adapter left dimensions stale when src was removed. This candidate
requests a clear after removal, request failure or an unavailable answer, and drops
JavaScript tracking only after the host acknowledges it. Each admitted dimension is
at most65535. If a command budget refuses a clear or replacement, the arena and its
tracking retain the last accepted pair. An asynchronous refusal ends that generation,
rejects decode waiters and reports an error, with no load event and no automatic retry.
A synchronous source-removal refusal propagates the host error to its caller.
There is no unconditional guarantee that an exhausted command budget clears old metadata.

The request form of op195 now returns a unit-density marker together with the URL
from the same call to `HTML.ImageSource.selected`. The original three-field currentSrc
wire keeps its existing answer. A successful non-unit-density request clears any
previous 1x dimensions and still fires its load event. Computing CSS dimensions for
such a request, including fractional widths, remains open. The realm's natural-width
and natural-height getters retain their existing semantics. The accepted-size flag
lives on the existing image request state, so this change adds no separate per-realm
image-tracking set. The general DOM node representation still needs measurement.

## Independent review corrections

The source-only independent review requested changes before acceptance. The parser
now reserves the empty string for a clear, accepts exactly two bounded decimal fields,
and rejects every other nonempty payload. Its eleven-byte guard precedes conversion
to Nat and the general numeric decoder. Refusal preserves the entire host state.

The image watcher now decodes null-namespace host names without changing local-name
case. It handles removeAttributeNS(null,src) and removeAttributeNode; a non-null
namespace or uppercase null-namespace local name does not restart src. Relevant
HTMLImageElement reflection uses the watched path, including srcset, crossOrigin
and referrerPolicy, rather than bypassing it through op167.

The source-extracted JavaScript checks cover a negative host acknowledgement,
namespace/case distinctions, and the same URL switching from 1x to 2x and back to 1x.
They use mock host replies. Actual-op Lean guards
start from a sized image and cover malformed input, both size axes, wrong target,
command-limit refusal and live/replay agreement ending in a non-default pair.
The native/Wasm BubblePopJS test also exercises a reflected 1x source replacement
and both null-namespace removal routes with distinct A/B dimensions. It also checks
that a 2x request does not reuse the preceding 1x geometry and a later 1x request
restores it. Those engine
tests and all new Lean declarations await exact-source cloud verification.

## Evidence so far

- `node --check tools/wasmvm/quickjs/prelude.js`: exit0.
- `git diff --check`: exit0.
- `node --test tools/wasmvm/quickjs/image_size_tracking_test.mjs`: five passes, zero failures.
- A direct native ABI probe of the already installed release `c91b7d21d0a9` returned
  `natural 0 0`, `scaled 0 0`, `cleared 0`, with no engine errors, for a newly created
  image, valid37×23 PNG response and no held-image cache entry.
  Probe: `/private/tmp/wpt-imgsize-baseline.ts`. This is an observed older-release
  failure, not an exact7d before/after test or a WPT score.
- The normal local Deno test command could not start: the sparse tree has no installed
  `.build/native-html/runtime/web-render.mjs`. Nothing was downloaded or copied to
  fill it. The direct ABI probe used the already installed native library and a small
  temporary Deno cache instead.
- No new Lean proof compiled yet. No candidate native/Wasm test ran, no WPT gain,
  timing or memory improvement is claimed.

## Proof candidates

All have Kind/Says/Does-not-say comments and individual `#print axioms`:

- `L4Factoidal.Rendering.Layout.blankReplaced_img_none`: no request dimensions retains
  the old layout branch.
- `L4Factoidal.Rendering.Layout.blankReplaced_img_some`: admitted node metadata is
  exactly the intrinsic pair selected for replaced layout.
- `L4Factoidal.WasmVM.Hosts.Dom.Command.apply_setNatural`: an existing image with
  admitted dimensions gets the exact requested arena update.
- `L4Factoidal.WasmVM.Hosts.Dom.Command.apply_setNatural_refused`: oversized dimensions
  are refused before a DOM update.

Two further boundary candidates are `Hosts.Dom.imageNaturalArg_empty` and
`Hosts.Dom.imageNatural_refusal_preserves`: explicit clear encoding and whole host-state
preservation after refusal. They are not counted as checked theorems.

These do not prove CSS Float arithmetic, successful decoder/network provenance,
wire round-trip, image pixels or host behaviour. They are unproved until a fresh
zero-exit check with permitted axiom reports and hygiene.

The existing ReplacedTests module gains width-only, height-only, both-dimension
and27:13 cases; the non-binary ratio uses a tolerance rather than excluding it.
DomCommands gains actual command bound, clear, clone-default and compacted-replay
guards. `script_reads_holds_test.ts` gains native and Wasm BubblePopJS tests that
deliver a request through the actual network-step ABI without `imageLoad`, read
natural and width-scaled geometry, then remove src and check clearing.

## Exact validation to request after coordinator commit/push

Fresh source-only proof checking must explicitly compile the affected Runtime/Tests
modules, including `L4Factoidal.Rendering.ReplacedTests` and
`L4Factoidal.WasmVM.Tests.DomCommands`, with normal bounded Lean processes.
Run every Lake command with `formal/lean4` as its explicit working directory.

Full native/Wasm engine gates must execute the existing
`labs/demos/foafnaut/script_reads_holds_test.ts`. The Linux `build.yml` host-tests job runs
this file on the Wasm engine. Its engine artifact contains no native `.so`, so that job
alone cannot supply a native test result. The branch WPT build exports the exact candidate
`libweb-render.so` as `branch-engine`. With that library, its pinned Lean shared runtime
and the Wasm wrapper installed, the same test file runs on Linux using
`WEB_RENDER_LIB=<path-to-branch-engine/libweb-render.so> deno test --allow-read --allow-ffi --allow-env --allow-write labs/demos/foafnaut/script_reads_holds_test.ts`.
A configured but missing library fails the test. Each network response and each settle turn
can start another image request in the fixture's load handler, so the test drains both.

For a complete affected-population development comparison, request `branch-wpt.yml`
in `danbri/factoidal-builds`, with a pushed exact candidate SHA as `core_ref`:

```text
names=/html/semantics/embedded-content/the-img-element/,/html/rendering/replaced-elements/images/,/html/rendering/replaced-elements/attributes-for-embedded-content-and-images/,sample:40
wpt_commit=71b58bb1916c14a3b0be82e369d89c8bcf9001e2
```

Those directories were checked against the official WPT tree at that ref.
The exact full commit and the baseline chosen by the workflow must be recorded.
Report names planned/run, passing subtests before/after, every regression and every
CRASH/STALL/TIMEOUT. This development check is not a whole-suite conformance score.
The template-clone natural-size test also needs adoption and density/SVG work, so
this narrow patch is not expected to make that entire test pass.

Before merge, require the exact-source Linux build gate, premerge checks, and a
measurement of inert-page timing and DOM memory. The new Node field changes the
general representation; it must not be described as having zero cost on pages
without images. Measure it, including a node-heavy page, rather than infer a
competitive performance result from a small source diff.
