# Dynamic font requests, 2026-11-03

The dynamic font frontend uses the existing Lean HTML parser, stylesheet reader,
computed styles and `Layout.inlineItems` scanner. `WebRenderFontRequests.collect`
returns the exact text/family/integer-size requests needed by the current inline
layout profile, including retained spaces and block strut metrics. It skips
hidden display subtrees and SVG descendants. SVG text remains outside this HTML
font path. The public JSON schema is `factoidal-font-requests-v1` with a
`requests` array of `{family,pixelSize,text}` objects.

The host `tools/font-broker.mjs` consumes this typed request JSON. It does not
receive or parse HTML. It binds one exact family to a local font file and calls
the existing HarfBuzz/FreeType `font-shape` adapter for each distinct request.
It returns the unchanged `factoidal-font-data-v1` records as an array, accepted
by the existing typed Lean `FontProvider.Face.decode`. The adapter's real font
hash, metrics, glyph advances, offsets, outlines and grayscale coverage survive
this transport. Lean performs CSS layout, line breaks, source span assignment,
scene construction and rendering after font data returns.

`createFontBroker({adapter,fonts})` permits an explicit deployment font map.
The default binds Arial to the local macOS Arial file; `FACTOIDAL_FONT_FILE`
can override that file. A file reporting another family is refused. The current
Lean layout takes one face per document, so multiple families are refused.
Generic CSS family matching, fallback, variable-font axes, font weight/style
selection, full bidi paragraph layout and fractional raster sizes are not
implemented. RTL runs and missing glyph zero are refused. The Lean request frontend uses
the existing Unicode bidi property table to refuse mixed Latin/RTL words and
directional embedding/isolate controls even when the shaper would guess LTR. No system font is
copied or committed.

Request bounds are 4,096 distinct requests, 65,536 UTF-8 bytes per word, 256
bytes per family, 1MiB aggregate request text, and integer sizes 1 to 512.
Output and host LRU cache are bounded at 16MiB. Adapter jobs are serial, take at
most 30 seconds each, and invoke the binary directly without a shell. The Lean
decoder separately checks transport size, identity, metrics, outlines, clusters
and aggregate resource counts before a scene can consume the data.

Validation on the local native adapter: `node --test
labs/demos/foafnaut/tools/test-font-broker.mjs` passes five tests. These use the
real Arial file and font libraries, verify changed text and size records,
nonlinear outline commands, stable font hash, cached data equality and queue
recovery. They reject missing glyphs, RTL, unsupported families, duplicate and
malformed requests, and allow a text-free request array without shaping.
The full native/wasm render and browser gates are recorded by the integration
owner after the ABI export is linked.

The targeted Lean build (`FontRequests`, `FontRequestsTests`, `BidiData`) passes.
The new frontend compiles to `.olean` and C, and its guard tests pass. Both
`collectDOMWithRules` and `compile` depend only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. `collectDOMWithRules(dom,rules)`
lets the document adapter supply the same resource-aware CSS rules used by the
final render, after script commands have changed the Lean DOM.

A native end-to-end check used a new HTML source containing `November2026 café
<span>office</span> edited`, Arial at 20px and the span at 28px. The new Lean
request frontend produced five requests: space plus three 20px words and
`office` at 28px. The host broker produced 27,296 bytes of actual font data
(hash `525979822591a3447cfc49d943d6f7683508e25543407871c0ed8fed05fd2bd9`).
The rebuilt native renderer consumed those records with `--font-data --pixels`
and returned a 420×100 image with 126,000 RGB components and 6,141 nonwhite
components. The PNG converted from those raw native components was inspected:
the text, accent, curves, distinct span size and shared baseline are visible.
Temporary evidence is `/tmp/font-dynamic-{mvp.html,requests.json,data.json,
pixels.json,native.png}`. This check uses a short `lake env lean --run` driver
for the request ABI; the integrated native CLI and browser gates remain the
integration owner's work.

The document transaction guard suite now checks embedded/external CSS source
order, author `!important`, inline `!important`, missing/duplicate/malformed
resource refusal, disabled and print sheets, unsupported media refusal, first
base selection and relative stylesheet/script URL resolution. It also checks
that a DOM text command changes requests collected with supplied external CSS.
The optional runtime driver passes with the actual Arial record file above:
changed text reaches the actual-font scene, and stale text is absent. The
transaction entry points retain only the same three standard axioms.

The Lean frontend selects the existing bitmap profile when all requested CSS
families are `monospace` or `ascii-bitmap`; it emits no host font requests for
that case. It refuses a mixture of bitmap and supplied families. The host does
not bind a generic family to Arial or rewrite CSS. New guards cover both cases.

`web-render/check-document-fonts.mjs` exercises the linked native and WASM
transaction ABIs with the same requests and compares complete JSON results. It
fetches no page and runs no browser DOM APIs. It obtains exact resource node
handles from Lean inspection, applies typed text commands, supplies ordered CSS,
uses the actual-font broker for fresh words and sizes, compares emitted scenes,
and checks a second arbitrary edit plus resource/bidi refusal controls.
