# Dynamic font requests in the Lean browser

The browser document transaction has three font phases. Lean first parses HTML,
applies typed DOM commands, reads the supplied stylesheets in document order,
and computes styles. `WebRenderFontRequests.collectDOMWithRules` then calls
`Rendering.FontRequests.forDOM`. That collector uses the rendering layout's
own `inlineItems` text scanner. It requests words, retained spaces and block
strut metrics using computed family and integer pixel size. The host does not
parse HTML, split words, compute style or choose line breaks.

Lean emits `factoidal-font-requests-v1`, an object whose `requests` array holds
`{family,pixelSize,text}` records. Entirely bitmap-family documents emit an
empty array and retain the existing Lean bitmap renderer. A document mixing
bitmap and supplied families is refused. The host never maps generic families
to Arial or changes author CSS.

The native data broker accepts only this request object. An explicit family to
file binding selects the local font. The existing `font-shape` executable calls
HarfBuzz for actual glyph IDs, advances, offsets and source clusters, and
FreeType for actual contours and coverage. Its records preserve the exact font
hash and face identity. The broker returns an array of unchanged
`factoidal-font-data-v1` records. The current default binding is local Arial;
`FACTOIDAL_FONT_FILE` overrides that file. The file must report the requested
family. Font files are not copied into the repository.

Lean's `FontProvider.Face.decode` checks that supplied records form one
consistent face and resource dictionary. Layout then consumes exact text/size
entries, breaks lines, positions baselines and builds the common scene. Missing
entries produce errors. Curves remain canonical quadratic/cubic contours until
the shared backend compiles them. CPU and GPU paths consume the same scene.

The document adapter accepts the same DOM commands and supplied CSS for font
requests and final rendering. This prevents a host from shaping the original
text and then rendering a different script-modified arena. Resource node IDs
come from Lean inspection. Hosts supply fetched stylesheet bytes, and Lean
controls source order and the cascade.

The MVP permits one exact supplied family, horizontal left-to-right layout and
integer sizes from 1 to 512 pixels. It has no CSS family matching, fallback,
weight/style selection, variable axes, color fonts or complete bidi paragraph
phase. Lean uses its existing Unicode bidi property table to refuse strong RTL,
Arabic numbers and directional formatting, including mixed words that a shaper
might otherwise label LTR. The broker also refuses RTL and missing glyph zero.
These are explicit profile limits.

The frontend bounds distinct requests, per-word and aggregate text, family
length and source bytes. The host runs one adapter process at a time, enforces
an output bound and timeout, and keeps a bounded whole-record cache. The typed
Lean decoder independently checks transport bytes, metrics, resource counts,
contours, source clusters and face identity before any supplied data can render.
The standard Lean axioms remain the only axioms of the transaction entry points.

Validation and measured native evidence are in
[the worknote](../20261103-web-render-dynamic-font-requests.md). The linked
native/WASM transaction differential is
[`check-document-fonts.mjs`](../../labs/demos/foafnaut/web-render/check-document-fonts.mjs).
