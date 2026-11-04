# Lean-rendered links and click logging

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared Lean web
renderer). This extends the [first image slice](20261102-lean-web-renderer-first-images.md).

HTML anchors with an `href` now default to blue text and an underline.
Author CSS can change their color or text decoration. Anchors without `href`
keep normal text behavior; `href=""` remains a link. Underlines are geometry
in the same retained scene as the glyphs.

Lean layout emits `Scene.links` from visible word fragments, retained collapsed
spaces and replaced-element boxes. Each fragment resolves its nearest actual
HTML DOM anchor and keeps that node's stable arena index and exact `href`.
The coordinates come from the same line baseline/layout as painting and are
clipped to the viewport. The browser transports canvas coordinates and the
unchanged Lean region records to the new Lean WASM picker. It does not read
browser DOM layout of the input document or implement its own link selection.
The pointer cursor appears only for an actual picker hit.

A click logs URL, source node and coordinates in the browser console and sends
one same-origin JSON event to the loopback server. The server writes one
JSON-escaped record to stdout. It does not fetch the URL or navigate. Events
are bounded to 16 KiB, hrefs to 2,048 UTF-8 bytes, and source/coordinate fields
are checked. The endpoint rejects foreign origins and malformed records.

`anchorAncestor_is_anchor` proves the resolved target is an actual HTML anchor
with an href attribute and that the returned string is that attribute value;
its only printed axiom is `propext`. `hitLink_mem` proves a successful picker
returns a region from the supplied common scene; it uses only the standard
Lean axioms `propext`, `Classical.choice` and `Quot.sound`.

The targeted build passed 28 style/layout guards and four picker-transport
guards. Actual Chrome/WebGPU `check-links.mjs` then passed six named groups:
wrapped word/space regions resolve the same anchor; blue underlines and red
CSS overrides are painted; non-href anchors have no underline, pointer or
click; inherited `currentColor` reaches an affine-mapped embedded SVG inside
an HTML anchor; four clicks reach console and server without navigation; and
invalid origins/records are rejected. Local evidence:
`/tmp/factoidal-web-links-gpu-20261102/report.json` and `links.png`.

This is pointer activation/logging for the admitted layout profile. Keyboard
activation, navigation, visited-link state, full browser `pointer-events`,
selection and internal SVG anchor elements remain outside this slice.
HTML stylesheet rules that target embedded SVG descendants are explicitly
refused until their cascade is unified; inherited HTML color/visibility at
the SVG root are passed into the existing SVG style reader. The temporary
font profile remains ASCII bitmap. The earlier native CLI is deliberately
frozen for the corpus run; these new link claims exercise the rebuilt WASM.
