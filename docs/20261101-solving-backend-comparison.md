# Solving: one SVG scene, two rendering backends

This is the first visible Solving slice for the browser-scene rendering idea.
Run the local page from `labs/demos/foafnaut/browser-webgpu/README.md`. Its
default fixture is `solving-browser-scene.svg`, a page-like composition split
into three SVG groups: `browser-shell`, `page-content` and
`interaction-overlay`.

After the Lean renderer accepts the document, the page shows the committed SVG
source in two places. The browser's SVG implementation renders the source as an
image. The second path sends the same source to the Lean WASM SVG compiler,
which creates geometry buffers and WGSL, then uses the Lean render plan and the
WebGPU bridge to produce pixels. The TypeScript host transfers source and
buffers, executes the plan, and presents returned pixels. It does not compute
shape geometry.

This makes one portable graphical document the visible input to multiple
renderers. Its current limit is that SVG source is the shared wire format; it
is not yet a shared retained scene tree emitted by an HTML parser/layout engine.
The browser and Lean parse the same document independently. The GPU path checks
selected samples against Lean's CPU sampler. No theorem or current comparison
proves that the browser SVG renderer, Lean sampler and GPU agree on every pixel.

The three groups retain their grouping in the browser source. Lean now parses
them into the nested `NativeSVG.DisplayNode` tree, preserving IDs and local
transforms. `NativeSVG.Scene` also keeps the painter-ordered primitive list
used by today's renderer; a proof field ties this cached list to the tree
lowering. Solving's retained envelope round-trips the tree without flattening.
The Lean artifact now includes this retained tree as optional inspection data
when it has at most 16,384 nodes, and the local page displays that data beside
the shader. The older compiled WASM artifact does not yet emit this field, so
rebuild the engine to see it. Larger scenes still render; Lean omits only the
optional inspector field.
The current renderer still flattens for drawing: there are no isolated group
surfaces or group-opacity semantics yet. The visible overlay is ordinary SVG
geometry and does not establish browser hit testing, CSS layout, text shaping
or event routing. The checked-in browser demo still uses the previous compiled
WASM artifact until the engine is rebuilt.

The fixture uses only elements and attributes admitted by the current reader.
This page is a local experiment; it is not a published demo or a claim of SVG
profile conformance.
