# Lean HTML/CSS renderer

This local renderer accepts original HTML/CSS source. The existing Lean HTML
parser and DOM arena feed Lean computed styles, block/inline text flow and a
common retained Float vector scene. An explicit adapter feeds the existing
Lean SVG CPU/WGSL renderer. The browser host transports bytes and WebGPU
commands; it does not use browser DOM layout for candidate output.

Build from the repository root:

```sh
labs/demos/foafnaut/build-web-render.sh --native
FACTOIDAL_WASM_RUNTIME_CACHE=/absolute/verified/lean-4.33.1-runtime \
  labs/demos/foafnaut/build-web-render.sh --wasm
node labs/demos/foafnaut/web-render/server.mjs 8099
```

The runtime path must contain the pinned Lean 4.33.1 wasm object closure and
validated string-list patch witness. It is read only. All generated outputs
stay under the ignored `.build/web-render` directory. The script compiles the
specific HTML/DOM/rendering import closure, not the full Factoidal library,
and requires at least 3 GiB free before a heavy build.

Open http://127.0.0.1:8099/ . Edits to source, CSS or viewport dimensions are
compiled by the new Lean WASM engine and change GPU output. The inspector
shows source DOM indexes, layout boxes and consumed glyph runs.

Native CLI:

```sh
labs/demos/foafnaut/.build/web-render/web-render-native INPUT.html WIDTH HEIGHT
labs/demos/foafnaut/.build/web-render/web-render-native INPUT.html WIDTH HEIGHT --pixels
```

The default output is the existing `lean-svg-v1` data/WGSL artifact plus
`webRender` layout metadata. `--pixels` returns a full CPU RGB image, capped
at 1,048,576 pixels. An evaluated unsupported profile returns error JSON;
invalid command arguments or file IO fail the process.

The temporary font profile is original ASCII bitmap outlines, with actual
word wrapping, baselines and source clusters. Real font shaping is a separate
milestone. CSS/layout refusals remain explicit. Embedded SVG initially admits
only untransformed fill rectangles wholly inside their viewport until the
shared clip extension lands. This is a working subset, not a browser or
HTML/text MVP completion claim.

The independent check uses installed Playwright Core and Chrome:

```sh
node labs/demos/foafnaut/web-render/check-browser.mjs \
  http://127.0.0.1:8099/ /absolute/playwright-core/index.mjs \
  /absolute/chrome /absolute/web-render-native /absolute/output-directory
```

It compares a whole GPU image against the whole CPU image and the original
HTML rendered independently by Chrome. It also changes CSS color/width and
text, verifies changed pixels/reflow, and checks unsupported font refusal.
It is a local profile check; upstream WPT results have their own corpus and
unchanged denominator. The browser reference receives the original HTML,
not an extracted SVG or candidate-generated markup.

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared Lean web
renderer). Architecture and exact scope:
[design record](../../../../docs/designissues/2026-11-02-lean-web-rendering.md).
