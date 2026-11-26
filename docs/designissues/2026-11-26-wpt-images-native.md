# Render scores: the wpt-images-native row

Tracking: https://github.com/danbri/factoidal-core/issues/1163 (Render scores: wpt-images-native).

## What the row measures

`tools/render-dashboard/run.py --only wpt-images-native` runs `tests/browser-wpt/native-reftests.py`.
For each of the 279 HTML relations of the pinned WPT SVG subtree (`tests/external/svg-wpt`), it
runs `web-render-native PAGE 800 600 --resources ROOT --pixels` and compares our image with the
browser's image of the reference page, with the WPT fuzzy limits. The browser images come from
`tests/external/svg-wpt/capture.mjs` (Chrome on macOS, or Chromium on Linux).

## Why the native row is below the wasm row

The rows count different cases. `wpt-images-wasm` counts all 601 relations; at 5fa2cbda0, 35 of
its 39 matches were `.svg` tests drawn by the SVG engine. `wpt-images-native` counts only the 279
HTML relations. On HTML relations at that commit, wasm had 4 matches and native 2. The comparison
method is the same in both harnesses.

## Steps and counts (Linux, Chromium 1243 reference images)

1. 225aa1799: 6 pass, 46 fail, 25 timeout, 66 unsupported, 136 unavailable (out of 279).
2. Harness: the plain HTML mode of the CLI gave the page no subresources, so every `<img>` of a
   local file drew nothing and was counted as "Pixels differ". Option `--resources ROOT` (the
   file policy of `--svg-resources`) and `WebRender.renderWith`. 2741abd21: 9 pass, 46 fail.
3. Engine: an `<img>` of an SVG file ignored an `svgView(...)` fragment (SVG 2, SVG fragment
   identifiers). `WebRender.svgViewOf` reads it; the image store gives such a key to a decoder
   that edits the root element (`viewBox`, `preserveAspectRatio`, a `g` with the `transform`).
   49266437b: 18 pass, 37 fail.

## Open

- The CLI's HTML mode (`WebRender.render`) is not the path that Foafnaut uses
  (`WebDocument.compile`). It draws no CSS `background-image`: 8 failures (the `media-fragment-*`
  tests and `svgview-viewbox-override-multiple`) draw 0 primitives for that reason. The harness
  should measure the document path.
- `svgview-preserveaspectratio-meet`: an SVG image is drawn at its natural size and then scaled to
  the `<img>` box, so its own `preserveAspectRatio` does not apply to the box (CSS Images 3 §5.3
  concrete object size).
- Other failures: nested `data:` SVG images (5), `non-scaling-stroke` (7), text on a path and
  combining marks (8).
