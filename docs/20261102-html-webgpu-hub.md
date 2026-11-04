# Hub page for the Lean HTML/CSS renderer

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared renderer).

`docs/web/hub/html-webgpu/` now contains the public-page source for
`/factoidal/web/hub/html-webgpu/`: editable original HTML/CSS, examples,
viewport controls, the GPU canvas, source-mapped link activation, layout
inspection and runtime provenance. It uses the existing hub navigation.
Compilation and GPU work run in a worker, so the source editor remains on
the page thread. A public click logs to the browser console and page; it
makes no localhost request and does not navigate.

The runtime files are installed from Builds under the ignored `runtime/`
directory. The public source does not commit binaries or maintain a separate
GPU renderer. The two GPU host modules are generated from the existing
canonical TypeScript transports; all GPU policy remains the Lean render plan.
The exact [runtime contract](web/hub/html-webgpu/README.md) lists the seven
runtime files plus the manifest. Relative module/wasm/fixture paths work with
the `/factoidal/` Pages prefix.

The installed local package used source commit `d63639c6d` and is explicitly
a development package, not a published release. Its renderer wasm SHA-256 is
`7d5ebe19782e5c744a9613dbdff41f1fa32b13f2d8e87aa97a5b4f03f88d1a76`.
The manifest records file hashes, source-witness identity and transport-source
hashes. Publication and runtime release installation are separate steps.

Verification on 2026-11-02:

- Offline Eleventy installation passed. The Nunjucks build passed, copying
  388 assets and rendering three pages, including this page with correct
  prefixed navigation and the unchanged compositor app.
- The existing compositor page test passed: 1 test, 0 failures.
- `check-public.mjs` passed six actual Chrome/WebGPU groups: worker/WASM
  rendering; a hand cursor and source-mapped link console log; CSS mutation
  changes pixels; unsupported font refusal removes stale output; mobile
  layout fits and recovers; and all runtime requests remain same origin under
  the Pages prefix. No POST or navigation occurred.
- The rendered default had 1,746 paint items and 32 glyph runs. Its full RGBA
  hash was `0f2d38feb0ef03228ba4c6591a88e0cf02b637b3dec7f58de2f86d2488a55a42`;
  the CSS control produced a different full image.

Evidence: `/tmp/factoidal-html-hub-public-check/report.json`, `desktop.png`
and `mobile.png`; Eleventy log `/tmp/factoidal-html-hub-build.log`.
The page retains the explicit ASCII bitmap/font and CSS scope statements.
This is a tested public-page preview, not a claim that the page or runtime
has already been deployed publicly.
