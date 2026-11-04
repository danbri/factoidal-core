# Public HTML/CSS renderer page

This is source for `/factoidal/web/hub/html-webgpu/`. It uses the existing hub
navigation and same-origin static assets, including when Pages has the
`/factoidal/` prefix. It has no localhost dependency or rendering-service API.
Compilation, layout and picking run in the Lean WASM module in a worker; the
existing GPU transport presents generated pixels. Public clicks log to the
browser console and page. Server stdout logging belongs to the local lab.

The shared lab fixtures are passed through by Eleventy from
`labs/demos/foafnaut/web-render/fixtures/`; they are not maintained twice.

## Runtime release contract

Builds installs these ignored files under `runtime/`, preserving names:

- `web-render.mjs`, `web-render.wasm`: the targeted Lean HTML/DOM/CSS/layout/
  common-scene/SVG engine, exporting `web_render_call`, `web_render_hit` and
  `web_render_free` through Emscripten `ccall`/`UTF8ToString`.
- `render-plan.mjs`, `render-plan.wasm`: existing Lean render-plan engine.
- `gpu-transport.mjs`: TypeScript-stripped canonical
  `labs/demos/foafnaut/gpu_transport.ts`, with its `./render_plan.ts` import
  changed to `./render-plan-host.mjs`.
- `render-plan-host.mjs`: TypeScript-stripped canonical
  `labs/demos/foafnaut/render_plan.ts`, with its engine import changed from
  `./.build/engines/render-plan.mjs` to `./render-plan.mjs`.
- `source-witness.json`: exact source/C/engine byte witnesses from the build.
- `manifest.json`: release/core identity, runtime and transport SHA-256 values,
  input source hashes, tool versions and the witness reference.

Those transport modules are generated artifacts, not another handwritten
renderer. Their canonical TypeScript sources and Lean render plan keep GPU
policy in one place. No runtime binaries or generated transport copies are
committed to this directory. The build must install a complete matching set;
a missing runtime is an explicit load error, not a browser-layout fallback.

The supported font and CSS scope is stated on the page. Link picking consumes
unchanged Lean-produced common-scene regions. It is pointer activation and
logging, not navigation, full event dispatch or keyboard link support.

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared renderer).

## Local verification

Build the Eleventy templates after installing the matching runtime assets.
`check-public.mjs PAGE_URL PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR` exercises the
actual public page worker, same-origin WASM/WebGPU, CSS edits, Lean link
picking, browser console output, unsupported-font refusal and mobile layout.
The PAGE_URL should include `/factoidal/web/hub/html-webgpu/` to test the
published path prefix. This driver is a source test and is not copied to the
public site.
