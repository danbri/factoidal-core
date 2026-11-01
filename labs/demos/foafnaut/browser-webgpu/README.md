# Lean SVG on browser WebGPU

A local, editable SVG demo using the same Lean SVG compiler and raw WebGPU
transport as the native screenshot experiment. No browser SVG renderer is used
for candidate pixels. The canvas uses `putImageData` only to present the GPU's
returned pixels.

From the repository root, with Node 22.22 or later and the existing lab engines:

```sh
node labs/demos/foafnaut/browser-webgpu/server.mjs 8097
```

Open <http://127.0.0.1:8097/> in a browser with WebGPU enabled. The server binds
only to IPv4 loopback. It serves an explicit file allowlist and accepts GET/HEAD
only. No external dependencies are fetched by the page. Node strips TypeScript
syntax when serving the existing bridge modules; it does not replace their logic.

Choose a fixture, edit the SVG, or open a local SVG file (up to 1 MiB). Use
Render SVG or Command/Control+Enter. Source edits clear old output and evidence.
Save PNG exports the last successful frame. Unsupported features produce the
Lean compiler's error rather than a fallback to browser SVG.

## Division of work

- `SVG.lean` and dependencies, extracted to `svg-engine.wasm`: SVG interpretation,
  geometry, buffer data, WGSL and expected pixel samples.
- `RenderPlan.lean`, extracted to `render-plan.wasm`: resource descriptors and
  GPU command ordering.
- Existing `svg_engine.ts`, `render_plan.ts` and `gpu_transport.ts`: ABI checks,
  GPU handles and execution of the Lean plan.
- This directory: source editor, fixture/file transport, worker coordination,
  error display and presentation of returned RGBA bytes.

Compilation and WebGPU work run in a module worker. Each explicit render creates
and closes an offscreen session. There is no animation loop, direct GPU canvas
presentation or cross-render pipeline reuse in this page. Display timing includes
CPU readback; it is not GPU-only timing.

## Runtime artifacts and publication

The server requires four existing build artifacts in the sibling
`.build/engines/` directory:

- `svg-engine.mjs`, `svg-engine.wasm`
- `render-plan.mjs`, `render-plan.wasm`

These are build products, not source files to commit. Local testing reuses the
warm development artifacts. `/provenance.json` reports SHA-256 hashes of every
served input and the main Lean source files. This identifies bytes but does not
prove that warm artifacts correspond to all current source dependencies.

A static published package needs `index.html`, `app.mjs`, `worker.mjs`,
`style.css`, the three fixture SVGs under `fixtures/`, the three stripped bridge
modules at `lab/{svg_engine,gpu_transport,render_plan}.ts` served as JavaScript,
and the four runtime artifacts under `lab/.build/engines/`. Preserve these relative
paths or rewrite imports in a build step. `provenance.json` must then be captured
from the exact staged inputs and labelled with the build/source commit.
Generate that package in factoidal-builds; do not check generated JS/WASM into
factoidal-core. Production hosting must serve WASM with `application/wasm` and
the `.ts` bridge URLs as JavaScript, over HTTPS (localhost is accepted locally).
The local server CSP permits only same-origin assets and WASM compilation.

## Assurance and validation, 2026-10-31

This is a restricted SVG implementation. The transport compares six sample
pixels in these fixtures against Lean expectations; that is not a full-image
proof, whole-SVG conformance result, or proof of the browser/GPU implementation.
The page exposes the generated WGSL, per-frame facts and runtime provenance.

The optional integration test uses already installed Chrome and Playwright:

```sh
node labs/demos/foafnaut/browser-webgpu/smoke.mjs \
  http://127.0.0.1:8097/ \
  /absolute/path/to/playwright-core/index.mjs \
  /absolute/path/to/chrome \
  /tmp/factoidal-browser-webgpu.png
```

Measured on Chrome 156.0.8078.76, Apple `metal-3`, non-fallback: real GPU rendering,
fixture switching, source-edit invalidation, unsupported SVG refusal, keyboard
render recovery, provenance endpoint, server allowlist and read-only HTTP all
passed. The screenshot was inspected. No renderer source or binaries were
changed. This is local validation, not a deployed-site claim.

The in-app Browser tool failed during setup with a missing `sandboxPolicy`
parameter. The test therefore used the repository's existing installed-browser
Playwright approach. No browser package was downloaded.


## Exact GPU shader inspection and editing

The WGSL tab receives the exact `code` argument at the shared bridge's
`device.createShaderModule` call, together with the actual vertex/fragment entry
names and compilation diagnostics. These stages share a module. This requires
the optional submission observer in `render_plan.ts` and `gpu_transport.ts`;
packages with older bridges must be updated before advertising this facility.

Editing WGSL enters **manual mode**, disables the original Lean sample-pixel
checks and invalidates the displayed frame. Apply WGSL or Ctrl/Cmd+Enter submits
it. Reset to Lean restores generated code and checks. Decimal float controls
cover finite signed values from −10000 through 10000, including unary negative
literals while leaving binary subtraction unchanged. They exclude integer
indices, array sizes and comments, and debounce rendering by 300 ms. They are experiment
controls, not verified policy parameters. Revision IDs discard superseded
asynchronous results; a compilation error clears the canvas and disables download
instead of displaying an old image as a successful new render.

The recorded localhost experiment passed an actual Chrome/Apple Metal GPU
check: original submitted source equals generated source; an edited shader
changes pixels; dragging a positive float changes pixels again; invalid WGSL
reports compiler diagnostics and removes output; reset restores identical
original pixels and sample checks. This validates the local host and bridge, not
a deployed hub or arbitrary manual shaders. The smoke script now also includes
a negative float drag, but that extension has not been rerun against WebGPU.
`shader-scalars.test.mjs` exercises signed literal selection, finite bounds,
stale positions and float syntax without GPU dependencies.

Component name: **Solving**, an SVG-scene rendering pipeline. Existing URL,
custom-element and module identifiers remain stable. The current demo is an
experimental subset; the name adds no SVG conformance or proof claim.
