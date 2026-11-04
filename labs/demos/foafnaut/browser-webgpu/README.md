# Lean SVG on browser WebGPU

A local, editable Solving experiment. One SVG document can be viewed through
two backends: the browser's SVG implementation and the Lean SVG compiler plus
raw WebGPU. The canvas uses `putImageData` only to present the GPU's returned
pixels. The browser preview receives the same committed source bytes as the
Lean compiler.

From the repository root, with Node 22.22 or later and the existing lab engines:

```sh
node labs/demos/foafnaut/browser-webgpu/server.mjs 8097
```

Open <http://127.0.0.1:8097/> in a browser with WebGPU enabled. The server binds
only to IPv4 loopback. It serves an explicit file allowlist and accepts GET/HEAD
only. No external dependencies are fetched by the page. Node strips TypeScript
syntax when serving the existing bridge modules; it does not replace their logic.

Choose **Solving · layered browser view**, edit the SVG, or open a local SVG
file (up to 1 MiB). The scene has separate `<g>` groups for browser shell, page
content and interaction overlay. Both views update only after Lean accepts and
renders the current source. The browser view shows its SVG output; the GPU
view uses the Lean-generated shader and render plan. Edit a fill, coordinate or
group and compare the two backends. Use Render scene or Command/Control+Enter.
Source edits clear both old outputs. Save PNG exports the last GPU frame.
Unsupported features stop the Lean render; the platform view is not used as a
fallback for the GPU result.

Open **Inspect the Lean scene tree, shader and runtime evidence** to see the
retained groups and their local affine matrices emitted by Lean. This field is
optional so older compiled WASM artifacts can still render. The 2026-11-02 local
rebuild populates it, and the browser smoke requires the three named scene groups
and all 46 paint nodes. Lean omits this inspection field above 16,384 retained
nodes to bound the extra transfer. The browser only formats the returned JSON.

This demonstrates a shared SVG wire model and browser-facing backend choice.
The Lean source now represents nested SVG groups and local transforms as a
retained tree, then proves the cached painter list used by the renderer is its
lowering. The 2026-11-02 browser check uses freshly linked WASM and inspects the
returned tree. It does not yet demonstrate a browser
HTML/layout engine, separate compositor surfaces, or pixel equivalence. The
browser SVG renderer and the GPU path still interpret the source independently.

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

These are build products, not source files to commit. The 2026-11-02 local check
uses rebuilt artifacts after the wasm32 runtime-cache and retained-tree traversal
repairs. `/provenance.json` reports SHA-256 hashes of every
served input and the main Lean source files. This identifies bytes but does not
prove that warm artifacts correspond to all current source dependencies.

A static published package needs `index.html`, `app.mjs`, `worker.mjs`,
`style.css`, the four fixture SVGs under `fixtures/`, the three stripped bridge
modules at `lab/{svg_engine,gpu_transport,render_plan}.ts` served as JavaScript,
and the four runtime artifacts under `lab/.build/engines/`. Preserve these relative
paths or rewrite imports in a build step. `provenance.json` must then be captured
from the exact staged inputs and labelled with the build/source commit.
Generate that package in factoidal-builds; do not check generated JS/WASM into
factoidal-core. Production hosting must serve WASM with `application/wasm` and
the `.ts` bridge URLs as JavaScript, over HTTPS (localhost is accepted locally).
The local server CSP permits only same-origin assets and WASM compilation.

## Assurance and validation, 2026-11-02

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
  /tmp/factoidal-browser-webgpu.png \
  --report /tmp/factoidal-browser-webgpu.json --require-tree
```

Measured on Chrome 156.0.8078.76, Apple `metal-3`, non-fallback: the required
retained-tree check, real GPU rendering, fixture switching, source-edit
invalidation, unsupported SVG refusal, keyboard recovery, manual shader fault,
invalid-WGSL cleanup, full-image reset, desktop alignment, narrow-screen stacking,
provenance and server checks all passed. The screenshot was inspected.

The rebuilt SVG WASM SHA-256 is
`cc304ebc359a29da36657fbe462f983b3a32cfeb27a9900b016b915ccbaa03fb`;
render-plan WASM is
`eed9715dc12ba25e4a13d958a26dd2de649c724087a487b118cbdc05fb116f96`.
The measured `SVG.lean` source SHA-256 is
`1a0e9f745bc4cd7c6feca3b1e4fe2b390e3c8b081687accf28e3e22f885521bf`.
The source checkout was dirty; the build and browser reports retain its file
hashes and artifact identities. These local checks do not establish a published
release or a proof of host/GPU correctness.

The complete 640×420 browser/GPU image comparison still differs at 668 of
268,800 pixels, with maximum channel difference 47. All differences are adjacent
to browser raster edges in a 3×3 neighborhood; none occur in flat browser-color
regions. This localizes the discrepancy but does not prove an anti-aliasing-only
cause or pixel equivalence. The six Lean sample checks pass. See the
[dated harness measurements](../../../../docs/20261102-svg-browser-harness.md)
for the unchanged 38-case WPT score and separate sensitivity controls.

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
