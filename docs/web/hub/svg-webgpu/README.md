---
permalink: false
eleventyExcludeFromCollections: true
---
# Hub SVG/WebGPU app integration

Source integration, 2026-11-01. Expected public URL after deployment:
`https://danbri.github.io/factoidal/web/hub/svg-webgpu/`.
This URL is a target, not a publication claim.

The host UI comes from the local `labs/demos/foafnaut/browser-webgpu` experiment.
It uses the `hub-app.njk` layout with its own `appBase` and `appSource`, so normal
hub prose styling does not narrow the editor/canvas layout. It deliberately
loads the small SVG and render-plan engines, not the unrelated core npm engine.
The layout's hardcoded `core 0.27.0` navigation label does not describe these
artifacts; the app reports its own artifact kind and source commit.

No renderer, WASM or generated JavaScript was copied into this directory. The
worker imports shared renderer bridges from a build-produced `runtime/` package.
Lean remains responsible for SVG parsing, geometry, WGSL and GPU commands.
Canvas2D only presents returned GPU pixels. There is no SVG-renderer fallback.

## Eleventy changes for the coordinator

Add explicit passthroughs for these source files (not this README or the test):

```js
for (const name of ['app.mjs', 'worker.mjs', 'style.css', 'runtime-contract.mjs']) {
  eleventyConfig.addPassthroughCopy(`web/hub/svg-webgpu/${name}`);
}
```

When the FOAFNaut source is present in this checkout, use the existing fixture
sources instead of creating a second fixture copy:

```js
for (const name of ['gallery.svg', 'affine.svg', 'linear-paths.svg']) {
  eleventyConfig.addPassthroughCopy({
    [`../labs/demos/foafnaut/svg-fixtures/${name}`]:
      `web/hub/svg-webgpu/fixtures/${name}`
  });
}
```

The release installer/build job must place the graphics web package under a
single gitignored artifact directory. One proposed path, to establish in the
build pipeline rather than pretend already available, is:

```js
eleventyConfig.addPassthroughCopy({
  '../labs/demos/foafnaut/.build/browser-runtime': 'web/hub/svg-webgpu/runtime'
});
```

This artifact directory must contain the files listed below. Missing runtime
metadata gives a specific visible error before attempting to render. A docs-only
source deployment is therefore useful for wiring review but is not a functioning
SVG demo release.

## Runtime package contract

Exactly these seven assets are required by `runtime-contract.mjs`:

- `svg_engine.mjs`, `gpu_transport.mjs`, `render_plan.mjs`
- `engines/svg-engine.mjs`, `engines/svg-engine.wasm`
- `engines/render-plan.mjs`, `engines/render-plan.wasm`

Build the three host bridges from the existing lab TypeScript sources by stripping
only TypeScript syntax. Rewrite their relative imports from `.ts` to `.mjs` and
from `./.build/engines/` to `./engines/`. Compile the engines through the existing
factoidal-builds graphics workflow. Do not write another SVG or GPU renderer here.
The generated JavaScript and engines belong in build artifacts, not git.

`provenance.json` must use this schema:

```json
{
  "format": "factoidal-svg-webgpu-runtime-v1",
  "kind": "release",
  "sourceCommit": "FULL_40_CHARACTER_LOWERCASE_GIT_COMMIT",
  "files": [
    {"path": "svg_engine.mjs", "bytes": 123, "sha256": "FULL_64_CHARACTER_LOWERCASE_SHA256"}
  ]
}
```

The example entry is illustrative: include one real hash/size entry for each of
the seven files. `kind` is either `release` or `development`. Source commit and
hashes identify the package, but metadata itself does not prove source/artifact
correspondence. A development preview from warm artifacts must retain that
qualification and cannot be relabelled a verified release. The installer/build
pipeline must verify hashes; the page validates inventory/schema only. It never
uses manifest paths to select an external executable or module URL.

Serve `.mjs` as JavaScript and `.wasm` as `application/wasm`, with the same relative
layout, over HTTPS. No cross-origin engine dependency is required. The current
hub layout CSP already permits same-origin workers, WebAssembly compilation and
fetches. It is broader than needed for this app; tightening it is a shared-layout
change owned by the coordinator.

## Verified and outstanding

`node --test docs/web/hub/svg-webgpu/runtime-contract.test.mjs` passes two groups:
complete provenance/inventory validation, and explicit missing/HTML-substituted
runtime errors. App/worker syntax checks pass. No browser or large build was run
for this integration. Prior local experiment browser results do not establish
that the generated hub deployment works.

At integration time `source/factoidal-routing` has no `labs/demos/foafnaut` tree.
The existing source is in `source/factoidal-foafnaut`, inspected at commit
`3169b9c05af38c3d4b33a384dcaa6db32b16335c`. Merge the needed lab source into the
release tree and publish/install matching runtime artifacts before the site is
advertised as runnable. Add a hub index entry, then validate the final site under
its `/factoidal/` path prefix and its final serving headers.


## Exact GPU shader inspection and editing

The WGSL tab receives the exact `code` argument at the shared bridge's
`device.createShaderModule` call, together with the actual vertex/fragment entry
names and compilation diagnostics. These stages share a module. This requires
the optional submission observer in `render_plan.ts` and `gpu_transport.ts`;
packages with older bridges must be updated before advertising this facility.

Editing WGSL enters **manual mode**, disables the original Lean sample-pixel
checks and invalidates the displayed frame. Apply WGSL or Ctrl/Cmd+Enter submits
it. Reset to Lean restores generated code and checks. Decimal float controls
cover finite nonnegative values from 0 through 10000, excluding integer indices,
array sizes and comments. They debounce rendering by 300 ms. They are experiment
controls, not verified policy parameters. Revision IDs discard superseded
asynchronous results; a compilation error clears the canvas and disables download
instead of displaying an old image as a successful new render.

The usable localhost experiment passed an actual Chrome/Apple Metal GPU check:
original submitted source equals generated source; an edited shader changes
pixels; dragging its float changes pixels again; invalid WGSL reports compiler
diagnostics and removes output; reset restores identical original pixels and
sample checks. This validates the local host and bridge, not a deployed hub or
arbitrary manual shaders. `shader-scalars.test.mjs` exercises literal selection,
finite bounds, stale positions and float syntax without GPU dependencies.

Component name: **Solving**, an SVG-scene rendering pipeline. Existing URL,
custom-element and module identifiers remain stable. The current demo is an
experimental subset; the name adds no SVG conformance or proof claim.
