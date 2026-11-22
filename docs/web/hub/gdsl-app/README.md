# GDSL in an independent app

[Open the Hub example](https://danbri.github.io/factoidal/web/hub/gdsl-app/).

This example consumes the public `gdsl.mjs` and `browser.js` modules. It
builds a PVGraph with three general operations:

1. `u32.map.mul`: multiply input A by a constant.
2. `u32.zip.add`: add input B element by element.
3. `u32.scan.sum`: calculate inclusive prefix sums of the mixed stream.

The outputs are `mixed` and `cumulative`. Arithmetic is modulo `2^32`.
Both inputs must have equal lengths. Empty buffers are valid. Construction,
admission, CPU evaluation and GPU planning use the built-in Lean/Wasm engine;
the example has no independent JavaScript operator evaluator.

## Run the Hub locally

Install a matching web runtime through the repository's normal
`tools/fetch-builds.sh` route, or build it with
`formal/lean4/Wasm/build-wasm.sh`. Follow the
[Hub local-runtime instructions](../README.md#mixed-cpu--gpu-sparql-local-runtime-workbench).
Serve the generated site and open `/factoidal/web/hub/gdsl-app/`.

The default package directory is `/factoidal/npm/factoidal/`. The optional
assets directory can select the matching Wasm build before the runtime is
first loaded. Imports are same-origin and the runtime loads only when Run is
pressed. No npm release or CDN module is needed.

The editor permits up to 4,096 words in each buffer. That is a UI limit, not
the language's buffer bound. Use the 2,048-word sample to exercise multiple
parallel scan workgroups. The runtime remains responsible for its own limits.

## Use the computation in another application

`example.mjs` exports a DOM-free recipe:

```js
import {createPVGraphWasm, runPVGraph} from './vendor/factoidal/gdsl.mjs';
import {loadEngine} from './vendor/factoidal/browser.js';
import {buildSignalMixer} from './example.mjs';

const {builder, pvgraph} = await buildSignalMixer({
  createPVGraphWasm, loadEngine, gain: 3
});
const bindings = {a: [2, 3, 5], b: [1, 4, 1]};
const result = await runPVGraph({
  pvgraph, bindings, loadEngine,
  minWords: 0,
  verifyWithLean: true
});
console.log(result.status, result.outputs);
// mixed: [7, 13, 16]; cumulative: [7, 20, 36]

// An explicit CPU run uses the same admitted PVGraph:
const reference = await builder.evaluate(pvgraph, bindings);
```

The Hub's **Copy JavaScript module** button includes the actual recipe
function, so the copied module does not need `example.mjs` or any Hub code.
**Download standalone HTML** gives a complete page with that same program,
the current inputs, error reporting and output display.

Place the repository's `npm/factoidal/` package directory, with its installed
runtime, at `vendor/factoidal/` beside the downloaded `gdsl-example.html`.
Preserve the directory structure, including `lib/`, `l4-assets/`, the package
metadata and public entry points. The Wasm is a build product installed by
the normal build or release-fetch command; do not commit it.

Run this from the independent app directory:

```sh
python3 -m http.server 8080
```

Open `http://localhost:8080/gdsl-example.html`. WebGPU requires a supported
browser and a secure context such as localhost or HTTPS. The reference
evaluator remains available when WebGPU cannot be used.

The package's corresponding bundler imports are
`@factoidal/core/gdsl` and `@factoidal/core/browser`. These exports are in the
repository; publication to npm is a separate release step.

## Execution modes and evidence

- **Automatic** calls `runPVGraph` with CPU fallback permitted.
- **CPU** calls the builder's `evaluate` method directly.
- **Required GPU** sets `requireGPU: true` and reports any device refusal.

The demo sets `minWords: 0` so small inputs exercise device execution. The
public API defaults to 1,024 words; the threshold is not a speed estimate for
an individual device. `verifyWithLean: true` compares all GPU output words
against the reference evaluator. A required-GPU failure clears the displayed
answer and disables report saving. Editing the input also clears the answer.

The bars and table are previews of returned words. A saved JSON report
contains the full inputs, PVGraph, outputs, backend, dispatch count, runtime
information and timings. Engine loading is measured separately from program
construction and execution. Single-run timings do not establish a GPU speedup.

The typed language and pure execution model have Lean definitions and
theorems. Compiler, Wasm host, ABI, WGSL implementation, driver and hardware
remain execution boundaries. A per-input comparison is an observation, not
a proof of those components.

Tracking: [independent application integration](https://github.com/danbri/factoidal-core/issues/741).
