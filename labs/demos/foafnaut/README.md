# Foafnaut native graphics lab

Lean owns scene generation, geometry, SVG parsing/paint, interaction state,
spring physics and responsive card layout. Deno is the native CPU/WASM host and
raw WebGPU transport. The macOS window shim only handles Cocoa windows, input,
visibility and Core Animation readiness. There is no browser, webview, HTML,
Canvas, Skia, or JavaScript geometry implementation.

This lab is experimental. Full SVG and browser behavior remain goals, not
claims about the current implementation. SVG scope and refusals are in
[SVG_README.md](SVG_README.md). Local tests, official-suite input audits, and real
GPU observations are separate evidence classes.

## Run a native release directory

Keep the three executables, Cocoa sidecar, launchers and fixtures together.
Double-click `Native Demos.command` for springs/layout/vectors, the dedicated
mode launchers, `Lean Still.command`, or `SVG Demo.command`. From Terminal:

```sh
cd PATH_TO_EXTRACTED_RELEASE
./native-webgpu-ui-darwin-arm64 --demo springs
./native-webgpu-ui-darwin-arm64 --demo layout
./native-webgpu-ui-darwin-arm64 --demo vectors
./native-webgpu-lean-darwin-arm64 render-lean.ppm
./native-webgpu-svg-darwin-arm64 svg-fixtures/gallery.svg render-svg.ppm
```

Springs: click/drag nodes, Space pauses/resumes, R resets. Layout: resize to
reflow, click cards to select, R clears. Vectors: click/drag the circle or pink
control handle, Space animates, R resets. Selection persists after release;
capture does not. Escape/window-close exits. Controls also appear in Terminal
and the native window title. Text shaping/fonts/CSS layout are not implemented.

The native window uses a persistent device/pipeline/buffer/bind group. Lean emits
WGSL once per mode, then data/commands. There is no per-frame shader compilation
or CPU pixel readback. Springs uses deterministic fixed-point damped Hooke
physics with 10 ms steps and bounded eight-step catch-up; layout computes twelve
responsive cards in Lean. Still images render offscreen, check Lean reference
pixels, save PPM, and open the result on macOS; `--no-open` suppresses preview.
No GPU adapter means exit 2 and no image; no CPU-rendered fallback is substituted.

Headless checks do not request a GPU/window:

```sh
./native-webgpu-ui-darwin-arm64 --demo springs --check-engine
./native-webgpu-ui-darwin-arm64 --diagnose
./native-webgpu-lean-darwin-arm64 --emit-artifact still.json
./native-webgpu-svg-darwin-arm64 svg-fixtures/gallery.svg --emit-artifact svg.json
shasum -a 256 -c SHA256SUMS
```

`--check-engine` works for all three interactive modes. `--diagnose` loads the
sidecar and checks the OS main thread; it does not create a window or validate
presentation. Launchers `cd` to the release directory: Deno's relative baked
read/FFI permissions then remain valid when the package is moved, including paths
with spaces. The UI allowlist covers only `./libnative-window.dylib`; it still
requests the already-required pathless surface FFI permission **before** any
window can take focus. Declining it creates no window. No broad FFI compile
permission is baked in. Still/SVG tools have read/write permissions and subprocess
access restricted to `/usr/bin/open`, with no network/environment/FFI grant.

## Build engines on Linux or macOS

Prerequisites: the repository's Lean 4.33.1 toolchain, Emscripten 6.0.8, Deno
2.9.4, Bash, Git, and a C/C++ compiler. Cold runtime preparation also needs the
libuv development headers used by the existing WASM build. Version pins are in
`toolchain-versions.env`; Lean follows `formal/lean4/lean-toolchain`.

```sh
labs/demos/foafnaut/build-engines.sh
labs/demos/foafnaut/test.sh --skip-build
```

All outputs are ignored under `.build/`: C, .olean, objects, engine glue/WASM,
native comparison JSON, provenance and native packages. No generated binary,
WASM, C output, logs or evidence JSON belongs in git. Sources and fixtures are
under this lab; XML imports come from this same checkout's
`L4Factoidal.XML.NamespaceView`, not a copied XML parser or another worktree.

The cold path invokes the existing `formal/lean4/Wasm/build-wasm.sh` with
`L4_WASM_RUNTIME_ONLY=1`. This skips the full Factoidal Lake/corpus build and
stops after preparing pinned runtime, Init and Std objects (steps 1–5), without
installing shipped WASM assets. Its normal positional work-directory argument
and `L4_WASM_WORK` default still work. Then the lab regenerates the small current
XML source closure and Graphics/UI/Demos/SVG modules only.

Share an already-built runtime cache to avoid rebuilding it:

```sh
labs/demos/foafnaut/build-engines.sh --runtime-cache PATH_TO_RUNTIME_CACHE
# Equivalent environment:
FACTOIDAL_WASM_RUNTIME_CACHE=PATH_TO_RUNTIME_CACHE labs/demos/foafnaut/test.sh
```

Precedence is `--runtime-cache`, `FACTOIDAL_WASM_RUNTIME_CACHE`, `L4_WASM_WORK`,
then `.build/runtime`. A supplied cache must match pinned Lean runtime headers.
`EM_CACHE`/other normal Emscripten configuration is honored; no machine-specific
SDK path is assumed. `FOAFNAUT_BUILD_LOCK` can name a coordinator's shared lock;
otherwise the lab uses `.build/lean.lock`. Every Lean invocation runs from the
explicit `formal/lean4` project directory. Cold cache preparation can download
pinned Lean/mimalloc sources; warm lab builds do not rebuild the runtime.

`test.sh` runs portable C coordinate checks, host type checking and actual-WASM
local tests. It builds engines unless `--skip-build` is given. A build emits:

- `.build/engines/{graphics-generator,ui-engine,demos-engine,svg-engine}.{mjs,wasm}`
- `.build/native-artifact.json` for native Lean/WASM comparison
- `.build/source-SHA256SUMS` and `.build/tool-versions.txt`

These are the artifacts needed to transfer Linux-built engines into the same
core checkout on a macOS packaging worker; no C/object/native Lean cache needs
transfer. The four modules use pure string ABIs with explicit owned-result frees.
The two known unused cached runtime IO signature warnings are allowed; any other
link signature mismatch fails the build.

## Package macOS ARM64

Cocoa packaging requires macOS ARM64 with Xcode command-line tools:

```sh
labs/demos/foafnaut/build-executables.sh [OUTPUT_DIRECTORY]
```

The default is `.build/dist`. The script runs local tests, compiles the native
sidecar and three separate executables, and copies launchers/fixtures/docs plus
relative-basename `SHA256SUMS` and source/tool provenance into that directory.
`DENORT_BIN` may point to an already-cached Deno runtime; otherwise Deno uses its
normal pinned runtime download/cache. The source tree never receives release
binaries. Release workflow orchestration belongs in `factoidal-builds`.

For a source-host diagnostic after packaging:

```sh
deno run --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  --allow-read --allow-ffi=./labs/demos/foafnaut/.build/native/libnative-window.dylib \
  labs/demos/foafnaut/run_ui.ts --diagnose
```

The optional `check-native-window-input.sh` posts Cocoa events only to its own
window. It requires a real WindowServer and returns 77 on headless skip; it is
not part of default headless tests. Never call a skip a pass.

## Input, visibility and evidence

The Cocoa bridge maps flipped view-local coordinates to top-left framebuffer
pixels using bounds/backing sizes, preserving signed outside-view coordinates.
Pure C tests cover origins/scales/outside points; WASM replays cover the real M1
trace that exposed the earlier negative-Y error. The view accepts the first
mouse click. Capture release/loss of key focus preserves selected highlights.

The surface receives both real NSWindow/NSView handles. Manual AppKit pumping
flushes CA transactions; visibility/occlusion gates acquisition. A newly visible
static scene redraws; a skipped draw remains dirty and counts no frame. Native
surface failure messages preserve stage, frame count and pointer-free state.
No blind generic-status retry hides a visible-window failure.

Cocoa and surface work must stay on the OS main thread. FFI calls are synchronous,
not nonblocking/Worker calls. Native modal/live-resize handling can temporarily
block this manual event pump. Native handles/dylib remain retained until explicit
GPU cleanup and process exit. This is not a general native UI/accessibility stack.

For diagnostic runs:

```sh
"./Native Demos.command" --trace-input
python3 summarize-input.py --output native-input-evidence.json
```

Launchers preserve a PTY for permission prompts and append `native-<mode>.log`,
with executable/sidecar hashes. Trace logging covers down/up/key transitions and
one drag move per gesture, not continuous idle/animation output. Source users can
pass `--directory .build/dist` to the summarizer; it is read-only unless an output
is requested. Traces count observed input and frames, not general correctness.

## Validation limits

The local lab has 40 passing Deno tests and 12 portable C checks on the measured
warm build. They cover native/WASM artifact equality, graphics transport,
selection/capture, physics replay/energy/step partitions, responsive layout,
permission ordering, visibility, coordinate conversion and the restricted SVG
reader/compiler. The SVG groups are local regressions, not W3C conformance results.
Official fixture audits are recorded in the [external SVG suite](../../../tests/external/svg/README.md),
which reports accepted/refused inputs separately from actual raster comparisons.
A test/reference relation rendered by this same implementation can share bugs;
it is evidence, not an independent conformance proof.

The source prototype has recorded M1 presentation/input traces for all three
interactive modes. A newly built release still needs its own native smoke;
compiled CPU/loader checks do not establish presentation. This integration's warm
engine build, tests, compiled CPU checks and relative-permission relocation probe
have run locally. The cold runtime-only bootstrap and Linux path are provided but
have not yet been measured in this local session; CI must validate them.
