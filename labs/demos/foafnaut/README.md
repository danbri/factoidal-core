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
./native-webgpu-ui-darwin-arm64 --demo foafnaut
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

## FOAFNaut: RDF people in a native window

`FOAFNaut.command` (menu option 4) opens a small graph from real Turtle parsed
by Factoidal in Lean. The included eight-person data is synthetic. A fresh
visual interpretation keeps the historical little-person idea, with a light
canvas, pastel accents, rounded name cards and larger bitmap labels. This is
inspiration from the original, not a pixel-accurate recreation.

Drag name cards to pin people where you put them, including after release.
The plus head reveals only already-loaded direct neighbors; the minus foot
hides only that person and incident links. Neither action moves other people.
R restores the initial radial layout, clears pins, and reveals everyone. Space
pauses/resumes one-sixth easing of unpinned positions. No network fetch occurs.

```sh
# From the source checkout, launchers find the ignored .build/dist package:
"labs/demos/foafnaut/FOAFNaut.command"
# From an extracted native package:
./native-webgpu-ui-darwin-arm64 --demo foafnaut --rdf /absolute/path/people.ttl
./native-webgpu-ui-darwin-arm64 --demo foafnaut --snapshot graph.ppm
./native-webgpu-ui-darwin-arm64 --demo foafnaut --emit-artifact graph.json
```

The graph view supports 16 people / 48 directed links. It preserves RDF identity,
keeps labels separate from identity, and counts invalid literal `foaf:knows`
objects. Default `foaf/fixtures/demo.ttl` has readable ASCII names;
`people.ttl` remains the Unicode/escaping regression fixture. Explicit RDF
names keep priority, including URI-valued literals. Generated fallback names
show a short IRI fragment/path segment or PERSON n. Full original labels,
Unicode and typed IDs remain in the model and selection log. The small
5×7 bitmap alphabet has ASCII letters, digits and punctuation; other characters
show `?`. Labels truncate to the available card width. This is lab lettering,
not SVG `<text>`, font loading or shaping. Self-links are retained in data but
their initial line representation is not a useful visible loop yet.

The navy header has a local RDF address bar. Click it, press Tab, or use
Cmd-L to edit. Enter selects and reveals an exact loaded IRI, typed ID, or
`_:blank` locator. An unknown address leaves a clear local-only status; it
does not start a Web request. Cmd-A/C/X/V select/copy/cut/paste. Arrows,
Shift-arrows, Home/End, Backspace/Delete, Return and Escape operate in Lean.
The address holds at most 512 Unicode scalars and scrolls within 64 fixed
glyph slots; truncation is reported. Paste above 65,536 scalars leaves the
address unchanged and shows a nonfatal status. OS clipboard failures also
show a status. Framebuffer sizes from 16×16 through 4096×4096 retain their
actual dimensions; small windows can clip content but keep pointer coordinates
aligned. This is scalar editing, not full text shaping or IME composition.
Clipboard requests are transient frame effects; the native bridge only moves
clipboard text. Printable committed text and paste replacement happen in Lean.
ASCII lowercase and URL punctuation preserve case, with slightly reinforced
pixel lettering. Original Unicode and RDF identity remain in the model.

See the [RDF adapter](foaf/README.md) and
[original FOAFNaut reference/attributions](foafnaut-reference/README.md).

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
read/write permissions remain valid when the package moves, including paths
with spaces. At the owner's request, the UI is compiled with `--allow-ffi`:
its native surface/window bridge no longer asks on every launch. Source-host
runs without that grant still finish permission preflight before creating a
window. Still/SVG tools have read/write permissions and subprocess
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

- `.build/engines/{graphics-generator,ui-engine,demos-engine,svg-engine,foafnaut-engine,render-plan}.{mjs,wasm}`
- `.build/native-artifact.json` for native Lean/WASM comparison
- `.build/source-SHA256SUMS` and `.build/tool-versions.txt`

These are the artifacts needed to transfer Linux-built engines into the same
core checkout on a macOS packaging worker; no C/object/native Lean cache needs
transfer. The six modules use pure string ABIs with explicit owned-result frees.
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

## Shared geometry and checked SVG (source prototype)

Drawing, hit-testing and node footprints now derive from one Lean shape list.
The shared Factoidal policy accepts bounded application configurations (the
experimental profile allows 3–7% bounding-box overlap and a 12–24 Hz target).
`checkedSnapshot` and `svg` refuse a scene that fails that same checker. The
native FOAFNaut window now uses the Lean live admission controller: invalid
candidates retain the previous approved geometry, viewport changes clear it,
and pointer-down uses the last successfully submitted frame. The older
serialized-model API remains diagnostic. The limits are human-designed and
the cadence is a target, not an operating-system scheduling guarantee.

After building the engines, serve this directory and visit `policy-demo.html`
for the web-component SVG demo. It uses the same Lean WASM and offers the
checked SVG for download. Export that scene and optionally render its SVG
through the native WebGPU path from the core repository root:

```sh
deno run --allow-read --allow-write --allow-run=open --unstable-webgpu \
  labs/demos/foafnaut/run_foaf_svg.ts \
  labs/demos/foafnaut/foaf/fixtures/people.ttl checked.svg checked.ppm
```

Omit `checked.ppm` to export without a GPU. A `.policy.json` companion records
the selected policy and the derived bounds. The exact theorem scope,
adapter contract and remaining gaps are in the
[shared policy record](../../../docs/designissues/2026-10-30-shared-ui-policy.md).
The browser component currently uses checked static exports; its live event
integration is still outstanding. The live native protocol and its validation
are recorded in [the live presentation worknote](../../../docs/20261030-foafnaut-live-presentation.md).

The macOS package includes the static site under `web/`. It also supports
exporting checked SVG without a development toolchain, then feeding that file
to the native SVG renderer (run from the package directory):

```sh
./native-webgpu-ui-darwin-arm64 --demo foafnaut --emit-svg checked.svg
./native-webgpu-svg-darwin-arm64 checked.svg checked.ppm
```

## Earlier validation baseline

The shared-geometry/policy update passed 58 fresh WASM/Deno tests, 12 C coordinate
checks, and all four compiled CPU modes in a relocated Mac package. The packaged
FOAFNaut executable exported checked SVG; the packaged native SVG executable
compiled that file to a storage-buffer artifact. Native geometry/policy proofs,
ten FOAFNaut state groups, four serializer groups and three SVG capacity groups
passed. This update has no new GPU/browser visual pass; the sandbox supplied no
GPU adapter and browser automation could not connect. The figures below describe
the preceding interaction/render-plan build.

The browser/render-plan build measured 51 passing Deno tests and 12 portable C
checks on the warm build. They cover native/WASM artifact equality, graphics transport,
selection/capture, physics replay/energy/step partitions, responsive layout,
permission ordering, visibility, coordinate conversion and the restricted SVG
reader/compiler and RDF-driven graph interaction. The small native FOAF builds
also run 12 RDF adapter and nine graph/editor-state test groups, plus the
RenderPlan kernel proofs and native guards. The SVG groups are
local regressions, not W3C conformance results.
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

## Lean rendering boundary

`RenderPlan.lean` supplies pipeline entries/topology, buffer usage and byte sizes,
bindings, clear/load/store operations, draw arguments and ordered window/offscreen
commands. The shared `render_plan.ts` interpreter maps these values to WebGPU
objects. SVG and the other scenes use this same transport. The accepted plan
proves its uniform capacity and alignment against supplied limits; readback rows
are proved to cover all pixels and obey 256-byte alignment.

The interpreter and device reports remain trusted. Persistent resource lifetime,
resize/visibility/dirty scheduling and error cleanup remain host policy in this
first increment. Theorems do not establish WGSL semantics or GPU output. See the
[render boundary record](../../../docs/designissues/2026-10-30-lean-render-plan.md).
