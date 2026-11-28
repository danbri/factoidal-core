# Foafnaut native desktop prototype

[Issue #1233](https://github.com/danbri/factoidal-core/issues/1233) tracks a desktop host that runs without Deno or V8. The first checkpoint is a Rust executable that calls the native BubblePopKit C API directly.

## Engine checkpoint

Run the executable from the repository root with the native engine library from the Foafnaut 0.38.1 release bundle:

```sh
cargo run --locked --release --manifest-path labs/demos/foafnaut/native-desktop/Cargo.toml -- /path/to/libweb-render.dylib
```

On Linux x86-64 use `libweb-render.so` from the corresponding release. The [macOS bundle](https://github.com/danbri/factoidal-builds/releases/tag/build-bd0d78dd12ff-foafnaut-darwin-arm64) and [Linux bundle](https://github.com/danbri/factoidal-builds/releases/tag/build-bd0d78dd12ff-foafnaut-linux-x86_64) both come from core commit `bd0d78dd12ff`. The smoke workflow checks the archive digests.

The fixture starts in two separate engine sessions. The host asks for the fresh script setting and checks that the engine chooses BubblePopJS. It forwards a click at a known point through the engine's hit test and applies the returned DOM commands to the next scene request. It checks the new scene's data, closes the first session, then checks that the second session still draws the original scene and handles its own first click. These are runtime checks. This checkpoint changes no engine code or proofs.

The prototype reports milliseconds from before loading the library to the first scene answer. This includes JSON decoding and provides no display latency measurement. A comparable measurement needs a common rendering and presentation endpoint in both hosts.

## Window and GPU milestone

Reuse the AppKit window bridge on macOS and use a Linux window surface for the same fixture. The engine already supplies WGSL and scene data. Its existing RenderPlan contract also supplies pipeline descriptors and the command sequence. The native host needs access to that plan before it can drive `wgpu` with the same inputs as the existing host. The window must forward actual pointer events and present the two resulting frames. The cross-platform comparison then uses the same engine build, fixture and viewport for startup, first frame, frame time, input latency and peak memory.

The engine checkpoint uses local data. The transport milestone in issue #1233 covers engine-owned redirect, address, TLS and proxy policy.

## Native render plan

`web_render_plan` is a native entry point to the existing Lean render-plan generator. It accepts the viewport, scene float count, surface format and actual device limits. It returns the same JSON contract used by the existing host and uses `web_render_free` for returned storage. The plan module initialises on first use.

Lean's new `svg-window` mode uses the storage-backed scene format and a presentable surface. The `svg_window_commands` and `svg_window_resources` theorems establish the command sequence and resource types. The existing `Plan` fields still carry the device, buffer and scene-size bounds. These proofs concern Lean's plan. The ABI smoke check uses a native build from this branch and verifies a real scene's accepted plan and a refusal when the supplied storage capacity is zero:

```sh
cargo run --locked --release --manifest-path labs/demos/foafnaut/native-desktop/Cargo.toml -- /path/to/libweb-render.dylib --check-render-plan
```

The Rust probe only forwards facts, parses the answer and asserts the expected contract for its fixed fixture. The presentation adapter will dispatch the plan's operations to the GPU and surface.

## Presenting the fixture

The Rust window adapter opens the existing AppKit or SDL bridge and creates a `wgpu` surface from its native handles. It passes the acquired device's capabilities to `web_render_plan`, uploads the engine's two scene byte streams and dispatches the resulting GPU commands. It checks that the answer corresponds to the scene and stops on an unsupported descriptor. The tile binding follows the existing `lean-svg-v1` shader ABI.

For a matching engine build with `web_render_plan` and its native window library:

```sh
cargo run --locked --release --manifest-path labs/demos/foafnaut/native-desktop/Cargo.toml -- \
  /path/to/libweb-render.dylib --window /path/to/libnative-window.dylib
```

Use the corresponding `.so` libraries on Linux. The fixture opens with a red swatch. Press and release the button to change it to blue. Native pointer coordinates go through Lean's `nodeAt` and `scriptSession` operations before the host requests a new scene. Window resize sends a viewport update to the same engine session. The window mode uses one local fixture. Real network transport, touch, audio, general page scheduling and paired timing measurements remain in issue #1233.

The Linux window check uses an isolated Xvfb display and sends a real X11 pointer click. It samples the displayed swatch before and after the click through the X server. It needs `xvfb-run`, `xdotool`, ImageMagick's `import` and a Vulkan driver, such as Mesa's software Vulkan driver on CI:

```sh
labs/demos/foafnaut/native-desktop/smoke-linux-window.sh \
  /path/to/foafnaut-native-desktop /path/to/libweb-render.so /path/to/libnative-window.so
```

## Timers and the audio wake path

The native event loop uses the engine's `clock` and `nextWake` from every script
turn. It waits for a window event or the requested wake, then supplies elapsed
monotonic time through `scriptSession advance`. Lean chooses which callbacks run,
including the turns that bring audio output events back to the page. The headless
smoke covers a real BubblePopJS timer using the same wake implementation.

To exercise real-time audio without opening an audible device, use
`FOAFNAUT_AUDIO_SINK=null` and pass `--check-audio` to the host. The test sends a
trusted click to the fixture, lets the engine render a tone and checks that the
sink consumed frames and the page observed the context close. The sink and
autoplay policy are the existing engine implementation. The smoke does not
measure waveform fidelity or exercise a physical audio device.
