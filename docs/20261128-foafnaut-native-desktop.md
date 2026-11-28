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
