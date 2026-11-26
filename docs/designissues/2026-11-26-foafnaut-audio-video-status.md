# Foafnaut: Web Audio, audio for media, and GPU video (status, 2026-11-26)

Owner, 2026-11-26, verbatim: "ok if we want to add an AudioContext and in general have audio for
playing video, and accelerated gpu for video files, how are we doing?"

Tracking: https://github.com/danbri/factoidal-core/issues/588 (media: audio and video in pages,
MSE, WebRTC; 7 stages, Web Audio is stage 7). Earlier records:
[2026-11-08-media-wasmvm.md](2026-11-08-media-wasmvm.md) (decoders in WasmVM) and
[2026-11-14-webgl-webcodecs.md](2026-11-14-webgl-webcodecs.md) (WebCodecs object model).

Result: none of the three works in a page on `main` (`225aa179`). Decoders exist outside the
engine. The page side, the audio output of the Mac host and GPU video are not started.

## 1. What exists

| Part | State | Source |
|---|---|---|
| Opus, Vorbis decode | In WasmVM, 2.3 to 3.5 times real time (Apple M1); samples within 1 of 32,768 of FFmpeg's | media-wasmvm record |
| VP8 decode | In WasmVM, byte-identical to libvpx; 35 fps at 160x90, 10 to 12 fps at 320x180 | media-wasmvm record |
| Ogg, WebM (Matroska) readers | Lean (`Media/Ogg.lean`, `Media/WebM.lean`) | media-wasmvm record |
| I420 to RGBA | Lean, on the CPU (2.5 ms a 320x180 frame) | media-wasmvm record |
| Decoder Wasm modules (libopus, libvorbis, libvpx; 377 KB) | Not in any repository; built on one machine by `tools/wasmvm/build-media.sh`; whether to vendor them or build them in CI is an open owner decision (2026-11-08) | media-wasmvm record |
| `HTMLMediaElement`, `MediaError`, `TimeRanges`, `Audio()` | In the page's JavaScript with no decoder: `canPlayType` answers "", `load()` ends in the source-not-supported steps, `play()` rejects | `docs/designissues/2026-11-14-dom-html.md`, step 12 |
| `<video>` in layout | A replaced box of the right size; no frame drawn | issue 588 |
| WebCodecs | Object model, layouts, `copyTo`, colour spaces, PCM `AudioDecoder` in Lean; no video or compressed audio codec | webgl-webcodecs record |
| `AudioContext` and the rest of Web Audio | Not present: no Web Audio name in the realm data or the prelude | `WasmVM/Hosts/LeanJSRealmData.lean`, `tools/wasmvm/quickjs/prelude.js` |
| Audio output of the Mac host | None. No AudioToolbox, AVFoundation or CoreAudio code in `labs/demos/foafnaut` | search of the tree |
| Hardware video decode, GPU colour conversion | None. No VideoToolbox, CoreVideo or IOSurface code | search of the tree |

WPT, full macOS run `20261113T2212Z` (core `6dde36491`,
`tests/browser-wpt/wpt-full-20261113-6dde36491.json`): `webaudio` 671 of 5,877 Chrome subtests
passed, `webcodecs` 7 of 3,922. The `webaudio` passes do not come from a working context (there is
none); which checks pass without one was not examined. Newer per-directory numbers are on branch
`wpt-scores` of `danbri/factoidal-builds` and were not read for this record.

## 2. What each goal needs (proposal; not started)

### Audio output (needed by all three)

A sink in the Mac host: an AudioQueue or an AudioUnit whose callback reads a ring buffer of PCM
that the engine writes. The callback must not block or allocate. The host plays samples; Lean
makes them and decides when. This is the "audio output" step of the media-wasmvm record.

### `<audio>` and the sound of `<video>`

Issue 588, stages 1 and 2: fetch, demux in Lean, decode in WasmVM, the sink above, the audio clock
as the master clock, `currentTime` and the media events. Blocked by the decision on the decoder
modules (section 3, item 1).

### `AudioContext`

The graph renders in Lean in blocks of 128 frames (the render quantum of the Web Audio API).
First `OfflineAudioContext`, which needs no audio device and lets the WPT `webaudio` tests run in
the cloud; then a real-time `AudioContext` that writes the same blocks into the sink, from a Lean
task. `AudioWorklet` runs page script on the rendering thread and comes last.

### GPU video

Software decode in WasmVM is 10 to 12 fps at 320x180; 1080p has 36 times the pixels. Two routes:

1. Faster software decode: the WasmVM speed work, or the Wasm-to-C route of
   [2026-11-08-wasmvm-aot.md](2026-11-08-wasmvm-aot.md) section 7 for fixed guests such as the
   decoders. The colour conversion moves to a WGSL shader that Lean emits.
2. Hardware decode through the operating system (VideoToolbox on macOS): H.264 and HEVC on every
   Apple Silicon Mac, AV1 on M3 and later (VP9 not checked). Lean keeps demux, timing, sync,
   layout and compositing; the host gives frames for compressed bytes. First step: copy the
   decoded planes into GPU textures and convert colour in a Lean-emitted shader. A path with no
   copy needs a host change that was not checked in Deno's WebGPU.

## 3. Decisions for the owner

1. The decoder Wasm modules: vendor them (377 KB) or build them in CI. Nothing plays until one
   is chosen.
2. May the Mac host use the operating system's hardware video decoder? The rule of
   [2026-11-08-wasmvm-aot.md](2026-11-08-wasmvm-aot.md) section 6 lets the host execute work that
   Lean decides (GPU shaders) and forbids the host implementing web features (a host `<video>`).
   A hardware decoder is between the two: Lean decides everything except the decoding of the
   compressed bytes. With the system decoder, no H.264 or HEVC code ships; the patent question of
   issue 588 stage 5 (MP4) is then a different question, and it stays the owner's.
3. Order: issue 588 puts Web Audio last (stage 7). If `AudioContext` comes first, the sink and
   `OfflineAudioContext` can start without decision 1.
