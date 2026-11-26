# Foafnaut audio: the Web Audio API in Lean, a jukebox, decoders, and the ties to Lean proofs

2026-11-26. Plan. Status before it:
[2026-11-26-foafnaut-audio-video-status.md](2026-11-26-foafnaut-audio-video-status.md). Tracking:
https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut), part of
https://github.com/danbri/factoidal-core/issues/588 (media: audio and video in pages).

## 0. The owner's decisions (2026-11-26, verbatim; also in `CLAUDE.md`)

1. "vendor them into factoidal-builds/ repo third_party/ with provenance version and license info.
   Include wasm and build chain."
2. "Yes. Think about how to tie all this in with Lean proofs to avoid weird weak links." (To: may the
   Mac host use the operating system's hardware video decoder, VideoToolbox?)
3. "Yep, let's get Audio working decently before getting bogged down in the endless woes around
   video, codecs etc. For audio we should be able to fully support the WebAudio API (and eventually
   its use in WebXR). And we should be able to make a simple web jukebox (ideally mp3 covered too).
   If we need an arms length friendly site with the wasm plugins for mp3 mp4 lean-certified we can
   investigate that."

## 1. Goal and measures

- The whole Web Audio API (W3C Web Audio API 1.1). Measure: the WPT `webaudio` directory, 5,877
  Chrome subtests. On 2026-11-13 (macOS full run, core `6dde36491`) 671 passed with no
  `AudioContext` in the engine; those passes are checks that pass without one.
- A jukebox page (`labs/demos/foafnaut/pages/jukebox.html`): a playlist of WAV, MP3, Ogg Vorbis and
  Opus files (CC0 clips made here, and files the person opens), with play, pause, next, seek and
  volume. First on Web Audio (`decodeAudioData`, `AudioBufferSourceNode`, `GainNode`), then on
  `<audio>`.
- Real-time measures, each in the trace and in `--perf-summary`: output latency (ms), under-runs a
  minute (target 0 on an idle machine), engine CPU per playing source, and time from the click to
  the first audible frame.

## 2. Where each part runs

Native first (`CLAUDE.md`, 2026-11-25): the Mac app is the product; the Hub build is not a goal
for audio now.

| Part | Where | What it does |
|---|---|---|
| Page interfaces | BubblePopJS, `prelude.js` | builds `AudioContext`, the nodes and `AudioParam` from a Lean table generated from the Web Audio IDL (as `PageGl.Table` is for WebGL); converts arguments as Web IDL says. Every check (ranges, `InvalidStateError`, `NotSupportedError`, `IndexSizeError`) is decided in Lean |
| Graph state and rendering | Lean | the control thread's view of the graph, and the rendering of blocks of 128 frames (the render quantum) |
| Rendering thread | one Lean dedicated task per running `AudioContext`, in the engine library | applies the control message queue at the start of each block (Web Audio API, "Rendering an audio graph"), renders the block, writes it to the output ring |
| `OfflineAudioContext` | Lean, in the engine, no device | renders N frames and resolves `startRendering()`. It comes first: it needs no device, and the WPT tests run on it in the cloud |
| Output | Mac host: a C sink on CoreAudio; Linux: a WAV-file sink for tests and a null sink | copies frames from the ring to the device. It does not mix, resample or decide anything |
| `decodeAudioData`, `<audio>` | container in Lean, decoder in WasmVM | Lean reads the container and gives the decoder one packet or frame a call; PCM comes back as 32-bit floats into an `AudioBuffer` |
| `AudioWorklet` | a BubblePopJS realm on the rendering task | later stage; its real-time cost is measured before it is offered |
| WebXR audio | `PannerNode`, `AudioListener` moved by the XR pose | later. The HRTF panning model needs a set of measured impulse responses: Chromium, WebKit and Firefox use one derived from the IRCAM Listen database; its licence is checked before any is used. Equal-power panning needs none |

## 3. Codecs for the jukebox

| Format | Decoder | Note |
|---|---|---|
| WAV: PCM, float, A-law, µ-law | Lean | `WebCodecs.Audio` has the sample conversions |
| MP3 | minimp3 (CC0-1.0) in WasmVM, module `mp3-wasmvm.wasm` | Lean reads ID3v2 and ID3v1 tags, the frame headers and the Xing/LAME header (encoder delay and padding, for gapless play) and gives one frame a call. MP3 patents ended in 2017: no separate site is needed |
| Ogg Vorbis, Opus | libvorbis, libopus in WasmVM | as now; the modules of 2026-11-26 add 32-bit float output and every channel (Vorbis: 8 at most) |
| FLAC | Lean (later) | integer only, and each stream carries the MD5 of its decoded samples, so a decode checks itself; a candidate for a decoder with proofs |
| AAC (`.m4a`, MP4) | AudioToolbox, the operating system's decoder (later) | needs the owner's yes: decision 2 named the hardware video decoder only |

The decoder modules, their build chain (Emscripten 6.0.8, source tarballs by SHA-256, flags),
provenance and licences are in `danbri/factoidal-builds`, `third_party/media-decoders/` (decision
1). Lean pins the SHA-256 of each module it loads and checks its interface version (`mw_abi`).

## 4. Ties to Lean proofs

The owner asked for no "weird weak links". The rule for every part that is not Lean:

1. its contract is stated in Lean;
2. Lean checks what goes in (it builds the inputs) and what comes out, at run time;
3. the part is a named assumption in the evidence record of every path that uses it (as for
   "Freeform composition over checked components", `CLAUDE.md` 2026-10-25);
4. a conformance or differential test runs it in CI.

Lean code gets theorems where the property is about indices, lengths, order, counts and time.
Lean's `Float` is opaque to the kernel, so a property of a floating-point value is stated over an
abstract number type (the owner's "prove over an abstraction", 2026-08-24), proved there, and the
`Float` instance is tested against it with `#guard` at chosen points.

| Part | Code | Proved in Lean | Checked at run time | Tested | Named assumption |
|---|---|---|---|---|---|
| Containers: WAV, Ogg, WebM, MP3 frames and tags; MP4 later | Lean | total; every read inside the input; every loop bounded by the input size; timestamps exact (rational) | malformed input refused with a named error | corpus and fuzz | none |
| Decoders in WasmVM | C (libopus, libvorbis, minimp3, libvpx) run by WasmVM | WasmVM semantics: the guest writes only its own memory; fuel and a memory limit end every call | module SHA-256 is a pinned one; samples per call at most the codec's maximum; channels and rate as configured; NaN replaced by 0 and counted | the same C built natively gives the same samples (bit for bit for minimp3 and libvpx); Opus test vectors (RFC 8251); MP3 compliance streams (licence to check) | "decoder D at version V decodes as its specification says" |
| Web Audio graph | Lean | processing order is a topological order of the graph with the edges into `DelayNode`s cut; a cycle with no `DelayNode` gives silence; `computedNumberOfChannels` for the three `channelCountMode`s; the up-mix and down-mix matrices of the specification's table; a scheduled source is zero outside its frames; the `AudioParam` event list (insertion order, `cancelScheduledValues`, `cancelAndHoldAtTime`) | — | WPT `webaudio` on `OfflineAudioContext` | none |
| Automation values and DSP | Lean, `Float` | the specification's formulas over an abstract ordered field: ramps reach their end values exactly and are monotone between them | non-finite values refused where the IDL says (`TypeError`) | `Float` against exact rationals at test points | none |
| Control to rendering messages | Lean channel | messages apply in the order sent, at the start of the first block after they are sent | — | — | none |
| Output ring and sink | C (about 60 lines) and CoreAudio | the ring protocol as a Lean state machine: the reader never passes the writer; each slot is read once; an under-run gives silence | under-runs counted in the trace | stress test under ThreadSanitizer on Linux | "CoreAudio plays the frames it is given, in order, at the device rate" |
| Clock | Lean | `currentTime` = frames rendered / sample rate, never decreasing | — | — | the host's latency figures |
| OS video decoder (decision 2, after audio) | VideoToolbox | Lean parses the parameter sets it hands over (profile, level, size, chroma format, bit depth) and refuses a stream outside the supported set | each picture's size, format, plane strides and time against what Lean parsed; a mismatch ends playback with a decode error | H.264, H.265 and AV1 decoding are bit-exact by their standards, so conformance bitstreams are compared with a reference software decoder on the macOS runner | "VideoToolbox decodes conformant streams as the standard says (N streams, chip, macOS version)" |
| Which decoders may run | Lean `MediaPolicy`, like `FontPolicy` | one value decides; `safe` allows the WasmVM decoders only | a refusal names the codec, the setting and its source | — | none |
| Page interfaces | `prelude.js` | the interface table is generated from the IDL, and the page and Lean read the same table | — | WPT `idlharness` | none |

## 5. MP4 in other open-source browsers

The MP4 file format (ISO base media file format) has no patent question; the codecs in it (H.264,
H.265, AAC) do. What others do:

- Firefox ships no H.264 or AAC decoder for playback. It uses the operating system's decoders
  (VideoToolbox and AudioToolbox on macOS, Media Foundation on Windows) and, on Linux, the FFmpeg
  that the person or the distribution installed. Cisco's OpenH264 binary, which Firefox downloads
  from Cisco and for which Cisco pays the licence, is for WebRTC calls, not for playback.
  Sources: [Mozilla support](https://support.mozilla.org/en-US/kb/audio-and-video-firefox),
  [Bugzilla 1755361](https://bugzilla.mozilla.org/show_bug.cgi?id=1755361).
- Chromium's open-source build leaves H.264 and AAC off (`proprietary_codecs=false`); the party that
  builds with them on (Google, for Chrome) holds the licences. Another setting uses only the
  operating system's decoders. Sources: [CEF issue 3559](https://github.com/chromiumembedded/cef/issues/3559),
  [chromium-dev](https://groups.google.com/a/chromium.org/g/chromium-dev/c/vrqKqsng9Bg).
- Ladybird reads Matroska and WebM itself and uses FFmpeg for the other containers and for
  decoding. Source: [LibMedia history (mirror)](https://remotebranch.eu/Stowage/ladybird/src/commit/6caa2f99aad7a54acac49c3c93368a18542b9e90/Libraries/LibMedia).

For Foafnaut on the Mac this gives: MP4 read in Lean; H.264 and H.265 by VideoToolbox (decision 2);
AAC by AudioToolbox if the owner agrees. No H.264 or AAC code ships. A separate site that hands out
decoder modules moves the licence question to whoever runs the site; it does not remove it. This is
not legal advice.

## 6. Stages

| Stage | What | Measure |
|---|---|---|
| A | Decoder modules vendored in factoidal-builds, MP3 added, float output, interface version 2; Lean pins their SHA-256 | done 2026-11-26 (section 8) |
| B | Web Audio core in Lean: `BaseAudioContext`, `OfflineAudioContext`, `AudioBuffer`, `AudioNode` connections, `AudioParam` with automation, `AudioDestinationNode`; nodes `Gain`, `Oscillator`, `AudioBufferSource`, `ConstantSource`, `Delay`, `BiquadFilter`, `StereoPanner`, `ChannelSplitter`, `ChannelMerger` | WPT `webaudio` before and after |
| C | `decodeAudioData` for WAV, MP3, Ogg Vorbis and Opus; the MP3 frame reader in Lean | WPT `decodeAudioData` tests; decode time per second of audio |
| D | Real-time `AudioContext`: the Mac CoreAudio sink, the Linux file sink, the rendering task | output latency, under-runs a minute, CPU per source |
| E | Jukebox page | time from click to sound; gapless MP3 |
| F | The other nodes: `Convolver`, `DynamicsCompressor`, `WaveShaper`, `IIRFilter`, `Analyser`, `Panner` (equal-power, then HRTF after the data licence check), `MediaElementAudioSource`; then `AudioWorklet` | WPT `webaudio` |
| G | `<audio>` playback on the same pipeline (issue 588, stage 1) | WPT `media-elements` |
| H | FLAC in Lean; AAC through AudioToolbox if approved | conformance streams |

After audio: WebXR audio, then the video stages of issue 588 with section 4's rules.

## 7. Questions for the owner

1. AAC through AudioToolbox (the macOS decoder), as Firefox does: yes or no?
2. Later: the HRTF data set for `PannerNode` (its licence will be reported first).

## 8. Stage A, done 2026-11-26

- `danbri/factoidal-builds`, branch `wip/1169-media-decoders` (commit `67701b16`; `main` after
  release 0.38.0, by its release manager): `third_party/media-decoders/` with the four modules,
  `PROVENANCE.md`, the licences, the build chain and the checks.
- Here: `Media/Modules.lean` (pins: size, SHA-256, interface version; `media-bench check` runs
  each module in WasmVM and compares its `mw_abi`), `media-bench` refuses a module that is not
  pinned (`MEDIA_ANY_MODULE=1` uses it with a warning), `tools/fetch-media-decoders.sh`, and three
  CC0 MP3 clips in `third_party/media/`. `tools/wasmvm/build-media.sh` and `tools/wasmvm/media/`
  moved to the builds repository.
- Checks: a second build gives the same bytes; the MP3 module gives the same floats as minimp3
  built natively, bit for bit, on the three MP3 clips, and 122 to 125 dB SNR against FFmpeg's
  decoder; Opus and Vorbis within 1 of 32768 of FFmpeg, with the instruction counts of 2026-11-08;
  VP8 frames byte-identical to libvpx; the float exports equal the int16 exports before rounding,
  on every sample; `media-bench test` 34 passed, 0 failed; `media-bench check` 4 of 4.
