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

## 9. Stage B: the structure of the engine

Files under `formal/lean4/L4Factoidal/WebAudio/` (library `WebAudio`, umbrella `WebAudio.lean`).
Each file imports `Init` and earlier `WebAudio` files only, so it type-checks alone and fast.

| File | What | State |
|---|---|---|
| `Mix.lean` | `computedNumberOfChannels`; up-mix and down-mix matrices (exact `Rat`), their `Float` evaluation; summing connections into an input | on `main` (`5bddeecfc`); tail-recursive loops and shape theorems on `wip/1169-mix-delay` |
| `Automation.lean` | the `AudioParam` automation event list: insertion, cancellation, the computed value at a time; stored times exact values of binary64 numbers, sums and frame conversion in binary64 (`ceil(t × rate)`, as WPT `audioparam-testing.js`) | on `main` (`cd8ab064f` to `b5bfaa30f`): 7 theorems, 114 `#guard` |
| `Graph.lean` | nodes, connections (node output to node input, node output to `AudioParam`), the ordered list of nodes of "Rendering an audio graph": `DelayNode`s in cycles split into a writer and a reader, cycles with no `DelayNode` muted | on `main` (`7507d103c`, `7cce27238`): no step twice, every connection in processing order, muted nodes lie on cycles; not yet proved: every node that is not muted is in the order |
| `Kernels.lean` | block kernels as pure functions with explicit state: Gain, ConstantSource, Delay, StereoPanner, ChannelSplitter, ChannelMerger | on `main` (`f1887ceaf`, `059cbe3bb`); cycle minimum and channel-count change on `wip/1169-mix-delay`: shape and state theorems, 75 `#guard`; fractional delay by linear interpolation (the specification names none) |
| `Filters.lean`, `Oscillator.lean` | BiquadFilter (coefficients of the specification, `getFrequencyResponse`), Oscillator and `PeriodicWave` | on `main` (`531881c86`, `e270b721b`), rendered through `Render` |
| `Buffer.lean` | `AudioBuffer`: channels of 32-bit floats, `copyFromChannel`, `copyToChannel`, `getChannelData` rules; the `AudioBufferSourceNode` playback algorithm | on `main` (`27c4e37d1`), rendered through `Render` |
| `Render.lean` | one render quantum: apply control messages, mix each node's inputs, compute its `AudioParam` values (intrinsic value plus the mixed-down inputs, clamped to the nominal range; a-rate or k-rate), run its kernel, in the ordered list | on `main`: frame, shape and graph theorems; Oscillator, BiquadFilter and AudioBufferSource output silence until their kernels land |
| `Context.lean` | `BaseAudioContext` state, `OfflineAudioContext.startRendering` (render N frames into an `AudioBuffer`) | on `main`: constructor checks, nodes, connections, automation methods, `startRendering`; shape theorems; 62 `#guard` renders |

A block is `Array FloatArray`: one `FloatArray` of `n` frames per channel, `n = 128` (the render
quantum; Web Audio 1.1's `renderSizeHint` makes it a parameter). Processing is in 64-bit floats;
values exposed to script (`AudioBuffer` data) are rounded to 32-bit floats, as the specification
requires. A kernel has the form
`process : State → (inputs : Array Block) → (params : Array FloatArray) → State × Array Block`,
with `params[i]` holding `n` values (a-rate) or one value (k-rate). The page interfaces
(`prelude.js`, the interface table from the Web Audio IDL, the ops) come after `Render.lean` and
`Context.lean`, so that `OfflineAudioContext` tests can run first.

## 10. Stage C, first part: the MP3 reader (2026-11-26)

`Media/Mp3.lean` (`bbd44a137`): ID3v2, ID3v1 and APEv2 tags skipped; MPEG-1, MPEG-2 and MPEG-2.5
frame headers; the first frame confirmed by the next header; the information frame left out; the
LAME delay and padding applied (gapless, as FFmpeg). `Decode.mp3` gives one whole frame per call
to the MP3 module and checks each result. On the three clips the WasmVM output equals the V8 run of
the same module bit for bit, the lengths equal FFmpeg's, and the samples are within 2 of 32768 of
FFmpeg's decoder.

Second part (`7599e970a` to `a17dd53f9`): `Media/Wav.lean` (PCM 8 to 32 bits, float 32 and 64,
A-law, µ-law, extensible; identical to FFmpeg on every WAV tried), float decoder paths for Opus,
Vorbis (every channel, 8 at most, in Web Audio's channel order) and MP3, and
`WebAudio/Decode.lean`: `decodeAudioData` (format sniffing, module pin check, decoding, a
Kaiser-windowed sinc resampler to the context's rate: gain within 1e-4 up to 0.9 of the lower
Nyquist, -103 dB at 1.1; about 98 dB SNR against FFmpeg's resampler in the interior). Not yet:
end trimming of Vorbis in WebM; Opus with more than two channels. `media-bench decode` runs it.

## 11. Open defects in the landed engine files (2026-11-26)

Found by the work on `Render.lean`; none blocks the offline renderer.

1. Fixed: parameter edges into a split `DelayNode` now end at its reader step (`paramDstStep`),
   so a later `delayTime` source is processed first. The ordering theorems were restated for audio
   edges (`order_topological_edge`) and parameter edges (`order_topological_param`), because the
   general form over `dstStep` is false once parameter edges go to the reader. Behaviour to check
   against WPT or another engine: a delay whose `delayTime` is driven from inside its own cycle
   leaves that cycle uncut, so the nodes on it are muted (`Graph.lean` guard 23c).
2. `Graph.lean`: not proved that every node that is not muted appears in the order (it needs "a
   finite graph with no cycle has a vertex with no incoming edge").
3. Fixed (`b867dfc8b` and the commit before it): `Mix.mixInput` and `Mix.apply` are tail-recursive
   loops (`mixConns`, `addRows`, `addFrames`, `applyRows`, `rowMix`, `scaleAdd`; channels updated
   in place with `Array.modify` and `set!`). Theorems `Mix.mixInput_shape` (`toCh` channels of
   `frames` samples for any connections) and `Mix.apply_shape` (every channel has `frames`
   samples). `Render.normalize` is left as it is.
4. Fixed (`b867dfc8b`): in a cycle the minimum wins, as the specification says ("clamped to a minimum of
   one render quantum"): the delay is at least `n` frames even above `maxDelayTime`.
   `DelayState` has `maxFrames`; the ring has `max maxFrames quantum + 1` frames (`Render` passes
   its quantum to `DelayState.init`; the default 0 gives `maxFrames + 1`); the upper clamp is
   `min (max maxFrames minFrames) (size - 1)`, so a quantum larger than the one given at node
   creation cannot index outside the ring. `#guard`s: 2-frame maximum, cycle, 4-frame quantum
   delays by 4; outside a cycle by 2.
5. Fixed (`b867dfc8b`): when the input channel count differs from the stored one, `delayProcess` replaces
   the whole ring by `Mix.apply (Mix.matrix interp old new) ring size` (`DelayState.retarget`);
   `interp` is a `DelayState` field that `Render.runKernel` sets from the node's
   `channelInterpretation`. `delay_state_wf` and `delay_shape` still hold. `#guard`s: mono to
   stereo (both channels), stereo (1, 3) to mono (2), `discrete` 2 to 1 (channel 0), unchanged count.

## 12. Stage B, last part: the page interfaces

How page script reaches the Lean engine, following WebGL and WebCodecs (`prelude.js` calls
`apiCall(op, args)`; `WasmVM/Hosts/WebApi.lean` routes the op; ops 100 to 119 are WebGL's, 120 to
139 WebCodecs').

- Ops 173 to 189 are Web Audio's (170 to 172 were already layout ops), in `WebAudio/Api.lean`
  (`295173571`; the op table is its header; theorems: no op changes a context it does not name, a
  failed op leaves the state unchanged). Its state is a field of
  `WebApi.State` (`audio`), so contexts persist between script turns: the contexts by id, each an
  `OfflineContext` for now (a real-time context in stage D).
- The page builds its classes from the interface table (`WebAudio/Idl.lean`, generated from WPT's
  `interfaces/webaudio.idl` by `tools/webaudio-idl-table.py`; one op answers its text, as WebGL's op
  100 does), so names, `length`s, attributes and enum values come from one list.
- Every decision is Lean's: argument ranges, the specification's errors (an op answers an error
  code that the page turns into the named `DOMException`), the graph, automation, rendering.
  `prelude.js` converts arguments as Web IDL says and keeps the page's objects.
- `AudioBuffer` data lives in the page (`Float32Array`s, as the specification's
  `getChannelData` requires); it goes to Lean when the specification says the content is acquired
  (setting `AudioBufferSourceNode.buffer`, `ConvolverNode.buffer`).
- `OfflineAudioContext.startRendering()`: the op renders the whole length in Lean and answers the
  channels (binary32 bytes) and the source nodes that ended; the page resolves the promise and
  fires `ended` and `complete` in queued tasks, in the order the specification gives.
- `decodeAudioData()`: the bytes go to Lean; WAV is read in Lean, MP3, Ogg Vorbis and Opus by the
  decoder modules (stage C). The engine gets the module bytes from its host at start, and checks
  each against `Media/Modules.lean` before use.
- Measure: `tests/browser-wpt/testharness-run.ts` on the WPT `webaudio` names, with the test files
  fetched by name, before and after each step.
