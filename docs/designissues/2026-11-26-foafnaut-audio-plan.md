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
| AAC (`.m4a`, MP4) | AudioToolbox, the operating system's decoder (stage H) | approved by the owner, 2026-11-26 (section 7, answer 1) |

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
AAC by AudioToolbox (approved 2026-11-26, section 7). No H.264 or AAC code ships. A separate site that hands out
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
| F | The other nodes: `Convolver`, `DynamicsCompressor`, `WaveShaper`, `IIRFilter`, `Analyser`, `Panner` (equal-power, then HRTF: data approved 2026-11-26, licence reported before use), `MediaElementAudioSource`; then `AudioWorklet` | WPT `webaudio` |
| G | `<audio>` playback on the same pipeline (issue 588, stage 1) | WPT `media-elements` |
| H | FLAC in Lean; AAC through AudioToolbox (approved 2026-11-26) | conformance streams |

After audio: WebXR audio, then the video stages of issue 588 with section 4's rules.

## 7. Questions for the owner, answered 2026-11-26

1. AAC through AudioToolbox (the macOS decoder), as Firefox does: yes or no?
2. Later: the HRTF data set for `PannerNode` (its licence will be reported first).
3. Autoplay (section 13.7): may a page start sound only after the person has used it (clicked,
   typed), as Chrome and Safari do? The default here is yes.

Owner, 2026-11-26, verbatim: "1. yes 2. yes 3. yes (but with a Settings or CLI setting
--dangerously-permit-audio). In future we may have other mechanisms for page trust." Recorded in
`CLAUDE.md`, "Audio: AAC through AudioToolbox, HRTF data, autoplay rule". What follows for the
autoplay rule: section 13.7.

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
| `Graph.lean` | nodes, connections (node output to node input, node output to `AudioParam`), the ordered list of nodes of "Rendering an audio graph": `DelayNode`s in cycles split into a writer and a reader, cycles with no `DelayNode` muted | on `main` (`7507d103c` to `e9f637920`): no step twice, every connection in processing order, muted nodes lie on cycles, every node that is not muted is in the order (well-formed graphs) |
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
2. Fixed (`c3f61291b` to `e9f637920`): `order_complete` proves that, in a well-formed graph
   (every connection's ends are nodes of the graph; `connect`, `connectParam` and `addNode` keep
   this, `connect_wellFormed` and the others), every step of a node that is not muted is in the
   order. The proof found a defect: a `DelayNode` whose `delayTime` is fed only through
   `delayTime` connections between delays (a delay into its own `delayTime`, or two delays into
   each other's) left a cycle of `DelayReader` steps that the split does not cut and that has no
   node step to mute, so the delay was neither ordered nor muted. Such a delay is now muted
   (`mutedIds`; guards 31 and 32), and a muted delay loses both of its steps (`isMuted` by node).
   So `muted_on_cycle` now says: a muted node is on a node cycle, or its `DelayReader` is on a
   cycle of the connections that touch no other muted node. The offline renderer computes the
   order once for each `startRendering` (`Plan.of`); the real-time renderer must compute it again
   only when the graph changes (section 13).
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
- The page classes (`prelude.js`, section "webaudio", landed 2026-11-26): the
  interfaces, attributes, operations, enums and dictionaries come from Lean's table (ops 173 and
  174); arguments are converted as Web IDL says; Lean's error codes become the named exceptions.
  Defined and working on ops 175 to 189: `BaseAudioContext`, `OfflineAudioContext` (rendering,
  then `ended`, the promise with the state `closed`, then `complete`, in the specification's
  order), `OfflineAudioCompletionEvent`, `AudioProcessingEvent`, `AudioBuffer`, `AudioParam`,
  `AudioNode`, `AudioScheduledSourceNode`, `AudioDestinationNode`, `GainNode`,
  `ConstantSourceNode`, `OscillatorNode`, `BiquadFilterNode`, `AudioBufferSourceNode`, `DelayNode`,
  `StereoPannerNode`, `ChannelSplitterNode`, `ChannelMergerNode`, `PeriodicWave`. Interface objects
  whose constructors and factory methods throw `NotSupportedError` naming this issue: the nodes the
  engine cannot render yet (stage F), the MediaStream and MediaElement nodes, `AudioWorklet`,
  `AudioListener`. `AudioContext` builds graphs on a context that is never rendered until stage D
  (D2b replaces it by ops 190 to 196).
- Known gaps, each with its plan: `decodeAudioData` rejects with `NotSupportedError` until ops 194
  and 195 (stage C, D3); `setValueCurveAtTime` and `cancelAndHoldAtTime` throw until op 179 takes
  them (D2); an `AudioBufferSourceNode` takes its buffer's samples when `buffer` is set, not at
  `start()` (a change between the two is not heard; an op that acquires at `start()` replaces op
  184's copy); no read op for a node's channel settings, `type`, `loop` and loop points (the page
  keeps the last value Lean accepted); no op that frees a context (256 a page session);
  `OfflineAudioContext.suspend(time)` needs rendering in steps.
- AudioWorklet is not faked (coordinator's decision, by the rule "a stated shortfall is a failing
  test plus an open issue", `CLAUDE.md`): `context.audioWorklet` throws, so the setup of WPT
  `idlharness` (which adds a worklet module and makes an `AudioWorkletNode`) fails until stage F;
  idlharness still tests the members of the objects made before that point.
- WPT `webaudio`, local runner (`tests/browser-wpt/testharness-run.ts`, BubblePopJS, native
  engine on Linux, the 313 test files of the 2026-11-13 list, WPT master), before and after the
  page classes (engines built from `main` with and without the section): 702 pass, 1,008 fail
  (out of 1,710 subtests reported) before; 2,572 pass, 712 fail (out of 3,284 reported) after.
  More subtests are reported after because the tests run further. Not counted after: 2 files over
  a limit of 3 minutes each (`sub-sample-buffer-stitching.html`, `retrospective-setTargetAtTime.html`;
  the renderer was not yet the faster one of section 14), and
  `audiobuffersource-reverse-long-buffer.html`, which did not finish in 12 minutes (an `AudioBuffer` of 2^23 + 512 frames set as a source's buffer; stage
  C's worker measures it). Two subtests that passed before fail after: `ctor-iirfilter.html`
  ("Invalid IIRFilterNode constructor should throw" passed because `IIRFilterNode` did not exist)
  and `audioparam-nominal-range.html` ("verifyTests" now reaches `context.listener`, which throws
  until `AudioListener` exists). The largest groups of failures after: nodes not implemented yet
  (stage F), `AudioContext` state (stage D), and `AudioParam` nominal ranges (a reading of
  `value` after an out-of-range set is not clamped; `AudioBufferSourceNode.detune`'s range;
  `BiquadFilterNode.gain.maxValue` is not the single-precision value WPT expects).

## 13. Stage D design: the real-time `AudioContext` (2026-11-26)

### 13.1 Threads and state

- **Control side.** The page's `WebApi.State.audio`, a pure value, as for offline contexts. A
  real-time context is the same context state (graph, nodes, automation, sample rate) plus a
  record of its own: the state (`suspended`, `running`, `closed`), the outbox of control messages,
  the last report of the rendering side, and the handle of the page callback that takes its
  events.
- **Rendering side.** One Lean dedicated task (`Task.Priority.dedicated`, a thread of its own) per
  real-time context, in the engine library, as the engine sessions of
  https://github.com/danbri/factoidal-core/issues/1031 (engine per tab). It holds its own copy of
  the context state. The engine library starts Lean's task manager in native builds
  (`web_render_shim.c`, `FOAFNAUT_LEAN_THREADS`); with no task manager there is no real-time
  context.
- **Output.** C in the engine library, `formal/lean4/ffi/audio_sink.c`: a single-producer,
  single-consumer ring of binary32 frames, and one consumer of the ring:
  - `coreaudio` (macOS): the default output unit; its render callback copies frames from the ring
    and gives silence for what is missing;
  - `null` (every POSIX system): a thread of the sink takes frames at the sample rate and drops
    them;
  - `wav:PATH` (every POSIX system): as `null`, and the frames go to a WAV file (32-bit float),
    for tests;
  - none in the Wasm build: `new AudioContext()` answers `NotSupportedError` there (audio in the
    Hub is not a goal, section 2).
  `FOAFNAUT_AUDIO_SINK` chooses; the default is `coreaudio` on macOS and `null` elsewhere. The C
  decides nothing about the audio: it copies frames, counts, and keeps time.

### 13.2 Control messages

Web Audio API, "Control Thread and Rendering Thread": the control thread queues control messages;
the rendering thread takes the whole queue at the start of a render quantum. Here:

1. Each op 176 to 185 that succeeds on a real-time context appends its op code and fields to the
   context's outbox. The control side applies the op to its own copy, as for an offline context,
   and answers the page.
2. At the end of each page task (each turn of the engine), the engine's IO layer moves each outbox
   to the inbox of its rendering task, as one batch. So the changes made in one task apply in the
   same render quantum (Firefox applies them at its "stable state" in the same way).
3. The rendering task applies each message with the same function as the control side (`Api.op`)
   to its own copy, before its next quantum. Node ids are given in op order, so both copies give
   the same ids. A message that fails on the rendering side is not expected (the same function on
   the same sequence of ops); it is counted and traced as `audio-divergence`.
4. `start(when)` and the automation times are absolute context times; a time before the
   rendering side's current time starts or applies at once, which is the specification's rule.
5. The rendering task computes the processing order (`Plan.of`) again only when a message
   changes the graph.

### 13.3 From the rendering side to the page

After each batch of quanta, the rendering task publishes a report: frames rendered, the sources
that ended, the state changes it made (running after `resume`, suspended, closed), and the sink's
counters (frames played, under-runs, device latency). Before each page task the IO layer copies the
newest report into the control side:

- `currentTime` is frames rendered divided by the sample rate (the specification's
  `[[current frame]]` of the rendering thread). The control side keeps the larger of the old and
  the new value, so `currentTime` never decreases (a theorem of D2).
- When the report has events, the IO layer queues the context's callback
  (`EventLoop.queueTask`, as `mapAsync` does for GPU readbacks). The callback reads the events with
  op 193 and fires `ended` and `statechange`, and resolves the promises of `resume()`,
  `suspend()` and `close()`.
- While a context runs, the turn's `nextWake` is at most 25 ms ahead, so that the host gives the
  turns that deliver the events.
- When the page session ends (navigation, tab closed), its contexts close: their tasks end and
  their sinks close.

### 13.4 The rendering task

1. Take the inbox; apply the messages.
2. If the context is suspended or closed: wait for a message, a `resume` or a `close`.
3. Read the sink's counters. While frames written minus frames played is below the target: render
   one quantum (`Render.renderQuantumWith`), convert it to interleaved binary32, write it to the
   ring.
4. Publish the report. Sleep until about half of the target has played (at least 1 ms).

Target, from `latencyHint`: `interactive` 1,024 frames, `balanced` 2,048, `playback` 4,096; a
number of seconds `s` gives `ceil(s × rate)`, from 256 to 16,384. The ring holds 4 times the
target (at least 8,192 frames). `baseLatency` is the target divided by the rate;
`outputLatency` is the device latency that the sink reports (CoreAudio: the device latency, the
safety offset and the buffer size; `null` and `wav`: 0).

### 13.5 The ring as a Lean state machine

`WebAudio/Ring.lean`: the state is the capacity, frames written, frames read, the under-run
count and the frames of silence given. `write k` is all or nothing: it takes `k` frames when `k`
is at most the free space and none otherwise (the rendering task writes whole render quanta).
`read k` gives `min k available` frames and `k` minus that of silence, and counts one under-run
event when it gives any silence. Theorems: in every reachable state, read ≤ written ≤ read +
capacity; the non-silent frames given by any sequence of reads are `0, 1, 2, ...` in order with
none twice; an under-run gives silence for exactly the frames not taken; an accepted write never
reuses the slot of a frame not yet read. The model has no time. Rule of the consumers (C only):
a consumer takes nothing and counts no under-run before the first write (it waits until
`written > 0` and starts its period clock then; CoreAudio starts the output unit at the first
write), nor while paused, so the measure "under-runs a minute" starts at 0. The C ring follows it: the writer copies frames, then stores `written` with release
order; the reader loads `written` with acquire order, copies, then stores `read` with release
order; each side writes only its own counter. Tests: a stress test of the C ring under
ThreadSanitizer (a writer thread and a reader thread, random sizes, every frame value checked),
and a sequential trace of C ring operations replayed through the Lean model, which must give the
same results.

### 13.6 Ties to Lean proofs (section 4)

The ring model's theorems; the C ring's tests; the named assumption "CoreAudio plays the frames it
is given, in order, at the device rate" on every path that uses the macOS sink; `currentTime`
never decreases. An end-to-end test on Linux: a page plays one second of a 440 Hz
`OscillatorNode` through the `wav` sink; the file holds the frames of an `OfflineAudioContext`
render of the same graph (bit for bit, binary32), and there is no under-run.

### 13.7 Autoplay

Chrome and Safari start a context `suspended` when the page has no user activation, and
`resume()` needs one; Firefox has a setting. The rule here (owner, 2026-11-26, section 7 answer 3):
a new context is `running` when the page has sticky activation (HTML "has been activated"), else
`suspended`; a `resume()` before it waits (`pendingResume`) and is released by the activation. The
option `--dangerously-permit-audio`, or a switch in Settings, turns the rule off.

How it is held in place:

1. Lean decides which input gives activation (`WebDriver.Input.activates`, HTML "activation
   triggering input event"), in `WebScripts.performInput`, the one place where the trusted input
   state changes. The same step releases the audio rule (`WebAudio.Api.activate`). No page op
   gives activation: op 196 is not in the page's op table, and a theorem says that no page op
   changes `activated`. Before this change the prelude decided it in JavaScript and called op 196.
2. "Permitted with no activation" is a risk token, `Risk.audioWithoutActivation`
   (`skills/lean-risk-flags`): `WebAudio.Api.State.autoplay` holds an
   `Option (Risk.Accepted .audioWithoutActivation)`, and the only call of `Risk.dangerouslyAccept`
   for it is the engine's start request with `dangerouslyPermitAudio: true`, which the host sends
   only for the command-line option or the Settings switch. A page can not reach it.
3. The host says when it is on: a warning on standard error at start (the option, or the saved
   setting), a line in `about:foafnaut`, and the Settings row. A WPT run passes it and its record
   says so, as Chrome's WPT runs pass `--autoplay-policy=no-user-gesture-required`.
4. The owner: "In future we may have other mechanisms for page trust." One value decides
   "allowed to start" (`Api.allowedToStart`), so a permission for each site changes one function.

### 13.8 Ops 190 to 199

As landed in D2 (`WebAudio/Api.lean`, header). Changes against the text below, and why:
`newAudioContext` also answers -20 for a bad hint or callback and -23 at 16 live contexts, and
its first outbox message is `(190, [id, rate (binary64), channels, target, state])` (the state field
added in D3, so the rendering side starts as the control side did) so the rendering side
knows its parameters; the `control` call id is answered as decimal text and a `resume` before
activation waits (`pendingResume`) until op 196; `events` has kind 4 (call rejected); op 195 gives
a stored error result once and then removes the job, which makes it the one op that changes the
state while it answers an error (`op_error_state` excludes it); op 196 `activate` is added; ops
197 to 199 answer -2. Op 179 gains `setValueCurveAtTime(values, startTime, duration)` and
`cancelAndHoldAtTime(cancelTime)`; a curve of fewer than 2 values answers -29 because
`Automation.validate` decides so (the specification says InvalidStateError).

- 190 `newAudioContext(latencyHint, sampleRate, callback)`: `latencyHint` is `interactive`,
  `balanced`, `playback` or an 8-byte double; `sampleRate` is a double or ""; `callback` is the
  page callback handle for events. Answers `"ID RATE CHANNELS STATE"`. -23 for a rate outside 3,000
  to 768,000 Hz, or when the engine has no sink.
- 191 `control(ctx, verb)`: `resume`, `suspend` or `close`; the promise resolves on the event.
- 192 `time(ctx)`: `currentTime`, `baseLatency`, `outputLatency` (doubles), the state (one byte),
  then `getOutputTimestamp()`'s `contextTime` and `performanceTime` (doubles).
- 193 `events(ctx)`: the events since the last call: a `u32` count, then for each a kind byte (1
  source ended, 2 state changed, 3 promise of a `control` call resolved) and a `u32` value.
- 194 `decodeAudioData(ctx, bytes, callback)`: queues a decode job of `bytes` at the context's
  sample rate; answers the job id. The job runs on a Lean task, not in the page task: decoding in
  WasmVM takes about as long as the audio for some formats, and a long file must not stop the page.
  When the job ends, the engine queues `callback`; the page then calls op 195.
- 195 `decodeResult(job)`: `u32` channels, `u32` length, the sample rate (double), then the samples
  as binary32, channel by channel; or -30 (`EncodingError`: a format the engine does not read, or
  a decoder that refused the data) or -23 (`NotSupportedError`: the decoder module is missing or
  not pinned). The result is given once.
- 196 to 199 are kept for Web Audio.

The decoder modules (stage C): the engine reads them, once, from the directory
`FOAFNAUT_MEDIA_DECODERS`, else `~/.cache/factoidal/media-decoders` (where
`tools/fetch-media-decoders.sh` puts them), and checks each against `Media/Modules.lean` before
use. The macOS app carries them and its host sets the variable. A decode job runs only in the
native engine; the Wasm build answers -23.

### 13.9 Measures

A trace line `native-audio` once a second for each running context: frames rendered and played,
under-runs, CPU time of rendering per second of audio, frames ahead (least and most), device
latency. `--perf-summary` gets a block `audio`.

### 13.10 Steps

- D1 (done 2026-11-26, branch `wip/1169-audio-ring`): `WebAudio/Ring.lean` with its theorems
  (invariant, frames in order and once, silence and under-run count, all-or-nothing write, no
  overwrite; no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`);
  `ffi/audio_sink.c` and `ffi/audio_ring.h` (ring, `null`, `wav`, the Wasm stub; the consumer
  takes nothing before the first write); `WebAudio/Sink.lean` (the externs; not imported by the
  umbrella); Lake (`libl4audio`, `audio-sink-test`) and `build-web-render.sh` wiring; `tests/audio/run.sh`
  (ThreadSanitizer stress, trace replay through the Lean model, WAV check). The Lean 4.33 ABI
  gives an `IO a` extern no world argument and a `BaseIO a` extern the plain value (no
  `lean_io_result`); `audio_sink.c` records it. Not done in D1: a full `build-web-render.sh --native` run (the cloud box passed the 40-minute cap at the 17th of 56 lab modules, in `SVGRaster`; the sink's object compiles with the script's flags and `nm` shows `l4_audio_sink_open`); run it on the next build machine; D1m (CoreAudio) and
  D3 use these.
- D1m: the `coreaudio` consumer and the macOS link flags. No macOS compiler is in the cloud
  sessions, so this part is written against Apple's documented C API and is checked by the macOS
  build of `danbri/factoidal-builds`. Written 2026-11-26 (`audio_sink.c`, section "The coreaudio
  consumer"): the default output unit (`kAudioUnitSubType_DefaultOutput`, which follows the
  output device the person chose), interleaved binary32 input at the context's rate (the unit
  converts to the device), a render callback that only calls `l4_ring_read`, the unit started at
  the first write and stopped on pause, the device latency, safety offset and buffer size as the
  latency, and the device's nominal rate as the preferred rate. `build-web-render.sh` links
  AudioToolbox and CoreAudio on macOS. Checked here: the branch compiles with gcc and clang,
  `-Wall -Wextra -Werror`, against declaration stubs written from Apple's documented signatures,
  and calls exactly nine Apple functions. Not checked: Apple's own headers (the first macOS build
  does that) and sound on a Mac (the owner).
- D2: real-time contexts in `Api.lean` (ops 190 to 196, the outbox, the report merge) and
  `AudioContext` in `prelude.js`. Lean part done 2026-11-26, branch `wip/1169-realtime-api`: the
  state (`realtime`, `device`, `autoplay`, `activated`, `decodeJobs`, `wakeups`), ops 190 to 196,
  the outbox in `op`, `applyReport`, `takeOutbox`, `takeDecodeJobs`, `finishDecode`,
  `takeWakeups`, and the two new `paramCall` methods; theorems `op_outbox`, `applyReport_mono`
  (and the list and graph-frame forms), `takeOutbox_empty`, `takeOutbox_messages`; routing
  173 to 199 in `WasmVM/Hosts/WebApi.lean`. Not done: `prelude.js` (`AudioContext`), D3.
- D3: the rendering task and the engine's IO layer (inbox, report, callback, `nextWake`, closing
  with the page), the decode jobs of ops 194 and 195 (stage C), the trace lines, the end-to-end
  test.
- D3, first part (2026-11-26, branch `wip/1169-realtime-run`, commits 67b8651af, ea290dd28,
  97a489f29 and 7cf6c0772): `new AudioContext()` in a page plays through the engine's audio
  output.
  - `WebAudio/RenderSide.lean` (pure): the rendering side's own copy of the graph state, made with
    `Api.rtContext` as op 190 makes the control side's (`ofOpen_context`,
    `Api.newAudioContextOp_context`); the messages applied in order with `Api.op` on a state that
    holds only this context (a failure is counted as `divergence`); the control calls
    (`control_closed`, `applyBatch_closed`); the quanta for the output, mixed by the speaker rule
    to the device's channels and interleaved (`fill_frames`: the frames written are the rendered
    quanta in order; `fill_frame`, `fill_size`); the quanta that bring the frames ahead to the
    target (`quantaFor_bounds`); the reports and their merge (`mergeReport_events`). Its
    `#guard`s check 256 frames of a 440 Hz oscillator against an `OfflineContext` render of the
    same graph, bit for bit after binary32 rounding.
  - `labs/demos/foafnaut/WebAudioRun.lean`: one dedicated Lean task per context (the loop of
    13.4; the sink is opened by the task, paused while suspended, closed on close); the registry
    in `WebDocument.Engine.audio`; the steps before and after each `scriptSession` call
    (`WebDocument.answerAudio`, around `answerIn` in `compile` and `compileBin`); the document op
    `audioRuns` (the measures). Whether Lean's task manager runs is asked of Lean
    (`taskManagerRuns`: a dedicated task runs on another thread only then), not of
    `web_render_shim.c`: the render command line (`WebRenderCLI`) links these modules without the
    shim. A new session takes the output from `Page.Limits.audioDevice` and `autoplay`
    (`FOAFNAUT_AUTOPLAY=allow`, or `autoplay:true` in `start`); the session of an `iframe` gets
    none (`WebScripts.frameLimits`: the engine does not take a frame's outbox).
    `nextWake` is at most 25 ms ahead while `Api.needsTurns`. The runs end with their page
    session (`close`, a new `start`), and with their engine session: `web_session_free` and the
    end of a task session (`WebDocument.engineEnd`), and the document op `audioEnd`, which the tab
    worker sends before it closes (its default session is never freed).
  - `prelude.js`: `AudioContext` on ops 190 to 196 (state, `currentTime`, `baseLatency`,
    `outputLatency`, `getOutputTimestamp()`, `resume()`, `suspend()`, `close()`, `ended`,
    `statechange` after the promise as the specification orders it), `setValueCurveAtTime` and
    `cancelAndHoldAtTime` on op 179, and the page's sticky activation (op 196 on the first trusted
    activation-triggering input event). The context's event callback is kept across tasks
    (`kept`): the host releases a callback after a task that runs it (`Page.lean`, the task branch
    of the event loop's run; `PageEvents.lean`), which deleted this one after its first delivery,
    so later events (`resume()` after `suspend()`, `close()` after `ended`) did not reach the page.
  - The opening message has a fifth field, the initial state (13.8).
  - Writes (13.4, step 3): once the output takes frames, the task writes each quantum when it is
    rendered. The first write after the sink opens, or after a `resume()` (the sink stays paused
    until then), holds the quanta up to the target in one write, because the `null` and `wav`
    consumers take 256 frames at their first period. Two other forms failed the 440 Hz test on
    this machine: all the quanta of a turn in one write (1 to 5 under-runs a second: the output
    waited for up to 8 quanta of work) and one quantum from the start (1 under-run of 128 frames at
    the start).
  - Measures at 97a489f29, `labs/demos/foafnaut/webaudio_realtime_test.ts` (Linux cloud VM, 4 vCPUs, no sound
    device, `wav` sink, 48 kHz, target 1,024 frames; another Lean build ran on the machine, load
    average 3.4), three runs:
    - 440 Hz `OscillatorNode` for 1 s: the WAV file holds the `OfflineAudioContext` render (the
      second and 2,048 frames of silence, 50,048 frames, 2 channels) bit for bit after binary32
      rounding, from its first frame; 0 under-runs; 53 `currentTime` samples, none smaller than
      the one before; `close()` closes the sink, the task ends, its thread is gone.
    - CPU time of the rendering thread (`/proc/self/task/TID/schedstat`): 223, 237 and 336 ms
      per second of audio; rendering and writing (`renderNs`): 229, 232 and 333 ms, that is 0.61
      to 0.89 ms per render quantum of 128 frames for one oscillator.
    - Frames ahead of the output when the task looked: least 256, most 1,024 (all three runs).
      With the `ConstantSourceNode` page of the suspend test the least was 0 once in three runs
      (the ring was empty when the task looked), with no under-run: on a loaded machine the
      `interactive` target leaves little room.
    - `suspend()` then 600 ms: no frame taken, no under-run counted; after `resume()`, 0
      under-runs. With no autoplay, `resume()` waits until a trusted mouse press (pointer down and
      up) activates the page, then resolves before `statechange` fires.
    - A run ends, and its thread is gone, on `audioEnd` and when its engine session ends with no
      `close` of the page.
    - Three more runs at 7cf6c0772 (the same loop), load average 6.7: CPU time 213,
      216 and 229 ms per second of audio, rendering and writing 228 to 241 ms; least frames ahead
      256, 0 and 0, most 1,024; no under-run, bit for bit.
    - Build, `build-web-render.sh --native`: 302 to 437 s, with a local reuse of this worktree's
      earlier outputs (not committed). A clean build was not timed.
  - Not done: the decode jobs of ops 194 and 195 (stage C); the `native-audio` trace line and the
    `--perf-summary` block (13.9); `autoplay` is not in `HostContract.relaxFields` (a host that
    sets it relaxes the autoplay policy); a host that drops an engine with none of the end steps
    above leaves its runs playing, and if the library is then unloaded a run's thread runs
    unloaded code (task sessions pin the library, real-time runs do not); the Wasm build was not
    run (no `emcc` here); the owner's check on a Mac (the `coreaudio` consumer
    takes the device's buffer at each callback, so the margin above may be smaller there). The
    rendering cost (above) has not been worked on.
- The autoplay rule as the owner decided it (13.7; branch `wip/1169-autoplay`, which holds D3's
  branch merged with `main`): `Risk.audioWithoutActivation`; `Api.State.autoplay` holds the token,
  made only by `WebScripts.audioLimits` from the start request's `dangerouslyPermitAudio`;
  `Api.op` gives back `autoplay` and `activated` (`op_gate`), code 196 answers -2;
  `WebScripts.performInput` calls `Api.activate` at the first input that gives activation; the
  prelude's own activation code is gone; the environment variable `FOAFNAUT_AUTOPLAY` is gone;
  `dangerouslyPermitAudio` is in `HostContract.relaxFields` (and in `host-trace.mjs`). The window:
  `--dangerously-permit-audio`, a warning on standard error and a `native-html-permit-audio`
  trace line, the Settings switch "Let pages start sound before I use them" (saved as
  `WebState.Settings.permitAudio`; command `permit-audio`, Settings-only by
  `WebRoute.settingsOnly`, theorem `settings_only_from_settings` now over every such command, and
  `link-route.mjs` the same), a row in `about:foafnaut`. The WPT runner: the same option, written
  in its report (`dangerouslyPermitAudio`). The Hub's Settings page says it has no audio output.
- D3, second part (2026-11-27, branch `wip/1169-page-decode`): decode jobs in pages, and large buffers.
  - `WebAudioRun.lean`: in `after`, each job of `Api.takeDecodeJobs` starts a task of the task pool
    (`BaseIO.asTask`, default priority) that runs `WebAudio.Decode.decodeAudioData` and packs the
    samples (`Api.channelsBytes`); finished tasks give their result to the page (`Api.finishDecode`) in
    `before`, and in `after` for a task that finished at once (no task manager: `asTask` runs on the
    calling thread, correct and only slower). `Api.needsTurns` is true while a job has no result. The
    decoder modules are read once per engine from `FOAFNAUT_MEDIA_DECODERS`, else
    `~/.cache/factoidal/media-decoders`, each checked with `Media.Modules.check`; a file that needs a
    missing module answers -23 (`NotSupportedError`, the message names `tools/fetch-media-decoders.sh`);
    other failures -30 (`EncodingError`). `build-web-render.sh` builds `L4Factoidal.WebAudio.Decode`
    into the library.
  - `prelude.js`: `decodeAudioData(arrayBuffer, success, error)` on ops 194 and 195: argument checks,
    `DataCloneError` for a detached buffer, `ArrayBuffer.prototype.transfer()` detaches the page's
    buffer (BubblePopJS has it), the promise resolves and then the success callback is called in the
    same task (the specification's order); the error path rejects with the named `DOMException` and then
    calls the error callback. The samples are `Float32Array` views of the op 195 answer, with no copy.
    Works on `AudioContext` and `OfflineAudioContext`.
  - Hygiene: importing `Media.Decode` brought `WasmVM.Bench.Sample` (its `initialize prof` is one more
    opaque) into the lab's closure. `Media.Decode.Module` now has an optional `sampler`
    (`WasmVM.Bench.Sample.runIO`, passed by `media-bench video` when `WASMVM_PROFILE` is set), so the
    import is gone: 38 externs, 2 opaques, as before. Side effect: `WASMVM_PROFILE` now samples only
    `media-bench video`, not `media-bench audio`.
  - Large buffers. Cause: `bufferArgs` read each value with `all.data[i]!` on a `FloatArray`; `.data` of a
    `FloatArray` copies the whole array, so setting a buffer was quadratic. Fixed (one pass,
    `Api.f32sFrom`), and the other loops of the same kind (`f32sBytes`, `Decode`'s rounding) are one pass
    now. Also: `checkOp` and `bufferArgs` no longer allocate a zero buffer of the full length to
    validate it, and the page passes each channel as its own argument instead of copying the channels
    into one array (`TypedArray.prototype.set` costs 0.7 microseconds a value in BubblePopJS; 2.5 s for
    one 2^22 channel). Host-timed page turns (`webaudio_bigbuffer_bench.ts`, Linux, 4 vCPUs, another
    build running):

    | frames | new AudioBuffer before / after | set `buffer` before / after | render answer into JS before / after |
    |---|---|---|---|
    | 2^12 | 9 ms | 121 ms | |
    | 2^14 | 14 ms | 1,980 ms | |
    | 2^15 | 20 ms | 8,259 ms | |
    | 2^16 | 50 / 6 ms | (about 33 s) / 4 ms | 22 / 15 ms |
    | 2^18 | 133 / 8 ms | (about 9 min) / 7 ms | 68 / 46 ms |
    | 2^20 | 464 / 16 ms | | 257 / 194 ms |
    | 2^22 | 1,986 / 43 ms | | 1,038 / 651 ms |

    Setting `buffer`: 2^22 118 ms, 2^23 (+512) 323 ms (target 2 s). Before, time grew by 4 for each doubling
    (quadratic; 2^23 extrapolates to about 150 hours). The 2^16 and 2^18 "before" values in
    parentheses are extrapolated from 2^15, not measured.
  - Findings inside BubblePopJS, not changed: `TypedArray.prototype.set` of another typed array is
    about 0.7 microseconds a value (2^22: 2.5 s); the `apiCall` block is limited to 64 MiB
    (`LeanJS.outCap`) in both directions, so a buffer or a decode answer above 16.7 million
    samples (a 3-minute stereo song at 48 kHz is 17.3 million) is refused with -5. Chunked transfer
    would need ops of its own and a contiguous `Float32Array` made without `set`. Issue
    https://github.com/danbri/factoidal-core/issues/1177 (one page call carried at most 64 MiB).
    Owner, 2026-11-27, verbatim, on that issue: "maybe our rules are too uptight?". The
    coordinator's answer, not the owner's words: the 64 MiB was the QuickJS build's `read_bytes`
    limit, copied into BubblePopJS, whose call memory is sparse; so on a 64-bit host `LeanJS.outCap`
    is 1 GiB and `Api.maxSamples` is 2^27 (a stereo recording of 23 minutes at 48 kHz; 512 MiB as
    binary32, 1 GiB as the engine's binary64). The Wasm build (32-bit) keeps 64 MiB and 2^25, and
    the QuickJS build keeps its 64 MiB. `webaudio_decode_test.ts` sets an 18-million-sample buffer.
  - Tests: `webaudio_decode_test.ts` (the five clips equal `lake exe media-bench decode` bit for bit at
    44.1 kHz; detach, order of callbacks, `EncodingError`, `DataCloneError`, `TypeError`, no modules
    gives `NotSupportedError`), `webaudio_jukebox_test.ts` (Decode all gives "Decoded 6 of 6 tracks.",
    Play: the WAV holds the first track bit for bit times 0.8, 0 under-runs; "From the last click to the
    first frame played" 121 to 135 ms; Decode all of 6 tracks about 7.4 s in this build).
    The jukebox test clicks by a message that makes the page call `click()`: the engine's hit test reads
    the page's static layout, which the page's own script changes.
- Then the owner's check on the Mac, and stage E (the jukebox).

## 14. Render quantum speed (2026-11-26)

Tracking: https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut). Branch
`wip/1169-render-perf`.

Target: one quantum (128 frames, 48 kHz, budget 2.67 ms) of one sine oscillator under 0.05 ms;
the graph of `labs/demos/foafnaut/pages/particle-rex.html` under 0.5 ms; same output.

Method. `lake exe webaudio-bench [a|b|c]` (`Harness/WebAudioBench.lean`) builds three graphs with
the `OfflineContext` functions and renders 300 quanta, 5 runs: (a) one sine oscillator into the
destination; (b) one `AudioBufferSourceNode` (1 s stereo buffer, looping) through a gain; (c) the
Particle Rex shape: master gain, feedback delay with a wet gain, a pad of three oscillators
(sine, sine, triangle) through gains and a lowpass with `setTargetAtTime`, three tone oscillators
(sine, square, sawtooth) with `setValueAtTime`, exponential and linear ramps and `stop`. It prints
the median ms per quantum and an FNV-style hash of the output bits (binary32 rounded). Profile:
`perf record -g --call-graph dwarf` on the bench, `perf report --no-children --sort symbol`. The
VM has 4 vCPUs shared with other sessions (load average 3.8 to 4.9 while measuring), so a number
has about 10 % noise.

| graph | before | after | hash |
|---|---|---|---|
| a, one oscillator | 0.227 ms | 0.014 ms | equal |
| b, buffer, gain | 0.132 ms | 0.035 ms | equal |
| c, Particle Rex shape | 4.03 ms | 0.41 ms | equal |

Where the time was (graph c, before): 80 % of the samples in `Automation.fill` and its callees.
`fill` called `valueAt` for each frame with exact rationals: `frameTime` made a `Rat` from a
`Float` (`ofDouble`: `mkRat` with a gcd on 2^60 to 2^70 denominators, so GMP; 50 % of the time),
and `walk` compared and subtracted rationals (24 %). Float literals above 2^32 and 2^52 inside
`ofDouble` and `validate` were parsed at each call (`lean_cstr_to_nat`, 5 %).

Changes, each with the output kept:

1. `Automation.fill` computes in binary64 (`fillFast`). `fillSpec` is the old definition and the
   specification. A stored time is the exact value of a double, so `timeToFloat` recovers it and
   the order of stored times is the IEEE order; the time of frame `f` is `f / sampleRate` in
   binary64. The events are converted once per call, the value before each event (`fBefore`) is
   computed once per call, and a cursor (`advance`) moves forward over the events because the
   frames increase. A list with a curve event uses `fillSpec`. Not proved (the kernel does not
   unfold `Float`): 13 `#guard`s compare `fill` and `fillSpec` bit for bit on each event kind,
   equal times, zero start values, a sample rate of 0 and a curve. No theorem mentions `fill`.
2. `@[specialize]` on `Kernels.iter` and `Kernels.mkChan`: the closure call and the boxed `Float`
   for each frame are gone (graph b 0.13 to 0.07 ms).
3. `@[inline] getF`, with the constant `zeroF` for its 0: an inlined `Float` literal is evaluated
   by `Float.ofScientific` at each call (it parses a big integer literal, about 1 us) unless it
   is a top-level constant. Trap: any `Float` literal in a function that is inlined or
   specialised into a branch of a hot loop has this cost; use a named constant.
4. `PeriodicWave.realZero` and `partialSumSin`: a wave whose cosine terms are all 0 (the built-in
   waves) is summed without `acc + 0 * ck` (`acc` is never `-0`, `ck` is finite, so the sum is
   bit equal). `#guard`s compare it with `partialSum` bit for bit on four waves at 12 phases.
5. `Automation.fillConst` and a one-value result in `Render.paramValues` for a parameter that is
   constant over the quantum (empty list, or only non-curve, non-`setTarget` events at or before
   the first frame) and has no connection. Every kernel reads a one-value array as constant over
   the block (`Kernels.paramAt`), so the output is the same; the array has 1 value, not `n`.
   `#guard`s check that `fill` gives that value at every later frame.

Randomized differential check of change 1 (`lake exe automation-fill-diff`, run by
`tests/audio/run.sh`): 20,000 random timelines from seed 20261126, each built with
`Automation.insert` from 0 to 9 operations (setValue, linear and exponential ramps, setTarget,
curves, `cancelScheduledValues`, `cancelAndHold`); times on frame times of the sample rate, one
ulp above and below them, multiples of 1/8000 and random; start frames 0 to 12,000; quantum 1
(k-rate), 32, 64, 128, 256 or 500; sample rate 44,100, 48,000, 8,000 or 0; default and event
values include 0, plus or minus 0.0001 and values below 1e-6. Result: `fill` equals `fillSpec`
bit for bit in all 20,000 cases (also seeds 1, 2 and 3, 20,000 each; 9.6 s per run). Not
measured: the power of the test against injected faults beyond the `#guard`s (a wrong cursor
comparison was caught by the `#guard`s at build time, before this test ran).

Remaining cost (graph c, 0.41 ms): the band-limited oscillator sum is about 30 % (the sawtooth at
110 Hz sums 217 partials per sample; a bit-exact version cannot skip terms, the recurrence is the
arithmetic; a wavetable would change the output within the 1e-9 tolerance of the tests), the
delay kernel 12 %, `fillFast` for the `setTarget` and ramp parameters 10 % (one `Float.exp` per
frame), allocation of one `FloatArray` per node per quantum about 15 %, input mixing 6 %.
Not done: the delay kernel and the mixers still go through `mkChan` closures for each channel;
an instruction-count measurement that does not depend on the load of the machine.

## 15. The HRTF data set: what its licence is known to be (2026-11-27)

Owner, 2026-11-26 (section 7, answer 2): yes to the HRTF data set for `PannerNode`, after its
licence is reported. Chromium (`third_party/blink/renderer/platform/audio/resources/`), WebKit
(`Source/WebCore/platform/audio/resources/`) and Firefox (`dom/media/webaudio/blink/`) ship the
same impulse responses, `IRC_Composite_C_R0195_T*_P*.wav` joined into one file (`Composite.wav`,
FLAC in Chromium). They come from the IRCAM LISTEN HRTF database.

What the sources say, read on 2026-11-27:

- Debian's copyright file of libmysofa, which ships one LISTEN subject as test data
  ([copyright file](https://metadata.ftp-master.debian.org/changelogs//main/libm/libmysofa/libmysofa_0.6~dfsg0-3+deb10u1_copyright)),
  records "Copyright: 2002, IRCAM" and licence `listen-ircam`, verbatim: "The Listen database is
  public and available for any use. We would however appreciate an acknowledgment of the database
  somewhere in the description of your work (e.g. paper) or in your development."
- Chromium's README for the files gives no licence; it points to
  [WebKit bug 98294](https://bugs.webkit.org/show_bug.cgi?id=98294), which is about the order of
  the elevations and gives no licence either. A W3C list message
  ([public-audio, 2013-01-24](https://lists.w3.org/Archives/Public/public-audio/2013JanMar/0210.html))
  says only that WebKit's set is derived from LISTEN.
- IRCAM's own LISTEN page (`recherche.ircam.fr/equipes/salles/listen/`) answered HTTP 503 twice,
  so IRCAM's text was not read.

Reading, not legal advice: the terms Debian records allow any use and ask for an acknowledgment.
Not shown: IRCAM's own text today, and whether the composite files of the browsers carry the same
terms (no file says). Before the data is vendored (in `danbri/factoidal-builds`, `third_party/`,
with provenance, as for the decoders), IRCAM's page is read again and quoted in the provenance
file, and the acknowledgment goes in the provenance file and in `about:foafnaut`. Equal-power
panning, which needs no data, comes first (stage F).
