/-
L4Factoidal.WebAudio: the W3C Web Audio API in Lean, for Foafnaut (issue
https://github.com/danbri/factoidal-core/issues/1169; plan:
docs/designissues/2026-11-26-foafnaut-audio-plan.md).

- `WebAudio.Mix`: `computedNumberOfChannels` and the up-mix and down-mix matrices of the
  specification's section 4 (channel up-mixing and down-mixing), as exact rationals, with their
  `Float` evaluation.
- `WebAudio.Automation`: the `AudioParam` automation event list (insertion, cancellation, the
  value at a time); stored times are exact values of binary64 numbers, sums and frame conversion
  are rounded to binary64.
- `WebAudio.Kernels`: block processing of Gain, ConstantSource, Delay, StereoPanner,
  ChannelSplitter and ChannelMerger as pure functions with explicit state; the start and stop
  rule of scheduled sources.
- `WebAudio.Graph`: nodes and connections, and the ordered list of nodes of "Rendering an audio
  graph" (`DelayNode`s in cycles split into a writer and a reader; cycles with no `DelayNode`
  muted). Proved: no step twice, topological order, every step of a node that is not muted is in
  the order (for graphs built by `connect`).
- `WebAudio.Render`: one render quantum of a context: mixed inputs, `AudioParam` values
  (automation plus connected signals, clamped), kernels in graph order, the destination's block.
- `WebAudio.Context`: an offline context: constructor checks, nodes, connections, automation,
  `startRendering` (whole quanta, then `length` frames rounded to binary32).
- `WebAudio.Buffer`: `AudioBuffer` (channels of binary32 values; copy rules) and the
  `AudioBufferSourceNode` playback algorithm (rate, detune, loops, offset, duration, sub-sample
  start, sample-rate conversion). Called by `Render.runKernel`.
- `WebAudio.Oscillator`: `PeriodicWave` (normalization), the built-in waveforms, and the
  `OscillatorNode` kernel (band-limited Fourier sum). Called by `Render.runKernel`.
- `WebAudio.Filters`: `BiquadFilterNode` coefficients for the eight types, the kernel, and
  `getFrequencyResponse`. Called by `Render.runKernel`.
- `WebAudio.Decode`: `decodeAudioData`: format sniffing, WAV, Opus, Vorbis and MP3 decoding to floats,
  the windowed-sinc resampler to the context rate, and the `AudioBuffer`.
- `WebAudio.Api`: the page operations (`web_api` ops 173 to 189) and the contexts kept between
  script turns; the op table is in its header.
- `WebAudio.Idl`: the interface table generated from WPT's `interfaces/webaudio.idl` by
  `tools/webaudio-idl-table.py` (interfaces, attributes, operations, enums, dictionaries).
-/
import L4Factoidal.WebAudio.Mix
import L4Factoidal.WebAudio.Automation
import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.Graph
import L4Factoidal.WebAudio.Render
import L4Factoidal.WebAudio.Context
import L4Factoidal.WebAudio.Buffer
import L4Factoidal.WebAudio.Oscillator
import L4Factoidal.WebAudio.Filters
import L4Factoidal.WebAudio.Idl
import L4Factoidal.WebAudio.Decode
import L4Factoidal.WebAudio.Api
