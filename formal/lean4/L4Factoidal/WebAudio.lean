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
-/
import L4Factoidal.WebAudio.Mix
import L4Factoidal.WebAudio.Automation
import L4Factoidal.WebAudio.Kernels
