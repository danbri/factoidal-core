/-
# Web Audio output: the audio sink (externs of `ffi/audio_sink.c`)

Stage D1 of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, section 13.

A `Sink` is a ring of binary32 frames and one consumer that takes frames out of it. The state
machine of the ring, with its theorems, is `WebAudio/Ring.lean`; the C follows it. The C decides
nothing about the audio: it converts binary64 to binary32, copies frames, counts and keeps time.

Do not import this module from `WebAudio.lean` or from a module that the web API (`WebApi.lean`)
imports: an executable that imports it links `ffi/audio_sink.c` (Lake: `libl4audio`;
`labs/demos/foafnaut/build-web-render.sh`).

## Contract (what each function gives, and what it relies on)

* `open spec rate channels capacity`: `spec` is `null`, `wav:PATH` or `coreaudio`. Fails with an
  `IO.userError` that names the reason: bad spec, rate outside 3000 to 768000 Hz, channels outside
  1 to 32, capacity outside 256 to 1048576 frames, file not writable, thread not started, or (the
  Wasm build) no audio output. `coreaudio` fails in a build with no CoreAudio consumer.
* `write s samples`: `samples` holds interleaved frames. ALL OR NOTHING (`Ring.write`): it answers
  the number of frames taken (`samples.size / channels`), or 0 when the ring has less free space
  than that, when `samples.size` is not a multiple of the channels, when it is empty, or when the
  sink is closed. Each value is rounded to binary32 (round to nearest, ties to even).
* `counters s`: `[written, read, underrunEvents, silentFrames, deviceLatencyFrames, rate,
  channels, capacity]`, as binary64 values. `read` frames were given to the consumer, silence
  excluded. Each under-run event is one consumer read that found fewer frames than it asked for
  (`Ring.read_silence`).
* `pause s true`: the consumer takes nothing and counts no under-run until `pause s false`.
* `close s`: stops the consumer and closes its file (a `wav` file gets its final header sizes).
  Closing twice is safe. A sink that is no longer referenced is closed and freed by its finalizer.
* `deviceInfo spec`: `[rate, channels]` that the consumer prefers. `null` and `wav`:
  `FOAFNAUT_AUDIO_RATE` (3000 to 768000) or 48000 Hz, and 2 channels.

Named assumption of every path that uses the macOS consumer: "CoreAudio plays the frames it is
given, in order, at the device rate". The `null` and `wav` consumers rest on no such assumption:
the `wav` file holds the frames the consumer took, silence included, and is checked bit for bit by
`tests/audio/run.sh`.
-/
namespace L4Factoidal.WebAudio.Sink

private opaque SinkPointed : NonemptyType

/-- An open audio sink (an external object). -/
def Sink : Type := SinkPointed.type

instance : Nonempty Sink := SinkPointed.property

/-- Open a sink. See the contract above. -/
@[extern "l4_audio_sink_open"]
opaque «open» (spec : @& String) (rate : Float) (channels : UInt32) (capacity : UInt32) : IO Sink

/-- All or nothing: frames taken (`samples.size / channels`), or 0. -/
@[extern "l4_audio_sink_write"]
opaque write (s : @& Sink) (interleaved : @& FloatArray) : BaseIO UInt32

/-- `[written, read, underrunEvents, silentFrames, deviceLatencyFrames, rate, channels, capacity]`. -/
@[extern "l4_audio_sink_counters"]
opaque counters (s : @& Sink) : BaseIO FloatArray

/-- A paused consumer takes nothing and counts no under-run. -/
@[extern "l4_audio_sink_pause"]
opaque pause (s : @& Sink) (paused : Bool) : BaseIO Unit

/-- Stop the consumer. Safe to call twice. -/
@[extern "l4_audio_sink_close"]
opaque close (s : @& Sink) : BaseIO Unit

/-- `[rate, channels]` that the consumer of `spec` prefers. -/
@[extern "l4_audio_device_info"]
opaque deviceInfo (spec : @& String) : BaseIO FloatArray

/-- The sink spec to use when the caller names none: `FOAFNAUT_AUDIO_SINK`, else `coreaudio` on
macOS, else `null`. -/
def defaultSpec : BaseIO String := do
  match ← IO.getEnv "FOAFNAUT_AUDIO_SINK" with
  | some s => if s.isEmpty then pure (if System.Platform.isOSX then "coreaudio" else "null") else pure s
  | none => pure (if System.Platform.isOSX then "coreaudio" else "null")

end L4Factoidal.WebAudio.Sink
