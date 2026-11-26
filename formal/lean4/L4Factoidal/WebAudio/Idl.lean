/-
L4Factoidal.WebAudio.Idl: the interfaces, enums, dictionaries and callbacks of the Web Audio API
as the page sees them (record: docs/designissues/2026-11-26-foafnaut-audio-plan.md, sections 2 and 9).

Written by `tools/webaudio-idl-table.py` from the Web Platform Tests' `interfaces/webaudio.idl`
(Web Audio API 1.1, extracted by Reffy). Change the IDL and run the tool; do not edit the lists.
Source file: fetched 2026-11-26 from
https://raw.githubusercontent.com/web-platform-tests/wpt/master/interfaces/webaudio.idl
(WPT commit not recorded), SHA-256 e12340db4b797f8ef949fb1984f70d53835ac3f9318ef92f0996b06ecd85396e.

Operation signatures are letters, as in `PageGl.Table`: u unsigned long, i long, l unsigned long
long, f float, d double, b boolean, s DOMString, a object, v undefined, h EventHandler,
`O` and a name for an interface, dictionary, enum or typed array, `Q` sequence, `Z` FrozenArray,
`R` record, `P` promise, `(x/y)` a union, `?` after a type nullable, `~` before an optional
argument; `|` separates overloads. Not kept: extended attributes of members, return types,
argument names.
-/

namespace L4Factoidal.WebAudio.Idl

/-- An attribute: name, IDL type text, read-only. -/
structure Attr where
  name : String
  type : String
  readOnly : Bool

/-- An operation or constructor: name, the fewest arguments an overload takes, and the argument types
of each overload. -/
structure Op where
  name : String
  minArgs : Nat
  sigs : String

/-- An interface. `ext` is the text of its extended attributes (`Exposed=Window`, ...); `ctor` is the
`constructor` operation, none when the IDL gives none; `other` holds members not kept as data
(`maplike`). -/
structure Iface where
  name : String
  parent : String
  ext : String
  ctor : Option Op
  attrs : List Attr
  ops : List Op
  statics : List Op
  other : List String

/-- An enum: name and values. -/
structure Enum where
  name : String
  values : List String

/-- A dictionary member: name, IDL type text, required, and default value text (empty: no default). -/
structure Member where
  name : String
  type : String
  required : Bool
  default : String

/-- A dictionary: name, parent (empty: none) and its own members. -/
structure Dict where
  name : String
  parent : String
  members : List Member

/-- A callback type: name, return type letter, argument type letters. -/
structure Callback where
  name : String
  ret : String
  args : String

/-- Every interface of `webaudio.idl`, in IDL order. -/
def interfaces : List Iface :=
[
    { name := "BaseAudioContext", parent := "EventTarget", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"destination", "AudioDestinationNode", true⟩,
      ⟨"sampleRate", "float", true⟩,
      ⟨"currentTime", "double", true⟩,
      ⟨"listener", "AudioListener", true⟩,
      ⟨"state", "AudioContextState", true⟩,
      ⟨"renderQuantumSize", "unsigned long", true⟩,
      ⟨"audioWorklet", "AudioWorklet", true⟩,
      ⟨"onstatechange", "EventHandler", false⟩],
      ops := [
      ⟨"createAnalyser", 0, ""⟩,
      ⟨"createBiquadFilter", 0, ""⟩,
      ⟨"createBuffer", 3, "u,u,f"⟩,
      ⟨"createBufferSource", 0, ""⟩,
      ⟨"createChannelMerger", 0, "~u"⟩,
      ⟨"createChannelSplitter", 0, "~u"⟩,
      ⟨"createConstantSource", 0, ""⟩,
      ⟨"createConvolver", 0, ""⟩,
      ⟨"createDelay", 0, "~d"⟩,
      ⟨"createDynamicsCompressor", 0, ""⟩,
      ⟨"createGain", 0, ""⟩,
      ⟨"createIIRFilter", 2, "Qd,Qd"⟩,
      ⟨"createOscillator", 0, ""⟩,
      ⟨"createPanner", 0, ""⟩,
      ⟨"createPeriodicWave", 2, "Qf,Qf,~OPeriodicWaveConstraints"⟩,
      ⟨"createScriptProcessor", 0, "~u,~u,~u"⟩,
      ⟨"createStereoPanner", 0, ""⟩,
      ⟨"createWaveShaper", 0, ""⟩,
      ⟨"decodeAudioData", 1, "OArrayBuffer,~ODecodeSuccessCallback?,~ODecodeErrorCallback?"⟩],
      statics := [],
      other := [] },
    { name := "AudioContext", parent := "BaseAudioContext", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 0, "~OAudioContextOptions"⟩,
      attrs := [
      ⟨"baseLatency", "double", true⟩,
      ⟨"outputLatency", "double", true⟩,
      ⟨"sinkId", "(DOMString or AudioSinkInfo)", true⟩,
      ⟨"onsinkchange", "EventHandler", false⟩,
      ⟨"onerror", "EventHandler", false⟩,
      ⟨"playbackStats", "AudioPlaybackStats", true⟩],
      ops := [
      ⟨"getOutputTimestamp", 0, ""⟩,
      ⟨"resume", 0, ""⟩,
      ⟨"suspend", 0, ""⟩,
      ⟨"close", 0, ""⟩,
      ⟨"setSinkId", 1, "(s/OAudioSinkOptions)"⟩,
      ⟨"createMediaElementSource", 1, "OHTMLMediaElement"⟩,
      ⟨"createMediaStreamSource", 1, "OMediaStream"⟩,
      ⟨"createMediaStreamTrackSource", 1, "OMediaStreamTrack"⟩,
      ⟨"createMediaStreamDestination", 0, ""⟩],
      statics := [],
      other := [] },
    { name := "AudioSinkInfo", parent := "", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"type", "AudioSinkType", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "OfflineAudioContext", parent := "BaseAudioContext", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OOfflineAudioContextOptions|u,u,f"⟩,
      attrs := [
      ⟨"length", "unsigned long?", true⟩,
      ⟨"oncomplete", "EventHandler", false⟩],
      ops := [
      ⟨"startRendering", 0, "~u?"⟩,
      ⟨"resume", 0, ""⟩,
      ⟨"suspend", 1, "d"⟩,
      ⟨"close", 0, ""⟩],
      statics := [],
      other := [] },
    { name := "OfflineAudioCompletionEvent", parent := "Event", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "s,OOfflineAudioCompletionEventInit"⟩,
      attrs := [
      ⟨"renderedBuffer", "AudioBuffer", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioBuffer", parent := "", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OAudioBufferOptions"⟩,
      attrs := [
      ⟨"sampleRate", "float", true⟩,
      ⟨"length", "unsigned long", true⟩,
      ⟨"duration", "double", true⟩,
      ⟨"numberOfChannels", "unsigned long", true⟩],
      ops := [
      ⟨"getChannelData", 1, "u"⟩,
      ⟨"copyFromChannel", 2, "OFloat32Array,u,~u"⟩,
      ⟨"copyToChannel", 2, "OFloat32Array,u,~u"⟩],
      statics := [],
      other := [] },
    { name := "AudioNode", parent := "EventTarget", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"context", "BaseAudioContext", true⟩,
      ⟨"numberOfInputs", "unsigned long", true⟩,
      ⟨"numberOfOutputs", "unsigned long", true⟩,
      ⟨"channelCount", "unsigned long", false⟩,
      ⟨"channelCountMode", "ChannelCountMode", false⟩,
      ⟨"channelInterpretation", "ChannelInterpretation", false⟩],
      ops := [
      ⟨"connect", 1, "OAudioNode,~u,~u|OAudioParam,~u"⟩,
      ⟨"disconnect", 0, "|u|OAudioNode|OAudioNode,u|OAudioNode,u,u|OAudioParam|OAudioParam,u"⟩],
      statics := [],
      other := [] },
    { name := "AudioParam", parent := "", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"value", "float", false⟩,
      ⟨"automationRate", "AutomationRate", false⟩,
      ⟨"defaultValue", "float", true⟩,
      ⟨"minValue", "float", true⟩,
      ⟨"maxValue", "float", true⟩],
      ops := [
      ⟨"setValueAtTime", 2, "f,d"⟩,
      ⟨"linearRampToValueAtTime", 2, "f,d"⟩,
      ⟨"exponentialRampToValueAtTime", 2, "f,d"⟩,
      ⟨"setTargetAtTime", 3, "f,d,f"⟩,
      ⟨"setValueCurveAtTime", 3, "Qf,d,d"⟩,
      ⟨"cancelScheduledValues", 1, "d"⟩,
      ⟨"cancelAndHoldAtTime", 1, "d"⟩],
      statics := [],
      other := [] },
    { name := "AudioScheduledSourceNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"onended", "EventHandler", false⟩],
      ops := [
      ⟨"start", 0, "~d"⟩,
      ⟨"stop", 0, "~d"⟩],
      statics := [],
      other := [] },
    { name := "AnalyserNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OAnalyserOptions"⟩,
      attrs := [
      ⟨"fftSize", "unsigned long", false⟩,
      ⟨"frequencyBinCount", "unsigned long", true⟩,
      ⟨"minDecibels", "double", false⟩,
      ⟨"maxDecibels", "double", false⟩,
      ⟨"smoothingTimeConstant", "double", false⟩],
      ops := [
      ⟨"getFloatFrequencyData", 1, "OFloat32Array"⟩,
      ⟨"getByteFrequencyData", 1, "OUint8Array"⟩,
      ⟨"getFloatTimeDomainData", 1, "OFloat32Array"⟩,
      ⟨"getByteTimeDomainData", 1, "OUint8Array"⟩],
      statics := [],
      other := [] },
    { name := "AudioBufferSourceNode", parent := "AudioScheduledSourceNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OAudioBufferSourceOptions"⟩,
      attrs := [
      ⟨"buffer", "AudioBuffer?", false⟩,
      ⟨"playbackRate", "AudioParam", true⟩,
      ⟨"detune", "AudioParam", true⟩,
      ⟨"loop", "boolean", false⟩,
      ⟨"loopStart", "double", false⟩,
      ⟨"loopEnd", "double", false⟩],
      ops := [
      ⟨"start", 0, "~d,~d,~d"⟩],
      statics := [],
      other := [] },
    { name := "AudioDestinationNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"maxChannelCount", "unsigned long", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioListener", parent := "", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"positionX", "AudioParam", true⟩,
      ⟨"positionY", "AudioParam", true⟩,
      ⟨"positionZ", "AudioParam", true⟩,
      ⟨"forwardX", "AudioParam", true⟩,
      ⟨"forwardY", "AudioParam", true⟩,
      ⟨"forwardZ", "AudioParam", true⟩,
      ⟨"upX", "AudioParam", true⟩,
      ⟨"upY", "AudioParam", true⟩,
      ⟨"upZ", "AudioParam", true⟩],
      ops := [
      ⟨"setPosition", 3, "f,f,f"⟩,
      ⟨"setOrientation", 6, "f,f,f,f,f,f"⟩],
      statics := [],
      other := [] },
    { name := "AudioProcessingEvent", parent := "Event", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "s,OAudioProcessingEventInit"⟩,
      attrs := [
      ⟨"playbackTime", "double", true⟩,
      ⟨"inputBuffer", "AudioBuffer", true⟩,
      ⟨"outputBuffer", "AudioBuffer", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "BiquadFilterNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OBiquadFilterOptions"⟩,
      attrs := [
      ⟨"type", "BiquadFilterType", false⟩,
      ⟨"frequency", "AudioParam", true⟩,
      ⟨"detune", "AudioParam", true⟩,
      ⟨"Q", "AudioParam", true⟩,
      ⟨"gain", "AudioParam", true⟩],
      ops := [
      ⟨"getFrequencyResponse", 3, "OFloat32Array,OFloat32Array,OFloat32Array"⟩],
      statics := [],
      other := [] },
    { name := "ChannelMergerNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OChannelMergerOptions"⟩,
      attrs := [],
      ops := [],
      statics := [],
      other := [] },
    { name := "ChannelSplitterNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OChannelSplitterOptions"⟩,
      attrs := [],
      ops := [],
      statics := [],
      other := [] },
    { name := "ConstantSourceNode", parent := "AudioScheduledSourceNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OConstantSourceOptions"⟩,
      attrs := [
      ⟨"offset", "AudioParam", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "ConvolverNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OConvolverOptions"⟩,
      attrs := [
      ⟨"buffer", "AudioBuffer?", false⟩,
      ⟨"normalize", "boolean", false⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "DelayNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~ODelayOptions"⟩,
      attrs := [
      ⟨"delayTime", "AudioParam", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "DynamicsCompressorNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~ODynamicsCompressorOptions"⟩,
      attrs := [
      ⟨"threshold", "AudioParam", true⟩,
      ⟨"knee", "AudioParam", true⟩,
      ⟨"ratio", "AudioParam", true⟩,
      ⟨"reduction", "float", true⟩,
      ⟨"attack", "AudioParam", true⟩,
      ⟨"release", "AudioParam", true⟩,
      ⟨"makeupGain", "AudioParam", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "GainNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OGainOptions"⟩,
      attrs := [
      ⟨"gain", "AudioParam", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "IIRFilterNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "OBaseAudioContext,OIIRFilterOptions"⟩,
      attrs := [],
      ops := [
      ⟨"getFrequencyResponse", 3, "OFloat32Array,OFloat32Array,OFloat32Array"⟩],
      statics := [],
      other := [] },
    { name := "MediaElementAudioSourceNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "OAudioContext,OMediaElementAudioSourceOptions"⟩,
      attrs := [
      ⟨"mediaElement", "HTMLMediaElement", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "MediaStreamAudioDestinationNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OAudioContext,~OAudioNodeOptions"⟩,
      attrs := [
      ⟨"stream", "MediaStream", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "MediaStreamAudioSourceNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "OAudioContext,OMediaStreamAudioSourceOptions"⟩,
      attrs := [
      ⟨"mediaStream", "MediaStream", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "MediaStreamTrackAudioSourceNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 2, "OAudioContext,OMediaStreamTrackAudioSourceOptions"⟩,
      attrs := [],
      ops := [],
      statics := [],
      other := [] },
    { name := "OscillatorNode", parent := "AudioScheduledSourceNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OOscillatorOptions"⟩,
      attrs := [
      ⟨"type", "OscillatorType", false⟩,
      ⟨"frequency", "AudioParam", true⟩,
      ⟨"detune", "AudioParam", true⟩],
      ops := [
      ⟨"setPeriodicWave", 1, "OPeriodicWave"⟩],
      statics := [],
      other := [] },
    { name := "PannerNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OPannerOptions"⟩,
      attrs := [
      ⟨"panningModel", "PanningModelType", false⟩,
      ⟨"positionX", "AudioParam", true⟩,
      ⟨"positionY", "AudioParam", true⟩,
      ⟨"positionZ", "AudioParam", true⟩,
      ⟨"orientationX", "AudioParam", true⟩,
      ⟨"orientationY", "AudioParam", true⟩,
      ⟨"orientationZ", "AudioParam", true⟩,
      ⟨"distanceModel", "DistanceModelType", false⟩,
      ⟨"refDistance", "double", false⟩,
      ⟨"maxDistance", "double", false⟩,
      ⟨"rolloffFactor", "double", false⟩,
      ⟨"coneInnerAngle", "double", false⟩,
      ⟨"coneOuterAngle", "double", false⟩,
      ⟨"coneOuterGain", "double", false⟩],
      ops := [
      ⟨"setPosition", 3, "f,f,f"⟩,
      ⟨"setOrientation", 3, "f,f,f"⟩],
      statics := [],
      other := [] },
    { name := "PeriodicWave", parent := "", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OPeriodicWaveOptions"⟩,
      attrs := [],
      ops := [],
      statics := [],
      other := [] },
    { name := "ScriptProcessorNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := none,
      attrs := [
      ⟨"onaudioprocess", "EventHandler", false⟩,
      ⟨"bufferSize", "long", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "StereoPannerNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OStereoPannerOptions"⟩,
      attrs := [
      ⟨"pan", "AudioParam", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "WaveShaperNode", parent := "AudioNode", ext := "Exposed=Window",
      ctor := some ⟨"constructor", 1, "OBaseAudioContext,~OWaveShaperOptions"⟩,
      attrs := [
      ⟨"curve", "Float32Array?", false⟩,
      ⟨"oversample", "OverSampleType", false⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioWorklet", parent := "Worklet", ext := "Exposed=Window, SecureContext",
      ctor := none,
      attrs := [
      ⟨"port", "MessagePort", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioWorkletGlobalScope", parent := "WorkletGlobalScope", ext := "Global=(Worklet, AudioWorklet), Exposed=AudioWorklet",
      ctor := none,
      attrs := [
      ⟨"currentFrame", "unsigned long long", true⟩,
      ⟨"currentTime", "double", true⟩,
      ⟨"sampleRate", "float", true⟩,
      ⟨"renderQuantumSize", "unsigned long", true⟩,
      ⟨"port", "MessagePort", true⟩],
      ops := [
      ⟨"registerProcessor", 2, "s,OAudioWorkletProcessorConstructor"⟩],
      statics := [],
      other := [] },
    { name := "AudioParamMap", parent := "", ext := "Exposed=Window",
      ctor := none,
      attrs := [],
      ops := [],
      statics := [],
      other := ["readonly maplike<DOMString, AudioParam>"] },
    { name := "AudioWorkletNode", parent := "AudioNode", ext := "Exposed=Window, SecureContext",
      ctor := some ⟨"constructor", 2, "OBaseAudioContext,s,~OAudioWorkletNodeOptions"⟩,
      attrs := [
      ⟨"parameters", "AudioParamMap", true⟩,
      ⟨"port", "MessagePort", true⟩,
      ⟨"onprocessorerror", "EventHandler", false⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioWorkletProcessor", parent := "", ext := "Exposed=AudioWorklet",
      ctor := some ⟨"constructor", 0, ""⟩,
      attrs := [
      ⟨"port", "MessagePort", true⟩],
      ops := [],
      statics := [],
      other := [] },
    { name := "AudioPlaybackStats", parent := "", ext := "Exposed=Window, SecureContext",
      ctor := none,
      attrs := [
      ⟨"underrunDuration", "double", true⟩,
      ⟨"underrunEvents", "unsigned long", true⟩,
      ⟨"totalDuration", "double", true⟩,
      ⟨"averageLatency", "double", true⟩,
      ⟨"minimumLatency", "double", true⟩,
      ⟨"maximumLatency", "double", true⟩],
      ops := [
      ⟨"resetLatency", 0, ""⟩,
      ⟨"toJSON", 0, ""⟩],
      statics := [],
      other := [] }]

/-- Every enum of `webaudio.idl`, in IDL order. -/
def enums : List Enum :=
[
    ⟨"AudioContextState", ["suspended", "running", "closed", "interrupted"]⟩,
    ⟨"AudioContextRenderSizeCategory", ["default", "hardware"]⟩,
    ⟨"AudioContextLatencyCategory", ["balanced", "interactive", "playback"]⟩,
    ⟨"AudioSinkType", ["none"]⟩,
    ⟨"ChannelCountMode", ["max", "clamped-max", "explicit"]⟩,
    ⟨"ChannelInterpretation", ["speakers", "discrete"]⟩,
    ⟨"AutomationRate", ["a-rate", "k-rate"]⟩,
    ⟨"BiquadFilterType", ["lowpass", "highpass", "bandpass", "lowshelf", "highshelf", "peaking", "notch", "allpass"]⟩,
    ⟨"MakeupGainOptions", ["automatic"]⟩,
    ⟨"OscillatorType", ["sine", "square", "sawtooth", "triangle", "custom"]⟩,
    ⟨"PanningModelType", ["equalpower", "HRTF"]⟩,
    ⟨"DistanceModelType", ["linear", "inverse", "exponential"]⟩,
    ⟨"OverSampleType", ["none", "2x", "4x"]⟩]

/-- Every dictionary of `webaudio.idl`, in IDL order. -/
def dicts : List Dict :=
[
    ⟨"AudioContextOptions", "", [
      ⟨"latencyHint", "(AudioContextLatencyCategory or double)", false, "\"interactive\""⟩,
      ⟨"sampleRate", "float", false, ""⟩,
      ⟨"sinkId", "(DOMString or AudioSinkOptions)", false, ""⟩,
      ⟨"renderSizeHint", "(AudioContextRenderSizeCategory or unsigned long)", false, "\"default\""⟩]⟩,
    ⟨"AudioSinkOptions", "", [
      ⟨"type", "AudioSinkType", true, ""⟩]⟩,
    ⟨"AudioTimestamp", "", [
      ⟨"contextTime", "double", false, ""⟩,
      ⟨"performanceTime", "DOMHighResTimeStamp", false, ""⟩]⟩,
    ⟨"OfflineAudioContextOptions", "", [
      ⟨"numberOfChannels", "unsigned long", false, "1"⟩,
      ⟨"length", "unsigned long?", false, "null"⟩,
      ⟨"sampleRate", "float", true, ""⟩,
      ⟨"renderSizeHint", "(AudioContextRenderSizeCategory or unsigned long)", false, "\"default\""⟩]⟩,
    ⟨"OfflineAudioCompletionEventInit", "EventInit", [
      ⟨"renderedBuffer", "AudioBuffer", true, ""⟩]⟩,
    ⟨"AudioBufferOptions", "", [
      ⟨"numberOfChannels", "unsigned long", false, "1"⟩,
      ⟨"length", "unsigned long", true, ""⟩,
      ⟨"sampleRate", "float", true, ""⟩]⟩,
    ⟨"AudioNodeOptions", "", [
      ⟨"channelCount", "unsigned long", false, ""⟩,
      ⟨"channelCountMode", "ChannelCountMode", false, ""⟩,
      ⟨"channelInterpretation", "ChannelInterpretation", false, ""⟩]⟩,
    ⟨"AnalyserOptions", "AudioNodeOptions", [
      ⟨"fftSize", "unsigned long", false, "2048"⟩,
      ⟨"maxDecibels", "double", false, "-30"⟩,
      ⟨"minDecibels", "double", false, "-100"⟩,
      ⟨"smoothingTimeConstant", "double", false, "0.8"⟩]⟩,
    ⟨"AudioBufferSourceOptions", "", [
      ⟨"buffer", "AudioBuffer?", false, ""⟩,
      ⟨"detune", "float", false, "0"⟩,
      ⟨"loop", "boolean", false, "false"⟩,
      ⟨"loopEnd", "double", false, "0"⟩,
      ⟨"loopStart", "double", false, "0"⟩,
      ⟨"playbackRate", "float", false, "1"⟩]⟩,
    ⟨"AudioProcessingEventInit", "EventInit", [
      ⟨"playbackTime", "double", true, ""⟩,
      ⟨"inputBuffer", "AudioBuffer", true, ""⟩,
      ⟨"outputBuffer", "AudioBuffer", true, ""⟩]⟩,
    ⟨"BiquadFilterOptions", "AudioNodeOptions", [
      ⟨"type", "BiquadFilterType", false, "\"lowpass\""⟩,
      ⟨"Q", "float", false, "1"⟩,
      ⟨"detune", "float", false, "0"⟩,
      ⟨"frequency", "float", false, "350"⟩,
      ⟨"gain", "float", false, "0"⟩]⟩,
    ⟨"ChannelMergerOptions", "AudioNodeOptions", [
      ⟨"numberOfInputs", "unsigned long", false, "6"⟩]⟩,
    ⟨"ChannelSplitterOptions", "AudioNodeOptions", [
      ⟨"numberOfOutputs", "unsigned long", false, "6"⟩]⟩,
    ⟨"ConstantSourceOptions", "", [
      ⟨"offset", "float", false, "1"⟩]⟩,
    ⟨"ConvolverOptions", "AudioNodeOptions", [
      ⟨"buffer", "AudioBuffer?", false, ""⟩,
      ⟨"disableNormalization", "boolean", false, "false"⟩]⟩,
    ⟨"DelayOptions", "AudioNodeOptions", [
      ⟨"maxDelayTime", "double", false, "1"⟩,
      ⟨"delayTime", "double", false, "0"⟩]⟩,
    ⟨"DynamicsCompressorOptions", "AudioNodeOptions", [
      ⟨"attack", "float", false, "0.003"⟩,
      ⟨"knee", "float", false, "30"⟩,
      ⟨"makeupGain", "(float or MakeupGainOptions)", false, "\"automatic\""⟩,
      ⟨"ratio", "float", false, "12"⟩,
      ⟨"release", "float", false, "0.25"⟩,
      ⟨"threshold", "float", false, "-24"⟩]⟩,
    ⟨"GainOptions", "AudioNodeOptions", [
      ⟨"gain", "float", false, "1.0"⟩]⟩,
    ⟨"IIRFilterOptions", "AudioNodeOptions", [
      ⟨"feedforward", "sequence<double>", true, ""⟩,
      ⟨"feedback", "sequence<double>", true, ""⟩]⟩,
    ⟨"MediaElementAudioSourceOptions", "", [
      ⟨"mediaElement", "HTMLMediaElement", true, ""⟩]⟩,
    ⟨"MediaStreamAudioSourceOptions", "", [
      ⟨"mediaStream", "MediaStream", true, ""⟩]⟩,
    ⟨"MediaStreamTrackAudioSourceOptions", "", [
      ⟨"mediaStreamTrack", "MediaStreamTrack", true, ""⟩]⟩,
    ⟨"OscillatorOptions", "AudioNodeOptions", [
      ⟨"type", "OscillatorType", false, "\"sine\""⟩,
      ⟨"frequency", "float", false, "440"⟩,
      ⟨"detune", "float", false, "0"⟩,
      ⟨"periodicWave", "PeriodicWave", false, ""⟩]⟩,
    ⟨"PannerOptions", "AudioNodeOptions", [
      ⟨"panningModel", "PanningModelType", false, "\"equalpower\""⟩,
      ⟨"distanceModel", "DistanceModelType", false, "\"inverse\""⟩,
      ⟨"positionX", "float", false, "0"⟩,
      ⟨"positionY", "float", false, "0"⟩,
      ⟨"positionZ", "float", false, "0"⟩,
      ⟨"orientationX", "float", false, "1"⟩,
      ⟨"orientationY", "float", false, "0"⟩,
      ⟨"orientationZ", "float", false, "0"⟩,
      ⟨"refDistance", "double", false, "1"⟩,
      ⟨"maxDistance", "double", false, "10000"⟩,
      ⟨"rolloffFactor", "double", false, "1"⟩,
      ⟨"coneInnerAngle", "double", false, "360"⟩,
      ⟨"coneOuterAngle", "double", false, "360"⟩,
      ⟨"coneOuterGain", "double", false, "0"⟩]⟩,
    ⟨"PeriodicWaveConstraints", "", [
      ⟨"disableNormalization", "boolean", false, "false"⟩]⟩,
    ⟨"PeriodicWaveOptions", "PeriodicWaveConstraints", [
      ⟨"real", "sequence<float>", false, ""⟩,
      ⟨"imag", "sequence<float>", false, ""⟩]⟩,
    ⟨"StereoPannerOptions", "AudioNodeOptions", [
      ⟨"pan", "float", false, "0"⟩]⟩,
    ⟨"WaveShaperOptions", "AudioNodeOptions", [
      ⟨"curve", "sequence<float>", false, ""⟩,
      ⟨"oversample", "OverSampleType", false, "\"none\""⟩]⟩,
    ⟨"AudioWorkletNodeOptions", "AudioNodeOptions", [
      ⟨"numberOfInputs", "unsigned long", false, "1"⟩,
      ⟨"numberOfOutputs", "unsigned long", false, "1"⟩,
      ⟨"outputChannelCount", "sequence<unsigned long>", false, ""⟩,
      ⟨"parameterData", "record<DOMString, double>", false, ""⟩,
      ⟨"processorOptions", "object", false, ""⟩]⟩,
    ⟨"AudioParamDescriptor", "", [
      ⟨"name", "DOMString", true, ""⟩,
      ⟨"defaultValue", "float", false, "0"⟩,
      ⟨"minValue", "float", false, "-3.4028235e38"⟩,
      ⟨"maxValue", "float", false, "3.4028235e38"⟩,
      ⟨"automationRate", "AutomationRate", false, "\"a-rate\""⟩]⟩]

/-- Every callback type of `webaudio.idl`, in IDL order. -/
def callbacks : List Callback :=
[
    ⟨"DecodeErrorCallback", "v", "ODOMException"⟩,
    ⟨"DecodeSuccessCallback", "v", "OAudioBuffer"⟩,
    ⟨"AudioWorkletProcessorConstructor", "OAudioWorkletProcessor", "a"⟩,
    ⟨"AudioWorkletProcessCallback", "b", "ZZOFloat32Array,ZZOFloat32Array,a"⟩]

/-! ## Lookups -/

def findInterface (n : String) : Option Iface := interfaces.find? (·.name == n)

def findEnum (n : String) : Option Enum := enums.find? (·.name == n)

def findDict (n : String) : Option Dict := dicts.find? (·.name == n)

/-- The values of an enum. -/
def enumValues (n : String) : Option (List String) := (findEnum n).map (·.values)

/-- The parents of an interface, nearest first, up to eight steps (the IDL's deepest chain has three). -/
def ancestors (n : String) : List String :=
  go 8 n
where
  go : Nat → String → List String
    | 0, _ => []
    | k + 1, n =>
      match findInterface n with
      | none => []
      | some i => if i.parent == "" then [] else i.parent :: go k i.parent

/-- The fewest arguments of the operation `op` that the interface itself declares. -/
def opMinArgs (iface op : String) : Option Nat :=
  (findInterface iface).bind fun i => (i.ops.find? (·.name == op)).map (·.minArgs)

/-- Whether the attribute `a` that the interface itself declares is read-only. -/
def attrReadOnly (iface a : String) : Option Bool :=
  (findInterface iface).bind fun i => (i.attrs.find? (·.name == a)).map (·.readOnly)

/-- The default text of a member of the dictionary itself (empty: the member has no default). -/
def dictDefault (dict m : String) : Option String :=
  (findDict dict).bind fun d => (d.members.find? (·.name == m)).map (·.default)

/-! ## Checks against the IDL text

Each fact below can be read off `webaudio.idl`. A `#guard` that fails stops the build, so a change
of the IDL that the generator reads is seen here first. -/

#guard interfaces.length == 39
#guard enums.length == 13
#guard dicts.length == 30
#guard callbacks.length == 4
#guard (enums.map (·.name)).eraseDups.length == enums.length
#guard (dicts.map (·.name)).eraseDups.length == dicts.length

-- Parents.
#guard (findInterface "OfflineAudioContext").map (·.parent) == some "BaseAudioContext"
#guard (findInterface "AudioContext").map (·.parent) == some "BaseAudioContext"
#guard (findInterface "AudioBufferSourceNode").map (·.parent) == some "AudioScheduledSourceNode"
#guard (findInterface "OscillatorNode").map (·.parent) == some "AudioScheduledSourceNode"
#guard (findInterface "AudioScheduledSourceNode").map (·.parent) == some "AudioNode"
#guard (findInterface "BaseAudioContext").map (·.parent) == some "EventTarget"
#guard (findInterface "AudioParam").map (·.parent) == some ""
#guard ancestors "OscillatorNode" == ["AudioScheduledSourceNode", "AudioNode", "EventTarget"]

-- AudioNode.
#guard (findInterface "AudioNode").map (·.attrs.map (·.name)) ==
  some ["context", "numberOfInputs", "numberOfOutputs", "channelCount", "channelCountMode",
    "channelInterpretation"]
#guard attrReadOnly "AudioNode" "context" == some true
#guard attrReadOnly "AudioNode" "channelCount" == some false
#guard opMinArgs "AudioNode" "connect" == some 1
#guard opMinArgs "AudioNode" "disconnect" == some 0

-- BaseAudioContext factory methods and their fewest arguments.
#guard opMinArgs "BaseAudioContext" "createGain" == some 0
#guard opMinArgs "BaseAudioContext" "createBuffer" == some 3
#guard opMinArgs "BaseAudioContext" "createIIRFilter" == some 2
#guard opMinArgs "BaseAudioContext" "createPeriodicWave" == some 2
#guard opMinArgs "BaseAudioContext" "createDelay" == some 0
#guard opMinArgs "BaseAudioContext" "createChannelMerger" == some 0
#guard opMinArgs "BaseAudioContext" "decodeAudioData" == some 1
#guard ((findInterface "BaseAudioContext").map (fun i => (i.ops.filter (·.name.startsWith "create")).length)) ==
  some 18
#guard attrReadOnly "BaseAudioContext" "onstatechange" == some false

-- AudioParam.
#guard (findInterface "AudioParam").map (·.ops.map (·.name)) ==
  some ["setValueAtTime", "linearRampToValueAtTime", "exponentialRampToValueAtTime", "setTargetAtTime",
    "setValueCurveAtTime", "cancelScheduledValues", "cancelAndHoldAtTime"]
#guard opMinArgs "AudioParam" "setTargetAtTime" == some 3
#guard opMinArgs "AudioParam" "setValueCurveAtTime" == some 3
#guard opMinArgs "AudioParam" "cancelScheduledValues" == some 1
#guard attrReadOnly "AudioParam" "value" == some false
#guard attrReadOnly "AudioParam" "defaultValue" == some true

-- Constructors.
#guard ((findInterface "OfflineAudioContext").bind (·.ctor)).map (·.minArgs) == some 1
#guard ((findInterface "AudioContext").bind (·.ctor)).map (·.minArgs) == some 0
#guard ((findInterface "OscillatorNode").bind (·.ctor)).map (·.minArgs) == some 1
#guard ((findInterface "AudioNode").bind (·.ctor)).isNone

-- Enums.
#guard enumValues "OscillatorType" == some ["sine", "square", "sawtooth", "triangle", "custom"]
#guard enumValues "BiquadFilterType" ==
  some ["lowpass", "highpass", "bandpass", "lowshelf", "highshelf", "peaking", "notch", "allpass"]
#guard enumValues "ChannelCountMode" == some ["max", "clamped-max", "explicit"]
#guard enumValues "ChannelInterpretation" == some ["speakers", "discrete"]
#guard enumValues "AutomationRate" == some ["a-rate", "k-rate"]
#guard enumValues "AudioContextState" == some ["suspended", "running", "closed", "interrupted"]
#guard enumValues "OverSampleType" == some ["none", "2x", "4x"]

-- Dictionary defaults.
#guard dictDefault "AudioBufferSourceOptions" "detune" == some "0"
#guard dictDefault "AudioBufferSourceOptions" "loop" == some "false"
#guard dictDefault "AudioBufferSourceOptions" "playbackRate" == some "1"
#guard dictDefault "AudioBufferSourceOptions" "buffer" == some ""
#guard dictDefault "OscillatorOptions" "type" == some "\"sine\""
#guard dictDefault "OscillatorOptions" "frequency" == some "440"
#guard dictDefault "BiquadFilterOptions" "type" == some "\"lowpass\""
#guard dictDefault "BiquadFilterOptions" "frequency" == some "350"
#guard dictDefault "BiquadFilterOptions" "Q" == some "1"
#guard (findDict "AudioNodeOptions").map (·.members.map (·.name)) ==
  some ["channelCount", "channelCountMode", "channelInterpretation"]
#guard (findDict "AudioNodeOptions").map (fun d => d.members.all (·.default == "")) == some true
#guard (findDict "OscillatorOptions").map (·.parent) == some "AudioNodeOptions"
#guard (findDict "OfflineAudioContextOptions").map (fun d => (d.members.filter (·.required)).map (·.name)) ==
  some ["sampleRate"]

/-- Invariant. Says: no two interfaces of the table have the same name. Does not say: that the table
holds every interface of the Web Audio API (it holds those of `webaudio.idl`). -/
theorem interface_names_nodup : (interfaces.map (·.name)).Nodup := by decide

end L4Factoidal.WebAudio.Idl
