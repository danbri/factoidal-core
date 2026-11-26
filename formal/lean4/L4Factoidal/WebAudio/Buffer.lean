import L4Factoidal.WebAudio.Kernels

/-!
# Web Audio: `AudioBuffer` and the `AudioBufferSourceNode` block kernel

Sections "The AudioBuffer Interface", "The AudioBufferSourceNode Interface" and "Playback of
AudioBuffer Contents" of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/), and the scheduling rules of
`AudioScheduledSourceNode`. Stage B of https://github.com/danbri/factoidal-core/issues/1169;
structure in `docs/designissues/2026-11-26-foafnaut-audio-plan.md` sections 4 and 9.

## Storage of the channel data (binary32)

The specification exposes channel data as `Float32Array`. Here each channel is a `FloatArray`
(64-bit `Float` slots) in which every stored value is a binary32 value: every write goes through
`toFloat32` (`toF32` below), which rounds to nearest-even, and a binary32 value converts to a
`Float` without loss. Reasons for this choice over a `ByteArray` of 4-byte groups:

* the block kernels of `WebAudio.Kernels` already use `FloatArray`, so a kernel reads a channel
  without a conversion per sample;
* a read needs no conversion; a `ByteArray` would need a bit-pattern to `Float32` to `Float`
  conversion for each sample.

The price is twice the memory of a `Float32Array`. The invariant "every stored value is a
binary32 value" holds because the only writers are `AudioBuffer.create` (zeros),
`copyToChannel` and `writeSample`, all of which round. It is not a field of the structure; the
test `#guard`s check it.

Processing is in 64-bit `Float`, as in `WebAudio.Kernels`; the output of the source kernel is not
rounded to binary32.

## What is proved

* `copyFromChannel` and `copyToChannel`: the error rule (`IndexSizeError` exactly when the channel
  number is not below the channel count), the index ranges (no read outside the buffer and no
  write outside the destination), the value of every element of the result, and that the channel
  count and the length of the buffer, and the shape of its data, are kept.
* `AudioBuffer.create` gives a well-formed buffer (channel count and length as given).
* The source kernel's output has the channel count the specification gives (the buffer's, one
  silent channel without a buffer, one silent channel after the end of playback of a buffer with
  more than one channel) and `n` frames in each channel.
* The output is silence at every frame before the start frame and at or after the stop frame, and
  from a source on which `start` was never called.

## What is tested only with `#guard`

Every statement about a `Float` value: interpolation, playback rate, loops, offset, duration,
sample rate conversion, binary32 rounding. Cases are named after the Web Platform Tests file
(`webaudio/the-audio-api/...`) they come from.

## Decisions where the specification leaves room

* Position arithmetic is done in buffer frames (`position_in_seconds * buffer.sampleRate`)
  instead of seconds. The specification's `dt * computedPlaybackRate` seconds per context frame
  become `computedPlaybackRate * buffer.sampleRate / context.sampleRate` buffer frames, so a
  buffer at 22050 Hz in a 44100 Hz context needs no separate correction (the figure "sample rate
  interpolation" in the specification). A value within 1e-9 frames of a whole frame is taken to
  be that frame (`snapFrames`), so that 3 x (1/44100) x 44100 reads frame 3 and not frame
  2.9999999999999996; the specification requires an exact frame to return that frame.
* Interpolation is linear. The frame after the last frame of the buffer is silence when the
  source does not loop, and the frame at the (floored) loop start when playback is inside the
  loop and the next frame is at or after the loop end ("as if the looped audio occurred in
  sequential regions", the specification's looping section).
* The reversed loop of the pseudocode (`loopStart` at or after the buffer duration while
  `loopEnd` is after `loopStart`) would make the `while` loops of the pseudocode run for ever.
  The looping section says "If any of these constraints are violated, the loop is considered to
  include the entire buffer contents", so after clamping `loopEnd` to the duration a loop with
  start not before end is the whole buffer.
* The pseudocode's `while` loops that wrap the playhead are computed by division, with one
  correction step; for a finite playhead the result is the pseudocode's result up to rounding.
* A sub-sample start time: the pseudocode starts playback at the first frame `f` with
  `f / sampleRate >= start`, with the playhead at `offset` on that frame. As the WPT
  `sub-sample-buffer-stitching.html` requires, the playhead on that first frame is further
  advanced by `(f - start * sampleRate)` frames of playback (`< 1` context frame): the signal is
  what it would have been, had playback begun at the exact `start` time. For `playbackRate` 0 the
  advance is 0 (WPT `audiobuffersource-playbackrate-zero.html`, second case).
* `start`, `stop` and the sample rate bounds: see `AudioBuffer.create` and `SourceState.start`.
  The sample rate range 3000 to 768000 Hz and the limit of 32 channels are the ones in the task
  description; the specification (section "Supported Sample Rates") requires only 8000 to 96000
  Hz and "at least 32 channels".

## Not done in this file

* `getChannelData` returns a copy of the channel, not a `Float32Array` that aliases the data; the
  "acquire the content" operation (detaching the arrays handed out by `getChannelData`) belongs
  to the script host.
* `AudioParam` automation: `params[0]` is `playbackRate` and `params[1]` is `detune`, both
  k-rate, supplied by the caller (as in `WebAudio.Kernels`). The k-rate value is the first
  value of the array.
* `loop`, `loopStart` and `loopEnd` changes between blocks take effect on the next block (the
  specification: "take effect on the next rendering quantum"); a change of `loop` from true to
  false clears the "entered loop" flag, a change of the loop points leaves the playhead where it
  is.
* The setter of `buffer` (`InvalidStateError` for a second non-null buffer) and the "acquire the
  content" snapshot: the caller holds `SourceConfig.buffer`.
* `ended` events and the cleanup of the node after playback: `SourceState.finished` is the
  flag; the graph module acts on it.
* `createBuffer`'s `NaN` and infinite arguments (`TypeError` by WebIDL): `create` refuses a
  non-finite sample rate as `notSupported`.
-/

namespace L4Factoidal.WebAudio.Buffer

open L4Factoidal.WebAudio.Kernels

/-! ## Errors -/

/-- The DOMException and JavaScript errors that the operations of this file can signal. -/
inductive Error where
  /-- `TypeError`: a non-finite `double` argument of `start` or `stop`. -/
  | typeError
  /-- `IndexSizeError`. -/
  | indexSize
  /-- `NotSupportedError`. -/
  | notSupported
  /-- `InvalidStateError`. -/
  | invalidState
  /-- `RangeError`. -/
  | range
  deriving DecidableEq, Repr

/-! ## binary32 values -/

/-- Round to the nearest binary32 value (ties to even), returned as a 64-bit `Float`. The value of
a `Float32Array` element after it is written. -/
def toF32 (x : Float) : Float := x.toFloat32.toFloat

/-- The 64-bit `Float` for positive infinity. -/
def inf : Float := 1.0 / 0.0

/-! ## Lemmas about `mkChan` values -/

theorem getF_push (a : FloatArray) (x : Float) (j : Nat) :
    getF (a.push x) j = if j < a.size then getF a j else if j = a.size then x else 0.0 := by
  cases a with
  | mk d =>
    simp only [getF, FloatArray.push, FloatArray.size, FloatArray.get!]
    by_cases h : j < d.size
    · have h1 : j < (d.push x).size := by simp; omega
      have h3 : j < d.size + 1 := by omega
      simp only [h, h3, if_true, Array.size_push]
      rw [getElem!_pos (d.push x) j h1, getElem!_pos d j h, Array.getElem_push_lt h]
    · by_cases h2 : j = d.size
      · subst h2
        have h1 : d.size < (d.push x).size := by simp
        simp only [Nat.lt_irrefl, if_false, if_true, Array.size_push, Nat.lt_succ_self]
        rw [getElem!_pos (d.push x) d.size h1]; simp
      · have h3 : ¬ j < d.size + 1 := by omega
        simp [h, h2, h3]

theorem getF_out_of_range (a : FloatArray) (j : Nat) (h : ¬ j < a.size) : getF a j = 0.0 := by
  simp [getF, h]

theorem getF_iter_push (f : Nat → Float) (k : Nat) :
    ∀ (i : Nat) (a : FloatArray) (j : Nat),
    getF (iter (fun j (a : FloatArray) => a.push (f j)) k i a) j =
      if j < a.size + k then (if j < a.size then getF a j else f (i + (j - a.size))) else 0.0 := by
  induction k with
  | zero =>
    intro i a j
    simp only [iter, Nat.add_zero]
    by_cases h : j < a.size
    · simp [h]
    · simp [h, getF_out_of_range a j h]
  | succ k ih =>
    intro i a j
    simp only [iter]
    rw [ih (i + 1) (a.push (f i)) j, size_push, getF_push]
    by_cases h1 : j < a.size
    · have h2 : j < a.size + 1 := by omega
      have h3 : j < a.size + 1 + k := by omega
      have h4 : j < a.size + (k + 1) := by omega
      simp [h1, h2, h3, h4]
    · by_cases h2 : j = a.size
      · subst h2
        have h3 : a.size < a.size + 1 + k := by omega
        have h4 : a.size < a.size + (k + 1) := by omega
        simp [h3, h4]
      · by_cases h5 : j < a.size + (k + 1)
        · have h6 : j < a.size + 1 + k := by omega
          have h7 : ¬ j < a.size + 1 := by omega
          simp only [h1, h2, h5, h6, h7, if_true, if_false]
          have : i + 1 + (j - (a.size + 1)) = i + (j - a.size) := by omega
          rw [this]
        · have h6 : ¬ j < a.size + 1 + k := by omega
          simp [h5, h6]

/-- Says: element `i` of `mkChan n f` is `f i` when `i < n` and 0 outside. Does not say: anything
about the values of `f`. -/
theorem getF_mkChan (n : Nat) (f : Nat → Float) (i : Nat) :
    getF (mkChan n f) i = if i < n then f i else 0.0 := by
  have := getF_iter_push f n 0 ⟨#[]⟩ i
  unfold mkChan
  rw [this]
  simp [FloatArray.size]

/-! ## AudioBuffer -/

/-- `AudioBuffer`: the slots `[[number of channels]]`, `[[length]]`, `[[sample rate]]` and
`[[internal data]]`. `sampleRate` is a binary32 value (the IDL type is `float`). Each channel of
`data` holds binary32 values (see the module comment). -/
structure AudioBuffer where
  numberOfChannels : Nat
  length : Nat
  sampleRate : Float
  data : Array FloatArray

/-- The buffer is well formed: one channel array for each channel, `length` frames in each. -/
def AudioBuffer.WF (b : AudioBuffer) : Prop :=
  b.data.size = b.numberOfChannels ∧ ∀ c ∈ b.data, c.size = b.length

/-- `duration` attribute: the length divided by the sample rate. -/
def AudioBuffer.duration (b : AudioBuffer) : Float := b.length.toFloat / b.sampleRate

/-- The constructor of `AudioBuffer` (and `createBuffer`). `NotSupportedError` when the number of
channels is 0 or above 32, the length is 0, or the sample rate (rounded to binary32, as the IDL
`float` is) is not within 3000 to 768000 Hz (a `NaN` is not). The data is zero. -/
def AudioBuffer.create (channels length : Nat) (sampleRate : Float) : Except Error AudioBuffer :=
  let sr := toF32 sampleRate
  if 1 ≤ channels ∧ channels ≤ 32 ∧ 1 ≤ length ∧ sr ≥ 3000.0 ∧ sr ≤ 768000.0 then
    .ok { numberOfChannels := channels, length, sampleRate := sr
          data := Array.replicate channels (mkChan length fun _ => 0.0) }
  else .error .notSupported

/-- Says: a buffer from `create` is well formed and has the given channel count and length.
Does not say: the sample rate is the argument (it is rounded to binary32). -/
theorem create_wf (channels length : Nat) (sampleRate : Float) (b : AudioBuffer)
    (h : AudioBuffer.create channels length sampleRate = .ok b) :
    b.WF ∧ b.numberOfChannels = channels ∧ b.length = length := by
  unfold AudioBuffer.create at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨⟨by simp, ?_⟩, rfl, rfl⟩
    intro c hc
    have := Array.eq_of_mem_replicate hc
    subst this
    exact mkChan_size _ _
  · cases h

/-- Says: `create` signals `NotSupportedError`, and nothing else, when a bound is broken.
Does not say: which bound. -/
theorem create_error (channels length : Nat) (sampleRate : Float) (e : Error)
    (h : AudioBuffer.create channels length sampleRate = .error e) : e = .notSupported := by
  unfold AudioBuffer.create at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

/-- `getChannelData(channel)` as a value: a copy of the channel; `IndexSizeError` when `channel`
is not below `numberOfChannels`. -/
def AudioBuffer.getChannelData (b : AudioBuffer) (channel : Nat) : Except Error FloatArray :=
  if channel < b.numberOfChannels then .ok (b.data.getD channel ⟨#[]⟩) else .error .indexSize

/-- Says: `getChannelData` fails exactly when the index is not below the channel count, and
then with `IndexSizeError`; on a well-formed buffer the result has `length` frames.
Does not say: that two calls give the same array object. -/
theorem getChannelData_spec (b : AudioBuffer) (hb : b.WF) (ch : Nat) :
    (ch < b.numberOfChannels →
      ∃ a, b.getChannelData ch = .ok a ∧ a.size = b.length) ∧
    (¬ ch < b.numberOfChannels → b.getChannelData ch = .error .indexSize) := by
  constructor
  · intro h
    refine ⟨b.data.getD ch ⟨#[]⟩, by simp [AudioBuffer.getChannelData, h], ?_⟩
    have hs : ch < b.data.size := by rw [hb.1]; exact h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
    exact hb.2 _ (Array.getElem_mem hs)
  · intro h; simp [AudioBuffer.getChannelData, h]

/-- A write `data[index] = value` to channel `channel` through the `Float32Array` that
`getChannelData` returns: the value is rounded to binary32; an index outside the channel, or a
channel outside the buffer, changes nothing (an out-of-range typed array write is ignored). -/
def AudioBuffer.writeSample (b : AudioBuffer) (channel index : Nat) (value : Float) : AudioBuffer :=
  if channel < b.data.size then
    let cur := b.data[channel]!
    { b with data := Array.ofFn (n := b.data.size) fun c =>
        if c.1 = channel then mkChan cur.size (fun i => if i = index then toF32 value else getF cur i)
        else b.data[c.1]! }
  else b

/-- Number of frames copied by `copyFromChannel` and `copyToChannel`:
`max(0, min(N_b - k, N_f))` (natural subtraction is already clipped at 0). -/
def copyCount (bufferLength offset arrayLength : Nat) : Nat := min (bufferLength - offset) arrayLength

/-- `copyFromChannel(destination, channelNumber, bufferOffset)`: returns the new content of
`destination`. `IndexSizeError` when `channelNumber` is not below the channel count. The first
`copyCount` elements are the channel's elements from `bufferOffset`; the others are not
modified. -/
def AudioBuffer.copyFromChannel (b : AudioBuffer) (destination : FloatArray) (channelNumber : Nat)
    (bufferOffset : Nat := 0) : Except Error FloatArray :=
  if channelNumber < b.numberOfChannels then
    let src := b.data.getD channelNumber ⟨#[]⟩
    let cnt := copyCount b.length bufferOffset destination.size
    .ok (mkChan destination.size fun j =>
      if j < cnt then getF src (bufferOffset + j) else getF destination j)
  else .error .indexSize

/-- `copyToChannel(source, channelNumber, bufferOffset)`: returns the new buffer. `IndexSizeError`
when `channelNumber` is not below the channel count. The `copyCount` frames from `bufferOffset`
are the elements of `source`, rounded to binary32; the other frames of the channel are not
modified. -/
def AudioBuffer.copyToChannel (b : AudioBuffer) (source : FloatArray) (channelNumber : Nat)
    (bufferOffset : Nat := 0) : Except Error AudioBuffer :=
  if channelNumber < b.numberOfChannels then
    let cur := b.data.getD channelNumber ⟨#[]⟩
    let cnt := copyCount b.length bufferOffset source.size
    let new := mkChan b.length fun i =>
      if bufferOffset ≤ i ∧ i - bufferOffset < cnt then toF32 (getF source (i - bufferOffset))
      else getF cur i
    .ok { b with data := Array.ofFn (n := b.data.size) fun c =>
            if c.1 = channelNumber then new else b.data[c.1]! }
  else .error .indexSize

/-- Says: `copyFromChannel` signals `IndexSizeError` exactly when the channel number is not below
the channel count, and signals nothing else. Does not say: anything about the data. -/
theorem copyFrom_error_iff (b : AudioBuffer) (dest : FloatArray) (ch k : Nat) :
    (∃ e, b.copyFromChannel dest ch k = .error e) ↔ ¬ ch < b.numberOfChannels := by
  unfold AudioBuffer.copyFromChannel
  split
  · simp_all
  · simp_all

theorem copyFrom_error_is_indexSize (b : AudioBuffer) (dest : FloatArray) (ch k : Nat)
    (e : Error) (h : b.copyFromChannel dest ch k = .error e) : e = .indexSize := by
  unfold AudioBuffer.copyFromChannel at h
  split at h
  · cases h
  · cases h; rfl

/-- Says: `copyToChannel` signals `IndexSizeError` exactly when the channel number is not below
the channel count, and signals nothing else. Does not say: anything about the data. -/
theorem copyTo_error_iff (b : AudioBuffer) (src : FloatArray) (ch k : Nat) :
    (∃ e, b.copyToChannel src ch k = .error e) ↔ ¬ ch < b.numberOfChannels := by
  unfold AudioBuffer.copyToChannel
  split
  · simp_all
  · simp_all

theorem copyTo_error_is_indexSize (b : AudioBuffer) (src : FloatArray) (ch k : Nat)
    (e : Error) (h : b.copyToChannel src ch k = .error e) : e = .indexSize := by
  unfold AudioBuffer.copyToChannel at h
  split at h
  · cases h
  · cases h; rfl

/-- Says: every index that `copyFromChannel` and `copyToChannel` copy lies inside the buffer
(`bufferOffset + j < length`) and inside the array (`j < array length`), for every argument,
including an offset beyond the end of the buffer (then nothing is copied). Does not say: that the
buffer or array is non-empty. -/
theorem copyCount_inside (bufferLength offset arrayLength j : Nat)
    (h : j < copyCount bufferLength offset arrayLength) :
    offset + j < bufferLength ∧ j < arrayLength := by
  unfold copyCount at h
  omega

/-- Says: `copyCount` is `max(0, min(N_b - k, N_f))` of the specification, and is 0 when the
offset is at or beyond the end of the buffer. Does not say: anything about the data. -/
theorem copyCount_zero_beyond (bufferLength offset arrayLength : Nat) (h : bufferLength ≤ offset) :
    copyCount bufferLength offset arrayLength = 0 := by
  unfold copyCount; omega

/-- Says: the result of `copyFromChannel` has the size of the destination (nothing is written
outside it), its first `copyCount` elements are the channel's elements from the offset (all of
them read inside the buffer, and inside the stored channel when the buffer is well formed), and
its other elements are those of the destination. Does not say: the values are binary32 (they are
when the buffer's are). -/
theorem copyFrom_spec (b : AudioBuffer) (hb : b.WF) (dest : FloatArray) (ch k : Nat)
    (r : FloatArray) (h : b.copyFromChannel dest ch k = .ok r) :
    ch < b.numberOfChannels ∧ r.size = dest.size ∧
    ∀ j, j < dest.size →
      (j < copyCount b.length k dest.size →
        k + j < b.length ∧ k + j < (b.data.getD ch ⟨#[]⟩).size ∧
        getF r j = getF (b.data.getD ch ⟨#[]⟩) (k + j)) ∧
      (¬ j < copyCount b.length k dest.size → getF r j = getF dest j) := by
  unfold AudioBuffer.copyFromChannel at h
  split at h
  · rename_i hch
    cases h
    refine ⟨hch, mkChan_size _ _, ?_⟩
    intro j hj
    have hs : ch < b.data.size := by rw [hb.1]; exact hch
    have hsz : (b.data.getD ch ⟨#[]⟩).size = b.length := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
      exact hb.2 _ (Array.getElem_mem hs)
    constructor
    · intro hc
      have := copyCount_inside _ _ _ _ hc
      refine ⟨this.1, by omega, ?_⟩
      rw [getF_mkChan]
      simp [hj, hc]
    · intro hc
      rw [getF_mkChan]
      simp [hj, hc]
  · cases h

/-- Says: the result of `copyToChannel` has the channel count and the length of the buffer, one
channel array for each channel, and `length` frames in each: a well-formed buffer stays well
formed. Does not say: anything about the values. -/
theorem copyTo_shape (b : AudioBuffer) (hb : b.WF) (src : FloatArray) (ch k : Nat)
    (r : AudioBuffer) (h : b.copyToChannel src ch k = .ok r) :
    r.numberOfChannels = b.numberOfChannels ∧ r.length = b.length ∧ r.sampleRate = b.sampleRate ∧
    r.WF := by
  unfold AudioBuffer.copyToChannel at h
  split at h
  · cases h
    refine ⟨rfl, rfl, rfl, ⟨by simpa using hb.1, ?_⟩⟩
    intro c hc
    simp only [Array.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    by_cases hj : j.1 = ch
    · simp only [hj, if_true]
      exact mkChan_size _ _
    · simp only [hj, if_false]
      have hj' : j.1 < b.data.size := j.2
      rw [getElem!_pos b.data j.1 hj']
      exact hb.2 _ (Array.getElem_mem hj')
  · cases h

/-- Says: after `copyToChannel`, frame `i` of the destination channel is the source element
`i - k` rounded to binary32 when `i` is one of the `copyCount` copied frames (so no write is
outside the buffer or the source), and the frame it was before otherwise; the other channels are
unchanged. Does not say: that a `Float32Array` obtained earlier from `getChannelData` sees the
change. -/
theorem copyTo_spec (b : AudioBuffer) (hb : b.WF) (src : FloatArray) (ch k : Nat)
    (r : AudioBuffer) (h : b.copyToChannel src ch k = .ok r) :
    ch < b.numberOfChannels ∧
    (∀ i, i < b.length →
      (k ≤ i ∧ i - k < copyCount b.length k src.size →
        i - k < src.size ∧ getF (r.data.getD ch ⟨#[]⟩) i = toF32 (getF src (i - k))) ∧
      (¬ (k ≤ i ∧ i - k < copyCount b.length k src.size) →
        getF (r.data.getD ch ⟨#[]⟩) i = getF (b.data.getD ch ⟨#[]⟩) i)) ∧
    (∀ c, c ≠ ch → r.data.getD c ⟨#[]⟩ = b.data.getD c ⟨#[]⟩) := by
  unfold AudioBuffer.copyToChannel at h
  split at h
  · rename_i hch
    cases h
    have hs : ch < b.data.size := by rw [hb.1]; exact hch
    refine ⟨hch, ?_, ?_⟩
    · intro i hi
      have hr : ({ b with data := Array.ofFn (n := b.data.size) fun c =>
            if c.1 = ch then mkChan b.length (fun i =>
              if k ≤ i ∧ i - k < copyCount b.length k src.size then toF32 (getF src (i - k))
              else getF (b.data.getD ch ⟨#[]⟩) i)
            else b.data[c.1]! } : AudioBuffer).data.getD ch ⟨#[]⟩ =
          mkChan b.length (fun i =>
              if k ≤ i ∧ i - k < copyCount b.length k src.size then toF32 (getF src (i - k))
              else getF (b.data.getD ch ⟨#[]⟩) i) := by
        simp [Array.getD_eq_getD_getElem?, hs]
      rw [hr, getF_mkChan]
      constructor
      · intro hc
        have := copyCount_inside _ _ _ _ (show i - k < copyCount b.length k src.size from hc.2)
        simp [hi, hc]
        omega
      · intro hc
        simp [hi, hc]
    · intro c hc
      by_cases hcs : c < b.data.size
      · simp [Array.getD_eq_getD_getElem?, hcs, hc]
      · simp [Array.getD_eq_getD_getElem?, hcs]
  · cases h

/-! ## Scheduling and the source node's state -/

/-- Control-thread attributes read on each block (the specification: "updated on a k-rate basis,
prior to each invocation of process()"). -/
structure SourceConfig where
  buffer : Option AudioBuffer := none
  loop : Bool := false
  loopStart : Float := 0.0
  loopEnd : Float := 0.0

/-- State of an `AudioBufferSourceNode` between blocks. Positions in the buffer are in buffer
frames (see the module comment). -/
structure SourceState where
  /-- The context's sample rate. -/
  sampleRate : Float
  /-- `start` was called: the first frame at or after the start time. -/
  startFrame : Option Nat := none
  /-- The start time as given. -/
  startTime : Float := 0.0
  /-- `stop` was called: the first silent frame. -/
  stopFrame : Option Nat := none
  /-- `offset` of `start`, in seconds. -/
  offset : Float := 0.0
  /-- `duration` of `start`, in seconds; infinity when not given. -/
  duration : Float := inf
  /-- Context frame number of the first frame of the next block (`currentFrame`). -/
  frame : Nat := 0
  /-- Pseudocode `offset`, after the clamping done on the first frame played, in buffer frames. -/
  offsetF : Float := 0.0
  /-- Pseudocode `bufferTime`, in buffer frames. -/
  bufferFrame : Float := 0.0
  /-- Pseudocode `bufferTimeElapsed`, in buffer frames. -/
  elapsed : Float := 0.0
  /-- Pseudocode `started`. -/
  started : Bool := false
  /-- Pseudocode `enteredLoop`. -/
  enteredLoop : Bool := false
  /-- Playback has ended: the output has become one channel of silence. -/
  finished : Bool := false

/-- `start(when, offset, duration)`. `InvalidStateError` when `start` was already called;
`TypeError` for a non-finite argument; `RangeError` for a negative argument. -/
def SourceState.start (s : SourceState) (when_ : Float) (offset : Float := 0.0)
    (duration : Option Float := none) : Except Error SourceState :=
  if s.startFrame.isSome then .error .invalidState
  else if !(when_.isFinite && offset.isFinite && (duration.getD 0.0).isFinite) then .error .typeError
  else if when_ < 0.0 || offset < 0.0 || (duration.getD 0.0) < 0.0 then .error .range
  else
    .ok { s with startFrame := some (frameOfTime when_ s.sampleRate), startTime := when_
                 offset := offset, duration := duration.getD inf }

/-- `stop(when)` (`when` absent: the current time, the frame `s.frame`). `InvalidStateError` when
`start` was not called; `TypeError`, `RangeError` as for `start`. -/
def SourceState.stop (s : SourceState) (when_ : Option Float := none) : Except Error SourceState :=
  if s.startFrame.isNone then .error .invalidState
  else match when_ with
    | none => .ok { s with stopFrame := some s.frame }
    | some w =>
      if !w.isFinite then .error .typeError
      else if w < 0.0 then .error .range
      else .ok { s with stopFrame := some (frameOfTime w s.sampleRate) }

/-- The number of output channels of the block that starts in state `s`. -/
def outChannels (cfg : SourceConfig) (s : SourceState) : Nat :=
  match cfg.buffer with
  | none => 1
  | some b => if s.finished && 1 < b.numberOfChannels then 1 else b.numberOfChannels

/-! ## The playback algorithm -/

/-- Take a value within 1e-9 of a whole number to be that number. -/
def snapFrames (x : Float) : Float :=
  let r := x.round
  if (x - r).abs < 1e-9 then r else x

/-- Move `bt` into `[ls, le)` by whole loop lengths: the pseudocode's two `while` loops, by
division. `le - ls` is positive (`loopPoints`). -/
def wrapLoop (bt ls le : Float) : Float :=
  let l := le - ls
  let r :=
    if bt ≥ le then bt - (((bt - le) / l).floor + 1.0) * l
    else if bt < ls then bt + ((ls - bt) / l).ceil * l
    else bt
  if r ≥ le then r - l else if r < ls then r + l else r

/-- Loop points in buffer frames: `(actualLoopStart, actualLoopEnd)` of the pseudocode. A negative
`loopStart` is read as 0 (the text of the `loopStart` attribute: "If loopStart is less than 0,
looping will begin at 0"; WPT `audiobuffersource-playbackrate-negative.html`, "clamped loopStart";
the pseudocode of the specification gives the whole buffer for it). The loop is the whole buffer
when `loopEnd` is not above 0, and when, after `loopEnd` is clamped to the duration, the start is
not before the end. -/
def loopPoints (cfg : SourceConfig) (b : AudioBuffer) : Float × Float :=
  let len := b.length.toFloat
  let ls := if cfg.loopStart < 0.0 then 0.0 else cfg.loopStart
  let r :=
    if cfg.loopEnd > 0.0 && ls < cfg.loopEnd then
      (snapFrames (ls * b.sampleRate),
       min (snapFrames (cfg.loopEnd * b.sampleRate)) len)
    else (0.0, len)
  if r.1 < r.2 then r else (0.0, len)

/-- Constants of one block. -/
structure Ctx where
  loopActive : Bool
  rate : Float
  /-- Buffer frames per context frame: `computedPlaybackRate * bufferRate / contextRate`. -/
  dp : Float
  len : Float
  ls : Float
  le : Float
  lsIdx : Nat
  /-- `duration` of `start` in buffer frames. -/
  durFrames : Float
  /-- `offset` of `start` in buffer frames, clamped to `[0, length]`. -/
  offsetFrames : Float
  startTime : Float

/-- Playhead position on a frame: a context frame at which the source plays, with the buffer
position, and whether the playhead has entered the loop. -/
abbrev Emit := Option (Float × Bool)

/-- One context frame of the pseudocode's render loop: the new state and what is output. -/
def stepFrame (c : Ctx) (cf : Nat) (st : SourceState) : SourceState × Emit :=
  if !(active st.startFrame st.stopFrame cf) || decide (st.elapsed ≥ c.durFrames) then (st, none)
  else
    let st1 :=
      if st.started then st
      else
        let o0 := c.offsetFrames
        let o1 := if c.loopActive && c.rate ≥ 0.0 && o0 ≥ c.le then c.le else o0
        let o2 := if c.rate < 0.0 && c.loopActive && o1 < c.ls then c.ls else o1
        -- sub-sample start: the playhead moves on by the part of a context frame between the
        -- start time and the first frame played
        let sub :=
          match st.startFrame with
          | some sf =>
            if sf = cf then
              let d := cf.toFloat - snapFrames (c.startTime * st.sampleRate)
              if d > 0.0 then d else 0.0
            else 0.0
          | none => 0.0
        -- the part of the `duration` before the first frame played is spent (WPT
        -- sub-sample-scheduling.html, "sub-sample-grain": the grain ends at the exact time)
        { st with offsetF := o2, bufferFrame := o2 + sub * c.dp, elapsed := sub * c.dp, started := true }
    let entered :=
      c.loopActive &&
        (st1.enteredLoop || (st1.offsetF < c.le && st1.bufferFrame ≥ c.ls) ||
          (st1.offsetF ≥ c.le && st1.bufferFrame < c.le))
    let bt := if entered then wrapLoop st1.bufferFrame c.ls c.le else st1.bufferFrame
    let e : Emit := if bt ≥ 0.0 && bt < c.len then some (bt, entered) else none
    ({ st1 with bufferFrame := bt + c.dp, elapsed := st1.elapsed + c.dp, enteredLoop := entered }, e)

/-- Linear interpolation of one channel at buffer position `x` (in frames); between the last frame and
the end of the buffer it extrapolates linearly from the last two frames. `wrap` is
`some (loopStartIndex, loopEnd)` when the playhead is in the loop. -/
def interp (ch : FloatArray) (len : Nat) (x : Float) (wrap : Option (Nat × Float)) : Float :=
  let x := snapFrames x
  let fl := x.floor
  let i := fl.toUInt64.toNat
  let fr := x - fl
  let v0 := getF ch i
  if fr == 0.0 then v0
  else
    let v1 :=
      match wrap with
      | some (w, le) => if (i + 1).toFloat ≥ le then getF ch w else getF ch (i + 1)
      | none =>
        if i + 1 < len then getF ch (i + 1)
        -- Past the last frame the signal is continued along the last two frames (a buffer of one
        -- frame holds its value): WPT buffer-resampling.html, "extrapolation at end of AudioBuffer".
        else if 1 ≤ i then 2.0 * v0 - getF ch (i - 1)
        else v0
    v0 * (1.0 - fr) + v1 * fr

/-- The output value of one channel on one frame. -/
def sampleAt (ch : FloatArray) (len : Nat) (c : Ctx) (e : Emit) : Float :=
  match e with
  | none => 0.0
  | some (x, ent) => interp ch len x (if ent then some (c.lsIdx, c.le) else none)

/-- One step of the loop over the frames of a block. -/
def posStep (c : Ctx) (base : Nat) (i : Nat) (p : SourceState × Array Emit) :
    SourceState × Array Emit :=
  let r := stepFrame c (base + i) p.1
  (r.1, p.2.push r.2)

/-- The constants of the block for `b`. `params[0]` is `playbackRate` and `params[1]` is `detune`
(k-rate: the first value of each array). -/
def mkCtx (cfg : SourceConfig) (b : AudioBuffer) (s : SourceState) (params : Array FloatArray) :
    Ctx :=
  let rate := paramAt (params.getD 0 ⟨#[]⟩) 0 * Float.pow 2.0 (paramAt (params.getD 1 ⟨#[]⟩) 0 / 1200.0)
  let lp := loopPoints cfg b
  let len := b.length.toFloat
  let off := snapFrames (s.offset * b.sampleRate)
  { loopActive := cfg.loop
    rate
    dp := rate * b.sampleRate / s.sampleRate
    len
    ls := lp.1
    le := lp.2
    lsIdx := lp.1.floor.toUInt64.toNat
    durFrames := snapFrames (s.duration * b.sampleRate)
    offsetFrames := if off ≥ 0.0 then (if off ≤ len then off else len) else 0.0
    startTime := s.startTime }

/-- One block of `n` frames. `inputs` is empty (the node has no input); `params` as for `mkCtx`.
Without a buffer the output is one channel of silence. -/
def process (n : Nat) (cfg : SourceConfig) (s : SourceState) (_inputs : Array Block)
    (params : Array FloatArray) : SourceState × Array Block :=
  match cfg.buffer with
  | none => ({ s with frame := s.frame + n, finished := true }, #[silence 1 n])
  | some b =>
    if s.finished then ({ s with frame := s.frame + n }, #[silence (outChannels cfg s) n])
    else
      let c := mkCtx cfg b s params
      let r := iter (posStep c s.frame) n 0 (s, (#[] : Array Emit))
      let st := r.1
      let out : Block := Array.ofFn (n := outChannels cfg s) fun ch =>
        mkChan n fun i => sampleAt (b.data.getD ch.1 ⟨#[]⟩) b.length c (r.2.getD i none)
      let stopReached := match st.stopFrame with
        | some e => decide (e ≤ s.frame + n)
        | none => false
      let durReached := st.started && decide (st.elapsed ≥ c.durFrames)
      let endReached := st.started && !c.loopActive && (st.bufferFrame ≥ c.len || st.bufferFrame < 0.0)
      ({ st with frame := s.frame + n, finished := stopReached || durReached || endReached }, #[out])

/-! ## Theorems about the source kernel -/

/-- Says: the source kernel returns one block, with `outChannels` channels (the buffer's channel
count while playback has not ended; one channel without a buffer, or after the end of playback of
a buffer of more than one channel) and `n` frames in each channel. Does not say: the values. -/
theorem process_shape (n : Nat) (cfg : SourceConfig) (s : SourceState) (inputs : Array Block)
    (params : Array FloatArray) :
    let o := (process n cfg s inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = outChannels cfg s ∧ IsBlock n b) := by
  intro o
  have key : ∀ (k : Nat) (f : Fin k → FloatArray) (hf : ∀ i, (f i).size = n),
      (Array.ofFn (n := k) f).size = k ∧ IsBlock n (Array.ofFn (n := k) f) := by
    intro k f hf
    refine ⟨by simp, ?_⟩
    intro c hc
    simp only [Array.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact hf j
  simp only [o, process]
  split
  · rename_i hn
    simp only [outChannels, hn]
    refine ⟨by simp, ?_⟩
    intro b hb
    simp only [Array.mem_singleton] at hb
    subst hb
    exact ⟨(silence_shape 1 n).1, (silence_shape 1 n).2⟩
  · rename_i bf hb
    split
    · refine ⟨by simp, ?_⟩
      intro b hb'
      simp only [Array.mem_singleton] at hb'
      subst hb'
      exact ⟨(silence_shape _ n).1, (silence_shape _ n).2⟩
    · refine ⟨by simp, ?_⟩
      intro b hb'
      simp only [Array.mem_singleton] at hb'
      subst hb'
      exact key _ _ (fun i => mkChan_size _ _) |> fun h => ⟨h.1, h.2⟩

/-- Says: the frame counter advances by `n`. Does not say: anything about the playback state. -/
theorem process_frame (n : Nat) (cfg : SourceConfig) (s : SourceState) (inputs : Array Block)
    (params : Array FloatArray) : (process n cfg s inputs params).1.frame = s.frame + n := by
  unfold process
  split
  · rfl
  · split
    · rfl
    · rfl

/-- Says: while playback has not ended (`finished` is false) the output of a source with a buffer
has the buffer's channel count. Does not say: when playback ends. -/
theorem process_channels_buffer (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (b : AudioBuffer)
    (hb : cfg.buffer = some b) (hf : s.finished = false) :
    ∀ o ∈ (process n cfg s inputs params).2, o.size = b.numberOfChannels := by
  intro o ho
  have := (process_shape n cfg s inputs params).2 o ho
  rw [this.1]
  simp [outChannels, hb, hf]

/-- Says: a source with no buffer outputs one channel. Does not say: anything about the values. -/
theorem process_channels_no_buffer (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (hb : cfg.buffer = none) :
    ∀ o ∈ (process n cfg s inputs params).2, o.size = 1 := by
  intro o ho
  have := (process_shape n cfg s inputs params).2 o ho
  rw [this.1]
  simp [outChannels, hb]

/-- Says: after playback of a buffer of more than one channel has ended, the output is one
channel. Does not say: when it ends. -/
theorem process_channels_ended (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (b : AudioBuffer)
    (hb : cfg.buffer = some b) (hf : s.finished = true) (hm : 1 < b.numberOfChannels) :
    ∀ o ∈ (process n cfg s inputs params).2, o.size = 1 := by
  intro o ho
  have := (process_shape n cfg s inputs params).2 o ho
  rw [this.1]
  simp [outChannels, hb, hf, hm]

/-- A frame is inactive when it is before the start frame or at or after the stop frame, or
`start` was never called. -/
theorem not_active_after_stop (st : Option Nat) (e f : Nat) (h : e ≤ f) :
    active st (some e) f = false := by
  cases st with
  | none => simp [active]
  | some s => simp [active, Nat.not_lt.mpr h]

theorem stepFrame_start (c : Ctx) (cf : Nat) (st : SourceState) :
    (stepFrame c cf st).1.startFrame = st.startFrame ∧
    (stepFrame c cf st).1.stopFrame = st.stopFrame := by
  unfold stepFrame
  split
  · exact ⟨rfl, rfl⟩
  · simp only
    split <;> simp

theorem iter_posStep_start (c : Ctx) (base : Nat) :
    ∀ (k i : Nat) (p : SourceState × Array Emit),
    (iter (posStep c base) k i p).1.startFrame = p.1.startFrame ∧
    (iter (posStep c base) k i p).1.stopFrame = p.1.stopFrame := by
  intro k
  induction k with
  | zero => intro i p; simp [iter]
  | succ k ih =>
    intro i p
    simp only [iter]
    have h := ih (i + 1) (posStep c base i p)
    have h2 := stepFrame_start c (base + i) p.1
    exact ⟨h.1.trans h2.1, h.2.trans h2.2⟩

theorem iter_posStep_size (c : Ctx) (base : Nat) :
    ∀ (k i : Nat) (p : SourceState × Array Emit),
    (iter (posStep c base) k i p).2.size = p.2.size + k := by
  intro k
  induction k with
  | zero => intro i p; simp [iter]
  | succ k ih =>
    intro i p
    simp only [iter]
    rw [ih (i + 1) (posStep c base i p)]
    simp [posStep]
    omega

theorem iter_posStep_prefix (c : Ctx) (base : Nat) :
    ∀ (k i : Nat) (p : SourceState × Array Emit) (j : Nat), j < p.2.size →
    (iter (posStep c base) k i p).2.getD j none = p.2.getD j none := by
  intro k
  induction k with
  | zero => intro i p j _; simp [iter]
  | succ k ih =>
    intro i p j hj
    simp only [iter]
    have hj' : j < (posStep c base i p).2.size := by simp [posStep]; omega
    rw [ih (i + 1) (posStep c base i p) j hj']
    simp only [posStep]
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_push_lt hj]
    simp [Array.getElem?_eq_getElem hj]

theorem iter_posStep_none (c : Ctx) (base : Nat) :
    ∀ (k i : Nat) (p : SourceState × Array Emit), p.2.size = i →
    ∀ j, i ≤ j → j < i + k → active p.1.startFrame p.1.stopFrame (base + j) = false →
    (iter (posStep c base) k i p).2.getD j none = none := by
  intro k
  induction k with
  | zero => intro i p _ j h1 h2; omega
  | succ k ih =>
    intro i p hs j h1 h2 hact
    simp only [iter]
    have hsz : (posStep c base i p).2.size = i + 1 := by simp [posStep, hs]
    by_cases hji : j = i
    · subst hji
      have hpre := iter_posStep_prefix c base k (j + 1) (posStep c base j p) j (by omega)
      rw [hpre]
      subst hs
      simp only [posStep]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
      simp only [Option.getD_some]
      unfold stepFrame
      simp [hact]
    · have hst := stepFrame_start c (base + i) p.1
      apply ih (i + 1) (posStep c base i p) hsz j (by omega) (by omega)
      simp only [posStep]
      rw [hst.1, hst.2]
      exact hact

/-- Says: on every frame at which the source is not active (before the start frame, at or after
the stop frame, or `start` never called), every channel of the output is 0, in every block, for
every state and parameter values. Does not say: that the source is silent in between (that
depends on the buffer), nor that a stop frame before the start frame has any other effect. -/
theorem process_silent_inactive (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (i : Nat) (hi : i < n)
    (hact : active s.startFrame s.stopFrame (s.frame + i) = false) :
    ∀ o ∈ (process n cfg s inputs params).2, ∀ ch, getF (o.getD ch ⟨#[]⟩) i = 0.0 := by
  intro o ho ch
  have silent : ∀ (k : Nat), o ∈ #[silence k n] → getF (o.getD ch ⟨#[]⟩) i = 0.0 := by
    intro k hk
    simp only [Array.mem_singleton] at hk
    subst hk
    simp only [silence]
    by_cases hc : ch < k
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      simp [hc, getF_mkChan]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      simp [hc, getF, FloatArray.size]
  unfold process at ho
  split at ho
  · exact silent _ ho
  · rename_i b hb
    split at ho
    · exact silent _ ho
    · simp only [Array.mem_singleton] at ho
      subst ho
      by_cases hc : ch < outChannels cfg s
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
        simp only [hc, dite_true, Option.getD_some]
        rw [getF_mkChan]
        simp only [hi, if_true]
        have hn := iter_posStep_none (mkCtx cfg b s params) s.frame n 0 (s, (#[] : Array Emit))
          rfl i (Nat.zero_le _) (by omega) hact
        simp only [sampleAt]
        simp only [hn]
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
        simp [hc, getF, FloatArray.size]

/-- Says: the output is silent at every frame before the start frame. Does not say: where the
start frame is (`frameOfTime`). -/
theorem process_silent_before_start (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (sf : Nat) (hs : s.startFrame = some sf)
    (i : Nat) (hi : i < n) (hb : s.frame + i < sf) :
    ∀ o ∈ (process n cfg s inputs params).2, ∀ ch, getF (o.getD ch ⟨#[]⟩) i = 0.0 := by
  apply process_silent_inactive n cfg s inputs params i hi
  rw [hs]
  exact active_before_start sf s.stopFrame _ hb

/-- Says: the output is silent at every frame at or after the stop frame. Does not say: what a
stop before the start means. -/
theorem process_silent_after_stop (n : Nat) (cfg : SourceConfig) (s : SourceState)
    (inputs : Array Block) (params : Array FloatArray) (e : Nat) (hs : s.stopFrame = some e)
    (i : Nat) (hi : i < n) (hb : e ≤ s.frame + i) :
    ∀ o ∈ (process n cfg s inputs params).2, ∀ ch, getF (o.getD ch ⟨#[]⟩) i = 0.0 := by
  apply process_silent_inactive n cfg s inputs params i hi
  rw [hs]
  exact not_active_after_stop _ _ _ hb

/-! ## Tests

Cases are from the Web Platform Tests directory `webaudio/the-audio-api/` (file named at each
group) and from the specification text. A frame count or time in these tests uses a sample rate of
8000 Hz so that a time `k / 8000` converts back to the frame `k` (`snapFrames` absorbs the
rounding). -/

section Tests

private def chn (xs : List Float) : FloatArray := ⟨xs.toArray⟩
private def toL (a : FloatArray) : List Float := a.data.toList
private def approx (a b : Float) : Bool := (a - b).abs < 1e-6
private def approxL (a : List Float) (b : List Float) : Bool :=
  a.length == b.length && (List.zip a b).all fun p => approx p.1 p.2
private def isErr {α : Type} (e : Except Error α) (x : Error) : Bool :=
  match e with | .error y => y == x | .ok _ => false
private def isOk {α : Type} (e : Except Error α) : Bool :=
  match e with | .ok _ => true | .error _ => false
private def bufOf (rate : Float) (chans : List (List Float)) : AudioBuffer :=
  { numberOfChannels := chans.length, length := (chans.headD []).length, sampleRate := rate
    data := (chans.map chn).toArray }
private def rampL (n : Nat) (c : Float) : List Float := (List.range n).map fun k => k.toFloat + c
private def sd (b : Except Error AudioBuffer) (ch : Nat) : List Float :=
  match b with | .ok b => toL (b.data.getD ch ⟨#[]⟩) | .error _ => []
private def cfgOf (b : AudioBuffer) (loop : Bool := false) (ls le : Float := 0.0) : SourceConfig :=
  { buffer := some b, loop, loopStart := ls, loopEnd := le }
private def started (sr : Float) (w : Float := 0.0) (o : Float := 0.0) (d : Option Float := none) :
    SourceState :=
  match SourceState.start { sampleRate := sr } w o d with
  | .ok s => s
  | .error _ => { sampleRate := sr }
private def blk (cfg : SourceConfig) (s : SourceState) (n : Nat) (rate : Float := 1.0)
    (detune : Float := 0.0) : SourceState × Block :=
  let r := process n cfg s #[] #[⟨#[rate]⟩, ⟨#[detune]⟩]
  (r.1, r.2.getD 0 #[])
private def play (cfg : SourceConfig) (s : SourceState) (n : Nat) (rate : Float := 1.0)
    (detune : Float := 0.0) : List Float :=
  toL ((blk cfg s n rate detune).2.getD 0 ⟨#[]⟩)

-- ctor-audiobuffer.html
#guard isErr (AudioBuffer.create 0 1 16000.0) .notSupported
#guard isErr (AudioBuffer.create 99 0 16000.0) .notSupported
#guard isErr (AudioBuffer.create 1 0 16000.0) .notSupported
#guard isErr (AudioBuffer.create 1 1 100.0) .notSupported
#guard (match AudioBuffer.create 3 1 48000.0 with
  | .ok b => b.numberOfChannels == 3 && b.length == 1 && b.sampleRate == 48000.0 | .error _ => false)
#guard (match AudioBuffer.create 5 17 16000.0 with
  | .ok b => b.numberOfChannels == 5 && b.length == 17 && b.sampleRate == 16000.0
      && b.data.size == 5 && b.data.all (fun c => c.size == 17 && (toL c).all (· == 0.0))
  | .error _ => false)
#guard (match AudioBuffer.create 3 42 54321.0 with
  | .ok b => b.sampleRate == 54321.0 | .error _ => false)
-- bounds: 32 channels, 3000 and 768000 Hz, NaN
#guard isOk (AudioBuffer.create 32 1 44100.0) && isErr (AudioBuffer.create 33 1 44100.0) .notSupported
#guard isOk (AudioBuffer.create 1 1 3000.0) && isOk (AudioBuffer.create 1 1 768000.0)
#guard isErr (AudioBuffer.create 1 1 2999.0) .notSupported
#guard isErr (AudioBuffer.create 1 1 768001.0) .notSupported
#guard isErr (AudioBuffer.create 1 1 (0.0 / 0.0)) .notSupported
-- the sample rate is a binary32 value (IDL type float) and duration is length / sampleRate
#guard (match AudioBuffer.create 1 4410 44100.1 with
  | .ok b => b.sampleRate == toF32 44100.1 && b.sampleRate != 44100.1
      && approx b.duration (4410.0 / toF32 44100.1)
  | .error _ => false)
#guard (match AudioBuffer.create 1 44100 44100.0 with
  | .ok b => b.duration == 1.0 | .error _ => false)

-- audiobuffer-getChannelData.html: the index rule, and the channel has `length` frames
#guard (match AudioBuffer.create 3 42 54321.0 with
  | .ok b => (match b.getChannelData 2 with | .ok a => a.size == 42 | .error _ => false)
      && isErr (b.getChannelData 3) .indexSize
  | .error _ => false)

-- audiobuffer-copy-channel.html: 3 channels, 16 frames, channel c holds k + c + 1
private def copyBuf : AudioBuffer := bufOf 44100.0 [rampL 16 1.0, rampL 16 2.0, rampL 16 3.0]
private def x8 : FloatArray := chn (List.replicate 8 (-1.0))
#guard (match copyBuf.copyFromChannel x8 0 with | .ok r => toL r == rampL 8 1.0 | .error _ => false)
#guard (match copyBuf.copyFromChannel x8 2 with | .ok r => toL r == rampL 8 3.0 | .error _ => false)
#guard isErr (copyBuf.copyFromChannel x8 3) .indexSize
-- offset at the end of the buffer (case 6): nothing copied, no error
#guard (match copyBuf.copyFromChannel x8 0 16 with
  | .ok r => toL r == List.replicate 8 (-1.0) | .error _ => false)
-- offset 10: 6 frames copied, the last two elements keep their value
#guard (match copyBuf.copyFromChannel x8 0 10 with
  | .ok r => toL r == [11.0, 12.0, 13.0, 14.0, 15.0, 16.0, -1.0, -1.0] | .error _ => false)
-- destination longer than the buffer
#guard (match copyBuf.copyFromChannel (chn (List.replicate 20 (-1.0))) 1 0 with
  | .ok r => toL r == rampL 16 2.0 ++ [-1.0, -1.0, -1.0, -1.0] | .error _ => false)
-- copyTo
private def src4 : FloatArray := chn [101.0, 102.0, 103.0, 104.0]
#guard isErr (copyBuf.copyToChannel src4 3) .indexSize
#guard sd (copyBuf.copyToChannel src4 1) 1 == [101.0, 102.0, 103.0, 104.0] ++ rampL 12 6.0
#guard sd (copyBuf.copyToChannel src4 1 6) 1
  == rampL 6 2.0 ++ [101.0, 102.0, 103.0, 104.0] ++ rampL 6 12.0
-- source runs past the end of the buffer: only the frames inside are written
#guard sd (copyBuf.copyToChannel src4 1 14) 1 == rampL 14 2.0 ++ [101.0, 102.0]
#guard sd (copyBuf.copyToChannel src4 1 16) 1 == rampL 16 2.0
#guard sd (copyBuf.copyToChannel src4 1 1000000) 1 == rampL 16 2.0
-- the other channels, the channel count and the length are kept
#guard (match copyBuf.copyToChannel src4 1 with
  | .ok r => r.numberOfChannels == 3 && r.length == 16 && r.data.size == 3
      && toL (r.data[0]!) == rampL 16 1.0 && toL (r.data[2]!) == rampL 16 3.0
      && r.data.all (·.size == 16)
  | .error _ => false)
-- binary32 rounding on write
#guard (sd (copyBuf.copyToChannel (chn [0.1]) 0) 0).head! == toF32 0.1
#guard (sd (copyBuf.copyToChannel (chn [0.1]) 0) 0).head! != 0.1
#guard toF32 16777217.0 == 16777216.0
#guard toF32 1e40 == inf
#guard toF32 0.1 == 0.10000000149011612
#guard (match AudioBuffer.create 1 2 44100.0 with
  | .ok b =>
      let b' := b.writeSample 0 1 0.1
      toL (b'.data[0]!) == [0.0, 0.10000000149011612]
        && toL ((b'.writeSample 0 2 5.0).data[0]!) == [0.0, 0.10000000149011612]
        && toL ((b'.writeSample 1 0 5.0).data[0]!) == [0.0, 0.10000000149011612]
  | .error _ => false)

-- the source: ramp 1 .. 8, context and buffer at 8000 Hz
private def ramp8 : AudioBuffer := bufOf 8000.0 [rampL 8 1.0]
private def s0 : SourceState := started 8000.0

-- rate 1, 0.5, 2, 0 and a negative rate
#guard approxL (play (cfgOf ramp8) s0 10) (rampL 8 1.0 ++ [0.0, 0.0])
#guard approxL (play (cfgOf ramp8) s0 8 0.5) [1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5]
#guard approxL (play (cfgOf ramp8) s0 6 2.0) [1.0, 3.0, 5.0, 7.0, 0.0, 0.0]
#guard approxL (play (cfgOf ramp8) s0 5 0.0) (List.replicate 5 1.0)
#guard approxL (play (cfgOf ramp8) (started 8000.0 0.0 (3.0 / 8000.0)) 5 (-1.0))
  [4.0, 3.0, 2.0, 1.0, 0.0]
-- detune: rate 1 with +1200 cents is rate 2; -1200 cents is rate 0.5; the product with playbackRate
#guard approxL (play (cfgOf ramp8) s0 4 1.0 1200.0) [1.0, 3.0, 5.0, 7.0]
#guard approxL (play (cfgOf ramp8) s0 4 1.0 (-1200.0)) [1.0, 1.5, 2.0, 2.5]
#guard approxL (play (cfgOf ramp8) s0 4 2.0 (-1200.0)) [1.0, 2.0, 3.0, 4.0]

-- audiobuffersource-playbackrate-zero.html, first case: rate 1 then 0 (k-rate, per block):
-- the output holds the sample at the playhead
#guard (let r1 := blk (cfgOf ramp8) s0 4 1.0
        let r2 := blk (cfgOf ramp8) r1.1 4 0.0
        toL (r1.2.getD 0 ⟨#[]⟩) == [1.0, 2.0, 3.0, 4.0]
          && toL (r2.2.getD 0 ⟨#[]⟩) == List.replicate 4 5.0)
-- the same render in one block and in blocks of 128, 128 and 44 (state continuity)
#guard (let cfg := cfgOf (bufOf 8000.0 [rampL 300 1.0]) true
        let one := play cfg s0 300 1.5
        let r1 := blk cfg s0 128 1.5
        let r2 := blk cfg r1.1 128 1.5
        let r3 := blk cfg r2.1 44 1.5
        approxL one (toL (r1.2[0]!) ++ toL (r2.2[0]!) ++ toL (r3.2[0]!)))

-- loops. audiobuffersource-loop-points.html: loop points inside, outside, reversed
-- the whole buffer
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0, 3.0, 4.0]]) true) s0 10)
  [1.0, 2.0, 3.0, 4.0, 1.0, 2.0, 3.0, 4.0, 1.0, 2.0]
-- loop points inside the buffer: [2, 4) frames
#guard approxL (play (cfgOf ramp8 true (2.0 / 8000.0) (4.0 / 8000.0)) s0 8)
  [1.0, 2.0, 3.0, 4.0, 3.0, 4.0, 3.0, 4.0]
-- loopEnd after the end of the buffer: the end of the buffer
#guard approxL (play (cfgOf ramp8 true (4.0 / 8000.0) 100.0) s0 12)
  [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 5.0, 6.0, 7.0, 8.0]
-- loopStart after the duration (reversed loop), loopEnd <= 0: the whole buffer; loopStart < 0 is 0
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0]]) true 1.0 2.0) s0 5)
  [1.0, 2.0, 1.0, 2.0, 1.0]
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0]]) true (1.0 / 8000.0) 0.0) s0 5)
  [1.0, 2.0, 1.0, 2.0, 1.0]
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0]]) true (-1.0) (2.0 / 8000.0)) s0 5)
  [1.0, 2.0, 1.0, 2.0, 1.0]
-- loopStart < 0 is read as 0 (WPT audiobuffersource-playbackrate-negative.html): rate -1, offset 3,
-- loop [0, 2): 4 3 2 1 then 2 1 2 1
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0, 3.0, 4.0]]) true (-1.0 / 8000.0) (2.0 / 8000.0))
    (started 8000.0 0.0 (3.0 / 8000.0)) 8 (-1.0))
  [4.0, 3.0, 2.0, 1.0, 2.0, 1.0, 2.0, 1.0]
-- no loop attribute: the loop points are ignored
#guard approxL (play (cfgOf ramp8 false (2.0 / 8000.0) (4.0 / 8000.0)) s0 10)
  (rampL 8 1.0 ++ [0.0, 0.0])
-- audiobuffersource-one-sample-loop.html: one frame, looped, 1000 frames of 1
#guard (play (cfgOf (bufOf 44100.0 [[1.0]]) true) (started 44100.0) 1000).all (· == 1.0)
-- half speed over the loop end: the last frame is interpolated with the loop start (specification
-- figure "playbackRate interpolation")
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0, 3.0, 4.0]]) true) s0 8 0.5)
  [1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 2.5]
-- a loop entered from inside: offset 3, loop [2, 4)
#guard approxL (play (cfgOf ramp8 true (2.0 / 8000.0) (4.0 / 8000.0))
    (started 8000.0 0.0 (3.0 / 8000.0)) 4)
  [4.0, 3.0, 4.0, 3.0]
-- a negative rate over a loop wraps from the start to the end
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0, 3.0, 4.0]]) true) s0 6 (-1.0))
  [1.0, 4.0, 3.0, 2.0, 1.0, 4.0]
-- offset after the loop end, positive rate: playback begins at the loop end, which is the buffer
-- end for the whole-buffer loop, so nothing plays
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0, 3.0, 4.0]]) true)
    (started 8000.0 0.0 (6.0 / 8000.0)) 3) [0.0, 0.0, 0.0]

-- start(when, offset, duration)
#guard approxL (play (cfgOf ramp8) (started 8000.0 0.0 (2.0 / 8000.0)) 4) [3.0, 4.0, 5.0, 6.0]
#guard approxL (play (cfgOf ramp8) (started 8000.0 0.0 100.0) 3) [0.0, 0.0, 0.0]
#guard approxL (play (cfgOf ramp8) (started 8000.0 (5.0 / 8000.0)) 8)
  [0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0]
#guard approxL (play (cfgOf ramp8) (started 8000.0 0.0 0.0 (some (3.0 / 8000.0))) 6)
  [1.0, 2.0, 3.0, 0.0, 0.0, 0.0]
-- duration counts buffer content, so at half speed it spans twice the frames
#guard approxL (play (cfgOf ramp8) (started 8000.0 0.0 0.0 (some (2.0 / 8000.0))) 6 0.5)
  [1.0, 1.5, 2.0, 2.5, 0.0, 0.0]
-- a loop ends at the duration
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 2.0]]) true)
    (started 8000.0 0.0 0.0 (some (5.0 / 8000.0))) 8)
  [1.0, 2.0, 1.0, 2.0, 1.0, 0.0, 0.0, 0.0]
-- stop
#guard (match (started 8000.0).stop (some (3.0 / 8000.0)) with
  | .ok s => approxL (play (cfgOf ramp8) s 6) [1.0, 2.0, 3.0, 0.0, 0.0, 0.0] | .error _ => false)
-- errors of start and stop
#guard (match (started 8000.0).start 0.0 with | .error e => e == .invalidState | .ok _ => false)
#guard (match SourceState.start { sampleRate := 8000.0 } (-1.0) with
  | .error e => e == .range | .ok _ => false)
#guard (match SourceState.start { sampleRate := 8000.0 } 0.0 (-1.0) with
  | .error e => e == .range | .ok _ => false)
#guard (match SourceState.start { sampleRate := 8000.0 } 0.0 0.0 (some (-1.0)) with
  | .error e => e == .range | .ok _ => false)
#guard (match SourceState.start { sampleRate := 8000.0 } (0.0 / 0.0) with
  | .error e => e == .typeError | .ok _ => false)
#guard (match SourceState.stop { sampleRate := 8000.0 } (some 1.0) with
  | .error e => e == .invalidState | .ok _ => false)
#guard (match (started 8000.0).stop (some (-1.0)) with
  | .error e => e == .range | .ok _ => false)

-- audiobuffersource-playbackrate-zero.html, second case: a sub-sample start time with rate 0
-- holds the first value from the first whole frame at or after the start time (frame 28 of 27.3)
#guard (let b := bufOf 8192.0 [rampL 64 5.0]
        let o := play (cfgOf b) (started 8192.0 (27.3 / 8192.0)) 40 0.0
        o.take 28 == List.replicate 28 0.0 && (o.drop 28).all (· == 5.0))
-- a grain that starts at frame 1.5 and lasts 3 frames ends at frame 4.5: frames 2, 3 and 4 play
#guard approxL (play (cfgOf (bufOf 8000.0 [[1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]]))
    (started 8000.0 (1.5 / 8000.0) 0.0 (some (3.0 / 8000.0))) 8)
  [0.0, 0.0, 1.0, 1.0, 1.0, 0.0, 0.0, 0.0]
-- sub-sample start with rate 1: the playhead is half a frame on at the first frame played
#guard approxL (play (cfgOf ramp8) (started 8000.0 (0.5 / 8000.0)) 4) [0.0, 1.5, 2.5, 3.5]
#guard approxL (play (cfgOf ramp8) (started 8000.0 (3.25 / 8000.0)) 6)
  [0.0, 0.0, 0.0, 0.0, 1.75, 2.75]

-- buffer-resampling.html idea: a buffer at 22050 Hz in a 44100 Hz context plays at half speed,
-- every other output frame interpolated; the frame between the last and the end is continued along
-- the last two frames (3.5, not the 1.5 of a zero after the end), then silence (no loop)
#guard approxL (play (cfgOf (bufOf 22050.0 [[0.0, 1.0, 2.0, 3.0]])) (started 44100.0) 9)
  [0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 0.0]
-- the same buffer at 44100 Hz in a 22050 Hz context plays at double speed
#guard approxL (play (cfgOf (bufOf 44100.0 [[0.0, 1.0, 2.0, 3.0, 4.0, 5.0]])) (started 22050.0) 4)
  [0.0, 2.0, 4.0, 0.0]
-- sample rate and playback rate multiply
#guard approxL (play (cfgOf (bufOf 22050.0 [[0.0, 1.0, 2.0, 3.0]])) (started 44100.0) 4 2.0)
  [0.0, 1.0, 2.0, 3.0]

-- output channels
private def st2 : AudioBuffer := bufOf 8000.0 [[1.0, 2.0, 3.0], [-1.0, -2.0, -3.0]]
#guard ((blk (cfgOf st2) s0 4).2.size == 2)
#guard (let o := (blk (cfgOf st2) s0 4).2
        toL (o[0]!) == [1.0, 2.0, 3.0, 0.0] && toL (o[1]!) == [-1.0, -2.0, -3.0, 0.0])
#guard ((blk {} s0 4).2.size == 1 && (toL ((blk {} s0 4).2[0]!)).all (· == 0.0))
-- two channels: one silent channel after the end of the buffer; a mono buffer keeps one
#guard (let r1 := blk (cfgOf st2) s0 4
        r1.1.finished && (blk (cfgOf st2) r1.1 4).2.size == 1
          && (toL ((blk (cfgOf st2) r1.1 4).2[0]!)).all (· == 0.0))
#guard (let r1 := blk (cfgOf ramp8) s0 10
        r1.1.finished && (blk (cfgOf ramp8) r1.1 4).2.size == 1)
-- a looping stereo buffer does not end; a source that was never started is silent
#guard (let r1 := blk (cfgOf st2 true) s0 10
        !r1.1.finished && r1.2.size == 2)
#guard (play (cfgOf ramp8) { sampleRate := 8000.0 } 10).all (· == 0.0)

end Tests

end L4Factoidal.WebAudio.Buffer
