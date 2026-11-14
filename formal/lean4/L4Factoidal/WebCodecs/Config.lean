/-
L4Factoidal.WebCodecs.Config: is a codec configuration valid, and does this engine support it
(WebCodecs §7: "valid AudioDecoderConfig", "valid VideoDecoderConfig", "valid AudioEncoderConfig",
"valid VideoEncoderConfig", and "Check Configuration Support"). Record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 5.

An invalid configuration is a TypeError of `configure` and `isConfigSupported`. A valid one that is
not supported makes `isConfigSupported` answer `supported: false` and `configure` close the codec
with a NotSupportedError. This engine has no encoder and no decoder, so no configuration is
supported (`check_not_supported`): the page is told so, and nothing is handed to a host codec.
-/
namespace L4Factoidal.WebCodecs.Config

inductive Kind where
  | audioDecoder | videoDecoder | audioEncoder | videoEncoder
  deriving DecidableEq, Repr, Inhabited

def Kind.ofName? : String → Option Kind
  | "AudioDecoder" => some .audioDecoder
  | "VideoDecoder" => some .videoDecoder
  | "AudioEncoder" => some .audioEncoder
  | "VideoEncoder" => some .videoEncoder
  | _ => none

inductive Verdict where
  | invalid | unsupported | supported
  deriving DecidableEq, Repr, Inhabited

def Verdict.name : Verdict → String
  | .invalid => "invalid" | .unsupported => "unsupported" | .supported => "supported"

/-- ASCII whitespace (Infra §4.6). -/
def isAsciiWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

/-- The codec string is empty after its leading and trailing ASCII whitespace is stripped. -/
def blank (codec : String) : Bool := codec.toList.all isAsciiWhitespace

/-- The members of a configuration that validity reads: the codec string, the numeric members the
page gave (by IDL name; a member of a codec's own dictionary as `opus.complexity`), and whether a
`description` it gave is detached. -/
structure Fields where
  codec : String
  nums : List (String × Nat) := []
  detached : Bool := false
  deriving Repr, Inhabited

def Fields.get? (f : Fields) (k : String) : Option Nat := (f.nums.find? (·.1 == k)).map (·.2)

/-- A member that is given is not zero. -/
def Fields.nonzero (f : Fields) (k : String) : Bool := f.get? k != some 0

/-- Both members given, or neither. -/
def Fields.together (f : Fields) (a b : String) : Bool := (f.get? a).isSome == (f.get? b).isSome

/-- The frame durations of Opus, in microseconds (RFC 6716 §2.1.4: 2.5 to 60 ms, and the packed
80, 100 and 120 ms). -/
def opusFrameDurations : List Nat := [2500, 5000, 10000, 20000, 40000, 60000, 80000, 100000, 120000]

/-- The bit rates an Opus encoder takes, in bits a second (RFC 6716 §2.1.1). -/
def opusBitrateOk (b : Nat) : Bool := 500 ≤ b && b ≤ 512000 * 255

/-- The largest bit rate of any encoder configuration here (a signed 32-bit number). -/
def maxBitrate : Nat := 2147483647

def valid (k : Kind) (f : Fields) : Bool :=
  !blank f.codec && !f.detached &&
  match k with
  | .audioDecoder => f.nonzero "sampleRate" && f.nonzero "numberOfChannels"
  | .videoDecoder =>
    f.together "codedWidth" "codedHeight" && f.nonzero "codedWidth" && f.nonzero "codedHeight" &&
    f.together "displayAspectWidth" "displayAspectHeight" && f.nonzero "displayAspectWidth" &&
    f.nonzero "displayAspectHeight"
  | .audioEncoder =>
    f.nonzero "sampleRate" && f.nonzero "numberOfChannels" && f.nonzero "bitrate" &&
    (match f.get? "bitrate" with | some b => decide (b ≤ maxBitrate) | none => true) &&
    (f.codec != "opus" ||
      ((match f.get? "bitrate" with | some b => opusBitrateOk b | none => true) &&
       (match f.get? "opus.complexity" with | some c => decide (c ≤ 10) | none => true) &&
       (match f.get? "opus.packetlossperc" with | some p => decide (p ≤ 100) | none => true) &&
       (match f.get? "opus.frameDuration" with | some d => opusFrameDurations.contains d | none => true)))
  | .videoEncoder =>
    f.get? "width" != some 0 && f.get? "height" != some 0 && (f.get? "width").isSome && (f.get? "height").isSome &&
    f.nonzero "displayWidth" && f.nonzero "displayHeight" && f.nonzero "bitrate"

/-- "Check Configuration Support" for a valid configuration. No codec is implemented. -/
def supported (_k : Kind) (_f : Fields) : Bool := false

def check (k : Kind) (f : Fields) : Verdict :=
  if !valid k f then .invalid else if supported k f then .supported else .unsupported

/-! ## Theorems -/

/-- Refusal. Says: a configuration whose codec string is empty or only ASCII whitespace is invalid
for every kind of codec, whatever its other members. -/
theorem check_blank (k : Kind) (f : Fields) (h : blank f.codec = true) : check k f = .invalid := by
  unfold check valid
  simp [h]

/-- Refusal. Says: a configuration with a detached `description` is invalid for every kind. -/
theorem check_detached (k : Kind) (f : Fields) (h : f.detached = true) : check k f = .invalid := by
  unfold check valid
  simp [h]

/-- Policy. Says: no configuration is answered as supported, so no page input is handed to an
encoder or a decoder. This engine has none; the statement must be replaced by a narrower one in
the commit that adds a codec. Does not say: that an unsupported codec string is well formed. -/
theorem check_not_supported (k : Kind) (f : Fields) : check k f ≠ .supported := by
  unfold check supported
  split
  · simp
  · simp

/-! ## Tests (`webcodecs/*-config.https.any.js`, `audio-decoder`, `video-decoder`) -/

private def c (k : Kind) (codec : String) (nums : List (String × Nat) := []) (detached := false) : String :=
  (check k { codec, nums, detached }).name

#guard c .videoDecoder "" == "invalid"
#guard c .videoDecoder "vp8" [] true == "invalid"
#guard c .videoDecoder "bogus" == "unsupported"
#guard c .videoDecoder "  vp09.00.10.08  " == "unsupported"
#guard c .videoDecoder "avc1.42001E" == "unsupported"
#guard c .videoDecoder "vp8" [("codedWidth", 4)] == "invalid"
#guard c .audioDecoder "opus" [("sampleRate", 0), ("numberOfChannels", 2)] == "invalid"
#guard c .audioDecoder "opus" [("sampleRate", 48000), ("numberOfChannels", 0)] == "invalid"
#guard c .audioDecoder "vorbis" [("sampleRate", 48000), ("numberOfChannels", 2)] == "unsupported"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("bitrate", 6000000000)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("bitrate", 0)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 48000), ("numberOfChannels", 2), ("bitrate", 1)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("opus.complexity", 11)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("opus.packetlossperc", 101)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("opus.frameDuration", 0)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("opus.frameDuration", 120001)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 8000), ("numberOfChannels", 2), ("opus.frameDuration", 2501)] == "invalid"
#guard c .audioEncoder "opus" [("sampleRate", 1), ("numberOfChannels", 2)] == "unsupported"
#guard c .audioEncoder " opus " [("sampleRate", 48000), ("numberOfChannels", 2)] == "unsupported"
#guard c .videoEncoder "vp8" [("width", 0), ("height", 480)] == "invalid"
#guard c .videoEncoder "vp8" [("width", 640), ("height", 480), ("displayWidth", 0)] == "invalid"
#guard c .videoEncoder "vp8" [("width", 640), ("height", 480), ("bitrate", 0)] == "invalid"
#guard c .videoEncoder "vp8" [("width", 1000000), ("height", 480)] == "unsupported"
#guard c .videoEncoder "vp09.00.10.10" [("width", 320), ("height", 240)] == "unsupported"

end L4Factoidal.WebCodecs.Config
