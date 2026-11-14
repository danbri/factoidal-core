/-
L4Factoidal.WebCodecs.Codec: codec strings (the WebCodecs Codec Registry; RFC 6381; the VP Codec
ISO Media File Format Binding, "Codecs Parameter String"). Record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 5.

`parse` reads a codec string to a `Codec`, or refuses it. Three families:

  * names that are whole strings (`vp8`, `opus`, `flac`, `mp3`, `vorbis`, `ulaw`, `alaw`, the five
    `pcm-*` and the six `mp4a.*` strings of the AAC registration): accepted exactly
    (`Named.ofName?_name`, `Named.ofName?_sound`), with no case folding and no trimming;
  * `vp09.PP.LL.DD` with the optional `.CC.cp.tc.mc.FF`: the fields are two decimal digits each,
    and the profile constrains bit depth and chroma subsampling (`Vp9.valid`,
    `vp9_profile_depth`, `vp9_profile_chroma`);
  * `avc1.PPCCLL` and `avc3.PPCCLL`: six hexadecimal digits.

`av01.*`, `hev1.*` and `hvc1.*` are not read yet (they parse to `none`, as an unknown codec
does): this engine implements no codec, so the only effect is the label.
-/
namespace L4Factoidal.WebCodecs.Codec

/-- The codecs whose codec string is one fixed name. -/
inductive Named where
  | vp8 | opus | flac | mp3 | vorbis | ulaw | alaw
  | pcmU8 | pcmS16 | pcmS24 | pcmS32 | pcmF32
  | aacLc | aacLc0 | aacHe | aacHe0 | aacHe2 | aacMpeg2
  deriving DecidableEq, Repr, Inhabited

namespace Named

def name : Named → String
  | .vp8 => "vp8" | .opus => "opus" | .flac => "flac" | .mp3 => "mp3" | .vorbis => "vorbis"
  | .ulaw => "ulaw" | .alaw => "alaw"
  | .pcmU8 => "pcm-u8" | .pcmS16 => "pcm-s16" | .pcmS24 => "pcm-s24" | .pcmS32 => "pcm-s32" | .pcmF32 => "pcm-f32"
  | .aacLc => "mp4a.40.2" | .aacLc0 => "mp4a.40.02" | .aacHe => "mp4a.40.5" | .aacHe0 => "mp4a.40.05"
  | .aacHe2 => "mp4a.40.29" | .aacMpeg2 => "mp4a.67"

def all : List Named :=
  [.vp8, .opus, .flac, .mp3, .vorbis, .ulaw, .alaw, .pcmU8, .pcmS16, .pcmS24, .pcmS32, .pcmF32,
   .aacLc, .aacLc0, .aacHe, .aacHe0, .aacHe2, .aacMpeg2]

def ofName? (s : String) : Option Named := all.find? (·.name == s)

def isVideo : Named → Bool
  | .vp8 => true
  | _ => false

/-- Round trip. Says: every registered fixed name is read as its codec. -/
theorem ofName?_name (c : Named) : ofName? c.name = some c := by
  cases c <;> decide

/-- Exactness. Says: a string is read as a named codec only when it is that codec's registered
name, character for character: no other casing, no surrounding space, no suffix is accepted. With
`ofName?_name`: the strings accepted are exactly the 18 registered names. -/
theorem ofName?_sound (s : String) (c : Named) (h : ofName? s = some c) : c.name = s := by
  have := List.find?_some h
  simpa using this

end Named

/-- The fields of a VP9 codec string. -/
structure Vp9 where
  profile : Nat
  level : Nat
  depth : Nat
  /-- Chroma subsampling: 0 and 1 are 4:2:0, 2 is 4:2:2, 3 is 4:4:4. `none` in the short form. -/
  chroma : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- The VP9 levels, as the two digits of the string (1, 1.1, 2, ..., 6.2). -/
def vp9Levels : List Nat := [10, 11, 20, 21, 30, 31, 40, 41, 50, 51, 52, 60, 61, 62]

/-- "Codecs Parameter String" of the VP binding: profiles 0 and 1 are 8-bit, 2 and 3 are 10 or
12-bit; profiles 0 and 2 are 4:2:0, 1 and 3 are 4:2:2 or 4:4:4 (the short form says nothing about
chroma, and stands for 4:2:0, which only profiles 0 and 2 have). -/
def Vp9.valid (v : Vp9) : Bool :=
  v.profile ≤ 3 && vp9Levels.contains v.level &&
  (if v.profile ≤ 1 then v.depth == 8 else v.depth == 10 || v.depth == 12) &&
  (match v.chroma with
   | none => v.profile == 0 || v.profile == 2
   | some c => if v.profile == 0 || v.profile == 2 then c ≤ 1 else c == 2 || c == 3)

inductive Codec where
  | named (c : Named)
  | vp9 (v : Vp9)
  /-- `avc1` (`avc3` when the flag is set): profile, constraint flags and level bytes. -/
  | avc (avc3 : Bool) (profile constraints level : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Exactly two decimal digits, as a number. -/
def dec2? (s : String) : Option Nat :=
  match s.toList with
  | [a, b] => if a.isDigit && b.isDigit then some ((a.toNat - 48) * 10 + (b.toNat - 48)) else none
  | _ => none

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Exactly six hexadecimal digits, as three bytes. -/
def hex6? (s : String) : Option (Nat × Nat × Nat) :=
  match s.toList.mapM hexDigit? with
  | some [a, b, c, d, e, f] => some (a * 16 + b, c * 16 + d, e * 16 + f)
  | _ => none

def parseVp9 (fields : List String) : Option Vp9 :=
  match fields.mapM dec2? with
  | some [p, l, d] => let v : Vp9 := { profile := p, level := l, depth := d }; if v.valid then some v else none
  | some [p, l, d, c, _cp, _tc, _mc, f] =>
    let v : Vp9 := { profile := p, level := l, depth := d, chroma := some c }
    if v.valid && f ≤ 1 then some v else none
  | _ => none

/-- The codec a string names; `none` for a string that is not in the registry's grammar as read
here. The string is taken as it is: surrounding whitespace or another casing is not a codec string. -/
def parse (s : String) : Option Codec :=
  match Named.ofName? s with
  | some c => some (.named c)
  | none =>
    match s.splitOn "." with
    | "vp09" :: fields => (parseVp9 fields).map .vp9
    | ["avc1", h] => (hex6? h).map fun (p, c, l) => .avc false p c l
    | ["avc3", h] => (hex6? h).map fun (p, c, l) => .avc true p c l
    | _ => none

/-! ## Theorems -/

/-- Profile constraint. Says: a valid VP9 string has 8-bit depth exactly when its profile is 0 or 1. -/
theorem vp9_profile_depth (v : Vp9) (h : v.valid = true) : (v.depth = 8 ↔ v.profile ≤ 1) := by
  unfold Vp9.valid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, _⟩, hd⟩, _⟩ := h
  split at hd
  · simp_all
  · rename_i hp
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    constructor
    · intro h8; omega
    · intro hle; exact absurd hle hp

/-- Profile constraint. Says: a valid VP9 string that gives its chroma subsampling has 4:2:0
(0 or 1) exactly when its profile is 0 or 2. -/
theorem vp9_profile_chroma (v : Vp9) (c : Nat) (h : v.valid = true) (hc : v.chroma = some c) :
    (c ≤ 1 ↔ (v.profile = 0 ∨ v.profile = 2)) := by
  unfold Vp9.valid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, hc] at h
  obtain ⟨_, hch⟩ := h
  split at hch
  · rename_i hp
    simp only [Bool.or_eq_true, beq_iff_eq] at hp
    simp_all
  · rename_i hp
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hp
    simp only [Bool.or_eq_true, beq_iff_eq] at hch
    constructor
    · intro h1; omega
    · intro h02; rcases h02 with h0 | h2
      · exact absurd h0 hp.1
      · exact absurd h2 hp.2

/-- Refusal. Says: `parseVp9` answers only strings whose fields are valid by `Vp9.valid`. -/
theorem parseVp9_valid (fields : List String) (v : Vp9) (h : parseVp9 fields = some v) : v.valid = true := by
  unfold parseVp9 at h
  split at h
  · simp only at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; assumption
    · cases h
  · simp only at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hv
      exact hv.1
    · cases h
  · cases h

/-! ## Tests (`webcodecs/vp9-codec-string-profile-constraints.https.any.js`, `video-decoder`, `audio-decoder`) -/

private def ok (s : String) : Bool := (parse s).isSome

#guard ok "vp8" && ok "opus" && ok "pcm-s16" && ok "mp4a.40.2" && ok "vp09.00.10.08" && ok "vp09.02.10.10" && ok "vp09.01.10.08.03.01.01.01.00"
#guard ok "avc1.42001E" && ok "avc3.42001E" && ok "avc1.4D401D" && ok "avc1.64001f"
-- Not codec strings: other casing, whitespace, a MIME type, the ambiguous `vp9`, another family's prefix.
#guard !ok "vP8" && !ok " opus " && !ok "Vp09.00.10.08" && !ok "video/webm; codecs=\"vp8\"" && !ok "vp9" && !ok "vp08.00.10.08"
#guard !ok "opus.123" && !ok "mp4a.FF.9" && !ok "bogus" && !ok ""
-- The profile constraints of the test.
#guard !ok "vp09.00" && !ok "vp09.00.10" && !ok "vp09.00.10.09" && !ok "vp09.00.10.10" && !ok "vp09.00.10.12"
#guard !ok "vp09.00.10.08.02" && !ok "vp09.00.10.08.03.01.01.01.00" && !ok "vp09.02.10.08" && !ok "vp09.02.10.10.03.01.01.01.00"
#guard !ok "vp09.99.99.08" && !ok "avc1.42001" && !ok "avc1.42001G" && !ok "avc1.42001E.1"
#guard parse "avc1.42001E" == some (.avc false 0x42 0 0x1E)
#guard parse "vp09.02.10.10" == some (.vp9 { profile := 2, level := 10, depth := 10 })

end L4Factoidal.WebCodecs.Codec
