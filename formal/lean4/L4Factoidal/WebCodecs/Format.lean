/-
L4Factoidal.WebCodecs.Format: the pixel formats of WebCodecs (§9.8 Pixel Format) and their planes
(record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 4).

A format is a list of planes. A plane has the bytes of one sample position (`sampleBytes`: 1 for an
8-bit sample, 2 for a 10 or 12-bit sample or for NV12's interleaved U and V, 4 for a packed RGB
pixel) and its sub-sampling factors against the frame (`subW`, `subH`). Every size the layout
module computes is a function of these three numbers.
-/
namespace L4Factoidal.WebCodecs

inductive Chroma where
  | c420 | c422 | c444
  deriving DecidableEq, Repr, Inhabited

inductive Depth where
  | d8 | d10 | d12
  deriving DecidableEq, Repr, Inhabited

/-- `VideoPixelFormat` (WebCodecs §9.8): the planar YUV family by chroma layout, alpha plane and
bit depth; NV12; and the four packed RGB formats. -/
inductive PixelFormat where
  | yuv (c : Chroma) (alpha : Bool) (d : Depth)
  | nv12 | rgba | rgbx | bgra | bgrx
  deriving DecidableEq, Repr, Inhabited

namespace PixelFormat

def name : PixelFormat → String
  | .yuv c a d =>
    "I" ++ (match c with | .c420 => "420" | .c422 => "422" | .c444 => "444") ++
      (if a then "A" else "") ++ (match d with | .d8 => "" | .d10 => "P10" | .d12 => "P12")
  | .nv12 => "NV12" | .rgba => "RGBA" | .rgbx => "RGBX" | .bgra => "BGRA" | .bgrx => "BGRX"

/-- Every format, in the order of the IDL enumeration's families. -/
def all : List PixelFormat :=
  [.yuv .c420 false .d8, .yuv .c420 false .d10, .yuv .c420 false .d12,
   .yuv .c420 true .d8, .yuv .c420 true .d10, .yuv .c420 true .d12,
   .yuv .c422 false .d8, .yuv .c422 false .d10, .yuv .c422 false .d12,
   .yuv .c422 true .d8, .yuv .c422 true .d10, .yuv .c422 true .d12,
   .yuv .c444 false .d8, .yuv .c444 false .d10, .yuv .c444 false .d12,
   .yuv .c444 true .d8, .yuv .c444 true .d10, .yuv .c444 true .d12,
   .nv12, .rgba, .rgbx, .bgra, .bgrx]

/-- The format an IDL enumeration value names; `none` for any other string. -/
def ofName? (s : String) : Option PixelFormat := all.find? (·.name == s)

def isRgb : PixelFormat → Bool
  | .rgba | .rgbx | .bgra | .bgrx => true
  | _ => false

/-- The format has an alpha channel that carries values (RGBX and BGRX have padding). -/
def hasAlpha : PixelFormat → Bool
  | .yuv _ a _ => a
  | .rgba | .bgra => true
  | _ => false

end PixelFormat

structure Plane where
  /-- Bytes of one sample position of the plane. -/
  sampleBytes : Nat
  /-- Horizontal sub-sampling factor. -/
  subW : Nat
  /-- Vertical sub-sampling factor. -/
  subH : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The planes of a format, in the order of §9.8 (Y, U, V, A; Y, UV; one packed plane). -/
def PixelFormat.planes : PixelFormat → List Plane
  | .yuv c a d =>
    let b := match d with | .d8 => 1 | _ => 2
    let sw := match c with | .c444 => 1 | _ => 2
    let sh := match c with | .c420 => 2 | _ => 1
    [⟨b, 1, 1⟩, ⟨b, sw, sh⟩, ⟨b, sw, sh⟩] ++ (if a then [⟨b, 1, 1⟩] else [])
  | .nv12 => [⟨1, 1, 1⟩, ⟨2, 2, 2⟩]
  | _ => [⟨4, 1, 1⟩]

/-! ## Theorems -/

/-- Round trip. Says: the name of a format is read back as that format, for all 23 formats.
Does not say: anything about strings that are not names (`ofName?_sound`). -/
theorem PixelFormat.ofName?_name (f : PixelFormat) : PixelFormat.ofName? f.name = some f := by
  cases f with
  | yuv c a d => cases c <;> cases a <;> cases d <;> decide
  | _ => decide

/-- Soundness. Says: a string is accepted only when it is exactly the name of the format answered,
so no string outside the enumeration is accepted. -/
theorem PixelFormat.ofName?_sound (s : String) (f : PixelFormat) (h : PixelFormat.ofName? s = some f) :
    f.name = s := by
  have := List.find?_some h
  simpa using this

/-- Invariant. Says: every plane of every format has positive sub-sampling factors and a positive
sample size, so the divisions of the layout module never divide by zero. -/
theorem PixelFormat.planes_pos (f : PixelFormat) :
    ∀ p ∈ f.planes, 0 < p.subW ∧ 0 < p.subH ∧ 0 < p.sampleBytes := by
  have h : f.planes.all (fun p => decide (0 < p.subW) && decide (0 < p.subH) && decide (0 < p.sampleBytes)) = true := by
    cases f with
    | yuv c a d => cases c <;> cases a <;> cases d <;> decide
    | _ => decide
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp at this
  exact ⟨this.1.1, this.1.2, this.2⟩

#guard PixelFormat.all.length == 23
#guard PixelFormat.ofName? "I420AP10" == some (.yuv .c420 true .d10)
#guard PixelFormat.ofName? "ABCD" == none
#guard PixelFormat.ofName? "rgba" == none
#guard (PixelFormat.ofName? "I422").map (·.planes) == some [⟨1, 1, 1⟩, ⟨1, 2, 1⟩, ⟨1, 2, 1⟩]
#guard (PixelFormat.all.map (·.name)).eraseDups.length == 23

end L4Factoidal.WebCodecs
