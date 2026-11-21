/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Paralliverse.ProgramCPU

/-!
# Glyph masks: a genuine two-dimensional Paralliverse stencil workload

A mask is an array of coverage alpha values (u32 transport, 0..255 for
admitted font inputs). The independent reference computes synthetic bolding:
each output pixel is the maximum alpha of the old mask's 3x3 neighbourhood,
with transparent pixels outside the image.

The CPU backend runs the *same stencil*, not an image-independent scalar map,
using the existing task-based Par.mapChunks over output pixel indices.
Every invocation reads only the original mask. The proof applies to all
worker counts, dimensions and inputs, including zero-sized/unadmitted grids.
The separate Admitted predicate states the actual font-mask boundary.

The typed Program extension composes whole-mask operations through the
already-existing general Paralliverse DSL. No new graph theory is invented.

Unproved/separate boundaries: font outline -> alpha mask, host output
transport, GPU WGSL lowering, device scheduling, physical IO and hardware.
-/

namespace L4Factoidal.Paralliverse.GlyphMask

structure Mask where
  width : Nat
  height : Nat
  alpha : Array UInt32
  deriving Repr, BEq

/-- Input must be one row-major coverage value per pixel, each in 0..255. -/
def Admitted (m : Mask) : Prop :=
  m.alpha.size = m.width * m.height ∧
  ∀ a ∈ m.alpha.toList, a.toNat ≤ 255

/-- Zero outside the mask or when the input is malformed. -/
def read (m : Mask) (x y : Int) : UInt32 :=
  if x < 0 || y < 0 then 0
  else if x.toNat < m.width && y.toNat < m.height then
    (m.alpha[y.toNat * m.width + x.toNat]?).getD 0
  else 0

def offsets : List Int := [-1, 0, 1]

/-- A source-pixel neighbourhood is a 3 × 3 stencil, not 9 independent maps. -/
def stencil (m : Mask) (i : Nat) : List UInt32 :=
  let x := Int.ofNat (i % m.width)
  let y := Int.ofNat (i / m.width)
  offsets.flatMap fun dy =>
    offsets.map fun dx => read m (x + dx) (y + dy)

/-- Pixel-local, exact unsigned morphological dilation. -/
def boldAt (m : Mask) (i : Nat) : UInt32 :=
  (stencil m i).foldl (fun a b => if a.toNat < b.toNat then b else a) 0

/-- Independent sequential denotation. -/
def boldSpec (m : Mask) : Mask :=
  {m with alpha := (Array.range (m.width * m.height)).map (boldAt m)}

/-- Actual Lean task-based CPU implementation with arbitrary worker count. -/
def boldCPU (workers : Nat) (m : Mask) : Mask :=
  let xs := Array.range (m.width * m.height)
  let ys := L4Factoidal.Par.mapChunks workers (boldAt m) xs
  {m with alpha := ys}

/-- Task decomposition preserves every output cell for every input and worker count. -/
theorem boldCPU_eq_boldSpec (workers : Nat) (m : Mask) :
    boldCPU workers m = boldSpec m := by
  simp only [boldCPU, boldSpec, L4Factoidal.Par.mapChunks_eq]

/-- The stencil always writes one word per logical pixel. -/
theorem boldSpec_size (m : Mask) :
    (boldSpec m).alpha.size = m.width * m.height := by
  simp [boldSpec]

/-- Positive/zero alpha values are not implicitly reordered or packed. -/
private def centerDot : Mask :=
  {width := 3, height := 3, alpha := #[0,0,0, 0,255,0, 0,0,0]}
#guard (boldSpec centerDot).alpha == #[255,255,255,255,255,255,255,255,255]
#guard (boldCPU 1 centerDot).alpha == (boldSpec centerDot).alpha
#guard (boldCPU 4 centerDot).alpha == (boldSpec centerDot).alpha
#guard (boldCPU 16 centerDot).alpha == (boldSpec centerDot).alpha
#guard (boldSpec {width := 0, height := 0, alpha := #[]}).alpha == #[]

/-- A 3×3 integer box blur with transparent samples beyond the mask.
No floating-point rounding or implementation-dependent image filtering. -/
def blurAt (m : Mask) (i : Nat) : UInt32 :=
  UInt32.ofNat (((stencil m i).map UInt32.toNat).sum / 9)

def blurSpec (m : Mask) : Mask :=
  {m with alpha := (Array.range (m.width * m.height)).map (blurAt m)}

def blurCPU (workers : Nat) (m : Mask) : Mask :=
  let xs := Array.range (m.width * m.height)
  let ys := L4Factoidal.Par.mapChunks workers (blurAt m) xs
  {m with alpha := ys}

theorem blurCPU_eq_blurSpec (workers : Nat) (m : Mask) :
    blurCPU workers m = blurSpec m := by
  simp only [blurCPU, blurSpec, L4Factoidal.Par.mapChunks_eq]

/-- An outer stroke is synthetic bold alpha minus the original alpha.
The subtraction is saturated at zero rather than a wrapping u32 difference. -/
def outlineAt (m : Mask) (i : Nat) : UInt32 :=
  UInt32.ofNat ((boldAt m i).toNat - (m.alpha[i]?.getD 0).toNat)

def outlineSpec (m : Mask) : Mask :=
  {m with alpha := (Array.range (m.width * m.height)).map (outlineAt m)}

def outlineCPU (workers : Nat) (m : Mask) : Mask :=
  let xs := Array.range (m.width * m.height)
  let ys := L4Factoidal.Par.mapChunks workers (outlineAt m) xs
  {m with alpha := ys}

theorem outlineCPU_eq_outlineSpec (workers : Nat) (m : Mask) :
    outlineCPU workers m = outlineSpec m := by
  simp only [outlineCPU, outlineSpec, L4Factoidal.Par.mapChunks_eq]

#guard (blurSpec centerDot).alpha == #[28,28,28,28,28,28,28,28,28]
#guard (outlineSpec centerDot).alpha == #[255,255,255,255,0,255,255,255,255]
#guard (blurCPU 8 centerDot).alpha == (blurSpec centerDot).alpha
#guard (outlineCPU 8 centerDot).alpha == (outlineSpec centerDot).alpha

/-- Closed primitive language: whole-mask neighbourhood operations. -/
inductive Atom where
  | mask
  deriving DecidableEq, Repr

abbrev maskShape : Shape Atom := .scalar .mask

def base : Atom → Type
  | .mask => Mask

inductive Op : Shape Atom → Shape Atom → Type where
  | syntheticBold : Op maskShape maskShape
  | softBlur : Op maskShape maskShape
  | outerStroke : Op maskShape maskShape

def reference {a b : Shape Atom} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .syntheticBold, m => boldSpec m
  | .softBlur, m => blurSpec m
  | .outerStroke, m => outlineSpec m

def implementation (workers : Nat) {a b : Shape Atom} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .syntheticBold, m => boldCPU workers m
  | .softBlur, m => blurCPU workers m
  | .outerStroke, m => outlineCPU workers m

theorem primitive_agrees (workers : Nat) {a b : Shape Atom}
    (op : Op a b) (x : Shape.Value base a) :
    implementation workers op x = reference op x := by
  cases op with
  | syntheticBold => exact boldCPU_eq_boldSpec workers x
  | softBlur => exact blurCPU_eq_blurSpec workers x
  | outerStroke => exact outlineCPU_eq_outlineSpec workers x

/-- Every composition of the font-mask primitive has the sequential meaning. -/
theorem programCPU_eq_reference (workers : Nat) {a b : Shape Atom}
    (p : Program Op a b) :
    Program.runCPU base (implementation workers) workers p =
      Program.eval base (@reference) p :=
  Program.runCPU_eq_eval base (@reference) (implementation workers)
    (primitive_agrees workers) workers p

def bold : Program Op maskShape maskShape := .prim .syntheticBold
def blur : Program Op maskShape maskShape := .prim .softBlur
def outline : Program Op maskShape maskShape := .prim .outerStroke
def twice : Program Op maskShape maskShape := .seq bold bold

/-- Keep original and boldened masks: useful for outlining and visual diff. -/
def compare : Program Op maskShape (.pair maskShape maskShape) :=
  .fanout .identity bold

#guard (Program.runCPU base (implementation 8) 8 bold centerDot).alpha ==
  (boldSpec centerDot).alpha
#guard (Program.runCPU base (implementation 8) 8 compare centerDot).1.alpha ==
  centerDot.alpha
#guard (Program.runCPU base (implementation 8) 8 compare centerDot).2.alpha ==
  (boldSpec centerDot).alpha

#print axioms boldCPU_eq_boldSpec
#print axioms blurCPU_eq_blurSpec
#print axioms outlineCPU_eq_outlineSpec
#print axioms boldSpec_size
#print axioms primitive_agrees
#print axioms programCPU_eq_reference

end L4Factoidal.Paralliverse.GlyphMask
