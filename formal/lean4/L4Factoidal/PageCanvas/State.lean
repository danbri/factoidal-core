/-
L4Factoidal.PageCanvas.State: the drawing state of a Canvas 2D context and its stack
(HTML §4.12.5.1.4 "the canvas state"; record docs/designissues/2026-11-08-canvas-2d.md).

`save()` pushes a copy of the drawing state; `restore()` pops it, and does nothing when
the stack is empty. The current path and the bitmap are not part of the drawing state.

Theorems: `restore_save` (restore after save gives the state before the save) and
`restore_setters_save` (the same with any setters between them: what a setter changes
is only the current drawing state, never the saved ones).
-/
import L4Factoidal.PageCanvas.Raster
import L4Factoidal.PageCanvas.Stroke

namespace L4Factoidal.PageCanvas

inductive Align where | start | end_ | left | right | center
  deriving Repr, Inhabited, BEq
inductive Baseline where | top | hanging | middle | alphabetic | ideographic | bottom
  deriving Repr, Inhabited, BEq
inductive Direction where | ltr | rtl | inherit
  deriving Repr, Inhabited, BEq

/-- A parsed CSS font (the parts the canvas uses). -/
structure Font where
  /-- The text as the `font` getter gives it (the serialised font). -/
  text : String := "10px sans-serif"
  size : Float := 10
  bold : Bool := false
  italic : Bool := false
  family : String := "sans-serif"
  deriving Repr, Inhabited

/-- HTML §4.12.5.1.4: everything `save()` keeps. -/
structure DrawState where
  ctm : Matrix := {}
  clip : Mask := none
  fill : Style := .color RGBA.black
  stroke : Style := .color RGBA.black
  alpha : Float := 1
  op : Op := .sourceOver
  line : StrokeStyle := { miterLimit := 10 }
  shadowColor : RGBA := RGBA.transparent
  shadowBlur : Float := 0
  shadowX : Float := 0
  shadowY : Float := 0
  font : Font := {}
  align : Align := .start
  baseline : Baseline := .alphabetic
  direction : Direction := .inherit
  letterSpacing : Float := 0
  wordSpacing : Float := 0
  smoothing : Bool := true
  smoothingQuality : String := "low"
  filter : String := "none"
  fontKerning : String := "auto"
  deriving Inhabited

/-- The current drawing state and the saved ones, the last saved first. -/
structure Stack where
  cur : DrawState := {}
  saved : List DrawState := []
  deriving Inhabited

/-- The most states `save()` keeps; a save past it is ignored (the engine's bound). -/
def maxSaved : Nat := 1024

namespace Stack

def save (s : Stack) : Stack :=
  if s.saved.length ≥ maxSaved then s else { s with saved := s.cur :: s.saved }

def restore (s : Stack) : Stack :=
  match s.saved with
  | [] => s
  | d :: rest => { cur := d, saved := rest }

/-- Change the current drawing state only. -/
def set (s : Stack) (f : DrawState → DrawState) : Stack := { s with cur := f s.cur }

/-- Restore after save gives the state before the save. -/
theorem restore_save (s : Stack) (h : s.saved.length < maxSaved) : (s.save).restore = s := by
  have : ¬ s.saved.length ≥ maxSaved := by omega
  simp [save, restore, this]

/-- A setter never changes the saved states. -/
theorem set_saved (s : Stack) (f : DrawState → DrawState) : (s.set f).saved = s.saved := rfl

/-- Any setters between a save and a restore: the restore gives the state of the save. -/
theorem restore_setters_save (s : Stack) (fs : List (DrawState → DrawState)) (h : s.saved.length < maxSaved) :
    (fs.foldl Stack.set s.save).restore = s := by
  have : ¬ s.saved.length ≥ maxSaved := by omega
  have key : ∀ (t : Stack) (gs : List (DrawState → DrawState)), (gs.foldl Stack.set t).saved = t.saved := by
    intro t gs
    induction gs generalizing t with
    | nil => rfl
    | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; rfl
  have hs := key s.save fs
  simp only [save, this, if_false] at hs ⊢
  simp only [restore, hs]

end Stack
end L4Factoidal.PageCanvas
