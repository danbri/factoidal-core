import L4Factoidal.Unicode.JoiningData

/-!
# The Arabic shaper's joining forms

The part of HarfBuzz's Arabic shaper (`hb-ot-shaper-arabic.cc`, 15.0.0) that
the Lean shaper uses (https://github.com/danbri/factoidal/issues/1275):

1. `joiningActions`: the joining state machine over the code points of a run,
   in logical order. Each code point has a joining column
   (`Unicode.JoiningData`, from ArabicShaping.txt): U, L, R, D (C is D, so
   ZWJ joins and ZWNJ, which is U, breaks a join), the Syriac groups ALAPH and
   DALATH RISH, or T. A transparent code point (marks, and other Mn, Me and
   Cf) gets no form and is skipped, so a letter joins across its marks. The
   machine gives each other code point one of the forms isol, fina, fin2,
   fin3, medi, med2, init, or none, and may change the form of the code point
   before it (`arabic_state_table`).
2. `maskOf`: the feature mask of each form. A glyph gets the global mask and
   the mask of its form, and each form's GSUB feature applies only to glyphs
   with its mask (`SfntSubst.substitute`).
3. `stages`: the GSUB stages of `collect_features_arabic`: `stch`; `ccmp` and
   `locl`; each of the seven forms in its own stage; `rlig`; `calt`, with a
   pause after it unless the font has `rclt`; then `liga`, `clig`, `mset`.

The run has no text before or after it here (HarfBuzz pre- and post-context):
layout shapes whole words, and a space does not join.

Not here: the fallback shaping of Arabic with presentation forms for a font
that has no GSUB forms, `stch` stretching, Mongolian variation selectors and
the reordering of Arabic modifier combining marks (`reorder_marks_arabic`).
-/
namespace L4Factoidal.Rendering.SfntArabic

/-- The forms, in HarfBuzz's `arabic_action_t` order; index 7 is no form. -/
def forms : Array String := #["isol", "fina", "fin2", "fin3", "medi", "med2", "init"]

/-- No form (HarfBuzz `NONE`). -/
def noForm : Nat := 7

/-- One entry of the state machine: the form of the previous joining code point
(`noForm` keeps it), the form of this one, and the next state. -/
structure Entry where
  prev : Nat
  curr : Nat
  next : Nat
  deriving Repr, BEq

private def e (p c n : Nat) : Entry := ⟨p, c, n⟩

/-- HarfBuzz `arabic_state_table`: 7 states, columns U, L, R, D, ALAPH,
DALATH RISH. 0 isol, 1 fina, 2 fin2, 3 fin3, 4 medi, 5 med2, 6 init, 7 none. -/
def table : Array (Array Entry) := #[
  -- State 0: prev was U, not willing to join.
  #[e 7 7 0, e 7 0 2, e 7 0 1, e 7 0 2, e 7 0 1, e 7 0 6],
  -- State 1: prev was R or ISOL/ALAPH, not willing to join.
  #[e 7 7 0, e 7 0 2, e 7 0 1, e 7 0 2, e 7 2 5, e 7 0 6],
  -- State 2: prev was D/L in ISOL form, willing to join.
  #[e 7 7 0, e 7 0 2, e 6 1 1, e 6 1 3, e 6 1 4, e 6 1 6],
  -- State 3: prev was D in FINA form, willing to join.
  #[e 7 7 0, e 7 0 2, e 4 1 1, e 4 1 3, e 4 1 4, e 4 1 6],
  -- State 4: prev was FINA ALAPH, not willing to join.
  #[e 7 7 0, e 7 0 2, e 5 0 1, e 5 0 2, e 5 2 5, e 5 0 6],
  -- State 5: prev was FIN2/FIN3 ALAPH, not willing to join.
  #[e 7 7 0, e 7 0 2, e 0 0 1, e 0 0 2, e 0 2 5, e 0 0 6],
  -- State 6: prev was DALATH/RISH, not willing to join.
  #[e 7 7 0, e 7 0 2, e 7 0 1, e 7 0 2, e 7 3 5, e 7 0 6]]

/-- The table is well formed: 7 states of 6 columns, each next state a state
and each form a form or none. -/
theorem table_wellFormed :
    table.size = 7 ∧ ∀ s ∈ table.toList, s.size = 6 ∧
      ∀ x ∈ s.toList, x.next < 7 ∧ x.prev ≤ noForm ∧ x.curr ≤ noForm := by
  decide

/-- The machine's state over a run: the forms so far, the position of the last
code point that was not transparent, and the state. -/
structure Joining where
  out : Array Nat := #[]
  prev : Option Nat := none
  state : Nat := 0

/-- The previous joining code point's form becomes `form`, unless that is `noForm`. -/
def setPrev (out : Array Nat) (prev : Option Nat) (form : Nat) : Array Nat :=
  match prev with
  | some p => if form != noForm then out.set! p form else out
  | none => out

theorem setPrev_size (out : Array Nat) (prev : Option Nat) (form : Nat) :
    (setPrev out prev form).size = out.size := by
  unfold setPrev
  split
  · split <;> simp
  · rfl

/-- One code point (HarfBuzz `arabic_joining`, the loop body). -/
def step (st : Joining) (cp : Nat) : Joining :=
  if Unicode.JoiningData.joiningOf cp ≥ 6 then { st with out := st.out.push noForm }
  else
    let x := (table.getD st.state #[]).getD (Unicode.JoiningData.joiningOf cp) ⟨noForm, noForm, 0⟩
    { out := (setPrev st.out st.prev x.prev).push x.curr, prev := some st.out.size, state := x.next }

/-- The form of each code point of a run (an index into `forms`, or `noForm`). -/
def joiningActions (cps : Array Nat) : Array Nat := (cps.foldl step {}).out

theorem step_size (st : Joining) (cp : Nat) : (step st cp).out.size = st.out.size + 1 := by
  unfold step
  split <;> simp [setPrev_size]

theorem foldl_step_size (l : List Nat) (st : Joining) :
    (l.foldl step st).out.size = st.out.size + l.length := by
  induction l generalizing st with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, step_size]; omega

/-- Each code point gets exactly one form. -/
theorem joiningActions_size (cps : Array Nat) : (joiningActions cps).size = cps.size := by
  unfold joiningActions
  rw [← Array.foldl_toList, foldl_step_size]
  simp

-- م ر ح ب ا: init fina init medi fina (as HarfBuzz gives for Noto Sans Arabic).
#guard joiningActions #[0x645, 0x631, 0x62D, 0x628, 0x627] == #[6, 1, 6, 4, 1]
-- A mark is transparent: ب َ ا is init, none, fina.
#guard joiningActions #[0x628, 0x64E, 0x627] == #[6, 7, 1]
-- ZWNJ breaks the join, ZWJ makes one: ب ZWNJ ب, and ZWJ ب ZWJ.
#guard joiningActions #[0x628, 0x200C, 0x628] == #[0, 7, 0]
#guard joiningActions #[0x200D, 0x628, 0x200D] == #[6, 4, 1]
-- Latin and spaces get no form.
#guard joiningActions #[0x61, 0x20, 0x62] == #[7, 7, 7]
-- Syriac: ܐ (ALAPH) after ܒ (D) is fina; ALAPH after DALATH is fin3.
#guard joiningActions #[0x712, 0x710] == #[6, 1]
#guard joiningActions #[0x715, 0x710] == #[0, 3]

/-- The mask of `rtlm`, which HarfBuzz gives to each glyph of a right-to-left
run that was not replaced by its mirror (`hb_ot_rotate_chars`). -/
def rtlmMask : Nat := 256

/-- Bits 1 to 7 are the forms, bit 8 `rtlm`; every other feature is global (bit 0). -/
def maskOf (tag : String) : Nat :=
  match forms.findIdx? (· == tag) with
  | some k => 2 ^ (k + 1)
  | none => if tag == "rtlm" then rtlmMask else 1

/-- The mask of a glyph with form `a`. -/
def formMask (a : Nat) : Nat := if a < forms.size then 2 ^ (a + 1) else 0

/-- Scripts with the Arabic shaper (HarfBuzz `hb_ot_shaper_categorize`). -/
def shaperScripts : List String := ["Arab", "Syrc"]

/-- Scripts whose USE shaping runs the joining machine (HarfBuzz `has_arabic_joining`). -/
def joiningScripts : List String :=
  ["Adlm", "Arab", "Chrs", "Rohg", "Mand", "Mani", "Mong", "Nkoo", "Ougr", "Phag", "Phlp",
   "Sogd", "Syrc"]

/-- GSUB stages of the Arabic shaper for a right-to-left run (see the module
comment). `hasRclt`: the font has `rclt`, so `calt` shares a stage with `liga`. -/
def stages (hasRclt : Bool) : List (List String) :=
  [["rvrn"], ["rtla", "rtlm", "stch"], ["ccmp", "locl"]] ++ forms.toList.map ([·]) ++
  [["rlig"]] ++
  (if hasRclt then [["calt", "liga", "clig", "mset", "rclt"]]
   else [["calt"], ["liga", "clig", "mset", "rclt"]])

end L4Factoidal.Rendering.SfntArabic
