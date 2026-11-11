import L4Factoidal.Unicode.Normalization

/-! # Bounded ink for stacked combining marks ("Zalgo" text)

A cluster of a base and many combining marks can stack its ink far above and below
its line. Three bounds hold here, in font units (`Int`), before glyphs are scaled to
pixels:

1. **Stream-Safe Text Format** (UAX #15 §13): a run of more than 30 non-starters
   gets U+034F COMBINING GRAPHEME JOINER before its 31st, so a cluster has at most 30
   marks (`streamSafe`; `streamSafe_bounded`, `streamSafe_erase`). The shaper's work
   per cluster is bounded by it.
2. **Cluster ink box**: each glyph's ink (the box of its outline points; a Bézier
   curve lies in the hull of its points) is moved, when it must be, into its cluster's
   advance box widened by `clusterBound` = 31 em on each side, and the ascender and
   descender widened by the same (`place`, `place_inside`). A glyph whose ink is wider
   or taller than that box is not drawn (`place` gives `none`). In pixels the bound is
   31 times the font size: a function of the font size and the 30-mark limit only.
3. **Ink rectangle**: the union of the ink boxes of a word contains each of them
   (`unionAll_contains`), so a damage or overflow rectangle made from it holds all
   the ink.

Non-starter here is a character with a canonical combining class other than 0
(UAX #15 counts the non-starters of the NFKD form; a precomposed character with
marks in its decomposition counts as one here). -/
namespace L4Factoidal.Rendering.InkBound

/-- U+034F COMBINING GRAPHEME JOINER: canonical combining class 0, default ignorable. -/
def cgj : Char := '͏'

def maxNonStarters : Nat := 30

/-- A character with a canonical combining class other than 0 (never `cgj`). -/
def nonStarter (c : Char) : Bool := c != cgj && Unicode.Normalization.ccc c.toNat != 0

/-- The reference: `n` non-starters came just before. -/
def safeFrom : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs =>
    if nonStarter c then
      if n < maxNonStarters then c :: safeFrom (n+1) cs else cgj :: c :: safeFrom 1 cs
    else c :: safeFrom 0 cs

/-- The same with an accumulator: one loop, no stack per character. -/
def safeAux : Nat → List Char → List Char → List Char
  | _, acc, [] => acc.reverse
  | n, acc, c :: cs =>
    if nonStarter c then
      if n < maxNonStarters then safeAux (n+1) (c :: acc) cs else safeAux 1 (c :: cgj :: acc) cs
    else safeAux 0 (c :: acc) cs

theorem safeAux_eq (n : Nat) (acc cs : List Char) : safeAux n acc cs = acc.reverse ++ safeFrom n cs := by
  induction cs generalizing n acc with
  | nil => simp [safeAux, safeFrom]
  | cons c cs ih =>
    unfold safeAux safeFrom
    split
    · split
      · rw [ih]; simp
      · rw [ih]; simp
    · rw [ih]; simp

/-- UAX #15 §13: the text in Stream-Safe Text Format. -/
def streamSafe (cs : List Char) : List Char := safeAux 0 [] cs

theorem streamSafe_eq (cs : List Char) : streamSafe cs = safeFrom 0 cs := by
  simp [streamSafe, safeAux_eq]

/-- No run of non-starters is longer than 30, counting `n` before the list. -/
def bounded : Nat → List Char → Bool
  | _, [] => true
  | n, c :: cs => if nonStarter c then decide (n+1 ≤ maxNonStarters) && bounded (n+1) cs else bounded 0 cs

private theorem cgj_starter : nonStarter cgj = false := by simp [nonStarter]

theorem safeFrom_bounded (n : Nat) (h : n ≤ maxNonStarters) (cs : List Char) : bounded n (safeFrom n cs) = true := by
  induction cs generalizing n with
  | nil => simp [safeFrom, bounded]
  | cons c cs ih =>
    unfold safeFrom
    split
    · split
      · rename_i hc hn
        simp only [bounded, hc, if_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, ih (n+1) (by omega)⟩
      · rename_i hc _
        simp only [bounded, cgj_starter, hc, if_true, Bool.false_eq_true, if_false, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨by simp [maxNonStarters], ih 1 (by simp [maxNonStarters])⟩
    · rename_i hc
      simp only [bounded, hc, Bool.false_eq_true, if_false]
      exact ih 0 (by omega)

/-- Every run of non-starters of the Stream-Safe text has at most 30 characters. -/
theorem streamSafe_bounded (cs : List Char) : bounded 0 (streamSafe cs) = true := by
  rw [streamSafe_eq]; exact safeFrom_bounded 0 (by simp [maxNonStarters]) cs

theorem safeFrom_erase (n : Nat) (cs : List Char) :
    (safeFrom n cs).filter (· != cgj) = cs.filter (· != cgj) := by
  induction cs generalizing n with
  | nil => simp [safeFrom]
  | cons c cs ih =>
    unfold safeFrom
    split
    · split
      · simp [List.filter_cons, ih]
      · simp [List.filter_cons, ih]
    · simp [List.filter_cons, ih]

/-- Only joiners are added: with the joiners left out, the text is the input. -/
theorem streamSafe_erase (cs : List Char) : (streamSafe cs).filter (· != cgj) = cs.filter (· != cgj) := by
  rw [streamSafe_eq]; exact safeFrom_erase 0 cs

/-- For each character of `streamSafe cs`, the index in `cs` of the character it is
(an added joiner: the character after it). -/
def sourceIndex (cs : List Char) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut n := 0
  let mut i := 0
  for c in cs do
    if nonStarter c then
      if n < maxNonStarters then n := n+1 else
        out := out.push i
        n := 1
    else n := 0
    out := out.push i
    i := i+1
  return out

/-! ### Boxes in font units (y up) -/

structure Box where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `inner` lies in `outer`. -/
def Box.within (inner outer : Box) : Prop :=
  outer.x0 ≤ inner.x0 ∧ inner.x1 ≤ outer.x1 ∧ outer.y0 ≤ inner.y0 ∧ inner.y1 ≤ outer.y1

def Box.shift (b : Box) (dx dy : Int) : Box := ⟨b.x0+dx,b.y0+dy,b.x1+dx,b.y1+dy⟩

def Box.union (a b : Box) : Box := ⟨min a.x0 b.x0,min a.y0 b.y0,max a.x1 b.x1,max a.y1 b.y1⟩

theorem Box.within_union_left (a b : Box) : a.within (a.union b) := by
  simp only [Box.within, Box.union]; omega
theorem Box.within_union_right (a b : Box) : b.within (a.union b) := by
  simp only [Box.within, Box.union]; omega
theorem Box.within_trans {a b c : Box} (h1 : a.within b) (h2 : b.within c) : a.within c := by
  simp only [Box.within] at *; omega

/-- The union of boxes: the ink rectangle of what they draw. -/
def unionAll : List Box → Option Box
  | [] => none
  | b :: bs => some (bs.foldl Box.union b)

private theorem foldl_union_within (bs : List Box) (acc : Box) :
    acc.within (bs.foldl Box.union acc) ∧ ∀ b ∈ bs, b.within (bs.foldl Box.union acc) := by
  induction bs generalizing acc with
  | nil => simp [Box.within]
  | cons x xs ih =>
    have ⟨h1,h2⟩ := ih (acc.union x)
    refine ⟨Box.within_trans (Box.within_union_left acc x) h1, ?_⟩
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Box.within_trans (Box.within_union_right acc b) h1
    · exact h2 b hb

/-- The ink rectangle holds the ink of every box. -/
theorem unionAll_contains (bs : List Box) (b : Box) (h : b ∈ bs) :
    ∃ r, unionAll bs = some r ∧ b.within r := by
  cases bs with
  | nil => simp at h
  | cons x xs =>
    refine ⟨xs.foldl Box.union x, rfl, ?_⟩
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact (foldl_union_within xs b).1
    · exact (foldl_union_within xs x).2 b h

/-! ### Glyph ink in its cluster box -/

/-- How far ink may go past its cluster's advance box and line: one em for the base
and one for each mark the Stream-Safe Text Format lets a cluster have. -/
def clusterBound (unitsPerEm : Nat) : Int := ((maxNonStarters+1)*unitsPerEm : Nat)

/-- The offset nearest `off` that puts `[a, b]` (at offset 0) in `[lo, hi]`. -/
def clampAxis (lo hi a b off : Int) : Int := max (lo-a) (min off (hi-b))

theorem clampAxis_inside (lo hi a b off : Int) (fits : b-a ≤ hi-lo) :
    lo ≤ a+clampAxis lo hi a b off ∧ b+clampAxis lo hi a b off ≤ hi := by
  simp only [clampAxis]; omega

/-- An offset that is already inside is kept. -/
theorem clampAxis_keep (lo hi a b off : Int) (h1 : lo ≤ a+off) (h2 : b+off ≤ hi) :
    clampAxis lo hi a b off = off := by
  simp only [clampAxis]; omega

/-- The offset of a glyph whose ink box at offset 0 is `ink`, so that its ink lies in
`box`; the offset asked for when it already does. `none` when the ink does not fit. -/
def place (box ink : Box) (dx dy : Int) : Option (Int × Int) :=
  if ink.x1-ink.x0 ≤ box.x1-box.x0 && ink.y1-ink.y0 ≤ box.y1-box.y0 then
    some (clampAxis box.x0 box.x1 ink.x0 ink.x1 dx,clampAxis box.y0 box.y1 ink.y0 ink.y1 dy)
  else none

/-- A placed glyph's ink lies in its box. -/
theorem place_inside (box ink : Box) (dx dy x y : Int) (h : place box ink dx dy = some (x,y)) :
    (ink.shift x y).within box := by
  unfold place at h
  split at h
  · rename_i fits
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    have hx := clampAxis_inside box.x0 box.x1 ink.x0 ink.x1 dx fits.1
    have hy := clampAxis_inside box.y0 box.y1 ink.y0 ink.y1 dy fits.2
    simp only [Box.within, Box.shift]; omega
  · cases h

/-- Ink already in its box is not moved. -/
theorem place_keep (box ink : Box) (dx dy : Int) (h : (ink.shift dx dy).within box) :
    place box ink dx dy = some (dx,dy) := by
  simp only [Box.within, Box.shift] at h
  have f1 : ink.x1-ink.x0 ≤ box.x1-box.x0 := by omega
  have f2 : ink.y1-ink.y0 ≤ box.y1-box.y0 := by omega
  simp only [place, f1, f2, decide_true, Bool.and_self, if_true, Option.some.injEq, Prod.mk.injEq]
  exact ⟨clampAxis_keep _ _ _ _ _ (by omega) (by omega), clampAxis_keep _ _ _ _ _ (by omega) (by omega)⟩

/-- The box of a cluster: its advance box `[x, x+advance]` and the line
`[descender, ascender]`, each widened by `clusterBound`. -/
def clusterBox (unitsPerEm : Nat) (ascender descender x advance : Int) : Box :=
  let b := clusterBound unitsPerEm
  ⟨x-b,descender-b,x+advance+b,ascender+b⟩

end L4Factoidal.Rendering.InkBound
