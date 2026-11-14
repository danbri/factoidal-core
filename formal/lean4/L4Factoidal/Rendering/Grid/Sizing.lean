/-
L4Factoidal.Rendering.Grid.Sizing — the track sizing algorithm (CSS Grid Layout 2 §12).

Sizes are whole layout units (1/64 px, `Grid.Units`), so sums are exact: no rounding
error can leave a gap or an overflow of a fraction of a unit, and the theorems below are
about the numbers the engine uses, not about an idealised real arithmetic.

One axis at a time. Input: the track sizing functions (`TrackFn`, percentages already
resolved), the gap, the size contributions of the items in this axis (`Contribution`),
the space (`Space`: definite, indefinite, or a min-content or max-content constraint) and
whether auto tracks stretch (§12.8). Output: the used size of every track.

The steps are those of §12.3: initialise (§12.4), resolve intrinsic sizes across
spanning items in span order (§12.5), maximise (§12.6), expand flexible tracks (§12.7),
stretch auto tracks (§12.8). Each step can only raise a track (`raise`), and only the
tracks the step is about.

Proved here:
* the shares of flexible tracks sum to the space they share, exactly (`frRound_sum`,
  `expandFlexible_sum`, `expandFlexible_sum_of_zero_base`);
* each share is proportional to its flex factor, to within one unit (`share_proportional`);
* a track with a fixed min sizing function is at least that size (`sizeTracks_ge_min`);
* a track with fixed min and max sizing functions, min ≤ max, is at most its max
  (`sizeTracks_le_max`);
* one size is answered for each track (`sizeTracks_size`);
* every loop is structural or has a fuel, so the algorithm terminates (Lean accepts the
  definitions as total; no `partial`).
Tested only (`#guard`): the distribution of extra space across spanning items (§12.5.1)
and the sizes of whole examples.
-/
import Std

namespace L4Factoidal.Rendering.Grid

/-- Layout units in one CSS px. -/
def unitsPerPx : Nat := 64

/-- A flex factor of `1fr`. Factors are whole numbers of 1/65536 fr. -/
def frScale : Nat := 65536

/-- A min track sizing function (§7.2.3), with lengths resolved to units. -/
inductive MinFn where
  | fixed (u : Nat) | minContent | maxContent | auto
  deriving Repr, BEq, DecidableEq

/-- A max track sizing function: `fr f` is a flex factor in 1/`frScale`;
`fitContent limit` is `fit-content(limit)`. -/
inductive MaxFn where
  | fixed (u : Nat) | minContent | maxContent | auto | fr (f : Nat) | fitContent (limit : Nat)
  deriving Repr, BEq, DecidableEq

/-- The sizing function of one track. `1fr` is `⟨.auto, .fr frScale⟩`; `fit-content(L)` is
`⟨.auto, .fitContent L⟩`; `100px` is `⟨.fixed 6400, .fixed 6400⟩`. -/
structure TrackFn where
  min : MinFn := .auto
  max : MaxFn := .auto
  deriving Repr, BEq, DecidableEq

instance : Inhabited TrackFn := ⟨{}⟩

def MinFn.isFixed : MinFn → Bool
  | .fixed _ => true | _ => false

def TrackFn.flex (t : TrackFn) : Nat :=
  match t.max with | .fr f => f | _ => 0

def TrackFn.isFlexible (t : TrackFn) : Bool :=
  match t.max with | .fr _ => true | _ => false

def TrackFn.intrinsicMax (t : TrackFn) : Bool :=
  match t.max with | .minContent | .maxContent | .auto | .fitContent _ => true | _ => false

def TrackFn.maxContentMax (t : TrackFn) : Bool :=
  match t.max with | .maxContent | .auto | .fitContent _ => true | _ => false

def TrackFn.autoMax (t : TrackFn) : Bool :=
  match t.max with | .auto => true | _ => false

/-- What one grid item asks of the tracks it spans in this axis (§12.5): its minimum
contribution (the outer size at its automatic minimum size), and its min-content and
max-content contributions. -/
structure Contribution where
  start : Nat
  span : Nat := 1
  minimum : Nat := 0
  minContent : Nat := 0
  maxContent : Nat := 0
  deriving Repr, Inhabited

/-- The space the tracks and gaps of an axis are sized in (§12.3): a definite size, an
indefinite size (an auto block size), or an intrinsic sizing constraint. -/
inductive Space where
  | definite (u : Nat) | indefinite | minContent | maxContent
  deriving Repr, BEq

/-! ### Flexible tracks: the shares of a space (§12.7.1)

A track is a pair `(base, factor)`; factor 0 is an inflexible track. The share of a
flexible track is the difference of two cuts of the space `T`: the cut at the factors
up to and including the track, less the cut at the factors before it. The cuts
telescope, so the shares add up to `T` exactly; each share is within one unit of the
exact proportional part. -/

/-- The size of one track in a round: an inflexible track keeps its base size; a
flexible track takes its share of `T`, and never less than its base size. `F` is the
sum of the factors and `P` the sum of the factors before this track. -/
def roundSize (T F P : Nat) (t : Nat × Nat) : Nat :=
  if t.2 = 0 then t.1 else max t.1 (T * (P + t.2) / F - T * P / F)

/-- The sizes of a round, as a specification (structural, used in proofs only). -/
noncomputable def roundSpec (T F : Nat) : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | P, t :: ts => roundSize T F P t :: roundSpec T F (P + t.2) ts

/-- The sizes of a round, as a loop. -/
def roundGo (T F : Nat) : List (Nat × Nat) → Nat → Array Nat → Array Nat
  | [], _, acc => acc
  | t :: ts, P, acc => roundGo T F ts (P + t.2) (acc.push (roundSize T F P t))

theorem roundGo_eq (T F : Nat) (ts : List (Nat × Nat)) (P : Nat) (acc : Array Nat) :
    (roundGo T F ts P acc).toList = acc.toList ++ roundSpec T F P ts := by
  induction ts generalizing P acc with
  | nil => simp [roundGo, roundSpec]
  | cons t ts ih => simp [roundGo, roundSpec, ih]

theorem roundGo_size (T F : Nat) (ts : List (Nat × Nat)) (P : Nat) (acc : Array Nat) :
    (roundGo T F ts P acc).size = acc.size + ts.length := by
  induction ts generalizing P acc with
  | nil => simp [roundGo]
  | cons t ts ih => simp [roundGo, ih]; omega

/-- Every flexible track's share is at least its base size (§12.7.1 step 4 finds no
track to treat as inflexible). -/
def roundOK (T F : Nat) : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | t :: ts, P =>
    if t.2 = 0 ∨ t.1 ≤ T * (P + t.2) / F - T * P / F then roundOK T F ts (P + t.2) else false

/-- The sum of the base sizes of the inflexible tracks. -/
def inflexSum (ts : List (Nat × Nat)) : Nat := (ts.map fun t => if t.2 = 0 then t.1 else 0).sum

/-- The sum of the flex factors. -/
def flexSum (ts : List (Nat × Nat)) : Nat := (ts.map (·.2)).sum

/-- `inflexSum` and `flexSum` as loops with an accumulator: what runs (`@[csimp]` below),
so a long track list takes no stack. -/
def inflexSumGo : List (Nat × Nat) → Nat → Nat
  | [], acc => acc
  | t :: ts, acc => inflexSumGo ts (acc + if t.2 = 0 then t.1 else 0)

def flexSumGo : List (Nat × Nat) → Nat → Nat
  | [], acc => acc
  | t :: ts, acc => flexSumGo ts (acc + t.2)

def inflexSumLoop (ts : List (Nat × Nat)) : Nat := inflexSumGo ts 0
def flexSumLoop (ts : List (Nat × Nat)) : Nat := flexSumGo ts 0

theorem inflexSumGo_eq (ts : List (Nat × Nat)) (acc : Nat) : inflexSumGo ts acc = acc + inflexSum ts := by
  induction ts generalizing acc with
  | nil => simp [inflexSumGo, inflexSum]
  | cons t ts ih =>
    by_cases h : t.2 = 0
    · simp only [inflexSumGo, if_pos h, ih]
      simp only [inflexSum, List.map_cons, List.sum_cons, if_pos h]; omega
    · simp only [inflexSumGo, if_neg h, ih]
      simp only [inflexSum, List.map_cons, List.sum_cons, if_neg h]; omega

theorem flexSumGo_eq (ts : List (Nat × Nat)) (acc : Nat) : flexSumGo ts acc = acc + flexSum ts := by
  induction ts generalizing acc with
  | nil => simp [flexSumGo, flexSum]
  | cons t ts ih =>
    simp only [flexSumGo, ih]
    simp only [flexSum, List.map_cons, List.sum_cons]; omega

/-- Kind: refinement. Says: the loop computes `inflexSum` (the compiler uses it). -/
@[csimp] theorem inflexSum_eq_loop : @inflexSum = @inflexSumLoop := by
  funext ts; simp [inflexSumLoop, inflexSumGo_eq]

/-- Kind: refinement. Says: the loop computes `flexSum` (the compiler uses it). -/
@[csimp] theorem flexSum_eq_loop : @flexSum = @flexSumLoop := by
  funext ts; simp [flexSumLoop, flexSumGo_eq]

theorem cut_mono (T F P Q : Nat) (h : P ≤ Q) : T * P / F ≤ T * Q / F :=
  Nat.div_le_div_right (Nat.mul_le_mul_left T h)

theorem roundSpec_sum (T F : Nat) (ts : List (Nat × Nat)) (P : Nat) (h : roundOK T F ts P = true) :
    (roundSpec T F P ts).sum = inflexSum ts + (T * (P + flexSum ts) / F - T * P / F) := by
  induction ts generalizing P with
  | nil => simp [roundSpec, inflexSum, flexSum]
  | cons t ts ih =>
    unfold roundOK at h
    split at h
    · rename_i hc
      have ih' := ih (P + t.2) h
      have hf : flexSum (t :: ts) = t.2 + flexSum ts := by simp [flexSum]
      have m1 := cut_mono T F P (P + t.2) (Nat.le_add_right _ _)
      have m2 := cut_mono T F (P + t.2) (P + t.2 + flexSum ts) (Nat.le_add_right _ _)
      have hs : (roundSpec T F P (t :: ts)).sum = roundSize T F P t + (roundSpec T F (P + t.2) ts).sum := by
        simp [roundSpec]
      rw [hs, ih', hf, ← Nat.add_assoc P t.2 (flexSum ts)]
      by_cases hz : t.2 = 0
      · have hi : inflexSum (t :: ts) = t.1 + inflexSum ts := by simp [inflexSum, hz]
        have hr : roundSize T F P t = t.1 := by unfold roundSize; rw [if_pos hz]
        have e1 : P + t.2 = P := by omega
        rw [hr, hi, e1]
        omega
      · have hi : inflexSum (t :: ts) = inflexSum ts := by simp [inflexSum, hz]
        have hle : t.1 ≤ T * (P + t.2) / F - T * P / F := by
          rcases hc with hc | hc
          · exact absurd hc hz
          · exact hc
        have hr : roundSize T F P t = T * (P + t.2) / F - T * P / F := by
          unfold roundSize; rw [if_neg hz]; exact Nat.max_eq_right hle
        rw [hr, hi]
        omega
    · cases h

/-- Kind: arithmetic law. Says: with `F > 0`, a share `s` of `T` for factor `f` (a cut
difference) is within one unit of the exact proportional part `T·f/F`, as
`s·F < T·f + F` and `T·f < s·F + F`. So two tracks with one factor differ by at most
one unit, and a track with twice the factor has twice the share to within the same
bound. Does not say: which of two equal factors gets the extra unit. -/
theorem share_proportional (T F P f : Nat) (hF : 0 < F) :
    (T * (P + f) / F - T * P / F) * F < T * f + F ∧
    T * f < (T * (P + f) / F - T * P / F) * F + F := by
  have ha := Nat.div_add_mod (T * P) F
  have hb := Nat.div_add_mod (T * (P + f)) F
  have ma := Nat.mod_lt (T * P) hF
  have mb := Nat.mod_lt (T * (P + f)) hF
  have hm := cut_mono T F P (P + f) (Nat.le_add_right _ _)
  have hd : T * (P + f) = T * P + T * f := Nat.mul_add T P f
  have hs : (T * (P + f) / F - T * P / F) * F = F * (T * (P + f) / F) - F * (T * P / F) := by
    rw [Nat.mul_comm, Nat.mul_sub]
  have hle : F * (T * P / F) ≤ F * (T * (P + f) / F) := Nat.mul_le_mul_left F hm
  rw [hs]
  omega

/-- The space the flexible tracks share: what the inflexible tracks leave, or, when the
factors add up to less than 1fr, that part of it (§12.7.1 step 2). -/
def frTotal (space : Nat) (ts : List (Nat × Nat)) : Nat :=
  if frScale ≤ flexSum ts then space - inflexSum ts else (space - inflexSum ts) * flexSum ts / frScale

/-- One round of §12.7.1 for the tracks `ts` in `space`. -/
def frRound (space : Nat) (ts : List (Nat × Nat)) : Array Nat :=
  roundGo (frTotal space ts) (flexSum ts) ts 0 #[]

/-- Kind: exact sum. Says: when the flex factors add up to at least 1fr, the inflexible
tracks fit in the space, and no flexible track's share is below its base size
(`roundOK`), the sizes of a round add up to the space exactly. Does not say: anything
when the factors add up to less than 1fr (the tracks then fill only that part of the
space, as §12.7.1 says), or when the inflexible tracks overflow the space. -/
theorem frRound_sum (space : Nat) (ts : List (Nat × Nat))
    (hok : roundOK (frTotal space ts) (flexSum ts) ts 0 = true)
    (hfr : frScale ≤ flexSum ts) (hfit : inflexSum ts ≤ space) :
    (frRound space ts).toList.sum = space := by
  have hF : 0 < flexSum ts := Nat.lt_of_lt_of_le (by decide) hfr
  have hT : frTotal space ts = space - inflexSum ts := by unfold frTotal; rw [if_pos hfr]
  unfold frRound
  rw [roundGo_eq]
  show (roundSpec (frTotal space ts) (flexSum ts) 0 ts).sum = space
  rw [roundSpec_sum _ _ _ _ hok, hT, Nat.zero_add, Nat.mul_zero, Nat.zero_div, Nat.sub_zero,
    Nat.mul_div_cancel _ hF]
  omega

/-- The tracks with every flexible track whose share is below its base size made
inflexible (§12.7.1 step 4: "restart this algorithm treating all such tracks as
inflexible"). -/
def freezeGo (T F : Nat) : List (Nat × Nat) → Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | [], _, acc => acc
  | t :: ts, P, acc =>
    freezeGo T F ts (P + t.2)
      (acc.push (if t.2 ≠ 0 ∧ T * (P + t.2) / F - T * P / F < t.1 then (t.1, 0) else t))

theorem freezeGo_size (T F : Nat) (ts : List (Nat × Nat)) (P : Nat) (acc : Array (Nat × Nat)) :
    (freezeGo T F ts P acc).size = acc.size + ts.length := by
  induction ts generalizing P acc with
  | nil => simp [freezeGo]
  | cons t ts ih => simp [freezeGo, ih]; omega

/-- §12.7.1, "find the size of an fr", and the sizes it gives: rounds until no flexible
track's share is below its base size. Each round that is not the last makes at least one
more track inflexible, so `fuel` = the number of tracks + 1 is enough. -/
def expand : Nat → Nat → List (Nat × Nat) → Array Nat
  | 0, space, ts => frRound space ts
  | fuel + 1, space, ts =>
    if roundOK (frTotal space ts) (flexSum ts) ts 0 then frRound space ts
    else expand fuel space (freezeGo (frTotal space ts) (flexSum ts) ts 0 #[]).toList

/-- The sizes of the tracks `(base, factor)` when the flexible ones are expanded into a
definite `space` (§12.7, definite free space). -/
def expandFlexible (space : Nat) (ts : List (Nat × Nat)) : Array Nat := expand (ts.length + 1) space ts

theorem expand_size (fuel space : Nat) (ts : List (Nat × Nat)) : (expand fuel space ts).size = ts.length := by
  induction fuel generalizing ts with
  | zero => simp [expand, frRound, roundGo_size]
  | succ n ih =>
    unfold expand
    split
    · simp [frRound, roundGo_size]
    · rw [ih]; simp [freezeGo_size]

/-- Kind: totality. Says: one size for each track. -/
theorem expandFlexible_size (space : Nat) (ts : List (Nat × Nat)) :
    (expandFlexible space ts).size = ts.length := expand_size _ _ _

/-- Kind: exact sum (the owner's "track sizes sum to the available space when a flexible
track exists and the space is definite"). Says: when the first round already gives every
flexible track at least its base size, the flex factors add up to at least 1fr and the
inflexible tracks fit, the sizes after expanding flexible tracks add up to the space
exactly. Does not say: the sum when a track is frozen at its base size in an earlier
round (`frRound_sum` then holds of the last round, with that round's tracks), or when
the factors add up to less than 1fr. Gaps are not in `space`: the caller takes them out
first. -/
theorem expandFlexible_sum (space : Nat) (ts : List (Nat × Nat))
    (hok : roundOK (frTotal space ts) (flexSum ts) ts 0 = true)
    (hfr : frScale ≤ flexSum ts) (hfit : inflexSum ts ≤ space) :
    (expandFlexible space ts).toList.sum = space := by
  have he : expandFlexible space ts = frRound space ts := by
    unfold expandFlexible
    simp only [expand, hok, ↓reduceIte]
  rw [he]
  exact frRound_sum space ts hok hfr hfit

theorem roundOK_of_zero_base (T F : Nat) (ts : List (Nat × Nat)) (P : Nat)
    (h : ∀ t ∈ ts, t.2 ≠ 0 → t.1 = 0) : roundOK T F ts P = true := by
  induction ts generalizing P with
  | nil => rfl
  | cons t ts ih =>
    unfold roundOK
    have hc : t.2 = 0 ∨ t.1 ≤ T * (P + t.2) / F - T * P / F := by
      by_cases hz : t.2 = 0
      · exact Or.inl hz
      · right; rw [h t (List.mem_cons_self) hz]; exact Nat.zero_le _
    simp only [hc, if_true]
    exact ih _ (fun u hu => h u (List.mem_cons_of_mem _ hu))

/-- Kind: exact sum, from the input alone. Says: when every flexible track has base size
0 (a track `minmax(0, Nfr)`, or a `Nfr` track whose items have no minimum), the factors
add up to at least 1fr and the inflexible tracks fit in the space, the track sizes add
up to the space exactly. -/
theorem expandFlexible_sum_of_zero_base (space : Nat) (ts : List (Nat × Nat))
    (hz : ∀ t ∈ ts, t.2 ≠ 0 → t.1 = 0) (hfr : frScale ≤ flexSum ts) (hfit : inflexSum ts ≤ space) :
    (expandFlexible space ts).toList.sum = space :=
  expandFlexible_sum space ts (roundOK_of_zero_base _ _ ts 0 hz) hfr hfit

/-- Kind: bound. Says: a round never makes a track smaller than its base size. -/
theorem roundSize_ge (T F P : Nat) (t : Nat × Nat) : t.1 ≤ roundSize T F P t := by
  unfold roundSize
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

/-! ### A step can only raise the tracks it is about -/

/-- The sizes after a step: track `i` becomes the larger of its size `base[i]` and the
step's candidate `cand[i]`, when the step applies to its sizing function (`ok`); else it
is unchanged. With `capFixed`, a track with a fixed max sizing function is not raised
past that max (§12.6: maximising stops at the growth limit). -/
def raise (tracks : Array TrackFn) (ok : TrackFn → Bool) (capFixed : Bool) (base cand : Array Nat) : Array Nat :=
  Array.ofFn (n := base.size) fun i =>
    if ok (tracks.getD i.val default) then
      max base[i] (if capFixed then
          (match (tracks.getD i.val default).max with
           | .fixed m => min (cand.getD i.val 0) (max m base[i])
           | _ => cand.getD i.val 0)
        else cand.getD i.val 0)
    else base[i]

theorem ofFn_getD {n : Nat} (f : Fin n → Nat) (i : Nat) (h : i < n) : (Array.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Array.getD, h]

theorem ofFn_getD_ge {n : Nat} (f : Fin n → Nat) (i : Nat) (h : ¬ i < n) : (Array.ofFn f).getD i 0 = 0 := by
  simp [Array.getD, h]

theorem getD_lt (a : Array Nat) (i : Nat) (h : i < a.size) : a.getD i 0 = a[i] := by
  simp [Array.getD, h]

theorem getD_ge (a : Array Nat) (i : Nat) (h : ¬ i < a.size) : a.getD i 0 = 0 := by
  simp [Array.getD, h]

theorem raise_size (tracks : Array TrackFn) (ok : TrackFn → Bool) (capFixed : Bool) (base cand : Array Nat) :
    (raise tracks ok capFixed base cand).size = base.size := by
  simp [raise]

theorem raise_ge (tracks : Array TrackFn) (ok : TrackFn → Bool) (capFixed : Bool) (base cand : Array Nat) (i : Nat) :
    base.getD i 0 ≤ (raise tracks ok capFixed base cand).getD i 0 := by
  by_cases h : i < base.size
  · unfold raise
    rw [ofFn_getD _ i h, getD_lt base i h]
    show base[i] ≤ if ok (tracks.getD i default) then max base[i] _ else base[i]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  · unfold raise
    rw [ofFn_getD_ge _ i h, getD_ge base i h]
    exact Nat.le_refl _

theorem raise_eq_of_not_ok (tracks : Array TrackFn) (ok : TrackFn → Bool) (capFixed : Bool) (base cand : Array Nat)
    (i : Nat) (hn : ok (tracks.getD i default) = false) :
    (raise tracks ok capFixed base cand).getD i 0 = base.getD i 0 := by
  by_cases h : i < base.size
  · unfold raise
    rw [ofFn_getD _ i h, getD_lt base i h]
    show (if ok (tracks.getD i default) then max base[i] _ else base[i]) = base[i]
    rw [hn]
    rfl
  · unfold raise
    rw [ofFn_getD_ge _ i h, getD_ge base i h]

theorem raise_le_fixed (tracks : Array TrackFn) (ok : TrackFn → Bool) (base cand : Array Nat) (i m : Nat)
    (hm : (tracks.getD i default).max = .fixed m) (hb : base.getD i 0 ≤ m) :
    (raise tracks ok true base cand).getD i 0 ≤ m := by
  by_cases h : i < base.size
  · rw [getD_lt base i h] at hb
    unfold raise
    rw [ofFn_getD _ i h]
    show (if ok (tracks.getD i default) then
        max base[i] (if true = true then
          (match (tracks.getD i default).max with
           | .fixed m => min (cand.getD i 0) (max m base[i])
           | _ => cand.getD i 0)
          else cand.getD i 0)
      else base[i]) ≤ m
    rw [hm]
    split
    · simp only [if_true]
      omega
    · exact hb
  · unfold raise
    rw [ofFn_getD_ge _ i h]
    exact Nat.zero_le _

/-! ### The steps (§12.4 to §12.8): candidates for `raise` -/

/-- §12.4: the base size of a track is its fixed min sizing function, else 0. -/
def initBase (tracks : Array TrackFn) : Array Nat :=
  tracks.map fun t => match t.min with | .fixed u => u | _ => 0

/-- The working sizes of §12.5: base sizes, growth limits where finite, and which growth
limits are infinite. -/
structure Working where
  base : Array Nat
  lim : Array Nat
  inf : Array Bool
  deriving Repr

/-- §12.4: the growth limit of a track is its fixed max sizing function (not below the
base size), else infinite. -/
def initWorking (tracks : Array TrackFn) : Working :=
  let base := initBase tracks
  { base,
    lim := tracks.mapIdx fun i t => match t.max with | .fixed u => max u (base.getD i 0) | _ => 0,
    inf := tracks.map fun t => match t.max with | .fixed _ => false | _ => true }

/-- Shares of `space` for entries `(index, room)`: equal, but none over its room (`none`:
no limit). The entries are taken by room, smallest first; each gets the smaller of its
room and an equal part of what is left (§12.5.1, "distribute space up to limits", with
freezing done by the order). Answers `(index, increase)` for every entry. -/
def distribute (space : Nat) (entries : List (Nat × Option Nat)) : List (Nat × Nat) :=
  let sorted := entries.mergeSort fun a b =>
    match a.2, b.2 with
    | some x, some y => decide (x ≤ y)
    | some _, none => true
    | none, some _ => false
    | none, none => true
  go sorted space sorted.length #[]
where
  go : List (Nat × Option Nat) → Nat → Nat → Array (Nat × Nat) → List (Nat × Nat)
    | [], _, _, acc => acc.toList
    | e :: es, rem, left, acc =>
      let part := rem / max 1 left
      let give := match e.2 with
        | some room => min room part
        | none => part
      go es (rem - give) (left - 1) (acc.push (e.1, give))

/-- The contribution phases of §12.5 step 3, in order. -/
inductive Phase where
  | intrinsicMin | contentMin | maxContentMin | intrinsicMax | maxContentMax
  deriving Repr, BEq

def Phase.isBase : Phase → Bool
  | .intrinsicMin | .contentMin | .maxContentMin => true
  | _ => false

/-- The tracks a phase can grow (§12.5 step 3, the list of each sub-step). Under a
max-content constraint, auto minimums count as max-content minimums. -/
def Phase.affects (p : Phase) (space : Space) (t : TrackFn) : Bool :=
  match p with
  | .intrinsicMin => !t.min.isFixed
  | .contentMin => t.min == .minContent || t.min == .maxContent
  | .maxContentMin => t.min == .maxContent || (t.min == .auto && space == .maxContent)
  | .intrinsicMax => t.intrinsicMax
  | .maxContentMax => t.maxContentMax

/-- The size an item asks for in a phase. Under an intrinsic sizing constraint the
minimum contribution of an item is its min-content contribution (§12.5 step 2, the note
on auto minimums). -/
def Phase.contribution (p : Phase) (space : Space) (c : Contribution) : Nat :=
  match p with
  | .intrinsicMin => if space == .minContent || space == .maxContent then c.minContent else c.minimum
  | .contentMin => c.minContent
  | .maxContentMin => c.maxContent
  | .intrinsicMax => c.minContent
  | .maxContentMax => c.maxContent

/-- §12.5.1 for one item in one phase: the increase the item asks of each track it spans
and the phase affects, as `(track, increase)`. `growable` marks the tracks whose growth
limit became finite in the phase before ("infinitely growable"). With `flexOnly` (§12.5
step 4) only flexible tracks grow, by the ratio of their factors when those add up to at
least 1fr. -/
def itemIncrease (tracks : Array TrackFn) (gap : Nat) (w : Working) (growable : Array Bool)
    (phase : Phase) (space : Space) (flexOnly : Bool) (c : Contribution) : List (Nat × Nat) :=
  let spanned := (List.range' c.start c.span).filter (· < tracks.size)
  let sizeOf := fun (i : Nat) =>
    if phase.isBase || w.inf.getD i true then w.base.getD i 0 else w.lim.getD i 0
  let used := (spanned.map sizeOf).sum + gap * (c.span - 1)
  let extra := phase.contribution space c - used
  let affected := spanned.filter fun i =>
    let t := tracks.getD i default
    phase.affects space t && (!flexOnly || t.isFlexible)
  if affected.isEmpty then []
  else
    let factors := affected.map fun i => (0, (tracks.getD i default).flex)
    if flexOnly && frScale ≤ flexSum factors then
      affected.zip (roundGo extra (flexSum factors) factors 0 #[]).toList
    else
      let room := fun (i : Nat) =>
        if phase.isBase then
          if w.inf.getD i true then
            match (tracks.getD i default).max with
            | .fitContent limit => some (limit - w.base.getD i 0)
            | _ => none
          else some (w.lim.getD i 0 - w.base.getD i 0)
        else if w.inf.getD i true || growable.getD i false then none else some 0
      let first := distribute extra (affected.map fun i => (i, room i))
      let rest := extra - (first.map (·.2)).sum
      if rest == 0 then first
      else
        let preferred := affected.filter fun i =>
          let t := tracks.getD i default
          if phase.isBase then (if phase == .maxContentMin then t.maxContentMax else t.intrinsicMax) else true
        let beyond := distribute rest ((if preferred.isEmpty then affected else preferred).map fun i => (i, none))
        first.map fun (i, d) => (i, d + (beyond.lookup i).getD 0)

/-- One phase for a group of items: the planned increase of every track is the largest
increase any item of the group asks of it; then the sizes grow by it (§12.5.1 steps 3
and 4). Answers the new sizes and the tracks whose growth limit became finite. -/
def runPhase (tracks : Array TrackFn) (gap : Nat) (space : Space) (flexOnly : Bool) (group : Array Contribution)
    (st : Working × Array Bool) (phase : Phase) : Working × Array Bool := Id.run do
  let (w, growable) := st
  let n := tracks.size
  let mut planned : Array (Option Nat) := Array.replicate n none
  for c in group do
    for (i, d) in itemIncrease tracks gap w growable phase space flexOnly c do
      planned := planned.setIfInBounds i (some (max d ((planned.getD i none).getD 0)))
  let mut base := w.base
  let mut lim := w.lim
  let mut inf := w.inf
  let mut grown : Array Bool := Array.replicate n false
  for i in [0:n] do
    match planned.getD i none with
    | none => pure ()
    | some d =>
      if phase.isBase then
        base := base.setIfInBounds i (base.getD i 0 + d)
      else if inf.getD i true then
        lim := lim.setIfInBounds i (base.getD i 0 + d)
        inf := inf.setIfInBounds i false
        if phase == .intrinsicMax then grown := grown.setIfInBounds i true
      else
        lim := lim.setIfInBounds i (lim.getD i 0 + d)
  -- a finite growth limit is never below the base size; fit-content() clamps it
  for i in [0:n] do
    if !inf.getD i true then
      let l := match (tracks.getD i default).max with
        | .fitContent limit => if phase.isBase then lim.getD i 0 else min (lim.getD i 0) limit
        | _ => lim.getD i 0
      lim := lim.setIfInBounds i (max l (base.getD i 0))
  return ({ base, lim, inf }, grown)

/-- The five phases for one group of items. -/
def runGroup (tracks : Array TrackFn) (gap : Nat) (space : Space) (flexOnly : Bool) (w : Working)
    (group : Array Contribution) : Working :=
  ([Phase.intrinsicMin, .contentMin, .maxContentMin, .intrinsicMax, .maxContentMax].foldl
    (runPhase tracks gap space flexOnly group) (w, Array.replicate tracks.size false)).1

/-- An item spans a flexible track. -/
def spansFlexible (tracks : Array TrackFn) (c : Contribution) : Bool :=
  (List.range' c.start c.span).any fun i => (tracks.getD i default).isFlexible

/-- §12.5: the items that span no flexible track, by span (smallest first, each span as
one group); then the items that span a flexible track, as one group that grows flexible
tracks only; then every infinite growth limit becomes the base size. -/
def resolveIntrinsic (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space) : Working := Id.run do
  let rigid := items.filter fun c => !spansFlexible tracks c
  let flexible := items.filter fun c => spansFlexible tracks c
  let spans := (rigid.toList.map (·.span)).eraseDups.mergeSort
  let mut w := initWorking tracks
  for s in spans do
    w := runGroup tracks gap space false w (rigid.filter (·.span == s))
  if !flexible.isEmpty then w := runGroup tracks gap space true w flexible
  return { w with lim := w.lim.mapIdx fun i l => if w.inf.getD i true then w.base.getD i 0 else l,
                  inf := w.inf.map fun _ => false }

/-- §12.6 "maximize tracks": candidates. With a definite space the free space is shared
equally up to the growth limits; with an indefinite space or a max-content constraint
every track grows to its growth limit; with a min-content constraint none grows. -/
def maximizeCand (gap : Nat) (space : Space) (base lim : Array Nat) : Array Nat :=
  match space with
  | .minContent => base
  | .indefinite | .maxContent => lim
  | .definite u =>
    let free := u - gap * (base.size - 1) - base.toList.sum
    let incs := distribute free (base.toList.zipIdx.map fun (b, i) => (i, some (lim.getD i 0 - b)))
    incs.foldl (fun acc (i, d) => acc.setIfInBounds i (acc.getD i 0 + d)) base

/-- §12.7.1 for the tracks `ts` and a space, as a fraction: the size of a factor `f` is
`f · num / den`. Tracks whose share would be below their base size are made inflexible
and the fraction is found again. -/
def findFr (space : Nat) (ts : List (Nat × Nat)) : Nat × Nat :=
  go ts.length ts
where
  go : Nat → List (Nat × Nat) → Nat × Nat
    | 0, ts => (space - inflexSum ts, max (flexSum ts) frScale)
    | fuel + 1, ts =>
      let num := space - inflexSum ts
      let den := max (flexSum ts) frScale
      let frozen := ts.map fun t => if t.2 ≠ 0 ∧ t.2 * num < t.1 * den then (t.1, 0) else t
      if frozen == ts then (num, den) else go fuel frozen

/-- §12.7 with an indefinite space: the fr size is the largest of each flexible track's
base size over its factor (a factor below 1fr counts as 1fr) and, for each item that
spans a flexible track, the fr size that fits its max-content contribution. Candidates:
each flexible track at its factor times that fr size, rounded up. -/
def flexIndefiniteCand (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (base : Array Nat) : Array Nat :=
  let own := (tracks.toList.zipIdx.filter (·.1.isFlexible)).map fun (t, i) => (base.getD i 0, max t.flex frScale)
  let spanning := (items.toList.filter (spansFlexible tracks)).map fun c =>
    findFr (c.maxContent - gap * (c.span - 1))
      (((List.range' c.start c.span).filter (· < tracks.size)).map fun i => (base.getD i 0, (tracks.getD i default).flex))
  let (num, den) := (own ++ spanning).foldl (fun (best : Nat × Nat) (x : Nat × Nat) =>
    if best.1 * x.2 < x.1 * best.2 then x else best) (0, 1)
  tracks.mapIdx fun i t => if t.isFlexible then (t.flex * num + den - 1) / den else base.getD i 0

/-- §12.7 "expand flexible tracks": candidates. -/
def flexCand (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space) (base : Array Nat) : Array Nat :=
  if !tracks.any (·.isFlexible) then base
  else match space with
    | .minContent => base
    | .definite u =>
      expandFlexible (u - gap * (base.size - 1)) (base.toList.zipIdx.map fun (b, i) => (b, (tracks.getD i default).flex))
    | .indefinite | .maxContent => flexIndefiniteCand tracks gap items base

/-- §12.8 "stretch auto tracks": candidates. With a definite space and positive free
space, the tracks with an `auto` max sizing function share the free space equally (the
first tracks take the units a whole division leaves). -/
def stretchCand (tracks : Array TrackFn) (gap : Nat) (space : Space) (stretch : Bool) (base : Array Nat) : Array Nat :=
  match space, stretch with
  | .definite u, true =>
    let free := u - gap * (base.size - 1) - base.toList.sum
    let count := (tracks.toList.filter (·.autoMax)).length
    if free == 0 || count == 0 then base
    else
      (tracks.toList.zipIdx.foldl (fun (acc : Array Nat × Nat) (t, i) =>
        if t.autoMax then
          (acc.1.push (base.getD i 0 + free / count + (if acc.2 < free % count then 1 else 0)), acc.2 + 1)
        else (acc.1.push (base.getD i 0), acc.2)) (#[], 0)).1
  | _, _ => base

/-- §12.3, the track sizing algorithm for one axis: the used size of every track. -/
def sizeTracks (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space) (stretch : Bool) : Array Nat :=
  let w := resolveIntrinsic tracks gap items space
  let b1 := raise tracks (fun t => !t.min.isFixed) false (initBase tracks) w.base
  let b2 := raise tracks (fun _ => true) true b1 (maximizeCand gap space b1 w.lim)
  let b3 := raise tracks (·.isFlexible) false b2 (flexCand tracks gap items space b2)
  raise tracks (·.autoMax) false b3 (stretchCand tracks gap space stretch b3)

/-- Kind: totality. Says: one size for each track. -/
theorem sizeTracks_size (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space) (stretch : Bool) :
    (sizeTracks tracks gap items space stretch).size = tracks.size := by
  simp [sizeTracks, raise_size, initBase]

theorem initBase_fixed (tracks : Array TrackFn) (i u : Nat) (h : (tracks.getD i default).min = .fixed u) :
    (initBase tracks).getD i 0 = u := by
  by_cases hi : i < tracks.size
  · have ht : tracks.getD i default = tracks[i] := by simp [Array.getD, hi]
    rw [ht] at h
    simp [initBase, Array.getD, hi, h]
  · have ht : tracks.getD i default = default := by simp [Array.getD, hi]
    rw [ht] at h
    have hd : (default : TrackFn).min = MinFn.auto := rfl
    rw [hd] at h
    cases h

/-- Kind: conformance bound (§12.4: the base size starts at a fixed min sizing function,
and no later step lowers it). Says: a track whose min sizing function is a length (after
percentages are resolved) is at least that long. Does not say: anything of a track with
an intrinsic min sizing function. -/
theorem sizeTracks_ge_min (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space)
    (stretch : Bool) (i u : Nat) (h : (tracks.getD i default).min = .fixed u) :
    u ≤ (sizeTracks tracks gap items space stretch).getD i 0 := by
  simp only [sizeTracks]
  have h0 := initBase_fixed tracks i u h
  refine Nat.le_trans ?_ (raise_ge _ _ _ _ _ i)
  refine Nat.le_trans ?_ (raise_ge _ _ _ _ _ i)
  refine Nat.le_trans ?_ (raise_ge _ _ _ _ _ i)
  refine Nat.le_trans ?_ (raise_ge _ _ _ _ _ i)
  rw [h0]; exact Nat.le_refl _

/-- Kind: conformance bound (§12.4 and §12.6: a growth limit that is a length stops the
track). Says: a track with both sizing functions fixed, min ≤ max, is at most its max.
With `sizeTracks_ge_min`: such a track lies between its min and its max. Does not say:
this of a track with an intrinsic or flexible sizing function, or with min > max (the
max is then floored by the min, §7.2.3). -/
theorem sizeTracks_le_max (tracks : Array TrackFn) (gap : Nat) (items : Array Contribution) (space : Space)
    (stretch : Bool) (i u v : Nat) (hmin : (tracks.getD i default).min = .fixed u)
    (hmax : (tracks.getD i default).max = .fixed v) (huv : u ≤ v) :
    (sizeTracks tracks gap items space stretch).getD i 0 ≤ v := by
  simp only [sizeTracks]
  have h0 := initBase_fixed tracks i u hmin
  have e4 : ∀ b c, (raise tracks (fun t => t.autoMax) false b c).getD i 0 = b.getD i 0 :=
    fun b c => raise_eq_of_not_ok _ _ _ _ _ i
      (by show TrackFn.autoMax (tracks.getD i default) = false; unfold TrackFn.autoMax; rw [hmax])
  have e3 : ∀ b c, (raise tracks (fun t => t.isFlexible) false b c).getD i 0 = b.getD i 0 :=
    fun b c => raise_eq_of_not_ok _ _ _ _ _ i
      (by show TrackFn.isFlexible (tracks.getD i default) = false; unfold TrackFn.isFlexible; rw [hmax])
  have e1 : ∀ b c, (raise tracks (fun t => !t.min.isFixed) false b c).getD i 0 = b.getD i 0 :=
    fun b c => raise_eq_of_not_ok _ _ _ _ _ i
      (by show (!(tracks.getD i default).min.isFixed) = false; rw [hmin]; rfl)
  rw [e4, e3]
  apply raise_le_fixed _ _ _ _ i v hmax
  rw [e1, h0]
  exact huv

/-! ### Examples -/

private def px (n : Nat) : Nat := n * unitsPerPx
private def fixed (n : Nat) : TrackFn := ⟨.fixed (px n), .fixed (px n)⟩
private def fr (n : Nat) : TrackFn := ⟨.auto, .fr (n * frScale)⟩
private def inPx (a : Array Nat) : List Nat := a.toList.map (· / unitsPerPx)

-- fixed tracks keep their sizes
#guard inPx (sizeTracks #[fixed 50, fixed 100, fixed 150] 0 #[] (.definite (px 500)) true) == [50, 100, 150]
-- 1fr 2fr in 300px; with a 100px track; with a gap
#guard inPx (sizeTracks #[fr 1, fr 2] 0 #[] (.definite (px 300)) true) == [100, 200]
#guard inPx (sizeTracks #[fixed 100, fr 1, fr 1] 0 #[] (.definite (px 300)) true) == [100, 100, 100]
#guard inPx (sizeTracks #[fr 1, fr 1] (px 20) #[] (.definite (px 300)) true) == [140, 140]
-- three 1fr tracks in 100px: the units add up to the space exactly
#guard (sizeTracks #[fr 1, fr 1, fr 1] 0 #[] (.definite (px 100)) true).toList.sum == px 100
-- auto tracks: content, then stretch into a definite space
#guard inPx (sizeTracks #[{}, {}] 0 #[⟨0, 1, px 30, px 30, px 60⟩, ⟨1, 1, px 10, px 10, px 20⟩] .indefinite true) == [60, 20]
#guard inPx (sizeTracks #[{}, {}] 0 #[⟨0, 1, px 30, px 30, px 60⟩, ⟨1, 1, px 10, px 10, px 20⟩] (.definite (px 200)) true) == [120, 80]
#guard inPx (sizeTracks #[{}, {}] 0 #[⟨0, 1, px 30, px 30, px 60⟩, ⟨1, 1, px 10, px 10, px 20⟩] (.definite (px 200)) false) == [60, 20]
-- min-content and max-content tracks
#guard inPx (sizeTracks #[⟨.minContent, .minContent⟩, ⟨.maxContent, .maxContent⟩] 0
    #[⟨0, 1, px 30, px 30, px 60⟩, ⟨1, 1, px 10, px 10, px 20⟩] (.definite (px 200)) true) == [30, 20]
-- an item spanning two auto tracks: the extra space is shared equally
#guard inPx (sizeTracks #[{}, {}] 0 #[⟨0, 2, px 100, px 100, px 100⟩] .indefinite true) == [50, 50]
-- a flexible track with a content minimum is frozen at it; the other takes the rest
#guard inPx (sizeTracks #[fr 1, fr 1] 0 #[⟨0, 1, px 200, px 200, px 200⟩] (.definite (px 300)) true) == [200, 100]
-- fr tracks in an indefinite space take the size of their content
#guard inPx (sizeTracks #[fr 1, fr 2] 0 #[⟨0, 1, px 50, px 50, px 50⟩] .indefinite true) == [50, 100]
-- fit-content(100px): content up to the limit
#guard inPx (sizeTracks #[⟨.auto, .fitContent (px 100)⟩] 0 #[⟨0, 1, px 30, px 30, px 300⟩] (.definite (px 500)) true) == [100]
#guard inPx (sizeTracks #[⟨.auto, .fitContent (px 100)⟩] 0 #[⟨0, 1, px 30, px 30, px 60⟩] (.definite (px 500)) true) == [60]
-- minmax(50px, 100px) grows to its max in free space, and stays at its min without
#guard inPx (sizeTracks #[⟨.fixed (px 50), .fixed (px 100)⟩] 0 #[] (.definite (px 500)) true) == [100]
#guard inPx (sizeTracks #[⟨.fixed (px 50), .fixed (px 100)⟩] 0 #[] (.definite (px 70)) true) == [70]

end L4Factoidal.Rendering.Grid
