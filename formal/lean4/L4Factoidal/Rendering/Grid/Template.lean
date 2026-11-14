/-
L4Factoidal.Rendering.Grid.Template — the explicit grid (CSS Grid Layout 2 §7) and the
resolution of grid lines to tracks (§8.3, §8.4).

* Track lists: track sizes, line names and `repeat()` (`TrackList`), expanded to the
  tracks and line names of one axis (`expand`); the number of repetitions of
  `repeat(auto-fill | auto-fit, …)` (`repeatCount`, §7.2.3.2).
* `grid-template-areas`: named areas and the line names they imply (§7.3).
* Grid lines of an item (`Line`: a number, a name, a span) resolved against the lines
  of an axis to a start track and a span (`resolveAxis`), with the conflict rules of
  §8.3.1.
* The sizing function of every track of the implicit grid: the explicit tracks, and
  around them the pattern of `grid-auto-rows` or `grid-auto-columns` (§7.6).

Lengths are whole layout units (1/64 px); percentages are parts per million of the
container; flex factors are in 1/65536 fr (`Grid.Sizing`).

Proved here: an auto-repeat count is at least 1 (`repeatCount_pos`) and the tracks it
gives do not overflow the container when one repetition fits (`repeatCount_fits`); a
definite start and end line give a span of at least 1 (`resolveAxis_span_pos`).
-/
import L4Factoidal.Rendering.Grid.Sizing
import L4Factoidal.Rendering.Grid.Placement

namespace L4Factoidal.Rendering.Grid

/-- A track breadth (§7.2.1): `<length-percentage>` as units plus parts per million of
the container, a flex factor, or a keyword. -/
inductive Breadth where
  | length (units ppm : Nat)
  | fr (factor : Nat)
  | minContent | maxContent | auto
  deriving Repr, BEq, Inhabited

/-- A track size (§7.2.1): a breadth, `minmax(min, max)` or `fit-content(limit)`. -/
inductive TrackSize where
  | breadth (b : Breadth)
  | minmax (min max : Breadth)
  | fitContent (units ppm : Nat)
  deriving Repr, BEq, Inhabited

/-- `units + ppm` of `avail`. -/
def resolveLength (avail units ppm : Nat) : Nat := units + avail * ppm / 1000000

/-- A breadth as a min track sizing function. A percentage of an indefinite size is
`auto` (§7.2.1); a flex factor is not a min sizing function and counts as `auto`. -/
def Breadth.toMin (avail : Option Nat) : Breadth → MinFn
  | .length u ppm =>
    if ppm == 0 then .fixed u
    else match avail with
      | some a => .fixed (resolveLength a u ppm)
      | none => .auto
  | .fr _ => .auto
  | .minContent => .minContent
  | .maxContent => .maxContent
  | .auto => .auto

def Breadth.toMax (avail : Option Nat) : Breadth → MaxFn
  | .length u ppm =>
    if ppm == 0 then .fixed u
    else match avail with
      | some a => .fixed (resolveLength a u ppm)
      | none => .auto
  | .fr f => .fr f
  | .minContent => .minContent
  | .maxContent => .maxContent
  | .auto => .auto

/-- The sizing function of a track in a container whose size in this axis is `avail`
(`none`: indefinite). `Nfr` is `minmax(auto, Nfr)`; `fit-content(L)` is
`minmax(auto, max-content)` clamped by `L`. -/
def TrackSize.toFn (avail : Option Nat) : TrackSize → TrackFn
  | .breadth (.fr f) => ⟨.auto, .fr f⟩
  | .breadth b => ⟨b.toMin avail, b.toMax avail⟩
  | .minmax lo hi => ⟨lo.toMin avail, hi.toMax avail⟩
  | .fitContent u ppm =>
    if ppm == 0 then ⟨.auto, .fitContent u⟩
    else match avail with
      | some a => ⟨.auto, .fitContent (resolveLength a u ppm)⟩
      | none => ⟨.auto, .maxContent⟩

/-- A breadth or track size with a percentage: its sizing functions depend on the size
of the container. -/
def Breadth.hasPercent : Breadth → Bool
  | .length _ ppm => ppm != 0
  | _ => false

def TrackSize.hasPercent : TrackSize → Bool
  | .breadth b => b.hasPercent
  | .minmax lo hi => lo.hasPercent || hi.hasPercent
  | .fitContent _ ppm => ppm != 0

/-- Kind: invariance. Says: a track size with no percentage has the same sizing functions
whatever the container's size, definite or not; so a container need size such tracks
only once. -/
theorem TrackSize.toFn_of_not_hasPercent (t : TrackSize) (h : t.hasPercent = false) (a b : Option Nat) :
    t.toFn a = t.toFn b := by
  cases t with
  | breadth br =>
    cases br <;> simp_all [toFn, Breadth.toMin, Breadth.toMax, hasPercent, Breadth.hasPercent]
  | minmax lo hi =>
    cases lo <;> cases hi <;> simp_all [toFn, Breadth.toMin, Breadth.toMax, hasPercent, Breadth.hasPercent]
  | fitContent u ppm => simp_all [toFn, hasPercent]

/-- The size a track counts for when repetitions are counted (§7.2.3.2): its max sizing
function when that is definite, else its min sizing function when that is definite, else
0. -/
def TrackSize.fixedSize (avail : Option Nat) (t : TrackSize) : Nat :=
  let f := t.toFn avail
  match f.max, f.min with
  | .fixed u, _ => u
  | .fitContent u, _ => u
  | _, .fixed u => u
  | _, _ => 0

/-- How often a `repeat()` repeats. -/
inductive RepeatCount where
  | times (n : Nat) | autoFill | autoFit
  deriving Repr, BEq, Inhabited

/-- A part of a track list or of a `repeat()`: line names, or a track. -/
inductive Part where
  | names (ns : List String)
  | track (t : TrackSize)
  deriving Repr, BEq, Inhabited

inductive Entry where
  | part (p : Part)
  | repeat (count : RepeatCount) (body : List Part)
  deriving Repr, BEq, Inhabited

/-- The value of `grid-template-columns` or `grid-template-rows`: `none` is no entries. -/
structure TrackList where
  entries : List Entry := []
  subgrid : Bool := false
  deriving Repr, BEq, Inhabited

/-- The explicit tracks of one axis: the size of each track, the names of each line
(one more than the tracks), and which tracks come from `repeat(auto-fit, …)`. -/
structure Axis where
  tracks : Array TrackSize := #[]
  names : Array (List String) := #[[]]
  autoFit : Array Bool := #[]
  deriving Repr, Inhabited

/-- The most tracks an axis may have: larger repeat counts stop here. -/
def maxTracks : Nat := 100000

def Axis.addPart (fit : Bool) (a : Axis) : Part → Axis
  | .names ns => {a with names := a.names.modify (a.names.size - 1) (· ++ ns)}
  | .track t =>
    if a.tracks.size ≥ maxTracks then a
    else {a with tracks := a.tracks.push t, names := a.names.push [], autoFit := a.autoFit.push fit}

/-- `body` added `n` times. -/
def Axis.addRepeat (fit : Bool) (body : List Part) : Nat → Axis → Axis
  | 0, a => a
  | n + 1, a => Axis.addRepeat fit body n (body.foldl (Axis.addPart fit) a)

/-- The tracks and line names of a track list, with `auto` repetitions of its
`repeat(auto-fill | auto-fit, …)`. -/
def TrackList.expand (list : TrackList) (auto : Nat) : Axis :=
  list.entries.foldl (fun a e =>
    match e with
    | .part p => a.addPart false p
    | .repeat (.times n) body => Axis.addRepeat false body (min n maxTracks) a
    | .repeat .autoFill body => Axis.addRepeat false body (min auto maxTracks) a
    | .repeat .autoFit body => Axis.addRepeat true body (min auto maxTracks) a) {}

/-- The track list has an automatic repetition. -/
def TrackList.hasAutoRepeat (list : TrackList) : Bool :=
  list.entries.any fun e => match e with
    | .repeat .autoFill _ | .repeat .autoFit _ => true
    | _ => false

/-- §7.2.3.2: the repetitions of an automatic `repeat()` in `avail` units: the most that
do not overflow, and at least one. `otherSum` and `nOther` are the total size and the
number of the tracks outside the repetition; `bodySum` and `nBody` those of one
repetition. A gap separates adjacent tracks. -/
def repeatCount (avail gap otherSum nOther bodySum nBody : Nat) : Nat :=
  max 1 ((avail + gap - otherSum - gap * nOther) / (bodySum + gap * nBody))

/-- Kind: bound. Says: an automatic repetition repeats at least once. -/
theorem repeatCount_pos (avail gap otherSum nOther bodySum nBody : Nat) :
    1 ≤ repeatCount avail gap otherSum nOther bodySum nBody := Nat.le_max_left _ _

/-- Kind: conformance (§7.2.3.2 "the largest possible positive integer that does not
cause the grid to overflow the content box"). Says: when one repetition fits beside the
other tracks, the tracks of all the repetitions, the other tracks and the gaps between
them fit in `avail`: tracks + (tracks − 1) gaps ≤ avail, written with the last gap added
to both sides. Does not say: that one more repetition would overflow (it would: the
count is a whole quotient), or anything when not even one repetition fits (the count is
then 1 and the grid overflows, as the specification says). -/
theorem repeatCount_fits (avail gap otherSum nOther bodySum nBody : Nat)
    (hpos : 0 < bodySum + gap * nBody)
    (hone : bodySum + gap * nBody ≤ avail + gap - otherSum - gap * nOther) :
    otherSum + repeatCount avail gap otherSum nOther bodySum nBody * bodySum +
      gap * (nOther + repeatCount avail gap otherSum nOther bodySum nBody * nBody) ≤ avail + gap := by
  unfold repeatCount
  generalize hX : avail + gap - otherSum - gap * nOther = X at hone
  generalize hper : bodySum + gap * nBody = per at hone hpos
  have hq : 1 ≤ X / per := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  rw [Nat.max_eq_right hq]
  have hmul : X / per * per ≤ X := Nat.div_mul_le_self X per
  have e1 : X / per * per = X / per * bodySum + gap * (X / per * nBody) := by
    rw [← hper, Nat.mul_add, Nat.mul_left_comm]
  have e2 : gap * (nOther + X / per * nBody) = gap * nOther + gap * (X / per * nBody) := Nat.mul_add _ _ _
  omega

/-- The repetitions of the automatic `repeat()` of a track list in a container of
`avail` units (`none`: indefinite, one repetition). -/
def TrackList.autoCount (list : TrackList) (avail : Option Nat) (gap : Nat) : Nat :=
  match avail with
  | none => 1
  | some a =>
    let sizes := fun (body : List Part) => body.filterMap fun p => match p with
      | .track t => some (t.fixedSize avail)
      | .names _ => none
    let (otherSum, nOther, bodySum, nBody) := list.entries.foldl (fun (acc : Nat × Nat × Nat × Nat) e =>
      match e with
      | .part (.track t) => (acc.1 + t.fixedSize avail, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
      | .part (.names _) => acc
      | .repeat (.times n) body =>
        (acc.1 + n * (sizes body).sum, acc.2.1 + n * (sizes body).length, acc.2.2.1, acc.2.2.2)
      | .repeat _ body => (acc.1, acc.2.1, (sizes body).sum, (sizes body).length)) (0, 0, 0, 0)
    if nBody == 0 then 0 else repeatCount a gap otherSum nOther bodySum nBody

/-! ### Named areas (§7.3) -/

structure NamedArea where
  name : String
  area : Area
  deriving Repr, BEq, Inhabited

/-- The named areas of `grid-template-areas`, one list of cell names for each row string
(`.` for a null cell), and the number of columns. `none`: the rows have different
lengths, a row is empty, or an area is not a rectangle (the declaration is invalid). -/
def parseAreas (rows : List (List String)) : Option (List NamedArea × Nat) :=
  match rows with
  | [] => some ([], 0)
  | first :: _ =>
    let cols := first.length
    if cols == 0 || rows.any (·.length != cols) then none
    else
      -- for each name: first row, last row, first column, last column, cells
      let found := rows.zipIdx.foldl (fun (acc : List (String × Nat × Nat × Nat × Nat × Nat)) (row, r) =>
        row.zipIdx.foldl (fun acc (name, c) =>
          if name.all (· == '.') then acc
          else match acc.find? (·.1 == name) with
            | none => acc ++ [(name, r, r, c, c, 1)]
            | some _ => acc.map fun e =>
              if e.1 == name then
                (name, min e.2.1 r, max e.2.2.1 r, min e.2.2.2.1 c, max e.2.2.2.2.1 c, e.2.2.2.2.2 + 1)
              else e) acc) []
      if found.all fun (_, r0, r1, c0, c1, n) => (r1 + 1 - r0) * (c1 + 1 - c0) == n then
        some (found.map fun (name, r0, r1, c0, c1, _) => ⟨name, ⟨r0, r1 + 1 - r0, c0, c1 + 1 - c0⟩⟩, cols)
      else none

/-- The line names of an axis with the names the areas imply (`a-start`, `a-end`), for a
grid of at least `tracks` tracks in the axis. -/
def lineNames (names : Array (List String)) (tracks : Nat) (areas : List NamedArea) (rows : Bool) : Array (List String) :=
  let base := Array.ofFn (n := max names.size (tracks + 1)) fun i => names.getD i.val []
  areas.foldl (fun acc a =>
    let s := if rows then a.area.row else a.area.col
    let e := if rows then a.area.rowEnd else a.area.colEnd
    (acc.modify s (· ++ [a.name ++ "-start"])).modify e (· ++ [a.name ++ "-end"])) base

/-! ### Grid lines (§8.3) -/

/-- The value of `grid-row-start` and its like: `auto`, a line number with an optional
name (`n` is not 0), a span, or a name alone. -/
inductive Line where
  | auto
  | index (n : Int) (name : Option String)
  | span (n : Nat) (name : Option String)
  | ident (name : String)
  deriving Repr, BEq, Inhabited

/-- One side of a placement, resolved: a line (0 is the first line of the explicit grid;
lines of the implicit grid are below 0 or past the last explicit line), a span, or
automatic. -/
inductive Side where
  | line (i : Int)
  | span (n : Nat) (name : Option String)
  | auto
  deriving Repr, BEq, Inhabited

/-- The lines that have `name`, in order. -/
def occurrences (names : Array (List String)) (name : String) : List Nat :=
  (names.toList.zipIdx.filter fun x => x.1.contains name).map (·.2)

/-- The `n`th line (`n` < 0 counts from the end), of the lines named `name` when a name
is given. Past the named lines of the explicit grid, every implicit line has the name
(§8.3, `<integer> && <custom-ident>?`). `tracks` is the number of explicit tracks. -/
def nthLine (names : Array (List String)) (tracks : Nat) (n : Int) (name : Option String) : Int :=
  match name with
  | none => if n > 0 then n - 1 else (tracks : Int) + 1 + n
  | some nm =>
    let occ := occurrences names nm
    if n > 0 then
      match occ[n.toNat - 1]? with
      | some i => (i : Int)
      | none => (tracks : Int) + (n - (occ.length : Int))
    else
      match occ.reverse[(-n).toNat - 1]? with
      | some i => (i : Int)
      | none => n + (occ.length : Int)

def resolveSide (names : Array (List String)) (tracks : Nat) (isEnd : Bool) : Line → Side
  | .auto => .auto
  | .index n name => if n == 0 then .auto else .line (nthLine names tracks n name)
  | .span n name => .span (max 1 n) name
  | .ident name =>
    match (occurrences names (name ++ (if isEnd then "-end" else "-start"))).head? with
    | some i => .line (i : Int)
    | none => .line (nthLine names tracks 1 (some name))

/-- The end line of `span n name` from start line `s`: the `n`th line named `name` after
`s`; past the explicit grid every implicit line has the name. -/
def spanEnd (names : Array (List String)) (tracks : Nat) (s : Int) (n : Nat) (name : String) : Int :=
  let after := (occurrences names name).filter fun (i : Nat) => s < Int.ofNat i
  match after[n - 1]? with
  | some i => (i : Int)
  | none => max (tracks : Int) s + ((n : Int) - (after.length : Int))

/-- The start line of `span n name` back from end line `e`. -/
def spanStart (names : Array (List String)) (e : Int) (n : Nat) (name : String) : Int :=
  let before := ((occurrences names name).filter fun (i : Nat) => Int.ofNat i < e).reverse
  match before[n - 1]? with
  | some i => (i : Int)
  | none => min 0 e - ((n : Int) - (before.length : Int))

/-- The placement of an item in one axis (§8.3 and the conflict rules of §8.3.1): its
start track counted from the first explicit track (below 0: before the explicit grid),
or `none` for an automatic position; and its span. Two definite lines in the wrong order
are exchanged; equal lines give a span of 1; of two spans the end span is dropped; a
span to a name with no definite line is a span of 1. `names` are the lines of the
explicit grid (one more than its tracks). -/
def resolveAxis (names : Array (List String)) (start end_ : Line) : Option Int × Nat :=
  let tracks := names.size - 1
  match resolveSide names tracks false start, resolveSide names tracks true end_ with
  | .line s, .line e =>
    if s < e then (some s, (e - s).toNat) else if e < s then (some e, (s - e).toNat) else (some s, 1)
  | .line s, .span n name =>
    (some s, match name with
      | none => n
      | some nm => max 1 (spanEnd names tracks s n nm - s).toNat)
  | .line s, .auto => (some s, 1)
  | .span n name, .line e =>
    match name with
    | none => (some (e - (n : Int)), n)
    | some nm => (some (spanStart names e n nm), max 1 (e - spanStart names e n nm).toNat)
  | .auto, .line e => (some (e - 1), 1)
  | .span n name, _ => (none, if name.isSome then 1 else n)
  | .auto, .span n name => (none, if name.isSome then 1 else n)
  | .auto, .auto => (none, 1)

/-- Kind: conformance (§8.3.1). Says: when both lines of an item are definite numbers of
lines (no names), the span is at least 1, whatever their order. -/
theorem resolveAxis_span_pos (names : Array (List String)) (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 ≤ (resolveAxis names (.index a none) (.index b none)).2 := by
  simp only [resolveAxis, resolveSide, ha, hb, beq_iff_eq, if_false]
  split
  · omega
  · split
    · omega
    · exact Nat.le_refl _

/-! ### The tracks of the implicit grid (§7.5, §7.6) -/

/-- The size of track `i` of an axis of the implicit grid: `lead` implicit tracks, then
the explicit tracks, then implicit tracks. Implicit tracks take the sizes of
`grid-auto-rows` or `grid-auto-columns` in turn: forwards after the explicit grid, and
backwards before it (the track just before the explicit grid has the last size). -/
def trackAt (explicit : Array TrackSize) (auto : Array TrackSize) (lead i : Nat) : TrackSize :=
  if i < lead then
    if auto.isEmpty then .breadth .auto
    else auto.getD (auto.size - 1 - (lead - 1 - i) % auto.size) (.breadth .auto)
  else if i - lead < explicit.size then explicit.getD (i - lead) (.breadth .auto)
  else if auto.isEmpty then .breadth .auto
  else auto.getD ((i - lead - explicit.size) % auto.size) (.breadth .auto)

/-! ### Examples -/

private def tpx (n : Nat) : TrackSize := .breadth (.length (n * unitsPerPx) 0)

-- repeat(2, [a] 10px) 20px [b]: three tracks, names a | a | (none) | b
#guard (TrackList.expand ⟨[.repeat (.times 2) [.names ["a"], .track (tpx 10)], .part (.track (tpx 20)),
    .part (.names ["b"])], false⟩ 0).names == #[["a"], ["a"], [], ["b"]]
#guard (TrackList.expand ⟨[.repeat (.times 2) [.names ["a"], .track (tpx 10)], .part (.track (tpx 20)),
    .part (.names ["b"])], false⟩ 0).tracks.size == 3
-- repeat(auto-fill, 100px) in 350px with a 10px gap: three columns (330px with gaps)
#guard TrackList.autoCount ⟨[.repeat .autoFill [.track (tpx 100)]], false⟩ (some (350 * unitsPerPx)) (10 * unitsPerPx) == 3
#guard TrackList.autoCount ⟨[.repeat .autoFill [.track (tpx 100)]], false⟩ (some (50 * unitsPerPx)) 0 == 1
#guard TrackList.autoCount ⟨[.repeat .autoFill [.track (tpx 100)]], false⟩ none 0 == 1
#guard TrackList.autoCount ⟨[.part (.track (tpx 50)), .repeat .autoFit [.track (tpx 100)]], false⟩ (some (350 * unitsPerPx)) 0 == 3
-- "a a b" / "c . b"
#guard (parseAreas [["a", "a", "b"], ["c", ".", "b"]]).map (·.1.map fun a => (a.name, a.area.row, a.area.rowSpan, a.area.col, a.area.colSpan)) ==
  some [("a", 0, 1, 0, 2), ("b", 0, 2, 2, 1), ("c", 1, 1, 0, 1)]
#guard (parseAreas [["a", "b"], ["b", "a"]]).isNone
#guard (parseAreas [["a", "b"], ["a"]]).isNone
-- lines: a grid of 4 tracks
private def four : Array (List String) := #[["first"], [], ["mid"], [], ["last"]]
#guard resolveAxis four (.index 2 none) (.index 4 none) == (some 1, 2)
#guard resolveAxis four (.index 4 none) (.index 2 none) == (some 1, 2)
#guard resolveAxis four (.index 2 none) (.index 2 none) == (some 1, 1)
#guard resolveAxis four (.index (-1) none) .auto == (some 4, 1)
#guard resolveAxis four .auto (.index (-1) none) == (some 3, 1)
#guard resolveAxis four (.span 2 none) (.index 3 none) == (some 0, 2)
#guard resolveAxis four (.index 2 none) (.span 3 none) == (some 1, 3)
#guard resolveAxis four (.span 2 none) .auto == (none, 2)
#guard resolveAxis four (.span 2 none) (.span 3 none) == (none, 2)
#guard resolveAxis four (.ident "mid") .auto == (some 2, 1)
#guard resolveAxis four (.ident "first") (.ident "last") == (some 0, 4)
#guard resolveAxis four (.index 2 (some "mid")) .auto == (some 5, 1)
#guard resolveAxis four (.index (-5) none) (.index (-7) none) == (some (-2), 2)
-- an area name: lines a-start and a-end
#guard resolveAxis (lineNames #[[], [], []] 2 [⟨"a", ⟨0, 1, 1, 1⟩⟩] false) (.ident "a") (.ident "a") == (some 1, 1)
-- implicit tracks around two explicit ones, with grid-auto-columns: 10px 20px
#guard (List.range 6).map (fun i => trackAt #[tpx 1, tpx 2] #[tpx 10, tpx 20] 3 i) ==
  [tpx 20, tpx 10, tpx 20, tpx 1, tpx 2, tpx 10]

end L4Factoidal.Rendering.Grid
