import Std.Data.HashMap

/-!
# L4Factoidal.JS.PropMap — own properties of an object

A map from property key to value, with the operations of the `Std.HashMap` it replaces.
Most objects have few properties, and a key is usually the same `String` object as the name
in the program text (identifiers are interned at parse time, `Parser.internToks`), so a scan of
a short key array compared by pointer first beats hashing the key on every access. A map with
more than `smallMax` keys is a `Std.HashMap`.

`PropMap.get?` is defined by the representation; `Tests.lean` checks it against the
association-list reading of the map (`toList`) on a mix of insertions and erasures.
-/

namespace L4Factoidal.JS

structure PropMap (V : Type) where
  /-- Keys and values, in slots. A key that was erased from a big map stays here as a
  tombstone (`big` no longer maps it); the keys' order is kept by the owner (`Obj.keys`). -/
  ks : Array String := #[]
  vs : Array V := #[]
  /-- With more than `smallMax` keys: the slot of each key. -/
  big : Option (Std.HashMap String Nat) := none
  deriving Inhabited

namespace PropMap
variable {V : Type}

/-- The most keys a small map holds. -/
def smallMax : Nat := 8

/-- The index of `k` in the small keys, scanning from `i`; `ks.size` when absent. Returns a
plain number: no `some` is allocated for a hit. -/
def scan (ks : Array String) (k : String) (i : Nat) : Nat :=
  if h : i < ks.size then
    if ks[i] == k then i else scan ks k (i + 1)
  else ks.size
termination_by ks.size - i
decreasing_by simp_wf; omega

/-- The slot of `k`, or `none`. -/
@[inline] def slot? (m : PropMap V) (k : String) : Option Nat :=
  match m.big with
  | some b => b.get? k
  | none =>
    let i := scan m.ks k 0
    if i == m.ks.size then none else some i

@[inline] def get? (m : PropMap V) (k : String) : Option V :=
  match m.big with
  | some b => match b.get? k with
    | some i => m.vs[i]?
    | none => none
  | none =>
    let i := scan m.ks k 0
    if i == m.ks.size then none else m.vs[i]?

/-- Whether slot `i` is the live slot of key `k`. In a big map an erased key stays in `ks` as a
tombstone (`erase`), so finding `k` at `ks[i]` is not enough: the hash map must still send `k`
to `i`. A small map has no tombstones. For a cache that remembers a slot (`vmGlobalHit`). -/
@[inline] def liveAt (m : PropMap V) (i : Nat) (k : String) : Bool :=
  match m.big with
  | some b => b.getD k m.ks.size == i
  | none => true

def contains (m : PropMap V) (k : String) : Bool :=
  match m.big with
  | some b => b.contains k
  | none => scan m.ks k 0 != m.ks.size

def size (m : PropMap V) : Nat :=
  match m.big with
  | some b => b.size
  | none => m.ks.size

def insert (m : PropMap V) (k : String) (v : V) : PropMap V :=
  match m.big with
  | some b =>
    match b.get? k with
    | some i => { m with vs := m.vs.set! i v }
    | none =>
      let i := m.ks.size
      { ks := m.ks.push k, vs := m.vs.push v, big := some (b.insert k i) }
  | none =>
    let i := scan m.ks k 0
    if i != m.ks.size then { m with vs := m.vs.set! i v }
    else
      if m.ks.size < smallMax then
        { m with ks := m.ks.push k, vs := m.vs.push v }
      else
        let ks := m.ks.push k
        let b : Std.HashMap String Nat :=
          (ks.zipIdx).foldl (fun b (k, i) => b.insert k i) (Std.HashMap.emptyWithCapacity (2 * smallMax))
        { ks, vs := m.vs.push v, big := some b }

def erase [Inhabited V] (m : PropMap V) (k : String) : PropMap V :=
  match m.big with
  | some b => { m with big := some (b.erase k) }   -- the slot stays as a tombstone
  | none =>
    let i := scan m.ks k 0
    if i != m.ks.size then
      -- the keys' order is kept by the owner (`Obj.keys`), so the last pair moves into the hole
      let last := m.ks.size - 1
      if i == last then { m with ks := m.ks.pop, vs := m.vs.pop }
      else { m with ks := (m.ks.set! i m.ks[last]!).pop, vs := (m.vs.set! i m.vs[last]!).pop }
    else m

/-! ## Lookups in a big map with no `Option` cell

`Std.HashMap.get?` makes a `some` for every hit (its bucket lookup is not inlined), and a property
read of an object with more than `smallMax` keys (a prototype with many methods, the global object)
is such a hit. `getD` with a number that is no slot answers the same question with no cell. The
definitions above stay the reference; the compiled program runs these (`@[csimp]`). -/

theorem getD_eq_get?_getD (b : Std.HashMap String Nat) (k : String) (d : Nat) :
    b.getD k d = (b.get? k).getD d := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getD_eq_getD_getElem?]

theorem contains_eq_get?_isSome (b : Std.HashMap String Nat) (k : String) :
    b.contains k = (b.get? k).isSome := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.contains_eq_isSome_getElem?]

/-- `get?`: an absent key reads slot `vs.size`, which is no slot. -/
@[inline] def getFast? (m : PropMap V) (k : String) : Option V :=
  match m.big with
  | some b => m.vs[b.getD k m.vs.size]?
  | none =>
    let i := scan m.ks k 0
    if i == m.ks.size then none else m.vs[i]?

/-- **Kind: refinement.** `getFast?` answers as `get?` for every map and key (no invariant of the
map is assumed). Does not say anything about speed. -/
@[csimp] theorem get?_eq_fast : @get? = @getFast? := by
  funext V m k
  unfold get? getFast?
  cases hb : m.big with
  | none => rfl
  | some b =>
    simp only [getD_eq_get?_getD]
    cases b.get? k with
    | none => simp
    | some i => rfl

/-- `slot?`: the slot by `getD` with `ks.size` for "absent"; only when the answer is that very
number is the map asked whether it holds the key. -/
@[inline] def slotFast? (m : PropMap V) (k : String) : Option Nat :=
  match m.big with
  | some b =>
    let i := b.getD k m.ks.size
    if i != m.ks.size then some i else if b.contains k then some i else none
  | none =>
    let i := scan m.ks k 0
    if i == m.ks.size then none else some i

/-- **Kind: refinement.** `slotFast?` answers as `slot?` for every map and key. -/
@[csimp] theorem slot?_eq_fast : @slot? = @slotFast? := by
  funext V m k
  unfold slot? slotFast?
  cases hb : m.big with
  | none => rfl
  | some b =>
    simp only [getD_eq_get?_getD, contains_eq_get?_isSome]
    cases h : b.get? k with
    | none => simp
    | some i => simp

/-- `insert`, with the lookup of the big map as in `slotFast?`. -/
def insertFast (m : PropMap V) (k : String) (v : V) : PropMap V :=
  match m.big with
  | some b =>
    let i := b.getD k m.ks.size
    if i != m.ks.size || b.contains k then { m with vs := m.vs.set! i v }
    else
      let i := m.ks.size
      { ks := m.ks.push k, vs := m.vs.push v, big := some (b.insert k i) }
  | none =>
    let i := scan m.ks k 0
    if i != m.ks.size then { m with vs := m.vs.set! i v }
    else
      if m.ks.size < smallMax then
        { m with ks := m.ks.push k, vs := m.vs.push v }
      else
        let ks := m.ks.push k
        let b : Std.HashMap String Nat :=
          (ks.zipIdx).foldl (fun b (k, i) => b.insert k i) (Std.HashMap.emptyWithCapacity (2 * smallMax))
        { ks, vs := m.vs.push v, big := some b }

/-- **Kind: refinement.** `insertFast` gives the map `insert` gives, for every map, key and value. -/
@[csimp] theorem insert_eq_fast : @insert = @insertFast := by
  funext V m k v
  unfold insert insertFast
  cases hb : m.big with
  | none => rfl
  | some b =>
    simp only [getD_eq_get?_getD, contains_eq_get?_isSome]
    cases h : b.get? k with
    | none => simp
    | some i => simp

#print axioms get?_eq_fast
#print axioms slot?_eq_fast
#print axioms insert_eq_fast

/-! ## A remembered slot

A cache that remembers the slot of a key (the register machine's global name cache,
`vmGlobalHit`; an inline cache for property reads) reads `vs[i]` where `get?` would look the key
up. These say when that is the same answer. -/

/-- `scan` from `s` stops at `i` when `ks[i]` is `k` and no slot from `s` to `i` before it is. -/
theorem scan_eq_first (ks : Array String) (k : String) (i : Nat) (hi : i < ks.size)
    (hk : ks[i] = k) (hfirst : ∀ j (hj : j < i), ks[j]'(by omega) ≠ k) :
    ∀ d s, i - s = d → s ≤ i → scan ks k s = i := by
  intro d
  induction d with
  | zero =>
    intro s hd hs
    have he : s = i := by omega
    subst he
    rw [scan]
    simp [hi, hk]
  | succ d ih =>
    intro s hd hs
    have hs' : s < ks.size := by omega
    have hne : ks[s] ≠ k := hfirst s (by omega)
    rw [scan]
    simp only [hs', dite_true, beq_iff_eq, hne, ite_false]
    exact ih (s + 1) (by omega) (by omega)

/-- **Kind: lemma for a cache guard.**

Says: if slot `i` holds key `k`, `liveAt i k` holds, and (in a small map) no slot before `i`
holds `k`, then `get? k` is the value in slot `i`. For a big map no further assumption is needed:
an erased key left in `ks` as a tombstone fails `liveAt`.

Does not say: that a cache which remembers `i` stays right after the map changes; the guard is
checked at each use for that reason. -/
theorem get?_of_slot (m : PropMap V) (i : Nat) (k : String)
    (hk : m.ks[i]? = some k) (hl : m.liveAt i k = true)
    (hfirst : m.big = none → ∀ j, j < i → m.ks[j]? ≠ some k) :
    m.get? k = m.vs[i]? := by
  have hi : i < m.ks.size := by
    rcases Nat.lt_or_ge i m.ks.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hk
  have hk' : m.ks[i] = k := by
    rw [Array.getElem?_eq_getElem hi] at hk
    exact Option.some.inj hk
  unfold get?
  unfold liveAt at hl
  cases hb : m.big with
  | some b =>
    simp only [hb] at hl ⊢
    rw [getD_eq_get?_getD] at hl
    cases hg : b.get? k with
    | none =>
      simp only [hg, Option.getD_none, beq_iff_eq] at hl
      omega
    | some j =>
      simp only [hg, Option.getD_some, beq_iff_eq] at hl
      subst hl
      rfl
  | none =>
    simp only
    have hf := hfirst hb
    have hsc : scan m.ks k 0 = i :=
      scan_eq_first m.ks k i hi hk' (fun j hj h => hf j hj (by
        rw [Array.getElem?_eq_getElem (by omega)]; exact congrArg some h)) (i - 0) 0 rfl (Nat.zero_le _)
    rw [hsc]
    have hne : (i == m.ks.size) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    rw [hne]
    rfl

#print axioms get?_of_slot

/-- The pairs, in no particular order. -/
def toList (m : PropMap V) : List (String × V) :=
  match m.big with
  | some b => b.toList.filterMap fun (k, i) => (m.vs[i]?).map (k, ·)
  | none => (m.ks.zip m.vs).toList

def fold {β : Type} (f : β → String → V → β) (init : β) (m : PropMap V) : β :=
  m.toList.foldl (fun acc (k, v) => f acc k v) init

/-- The map with every value changed by `f`. -/
def mapValues (f : V → V) (m : PropMap V) : PropMap V :=
  { m with vs := m.vs.map f }

end PropMap

end L4Factoidal.JS
