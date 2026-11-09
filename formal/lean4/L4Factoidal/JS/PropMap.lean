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
  /-- Keys and values, for a small map. Unused when `big` is set. -/
  ks : Array String := #[]
  vs : Array V := #[]
  big : Option (Std.HashMap String V) := none
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

@[inline] def get? (m : PropMap V) (k : String) : Option V :=
  match m.big with
  | some b => b.get? k
  | none =>
    let i := scan m.ks k 0
    if i == m.ks.size then none else m.vs[i]?

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
  | some b => { m with big := some (b.insert k v) }
  | none =>
    let i := scan m.ks k 0
    if i != m.ks.size then { m with vs := m.vs.set! i v }
    else
      if m.ks.size < smallMax then
        { m with ks := m.ks.push k, vs := m.vs.push v }
      else
        let b : Std.HashMap String V := Std.HashMap.emptyWithCapacity (2 * smallMax)
        let b := (m.ks.zip m.vs).foldl (fun b (k, v) => b.insert k v) b
        { ks := #[], vs := #[], big := some (b.insert k v) }

def erase [Inhabited V] (m : PropMap V) (k : String) : PropMap V :=
  match m.big with
  | some b => { m with big := some (b.erase k) }
  | none =>
    let i := scan m.ks k 0
    if i != m.ks.size then
      -- the keys' order is kept by the owner (`Obj.keys`), so the last pair moves into the hole
      let last := m.ks.size - 1
      if i == last then { m with ks := m.ks.pop, vs := m.vs.pop }
      else { m with ks := (m.ks.set! i m.ks[last]!).pop, vs := (m.vs.set! i m.vs[last]!).pop }
    else m

/-- The pairs, in no particular order. -/
def toList (m : PropMap V) : List (String × V) :=
  match m.big with
  | some b => b.toList
  | none => (m.ks.zip m.vs).toList

def fold {β : Type} (f : β → String → V → β) (init : β) (m : PropMap V) : β :=
  match m.big with
  | some b => b.fold f init
  | none => (m.ks.zip m.vs).foldl (fun acc (k, v) => f acc k v) init

/-- The map with every value changed by `f`. -/
def mapValues (f : V → V) (m : PropMap V) : PropMap V :=
  match m.big with
  | some b => { m with big := some (b.fold (fun acc k v => acc.insert k (f v)) {}) }
  | none => { m with vs := m.vs.map f }

end PropMap

end L4Factoidal.JS
