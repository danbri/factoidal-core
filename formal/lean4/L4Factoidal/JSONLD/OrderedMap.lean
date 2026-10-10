/-
L4Factoidal.JSONLD.OrderedMap — a finite map keyed by `String` that
remembers the order in which keys were first inserted.

It is the representation behind the JSON-LD node map (API §7.1): a node's
entries must come out in first-creation order (the flattened output shows
that order as the order of the object's members), while lookup and update
must not scan. The structure is PERSISTENT — an update shares everything
it does not change — so it is correct and fast whether or not the old
value is still referenced. A mutable `Array` or `HashMap` would copy its
whole bucket array on every update made through a shared reference.

Representation: a `Std.TreeMap` from key to value (lookup, insert, and a
traversal in key order, all logarithmic or linear), and `rev`, the keys in
reverse order of first insertion (`cons` is constant time). The
well-formedness condition `OMap.WF` says `rev` lists exactly the keys of
`tab`, each once; `NodeMapTheorems.lean` proves every operation preserves
it and that the operations agree with the association-list functions
`flLookup` and `flUpd` they replaced.
-/
import Std.Data.TreeMap
import Std.Data.TreeSet

namespace L4Factoidal.JSONLD

/-- Insertion-ordered finite map from `String` keys to `α`. -/
structure OMap (α : Type) where
  /-- The keys, most recently inserted first. -/
  rev : List String
  /-- The key-to-value table (`compare` on `String`: code-point order). -/
  tab : Std.TreeMap String α

namespace OMap

variable {α : Type}

def empty : OMap α := { rev := [], tab := Std.TreeMap.empty }

instance : EmptyCollection (OMap α) := ⟨empty⟩

/-- The value under `k`. -/
def find? (m : OMap α) (k : String) : Option α := m.tab.get? k

def contains (m : OMap α) (k : String) : Bool := m.tab.contains k

def size (m : OMap α) : Nat := m.tab.size

/-- Replace the value under `k` in place (the key keeps its position), or
append a new key at the end of the insertion order. -/
def upsert (m : OMap α) (k : String) (v : α) : OMap α :=
  if m.tab.contains k then { m with tab := m.tab.insert k v }
  else { rev := k :: m.rev, tab := m.tab.insert k v }

/-- The entries in order of first insertion. -/
def toList (m : OMap α) : List (String × α) :=
  m.rev.reverse.filterMap (fun k => (m.tab.get? k).map (fun v => (k, v)))

/-- The entries in code-point order of their keys. -/
def toSortedList (m : OMap α) : List (String × α) := m.tab.toList

/-- Well-formedness: `rev` lists each key of `tab` exactly once. -/
def WF (m : OMap α) : Prop :=
  m.rev.Nodup ∧ ∀ k, k ∈ m.rev ↔ m.tab.contains k = true

end OMap

end L4Factoidal.JSONLD
