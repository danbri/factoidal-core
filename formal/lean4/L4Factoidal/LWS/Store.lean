/-
L4Factoidal.LWS.Store — the abstract resource store, its laws, and the
reference in-memory instance.

The Linked Web Storage Protocol 1.0 Core draft
(https://w3c.github.io/lws-protocol/lws10-core/) names the operations —
"An operation is any of the following actions that can be performed on a
served resource: create resource, read resource, update resource, delete
resource" — and leaves their section bodies empty. What a backend must
provide is therefore stated here as a structure of pure functions over an
abstract state, and what it must SATISFY is stated as `Prop` fields beside
it. `L4Factoidal.LWS.Operations.step` is written against the structure, so
any backend that satisfies the laws answers the same responses.

`MemStore` is the reference instance: a list of entries, first match wins,
with `put` replacing any entry at the same path. `memStoreLaws` proves it
satisfies every law. It is the instance the wasm operations run.
-/
import L4Factoidal.LWS.Model
import Std.Data.TreeMap

namespace L4Factoidal.LWS

open L4Factoidal.RDF

/-! ## The abstract store -/

/-- The operations a backend provides over its own state type `σ`.

`now` and `tick` carry the clock. `now` is the time a mutation stamps into
`Entry.mtime`; `tick` advances it. Neither reads a real clock: a host that
has one sets the state's clock through `L4Factoidal.LWS.Operations`. -/
structure Store (σ : Type) where
  lookup : σ → String → Option Entry
  put    : σ → Entry → σ
  remove : σ → String → σ
  paths  : σ → List String
  now    : σ → Nat
  tick   : σ → σ

/-- The laws every backend must satisfy for `Operations.step` to answer what
the specification says it answers.

* `lookupPutSame` — a write is readable at the path it was written to.
* `lookupPutOther` — a write is invisible at every other path. Without it a
  PUT could change a sibling resource, and the containment correspondence of
  Solid Protocol §4.2 would not hold.
* `lookupRemoveSame` — a delete is a delete.
* `lookupRemoveOther` — a delete touches nothing else. This is the law the
  auxiliary-resource lifecycle of §4.3 needs: deleting a subject resource
  deletes its auxiliaries and nothing besides.
* `pathsLookup` — `paths` enumerates exactly the paths that resolve, which
  is what a container enumerating its members reads.
* `nowTick` — `tick` advances the clock by one, so two writes inside one
  request never carry the same `Last-Modified`. A host with a real clock
  resets the clock before each request, so across requests it can repeat
  (https://github.com/danbri/factoidal/issues/911).
* `lookupTick` — advancing the clock changes no resource. The move theorems
  of `L4Factoidal.LWS.Move` need it (a move stamps the two containers and
  advances the clock between the stamps), and so does the type index
  (`L4Factoidal.LWS.TypeIndex`), whose invariant is stated over `lookup`
  (https://github.com/danbri/factoidal/issues/912).
* `lookupPath` — an entry is found at its own path. -/
structure StoreLaws {σ : Type} (S : Store σ) : Prop where
  lookupPutSame   : ∀ s e, S.lookup (S.put s e) e.path = some e
  lookupPutOther  : ∀ s e p, p ≠ e.path → S.lookup (S.put s e) p = S.lookup s p
  lookupRemoveSame : ∀ s p, S.lookup (S.remove s p) p = none
  lookupRemoveOther : ∀ s p q, q ≠ p → S.lookup (S.remove s p) q = S.lookup s q
  pathsLookup     : ∀ s p, (S.paths s).contains p = (S.lookup s p).isSome
  nowTick         : ∀ s, S.now (S.tick s) = S.now s + 1
  lookupTick      : ∀ s p, S.lookup (S.tick s) p = S.lookup s p
  lookupPath      : ∀ s p e, S.lookup s p = some e → e.path = p

/-! ## The reference in-memory instance -/

/-- The reference state: the entries, newest first, and the clock. -/
structure MemState where
  entries : List Entry := []
  clock   : Nat := 0
deriving Inhabited

def memLookup (s : MemState) (p : String) : Option Entry :=
  s.entries.find? (fun e => e.path == p)

def memPut (s : MemState) (e : Entry) : MemState :=
  { s with entries := e :: s.entries.filter (fun x => x.path != e.path) }

def memRemove (s : MemState) (p : String) : MemState :=
  { s with entries := s.entries.filter (fun x => x.path != p) }

def memPaths (s : MemState) : List String :=
  s.entries.map (·.path)

/-- The reference `Store`. -/
def MemStore : Store MemState where
  lookup := memLookup
  put    := memPut
  remove := memRemove
  paths  := memPaths
  now    := (·.clock)
  tick   := fun s => { s with clock := s.clock + 1 }

/-! ## The laws, proved for `MemStore` -/

/-- After filtering out every entry at `q`, no entry at `q` is found. -/
theorem find_filter_self (l : List Entry) (q : String) :
    List.find? (fun e => e.path == q) (l.filter (fun x => x.path != q)) = none := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hq : a.path = q
      · have h1 : (a.path != q) = false := by simp [hq]
        simp [List.filter_cons, h1, ih]
      · have h1 : (a.path != q) = true := by simp [hq]
        have h2 : (a.path == q) = false := by simp [hq]
        simp [List.filter_cons, h1, List.find?_cons, h2, ih]

/-- Filtering out the entries at `q` does not change what is found at a
different path `p`. -/
theorem find_filter_ne (l : List Entry) (p q : String) (h : p ≠ q) :
    List.find? (fun e => e.path == p) (l.filter (fun x => x.path != q))
      = List.find? (fun e => e.path == p) l := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hq : a.path = q
      · have h1 : (a.path != q) = false := by simp [hq]
        have hne : a.path ≠ p := by rw [hq]; exact fun hc => h hc.symm
        have h2 : (a.path == p) = false := by simp [hne]
        simp [List.filter_cons, h1, List.find?_cons, h2, ih]
      · have h1 : (a.path != q) = true := by simp [hq]
        by_cases hp2 : a.path = p
        · have h2 : (a.path == p) = true := by simp [hp2]
          simp [List.filter_cons, h1, List.find?_cons, h2]
        · have h2 : (a.path == p) = false := by simp [hp2]
          simp [List.filter_cons, h1, List.find?_cons, h2, ih]

theorem memLookup_memPut_same (s : MemState) (e : Entry) :
    memLookup (memPut s e) e.path = some e := by
  simp [memLookup, memPut]

theorem memLookup_memPut_other (s : MemState) (e : Entry) (p : String)
    (h : p ≠ e.path) : memLookup (memPut s e) p = memLookup s p := by
  have hp : ¬ (e.path = p) := fun hc => h hc.symm
  simp [memLookup, memPut, hp, find_filter_ne _ _ _ h]

theorem memLookup_memRemove_same (s : MemState) (p : String) :
    memLookup (memRemove s p) p = none := by
  simp [memLookup, memRemove]

theorem memLookup_memRemove_other (s : MemState) (p q : String) (h : q ≠ p) :
    memLookup (memRemove s p) q = memLookup s q := by
  simp [memLookup, memRemove, find_filter_ne _ _ _ h]

/-- `memPaths` lists exactly the paths that resolve. -/
theorem memPaths_memLookup (s : MemState) (p : String) :
    (memPaths s).contains p = (memLookup s p).isSome := by
  simp only [memPaths, memLookup]
  induction s.entries with
  | nil => simp
  | cons a t ih =>
      by_cases hp : a.path = p
      · have h2 : (a.path == p) = true := by simp [hp]
        have h3 : (p == a.path) = true := by rw [hp]; simp
        simp only [List.map_cons, List.contains_cons, h3, Bool.true_or,
                   List.find?_cons, h2, Option.isSome_some]
      · have hne : p ≠ a.path := fun hc => hp hc.symm
        have h2 : (a.path == p) = false := by simp [hp]
        have h3 : (p == a.path) = false := by simp [hne]
        simp only [List.map_cons, List.contains_cons, h3, Bool.false_or,
                   List.find?_cons, h2, ih]

/-- `memLookup` finds an entry at its own path. -/
theorem memLookup_path (s : MemState) (p : String) (e : Entry) (h : memLookup s p = some e) :
    e.path = p := by
  have := List.find?_some h
  simpa using this

theorem memStoreLaws : StoreLaws MemStore where
  lookupPutSame := memLookup_memPut_same
  lookupPutOther := fun s e p h => memLookup_memPut_other s e p h
  lookupRemoveSame := memLookup_memRemove_same
  lookupRemoveOther := fun s p q h => memLookup_memRemove_other s p q h
  pathsLookup := memPaths_memLookup
  nowTick := fun _ => rfl
  lookupTick := fun _ _ => rfl
  lookupPath := memLookup_path

/-! ## The store the LWS handles run: a persistent search tree

`MemStore` finds and replaces an entry by a walk over a list, so one write
costs the size of the store (measured 2026-10-22, issue 918: one PUT 0.13 ms
in a store of 1,000 resources and 2.2 ms in one of 16,000). `TreeStore`
keeps the entries in a `Std.TreeMap` keyed by path: a lookup, a write and a
removal each cost a logarithm of the size. The tree is persistent: a write
to a state that something else still refers to (the state before a step,
which `Notifications.serverStep` compares with the state after it, and the
state at the last persist in `Journal.JState`) copies one path of the tree,
not the whole table (`skills/lean4-performance`, "A table in a state that a
caller may keep").

`paths` lists the paths in increasing order (the reference store lists them
newest first). No response depends on that order: every listing and every
search result is put in path order by `orderPaths`
(https://github.com/danbri/factoidal/issues/918, stage 2). -/

/-- The state of `TreeStore`: the entries keyed by path, the clock, and the
proof that every entry is stored under its own path. -/
structure TreeState where
  map : Std.TreeMap String Entry := {}
  clock : Nat := 0
  wf : ∀ (p : String) (e : Entry), map[p]? = some e → e.path = p := by
    intro p e h; simp at h

instance : Inhabited TreeState := ⟨{}⟩

def treeLookup (s : TreeState) (p : String) : Option Entry := s.map[p]?

def treePut (s : TreeState) (e : Entry) : TreeState :=
  { map := s.map.insert e.path e, clock := s.clock
    wf := fun p x h => by
      rw [Std.TreeMap.getElem?_insert] at h
      split at h
      · rename_i hc
        have : e.path = p := Std.LawfulEqCmp.eq_of_compare hc
        cases h; exact this
      · exact s.wf p x h }

def treeRemove (s : TreeState) (q : String) : TreeState :=
  { map := s.map.erase q, clock := s.clock
    wf := fun p x h => by
      rw [Std.TreeMap.getElem?_erase] at h
      split at h
      · cases h
      · exact s.wf p x h }

def treePaths (s : TreeState) : List String := s.map.keys

/-- The tree store. -/
def TreeStore : Store TreeState where
  lookup := treeLookup
  put    := treePut
  remove := treeRemove
  paths  := treePaths
  now    := (·.clock)
  tick   := fun s => { s with clock := s.clock + 1 }

theorem compare_ne_of_ne {a b : String} (h : a ≠ b) : compare a b ≠ .eq :=
  fun hc => h (Std.LawfulEqCmp.eq_of_compare hc)

/-- **The tree store satisfies every law** of `StoreLaws`, so
`Operations.step` answers over it what it answers over `MemStore`. -/
theorem treeStoreLaws : StoreLaws TreeStore where
  lookupPutSame := fun s e => by
    show (s.map.insert e.path e)[e.path]? = some e
    exact Std.TreeMap.getElem?_insert_self
  lookupPutOther := fun s e p h => by
    show (s.map.insert e.path e)[p]? = s.map[p]?
    rw [Std.TreeMap.getElem?_insert, if_neg (compare_ne_of_ne (fun h' => h h'.symm))]
  lookupRemoveSame := fun s p => by
    show (s.map.erase p)[p]? = none
    exact Std.TreeMap.getElem?_erase_self
  lookupRemoveOther := fun s p q h => by
    show (s.map.erase p)[q]? = s.map[q]?
    rw [Std.TreeMap.getElem?_erase, if_neg (compare_ne_of_ne (fun h' => h h'.symm))]
  pathsLookup := fun s p => by
    show s.map.keys.contains p = (s.map[p]?).isSome
    rw [Std.TreeMap.contains_keys, Std.TreeMap.contains_eq_isSome_getElem?]
  nowTick := fun _ => rfl
  lookupTick := fun _ _ => rfl
  lookupPath := fun s p e h => s.wf p e h

/-! ## From the reference state to the tree state, and back -/

/-- The tree state with the entries of a reference state. The entries are
written last first, so where a list holds a path twice the FIRST entry is
the one kept, as `memLookup` (`List.find?`) answers it. -/
def TreeState.ofMem (m : MemState) : TreeState :=
  { (m.entries.reverse.foldl treePut {}) with clock := m.clock }

theorem foldr_treePut_lookup (es : List Entry) (p : String) :
    (es.foldr (fun e s => treePut s e) ({} : TreeState)).map[p]? =
      es.find? (fun e => e.path == p) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
      simp only [List.foldr_cons]
      show ((rest.foldr (fun e s => treePut s e) ({} : TreeState)).map.insert e.path e)[p]? = _
      rw [Std.TreeMap.getElem?_insert, List.find?_cons]
      by_cases h : e.path = p
      · subst h; simp
      · rw [if_neg (compare_ne_of_ne h), ih]
        have : (e.path == p) = false := by simp [h]
        rw [this]

/-- **The tree state of a reference state answers every lookup the same.** -/
theorem treeLookup_ofMem (m : MemState) (p : String) :
    treeLookup (TreeState.ofMem m) p = memLookup m p := by
  show ((m.entries.reverse.foldl treePut {})).map[p]? = _
  rw [List.foldl_reverse]
  exact foldr_treePut_lookup m.entries p

theorem clock_ofMem (m : MemState) : (TreeState.ofMem m).clock = m.clock := rfl

/-- The entries of a tree state, in path order. -/
def TreeState.entries (s : TreeState) : List Entry := s.map.values

/-- The reference state with the entries of a tree state (for the snapshot
document, `snapshotJson`). -/
def TreeState.toMem (s : TreeState) : MemState := { entries := s.entries, clock := s.clock }

end L4Factoidal.LWS
