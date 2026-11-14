/-
L4Factoidal.ClientStorage.IdbStore — IndexedDB object stores, indexes and databases at
rest (Indexed Database API 3.0 §2.1 "Database", §2.2 "Object store", §2.7 "Index", §2.11
"Key generators", §7.6 "store a record", §7.7 "delete records", §7.8 "iterate a cursor"),
and the one way a database changes: a commit.

## Decisions

* An object store's records are a list sorted by key (`Sorted`), with a running byte
  count; an index holds its entries (index key, primary key) sorted by that pair.
* A transaction never changes a database in place. It works on a copy (`IdbOps`), and the
  databases of a storage key change only by `applyEffect`: the commit of a read-write
  transaction replaces the object stores in its scope by the copy's; the commit of a
  version-change transaction replaces the database; a deletion removes it. So an aborted
  transaction leaves no trace by construction, and `commit_visible`, `commit_other_store`
  and `commit_last_wins` say what a later transaction reads.
* `Store.wf` (records strictly sorted; the byte count equals the sum of the record sizes)
  is kept by every store operation: `put_wf`, `delete_wf`, `deleteRange_wf`, `clear_wf`.

Not proved: that an index's entries are exactly the index keys of the store's records
(tested by `#guard`; `Store.indexOk` is the decidable statement).
-/
import L4Factoidal.ClientStorage.IdbValue
import L4Factoidal.ClientStorage.Sorted

namespace L4Factoidal.ClientStorage.Idb

open L4Factoidal.ClientStorage.Sorted
open L4Factoidal.Net.Storage (get set del get_set_same get_set_other)

/-- Kind: order law. Says: `Key.cmp` is a strict total order (the four laws of
`Sorted.IsOrder`), so the theorems of `Sorted` hold for object stores and indexes. -/
theorem Key.isOrder : IsOrder Key.cmp := ⟨Key.cmp_refl, Key.eq_of_cmp, Key.cmp_swap, Key.cmp_trans⟩

/-- The comparator of index entries: index key, then primary key (§2.7). -/
abbrev ecmp : Key × Key → Key × Key → Ordering := lex Key.cmp Key.cmp

theorem ecmp_isOrder : IsOrder ecmp := Key.isOrder.lex Key.isOrder

/-! ## Indexes -/

structure Index where
  id : Nat
  name : String
  keyPath : KeyPath
  unique : Bool := false
  multiEntry : Bool := false
  /-- (index key, primary key), sorted by `ecmp`. -/
  entries : List ((Key × Key) × Unit) := []
  /-- Made while requests of its transaction were queued: it is built once the requests up to
  this id have run (0: built). Until then it neither checks nor answers. -/
  pendingUntil : Nat := 0
  deriving Inhabited

/-- The keys of an array value's items that are keys, without repeats (§7.2 with the
multiEntry flag: items that are not keys are left out). -/
def multiKeys (v : Val) : List Key :=
  match v[0]? with
  | some t =>
    if tagOf t != 'A' then [] else
    ((List.range (countOf t)).foldl (fun (acc : List Key × Nat) _ =>
      let next := skip v acc.2
      match Key.ofToks (v.extract acc.2 next) with
      | some k => (if acc.1.any (fun x => x.cmp k == .eq) then acc.1 else k :: acc.1, next)
      | none => (acc.1, next)) ([], 1)).1.reverse
  | none => []

/-- The index keys of a value in an index (§7.6 steps 4 and 5): none when the key path does
not resolve to a key. -/
def Index.keysOf (ix : Index) (v : Val) : List Key :=
  match ix.multiEntry, ix.keyPath with
  | true, .one p =>
    match evalPath v p with
    | some sub => if (sub[0]?.map tagOf) == some 'A' then multiKeys sub else (Key.ofToks sub).toList
    | none => []
  | _, kp => match extractKey v kp with | some (some k) => [k] | _ => []

/-- A unique index already holds one of `ks` for another primary key (`ConstraintError`). -/
def Index.conflict (ix : Index) (ks : List Key) (pk : Key) : Bool :=
  ix.unique && ix.pendingUntil == 0 && ks.any fun k => ix.entries.any fun e => e.1.1.cmp k == .eq && e.1.2.cmp pk != .eq

/-- The index without the entries of primary key `pk`. -/
def Index.without (ix : Index) (pk : Key) : Index :=
  { ix with entries := ix.entries.filter fun e => e.1.2.cmp pk != .eq }

/-- The index with the entries (`k`, `pk`) for `k` in `ks`. -/
def Index.withKeys (ix : Index) (ks : List Key) (pk : Key) : Index :=
  { ix with entries := ks.foldl (fun es k => insert ecmp es (k, pk) ()) ix.entries }

/-! ## Object stores -/

structure Store where
  name : String
  keyPath : KeyPath := .none
  autoInc : Bool := false
  /-- The key generator's current number (§2.11). -/
  gen : Nat := 1
  /-- Sorted by `Key.cmp`. -/
  records : List (Key × Val) := []
  indexes : List Index := []
  nextIndex : Nat := 1
  /-- The running byte count of `records`. -/
  bytes : Nat := 0
  deriving Inhabited

/-- The bytes one record counts for: its value's tokens and a fixed 16 for its key. -/
def recSize (r : Key × Val) : Nat := r.2.size + 16

/-- The store's invariant: strictly sorted records, and a byte count equal to the sum of the
record sizes. -/
structure Store.wf (s : Store) : Prop where
  sorted : Sorted Key.cmp s.records
  bytes : s.bytes = sizeSum recSize s.records

/-- The record of key `k`. -/
def Store.find (s : Store) (k : Key) : Option Val := (Sorted.find Key.cmp s.records k).map (·.2)

/-- A unique index of the store refuses value `v` under primary key `k`. -/
def Store.conflict (s : Store) (k : Key) (v : Val) : Bool :=
  s.indexes.any fun ix => ix.conflict (ix.keysOf v) k

/-- "Store a record" (§7.6) once the checks have passed: the record replaces the one with
that key, the byte count follows, and each index drops the old entries of the key and takes
the new ones. -/
def Store.put (s : Store) (k : Key) (v : Val) : Store :=
  { s with
    records := insert Key.cmp s.records k v
    bytes := s.bytes - sizeSum recSize (s.records.filter fun e => Key.cmp e.1 k == .eq) + recSize (k, v)
    indexes := s.indexes.map fun ix => (ix.without k).withKeys (ix.keysOf v) k }

/-- "Delete records" (§7.7) for one key. -/
def Store.delete (s : Store) (k : Key) : Store :=
  { s with
    records := erase Key.cmp s.records k
    bytes := s.bytes - sizeSum recSize (s.records.filter fun e => Key.cmp e.1 k == .eq)
    indexes := s.indexes.map (·.without k) }

/-- "Delete records" (§7.7) for a key range. -/
def Store.deleteRange (s : Store) (r : Range) : Store :=
  { s with
    records := s.records.filter fun e => !r.includes e.1
    bytes := s.bytes - sizeSum recSize (s.records.filter fun e => r.includes e.1)
    indexes := s.indexes.map fun ix => { ix with entries := ix.entries.filter fun e => !r.includes e.1.2 } }

/-- "Clear an object store" (§7.5). -/
def Store.clear (s : Store) : Store :=
  { s with records := [], bytes := 0, indexes := s.indexes.map fun ix => { ix with entries := [] } }

theorem sizeSum_filter_le {α : Type} (size : α → Nat) (p : α → Bool) (l : List α) :
    sizeSum size (l.filter p) ≤ sizeSum size l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih => cases hx : p x <;> simp [hx, sizeSum_cons] <;> omega

theorem sizeSum_filter_not {α : Type} (size : α → Nat) (p : α → Bool) (l : List α) :
    sizeSum size (l.filter fun e => !p e) + sizeSum size (l.filter p) = sizeSum size l := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx, sizeSum_cons] <;> omega

/-- Kind: invariant (order and quota accounting). Says: after a record is stored, the
records are still strictly sorted and the byte count is still the sum of the stored record
sizes. Does not say: that the size of a record is the memory the engine uses for it. -/
theorem Store.put_wf (s : Store) (k : Key) (v : Val) (h : s.wf) : (s.put k v).wf where
  sorted := insert_sorted Key.isOrder _ _ _ h.sorted
  bytes := by
    have e := sizeSum_insert (c := Key.cmp) recSize s.records k v
    have le := sizeSum_filter_le recSize (fun e => Key.cmp e.1 k == .eq) s.records
    show s.bytes - _ + _ = sizeSum recSize (insert Key.cmp s.records k v)
    rw [h.bytes]; omega

/-- Kind: invariant (order and quota accounting). Says: the same after a record is deleted. -/
theorem Store.delete_wf (s : Store) (k : Key) (h : s.wf) : (s.delete k).wf where
  sorted := erase_sorted _ _ h.sorted
  bytes := by
    have e := sizeSum_erase (c := Key.cmp) recSize s.records k
    show s.bytes - _ = sizeSum recSize (erase Key.cmp s.records k)
    rw [h.bytes]; omega

/-- Kind: invariant (order and quota accounting). Says: the same after the records of a key
range are deleted. -/
theorem Store.deleteRange_wf (s : Store) (r : Range) (h : s.wf) : (s.deleteRange r).wf where
  sorted := List.Pairwise.filter _ h.sorted
  bytes := by
    have e := sizeSum_filter_not recSize (fun e : Key × Val => r.includes e.1) s.records
    show s.bytes - _ = sizeSum recSize (s.records.filter fun e => !r.includes e.1)
    rw [h.bytes]; omega

/-- Kind: invariant (order and quota accounting). Says: an empty or cleared store has the
invariant with a count of zero. -/
theorem Store.clear_wf (s : Store) : s.clear.wf := ⟨List.Pairwise.nil, rfl⟩

/-- The decidable statement that an index holds exactly the index keys of the records
(checked in `#guard`s; not proved as an invariant). -/
def Store.indexOk (s : Store) : Bool :=
  s.indexes.all fun ix =>
    let want := s.records.foldl (fun es r => (ix.keysOf r.2).foldl (fun es k => insert ecmp es (k, r.1) ()) es) []
    want.map (·.1) == ix.entries.map (·.1)

/-! ## Rows: what a query or a cursor ranges over -/

/-- The rows of a source in order: for the store itself (key, key) of each record; for an
index its entries (index key, primary key). -/
def Store.rows (s : Store) (index : Option Nat) : List ((Key × Key) × Unit) :=
  match index with
  | none => s.records.map fun r => ((r.1, r.1), ())
  | some id => match s.indexes.find? (·.id == id) with | some ix => ix.entries | none => []

/-- Cursor directions (§2.10): 0 next, 1 nextunique, 2 prev, 3 prevunique. -/
abbrev Dir := Nat

/-- One step of a cursor over `rows` (§7.8 "iterate a cursor"): the next row in direction
`dir` that is in `range`, after position `pos`, and not before the targets `tkey` (of
`continue(key)`) and `tpk` (of `continuePrimaryKey`). -/
def stepRows (rows : List ((Key × Key) × Unit)) (range : Range) (dir : Dir) (pos : Option (Key × Key))
    (tkey tpk : Option Key) : Option (Key × Key) :=
  let fwd := dir < 2
  let uniq := dir == 1 || dir == 3
  -- `a` is at or past `b` in the cursor's direction
  let past (a b : Key) : Bool := if fwd then a.cmp b != .lt else a.cmp b != .gt
  let inR (e : Key × Key) : Bool :=
    range.includes e.1 &&
    (match tkey with | some t => past e.1 t | none => true) &&
    (match tkey, tpk with
     | some t, some p => e.1.cmp t != .eq || past e.2 p
     | _, _ => true) &&
    (match pos with
     | some p => if uniq then (if fwd then p.1.cmp e.1 == .lt else e.1.cmp p.1 == .lt) else true
     | none => true)
  let found :=
    if fwd then next ecmp inR rows (if uniq then none else pos)
    else next (Sorted.flip ecmp) inR rows.reverse (if uniq then none else pos)
  match found with
  | some e =>
    -- prevunique: the first (lowest primary key) row of that index key
    if dir == 3 then (rows.find? fun r => r.1.1.cmp e.1.1 == .eq).map (·.1) else some e.1
  | none => none

/-- The rows of a source in a range, in direction `dir`, at most `count` of them (0: all):
`getAll`, `getAllKeys`, `getAllRecords`, `count`. -/
def rowsIn (rows : List ((Key × Key) × Unit)) (range : Range) (dir : Dir) (count : Nat) : List (Key × Key) :=
  let inRange := (rows.filter fun e => range.includes e.1.1).map (·.1)
  let uniqF (l : List (Key × Key)) : List (Key × Key) :=
    (l.foldl (fun (acc : List (Key × Key)) e =>
      match acc with
      | last :: _ => if last.1.cmp e.1 == .eq then acc else e :: acc
      | [] => [e]) []).reverse
  let ordered := match dir with
    | 0 => inRange
    | 1 => uniqF inRange
    | 2 => inRange.reverse
    | _ => (uniqF inRange).reverse
  if count == 0 then ordered else ordered.take count

/-! ## Databases and commits -/

structure Db where
  version : Nat := 0
  /-- Object stores by id (an id is never reused in one database, so a handle of a deleted
  store never names a later one). -/
  stores : List (Nat × Store) := []
  nextStore : Nat := 1
  deriving Inhabited

/-- The bytes a store's description counts for in `estimate()`: its name and a fixed 64 for
itself and for each index (an estimate, as the Storage Standard allows; a constant reveals
nothing about the host). -/
def Store.overhead (s : Store) : Nat := s.name.utf8ByteSize + 64 * (s.indexes.length + 1)

/-- The bytes a database holds: the sum of its stores' byte counts and descriptions. -/
def Db.usage (d : Db) : Nat := sizeSum (fun p : Nat × Store => p.2.bytes + p.2.overhead) d.stores

/-- The store named `name`, with its id. -/
def Db.storeNamed (d : Db) (name : String) : Option (Nat × Store) := d.stores.find? fun p => p.2.name == name

/-- What one step may do to the databases of a storage key. -/
inductive Effect where
  | none
  /-- A transaction on database `name` commits its working copy `work`: the stores of
  `scope`, or the whole database for a version-change transaction (`scope` is `none`). -/
  | commit (name : String) (work : Db) (scope : Option (List Nat))
  | delete (name : String)

/-- The stores of `stores` with those of `scope` replaced by the working copy's. -/
def commitStores (stores work : List (Nat × Store)) (scope : List Nat) : List (Nat × Store) :=
  scope.foldl (fun st id => match get work id with | some s => set st id s | none => st) stores

/-- The databases after an effect. This is the only function that changes them. -/
def applyEffect (dbs : List (String × Db)) : Effect → List (String × Db)
  | .none => dbs
  | .commit name work none => set dbs name work
  | .commit name work (some scope) =>
    match get dbs name with
    | some db => set dbs name { db with stores := commitStores db.stores work.stores scope }
    | none => dbs
  | .delete name => del dbs name

theorem commitStores_get (work : List (Nat × Store)) (scope : List Nat) :
    ∀ (stores : List (Nat × Store)) (id : Nat),
      get (commitStores stores work scope) id =
        if id ∈ scope then (match get work id with | some s => some s | none => get stores id) else get stores id := by
  induction scope with
  | nil => intro stores id; simp [commitStores]
  | cons x xs ih =>
    intro stores id
    have hstep : commitStores stores work (x :: xs) =
        commitStores (match get work x with | some s => set stores x s | none => stores) work xs := rfl
    rw [hstep, ih]
    by_cases hx : id = x
    · subst hx
      cases hw : get work id with
      | none => simp
      | some s => simp [get_set_same]
    · have hbeq : (x == id) = false := by simpa using fun e : x = id => hx e.symm
      cases hw : get work x with
      | none => simp [hx]
      | some s => simp [hx, get_set_other _ _ _ _ hbeq]

/-- Kind: transaction law (a commit is visible). Says: after a read-write transaction
commits, each store of its scope is, in the database, the store of the transaction's
working copy: a later transaction, whose copy is taken from the database, reads what was
committed. Does not say: anything of durability (the database is in memory). -/
theorem commit_visible (dbs : List (String × Db)) (name : String) (db work : Db) (scope : List Nat)
    (id : Nat) (s : Store) (hdb : get dbs name = some db) (hid : id ∈ scope) (hs : get work.stores id = some s) :
    ((get (applyEffect dbs (.commit name work (some scope))) name).bind fun d => get d.stores id) = some s := by
  simp [applyEffect, hdb, get_set_same, commitStores_get, hid, hs]

/-- Kind: transaction law (isolation of a commit). Says: a commit changes no object store
outside the transaction's scope. -/
theorem commit_other_store (dbs : List (String × Db)) (name : String) (db work : Db) (scope : List Nat)
    (id : Nat) (hdb : get dbs name = some db) (hid : id ∉ scope) :
    ((get (applyEffect dbs (.commit name work (some scope))) name).bind fun d => get d.stores id) = get db.stores id := by
  simp [applyEffect, hdb, get_set_same, commitStores_get, hid]

/-- Kind: transaction law (isolation of a commit). Says: a commit or a deletion of one
database changes no other database of the storage key. -/
theorem effect_other_db (dbs : List (String × Db)) (e : Effect) (name name' : String)
    (hn : (name == name') = false)
    (he : e = .none ∨ (∃ w sc, e = .commit name w sc) ∨ e = .delete name) :
    get (applyEffect dbs e) name' = get dbs name' := by
  rcases he with rfl | ⟨w, sc, rfl⟩ | rfl
  · rfl
  · cases sc with
    | none => simp [applyEffect, get_set_other _ _ _ _ hn]
    | some scope =>
      simp only [applyEffect]
      cases hdb : get dbs name with
      | none => rfl
      | some db => simp [get_set_other _ _ _ _ hn]
  · simp [applyEffect, L4Factoidal.Net.Storage.get_del_other _ _ _ hn]

/-- Kind: transaction law (commit order). Says: when two transactions commit one after the
other and a store is in both scopes, the database holds the store of the one that
committed last: committed writes are seen in commit order. -/
theorem commit_last_wins (dbs : List (String × Db)) (name : String) (db w1 w2 : Db) (sc1 sc2 : List Nat)
    (id : Nat) (s : Store) (hdb : get dbs name = some db) (hid : id ∈ sc2) (hs : get w2.stores id = some s) :
    ((get (applyEffect (applyEffect dbs (.commit name w1 (some sc1))) (.commit name w2 (some sc2))) name).bind
      fun d => get d.stores id) = some s := by
  have h1 : ∃ db1, get (applyEffect dbs (.commit name w1 (some sc1))) name = some db1 := by
    simp [applyEffect, hdb, get_set_same]
  obtain ⟨db1, h1⟩ := h1
  exact commit_visible _ name db1 w2 sc2 id s h1 hid hs

/-- Kind: transaction law (atomicity). Says: a step with no effect leaves the databases as
they were. Every request of a transaction, and its abort, is such a step (`IdbOps.op` gives
`Effect.none` for everything but the commit of a transaction and the deletion of a
database): after an abort the databases equal the databases before the transaction. -/
theorem effect_none (dbs : List (String × Db)) : applyEffect dbs .none = dbs := rfl

/-! ## Checks -/

private def T (xs : List String) : Val := (xs.map String.toUTF8).toArray
private def nk (n : Nat) : Key := .number (Int.ofNat (natBits n))
private def person (name : String) (tags : List String) : Val :=
  T (["o2", "kname", "s" ++ name, "ktags", s!"A{tags.length}"] ++ tags.map ("s" ++ ·))
private def st0 : Store :=
  { name := "people", indexes := [{ id := 1, name := "by_name", keyPath := .one "name", unique := true },
                                  { id := 2, name := "by_tag", keyPath := .one "tags", multiEntry := true }] }
private def st1 : Store := ((st0.put (nk 2) (person "bob" ["x", "y"])).put (nk 1) (person "al" ["y"])).put (nk 3) (person "cy" [])
#guard st1.records.map (·.1) == [nk 1, nk 2, nk 3]
#guard st1.bytes == sizeSum recSize st1.records && st1.indexOk
#guard (st1.rows (some 1)).map (·.1.2) == [nk 1, nk 2, nk 3]
#guard (st1.rows (some 2)).map (·.1) == [(.string [120], nk 2), (.string [121], nk 1), (.string [121], nk 2)]
#guard st1.conflict (nk 9) (person "bob" []) && !st1.conflict (nk 2) (person "bob" []) && !st1.conflict (nk 9) (person "dee" [])
#guard ((st1.put (nk 2) (person "rob" ["z"])).rows (some 2)).map (·.1) == [(.string [121], nk 1), (.string [122], nk 2)]
#guard (st1.put (nk 2) (person "rob" ["z"])).indexOk && (st1.delete (nk 2)).indexOk && (st1.deleteRange { lower := some (nk 2) }).indexOk
#guard (st1.delete (nk 2)).bytes == sizeSum recSize (st1.delete (nk 2)).records
#guard (st1.deleteRange { lower := some (nk 2) }).records.map (·.1) == [nk 1]
#guard st1.clear.bytes == 0 && st1.clear.indexOk
-- cursors over the store and over an index
#guard stepRows (st1.rows none) {} 0 none none none == some (nk 1, nk 1)
#guard stepRows (st1.rows none) {} 0 (some (nk 1, nk 1)) none none == some (nk 2, nk 2)
#guard stepRows (st1.rows none) {} 0 (some (nk 3, nk 3)) none none == none
#guard stepRows (st1.rows none) {} 2 none none none == some (nk 3, nk 3)
#guard stepRows (st1.rows none) {} 2 (some (nk 3, nk 3)) none none == some (nk 2, nk 2)
#guard stepRows (st1.rows none) {} 0 (some (nk 1, nk 1)) (some (nk 3)) none == some (nk 3, nk 3)
#guard stepRows (st1.rows (some 2)) {} 1 (some (.string [120], nk 2)) none none == some (.string [121], nk 1)
#guard stepRows (st1.rows (some 2)) {} 0 (some (.string [121], nk 1)) none none == some (.string [121], nk 2)
#guard stepRows (st1.rows (some 2)) {} 3 none none none == some (.string [121], nk 1)
#guard stepRows (st1.rows (some 2)) {} 2 none none none == some (.string [121], nk 2)
#guard stepRows (st1.rows (some 2)) {} 0 none (some (.string [121])) (some (nk 2)) == some (.string [121], nk 2)
#guard rowsIn (st1.rows (some 2)) {} 1 0 == [(.string [120], nk 2), (.string [121], nk 1)]
#guard rowsIn (st1.rows none) { lower := some (nk 2) } 2 1 == [(nk 3, nk 3)]
-- commits
private def db0 : Db := { version := 1, stores := [(1, st0), (2, { name := "other" })], nextStore := 3 }
private def dbs1 := applyEffect [("d", db0)] (.commit "d" { db0 with stores := [(1, st1), (2, { name := "ignored" })] } (some [1]))
#guard ((get dbs1 "d").bind fun d => (get d.stores 1).map (·.records.length)) == some 3
#guard ((get dbs1 "d").bind fun d => (get d.stores 2).map (·.name)) == some "other"
#guard (get (applyEffect dbs1 (.delete "d")) "d").isNone
#guard ((get dbs1 "d").map Db.usage) == some (st1.bytes + st1.overhead + ({ name := "other" } : Store).overhead)

end L4Factoidal.ClientStorage.Idb
