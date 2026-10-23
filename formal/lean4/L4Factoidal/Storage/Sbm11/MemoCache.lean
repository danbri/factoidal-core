/-
L4Factoidal.Storage.Sbm11.MemoCache — the bounded caches of a query
session as pure functions over a hash map, and their coherence
(https://github.com/danbri/factoidal/issues/776; row L4e′ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

A query session (`Harness/Sbm11Query.lean`) keeps answers it has computed
once: the dictionary id of a term (`idMemo`), the PRM1 entries of a key
range (`LoadedPerm.ranges`) and the decoded dictionary pages (`pages`). Each
cache is a hash map that is emptied when it is full and then takes the new
entry (`insertBounded`). The session reads and writes these maps only with
`find?` and `insertBounded`.

`Coherent f m`: every entry of `m` is the answer of `f` for its key.
Theorems:

* `coherent_empty`, `coherent_insertBounded`: the empty map is coherent,
  and inserting the answer of `f` keeps a map coherent, also when the
  insert empties a full map first;
* `find?_coherent`: a hit in a coherent map is the answer of `f`;
* `lookup_eq`: `lookup m k (f k)`, the cached lookup with the fresh answer
  computed on a miss, gives `f k`, and the map after it is coherent.

So a cached answer is the answer of the function the cache stands for, for
every sequence of lookups, as long as every value the session inserts is
that function's answer for the key. That last condition is the obligation
the session code meets by construction (each insert takes the value just
computed by the uncached read) and that `FileGenTheorems.store_written`
discharges for the uncached reads over the files' bytes, with the I/O
assumption `ReadsWritten`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashMap

namespace L4Factoidal.Storage.Sbm11.MemoCache

variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]

/-- The cached value of `k`. -/
def find? (m : Std.HashMap κ ν) (k : κ) : Option ν := m[k]?

/-- Insert `k ↦ v`; a map that holds `lim` entries or more is emptied
    first. -/
def insertBounded (lim : Nat) (m : Std.HashMap κ ν) (k : κ) (v : ν) : Std.HashMap κ ν :=
  (if m.size < lim then m else {}).insert k v

/-- The cached lookup: a hit, or the fresh answer `fresh`, kept in the map
    when it is `some`. -/
def lookup (lim : Nat) (m : Std.HashMap κ ν) (k : κ) (fresh : Option ν) : Option ν × Std.HashMap κ ν :=
  match find? m k with
  | some v => (some v, m)
  | none =>
    match fresh with
    | some v => (some v, insertBounded lim m k v)
    | none => (none, m)

/-- Every entry of `m` is the answer of `f` for its key. -/
def Coherent (f : κ → Option ν) (m : Std.HashMap κ ν) : Prop := ∀ k v, m[k]? = some v → f k = some v

theorem coherent_empty (f : κ → Option ν) : Coherent f ({} : Std.HashMap κ ν) := by
  intro k v h
  simp at h

theorem coherent_insertBounded (f : κ → Option ν) (lim : Nat) (m : Std.HashMap κ ν) (hm : Coherent f m)
    (k : κ) (v : ν) (hv : f k = some v) : Coherent f (insertBounded lim m k v) := by
  have hb : Coherent f (if m.size < lim then m else {}) := by
    split
    · exact hm
    · exact coherent_empty f
  intro k' v' h
  unfold insertBounded at h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i e
    have e' : k = k' := LawfulBEq.eq_of_beq e
    subst e'
    simp only [Option.some.injEq] at h
    subst h
    exact hv
  · exact hb k' v' h

omit [LawfulBEq κ] in
theorem find?_coherent (f : κ → Option ν) (m : Std.HashMap κ ν) (hm : Coherent f m) (k : κ) (v : ν)
    (h : find? m k = some v) : f k = some v :=
  hm k v h

/-- The cached lookup with the fresh answer `f k` on a miss gives `f k`, and
    leaves a coherent map. -/
theorem lookup_eq (f : κ → Option ν) (lim : Nat) (m : Std.HashMap κ ν) (hm : Coherent f m) (k : κ) :
    (lookup lim m k (f k)).1 = f k ∧ Coherent f (lookup lim m k (f k)).2 := by
  unfold lookup
  cases hk : find? m k with
  | some v =>
    exact ⟨(find?_coherent f m hm k v hk).symm, hm⟩
  | none =>
    cases hf : f k with
    | none => exact ⟨rfl, hm⟩
    | some v => exact ⟨rfl, coherent_insertBounded f lim m hm k v hf⟩

/-- Any sequence of cached lookups, each with the fresh answer of `f`, gives
    the answers of `f`. -/
theorem lookups_eq (f : κ → Option ν) (lim : Nat) :
    ∀ (ks : List κ) (m : Std.HashMap κ ν), Coherent f m →
      (ks.foldl (fun (acc : List (Option ν) × Std.HashMap κ ν) k =>
        let r := lookup lim acc.2 k (f k); (acc.1 ++ [r.1], r.2)) ([], m)).1 = ks.map f
  | ks, m, hm => by
    suffices H : ∀ (ks : List κ) (acc : List (Option ν)) (m : Std.HashMap κ ν), Coherent f m →
        (ks.foldl (fun (acc : List (Option ν) × Std.HashMap κ ν) k =>
          let r := lookup lim acc.2 k (f k); (acc.1 ++ [r.1], r.2)) (acc, m)).1 = acc ++ ks.map f by
      simpa using H ks [] m hm
    intro ks
    induction ks with
    | nil => intro acc m _; simp
    | cons k ks ih =>
      intro acc m hm
      obtain ⟨h1, h2⟩ := lookup_eq f lim m hm k
      simp only [List.foldl_cons, List.map_cons]
      rw [ih _ _ h2, h1]
      simp

/-! ## The page caches: eviction by class -/

/-- The class of pages that a full page cache drops: the pages whose number
    has the remainder of the new page modulo 16. -/
def evictClasses : Nat := 16

/-- Insert page `pg` in a page map of at most `lim` entries: when the map is
    full, the entries of the class of `pg` are dropped, and the whole map
    when that does not make room. -/
def insertEvict {α : Type} (m : Std.HashMap Nat α) (lim pg : Nat) (v : α) : Std.HashMap Nat α :=
  if m.size < lim then m.insert pg v
  else
    let m' := m.filter fun k _ => k % evictClasses != pg % evictClasses
    (if m'.size < lim then m' else {}).insert pg v

theorem coherent_filter {α : Type} (f : Nat → Option α) (m : Std.HashMap Nat α) (hm : Coherent f m)
    (p : Nat → α → Bool) : Coherent f (m.filter p) := by
  intro k v h
  rw [Std.HashMap.getElem?_filter'] at h
  cases hk : m[k]? with
  | none => rw [hk] at h; cases h
  | some w =>
    rw [hk] at h
    simp only [Option.filter] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hm k w hk
    · cases h

theorem coherent_insertEvict {α : Type} (f : Nat → Option α) (m : Std.HashMap Nat α) (hm : Coherent f m)
    (lim pg : Nat) (v : α) (hv : f pg = some v) : Coherent f (insertEvict m lim pg v) := by
  have hins : ∀ m0 : Std.HashMap Nat α, Coherent f m0 → Coherent f (m0.insert pg v) := by
    intro m0 h0
    have := coherent_insertBounded f (m0.size + 1) m0 h0 pg v hv
    unfold insertBounded at this
    rwa [if_pos (Nat.lt_succ_self _)] at this
  unfold insertEvict
  split
  · exact hins m hm
  · apply hins
    split
    · exact coherent_filter f m hm _
    · exact coherent_empty f

/-- A copy of a packed page made by the calling thread: the same value. -/
def copyPage (ks : ByteArray × Array Nat) : ByteArray × Array Nat :=
  (ks.1.extract 0 ks.1.size, ks.2.extract 0 ks.2.size)

theorem copyPage_eq (ks : ByteArray × Array Nat) : copyPage ks = ks := by
  obtain ⟨b, a⟩ := ks
  simp only [copyPage, Prod.mk.injEq, Array.extract_size, and_true]
  apply ByteArray.ext
  simp [ByteArray.extract, ByteArray.copySlice]

end L4Factoidal.Storage.Sbm11.MemoCache
