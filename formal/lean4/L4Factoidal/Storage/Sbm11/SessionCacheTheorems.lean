/-
L4Factoidal.Storage.Sbm11.SessionCacheTheorems — the cached lookups of a
query session give the answers of the uncached reads
(https://github.com/danbri/factoidal/issues/776; row L4e′ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`Harness/Sbm11Query.lean` keeps two caches of answers in a session:
`idMemo` (the dictionary id of a normalised term) and, per permutation,
`ranges` (the PRM1 entries of a key). Both are read with
`MemoCache.find?` and written with `MemoCache.insertBounded` of the value
the uncached read has just given. This module states the two lookups over
the bytes of the files (`FileGen`, row L4e′) with their caches and proves:

* `idOfMemo_eq`: with a cache whose entries are ids of `G.cid`, the cached
  `idOf` answers `F.idOf` (the uncached read of `FileGenTheorems`), and
  the cache stays so; with `idOf_written`, the answer is `G.cid t`;
* `rangeMemo_eq`: with a cache whose entries are answers of
  `F.store.blocksForRange p`, the cached range answers it, and the cache
  stays so.

The page caches (`pages`, `taskPages`) and the verified chunk caches of the
files are not covered here; the row L4e′ of the lemma table states their
obligation.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FileGenTheorems
import L4Factoidal.Storage.Sbm11.MemoCache
import L4Factoidal.Storage.Sbm11.FilterIdTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block

/-- `Session.idOf` with its memo `idMemo` and no delta log, over the bytes
    of the files: the inline code, else a hit of the memo, else the
    uncached read `F.idOf`, whose dictionary id the memo then keeps. -/
def FileGen.idOfMemo (F : FileGen) (lim : Nat) (m : Std.HashMap Term UInt64) (t0 : Term) :
    ExceptT String Id (Option UInt64) × Std.HashMap Term UInt64 :=
  let t := normalizeTerm t0
  match inlineCode? t with
  | some c => (pure (some c.toUInt64), m)
  | none =>
    match MemoCache.find? m t with
    | some x => (pure (some x), m)
    | none =>
      match (F.idOf t0).run with
      | .ok (some x) => (pure (some x), MemoCache.insertBounded lim m t x)
      | _ => (F.idOf t0, m)

theorem cid_normalize (G : MemGen) (t : Term) : G.cid (normalizeTerm t) = G.cid t := by
  unfold MemGen.cid
  rw [FilterIdTheorems.normalize_idem]

/-- The cached `idOf` answers the uncached read, and keeps the memo
    coherent with `G.cid`. -/
theorem idOfMemo_eq (G : MemGen) (F : FileGen) (hw : Written G F) (lim : Nat) (m : Std.HashMap Term UInt64)
    (hm : MemoCache.Coherent G.cid m) (t0 : Term) :
    (F.idOfMemo lim m t0).1 = F.idOf t0 ∧ MemoCache.Coherent G.cid (F.idOfMemo lim m t0).2 := by
  have hw' := idOf_written G F hw t0
  unfold FileGen.idOfMemo
  dsimp only
  cases hin : inlineCode? (normalizeTerm t0) with
  | some c =>
    refine ⟨?_, hm⟩
    rw [hw']
    unfold MemGen.cid toCode?
    rw [hin]
    rfl
  | none =>
    dsimp only
    cases hf : MemoCache.find? m (normalizeTerm t0) with
    | some x =>
      refine ⟨?_, hm⟩
      have := MemoCache.find?_coherent G.cid m hm _ x hf
      rw [cid_normalize] at this
      rw [hw', this]
    | none =>
      dsimp only
      rw [hw']
      cases hc : G.cid t0 with
      | none => exact ⟨rfl, hm⟩
      | some x =>
        refine ⟨rfl, MemoCache.coherent_insertBounded G.cid lim m hm _ x ?_⟩
        rw [cid_normalize, hc]

/-- `Session.rangeFor` with its cache `ranges` (at most 256 keys), over the
    bytes of the files. -/
def FileGen.rangeMemo (F : FileGen) (p : Nat) (m : Std.HashMap (Array UInt64) (Array BlockMeta))
    (key : Array UInt64) : ExceptT String Id (Array BlockMeta) × Std.HashMap (Array UInt64) (Array BlockMeta) :=
  match MemoCache.find? m key with
  | some r => (pure r, m)
  | none =>
    match (F.store.blocksForRange p key).run with
    | .ok r => (pure r, MemoCache.insertBounded 256 m key r)
    | .error e => (throw e, m)

/-- The answer of the uncached range read, when it is not an error. -/
def FileGen.rangeAns (F : FileGen) (p : Nat) (key : Array UInt64) : Option (Array BlockMeta) :=
  match (F.store.blocksForRange p key).run with
  | .ok r => some r
  | .error _ => none

theorem except_eq_of_run {α : Type} (x : ExceptT String Id α) (r : α) (h : x.run = .ok r) : x = pure r := h

/-- The cached range answers the uncached read, and keeps the cache
    coherent with it. -/
theorem rangeMemo_eq (F : FileGen) (p : Nat) (m : Std.HashMap (Array UInt64) (Array BlockMeta))
    (hm : MemoCache.Coherent (F.rangeAns p) m) (key : Array UInt64) :
    (F.rangeMemo p m key).1 = F.store.blocksForRange p key ∧
      MemoCache.Coherent (F.rangeAns p) (F.rangeMemo p m key).2 := by
  unfold FileGen.rangeMemo
  cases hf : MemoCache.find? m key with
  | some r =>
    refine ⟨?_, hm⟩
    have h := MemoCache.find?_coherent (F.rangeAns p) m hm key r hf
    unfold FileGen.rangeAns at h
    split at h
    · rename_i r' hr
      simp only [Option.some.injEq] at h
      subst h
      exact (except_eq_of_run _ _ hr).symm
    · cases h
  | none =>
    dsimp only
    cases hr : (F.store.blocksForRange p key).run with
    | ok r =>
      refine ⟨(except_eq_of_run _ _ hr).symm, ?_⟩
      exact MemoCache.coherent_insertBounded (F.rangeAns p) 256 m hm key r (by simp [FileGen.rangeAns, hr])
    | error e =>
      refine ⟨?_, hm⟩
      show (throw e : ExceptT String Id (Array BlockMeta)) = _
      exact hr.symm

end L4Factoidal.Storage.Sbm11.MemGen
