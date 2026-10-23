/-
L4Factoidal.Storage.Sbm11.FileGenTheorems — the read path of the I/O store
over the bytes of the files of a generation answers as `MemGen.store`
(https://github.com/danbri/factoidal/issues/776; row L4e′ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`FileGen` is the bytes of the files of a generation: GDV1, GDX1, per
permutation PRM1 and PRB1, and the named graph ids. `FileGen.store :
Store Id` reads them with the functions that `Session.store`
(`Harness/Sbm11Query.lean`) calls, each on positioned reads `b.extract off
(off + len)` of the bytes:

* `idOf`: `inlineCode?` of `normalizeTerm t`, else `Dict.lookupM` over
  GDX1 and GDV1 and `dictIdOfRank` of the rank (`Session.idOf`);
* `lowerBound`: `DictRange.lowerBoundM` (`Session.lowerBound`);
* `blockCount`, `blocksForRange`: `PrmRange.openM`, then `PrmRange.rangeM`
  over `bytesReader` of the PRM1 bytes (`Session.perm`, `Session.rangeFor`);
* `prb`: the bytes of the PRB1 file (`Session.prb`);
* `keyOf`, `keySlice`, `termOf`: the key of a rank below the term count,
  from `Dict.pageM` of its page (`Session.keySlice`, `Session.termOf`).

`Written G F`: the files hold the bytes the encoders write for `G`
(`encodeDict? G.keys`, `encodePrm? p (G.ms p)`, the PRB1 bytes `G.prb p`,
the named graph ids). Proved:

* `store_written`: under `Written G F`, with no blocks in permutations 4
  and above, `F.store = G.store` (field by field: `idOf_written` from
  `DictLookupTheorems.lookupM_encodeDict`, `keyAt_written` from
  `DictLookupTheorems.pageM_dict`, `lowerBound_written` from
  `DictRangeTheorems.lowerBoundM_encodeDict`, `blockCount_written` from
  `PrmRangeTheorems.openM_bytes`, `blocksForRange_written` from
  `PrmRangeTheorems.rangeM_bytes` and `rangeM_array`);
* `harness_where_allowed_file`: `MemGenWhereTheorems.harness_where_allowed_mem`
  for `F.store`.

Where `FileGen.store` is not the code of `Session.store` (each difference is
on an argument that is not an id or a permutation of the store):

* permutation codes 4 and above: `Session.perm` throws; `FileGen.store` has
  no blocks there;
* `keyOf x` for an id whose tag is not a dictionary tag or whose rank is not
  below the term count: `Session.keySlice` throws; `FileGen.store` gives the
  key of the rank or the empty key, as `MemGen.store` does;
* the error texts of `termOf`; `Session.termOf` reads the key in place
  (`decodeKeySlice?`, equal to `decodeKey?` of the bytes by
  `TermKeyFast.decodeKeySlice?_eq`);
* `Session` keeps caches (`idMemo`, `baseIds`, the dictionary page caches,
  the PRM1 range answers) and the delta overlay. With no delta log each
  cache entry is the answer of an earlier read of the same bytes; this is
  not proved here.

The I/O assumption that stays (`IO` is opaque to Lean), named
`ReadsWritten`: every positioned read that `Session` makes of bytes
`[off, off + len)` of a file of the generation (`verifiedRead` under
`Session.gdxFetch`, `Session.gdvFetch`, `Session.prmReadAt` and
`Session.prb`) returns `b.extract off (off + len)` of the bytes `b` that the
packer wrote to that file, and the length the manifest records for a PRM1
file is `b.size`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.MemGenWhereTheorems
import L4Factoidal.Storage.Sbm11.DictLookupTheorems
import L4Factoidal.Storage.Sbm11.DictRangeTheorems
import L4Factoidal.Storage.Sbm11.PrmAtTheorems
import L4Factoidal.Storage.Sbm11.PrmRangeTheorems
import L4Factoidal.Storage.Sbm11.BlockTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery (Store)
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (nestedTableM queryEnvOf)
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (WhereOk)
open L4Factoidal.Storage.Sbm11.LocalVocab
open L4Factoidal.Storage.Sbm11.Dict (fetchOf encodeDict? lookupM parseGdxHeader gdxHeaderBytes bytesToList
  pageM pageTerms chunk chunkGo)
open L4Factoidal.Storage.Sbm11.PrmRangeTheorems (readOf)

/-- The bytes of the files of an SBM11 generation. -/
structure FileGen where
  gdv : ByteArray
  gdx : ByteArray
  prm : Nat → ByteArray
  prb : Nat → ByteArray
  named : Array UInt64

/-- The id of the dictionary key `k` of rank `r` (`Session`'s `dictIdOfRank`). -/
def dictIdOfRank (k : ByteArray) (r : Nat) : UInt64 := (dictCode k.data.toList r).toUInt64

/-- The GDX1 header from the first 21 bytes. -/
def FileGen.hdr (F : FileGen) : ExceptT String Id Dict.GdxHeader :=
  match parseGdxHeader (fetchOf F.gdx 0 gdxHeaderBytes) with
  | .ok h => pure h
  | .error e => throw e

/-- `Session.idOf` with no delta log and no cache. -/
def FileGen.idOf (F : FileGen) (t0 : Term) : ExceptT String Id (Option UInt64) :=
  let t := normalizeTerm t0
  match inlineCode? t with
  | some c => pure (some c.toUInt64)
  | none =>
    match termKeyBytes? t with
    | none => pure none
    | some k => do
      let h ← F.hdr
      let (r, _) ← lookupM (fetchOf F.gdx) (fetchOf F.gdv) h k
      pure (r.map (dictIdOfRank k))

/-- The key of rank `r`: `none` when `r` is not below the term count, else
    the key at `r % pageTerms` of page `r / pageTerms` (`Session.keySlice`). -/
def FileGen.keyAt? (F : FileGen) (r : Nat) : ExceptT String Id (Option Key) := do
  let h ← F.hdr
  if r < h.termCount then
    let ks ← pageM (fetchOf F.gdx) (fetchOf F.gdv) (r / pageTerms)
    pure ((ks[r % pageTerms]?).map bytesToList)
  else pure none

/-- The key of a dictionary id (the empty key when its rank has none). -/
def FileGen.keyOf (F : FileGen) (x : UInt64) : ExceptT String Id ByteArray := do
  match ← F.keyAt? (x.toNat % two60) with
  | some k => pure ⟨k.toArray⟩
  | none => pure ⟨#[]⟩

/-- `Session.termOf` with no delta log: an inline id decodes by itself, a
    dictionary id by its key when the key's class is the id's tag. -/
def FileGen.termOf (F : FileGen) (x : UInt64) : ExceptT String Id Term := do
  let n := x.toNat
  let tag := n / two60
  if tag == tagBool || tag == tagInt then
    match ofInlineCode? n with
    | some t => pure t
    | none => throw s!"id {x}: no term"
  else if isDictTag tag then
    match ← F.keyAt? (n % two60) with
    | some k =>
      if classTag k == tag then
        match decodeKey? k with
        | some t => pure t
        | none => throw s!"id {x}: no term"
      else throw s!"id {x}: no term"
    | none => throw s!"id {x}: no term"
  else throw s!"id {x}: no term"

/-- The store over the bytes of the files. -/
def FileGen.store (F : FileGen) : Store Id where
  blockCount p := if p < 4 then PrmRange.openM (readOf (F.prm p)) (F.prm p).size p else pure 0
  blocksForRange p key :=
    if p < 4 then do
      let n ← PrmRange.openM (readOf (F.prm p)) (F.prm p).size p
      PrmRange.rangeM (PrmRange.bytesReader (readOf (F.prm p)) n) key
    else pure #[]
  prb p off len := readOf (F.prb p) off len
  idOf t := F.idOf t
  keyOf x := F.keyOf x
  keySlice x := do
    let k ← F.keyOf x
    pure (k, 0, k.size)
  termOf x := F.termOf x
  lowerBound k := do
    let h ← F.hdr
    DictRange.lowerBoundM (fetchOf F.gdx) (fetchOf F.gdv) h k
  namedGraphs := some (pure F.named)

/-- The files hold the bytes the encoders write for `G`. -/
structure Written (G : MemGen) (F : FileGen) : Prop where
  dict : ∃ v x, encodeDict? G.keys = some (v, x) ∧ F.gdv = ⟨v.toArray⟩ ∧ F.gdx = ⟨x.toArray⟩
  prm : ∀ p, p < 4 → ∃ bs, encodePrm? p (G.ms p) = some bs ∧ F.prm p = ⟨bs.toArray⟩
  prb : ∀ p, F.prb p = G.prb p
  named : F.named = G.named

/-! ## The dictionary -/

theorem parseGdxHeader_prefix (b : ByteArray) (hb : gdxHeaderBytes ≤ b.size) :
    parseGdxHeader (fetchOf b 0 gdxHeaderBytes) = parseGdxHeader b := by
  have hsz : (fetchOf b 0 gdxHeaderBytes).size = gdxHeaderBytes := by
    simp [fetchOf, ByteArray.size_extract]; simp [gdxHeaderBytes] at hb ⊢; omega
  have hg : ∀ i, i < gdxHeaderBytes → (fetchOf b 0 gdxHeaderBytes).get! i = b.get! i := by
    intro i hi
    have := PrmRangeTheorems.get!_extract b 0 gdxHeaderBytes i (by omega) hb
    simpa [fetchOf] using this
  have hm : (fetchOf b 0 gdxHeaderBytes).extract 0 5 = b.extract 0 5 := by
    simp [fetchOf, ByteArray.extract_extract, gdxHeaderBytes]
  unfold parseGdxHeader
  rw [hsz, hm]
  simp only [Nat.lt_irrefl, if_false, show ¬ b.size < gdxHeaderBytes by omega]
  unfold Dict.word64At
  rw [hg 5 (by decide), hg 6 (by decide), hg 7 (by decide), hg 8 (by decide), hg 9 (by decide),
    hg 10 (by decide), hg 11 (by decide), hg 12 (by decide), hg 13 (by decide), hg 14 (by decide),
    hg 15 (by decide), hg 16 (by decide), hg 17 (by decide), hg 18 (by decide), hg 19 (by decide),
    hg 20 (by decide)]

section dict
variable (G : MemGen) (F : FileGen) (hw : Written G F)
include hw

theorem written_admitted : Dict.dictAdmitted G.keys (chunk pageTerms G.keys) = true := by
  obtain ⟨v, x, hd, _, _⟩ := hw.dict
  unfold encodeDict? at hd; dsimp only at hd; split at hd
  · assumption
  · cases hd

/-- The header the store reads. -/
theorem hdr_written : F.hdr = pure ⟨G.keys.length, (chunk pageTerms G.keys).length⟩ := by
  obtain ⟨v, x, hd, _, hx⟩ := hw.dict
  have hhdr := (Dict.lookupM_encodeDict G.keys v x hd ⟨#[]⟩).1
  have hxs : gdxHeaderBytes ≤ (⟨x.toArray⟩ : ByteArray).size := by
    refine Nat.le_of_not_lt fun hc => ?_
    unfold parseGdxHeader at hhdr
    rw [if_pos hc] at hhdr
    cases hhdr
  unfold FileGen.hdr
  rw [hx, parseGdxHeader_prefix _ hxs, hhdr]

end dict

/-- The rank `res` that `lookupM` answers is the rank `toCode?` reads. -/
theorem res_eq (keys : List Key) (k : Key) (res : Option Nat)
    (hres : ∀ r, res = some r ↔ keys[r]? = some k) :
    res = if keys.idxOf k < keys.length then some (keys.idxOf k) else none := by
  by_cases hk : k ∈ keys
  · have hlt := List.idxOf_lt_length_of_mem hk
    rw [if_pos hlt]
    exact (hres _).mpr (by rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt])
  · rw [if_neg (by rw [List.idxOf_eq_length hk]; exact Nat.lt_irrefl _)]
    cases hr : res with
    | none => rfl
    | some r =>
      exfalso
      have := (hres r).mp hr
      exact hk (List.mem_of_getElem? this)

/-! ## Pages of the dictionary -/

theorem chunkGo_acc {α : Type} (n : Nat) : ∀ (f : Nat) (l : List α) (acc : List (List α)),
    chunkGo n f l acc = acc.reverse ++ chunkGo n f l [] := by
  intro f
  induction f with
  | zero => intro l acc; simp [chunkGo]
  | succ f ih =>
    intro l acc
    cases l with
    | nil => simp [chunkGo]
    | cons a l =>
      simp only [chunkGo]
      rw [ih _ (_ :: acc), ih _ [_]]
      simp

/-- Position `j` of chunk `i` is position `i * n + j` of the list. -/
theorem chunkGo_getElem? {α : Type} (n : Nat) (hn : 0 < n) : ∀ (f : Nat) (l : List α) (i j : Nat),
    l.length < f → j < n → i * n + j < l.length →
      ∃ c, (chunkGo n f l [])[i]? = some c ∧ c[j]? = l[i * n + j]? := by
  intro f
  induction f with
  | zero => intro l i j hf; omega
  | succ f ih =>
    intro l i j hf hj hi
    cases l with
    | nil => simp at hi
    | cons a l' =>
      simp only [chunkGo]
      rw [chunkGo_acc]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      cases i with
      | zero =>
        refine ⟨(a :: l').take n, rfl, ?_⟩
        rw [List.getElem?_take]
        simp [hj]
      | succ i =>
        have hlen : ((a :: l').drop n).length < f := by
          simp only [List.length_drop, List.length_cons] at hf ⊢; omega
        have hi' : i * n + j < ((a :: l').drop n).length := by
          simp only [List.length_drop]; rw [Nat.succ_mul] at hi; omega
        obtain ⟨c, hc, hcj⟩ := ih ((a :: l').drop n) i j hlen hj hi'
        refine ⟨c, by simpa using hc, ?_⟩
        rw [hcj, List.getElem?_drop, Nat.succ_mul]
        congr 1
        omega

theorem chunk_getElem? {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (r : Nat) (hr : r < l.length) :
    ∃ c, (chunk n l)[r / n]? = some c ∧ c[r % n]? = l[r]? := by
  have h := chunkGo_getElem? n hn (l.length + 1) l (r / n) (r % n) (by omega) (Nat.mod_lt _ hn)
    (by rw [Nat.mul_comm, Nat.div_add_mod]; exact hr)
  rw [Nat.mul_comm, Nat.div_add_mod] at h
  exact h

section dict2
variable (G : MemGen) (F : FileGen) (hw : Written G F)
include hw

/-- The key of a rank, read from its page, is the key of that rank. -/
theorem keyAt_written (r : Nat) : F.keyAt? r = pure G.keys[r]? := by
  have hadm := written_admitted G F hw
  obtain ⟨v, x, hd, hv, hx⟩ := hw.dict
  unfold encodeDict? at hd
  simp only [hadm, if_true, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  simp only [Dict.dictAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
  obtain ⟨⟨_, hpf⟩, hfit⟩ := hadm
  unfold FileGen.keyAt?
  rw [hdr_written G F hw, pure_bind]
  dsimp only
  by_cases hr : r < G.keys.length
  · rw [if_pos hr]
    obtain ⟨c, hc, hcj⟩ := chunk_getElem? pageTerms (by decide) G.keys r hr
    have hi : r / pageTerms < (chunk pageTerms G.keys).length := by
      rcases List.getElem?_eq_some_iff.mp hc with ⟨h, _⟩; exact h
    obtain ⟨ks, hks, hmap⟩ := Dict.pageM_dict (chunk pageTerms G.keys) G.keys.length hfit hpf _ hi
    rw [hv, hx, hks, pure_bind]
    have hc' : (chunk pageTerms G.keys)[r / pageTerms] = c := by
      rw [List.getElem?_eq_some_iff] at hc; exact hc.2
    rw [hc'] at hmap
    rw [← hcj, ← hmap]
    simp
  · rw [if_neg hr, List.getElem?_eq_none (by omega)]

theorem keyOf_written (x : UInt64) : F.keyOf x = pure (G.keyBytes x) := by
  unfold FileGen.keyOf MemGen.keyBytes
  rw [keyAt_written G F hw, pure_bind]
  cases G.keys[x.toNat % two60]? <;> rfl

theorem termOf_written (x : UInt64) : F.termOf x = G.store.termOf x := by
  show _ = match ofCode? G.keys x.toNat with
    | some t => pure t
    | none => throw s!"id {x}: no term"
  unfold FileGen.termOf ofCode?
  dsimp only
  simp only [keyAt_written G F hw]
  by_cases h1 : (x.toNat / two60 == tagBool || x.toNat / two60 == tagInt) = true
  · simp only [h1, if_true]
  · simp only [h1, if_false, Bool.false_eq_true]
    by_cases h2 : isDictTag (x.toNat / two60) = true
    · simp only [h2, if_true, pure_bind]
      cases G.keys[x.toNat % two60]? with
      | none => rfl
      | some k =>
        dsimp only
        by_cases h3 : (classTag k == x.toNat / two60) = true
        · simp only [h3, if_true]
        · simp only [h3, if_false, Bool.false_eq_true]
    · simp only [h2, if_false, Bool.false_eq_true]

theorem idOf_written (t : Term) : F.idOf t = pure (G.cid t) := by
  obtain ⟨v, x, hd, hv, hx⟩ := hw.dict
  have hmax : G.keys.length < Dict.maxTerms := by
    have hadm := written_admitted G F hw
    simp only [Dict.dictAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
    exact hadm.1.1.1.2
  unfold FileGen.idOf MemGen.cid toCode?
  generalize normalizeTerm t = u
  dsimp only
  cases hin : inlineCode? u with
  | some c => rfl
  | none =>
    simp only [termKeyBytes?]
    cases hk : termKey? u with
    | none => rfl
    | some k =>
      obtain ⟨res, probes, hl, hres⟩ := (Dict.lookupM_encodeDict G.keys v x hd ⟨k.toArray⟩).2
      have hr := res_eq G.keys k res (by simpa [Dict.bytesToList_mk] using hres)
      rw [Option.map_some]
      dsimp only
      rw [hdr_written G F hw, pure_bind, hv, hx]
      rw [hl, pure_bind]
      dsimp only
      rw [hr]
      by_cases hlt : G.keys.idxOf k < G.keys.length
      · have h60 : G.keys.idxOf k < two60 := by
          have : two60 = Dict.maxTerms := rfl
          rw [this]; omega
        rw [if_pos hlt]
        have hc : (decide (List.idxOf k G.keys < G.keys.length) && decide (List.idxOf k G.keys < two60)) = true := by
          simp only [hlt, h60, decide_true, Bool.and_self]
        rw [if_pos hc]
        simp only [Option.map_some, dictIdOfRank, Nat.toUInt64]
      · rw [if_neg hlt]
        have hc : ¬ (decide (List.idxOf k G.keys < G.keys.length) && decide (List.idxOf k G.keys < two60)) = true := by
          simp only [hlt, decide_false, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
        rw [if_neg hc]
        simp only [Option.map_none]

theorem lowerBound_written (k : ByteArray) : F.store.lowerBound k = G.store.lowerBound k := by
  obtain ⟨v, x, hd, hv, hx⟩ := hw.dict
  show (do let h ← F.hdr; DictRange.lowerBoundM (fetchOf F.gdx) (fetchOf F.gdv) h k) = _
  rw [hdr_written G F hw, pure_bind, hv, hx, DictRange.lowerBoundM_encodeDict G.keys v x hd k]
  rfl

end dict2

/-! ## The permutations -/

theorem decodePrmAt_written (p : Nat) (ms : List BlockMeta) (bs : List UInt8)
    (h : encodePrm? p ms = some bs) : PrmAt.decodePrmAt ⟨bs.toArray⟩ = some (p, ms.toArray) := by
  have hd := PrmAt.decodePrmAt_eq ⟨bs.toArray⟩
  rw [Dict.bytesToList_mk, decodePrm_encodePrm? p ms bs h] at hd
  cases hq : PrmAt.decodePrmAt ⟨bs.toArray⟩ with
  | none => rw [hq] at hd; cases hd
  | some q =>
    rw [hq] at hd
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨h1, h2⟩ := hd
    obtain ⟨q1, q2⟩ := q
    simp only at h1 h2
    subst h1
    rw [← h2]

theorem rangeM_empty (key : Array UInt64) :
    PrmRange.rangeM (m := Id) (PrmRange.arrayReader ([] : List BlockMeta).toArray) key = pure #[] := rfl

/-- Two stores with the same fields are equal. -/
theorem store_ext (S T : Store Id) (h1 : S.blockCount = T.blockCount) (h2 : S.blocksForRange = T.blocksForRange)
    (h3 : S.prb = T.prb) (h4 : S.idOf = T.idOf) (h5 : S.keyOf = T.keyOf) (h6 : S.keySlice = T.keySlice)
    (h7 : S.termOf = T.termOf) (h8 : S.lowerBound = T.lowerBound) (h9 : S.ovl = T.ovl)
    (h10 : S.prefetch = T.prefetch) (h11 : S.scanTable = T.scanTable) (h12 : S.scanSipTable = T.scanSipTable)
    (h13 : S.sipFactor = T.sipFactor) (h14 : S.aggOnIds = T.aggOnIds) (h15 : S.namedGraphs = T.namedGraphs)
    (h16 : S.mark = T.mark) : S = T := by
  cases S; cases T
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  rfl

section perm
variable (G : MemGen) (F : FileGen) (hw : Written G F) (h4 : ∀ p, 4 ≤ p → G.ms p = [])
include hw h4

theorem blockCount_written (p : Nat) : F.store.blockCount p = G.store.blockCount p := by
  show (if p < 4 then _ else pure 0) = pure (G.ms p).length
  by_cases hp : p < 4
  · rw [if_pos hp]
    obtain ⟨bs, he, hb⟩ := hw.prm p hp
    rw [hb, PrmRangeTheorems.openM_bytes _ p (G.ms p).toArray (decodePrmAt_written p _ bs he)]
    simp
  · rw [if_neg hp, h4 p (by omega)]
    rfl

theorem blocksForRange_written (p : Nat) (key : Array UInt64) :
    F.store.blocksForRange p key = G.store.blocksForRange p key := by
  show (if p < 4 then _ else pure #[]) = PrmRange.rangeM (PrmRange.arrayReader (G.ms p).toArray) key
  by_cases hp : p < 4
  · rw [if_pos hp]
    obtain ⟨bs, he, hb⟩ := hw.prm p hp
    have hdec := decodePrmAt_written p _ bs he
    have hadm := (decodePrm_admitted bs p (G.ms p) (decodePrm_encodePrm? p _ bs he)).1
    have := PrmRangeTheorems.rangeM_bytes ⟨bs.toArray⟩ p (G.ms p) hdec key
    rw [hb, this, PrmRangeTheorems.rangeM_array p (G.ms p) hadm key]
  · rw [if_neg hp, h4 p (by omega), rangeM_empty]

/-- Under `Written G F`, with no blocks in permutations 4 and above, the
    store over the files is the store of the generation in memory. -/
theorem store_written : F.store = G.store := by
  have hbc : F.store.blockCount = G.store.blockCount := funext (blockCount_written G F hw h4)
  have hbr : F.store.blocksForRange = G.store.blocksForRange :=
    funext fun p => funext (blocksForRange_written G F hw h4 p)
  have hprb : F.store.prb = G.store.prb := by
    funext p off len
    show readOf (F.prb p) off len = _
    rw [hw.prb p]
    rfl
  have hid : F.store.idOf = G.store.idOf := funext (idOf_written G F hw)
  have hko : F.store.keyOf = G.store.keyOf := funext (keyOf_written G F hw)
  have hks : F.store.keySlice = G.store.keySlice := by
    funext x
    show (do let k ← F.keyOf x; pure (k, 0, k.size)) = _
    rw [keyOf_written G F hw, pure_bind]
    rfl
  have hto : F.store.termOf = G.store.termOf := funext (termOf_written G F hw)
  have hlb : F.store.lowerBound = G.store.lowerBound := funext (lowerBound_written G F hw)
  have hng : F.store.namedGraphs = G.store.namedGraphs := by
    show some (pure F.named) = some (pure G.named)
    rw [hw.named]
  exact store_ext _ _ hbc hbr hprb hid hko hks hto hlb rfl rfl rfl rfl rfl rfl hng rfl

end perm


/-- The WHERE clause theorem of the harness
    (`MemGenWhereTheorems.harness_where_allowed_mem`) for the store over the
    files: when the files hold the bytes the encoders write for a generation
    `G` with `G.check = true` and no blocks in permutations 4 and above. -/
theorem harness_where_allowed_file (G : MemGen) (F : FileGen) (hw : Written G F)
    (h4 : ∀ p, 4 ≤ p → G.ms p = []) (hG : G.check = true) (clock : EvalEnv) (base : Option String)
    (plan : Plan) (p : QueryPattern) (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hq : QHyps G.cid p) :
    (∃ e, nestedTableM F.store plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM F.store plan (queryEnvOf clock base) =
          pure (t, F.store.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
          G.denote.default {} t s := by
  rw [store_written G F hw h4]
  exact harness_where_allowed_mem G hG clock base plan p hnest hdsq hq

end L4Factoidal.Storage.Sbm11.MemGen

#print axioms L4Factoidal.Storage.Sbm11.MemGen.store_written
#print axioms L4Factoidal.Storage.Sbm11.MemGen.harness_where_allowed_file
