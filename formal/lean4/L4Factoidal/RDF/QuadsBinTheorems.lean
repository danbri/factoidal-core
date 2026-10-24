/-
L4Factoidal.RDF.QuadsBinTheorems — the region of `QuadsBin.quadsBin` reads back
as exactly the quads it was written from
(https://github.com/danbri/factoidal/issues/900).

* `decodeBin_binSpec`: `decodeBin` inverts `binSpec`.
* `quadsBin_binSpec`: the one-pass writer `quadsBin` writes `binSpec tbl ixs`
  for a table `tbl` and index lists `ixs` with
  `TermJson.decodeCompactArr tbl ixs = some qs`.
* `decodeBin_quadsBin`: the two together; the quads read back with their
  language tags in lower case (`Storage.TermFold.foldQuad`).
* `quadsBin_dictInjective`: the table has one entry per RDF term
  (https://github.com/danbri/factoidal/issues/977): no duplicate, every entry
  folded, so `RDF.DictInjective` with the lookup through the fold.
-/
import L4Factoidal.RDF.QuadsBin
import L4Factoidal.Storage.TermFoldTheorems

namespace L4Factoidal.RDF.QuadsBin

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.RDF.TermJson
open L4Factoidal.Storage.TermFold (foldTerm)

/-! ## Bytes written by the `ByteArray` writer -/

theorem push_data (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  rw [ByteArray.data_push, Array.toList_push]

theorem putU32_data (b : ByteArray) (n : UInt32) :
    (putU32 b n).data.toList = b.data.toList ++ writeU32LE n := by
  unfold putU32 writeU32LE
  rw [push_data, push_data, push_data, push_data]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.toUTF8.size := by
  rw [bytesOfString, byteArray_toList_eq, Array.length_toList]
  rfl

theorem putLString_none {b : ByteArray} {s : String} (h : serializeLString? s = none) :
    putLString b s = none := by
  unfold serializeLString? at h
  unfold putLString
  have hl := bytesOfString_length s
  by_cases hc : (bytesOfString s).length >= two32
  · rw [if_neg (by omega)]
  · rw [if_neg hc] at h; exact absurd h (by simp)

theorem putLString_some {b : ByteArray} {s : String} {l : List UInt8}
    (h : serializeLString? s = some l) :
    ∃ r, putLString b s = some r ∧ r.data.toList = b.data.toList ++ l := by
  unfold serializeLString? at h
  unfold putLString
  have hl := bytesOfString_length s
  by_cases hc : (bytesOfString s).length >= two32
  · rw [if_pos hc] at h; exact absurd h (by simp)
  · rw [if_neg hc] at h
    rw [if_pos (by omega)]
    refine ⟨_, rfl, ?_⟩
    simp only [Option.some.injEq] at h
    subst h
    rw [ByteArray.data_append, Array.toList_append, putU32_data, hl]
    simp [bytesOfString, byteArray_toList_eq]

/-- A literal the DLOG version 2 codec refuses, the writer refuses. -/
theorem putLiteral_none {b : ByteArray} {lit : WfLiteral}
    (h : serializeDeltaLiteral? lit = none) : putLiteral b lit = none := by
  unfold serializeDeltaLiteral? at h
  unfold putLiteral
  cases h1 : serializeLString? lit.val.lexicalForm with
  | none => rw [putLString_none h1]
  | some a =>
    obtain ⟨r1, hr1, -⟩ := putLString_some (b := b.push termTagLiteral) h1
    rw [hr1]; dsimp only
    cases h2 : serializeLString? lit.val.datatype.val with
    | none => rw [putLString_none h2]
    | some c =>
      obtain ⟨r2, hr2, -⟩ := putLString_some (b := r1) h2
      rw [hr2]; dsimp only
      rw [h1, h2] at h
      rcases hlang : lit.val.langTag with _ | tag <;>
        rcases hdir : lit.val.direction with _ | d <;>
        simp only [hlang, hdir, bind, Option.bind] at h ⊢
      · exact absurd h (by simp)
      · cases h3 : serializeLString? tag with
        | none => rw [putLString_none h3]
        | some e => rw [h3] at h; exact absurd h (by simp)
      · cases h3 : serializeLString? tag with
        | none => rw [putLString_none h3]; rfl
        | some e => rw [h3] at h; exact absurd h (by simp)

/-- A literal: the writer writes the bytes of the DLOG version 2 codec. -/
theorem putLiteral_some {b : ByteArray} {lit : WfLiteral} {l : List UInt8}
    (h : serializeDeltaLiteral? lit = some l) :
    ∃ r, putLiteral b lit = some r ∧ r.data.toList = b.data.toList ++ l := by
  unfold serializeDeltaLiteral? at h
  unfold putLiteral
  cases h1 : serializeLString? lit.val.lexicalForm with
  | none => rw [h1] at h; exact absurd h (by simp [bind])
  | some a =>
    obtain ⟨r1, hr1, hd1⟩ := putLString_some (b := b.push termTagLiteral) h1
    rw [hr1]; dsimp only
    cases h2 : serializeLString? lit.val.datatype.val with
    | none => rw [h1, h2] at h; exact absurd h (by simp [bind])
    | some c =>
      obtain ⟨r2, hr2, hd2⟩ := putLString_some (b := r1) h2
      rw [hr2]; dsimp only
      rw [h1, h2] at h
      rw [push_data] at hd1
      rcases hlang : lit.val.langTag with _ | tag <;>
        rcases hdir : lit.val.direction with _ | d <;>
        simp only [hlang, hdir, bind, Option.bind] at h ⊢
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨_, rfl, ?_⟩
        rw [push_data, hd2, hd1]; simp
      · exact absurd h (by simp)
      · cases h3 : serializeLString? tag with
        | none => rw [h3] at h; exact absurd h (by simp)
        | some e =>
          rw [h3] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨r3, hr3, hd3⟩ := putLString_some (b := r2.push 1) h3
          refine ⟨r3, hr3, ?_⟩
          rw [hd3, push_data, hd2, hd1]; simp
      · cases h3 : serializeLString? tag with
        | none => rw [h3] at h; exact absurd h (by simp)
        | some e =>
          rw [h3] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨r3, hr3, hd3⟩ := putLString_some (b := r2.push 2) h3
          refine ⟨r3.push (dirByte d), by rw [hr3]; rfl, ?_⟩
          rw [push_data, hd3, push_data, hd2, hd1]; simp

/-- The writer of one term refuses what the DLOG version 2 term codec refuses. -/
theorem putTerm_none {b : ByteArray} {t : Term} (h : serializeDeltaTerm? t = none) :
    putTerm b t = none := by
  cases t with
  | iri i =>
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, Option.map_eq_none_iff] at h
      exact putLString_none h
  | bnode x =>
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, Option.map_eq_none_iff] at h
      exact putLString_none h
  | literal l => exact putLiteral_none h
  | tripleTerm s p o =>
      simp only [putTerm, h, Option.map_none]

/-- The writer of one term writes the bytes of the DLOG version 2 term codec. -/
theorem putTerm_some {b : ByteArray} {t : Term} {l : List UInt8}
    (h : serializeDeltaTerm? t = some l) :
    ∃ r, putTerm b t = some r ∧ r.data.toList = b.data.toList ++ l := by
  cases t with
  | iri i =>
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      obtain ⟨r, hr, hd⟩ := putLString_some (b := b.push termTagIri) ha
      exact ⟨r, hr, by rw [hd, push_data]; simp⟩
  | bnode x =>
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      obtain ⟨r, hr, hd⟩ := putLString_some (b := b.push termTagBnode) ha
      exact ⟨r, hr, by rw [hd, push_data]; simp⟩
  | literal lit => exact putLiteral_some h
  | tripleTerm s p o =>
      refine ⟨b ++ ⟨l.toArray⟩, by simp only [putTerm, h, Option.map_some], ?_⟩
      rw [ByteArray.data_append, Array.toList_append]

/-! ## The state of the one-pass writer -/

/-- Every entry of `a` is in `b` at the same index. -/
abbrev Ext (a b : Array Term) : Prop := ∀ (k : Nat) (t : Term), a[k]? = some t → b[k]? = some t

theorem Ext.refl (a : Array Term) : Ext a a := fun _ _ h => h

theorem Ext.trans {a b c : Array Term} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  fun k t h => h2 k t (h1 k t h)

theorem Ext.push (a : Array Term) (t : Term) : Ext a (a.push t) := by
  intro k u h
  have hk : k < a.size := by
    rcases Nat.lt_or_ge k a.size with hk | hk
    · exact hk
    · rw [Array.getElem?_eq_none hk] at h; exact absurd h (by simp)
  rw [Array.getElem?_push, if_neg (by omega)]
  exact h

theorem getElem?_push_size (a : Array Term) (t : Term) : (a.push t)[a.size]? = some t := by
  simp

/-- The writer's state is consistent: each index in a map names that term in
the table, the table has fewer than 2^32 entries, and the term bytes are the
bytes of the table. -/
structure Inv (st : BinState) : Prop where
  iris : ∀ s k, st.iris[s]? = some k → ∃ h, st.tbl[k]? = some (Term.iri ⟨s, h⟩)
  bnodes : ∀ s k, st.bnodes[s]? = some k → st.tbl[k]? = some (Term.bnode s)
  others : ∀ (t : Term) (k : Nat), st.others[t]? = some k → st.tbl[k]? = some t
  size : st.tbl.size < two32
  terms : serTerms st.tbl.toList = some st.terms.data.toList

theorem serTerms_snoc : ∀ (l : List Term) (a : List UInt8) (t : Term) (b : List UInt8),
    serTerms l = some a → serializeDeltaTerm? t = some b → serTerms (l ++ [t]) = some (a ++ b)
  | [], a, t, b, h, ht => by
      simp only [serTerms, Option.some.injEq] at h
      subst h
      simp [serTerms, ht]
  | x :: xs, a, t, b, h, ht => by
      simp only [serTerms] at h
      cases hx : serializeDeltaTerm? x with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some ax =>
        cases hr : serTerms xs with
        | none => rw [hx, hr] at h; exact absurd h (by simp)
        | some ar =>
          rw [hx, hr] at h
          simp only [Option.some.injEq] at h
          subst h
          simp [serTerms, hx, serTerms_snoc xs ar t b hr ht]

theorem add_spec {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st)
    (h : st.add t = some (k, st')) :
    st'.tbl = st.tbl.push t ∧ k = st.tbl.size ∧ st'.iris = st.iris ∧ st'.bnodes = st.bnodes ∧
      st'.others = st.others ∧ st'.quads = st.quads ∧ serTerms st'.tbl.toList = some st'.terms.data.toList ∧
      st'.tbl.size < two32 := by
  unfold BinState.add at h
  by_cases hs : st.tbl.size + 1 < two32
  · rw [if_pos hs] at h
    cases hp : putTerm st.terms t with
    | none => rw [hp] at h; exact absurd h (by simp)
    | some b =>
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hser : serializeDeltaTerm? t with
      | none => rw [putTerm_none hser] at hp; exact absurd hp (by simp)
      | some l =>
        obtain ⟨r, hr, hd⟩ := putTerm_some (b := st.terms) hser
        rw [hp, Option.some.injEq] at hr
        subst hr
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · simp only [Array.toList_push]
          rw [serTerms_snoc _ _ t l hi.terms hser, hd]
        · simp only [Array.size_push]; exact hs
  · rw [if_neg hs] at h; exact absurd h (by simp)

theorem add_inv {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st)
    (h : st.add t = some (k, st')) :
    Inv st' ∧ st'.tbl[k]? = some t ∧ Ext st.tbl st'.tbl ∧ st'.quads = st.quads := by
  obtain ⟨ht, hk, hir, hbn, hoth, hq, hterms, hsz⟩ := add_spec hi h
  refine ⟨⟨?_, ?_, ?_, hsz, hterms⟩, ?_, ?_, hq⟩
  · intro s j hj
    rw [hir] at hj
    obtain ⟨hh, hj'⟩ := hi.iris s j hj
    exact ⟨hh, by rw [ht]; exact Ext.push _ _ _ _ hj'⟩
  · intro s j hj
    rw [hbn] at hj
    rw [ht]; exact Ext.push _ _ _ _ (hi.bnodes s j hj)
  · intro u j hj
    rw [hoth] at hj
    rw [ht]; exact Ext.push _ _ _ _ (hi.others u j hj)
  · rw [ht, hk]; exact getElem?_push_size _ _
  · rw [ht]; exact Ext.push _ _

theorem indexOther_inv {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st)
    (h : st.indexOther t = some (k, st')) :
    Inv st' ∧ st'.tbl[k]? = some t ∧ Ext st.tbl st'.tbl ∧ st'.quads = st.quads := by
  unfold BinState.indexOther at h
  cases hm : st.others[t]? with
  | some k0 =>
    rw [hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, hi.others _ _ hm, Ext.refl _, rfl⟩
  | none =>
    rw [hm] at h
    dsimp only at h
    cases ha : st.add t with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some r =>
      obtain ⟨k1, st1⟩ := r
      rw [ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨i1, l1, e1, q1⟩ := add_inv hi ha
      refine ⟨⟨i1.iris, i1.bnodes, ?_, i1.size, i1.terms⟩, l1, e1, q1⟩
      intro u j hj
      simp only [Std.HashMap.getElem?_insert] at hj
      by_cases hu : t = u
      · subst hu
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at hj
        subst hj
        exact l1
      · rw [if_neg (by simpa using hu)] at hj
        exact i1.others u j hj

theorem index_inv {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st)
    (h : st.index t = some (k, st')) :
    Inv st' ∧ st'.tbl[k]? = some t ∧ Ext st.tbl st'.tbl ∧ st'.quads = st.quads := by
  cases t with
  | iri i =>
      unfold BinState.index at h
      dsimp only at h
      cases hm : st.iris[i.val]? with
      | some k0 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hh, hk⟩ := hi.iris _ _ hm
        exact ⟨hi, hk, Ext.refl _, rfl⟩
      | none =>
        rw [hm] at h
        dsimp only at h
        cases ha : st.add (.iri i) with
        | none => rw [ha] at h; exact absurd h (by simp)
        | some r =>
          obtain ⟨k1, st1⟩ := r
          rw [ha] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ht, hk, hir, hbn, hoth, hq, hterms, hsz⟩ := add_spec hi ha
          refine ⟨⟨?_, ?_, ?_, hsz, hterms⟩, ?_, ?_, hq⟩
          · intro s j hj
            simp only [Std.HashMap.getElem?_insert] at hj
            by_cases hs : i.val = s
            · subst hs
              simp only [beq_self_eq_true, if_true, Option.some.injEq] at hj
              subst hj
              refine ⟨i.property, ?_⟩
              rw [ht, hk]; exact getElem?_push_size _ _
            · rw [if_neg (by simpa using hs)] at hj
              rw [hir] at hj
              obtain ⟨hh, hj'⟩ := hi.iris s j hj
              exact ⟨hh, by rw [ht]; exact Ext.push _ _ _ _ hj'⟩
          · intro s j hj
            rw [hbn] at hj
            rw [ht]; exact Ext.push _ _ _ _ (hi.bnodes s j hj)
          · intro u j hj
            simp only [hoth] at hj
            rw [ht]; exact Ext.push _ _ _ _ (hi.others u j hj)
          · rw [ht, hk]; exact getElem?_push_size _ _
          · rw [ht]; exact Ext.push _ _
  | bnode b =>
      unfold BinState.index at h
      dsimp only at h
      cases hm : st.bnodes[b]? with
      | some k0 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hi, hi.bnodes _ _ hm, Ext.refl _, rfl⟩
      | none =>
        rw [hm] at h
        dsimp only at h
        cases ha : st.add (.bnode b) with
        | none => rw [ha] at h; exact absurd h (by simp)
        | some r =>
          obtain ⟨k1, st1⟩ := r
          rw [ha] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ht, hk, hir, hbn, hoth, hq, hterms, hsz⟩ := add_spec hi ha
          refine ⟨⟨?_, ?_, ?_, hsz, hterms⟩, ?_, ?_, hq⟩
          · intro s j hj
            rw [hir] at hj
            obtain ⟨hh, hj'⟩ := hi.iris s j hj
            exact ⟨hh, by rw [ht]; exact Ext.push _ _ _ _ hj'⟩
          · intro s j hj
            simp only [Std.HashMap.getElem?_insert] at hj
            by_cases hs : b = s
            · subst hs
              simp only [beq_self_eq_true, if_true, Option.some.injEq] at hj
              subst hj
              rw [ht, hk]; exact getElem?_push_size _ _
            · rw [if_neg (by simpa using hs)] at hj
              rw [hbn] at hj
              rw [ht]; exact Ext.push _ _ _ _ (hi.bnodes s j hj)
          · intro u j hj
            simp only [hoth] at hj
            rw [ht]; exact Ext.push _ _ _ _ (hi.others u j hj)
          · rw [ht, hk]; exact getElem?_push_size _ _
          · rw [ht]; exact Ext.push _ _
  | literal l => exact indexOther_inv hi h
  | tripleTerm s p o => exact indexOther_inv hi h

/-! ## One quad, and the loop over the quads -/

theorem lt_of_getElem? {a : Array Term} {k : Nat} {t : Term} (h : a[k]? = some t) : k < a.size := by
  rcases Nat.lt_or_ge k a.size with hk | hk
  · exact hk
  · rw [Array.getElem?_eq_none hk] at h; exact absurd h (by simp)

theorem mapM_lookup_mono {a b : Array Term} (hab : Ext a b) :
    ∀ (ix : List Nat) (ts : List Term), ix.mapM (a[·]?) = some ts → ix.mapM (b[·]?) = some ts
  | [], ts, h => h
  | i :: r, ts, h => by
      simp only [List.mapM_cons] at h ⊢
      cases hi : a[i]? with
      | none => rw [hi] at h; exact absurd h (by simp [bind])
      | some t =>
        cases hr : r.mapM (a[·]?) with
        | none => rw [hi, hr] at h; exact absurd h (by simp [bind])
        | some us =>
          rw [hi, hr] at h
          rw [hab i t hi, mapM_lookup_mono hab r us hr]
          exact h

theorem decodeIx_mono {a b : Array Term} (hab : Ext a b) {ix : List Nat} {q : TermJson.Quad}
    (h : decodeIx a ix = some q) : decodeIx b ix = some q := by
  unfold decodeIx at h ⊢
  cases hm : ix.mapM (a[·]?) with
  | none => rw [hm] at h; exact absurd h (by simp [bind])
  | some ts => rw [hm] at h; rw [mapM_lookup_mono hab ix ts hm]; exact h

theorem mapM_decodeIx_mono {a b : Array Term} (hab : Ext a b) :
    ∀ (ixs : List (List Nat)) (qs : List TermJson.Quad),
      ixs.mapM (decodeIx a) = some qs → ixs.mapM (decodeIx b) = some qs
  | [], qs, h => h
  | ix :: r, qs, h => by
      simp only [List.mapM_cons] at h ⊢
      cases hi : decodeIx a ix with
      | none => rw [hi] at h; exact absurd h (by simp [bind])
      | some q =>
        cases hr : r.mapM (decodeIx a) with
        | none => rw [hi, hr] at h; exact absurd h (by simp [bind])
        | some us =>
          rw [hi, hr] at h
          rw [decodeIx_mono hab hi, mapM_decodeIx_mono hab r us hr]
          exact h

theorem quad_inv {st st' : BinState} {q : TermJson.Quad} (hi : Inv st) (h : st.quad q = some st') :
    Inv st' ∧ Ext st.tbl st'.tbl ∧ ∃ ix b, ixSpec ix = some b ∧
      st'.quads.data.toList = st.quads.data.toList ++ b ∧
        decodeIx st'.tbl ix = some (Storage.TermFold.foldQuad q) := by
  obtain ⟨g, ⟨s, p, o⟩⟩ := q
  unfold BinState.quad at h
  dsimp only at h
  cases h1 : st.index (subjectToTerm s) with
  | none => rw [h1] at h; exact absurd h (by simp)
  | some r1 =>
  obtain ⟨si, st1⟩ := r1
  rw [h1] at h; dsimp only at h
  obtain ⟨i1, l1, e1, q1⟩ := index_inv hi h1
  cases h2 : st1.index (.iri p) with
  | none => rw [h2] at h; exact absurd h (by simp)
  | some r2 =>
  obtain ⟨pi, st2⟩ := r2
  rw [h2] at h; dsimp only at h
  obtain ⟨i2, l2, e2, q2⟩ := index_inv i1 h2
  cases h3 : st2.index (Storage.TermFold.foldTerm o) with
  | none => rw [h3] at h; exact absurd h (by simp)
  | some r3 =>
  obtain ⟨oi, st3⟩ := r3
  rw [h3] at h; dsimp only at h
  obtain ⟨i3, l3, e3, q3⟩ := index_inv i2 h3
  cases g with
  | none =>
    simp only [Option.some.injEq] at h
    subst h
    have hs3 : st3.tbl[si]? = some (subjectToTerm s) := e3 _ _ (e2 _ _ l1)
    have hp3 : st3.tbl[pi]? = some (.iri p) := e3 _ _ l2
    have hsz := i3.size
    refine ⟨⟨i3.iris, i3.bnodes, i3.others, i3.size, i3.terms⟩, e1.trans (e2.trans e3), [si, pi, oi],
      writeU32LE (UInt32.ofNat si) ++ writeU32LE (UInt32.ofNat pi) ++
        writeU32LE (UInt32.ofNat oi) ++ writeU32LE 0, ?_, ?_, ?_⟩
    · simp only [ixSpec]
      rw [if_pos ⟨by have := lt_of_getElem? hs3; omega, by have := lt_of_getElem? hp3; omega,
        by have := lt_of_getElem? l3; omega⟩]
    · simp only [putU32_data, q3, q2, q1, List.append_assoc]
    · simp [decodeIx, List.mapM_cons, hs3, hp3, l3, toSubject?_toTerm, termToIri?, bind, pure,
        Storage.TermFold.foldQuad, Storage.TermFold.foldTriple]
  | some gs =>
    dsimp only at h
    cases h4 : st3.index (subjectToTerm gs) with
    | none => rw [h4] at h; exact absurd h (by simp)
    | some r4 =>
    obtain ⟨gi, st4⟩ := r4
    rw [h4] at h; dsimp only at h
    obtain ⟨i4, l4, e4, q4⟩ := index_inv i3 h4
    simp only [Option.some.injEq] at h
    subst h
    have hs4 : st4.tbl[si]? = some (subjectToTerm s) := e4 _ _ (e3 _ _ (e2 _ _ l1))
    have hp4 : st4.tbl[pi]? = some (.iri p) := e4 _ _ (e3 _ _ l2)
    have ho4 : st4.tbl[oi]? = some (Storage.TermFold.foldTerm o) := e4 _ _ l3
    have hsz := i4.size
    refine ⟨⟨i4.iris, i4.bnodes, i4.others, i4.size, i4.terms⟩, e1.trans (e2.trans (e3.trans e4)),
      [si, pi, oi, gi], writeU32LE (UInt32.ofNat si) ++ writeU32LE (UInt32.ofNat pi) ++
        writeU32LE (UInt32.ofNat oi) ++ writeU32LE (UInt32.ofNat (gi + 1)), ?_, ?_, ?_⟩
    · simp only [ixSpec]
      rw [if_pos ⟨by have := lt_of_getElem? hs4; omega, by have := lt_of_getElem? hp4; omega,
        by have := lt_of_getElem? ho4; omega, by have := lt_of_getElem? l4; omega⟩]
    · simp only [putU32_data, q4, q3, q2, q1, List.append_assoc]
    · simp [decodeIx, List.mapM_cons, hs4, hp4, ho4, l4, toSubject?_toTerm, termToIri?, bind, pure,
        Storage.TermFold.foldQuad, Storage.TermFold.foldTriple]

theorem binLoop_inv : ∀ (qs : List TermJson.Quad) (st st' : BinState), Inv st → binLoop st qs = some st' →
    Inv st' ∧ Ext st.tbl st'.tbl ∧ ∃ ixs b, serIxs ixs = some b ∧
      st'.quads.data.toList = st.quads.data.toList ++ b ∧
      ixs.mapM (decodeIx st'.tbl) = some (qs.map Storage.TermFold.foldQuad) ∧ ixs.length = qs.length
  | [], st, st', hi, h => by
      simp only [binLoop, Option.some.injEq] at h
      subst h
      exact ⟨hi, Ext.refl _, [], [], rfl, by simp, rfl, rfl⟩
  | q :: qs, st, st', hi, h => by
      simp only [binLoop] at h
      cases hq : st.quad q with
      | none => rw [hq] at h; exact absurd h (by simp)
      | some st1 =>
        rw [hq] at h; dsimp only at h
        obtain ⟨i1, e1, ix, b1, hb1, hd1, hx1⟩ := quad_inv hi hq
        obtain ⟨i2, e2, ixs, b2, hb2, hd2, hx2, hlen⟩ := binLoop_inv qs st1 st' i1 h
        refine ⟨i2, e1.trans e2, ix :: ixs, b1 ++ b2, ?_, ?_, ?_, ?_⟩
        · simp [serIxs, hb1, hb2]
        · rw [hd2, hd1, List.append_assoc]
        · simp [List.mapM_cons, decodeIx_mono e2 hx1, hx2, bind, pure]
        · simp [hlen]

/-! ## One table entry per RDF term (issue 977)

`Uniq`: each table entry is the entry its map gives, so the table has no
duplicate (`Uniq.nodup`), and each entry is folded. The writer keeps it. -/

/-- The index-map entry of a term. -/
def slot (st : BinState) : Term → Option Nat
  | .iri i => st.iris[i.val]?
  | .bnode b => st.bnodes[b]?
  | .literal l => st.others[Term.literal l]?
  | .tripleTerm s p o => st.others[Term.tripleTerm s p o]?

/-- Every table entry is the entry its map gives (so the table has no
duplicate), and every table entry is folded. -/
structure Uniq (st : BinState) : Prop where
  complete : ∀ (k : Nat) (hk : k < st.tbl.size), slot st st.tbl[k] = some k
  folded : ∀ (k : Nat) (t : Term), st.tbl[k]? = some t → foldTerm t = t

theorem Uniq.nodup {st : BinState} (hu : Uniq st) : st.tbl.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [Array.length_toList] at hi hj
  simp only [Array.getElem_toList] at heq
  have h1 := hu.complete i hi
  have h2 := hu.complete j hj
  rw [heq, h2] at h1
  have := Option.some.inj h1
  omega

/-- A new entry `t` at the end of the table, with the map of its kind updated:
the old entries keep their slots when `t`'s slot was empty. -/
theorem uniq_push {st st' : BinState} {t : Term} (hu : Uniq st) (hf : foldTerm t = t)
    (hnone : slot st t = none) (htbl : st'.tbl = st.tbl.push t)
    (hslot : ∀ x, slot st' x = if x = t then some st.tbl.size else slot st x) : Uniq st' := by
  refine ⟨fun k hk => ?_, fun k u hk => ?_⟩
  · have hsz : st'.tbl.size = st.tbl.size + 1 := by rw [htbl]; simp
    rcases Nat.lt_or_ge k st.tbl.size with hlt | hge
    · have he : st'.tbl[k] = st.tbl[k] := by
        simp only [htbl, Array.getElem_push_lt hlt]
      rw [he, hslot]
      split
      · rename_i hx
        have := hu.complete k hlt
        rw [hx, hnone] at this
        cases this
      · exact hu.complete k hlt
    · have hk' : k = st.tbl.size := by omega
      subst hk'
      have he : st'.tbl[st.tbl.size] = t := by simp only [htbl, Array.getElem_push_eq]
      rw [he, hslot, if_pos rfl]
  · rw [htbl, Array.getElem?_push] at hk
    split at hk
    · cases Option.some.inj hk; exact hf
    · exact hu.folded k u hk

theorem indexOther_uniq {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st) (hu : Uniq st)
    (hf : foldTerm t = t) (h : st.indexOther t = some (k, st'))
    (hkind : (∃ l, t = .literal l) ∨ (∃ a b c, t = .tripleTerm a b c)) : Uniq st' := by
  have hs : ∀ (st0 : BinState), slot st0 t = st0.others[t]? := by
    rcases hkind with ⟨l, rfl⟩ | ⟨a, b, c, rfl⟩ <;> intro st0 <;> rfl
  unfold BinState.indexOther at h
  cases hm : st.others[t]? with
  | some k0 =>
    rw [hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hu
  | none =>
    rw [hm] at h
    dsimp only at h
    cases ha : st.add t with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some r =>
      obtain ⟨k1, st1⟩ := r
      rw [ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ht, hk, hir, hbn, hoth, -, -, -⟩ := add_spec hi ha
      refine uniq_push hu hf (by rw [hs]; exact hm) (by simpa using ht) (fun x => ?_)
      cases x with
      | iri j =>
        have : ¬ (Term.iri j = t) := by
          rcases hkind with ⟨l, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp
        simp [slot, hir, this]
      | bnode c =>
        have : ¬ (Term.bnode c = t) := by
          rcases hkind with ⟨l, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp
        simp [slot, hbn, this]
      | literal l =>
        simp only [slot, Std.HashMap.getElem?_insert, hoth, hk]
        by_cases e : t = Term.literal l
        · subst e; simp
        · simp [e, Ne.symm e]
      | tripleTerm a b c =>
        simp only [slot, Std.HashMap.getElem?_insert, hoth, hk]
        by_cases e : t = Term.tripleTerm a b c
        · subst e; simp
        · simp [e, Ne.symm e]

theorem index_uniq {st st' : BinState} {t : Term} {k : Nat} (hi : Inv st) (hu : Uniq st)
    (hf : foldTerm t = t) (h : st.index t = some (k, st')) : Uniq st' := by
  cases t with
  | iri i =>
      unfold BinState.index at h
      dsimp only at h
      cases hm : st.iris[i.val]? with
      | some k0 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hu
      | none =>
        rw [hm] at h
        dsimp only at h
        cases ha : st.add (.iri i) with
        | none => rw [ha] at h; exact absurd h (by simp)
        | some r =>
          obtain ⟨k1, st1⟩ := r
          rw [ha] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ht, hk, hir, hbn, hoth, -, -, -⟩ := add_spec hi ha
          refine uniq_push hu hf (by simpa [slot] using hm) (by simpa using ht) (fun x => ?_)
          cases x with
          | iri j =>
            simp only [slot, Std.HashMap.getElem?_insert, hir, hk]
            by_cases e : i.val = j.val
            · have : j = i := Subtype.ext e.symm
              subst this; simp
            · have : ¬ (Term.iri j = Term.iri i) := fun h' => e (by cases h'; rfl)
              simp [e, this]
          | bnode b => simp [slot, hbn]
          | literal l => simp [slot, hoth]
          | tripleTerm a b c => simp [slot, hoth]
  | bnode b =>
      unfold BinState.index at h
      dsimp only at h
      cases hm : st.bnodes[b]? with
      | some k0 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hu
      | none =>
        rw [hm] at h
        dsimp only at h
        cases ha : st.add (.bnode b) with
        | none => rw [ha] at h; exact absurd h (by simp)
        | some r =>
          obtain ⟨k1, st1⟩ := r
          rw [ha] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ht, hk, hir, hbn, hoth, -, -, -⟩ := add_spec hi ha
          refine uniq_push hu hf (by simpa [slot] using hm) (by simpa using ht) (fun x => ?_)
          cases x with
          | iri j => simp [slot, hir]
          | bnode c =>
            simp only [slot, Std.HashMap.getElem?_insert, hbn, hk]
            by_cases e : b = c
            · subst e; simp
            · simp [e, Ne.symm e]
          | literal l => simp [slot, hoth]
          | tripleTerm a b c => simp [slot, hoth]
  | literal l => exact indexOther_uniq hi hu hf h (Or.inl ⟨l, rfl⟩)
  | tripleTerm a b c => exact indexOther_uniq hi hu hf h (Or.inr ⟨a, b, c, rfl⟩)

theorem foldTerm_subjectToTerm (s : Subject) : foldTerm (subjectToTerm s) = subjectToTerm s := by
  cases s <;> rfl

theorem uniq_quads {st : BinState} (hu : Uniq st) (b : ByteArray) : Uniq { st with quads := b } :=
  ⟨hu.complete, hu.folded⟩

theorem quad_uniq {st st' : BinState} {q : TermJson.Quad} (hi : Inv st) (hu : Uniq st)
    (h : st.quad q = some st') : Uniq st' := by
  obtain ⟨g, ⟨s, p, o⟩⟩ := q
  unfold BinState.quad at h
  dsimp only at h
  cases h1 : st.index (subjectToTerm s) with
  | none => rw [h1] at h; exact absurd h (by simp)
  | some r1 =>
  obtain ⟨si, st1⟩ := r1
  rw [h1] at h; dsimp only at h
  have u1 := index_uniq hi hu (foldTerm_subjectToTerm s) h1
  obtain ⟨i1, -, -, -⟩ := index_inv hi h1
  cases h2 : st1.index (.iri p) with
  | none => rw [h2] at h; exact absurd h (by simp)
  | some r2 =>
  obtain ⟨pi, st2⟩ := r2
  rw [h2] at h; dsimp only at h
  have u2 := index_uniq i1 u1 rfl h2
  obtain ⟨i2, -, -, -⟩ := index_inv i1 h2
  cases h3 : st2.index (foldTerm o) with
  | none => rw [h3] at h; exact absurd h (by simp)
  | some r3 =>
  obtain ⟨oi, st3⟩ := r3
  rw [h3] at h; dsimp only at h
  have u3 := index_uniq i2 u2 (TermFold.foldTerm_idem o) h3
  obtain ⟨i3, -, -, -⟩ := index_inv i2 h3
  cases g with
  | none =>
    simp only [Option.some.injEq] at h
    subst h
    exact uniq_quads u3 _
  | some gs =>
    dsimp only at h
    cases h4 : st3.index (subjectToTerm gs) with
    | none => rw [h4] at h; exact absurd h (by simp)
    | some r4 =>
    obtain ⟨gi, st4⟩ := r4
    rw [h4] at h; dsimp only at h
    have u4 := index_uniq i3 u3 (foldTerm_subjectToTerm gs) h4
    simp only [Option.some.injEq] at h
    subst h
    exact uniq_quads u4 _

theorem binLoop_uniq : ∀ (qs : List TermJson.Quad) (st st' : BinState), Inv st → Uniq st →
    binLoop st qs = some st' → Uniq st'
  | [], st, st', _, hu, h => by
      simp only [binLoop, Option.some.injEq] at h
      subst h; exact hu
  | q :: qs, st, st', hi, hu, h => by
      simp only [binLoop] at h
      cases hq : st.quad q with
      | none => rw [hq] at h; exact absurd h (by simp)
      | some st1 =>
        rw [hq] at h; dsimp only at h
        obtain ⟨i1, -⟩ := quad_inv hi hq
        exact binLoop_uniq qs st1 st' i1 (quad_uniq hi hu hq) h


theorem emptyWithCapacity_data (c : Nat) : (ByteArray.emptyWithCapacity c).data.toList = [] := rfl

theorem writeU32LE_magic : writeU32LE 0x31425146 = magic := by decide

/-- **The one-pass writer writes the layout of `binSpec`, for a table and
index lists that read back as exactly the folded quads.** -/
theorem quadsBin_binSpec {qs : List TermJson.Quad} {r : ByteArray} (h : quadsBin qs = some r) :
    ∃ tbl ixs, binSpec tbl ixs = some r.data.toList ∧
      decodeCompactArr tbl ixs = some (qs.map Storage.TermFold.foldQuad) ∧
      tbl.toList.Nodup ∧ ∀ t ∈ tbl.toList, foldTerm t = t := by
  unfold quadsBin at h
  dsimp only at h
  by_cases hn : qs.length < two32
  · rw [if_pos hn] at h
    have init : Inv (BinState.init qs.length) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro s k hk; simp [BinState.init] at hk
      · intro s k hk; simp [BinState.init] at hk
      · intro t k hk; simp [BinState.init] at hk
      · simp [BinState.init]
      · show serTerms (Array.emptyWithCapacity qs.length).toList = some (ByteArray.emptyWithCapacity (32 * qs.length)).data.toList
        rw [emptyWithCapacity_data]; rfl
    cases hl : binLoop (BinState.init qs.length) qs with
    | none => rw [hl] at h; exact absurd h (by simp)
    | some st =>
      rw [hl] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨i, -, ixs, b, hb, hd, hx, hlen⟩ := binLoop_inv qs _ st init hl
      have u := binLoop_uniq qs _ st init
        ⟨fun k hk => by simp [BinState.init] at hk, fun k t hk => by simp [BinState.init] at hk⟩ hl
      refine ⟨st.tbl, ixs, ?_, ?_, u.nodup, fun t ht => ?_⟩
      · unfold binSpec
        rw [if_pos ⟨i.size, by rw [hlen]; exact hn⟩, i.terms, hb]
        dsimp only
        rw [ByteArray.data_append, Array.toList_append, ByteArray.data_append, Array.toList_append,
          putU32_data, putU32_data, putU32_data, hd, hlen]
        simp only [BinState.init, emptyWithCapacity_data] at hd ⊢
        simp [hd, writeU32LE_magic, List.append_assoc]
      · rw [decodeCompactArr, decodeCompactLoop_eq, hx]
        simp
      · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
        exact u.folded k _ (by simpa [Array.getElem?_toList] using hk)
  · rw [if_neg hn] at h; exact absurd h (by simp)

/-! ## The reader inverts the layout -/

theorem parseTermsGo_serTerms : ∀ (l : List Term) (ts rest : List UInt8) (acc : Array Term),
    serTerms l = some ts → parseTermsGo l.length (ts ++ rest) acc = some (acc ++ l.toArray, rest)
  | [], ts, rest, acc, h => by
      simp only [serTerms, Option.some.injEq] at h
      subst h
      simp [parseTermsGo]
  | x :: xs, ts, rest, acc, h => by
      simp only [serTerms] at h
      cases hx : serializeDeltaTerm? x with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some a =>
        cases hr : serTerms xs with
        | none => rw [hx, hr] at h; exact absurd h (by simp)
        | some r =>
          rw [hx, hr] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_cons, parseTermsGo, List.append_assoc,
            parseDeltaTerm_serializeDeltaTerm? x a (r ++ rest) hx]
          rw [parseTermsGo_serTerms xs r rest (acc.push x) hr]
          simp

theorem u32_toNat {n : Nat} (h : n < two32) : (UInt32.ofNat n).toNat = n :=
  UInt32.toNat_ofNat_of_lt' h

theorem writeU32LE_length (n : UInt32) : (writeU32LE n).length = 4 := rfl

theorem read4 (a b c d : UInt32) (rest : List UInt8) :
    readU32LE (writeU32LE a ++ writeU32LE b ++ writeU32LE c ++ writeU32LE d ++ rest) 0 = some a ∧
    readU32LE (writeU32LE a ++ writeU32LE b ++ writeU32LE c ++ writeU32LE d ++ rest) 4 = some b ∧
    readU32LE (writeU32LE a ++ writeU32LE b ++ writeU32LE c ++ writeU32LE d ++ rest) 8 = some c ∧
    readU32LE (writeU32LE a ++ writeU32LE b ++ writeU32LE c ++ writeU32LE d ++ rest) 12 = some d ∧
    (writeU32LE a ++ writeU32LE b ++ writeU32LE c ++ writeU32LE d ++ rest).drop 16 = rest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.append_assoc]
    exact readU32LE_writeU32LE_append a _
  · have := readU32LE_append_writeU32LE (writeU32LE a) b (writeU32LE c ++ writeU32LE d ++ rest)
    simpa only [List.append_assoc, writeU32LE_length] using this
  · have := readU32LE_append_writeU32LE (writeU32LE a ++ writeU32LE b) c (writeU32LE d ++ rest)
    simpa only [List.append_assoc, List.length_append, writeU32LE_length] using this
  · have := readU32LE_append_writeU32LE (writeU32LE a ++ writeU32LE b ++ writeU32LE c) d rest
    simpa only [List.append_assoc, List.length_append, writeU32LE_length] using this
  · simp [writeU32LE]

theorem parseIxsGo_serIxs : ∀ (ixs : List (List Nat)) (b : List UInt8) (acc : Array (List Nat)),
    serIxs ixs = some b → parseIxsGo ixs.length b acc = some (acc.toList ++ ixs)
  | [], b, acc, h => by
      simp only [serIxs, Option.some.injEq] at h
      subst h
      simp [parseIxsGo]
  | ix :: r, b, acc, h => by
      simp only [serIxs] at h
      cases hx : ixSpec ix with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some a =>
        cases hr : serIxs r with
        | none => rw [hx, hr] at h; exact absurd h (by simp)
        | some c =>
          rw [hx, hr] at h
          simp only [Option.some.injEq] at h
          subst h
          have step : ∀ (s p o g : UInt32), ixOf s p o g = ix →
              a = writeU32LE s ++ writeU32LE p ++ writeU32LE o ++ writeU32LE g →
              parseIxsGo (r.length + 1) (a ++ c) acc = some (acc.toList ++ ix :: r) := by
            intro s p o g hix ha
            subst ha
            obtain ⟨h0, h4, h8, h12, hd⟩ := read4 s p o g c
            simp only [parseIxsGo, h0, h4, h8, h12, hd, hix]
            rw [parseIxsGo_serIxs r c (acc.push ix) hr]
            simp
          match ix, hx with
          | [s, p, o], hx =>
            simp only [ixSpec] at hx
            by_cases hb : s < two32 ∧ p < two32 ∧ o < two32
            · rw [if_pos hb, Option.some.injEq] at hx
              exact step _ _ _ _ (by simp [ixOf, u32_toNat hb.1, u32_toNat hb.2.1, u32_toNat hb.2.2])
                hx.symm
            · rw [if_neg hb] at hx; exact absurd hx (by simp)
          | [s, p, o, g], hx =>
            simp only [ixSpec] at hx
            by_cases hb : s < two32 ∧ p < two32 ∧ o < two32 ∧ g + 1 < two32
            · rw [if_pos hb, Option.some.injEq] at hx
              have hg : (UInt32.ofNat (g + 1)).toNat = g + 1 := u32_toNat hb.2.2.2
              have hg0 : UInt32.ofNat (g + 1) ≠ 0 := by
                intro h0; rw [h0] at hg; simp at hg
              exact step _ _ _ _ (by
                rw [ixOf, if_neg hg0, hg, u32_toNat hb.1, u32_toNat hb.2.1, u32_toNat hb.2.2.1,
                  Nat.add_sub_cancel])
                hx.symm
            · rw [if_neg hb] at hx; exact absurd hx (by simp)
          | [], hx => simp [ixSpec] at hx
          | [_], hx => simp [ixSpec] at hx
          | [_, _], hx => simp [ixSpec] at hx
          | _ :: _ :: _ :: _ :: _ :: _, hx => simp [ixSpec] at hx

/-- **`decodeBin` inverts `binSpec`.** -/
theorem decodeBin_binSpec {tbl : Array Term} {ixs : List (List Nat)} {bs : List UInt8}
    (h : binSpec tbl ixs = some bs) : decodeBin bs = some (tbl, ixs) := by
  unfold binSpec at h
  by_cases hs : tbl.size < two32 ∧ ixs.length < two32
  · rw [if_pos hs] at h
    cases ht : serTerms tbl.toList with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some ts =>
      cases hq : serIxs ixs with
      | none => rw [ht, hq] at h; exact absurd h (by simp)
      | some qs =>
        rw [ht, hq] at h
        simp only [Option.some.injEq] at h
        subst h
        have r4 := readU32LE_append_writeU32LE magic (UInt32.ofNat tbl.size)
          (writeU32LE (UInt32.ofNat ixs.length) ++ ts ++ qs)
        have r8 := readU32LE_append_writeU32LE (magic ++ writeU32LE (UInt32.ofNat tbl.size))
          (UInt32.ofNat ixs.length) (ts ++ qs)
        simp only [List.append_assoc, List.length_append, writeU32LE_length] at r4 r8
        have hm : magic.length = 4 := rfl
        rw [hm] at r4 r8
        unfold decodeBin
        have hd : (magic ++ (writeU32LE (UInt32.ofNat tbl.size) ++
            (writeU32LE (UInt32.ofNat ixs.length) ++ (ts ++ qs)))).drop 12 = ts ++ qs := by
          simp [magic, writeU32LE]
        simp only [List.append_assoc]
        rw [if_pos (by simp [magic]), r4, r8]
        dsimp only
        rw [hd, u32_toNat hs.1, u32_toNat hs.2]
        have := parseTermsGo_serTerms tbl.toList ts qs #[] ht
        rw [Array.length_toList] at this
        rw [this]
        dsimp only
        rw [parseIxsGo_serIxs ixs qs #[] hq]
        simp
  · rw [if_neg hs] at h; exact absurd h (by simp)

/-- **The region of `quadsBin qs` reads back as exactly the folded quads**:
`decodeBin` gives a table and index lists, and `TermJson.decodeCompactArr`
reads them as `qs.map Storage.TermFold.foldQuad` (language tags in lower
case). -/
theorem decodeBin_quadsBin {qs : List TermJson.Quad} {r : ByteArray} (h : quadsBin qs = some r) :
    ∃ tbl ixs, decodeBin r.data.toList = some (tbl, ixs) ∧
      decodeCompactArr tbl ixs = some (qs.map Storage.TermFold.foldQuad) := by
  obtain ⟨tbl, ixs, hb, hd, -⟩ := quadsBin_binSpec h
  exact ⟨tbl, ixs, decodeBin_binSpec hb, hd⟩

/-- **The table of `quadsBin qs` has one entry per RDF term**: it reads back as
    a `DictInjective` dictionary of folded terms (lookup through the fold), and
    two terms with entries have one entry exactly when they are `Term.eqb`-equal
    (`TermFold.foldedListEnc_eq_iff_eqb`). -/
theorem quadsBin_dictInjective {qs : List TermJson.Quad} {r : ByteArray} (h : quadsBin qs = some r) :
    ∃ tbl ixs, decodeBin r.data.toList = some (tbl, ixs) ∧
      decodeCompactArr tbl ixs = some (qs.map Storage.TermFold.foldQuad) ∧
      DictInjective (fun t => listEnc tbl.toList (foldTerm t)) (listDec tbl.toList)
        (· ∈ tbl.toList) (· < tbl.toList.length) := by
  obtain ⟨tbl, ixs, hb, hd, hnd, hf⟩ := quadsBin_binSpec h
  exact ⟨tbl, ixs, decodeBin_binSpec hb, hd, TermFold.foldedListDict_dictInjective _ hnd hf⟩

/-! ## A page of the quads of a dataset -/

/-- The quads of one graph segment. -/
def segQuads (s : Option Subject × List Triple) : List TermJson.Quad := s.2.map (fun t => (s.1, t))

theorem quadList_segs (ds : Dataset) : TermJson.Dataset.quadList ds = (segs ds).flatMap segQuads := by
  simp [TermJson.Dataset.quadList, segs, segQuads, List.flatMap_map]

/-- The list form of `pageAcc` (specification only, so not compiled). -/
noncomputable def pageGo : List (Option Subject × List Triple) → Nat → Nat → List TermJson.Quad
  | [], _, _ => []
  | s :: rest, off, lim =>
    if lim = 0 then []
    else
      let k := s.2.length
      if k ≤ off then pageGo rest (off - k) lim
      else
        let here := ((s.2.drop off).take lim).map (fun t => (s.1, t))
        here ++ pageGo rest 0 (lim - here.length)

theorem pageGo_eq : ∀ (ss : List (Option Subject × List Triple)) (off lim : Nat),
    pageGo ss off lim = ((ss.flatMap segQuads).drop off).take lim
  | [], off, lim => by simp [pageGo]
  | s :: rest, off, lim => by
    unfold pageGo
    by_cases h0 : lim = 0
    · simp [h0]
    · rw [if_neg h0]
      simp only [List.flatMap_cons]
      have hl : (segQuads s).length = s.2.length := by simp [segQuads]
      by_cases hk : s.2.length ≤ off
      · rw [if_pos hk, pageGo_eq rest]
        conv => rhs; rw [List.drop_append, hl, List.drop_eq_nil_of_le (by rw [hl]; exact hk),
          List.nil_append]
      · rw [if_neg hk]
        rw [pageGo_eq rest]
        conv => rhs; rw [List.drop_append, hl, show off - s.2.length = 0 by omega, List.drop_zero,
          List.take_append]
        have hseg : (List.take lim (List.drop off s.2)).map (fun t => (s.1, t)) =
            List.take lim (List.drop off (segQuads s)) := by
          simp [segQuads, List.map_drop, List.map_take]
        rw [hseg]
        congr 2
        simp only [List.length_take, List.length_drop, hl]
        omega

theorem pushTake_toList (g : Option Subject) : ∀ (ts : List Triple) (n : Nat) (acc : Array TermJson.Quad),
    (pushTake g ts n acc).toList = acc.toList ++ (ts.take n).map (fun t => (g, t))
  | [], _, acc => by simp [pushTake]
  | _ :: _, 0, acc => by simp [pushTake]
  | t :: ts, n + 1, acc => by
    simp [pushTake, pushTake_toList g ts n]

theorem pageAcc_toList : ∀ (ss : List (Option Subject × List Triple)) (off lim : Nat)
    (acc : Array TermJson.Quad),
    (pageAcc ss off lim acc).toList = acc.toList ++ pageGo ss off lim
  | [], _, _, acc => by simp [pageAcc, pageGo]
  | s :: rest, off, lim, acc => by
    unfold pageAcc pageGo
    by_cases h0 : lim = 0
    · simp [h0]
    · rw [if_neg h0, if_neg h0]
      by_cases hk : s.2.length ≤ off
      · rw [if_pos hk, if_pos hk, pageAcc_toList rest]
      · rw [if_neg hk, if_neg hk, pageAcc_toList rest, pushTake_toList]
        simp only [List.length_map, List.length_take, List.length_drop, List.append_assoc]

/-- **The page op reads the same quads as the whole quad list.** -/
theorem quadPage_eq (ds : Dataset) (off lim : Nat) :
    quadPage ds off lim = ((TermJson.Dataset.quadList ds).drop off).take lim := by
  rw [quadPage, pageAcc_toList, pageGo_eq, quadList_segs]; simp

theorem quadCountGo_eq : ∀ (ss : List (Option Subject × List Triple)) (a : Nat),
    quadCountGo ss a = a + (ss.flatMap segQuads).length
  | [], a => by simp [quadCountGo]
  | s :: rest, a => by
    simp [quadCountGo, quadCountGo_eq rest, segQuads]; omega

theorem quadCount_eq (ds : Dataset) : quadCount ds = (TermJson.Dataset.quadList ds).length := by
  rw [quadCount, quadCountGo_eq, quadList_segs]; simp

/-! ## Build-time checks -/

private def exQuads : List TermJson.Quad :=
  [ (none, ⟨.iri ⟨"http://e/s", rfl⟩, ⟨"http://e/p", rfl⟩, .bnode "b"⟩)
  , (some (.iri ⟨"http://e/g", rfl⟩), ⟨.bnode "b", ⟨"http://e/p", rfl⟩, .iri ⟨"http://e/s", rfl⟩⟩) ]

-- the region reads back as the quads, and shares the repeated IRIs and label
#guard match quadsBin exQuads with
  | some r => match decodeBin r.data.toList with
    | some (tbl, ixs) => tbl.size == 4 && decodeCompactArr tbl ixs == some (exQuads.map Storage.TermFold.foldQuad)
    | none => false
  | none => false
-- a region with another magic number is refused
#guard match quadsBin exQuads with
  | some r => (decodeBin (0 :: r.data.toList.drop 1)).isNone
  | none => false
-- a truncated region is refused
#guard match quadsBin exQuads with
  | some r => (decodeBin (r.data.toList.take (r.size - 1))).isNone
  | none => false
-- an index list of the wrong shape has no bytes
#guard (ixSpec [1, 2]).isNone && (ixSpec [0, 1, 2]).isSome

#print axioms putTerm_some
#print axioms putTerm_none
#print axioms index_inv
#print axioms quadsBin_binSpec
#print axioms decodeBin_binSpec
#print axioms decodeBin_quadsBin
#print axioms quadsBin_dictInjective

end L4Factoidal.RDF.QuadsBin
