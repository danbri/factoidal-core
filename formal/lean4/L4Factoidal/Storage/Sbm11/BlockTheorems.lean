/-
L4Factoidal.Storage.Sbm11.BlockTheorems — the PRB1 block and PRM1 round
trips.

* `decodeBlock_encodeBlock?`: `encodeBlock? off rows = some (m, bs) →
  decodeBlock m bs = some rows`. The only hypothesis is the encoder's
  admission.
* `decodeBlock_bounds`: a block that decodes has `m.rows` rows, strictly
  increasing, the first is `m.first` and the last is `m.last`. So the
  first and last key of a PRM1 entry are the first and last rows of its
  decoded block.
* `encodeBlock?_bounds`: the PRM1 entry the encoder writes holds the first
  and the last row of the block.
* `decodePrm_encodePrm?`: `encodePrm? perm ms = some bs → decodePrm bs =
  some (perm, ms)`.
* `decodePrm_admitted`: a PRM1 file that decodes is admitted: blocks sorted,
  not overlapping, contiguous in PRB1.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Block
import L4Factoidal.Storage.Sbm11.ColumnTheorems

namespace L4Factoidal.Storage.Sbm11.Block

open L4Factoidal (two32 two64)
open L4Factoidal.Storage.Sbm11.Column

theorem zipRows_map : ∀ (rows : List Row),
    zipRows (rows.map Row.c0) (rows.map Row.c1) (rows.map Row.c2) (rows.map Row.g) = rows := by
  intro rows
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [zipRows, List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

theorem decodeFrame_frameBytes (xs : List Nat) (h : ∀ x ∈ xs, x < two64) :
    decodeFrame xs.length (frameBytes xs) = some xs := by
  have he : encodeColumn? xs = some (frameBytes xs) := by
    unfold encodeColumn? columnAdmitted
    rw [if_pos (List.all_eq_true.mpr (fun x hx => by simpa using h x hx))]
  have := decodeColumn_encodeColumn? xs _ he []
  rw [List.append_nil] at this
  unfold decodeFrame
  rw [this]

private theorem fits_c0 (rows : List Row) (h : rows.all Row.fits = true) : ∀ x ∈ rows.map Row.c0, x < two64 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp h r hr
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1

private theorem fits_c1 (rows : List Row) (h : rows.all Row.fits = true) : ∀ x ∈ rows.map Row.c1, x < two64 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp h r hr
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.2

private theorem fits_c2 (rows : List Row) (h : rows.all Row.fits = true) : ∀ x ∈ rows.map Row.c2, x < two64 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp h r hr
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

private theorem fits_g (rows : List Row) (h : rows.all Row.fits = true) : ∀ x ∈ rows.map Row.g, x < two64 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp h r hr
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

/-- The block round trip. The only hypothesis is the encoder's admission. -/
theorem decodeBlock_encodeBlock? (off : Nat) (rows : List Row) (m : BlockMeta) (bs : List UInt8)
    (h : encodeBlock? off rows = some (m, bs)) : decodeBlock m bs = some rows := by
  unfold encodeBlock? at h
  split at h
  · rename_i hadm
    simp only [blockAdmitted, Bool.and_eq_true] at hadm
    obtain ⟨⟨⟨⟨⟨⟨⟨hne, hsorted⟩, hfits⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hadm
    have hne' : rows ≠ [] := by
      intro he; subst he; simp at hne
    obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hm, hb⟩ := h
    subst hm hb
    unfold decodeBlock blockBytes
    simp only [BlockMeta.size, List.append_assoc, List.length_append, Nat.add_assoc,
      bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [List.take_left, List.drop_left, List.take_left, List.drop_left, List.take_left,
      List.drop_left]
    have e0 := decodeFrame_frameBytes _ (fits_c0 _ hfits)
    have e1 := decodeFrame_frameBytes _ (fits_c1 _ hfits)
    have e2 := decodeFrame_frameBytes _ (fits_c2 _ hfits)
    have e3 := decodeFrame_frameBytes _ (fits_g _ hfits)
    simp only [List.length_map] at e0 e1 e2 e3
    rw [e0, e1, e2, e3]
    dsimp only
    rw [zipRows_map]
    split
    · rfl
    · rename_i hno
      exfalso
      apply hno
      simp only [blockOk, hsorted, beq_self_eq_true, List.head?_cons, List.headD_cons, Bool.and_true,
        Bool.true_and, List.getLastD_eq_getLast?]
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil r rs)]
      simp
  · cases h

/-- A block that decodes: `m.rows` rows, strictly increasing, from `m.first`
    to `m.last`. -/
theorem decodeBlock_bounds (m : BlockMeta) (bs : List UInt8) (rows : List Row)
    (h : decodeBlock m bs = some rows) :
    rows.length = m.rows ∧ rows.head? = some m.first ∧ rows.getLast? = some m.last ∧
      rowsSorted rows = true := by
  unfold decodeBlock at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [blockOk, Bool.and_eq_true, beq_iff_eq] at hok
        exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩
      · cases h
    · cases h

/-- The PRM1 entry the encoder writes holds the first and the last row of
    the block. -/
theorem encodeBlock?_bounds (off : Nat) (rows : List Row) (m : BlockMeta) (bs : List UInt8)
    (h : encodeBlock? off rows = some (m, bs)) :
    rows.head? = some m.first ∧ rows.getLast? = some m.last ∧ rows.length = m.rows := by
  have := decodeBlock_bounds m bs rows (decodeBlock_encodeBlock? off rows m bs h)
  exact ⟨this.2.1, this.2.2.1, this.1⟩

/-! ## PRM1 -/

theorem getRow_rowBytes (r : Row) (h : r.fits = true) (rest : List UInt8) :
    getRow (rowBytes r ++ rest) = some (r, rest) := by
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  simp only [getRow, rowBytes, List.append_assoc, get64_put64 _ h0, get64_put64 _ h1,
    get64_put64 _ h2, get64_put64 _ h3, bind, Option.bind]

theorem getEntry_entryBytes (m : BlockMeta) (h : metaFits m = true) (rest : List UInt8) :
    getEntry (entryBytes m ++ rest) = some (m, rest) := by
  simp only [metaFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hl⟩, _⟩, hr⟩, ho⟩, h0⟩, h1⟩, h2⟩, h3⟩, _⟩ := h
  simp only [getEntry, entryBytes, List.append_assoc, getRow_rowBytes _ hf, getRow_rowBytes _ hl,
    get32_put32 _ hr, get64_put64 _ ho, get32_put32 _ h0, get32_put32 _ h1, get32_put32 _ h2,
    get32_put32 _ h3, bind, Option.bind]

theorem chainGo_fits : ∀ (ms : List BlockMeta) (off : Nat), chainGo off ms = true →
    ∀ m ∈ ms, metaFits m = true := by
  intro ms
  induction ms with
  | nil => intro off _ m hm; cases hm
  | cons x xs ih =>
    intro off h m hm
    unfold chainGo at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      cases hm with
      | head => exact hc.1
      | tail _ hm' =>
        cases xs with
        | nil => cases hm'
        | cons n ns =>
          simp only at h
          split at h
          · exact ih _ h m hm'
          · cases h
    · cases h

theorem getEntriesGo_entries : ∀ (ms : List BlockMeta) (acc : List BlockMeta) (rest : List UInt8),
    (∀ m ∈ ms, metaFits m = true) →
    getEntriesGo ms.length ((ms.map entryBytes).flatten ++ rest) acc = some (acc.reverse ++ ms, rest) := by
  intro ms
  induction ms with
  | nil => intro acc rest _; simp [getEntriesGo]
  | cons m ms ih =>
    intro acc rest hf
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.length_cons, getEntriesGo]
    rw [getEntry_entryBytes m (hf m (by simp))]
    dsimp only
    rw [ih (m :: acc) rest (fun x hx => hf x (by simp [hx]))]
    simp

/-- The PRM1 round trip. The only hypothesis is the encoder's admission. -/
theorem decodePrm_encodePrm? (perm : Nat) (ms : List BlockMeta) (bs : List UInt8)
    (h : encodePrm? perm ms = some bs) : decodePrm bs = some (perm, ms) := by
  unfold encodePrm? at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq] at h
    subst h
    have hadm' := hadm
    simp only [prmAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm'
    obtain ⟨⟨⟨hp, hchain⟩, hlen⟩, hsum⟩ := hadm'
    have hpn : perm.toUInt8.toNat = perm := UInt8.toNat_ofNat_of_lt' (by show perm < 256; omega)
    simp only [prmBytes, prmMagic, List.cons_append, List.nil_append, List.append_assoc, decodePrm]
    rw [get64_put64 _ hlen]
    dsimp only
    rw [get64_put64 _ hsum]
    dsimp only
    have he := getEntriesGo_entries ms [] [] (chainGo_fits ms _ hchain)
    simp only [List.append_nil, List.reverse_nil, List.nil_append] at he
    rw [he]
    dsimp only
    rw [hpn, if_pos (by simp [hadm])]
  · cases h

/-- A PRM1 file that decodes is admitted: its blocks are sorted, do not
    overlap and are contiguous in PRB1. -/
theorem decodePrm_admitted (bs : List UInt8) (perm : Nat) (ms : List BlockMeta)
    (h : decodePrm bs = some (perm, ms)) : prmAdmitted perm ms = true ∧ perm < 4 := by
  unfold decodePrm at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true] at hc
            refine ⟨hc.1, ?_⟩
            have := hc.1
            simp only [prmAdmitted, Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.1.1
          · cases h
        · cases h
  · cases h

end L4Factoidal.Storage.Sbm11.Block
