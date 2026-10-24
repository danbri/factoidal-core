/-
L4Factoidal.RDF.WriterLabels — the blank-node labels that the writers of the
N-Triples family write (https://github.com/danbri/factoidal/issues/986).

A blank-node label is local to its document (RDF 1.1 Concepts section 3.4):
the writer may write any label, provided that the same blank node gets the same
label and two blank nodes get two labels. The N-Triples, N-Quads, Turtle and
TriG writers (`Sink.serializeDataset`, `Sink.streamDataset`) first apply
`Dataset.relabelForWrite`:

* a label that is a BLANK_NODE_LABEL (RDF 1.1 N-Triples [141s],
  `isBlankNodeLabel`) is kept;
* each other label `b` gets `pre ++ toString k`, with `k` the position of `b`
  in the list of the labels outside the production (`Dataset.bnodes` order),
  and `pre` the letter `r`
  written one time more than the length of the longest label of the dataset.
  So the new label is a BLANK_NODE_LABEL, it is longer than every label of the
  dataset (no collision), and two labels get two new labels.

Proved:

* `writeLabelMap_injOn`: the map is injective on the blank nodes of the
  dataset, so (`Dataset.den_iso_renameBnodes`) the relabelled dataset denotes
  an isomorphic dataset (`den_iso_relabelForWrite`);
* `writeLabelMap_valid`, `relabelForWrite_labels`: every label of the
  relabelled dataset is a BLANK_NODE_LABEL;
* `writeLabelMap_keep`: a valid label is kept; `relabelForWrite_eq`: the
  relabelled dataset is the rename by the map.

The cost: when every label is valid, one pass over the labels
(`Dataset.bnodes`, hash set) and no copy. Otherwise each label outside the
production is found in the list of those labels (`List.idxOf`), so the time is
quadratic in the number of distinct labels outside the production, and linear
otherwise.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.BnodeTransport
import L4Factoidal.RDF.DocumentScope
import L4Factoidal.Syntax.BlankNodeLabel

namespace L4Factoidal.RDF

open L4Factoidal.Syntax

/-! ## The map -/

/-- The length of the longest label of the list (0 for none). -/
def labelLenMax (ls : List BNodeId) : Nat := ls.foldl (fun m b => max m b.length) 0

/-- The prefix of the new labels: `r`, one time more than the longest label. -/
def writeLabelPrefix (ls : List BNodeId) : String :=
  String.ofList (List.replicate (labelLenMax ls + 1) 'r')

/-- The label written for `b`: `b` when it is a BLANK_NODE_LABEL, otherwise
the prefix and the position of `b` in `bad`. -/
def writeLabel (pre : String) (bad : List BNodeId) (b : BNodeId) : BNodeId :=
  if isBlankNodeLabel b then b else pre ++ toString (bad.idxOf b)

/-- The labels of the list outside BLANK_NODE_LABEL. -/
def badLabelsOf (ls : List BNodeId) : List BNodeId := ls.filter (fun b => !isBlankNodeLabel b)

/-- The relabelling of the labels of `ds`. -/
def Dataset.writeLabelMap (ds : Dataset) : BNodeId → BNodeId :=
  writeLabel (writeLabelPrefix ds.bnodes) (badLabelsOf ds.bnodes)

/-- **The dataset that the writers of the N-Triples family write**: the same
dataset when every label is a BLANK_NODE_LABEL, otherwise the rename by
`writeLabelMap`. -/
def Dataset.relabelForWrite (ds : Dataset) : Dataset :=
  let ls := ds.bnodes
  if ls.all isBlankNodeLabel then ds
  else ds.renameBnodes (writeLabel (writeLabelPrefix ls) (badLabelsOf ls))

/-! ## The new labels are BLANK_NODE_LABELs -/

theorem isBnodeChar_of_isDigit {c : Char} (h : c.isDigit = true) : isBnodeChar c = true := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hlt : c.toNat < 0x80 := by
    have : c.val ≤ ('9' : Char).val := h2
    simp only [Char.toNat]
    have h' : c.val.toNat ≤ ('9' : Char).val.toNat := UInt32.le_iff_toNat_le.mp this
    have h9 : ('9' : Char).val.toNat = 57 := rfl
    omega
  simp only [isBnodeChar, hlt, if_true]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))))

theorem isBlankNodeLabel_fresh (n k : Nat) :
    isBlankNodeLabel (String.ofList (List.replicate (n + 1) 'r') ++ toString k) = true := by
  have hd : ∀ c ∈ Nat.toDigits 10 k, isBnodeChar c = true := fun c hc =>
    isBnodeChar_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
  unfold isBlankNodeLabel
  simp only [String.toList_append, String.toList_ofList, toList_toString_nat, List.replicate_succ,
    List.cons_append]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · simp only [List.all_append, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun c hc => ?_, hd⟩
    rw [(List.eq_of_mem_replicate hc)]
    decide
  · intro h
    have hm := List.mem_of_getLast? h
    rcases List.mem_append.mp hm with hm | hm
    · exact absurd (List.eq_of_mem_replicate hm) (by decide)
    · have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm
      exact absurd this (by decide)

/-- **Every label the map gives is a BLANK_NODE_LABEL.** -/
theorem writeLabelMap_valid (ds : Dataset) (b : BNodeId) : isBlankNodeLabel (ds.writeLabelMap b) = true := by
  unfold Dataset.writeLabelMap writeLabel writeLabelPrefix
  split
  · assumption
  · exact isBlankNodeLabel_fresh _ _

/-- **A BLANK_NODE_LABEL is kept.** -/
theorem writeLabelMap_keep (ds : Dataset) {b : BNodeId} (h : isBlankNodeLabel b = true) :
    ds.writeLabelMap b = b := by
  simp [Dataset.writeLabelMap, writeLabel, h]

/-! ## The map is injective on the labels of the dataset -/

theorem labelLen_le_foldl_max (ls : List BNodeId) : ∀ acc : Nat, acc ≤ ls.foldl (fun m b => max m b.length) acc := by
  induction ls with
  | nil => intro acc; exact Nat.le_refl _
  | cons x xs ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem length_labelLen_le_foldl_max (ls : List BNodeId) :
    ∀ (acc : Nat) {b : BNodeId}, b ∈ ls → b.length ≤ ls.foldl (fun m b => max m b.length) acc := by
  induction ls with
  | nil => intro acc b h; cases h
  | cons x xs ih =>
    intro acc b h
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (labelLen_le_foldl_max xs _)
    · exact ih _ h

theorem length_le_labelLenMax {ls : List BNodeId} {b : BNodeId} (h : b ∈ ls) :
    b.length ≤ labelLenMax ls :=
  length_labelLen_le_foldl_max ls 0 h

theorem length_fresh (n k : Nat) :
    n + 1 ≤ (String.ofList (List.replicate (n + 1) 'r') ++ toString k).length := by
  rw [String.length_append, String.length_ofList, List.length_replicate]
  omega

theorem toString_nat_inj {k1 k2 : Nat} (h : toString k1 = toString k2) : k1 = k2 := by
  have h1 := congrArg String.toList h
  rw [toList_toString_nat, toList_toString_nat] at h1
  rw [← Nat.ofDigitChars_toDigits (b := 10) (n := k1) (by decide) (by decide),
    ← Nat.ofDigitChars_toDigits (b := 10) (n := k2) (by decide) (by decide), h1]

theorem idxOf_inj_of_mem {l : List BNodeId} {a b : BNodeId} (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a = l.idxOf b) : a = b := by
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have e1 := List.getElem_idxOf ha'
  have e2 := List.getElem_idxOf hb'
  rw [← e1, ← e2]
  simp only [h]

/-- **The map is injective on the labels of the dataset.** -/
theorem writeLabelMap_injOn (ds : Dataset) : ds.InjectiveOnBnodes ds.writeLabelMap := by
  intro b1 h1 b2 h2 he
  unfold Dataset.writeLabelMap writeLabel writeLabelPrefix at he
  have hl1 := length_le_labelLenMax h1
  have hl2 := length_le_labelLenMax h2
  by_cases v1 : isBlankNodeLabel b1 = true <;> by_cases v2 : isBlankNodeLabel b2 = true
  · simpa [v1, v2] using he
  · simp only [v1, v2, if_true, if_false, Bool.false_eq_true] at he
    have := length_fresh (labelLenMax ds.bnodes) ((badLabelsOf ds.bnodes).idxOf b2)
    rw [← he] at this
    omega
  · simp only [v1, v2, if_true, if_false, Bool.false_eq_true] at he
    have := length_fresh (labelLenMax ds.bnodes) ((badLabelsOf ds.bnodes).idxOf b1)
    rw [he] at this
    omega
  · simp only [v1, v2, if_false, Bool.false_eq_true] at he
    have hs := toString_nat_inj (String.append_right_inj _ |>.mp he)
    have m1 : b1 ∈ badLabelsOf ds.bnodes := List.mem_filter.mpr ⟨h1, by simpa using v1⟩
    have m2 : b2 ∈ badLabelsOf ds.bnodes := List.mem_filter.mpr ⟨h2, by simpa using v2⟩
    exact idxOf_inj_of_mem m1 m2 hs

/-! ## The relabelled dataset -/

/-- The relabelled dataset is the rename by `writeLabelMap`. -/
theorem relabelForWrite_eq (ds : Dataset) : ds.relabelForWrite = ds.renameBnodes ds.writeLabelMap := by
  unfold Dataset.relabelForWrite
  dsimp only
  split
  · next h =>
    rw [Dataset.renameBnodes_congr (g := fun b => b), Dataset.renameBnodes_idf]
    intro b hb
    have hm : b ∈ ds.bnodes := Dataset.mem_bnodes_iff.mpr hb
    exact writeLabelMap_keep ds (List.all_eq_true.mp h b hm)
  · rfl

/-- **The relabelled dataset denotes an isomorphic dataset.** -/
theorem den_iso_relabelForWrite (ds : Dataset) : DatasetDen.Iso ds.den ds.relabelForWrite.den := by
  rw [relabelForWrite_eq]
  exact Dataset.den_iso_renameBnodes (writeLabelMap_injOn ds)

/-- **Every label of the relabelled dataset is a BLANK_NODE_LABEL.** -/
theorem relabelForWrite_labels (ds : Dataset) {b : BNodeId} (h : ds.relabelForWrite.BnodeOccurs b) :
    isBlankNodeLabel b = true := by
  rw [relabelForWrite_eq] at h
  obtain ⟨a, -, rfl⟩ := Dataset.bnodeOccurs_renameBnodes.mp h
  exact writeLabelMap_valid ds a

private def exP : WfIri := ⟨"http://e/p", by decide⟩
private def exDs : Dataset :=
  { default := [{ s := .bnode "a b", p := exP, o := .bnode "b1" }, { s := .bnode "", p := exP, o := .bnode "a b" }],
    named := [] }
-- The empty label and `a b` get `rrrr0` and `rrrr1` (the order of `Dataset.bnodes`: the
-- last occurrence of each label); `b1` is kept.
#guard exDs.relabelForWrite.default.map (fun t => (t.s, t.o)) ==
  [(.bnode "rrrr1", .bnode "b1"), (.bnode "rrrr0", .bnode "rrrr1")]
-- Every label valid: the same dataset.
#guard ({ default := [{ s := .bnode "b1", p := exP, o := .bnode "b2" }], named := [] } : Dataset).relabelForWrite.default.map
  (·.s) == [.bnode "b1"]

#print axioms writeLabelMap_valid
#print axioms writeLabelMap_injOn
#print axioms relabelForWrite_eq
#print axioms den_iso_relabelForWrite
#print axioms relabelForWrite_labels

end L4Factoidal.RDF
