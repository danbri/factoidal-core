import L4Factoidal.Paralliverse.PackWire

/-! # Physical words of an accepted Paralliverse packet

The hypotheses below concern the result of the executable byte decoder. The packet may
have been supplied by any producer. The word view reads little-endian bytes independently
of the decoded rows. Its extent contains only complete four-byte words.
-/

namespace L4Factoidal.Paralliverse.PackWire
open StaticPack (Rows)

def wordView (src : ByteArray) : Array UInt32 :=
  ((List.range (src.size / 4)).map (fun i => UInt32.ofNat (readU32 src i))).toArray

/-- Invariant.
Says: the natural number assembled from four bytes fits a u32.
Does not say: that a particular word index is in bounds. -/
private theorem readU32_fits (src : ByteArray) (i : Nat) : readU32 src i < UInt32.size := by
  have h0 : src[4*i]!.toNat < 256 := UInt8.toNat_lt _
  have h1 : src[4*i + 1]!.toNat < 256 := UInt8.toNat_lt _
  have h2 : src[4*i + 2]!.toNat < 256 := UInt8.toNat_lt _
  have h3 : src[4*i + 3]!.toNat < 256 := UInt8.toNat_lt _
  change src[4*i]!.toNat + 256 * src[4*i + 1]!.toNat +
    65536 * src[4*i + 2]!.toNat + 16777216 * src[4*i + 3]!.toNat < 4294967296
  omega

/-- Bridge.
Says: a full four-byte slot in the finite word array contains the little-endian packet word.
Does not say: that a host has uploaded those bytes into a device buffer. -/
theorem wordView_at (src : ByteArray) (i : Nat) (h : 4*i + 3 < src.size) :
    (wordView src)[i]? = some (UInt32.ofNat (readU32 src i)) := by
  have hi : i < src.size / 4 := by omega
  have hr : i < (List.range (src.size / 4)).length := by simpa using hi
  simp only [wordView, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hr, List.getElem_range, Option.map_some]

private structure Accepted (src : ByteArray) (rows : Rows) : Prop where
  headerBytes : 12 ≤ src.size
  rowLimit : readU32 src 1 ≤ maxRows
  bankLimit : readU32 src 2 ≤ maxBankWords
  extent : src.size = 4 * (3 + 2 * readU32 src 1 + readU32 src 2)
  plan : ∃ spans, readSpans src (readU32 src 2) (List.range (readU32 src 1)) 0 [] = .ok spans ∧
    rows = spans.map (readSpan src (3 + 2 * readU32 src 1))

/-- Invariant.
Says: acceptance discharges the header checks and supplies the spans used to read the rows.
Does not say: that the packet came from the bundled encoder. -/
private theorem accepted {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    Accepted src rows := by
  unfold decode at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  exact ⟨by omega, by omega, by omega, by omega, ⟨_, by assumption, (Except.ok.inj h).symm⟩⟩

/-- Invariant.
Says: a successful descriptor walk returns each physical descriptor in the supplied order.
Does not say: that source ranges are disjoint or sorted by address. -/
private theorem spans_order (src : ByteArray) (bank : Nat) (ids : List Nat) (used : Nat)
    (rev spans : List (Nat × Nat)) (h : readSpans src bank ids used rev = .ok spans) :
    spans = rev.reverse ++ ids.map (descriptorAt src) := by
  induction ids generalizing used rev with
  | nil =>
    have he := Except.ok.inj h
    simpa using he.symm
  | cons i ids ih =>
    simp only [readSpans] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    simpa [List.append_assoc] using ih _ _ h

/-- Refinement.
Says: accepted rows follow the descriptor IDs in header order and read from their bank spans.
Does not say: that the bank uses a canonical ordering of payload words. -/
private theorem accepted_rows {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    rows = (List.range (readU32 src 1)).map
      (fun i => readSpan src (3 + 2 * readU32 src 1) (descriptorAt src i)) := by
  obtain ⟨spans, hv, hr⟩ := (accepted h).plan
  rw [hr, spans_order _ _ _ _ _ _ hv]
  simp only [List.reverse_nil, List.nil_append, List.map_map, Function.comp_def]

/-- Invariant.
Says: the physical row-count word equals the number of rows returned on acceptance.
Does not say: that merely supplying this count is sufficient for acceptance. -/
theorem decode_row_count {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    readU32 src 1 = rows.length := by
  rw [accepted_rows h]
  simp

/-- Invariant.
Says: the displayed row count of an accepted packet is within the decoder's row limit.
Does not say: that this limit is a device's permitted workgroup count. -/
theorem decode_row_count_le {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    rows.length ≤ maxRows := (decode_row_count h) ▸ (accepted h).rowLimit

/-- Invariant.
Says: the packet ends exactly after the header, descriptors and declared word bank.
Does not say: that every word of that bank belongs to a logical row. -/
theorem decode_extent {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    src.size = 4 * (3 + 2 * rows.length + readU32 src 2) := by
  rw [← decode_row_count h]
  exact (accepted h).extent

/-- Bridge.
Says: the finite array's second word gives the actual number of decoded logical rows.
Does not say: that reading this header field alone validates the packet. -/
theorem decode_header_word {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    ((wordView src)[1]?).map UInt32.toNat = some rows.length := by
  have hsz := (accepted h).headerBytes
  rw [wordView_at _ _ (by omega), Option.map_some, UInt32.toNat_ofNat_of_lt' (readU32_fits _ _),
    decode_row_count h]

/-- Invariant.
Says: an in-range logical row reads the payload specified by its own physical descriptor.
Does not say: that different logical rows read different source words. -/
private theorem row_at {src : ByteArray} {rows : Rows} (h : decode src = .ok rows)
    (i : Nat) (hi : i < rows.length) :
    rows.getD i [] = readSpan src (3 + 2 * readU32 src 1) (descriptorAt src i) := by
  have hg : i < (List.range (readU32 src 1)).length := by simpa [decode_row_count h] using hi
  rw [accepted_rows h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hg, List.getElem_range] <;> rfl

/-- Bridge.
Says: the finite array's descriptor length at 4 + 2*i equals the actual decoded row length.
Does not say: that replacing this field with the descriptor start preserves the result. -/
theorem decode_descriptor_length_word {src : ByteArray} {rows : Rows} (h : decode src = .ok rows)
    (i : Nat) (hi : i < rows.length) :
    ((wordView src)[4 + 2*i]?).map UInt32.toNat = some (rows.getD i []).length := by
  have he := decode_extent h
  have hb : 4 * (4 + 2*i) + 3 < src.size := by omega
  rw [wordView_at _ _ hb, Option.map_some, UInt32.toNat_ofNat_of_lt' (readU32_fits _ _), row_at h i hi]
  simp [readSpan, descriptorAt]

/-- Invariant.
Says: a successful walk from a bounded initial count has checked every source range
and included every visited length in its cumulative word limit.
Does not say: that overlapping source spans count only once. -/
private theorem spans_safe (src : ByteArray) (bank : Nat) (ids : List Nat) (used : Nat)
    (rev spans : List (Nat × Nat)) (hu : used ≤ maxWords)
    (h : readSpans src bank ids used rev = .ok spans) :
    (∀ i ∈ ids, (descriptorAt src i).1 + (descriptorAt src i).2 ≤ bank) ∧
    used + (ids.map (fun i => (descriptorAt src i).2)).sum ≤ maxWords := by
  induction ids generalizing used rev with
  | nil => simpa using hu
  | cons i ids ih =>
    simp only [readSpans] at h
    split at h <;> try contradiction
    rename_i hspan
    split at h <;> try contradiction
    rename_i htotal
    obtain ⟨ranges, total⟩ := ih _ _ (Nat.le_of_not_gt htotal) h
    constructor
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hrest
      · exact Nat.le_of_not_gt hspan
      · exact ranges j hrest
    · simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using total

/-- Invariant.
Says: decoder acceptance checks all descriptor IDs from zero and bounds their total length.
Does not say: that the physical bank consists of only the words those IDs reference. -/
private theorem accepted_limits {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    (∀ i < readU32 src 1, (descriptorAt src i).1 + (descriptorAt src i).2 ≤ readU32 src 2) ∧
    ((List.range (readU32 src 1)).map (fun i => (descriptorAt src i).2)).sum ≤ maxWords := by
  obtain ⟨spans, hv, _⟩ := (accepted h).plan
  obtain ⟨ranges, total⟩ := spans_safe _ _ _ 0 [] spans (Nat.zero_le _) hv
  exact ⟨fun i hi => ranges i (List.mem_range.mpr hi), by simpa using total⟩

/-- Bridge.
Says: the physical descriptor-start slot supplies the decoded row's bank start and
its exclusive end is within the declared bank, including for an empty span at its end.
Does not say: that row starts are monotone or identify distinct source regions. -/
theorem decode_descriptor_span {src : ByteArray} {rows : Rows} (h : decode src = .ok rows)
    (i : Nat) (hi : i < rows.length) :
    ((wordView src)[3 + 2*i]?).map UInt32.toNat = some (descriptorAt src i).1 ∧
    (descriptorAt src i).1 + (descriptorAt src i).2 ≤ readU32 src 2 := by
  have he := decode_extent h
  have hb : 4 * (3 + 2*i) + 3 < src.size := by omega
  constructor
  · rw [wordView_at _ _ hb, Option.map_some, UInt32.toNat_ofNat_of_lt' (readU32_fits _ _)] <;> rfl
  · exact (accepted_limits h).1 i (by simpa only [decode_row_count h] using hi)

/-- Bridge.
Says: all four byte addresses of a logical row word are in bounds and the corresponding
finite bank lookup returns exactly the word at that local index in the decoded row.
Does not say: that the bank has been copied unchanged into a GPU binding. -/
theorem decode_source_word {src : ByteArray} {rows : Rows} (h : decode src = .ok rows)
    (i : Nat) (hi : i < rows.length) (j : Nat) (hj : j < (rows.getD i []).length) :
    let addr := 3 + 2*rows.length + (descriptorAt src i).1 + j
    (∀ b : Fin 4, 4*addr + b.val < src.size) ∧
    (wordView src)[addr]? = some (rows.getD i [])[j] := by
  let addr := 3 + 2*rows.length + (descriptorAt src i).1 + j
  change (∀ b : Fin 4, 4*addr + b.val < src.size) ∧ (wordView src)[addr]? = _
  have hlen : (rows.getD i []).length = (descriptorAt src i).2 := by
    rw [row_at h i hi]
    simp [readSpan]
  have hj' : j < (descriptorAt src i).2 := hlen ▸ hj
  have he := decode_extent h
  have hs := (decode_descriptor_span h i hi).2
  have hbytes : 4*addr + 3 < src.size := by
    dsimp only [addr]
    omega
  constructor
  · intro b
    have hb := b.isLt
    omega
  · have hrg : j < (List.range (descriptorAt src i).2).length := by simpa using hj'
    rw [← List.getElem?_eq_getElem hj, row_at h i hi, wordView_at _ _ hbytes]
    simp only [readSpan, List.getElem?_map, List.getElem?_eq_getElem hrg,
      List.getElem_range, Option.map_some, addr, decode_row_count h]

/-- Invariant.
Says: all logical row lengths of an accepted packet sum to at most the word limit,
including repeated reads when rows overlap in the bank.
Does not say: that the declared bank length equals the packed output length. -/
theorem decode_total_bound {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    (StaticPack.counts rows).sum ≤ maxWords := by
  have ht := (accepted_limits h).2
  rw [accepted_rows h]
  simpa only [StaticPack.counts, List.map_map, Function.comp_def, readSpan,
    List.length_map, List.length_range] using ht

/-- Bridge.
Says: decoder acceptance establishes the static packing word-address admission
at capacity maxWords.
Does not say: that a device binding or dispatch satisfies its physical limits. -/
theorem decode_admitted {src : ByteArray} {rows : Rows} (h : decode src = .ok rows) :
    StaticPack.Admitted rows maxWords :=
  ⟨Nat.lt_of_le_of_lt (decode_row_count_le h) (by decide : maxRows < UInt32.size),
    decode_total_bound h, by decide⟩

#print axioms wordView_at
#print axioms decode_row_count
#print axioms decode_row_count_le
#print axioms decode_extent
#print axioms decode_header_word
#print axioms decode_descriptor_length_word
#print axioms decode_descriptor_span
#print axioms decode_source_word
#print axioms decode_total_bound
#print axioms decode_admitted

-- Hand-written descriptors share a source word and include an empty span at the bank end.
#guard match decode (outputWords [1, 3, 3, 2, 1, 1, 2, 3, 0, 42, 7, 9]) with
  | .ok rows => rows == [[9], [7, 9], []]
  | .error _ => false

end L4Factoidal.Paralliverse.PackWire
