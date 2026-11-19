/-
Lookup in the complete TLI1 bytes produced for a PTD1 dictionary.
https://github.com/danbri/factoidal-core/issues/634
-/
import L4Factoidal.Storage.TermLocalIndexLookupTheorems
import L4Factoidal.Storage.TermLocalIndexWireTheorems

namespace L4Factoidal.Storage.TermLocalIndexWire

open L4Factoidal.RDF
open L4Factoidal.Storage.TermLocalIndex

/-- Kind: order invariant.
    Says: the TLI1 adjacency check places every earlier entry strictly before
    every later entry in lexicographic byte order.
    Does not say: a particular dictionary or page passes the check. -/
theorem strictlyIncreasing_pairwise_key_lt (entries : List Entry)
    (ordered : strictlyIncreasing entries = true) :
    entries.Pairwise (fun a b => a.key < b.key) := by
  have byteOrder (xs ys : List UInt8) : lessKey xs ys = true ↔ xs < ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp [lessKey]
    | cons x xs ih =>
      cases ys with
      | nil => simp [lessKey]
      | cons y ys =>
        by_cases lt : x < y
        · simp [lessKey, lt, List.cons_lt_cons_iff]
        · by_cases eq : x = y
          · subst y
            simp [lessKey, lt, List.cons_lt_cons_iff, ih]
          · simp [lessKey, lt, eq, List.cons_lt_cons_iff]
  induction entries with
  | nil => exact .nil
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      change (lessKey x.key y.key && strictlyIncreasing (y :: ys)) = true at ordered
      obtain ⟨adjacent, rest⟩ := Bool.and_eq_true_iff.mp ordered
      have first := (byteOrder x.key y.key).mp adjacent
      have tail := ih rest
      refine List.Pairwise.cons ?_ tail
      intro z member
      rcases List.mem_cons.mp member with eq | later
      · subst z; exact first
      · exact List.lt_trans first (List.rel_of_pairwise_cons tail later)

/-- Kind: producer and search refinement.
    Says: successful full TLI1 encoding of the built index makes lookup of
    every original PTD1 entry return that entry's original dictionary ID.
    Does not say: every dictionary fits the wire format or the range reader
    chose a page containing the term. -/
theorem lookup_entriesOf_at_of_encode? (terms : Array Term) (target bytes : ByteArray)
    (encoded : encode? ⟨target, entriesOf terms⟩ = some bytes)
    (id : Nat) (inRange : id < terms.size) :
    lookup? (entriesOf terms) terms[id] = some id := by
  let entries := entriesOf terms
  have ordered : strictlyIncreasing entries.toList = true := by
    simp only [encode?] at encoded
    split at encoded <;> try contradiction
    split at encoded <;> try contradiction
    rename_i passed
    simpa [entries] using passed
  have sorted := strictlyIncreasing_pairwise_key_lt entries.toList ordered
  have increasing (j k : Nat) (hj : j < entries.size) (hk : k < entries.size) (lt : j < k) :
      entries[j].key < entries[k].key := by
    simpa only [Array.getElem_toList] using
      (List.pairwise_iff_getElem.mp sorted j k (by simpa using hj) (by simpa using hk) lt)
  let original : Entry := ⟨serializeTerm terms[id], terms[id], id⟩
  have member : original ∈ entries :=
    (mem_entriesOf_iff terms original).mpr ⟨Array.getElem?_eq_getElem inRange, rfl⟩
  obtain ⟨k, hk, atK⟩ := Array.mem_iff_getElem.mp member
  have keyMatch : entries[k].key = serializeTerm (TermFold.foldTerm terms[id]) := by
    simpa only [TermFold.foldTerm_eq_self] using congrArg Entry.key atK
  have termMatch : entries[k].term = TermFold.foldTerm terms[id] := by
    simpa only [TermFold.foldTerm_eq_self] using congrArg Entry.term atK
  have cut (j : Nat) (hj : j < entries.size) :
      entries[j].key < serializeTerm (TermFold.foldTerm terms[id]) ↔ j < k := by
    rw [← keyMatch]
    constructor
    · intro less
      rcases Nat.lt_trichotomy j k with before | same | after
      · exact before
      · subst j
        exact False.elim (List.lt_irrefl _ less)
      · exact False.elim (List.lt_asymm (increasing k j hk hj after) less)
    · exact increasing j k hj hk
  exact (lookup?_eq_some_of_key_cut entries terms[id] k hk cut keyMatch termMatch).trans
    (congrArg (fun e : Entry => some e.localId) atK)

/-- Kind: full wire decoder and lookup refinement.
    Says: after successful encoding, searching the complete decoded TLI1
    index returns the direct PTD1 first ID or the same absence for every RDF term.
    Does not say: a selective page lookup, verified range read or complete
    persistent SPARQL query returns its reference result. -/
theorem decode_lookup_entriesOf_eq_findTermId? (terms : Array Term) (target bytes : ByteArray)
    (encoded : encode? ⟨target, entriesOf terms⟩ = some bytes) (wanted : Term) :
    (decode? bytes).bind (fun index => lookup? index.entries wanted) =
      PagedTermDictionary.findTermId? terms wanted := by
  rw [decode?_encode? _ bytes encoded]
  change lookup? (entriesOf terms) wanted = PagedTermDictionary.findTermId? terms wanted
  cases reference : PagedTermDictionary.findTermId? terms wanted with
  | none =>
    cases indexed : lookup? (entriesOf terms) wanted with
    | none => rfl
    | some id =>
      have miss : terms.findIdx? (fun t => TermFold.foldTerm t == TermFold.foldTerm wanted) = none :=
        reference
      have present := Array.mem_of_getElem? (lookup_entriesOf_sound terms wanted id indexed)
      have absent := (Array.findIdx?_eq_none_iff.mp miss) wanted present
      simpa using absent
  | some id =>
    have hit : terms.findIdx? (fun t => TermFold.foldTerm t == TermFold.foldTerm wanted) = some id :=
      reference
    obtain ⟨inRange, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hit
    have atId : terms[id] = wanted := by
      simpa only [TermFold.foldTerm_eq_self, beq_iff_eq] using same
    simpa only [atId] using lookup_entriesOf_at_of_encode? terms target bytes encoded id inRange

#print axioms L4Factoidal.Storage.TermLocalIndex.lookup?_eq_some_of_key_cut
#print axioms L4Factoidal.Storage.TermLocalIndexWire.strictlyIncreasing_pairwise_key_lt
#print axioms L4Factoidal.Storage.TermLocalIndexWire.lookup_entriesOf_at_of_encode?
#print axioms L4Factoidal.Storage.TermLocalIndexWire.decode_lookup_entriesOf_eq_findTermId?

end L4Factoidal.Storage.TermLocalIndexWire
