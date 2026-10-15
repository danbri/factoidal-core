/-
L4Factoidal.Storage.Sbm11.TermKeyFast — the term of a dictionary key read
from a range of a byte array, without the lists of the specification
(https://github.com/danbri/factoidal/issues/825; record
docs/designissues/2026-10-12-sbm11-stage4.md section 15).

`Session.termOf` used to copy the key's bytes (`ByteArray.extract`), turn them
into a `List UInt8` (one cell per byte), and give the list to `decodeKey?`,
which copies it again for `String.fromUTF8?`. For a DBpedia IRI of 40 bytes
that is three passes and 82 allocations before the string exists. The decoder
here reads the class byte at `a` and gives the body, `buf[a + 1, e)`, to
`String.fromUTF8?` at once, for the classes that are the bulk of a dictionary:
blank nodes (1), IRIs (2) and `xsd:string` literals (3). Every other class, and
every range that is not inside the array, goes to `decodeKey?` on the list of
the range, so the theorem needs no case analysis for them.

`decodeKeySlice?_eq`: for every array and range, `decodeKeySlice? buf a e` is
`decodeKey?` of the list of the bytes `buf[a, e)`. `classTagSlice_eq`: the same
for the tag of the key's class.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermId

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF

/-- The bytes `buf[a, e)` as a list: the key the specification reads. -/
def sliceList (buf : ByteArray) (a e : Nat) : List UInt8 := (buf.extract a e).data.toList

/-- The range is a non-empty range inside the array. -/
@[inline] def sliceOk (buf : ByteArray) (a e : Nat) : Bool := a < e && e ≤ buf.size

/-- The term of the key `buf[a, e)`. -/
def decodeKeySlice? (buf : ByteArray) (a e : Nat) : Option Term :=
  if sliceOk buf a e then
    let c := buf.get! a
    if c == classBnode then (String.fromUTF8? (buf.extract (a + 1) e)).map Term.bnode
    else if c == classIri then
      match String.fromUTF8? (buf.extract (a + 1) e) with
      | none => none
      | some s => if h : isIri s then some (.iri ⟨s, h⟩) else none
    else if c == classString then
      (String.fromUTF8? (buf.extract (a + 1) e)).map fun s => .literal (Literal.string s)
    else decodeKey? (sliceList buf a e)
  else decodeKey? (sliceList buf a e)

/-- The tag of the class of the key `buf[a, e)`. -/
def classTagSlice (buf : ByteArray) (a e : Nat) : Nat :=
  if sliceOk buf a e then classTagOfByte (buf.get! a) else classTag (sliceList buf a e)

/-- Inside the array, the list of `buf[a, e)` is the byte at `a` and the list of
`buf[a + 1, e)`. -/
theorem sliceList_cons (buf : ByteArray) (a e : Nat) (h : sliceOk buf a e = true) :
    sliceList buf a e = buf.get! a :: sliceList buf (a + 1) e := by
  simp only [sliceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hae, hes⟩ := h
  have hlt : a < buf.data.size := by
    have := ByteArray.size_data (a := buf)
    omega
  unfold sliceList
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  have hdrop : buf.data.toList.drop a = buf.data.toList[a]'(by simpa using hlt) :: buf.data.toList.drop (a + 1) :=
    List.drop_eq_getElem_cons (by simpa using hlt)
  have hn : e - a = (e - (a + 1)) + 1 := by omega
  rw [hdrop, hn, List.take_succ_cons]
  congr 1
  simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getElem?_eq_getElem hlt]

/-- The string of a range is `String.fromUTF8?` of the range. -/
theorem stringOfBytes_slice (buf : ByteArray) (a e : Nat) :
    L4Factoidal.Storage.stringOfBytes? (sliceList buf a e) = String.fromUTF8? (buf.extract a e) := by
  unfold L4Factoidal.Storage.stringOfBytes? sliceList
  rw [Array.toArray_toList]

theorem decodeKeySlice?_eq (buf : ByteArray) (a e : Nat) :
    decodeKeySlice? buf a e = decodeKey? (sliceList buf a e) := by
  unfold decodeKeySlice?
  by_cases h : sliceOk buf a e = true
  · simp only [h, if_true]
    rw [sliceList_cons buf a e h]
    have hs := stringOfBytes_slice buf (a + 1) e
    generalize buf.get! a = c
    generalize sliceList buf (a + 1) e = rest at hs ⊢
    generalize String.fromUTF8? (buf.extract (a + 1) e) = r at hs ⊢
    by_cases hb : (c == classBnode) = true
    · have hc : c = classBnode := by simpa using hb
      subst hc
      simp [decodeKey?, decodeAtom?, classBnode, classTriple, hs]
    · by_cases hi : (c == classIri) = true
      · have hc : c = classIri := by simpa using hi
        subst hc
        simp only [decodeKey?, decodeAtom?, decodeIri?, hs, classBnode, classIri, classTriple,
          beq_self_eq_true, if_true]
        cases r <;> simp
      · by_cases hst : (c == classString) = true
        · have hc : c = classString := by simpa using hst
          subst hc
          simp [decodeKey?, decodeAtom?, classBnode, classIri, classString, classTriple, hs]
        · simp [hb, hi, hst]
  · simp [h]

theorem classTagSlice_eq (buf : ByteArray) (a e : Nat) :
    classTagSlice buf a e = classTag (sliceList buf a e) := by
  unfold classTagSlice
  by_cases h : sliceOk buf a e = true
  · simp only [h, if_true]
    rw [sliceList_cons buf a e h]
    rfl
  · simp [h]

#print axioms sliceList_cons
#print axioms stringOfBytes_slice
#print axioms decodeKeySlice?_eq
#print axioms classTagSlice_eq

end L4Factoidal.Storage.Sbm11
