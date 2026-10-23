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
blank nodes (1), IRIs (2) and `xsd:string` literals (3), and, since stage 1k
of docs/designissues/2026-10-12-parallel-block-scans.md, language-tagged
literals (4: `decodeLangSlice`, the last `0x00` found by `lastZeroGo` and the
two parts given to `String.fromUTF8?`). Every other class, and
every range that is not inside the array, goes to `decodeKey?` on the list of
the range, so the theorem needs no case analysis for them.

`decodeKeySlice?_eq`: for every array and range, `decodeKeySlice? buf a e` is
`decodeKey?` of the list of the bytes `buf[a, e)` (for class 4 through
`decodeLangSlice_eq` and `lastZeroGo_spec`). `classTagSlice_eq`: the same
for the tag of the key's class.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.TermKeyTheorems

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF

/-- The bytes `buf[a, e)` as a list: the key the specification reads. -/
def sliceList (buf : ByteArray) (a e : Nat) : List UInt8 := (buf.extract a e).data.toList

/-- The range is a non-empty range inside the array. -/
@[inline] def sliceOk (buf : ByteArray) (a e : Nat) : Bool := a < e && e ≤ buf.size


/-- The last `0x00` of `buf[lo, i)`: the largest `z` with `lo ≤ z < i` and
    `buf[z] = 0`, looked for from `i - 1` down (fuel `f`; a tail call per
    byte). `lastZeroGo_spec`: it is where `splitLast` cuts the list. -/
def lastZeroGo (buf : ByteArray) (lo : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, i =>
    if i ≤ lo then none
    else if buf.get! (i - 1) == 0 then some (i - 1)
    else lastZeroGo buf lo f (i - 1)

/-- The term of a class 4 (`rdf:langString`) key `buf[a, e)`: the body is
    lexical form, `0x00`, tag, and the tag has no `0x00`, so the separator is
    the last one (`lastZeroGo`). Stage 1k: the list form (`decodeLang?` on the
    list of the key) took most of olympics q07's ORDER BY keys (291 labels,
    about 0.3 ms: the list of the key, `splitLast` with two reversals, and
    the UTF-8 checks over lists). `decodeLangSlice_eq`: it is `decodeLang?`
    of the list of the body. -/
def decodeLangSlice (buf : ByteArray) (a e : Nat) : Option Term :=
  match lastZeroGo buf (a + 1) (e - (a + 1)) e with
  | none => none
  | some z =>
    match String.fromUTF8? (buf.extract (a + 1) z), String.fromUTF8? (buf.extract (z + 1) e) with
    | some lex, some tag =>
        if tagAdmitted tag then mkLit lex rdfLangString.val (some tag) none else none
    | _, _ => none

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
    else if c == classLang then decodeLangSlice buf a e
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

theorem sliceList_append (buf : ByteArray) {a m e : Nat} (ham : a ≤ m) (hme : m ≤ e) :
    sliceList buf a e = sliceList buf a m ++ sliceList buf m e := by
  unfold sliceList
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  have : e - a = (m - a) + (e - m) := by omega
  rw [this, List.take_add, List.drop_drop, Nat.add_sub_cancel' ham]

theorem sliceList_nil (buf : ByteArray) (a : Nat) : sliceList buf a a = [] := by
  simp [sliceList]

theorem sliceList_one (buf : ByteArray) (i : Nat) (h : i < buf.size) :
    sliceList buf i (i + 1) = [buf.get! i] := by
  have hok : sliceOk buf i (i + 1) = true := by simp [sliceOk]; omega
  rw [sliceList_cons buf i (i + 1) hok, sliceList_nil]

theorem splitLast_none (l : List UInt8) (h : noZero l = true) : splitLast l = none := by
  have hgo : ∀ acc (l : List UInt8), noZero l = true → splitFirstGo acc l = none := by
    intro acc l hl
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      simp only [noZero, List.all_cons, Bool.and_eq_true] at hl
      have hx : (x == 0) = false := by simpa using hl.1
      simp only [splitFirstGo, hx, Bool.false_eq_true, if_false]
      exact ih _ hl.2
  have hr : noZero l.reverse = true := by rw [noZero_reverse]; exact h
  simp [splitLast, splitFirst, hgo [] _ hr]

theorem lastZeroGo_spec (buf : ByteArray) (lo e : Nat) (he : e ≤ buf.size) :
    ∀ f i, lo ≤ i → i ≤ e → i - lo ≤ f → noZero (sliceList buf i e) = true →
      splitLast (sliceList buf lo e)
        = (lastZeroGo buf lo f i).map (fun z => (sliceList buf lo z, sliceList buf (z + 1) e)) := by
  intro f
  induction f with
  | zero =>
    intro i hli hie hf hz
    have : i = lo := by omega
    subst this
    simp [lastZeroGo, splitLast_none _ hz]
  | succ f ih =>
    intro i hli hie hf hz
    unfold lastZeroGo
    by_cases hil : i ≤ lo
    · have : i = lo := by omega
      subst this
      simp [splitLast_none _ hz]
    · simp only [hil, if_false]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hj : j < buf.size := by omega
      have hcell : sliceList buf j e = buf.get! j :: sliceList buf (j + 1) e := by
        rw [sliceList_append buf (a := j) (m := j + 1) (by omega) hie, sliceList_one buf j hj]
        simp
      have hsplit : sliceList buf lo e = sliceList buf lo j ++ buf.get! j :: sliceList buf (j + 1) e := by
        rw [sliceList_append buf (m := j) (by omega) (by omega), hcell]
      by_cases hb : (buf.get! j == 0) = true
      · simp only [hb, if_true, Option.map_some]
        have hb0 : buf.get! j = 0 := by simpa using hb
        rw [hsplit, hb0, splitLast_append _ _ hz]
      · simp only [hb, Bool.false_eq_true, if_false]
        apply ih j (by omega) (by omega) (by omega)
        rw [hcell]
        simp only [noZero, List.all_cons, Bool.and_eq_true]
        exact ⟨by simpa using hb, by simpa [noZero] using hz⟩


theorem decodeLangSlice_eq (buf : ByteArray) (a e : Nat) (h : sliceOk buf a e = true) :
    decodeLangSlice buf a e = decodeLang? (sliceList buf (a + 1) e) := by
  simp only [sliceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs := lastZeroGo_spec buf (a + 1) e h.2 (e - (a + 1)) e (by omega) (Nat.le_refl _) (by omega)
    (by rw [sliceList_nil]; rfl)
  unfold decodeLangSlice decodeLang?
  rw [hs]
  cases lastZeroGo buf (a + 1) (e - (a + 1)) e with
  | none => rfl
  | some z =>
    simp only [Option.map_some, stringOfBytes_slice]
    rfl

theorem decodeKeySlice?_eq (buf : ByteArray) (a e : Nat) :
    decodeKeySlice? buf a e = decodeKey? (sliceList buf a e) := by
  unfold decodeKeySlice?
  by_cases h : sliceOk buf a e = true
  · simp only [h, if_true]
    have hl := decodeLangSlice_eq buf a e h
    rw [sliceList_cons buf a e h]
    have hs := stringOfBytes_slice buf (a + 1) e
    generalize buf.get! a = c
    generalize decodeLangSlice buf a e = r4 at hl ⊢
    generalize sliceList buf (a + 1) e = rest at hs hl ⊢
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
        · by_cases hla : (c == classLang) = true
          · have hc : c = classLang := by simpa using hla
            subst hc
            simp [decodeKey?, decodeAtom?, classBnode, classIri, classString, classLang, classTriple, hl]
          · simp [hb, hi, hst, hla]
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
#print axioms lastZeroGo_spec
#print axioms decodeLangSlice_eq
#print axioms decodeKeySlice?_eq
#print axioms classTagSlice_eq

end L4Factoidal.Storage.Sbm11
