/-
L4Factoidal.RDF.DictInjective — the contract of the term dictionary of an
id-based store (https://github.com/danbri/factoidal/issues/975, step 2).

An id-based store keeps ids in its rows and maps them to RDF terms with a
dictionary. The abstraction of such a store is "decode after denote": the
quads of the store are the rows with each id replaced by its term. That
abstraction is faithful only when the dictionary is injective on the ids that
the store uses and encoding and decoding are inverse there.

`DictInjective enc dec dom used` states this for

* `enc : Term → Option Nat`, the id of a term (`none`: the term has no id);
* `dec : Nat → Option Term`, the term of an id (`none`: the id names no term);
* `dom : Term → Prop`, the terms the store holds;
* `used : Nat → Prop`, the ids that occur in the store.

The fields:

* `covers`: every term of the store has an id, and that id is in use;
* `encInj` (item (a) of step 2): two terms of the store with the same id are
  the same term;
* `decInj` (item (b)): two ids in use that decode to the same term are the
  same id, so a term never has two ids;
* `decEnc` (item (c), first half): `dec (enc t) = t` for a term of the store;
* `encDec` (item (c), second half): every id in use decodes to a term of the
  store, and `enc (dec i) = i`.

The record is stated for any entry type `α`; for RDF terms `α` is `Term`, and
an IBK5 dictionary holds `TermWireV2.WireTerm`. Term equality here is `Eq` on
`α` (structural; RDF 1.1 Concepts section 3, strict term equality). A store that folds language tags to lower case
(RDF 1.1 Concepts section 3.3) states its `dom` over the folded terms, and
proves separately that its lookup folds the tag first and that one id means
`Term.eqb`; see `Storage/Sbm11/DictInjectiveTheorems.lean` and, for the
other stores (https://github.com/danbri/factoidal/issues/977),
`Storage/TermFoldTheorems.lean` and `Storage/StoreDictTheorems.lean`.

`DictInjective.ofRoundTrip` builds the record from `covers`, `decEnc` and
`encDec`: (a) and (b) follow from the round trips because `enc` and `dec` are
functions.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RDF

/-- The term dictionary of an id-based store is injective on the ids in use,
    and encoding and decoding are inverse there. -/
structure DictInjective {α : Type} (enc : α → Option Nat) (dec : Nat → Option α)
    (dom : α → Prop) (used : Nat → Prop) : Prop where
  /-- Every term of the store has an id in use. -/
  covers : ∀ t, dom t → ∃ n, used n ∧ enc t = some n
  /-- (a) Two terms of the store with one id are one term. -/
  encInj : ∀ t u n, dom t → dom u → enc t = some n → enc u = some n → t = u
  /-- (b) Two ids in use with one term are one id. -/
  decInj : ∀ n m t, used n → used m → dec n = some t → dec m = some t → n = m
  /-- (c) The term of the id of a term of the store is that term. -/
  decEnc : ∀ t n, dom t → enc t = some n → dec n = some t
  /-- (c) An id in use is the id of its term, and that term is in the store. -/
  encDec : ∀ n, used n → ∃ t, dom t ∧ dec n = some t ∧ enc t = some n

namespace DictInjective

variable {α : Type} {enc : α → Option Nat} {dec : Nat → Option α} {dom : α → Prop} {used : Nat → Prop}

/-- The record from the two round trips and `covers`. -/
theorem ofRoundTrip
    (hcov : ∀ t, dom t → ∃ n, used n ∧ enc t = some n)
    (hde : ∀ t n, dom t → enc t = some n → dec n = some t)
    (hed : ∀ n, used n → ∃ t, dom t ∧ dec n = some t ∧ enc t = some n) :
    DictInjective enc dec dom used where
  covers := hcov
  encInj t u n ht hu h1 h2 := by
    have e1 := hde t n ht h1
    have e2 := hde u n hu h2
    rw [e1] at e2
    exact Option.some.inj e2
  decInj n m t hn hm h1 h2 := by
    obtain ⟨t1, _, d1, e1⟩ := hed n hn
    obtain ⟨t2, _, d2, e2⟩ := hed m hm
    rw [h1] at d1
    rw [h2] at d2
    cases Option.some.inj d1
    cases Option.some.inj d2
    rw [e1] at e2
    exact Option.some.inj e2
  decEnc := hde
  encDec := hed

/-- Two terms of the store have the same id exactly when they are the same
    term. -/
theorem enc_eq_iff (D : DictInjective enc dec dom used) {t u : α} {n m : Nat}
    (ht : dom t) (hu : dom u) (h1 : enc t = some n) (h2 : enc u = some m) : n = m ↔ t = u := by
  constructor
  · intro e
    subst e
    exact D.encInj t u n ht hu h1 h2
  · intro e
    subst e
    rw [h1] at h2
    exact Option.some.inj h2

/-- Two ids in use name the same term exactly when they are the same id. -/
theorem dec_eq_iff (D : DictInjective enc dec dom used) {n m : Nat} {t u : α}
    (hn : used n) (hm : used m) (h1 : dec n = some t) (h2 : dec m = some u) : t = u ↔ n = m := by
  constructor
  · intro e
    subst e
    exact D.decInj n m t hn hm h1 h2
  · intro e
    subst e
    rw [h1] at h2
    exact Option.some.inj h2

/-- The record for a dictionary whose terms are the terms of its ids in use,
    from one fact checked over the ids: every id in use decodes to a term that
    encodes back to it. (For a dictionary read from a file written by another
    tool, such as HDT, this is a test over the whole file.) -/
theorem ofDecodeCert (hc : ∀ n, used n → ∃ t, dec n = some t ∧ enc t = some n) :
    DictInjective enc dec (fun t => ∃ n, used n ∧ dec n = some t) used := by
  refine ofRoundTrip (fun t ⟨n, hn, hd⟩ => ?_) (fun t m ⟨n, hn, hd⟩ he => ?_) (fun n hn => ?_)
  · obtain ⟨u, hu, he⟩ := hc n hn
    rw [hd] at hu
    cases Option.some.inj hu
    exact ⟨n, hn, he⟩
  · obtain ⟨u, hu, he'⟩ := hc n hn
    rw [hd] at hu
    cases Option.some.inj hu
    rw [he'] at he
    cases Option.some.inj he
    exact hd
  · obtain ⟨t, hd, he⟩ := hc n hn
    exact ⟨t, ⟨n, hn, hd⟩, hd, he⟩

/-- A lookup that agrees with the lookup of a `DictInjective` dictionary on
    the terms of the store gives a `DictInjective` dictionary: the record
    reads `enc` only at those terms. -/
theorem congr_on {enc' : α → Option Nat} (D : DictInjective enc dec dom used)
    (h : ∀ t, dom t → enc' t = enc t) : DictInjective enc' dec dom used where
  covers t ht := by rw [h t ht]; exact D.covers t ht
  encInj t u n ht hu h1 h2 := D.encInj t u n ht hu (by rw [← h t ht]; exact h1) (by rw [← h u hu]; exact h2)
  decInj := D.decInj
  decEnc t n ht he := D.decEnc t n ht (by rw [← h t ht]; exact he)
  encDec n hn := by
    obtain ⟨t, ht, hd, he⟩ := D.encDec n hn
    exact ⟨t, ht, hd, by rw [h t ht]; exact he⟩

end DictInjective

/-! ## A dictionary that is a list without duplicates -/

/-- In a list without duplicates, the index of the entry at `i` is `i`. -/
theorem idxOf_getElem_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), l.Nodup → l.idxOf l[i] = i
  | [], _, hi, _ => by simp at hi
  | b :: l, 0, _, _ => by simp
  | b :: l, i + 1, hi, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    have hi' : i < l.length := by simpa using hi
    have hne : (b == l[i]) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro e
      exact hnd'.1 (e ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ, List.idxOf_cons, hne, cond_false]
    rw [idxOf_getElem_of_nodup l i hi' hnd'.2]

/-- The id of a term in a list dictionary: its position. -/
def listEnc {α : Type} [DecidableEq α] (l : List α) (t : α) : Option Nat :=
  if t ∈ l then some (l.idxOf t) else none

/-- The term of an id in a list dictionary: the entry at that position. -/
def listDec {α : Type} (l : List α) (n : Nat) : Option α := l[n]?

/-- A list dictionary without duplicates is `DictInjective` on its entries
    and its positions. -/
theorem listDict_dictInjective {α : Type} [DecidableEq α] (l : List α) (h : l.Nodup) :
    DictInjective (listEnc l) (listDec l) (· ∈ l) (· < l.length) := by
  have hde : ∀ t n, t ∈ l → listEnc l t = some n → listDec l n = some t := by
    intro t n hm he
    unfold listEnc at he
    rw [if_pos hm] at he
    cases Option.some.inj he
    have hl : l.idxOf t < l.length := List.idxOf_lt_length_iff.mpr hm
    unfold listDec
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]
  have hed : ∀ n, n < l.length → ∃ t, t ∈ l ∧ listDec l n = some t ∧ listEnc l t = some n := by
    intro n hn
    refine ⟨l[n], List.getElem_mem hn, ?_, ?_⟩
    · unfold listDec; rw [List.getElem?_eq_getElem hn]
    · unfold listEnc; rw [if_pos (List.getElem_mem hn), idxOf_getElem_of_nodup l n hn h]
  refine DictInjective.ofRoundTrip (fun t hm => ?_) hde hed
  have hl : l.idxOf t < l.length := List.idxOf_lt_length_iff.mpr hm
  exact ⟨l.idxOf t, hl, by unfold listEnc; rw [if_pos hm]⟩

end L4Factoidal.RDF
