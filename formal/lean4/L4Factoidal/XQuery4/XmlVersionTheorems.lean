/-
L4Factoidal.XQuery4.XmlVersionTheorems — the XML 1.1 setting of the
XQuery 4.0 grammar (`Env.xml11`, `Cfg.xml11`) changes nothing for a
query written only in XML 1.0 terms.

Proved here (no `sorry`, no new axioms):

* `normalizeLineEnds_agree` — the XML 1.1 end-of-line handling (XQuery
  4.0 §A.3.3.2) and the XML 1.0 handling (§A.3.3.1) give the same text
  when the query holds no NEL (#x85) and no LINE SEPARATOR (#x2028).
* `normalizeLineEnds_no_cr` — after either handling, the text holds no
  CR (#xD).
* `isXmlCharV_false`, `isXmlCharV_of_xml10` — a character reference that
  the XML 1.0 grammar reads is read the same way with XML 1.1: the XML
  1.1 `Char` class contains the XML 1.0 one (XML 1.1 §2.2), so the
  XQST0090 check only admits more.
* `isXmlCharV_true_eq` — the XML 1.1 class of the grammar is
  `XML.isXml11CharCode` of the project's XML parser.
-/
import L4Factoidal.XQuery4.Module
import L4Factoidal.XML.Document

namespace L4Factoidal.XQuery4.XmlVersionTheorems

open L4Factoidal.XQuery4

theorem go_agree (cs acc : List Char)
    (h : ∀ c ∈ cs, c ≠ '\u0085' ∧ c ≠ '\u2028') :
    normalizeLineEnds.go true cs acc = normalizeLineEnds.go false cs acc := by
  induction cs, acc using normalizeLineEnds.go.induct true with
  | case1 acc => simp [normalizeLineEnds.go]
  | case2 r acc ih =>
    simp only [normalizeLineEnds.go]
    exact ih (fun c hc => h c (by simp [hc]))
  | case3 c r acc _ htrue _ =>
    have := (h c (by simp)).1
    simp at htrue
    exact absurd htrue this
  | case4 c r acc hcn hnot ih =>
    have hc := (h c (by simp)).1
    have e1 : normalizeLineEnds.go true ('\r' :: c :: r) acc = normalizeLineEnds.go true (c :: r) ('\n' :: acc) := by
      rw [normalizeLineEnds.go] <;> first | exact hcn | simp [hc]
    have e2 : normalizeLineEnds.go false ('\r' :: c :: r) acc = normalizeLineEnds.go false (c :: r) ('\n' :: acc) := by
      rw [normalizeLineEnds.go] <;> first | exact hcn | simp
    rw [e1, e2]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
  | case5 acc ih =>
    simp only [normalizeLineEnds.go]
  | case6 c r acc _ _ _ htrue _ =>
    have := h c (by simp)
    simp at htrue
    rcases htrue with h1 | h1
    · exact absurd h1 this.1
    · exact absurd h1 this.2
  | case7 c r acc n1 n2 n3 hnot ih =>
    have hc := h c (by simp)
    have e1 : normalizeLineEnds.go true (c :: r) acc = normalizeLineEnds.go true r (c :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    have e2 : normalizeLineEnds.go false (c :: r) acc = normalizeLineEnds.go false r (c :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    rw [e1, e2]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem normalizeLineEnds_agree (cs : List Char)
    (h : ∀ c ∈ cs, c ≠ '\u0085' ∧ c ≠ '\u2028') :
    normalizeLineEnds true cs = normalizeLineEnds false cs :=
  go_agree cs [] h

theorem go_no_cr (b : Bool) (cs acc : List Char) (hacc : '\r' ∉ acc) :
    '\r' ∉ normalizeLineEnds.go b cs acc := by
  induction cs, acc using normalizeLineEnds.go.induct b with
  | case1 acc => simpa [normalizeLineEnds.go] using hacc
  | case2 r acc ih =>
    simp only [normalizeLineEnds.go]
    exact ih (by simp [hacc])
  | case3 c r acc hcn htrue ih =>
    have e : normalizeLineEnds.go b ('\r' :: c :: r) acc = normalizeLineEnds.go b r ('\n' :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    rw [e]; exact ih (by simp [hacc])
  | case4 c r acc hcn hnot ih =>
    have e : normalizeLineEnds.go b ('\r' :: c :: r) acc = normalizeLineEnds.go b (c :: r) ('\n' :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    rw [e]; exact ih (by simp [hacc])
  | case5 acc ih =>
    simp only [normalizeLineEnds.go]
    exact ih (by simp [hacc])
  | case6 c r acc n1 n2 n3 htrue ih =>
    have e : normalizeLineEnds.go b (c :: r) acc = normalizeLineEnds.go b r ('\n' :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    rw [e]; exact ih (by simp [hacc])
  | case7 c r acc n1 n2 n3 hnot ih =>
    have e : normalizeLineEnds.go b (c :: r) acc = normalizeLineEnds.go b r (c :: acc) := by
      rw [normalizeLineEnds.go] <;> simp_all
    have hc : c ≠ '\r' := by
      intro hc
      cases r with
      | nil => exact n3 hc rfl
      | cons d r' => exact n2 d r' hc rfl
    rw [e]; exact ih (by simp [hacc, Ne.symm hc])

/-- After either end-of-line handling the query holds no CR. -/
theorem normalizeLineEnds_no_cr (b : Bool) (cs : List Char) :
    '\r' ∉ normalizeLineEnds b cs :=
  go_no_cr b cs [] (by simp)

theorem isXmlCharV_false (n : Nat) : isXmlCharV false n = isXmlChar n := rfl

theorem isXmlCharV_true_eq (n : Nat) : isXmlCharV true n = L4Factoidal.XML.isXml11CharCode n := rfl

theorem isXmlCharV_of_xml10 (n : Nat) (h : isXmlChar n = true) : isXmlCharV true n = true := by
  unfold isXmlChar at h
  simp only [isXmlCharV, if_true]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  omega

end L4Factoidal.XQuery4.XmlVersionTheorems
