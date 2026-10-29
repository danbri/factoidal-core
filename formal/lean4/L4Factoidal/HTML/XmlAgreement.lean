/-
L4Factoidal.HTML.XmlAgreement — where the HTML parser (WHATWG HTML Living
Standard, §13.2, snapshot whatwg/html `93967771`, 26 October 2026) and the XML
parser (XML 1.0 Fifth Edition, `L4Factoidal/XML/Parser.lean`) are connected
(https://github.com/danbri/factoidal/issues/1167, milestone 5).

Proved here:

1. `htmlNewlines_eq_xml10LineEndings`: the newline normalisation of the HTML input
   stream (§13.2.3.5) is XML 1.0 §2.11 end-of-line handling
   (`XML.normalizeLineEndings`), on every input.
2. `numericRef_agrees_xml`: for a numeric character reference to a code point
   that the HTML syntax allows (§13.1.4: not U+0000, not U+000D, not a
   surrogate, not a noncharacter, not a control other than ASCII whitespace) and
   that is at most U+10FFFF, the HTML tokenizer gives the same one-character
   string as the XML parser (`XML.codepointToString`), and no parse error.
   Outside these code points the two specifications differ (for example
   `&#x80;` is U+20AC in HTML and U+0080 in XML), and those references are not
   allowed in an HTML document that conforms.

Measured, not proved: the whole tree. `xhtmlTree` maps the HTML parser's arena
to `XML.Node`, and `Harness/Html5lib.lean` (`l4html5lib agree`) compares it with
the XML parser's document element on generated documents that are well-formed
XML and that the HTML parser reads with no parse error. A theorem for the whole
parser is ISSUE_WHOLE.
-/
import L4Factoidal.HTML.TreeBuilder
import L4Factoidal.XML.Parser

namespace L4Factoidal.HTML

/-! ## 1. Newline normalisation -/

theorem normalizeNewlinesList_eq_xml10 (cs : List Char) :
    normalizeNewlinesList cs = XML.normalizeLineEndings cs := by
  fun_induction normalizeNewlinesList cs with
  | case1 rest ih => simp [XML.normalizeLineEndings, ih]
  | case2 rest h ih =>
    rw [ih]
    conv => rhs; rw [XML.normalizeLineEndings.eq_def]
    split
    · rename_i heq
      simp only [List.cons.injEq, true_and] at heq
      exact absurd heq (h _)
    · rename_i heq
      simp only [List.cons.injEq] at heq
      rw [heq.2]
    · rename_i hne heq
      simp only [List.cons.injEq] at heq
      exact absurd heq.1.symm hne
    · rename_i heq
      exact absurd heq (by simp)
  | case3 c rest h1 h2 ih =>
    rw [ih]
    conv => rhs; rw [XML.normalizeLineEndings.eq_def]
    split
    · rename_i r _ heq
      simp only [List.cons.injEq] at heq
      exact absurd heq.1 h2
    · rename_i r heq
      simp only [List.cons.injEq] at heq
      exact absurd heq.1 h2
    · rename_i hne _ heq
      simp only [List.cons.injEq] at heq
      rw [heq.1, heq.2]
    · rename_i heq
      exact absurd heq (by simp)
  | case4 => simp [XML.normalizeLineEndings]

/-- The HTML input stream after preprocessing is the XML 1.0 §2.11 line-end
normalisation of the same characters. -/
theorem htmlNewlines_eq_xml10LineEndings (s : String) :
    (normalizeNewlines s).toList = XML.normalizeLineEndings s.toList := by
  simp [normalizeNewlines, normalizeNewlinesList_eq_xml10]

/-! ## 2. Numeric character references -/

/-- A code point that the HTML syntax allows in a numeric character reference
(§13.1.4) and that XML 1.0 `[2] Char` also allows as text. -/
def htmlRefAllowed (n : Nat) : Prop :=
  0 < n ∧ n ≤ 0x10FFFF ∧ ¬(0xD800 ≤ n ∧ n ≤ 0xDFFF) ∧ isNonCharacter n = false
    ∧ isControlCp n = false ∧ n ≠ 0x0D

theorem numericRef_allowed (n : Nat) (h : htmlRefAllowed n) :
    numericRef n = (Char.ofNat n, []) := by
  obtain ⟨h0, hmax, hsur, hnc, hctl, hcr⟩ := h
  have hc1 : ¬(0x80 ≤ n ∧ n ≤ 0x9F) := by
    intro ⟨a, b⟩
    simp only [isControlCp, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hctl
    omega
  have hn0 : n ≠ 0 := by omega
  have hmax' : ¬(n > 0x10FFFF) := by omega
  unfold numericRef
  simp only [beq_iff_eq, hn0, if_false, hmax', hnc, hctl]
  simp only [decide_eq_true_eq, Bool.and_eq_true, hsur, if_false]
  simp [hc1, hcr]

/-- The HTML tokenizer and the XML parser give the same character for a numeric
character reference to an allowed code point, and HTML reports no error. -/
theorem numericRef_agrees_xml (n : Nat) (h : htmlRefAllowed n) :
    String.singleton (numericRef n).1 = XML.codepointToString n ∧ (numericRef n).2 = [] := by
  rw [numericRef_allowed n h]
  exact ⟨rfl, rfl⟩

/-! ## The HTML arena as XML nodes -/

/-- The children of arena node `id` as `XML.Node`s: elements by local name
(namespace dropped), attributes in token order. One call per tree level,
bounded by `fuel`, as `buildTree` in `HTML/TreeBuilder.lean`. -/
def xhtmlTree (dom : Array DNode) (fuel : Nat) (id : Nat) : List XML.Node :=
  match fuel with
  | 0 => []
  | f + 1 =>
    let n := dom[id]!
    n.kids.toList.filterMap fun k =>
      let c := dom[k]!
      match c.kind with
      | .text => some (XML.Node.text c.data)
      | .comment => some (XML.Node.comment c.data)
      | .pi => some (XML.Node.pi c.name c.data)
      | .elem => some (XML.Node.element c.name (c.attrs.toList.map fun a => { name := a.1, value := a.2 })
          (xhtmlTree dom f k))
      | .doc | .doctype => none

end L4Factoidal.HTML
