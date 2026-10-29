/-
L4Factoidal.XML.XPointerTheorems — properties of the XPointer Framework,
element() and xmlns() schemes (all W3C Recommendations of 25 March 2003)
as implemented in `L4Factoidal.XML.XPointer`. The names carry the year of
the Recommendations (`xptr2003_`), so a later edition gets new theorems.

* `xptr2003_unknown_scheme_skipped`: a part of a scheme that the
  processor does not know identifies no subresource, and evaluation goes
  on with the next part (Framework §3.3).
* `xptr2003_xmlns_never_identifies`: a pointer of xmlns() parts only
  identifies no subresource (xmlns() §3).
* `xptr2003_element_ncname_eq_shorthand`: element() scheme data that is
  an NCName with no child sequence identifies the element that the
  shorthand pointer with that NCName identifies (element() §3, "an
  NCName alone ... the same element as a shorthand pointer").
* `xptr2003_followSteps_append`: a child sequence `s ++ t` is `s`, then
  `t` from the element that `s` selects.
* `xptr2003_schemeData_escape`: scheme data written by `escapeData` is
  read back unchanged, and reading stops at the closing parenthesis
  (Framework §3.1, the escaping of `^`, `(` and `)`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.XPointer

namespace L4Factoidal.XML.XPointer

open L4Factoidal.XML

theorem xptr2003_unknown_scheme_skipped (sch : Schemes) (d : Document)
    (ns : List (String × String)) (p : Part) (ps : List Part)
    (h1 : p.scheme ≠ "xmlns") (h2 : p.scheme ≠ "element") (h3 : p.scheme ≠ "xpointer") :
    evalParts sch d ns (p :: ps) = evalParts sch d ns ps := by
  simp [evalParts, h1, h2, h3]

theorem xptr2003_xmlns_never_identifies (sch : Schemes) (d : Document) :
    ∀ (ps : List Part) (ns : List (String × String)),
      (∀ p ∈ ps, p.scheme = "xmlns") → evalParts sch d ns ps = none
  | [], _, _ => by simp [evalParts]
  | p :: ps, ns, h => by
    have hp : p.scheme = "xmlns" := h p (by simp)
    have hr : ∀ q ∈ ps, q.scheme = "xmlns" := fun q hq => h q (by simp [hq])
    unfold evalParts
    simp only [hp]
    cases parseXmlnsData p.data with
    | some b => exact xptr2003_xmlns_never_identifies sch d ps _ hr
    | none => exact xptr2003_xmlns_never_identifies sch d ps _ hr

theorem xptr2003_element_ncname_eq_shorthand (sch : Schemes) (d : Document) (n : String) :
    evaluate sch d (.shorthand n) =
      (evalElement d { start := some n, steps := [] }).map (fun (e, sc) => [Hit.node e sc]) := by
  simp only [evaluate, evalElement]
  cases elementById d n <;> simp [followSteps]

theorem xptr2003_followSteps_append :
    ∀ (s t : List Nat) (x : Node × List (String × String)),
      followSteps (s ++ t) x = (followSteps s x).bind (followSteps t)
  | [], _, _ => by simp [followSteps]
  | k :: ks, t, (n, sc) => by
    simp only [List.cons_append, followSteps]
    split
    · split
      · split
        · simp
        · exact xptr2003_followSteps_append ks t _
      · simp
    · simp

/-- The characters `escapeData` writes for `cs`. -/
def escChars (cs : List Char) : List Char :=
  cs.flatMap (fun c => if c == '^' || c == '(' || c == ')' then ['^', c] else [c])

theorem escapeData_toList (s : String) : (escapeData s).toList = escChars s.toList := by
  simp [escapeData, escChars]

theorem schemeData_escChars (rest : List Char) :
    ∀ (cs acc : List Char),
      schemeData (escChars cs ++ ')' :: rest) 0 acc = .ok (String.ofList (acc.reverse ++ cs), rest)
  | [], acc => by simp [escChars, schemeData]
  | c :: cs, acc => by
    have ih := schemeData_escChars rest cs (c :: acc)
    have fin : String.ofList ((c :: acc).reverse ++ cs) = String.ofList (acc.reverse ++ c :: cs) := by
      simp
    rw [← fin, ← ih]
    by_cases h1 : c = '^'
    · subst h1; simp [escChars, schemeData]
    by_cases h2 : c = '('
    · subst h2; simp [escChars, schemeData]
    by_cases h3 : c = ')'
    · subst h3; simp [escChars, schemeData]
    have hesc : escChars (c :: cs) = c :: escChars cs := by simp [escChars, h1, h2, h3]
    rw [hesc, List.cons_append, schemeData.eq_def]
    split <;> simp_all

theorem xptr2003_schemeData_escape (s : String) (rest : List Char) :
    schemeData ((escapeData s).toList ++ ')' :: rest) 0 [] = .ok (s, rest) := by
  rw [escapeData_toList, schemeData_escChars]
  simp

end L4Factoidal.XML.XPointer
