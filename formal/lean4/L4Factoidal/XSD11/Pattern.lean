/-
L4Factoidal.XSD11.Pattern — the `pattern` facet (XML Schema 1.1 Part 2
§4.3.4) over the project's shared regular-expression engine
(`L4Factoidal.Regex`).

A pattern is first compiled by the shared XSD 1.1 profile
(`Regex.Profiles.compileXsd11`), which `XSD.SimpleType` also uses. That
profile refuses some of the XSD 1.1 grammar (multi-character escapes such
as `\d` and `\w`, category escapes, class subtraction). For those the
F&O 4.0 parser (`Regex.XPath40`) is used: its grammar is the XSD 1.1
Appendix G grammar with additions, so the additions are refused first
(reluctant quantifiers, `(?`, `(*`, back-references, `\b`, `\B`, `\k`,
`\$`, `\#`), and `^` and `$` outside a character class, which are plain
characters in XSD, are escaped. A pattern is matched against the WHOLE
literal (Appendix G: an XSD regular expression is implicitly anchored).

`Theorems.lean` proves that when the shared profile reads every pattern
the result is the shared one (`patternOk11_shared`), so the two dialects
are one definition wherever both apply.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Regex.Xsd11
import L4Factoidal.Regex.XPath40

namespace L4Factoidal.XSD11

open L4Factoidal.Regex

/-- Rewrite an XSD pattern for the F&O 4.0 parser: `none` when it uses
syntax that F&O 4.0 adds to XSD; `^` and `$` outside a class escaped. -/
def xsdForXPath40 : List Char → Nat → Bool → List Char → Option (List Char)
  | [], _, _, acc => some acc.reverse
  -- inside the braces of `\p{...}`: copied up to the closing brace
  | c :: rest, d, true, acc => xsdForXPath40 rest d (c != '}') (c :: acc)
  | '\\' :: c :: rest, d, false, acc =>
    if c.isDigit || c == 'b' || c == 'B' || c == 'k' || c == '$' || c == '#' then none
    else match hr : rest with
      | '{' :: rest' =>
        if c == 'p' || c == 'P' then xsdForXPath40 rest' d true ('{' :: c :: '\\' :: acc)
        else xsdForXPath40 rest d false (c :: '\\' :: acc)
      | _ => xsdForXPath40 rest d false (c :: '\\' :: acc)
  | '[' :: rest, d, false, acc => xsdForXPath40 rest (d + 1) false ('[' :: acc)
  | ']' :: rest, d, false, acc => xsdForXPath40 rest (d - 1) false (']' :: acc)
  | '(' :: '?' :: _, 0, false, _ => none
  | '(' :: '*' :: _, 0, false, _ => none
  | '^' :: rest, 0, false, acc => xsdForXPath40 rest 0 false ('^' :: '\\' :: acc)
  | '$' :: rest, 0, false, acc => xsdForXPath40 rest 0 false ('$' :: '\\' :: acc)
  | q :: '?' :: rest, 0, false, acc =>
    if q == '*' || q == '+' || q == '?' || q == '}' then none
    else xsdForXPath40 ('?' :: rest) 0 false (q :: acc)
  | c :: rest, d, false, acc => xsdForXPath40 rest d false (c :: acc)
termination_by cs => cs.length
decreasing_by all_goals (simp_all; try omega)

/-- The derivative regex of an XSD 1.1 pattern, or `none` when it is not
a valid pattern. -/
def xsdPatternRe (p : String) : Option Re :=
  match Profiles.compileXsd11 p with
  | .ok r => some r
  | .error _ =>
    match xsdForXPath40 p.toList 0 false [] with
    | none => none
    | some cs =>
      match XPath40.parse false (cs.map Char.toNat) with
      | some (node, _) => some (XPath40.toRe { ci := false, dotAll := false, multiline := false } node)
      | none => none

/-- §4.3.4.4: the literal is in the pattern's language. -/
def patternMatch11 (p : String) (lit : String) : Option Bool :=
  (xsdPatternRe p).map (fun r => Exec.acceptsNorm r (lit.toList.map Char.toNat))

/-- Every group (a conjunction over restriction steps) has an alternative
that matches. A group with no readable alternative is vacuous here; such
a pattern is a schema error (`Constraints.lean`). -/
def patternOk11 (groups : List (List String)) (lit : String) : Bool :=
  groups.all (fun alts =>
    let rs := alts.filterMap (fun p => patternMatch11 p lit)
    rs.isEmpty || rs.any id)

/-- The patterns no dialect reads. -/
def unreadablePatterns11 (groups : List (List String)) : List String :=
  groups.flatMap (fun alts => alts.filter (fun p => (xsdPatternRe p).isNone))

end L4Factoidal.XSD11
