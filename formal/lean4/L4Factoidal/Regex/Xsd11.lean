/- XSD 1.1 (2012), G.4.2.5 and K.1: name escapes use the XML
1.0 Fifth Edition NameStartChar/NameChar tables already in XSDPattern.
This separate admission adapter preserves the XSD 1.0 profile unchanged.
`compileXsd11` is the restricted profile: digit/word category escapes,
`\p{..}` and class subtraction are refused by it. `xsd11Re` is the whole
reader of a `pattern` facet: the restricted profile first, and for what it
refuses the F&O 4.0 parser (`Regex.XPath40`, which has the Unicode
category tables), with the syntax that F&O 4.0 adds to XSD refused first.
The parser and derivative matcher remain shared; this is not a proof of
complete XSD regex conformance.
https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#regexs -/
import L4Factoidal.Regex.Profiles

namespace L4Factoidal.Regex.Profiles

/-- XSD 1.1 adds the existing XML name tables to the shared conservative
escape admission. Other escapes retain the XSD 1.0 subset policy. -/
def xsd11EscapesSupported : List Char → Bool
  | [] => true
  | '\\' :: c :: rest =>
      ("iIcC".contains c || escapesSupported .xsd10 ['\\', c]) &&
        xsd11EscapesSupported rest
  | '\\' :: [] => false
  | _ :: rest => xsd11EscapesSupported rest

/-- Compile the existing XSD 1.1 caller's whole-string facet language,
using XML 1.0 Fifth Edition names. Category tables, subtraction, special
groups and lazy-quantifier syntax remain outside this profile. -/
def compileXsd11 (pattern : String) : Except Error Re :=
  if !xsd11EscapesSupported pattern.toList ||
      hasClassSubtraction pattern.toList false ||
      (pattern.splitOn "(?").length > 1 ||
      (["*?", "+?", "??", "}?"]).any (fun token => (pattern.splitOn token).length > 1) then
    .error (.unsupported "XSD 1.1 regex outside the supported subset")
  else
    match XSDPattern.parseXsdPattern (String.ofList (xsdLiterals pattern.toList false)) with
    | some r => .ok r
    | none => .error (.invalid "invalid or unsupported XSD 1.1 pattern")

/-- Rewrite an XSD pattern for the F&O 4.0 parser: `none` when it uses
syntax that F&O 4.0 adds to XSD (reluctant quantifiers, `(?`, `(*`,
back-references, `\b`, `\B`, `\k`, `\$`, `\#`); `^` and `$` outside a
class, which are plain characters in XSD (Appendix G), are escaped.
Arguments: the rest of the pattern, the class nesting depth, whether the
reader is inside the braces of `\p{...}`, the output so far (reversed). -/
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

/-- The derivative regex of an XSD 1.1 `pattern` facet (Part 2 §4.3.4,
Appendix G), or `none` when it is not a pattern this tree reads: the
restricted profile `compileXsd11` first; for what that refuses (`\d`,
`\w`, `\p{..}`, class subtraction) the F&O 4.0 parser. One reader for
`XSD.SimpleType` (Part 2 validation) and `XSD11` (Part 1 assessment). -/
def xsd11Re (p : String) : Option Re :=
  match compileXsd11 p with
  | .ok r => some r
  | .error _ =>
    match xsdForXPath40 p.toList 0 false [] with
    | none => none
    | some cs =>
      match XPath40.parse false (cs.map Char.toNat) with
      | some (node, _) => some (XPath40.toRe { ci := false, dotAll := false, multiline := false } node)
      | none => none

/-- Kind: agreement of two readers.
Says: when the restricted profile `compileXsd11` reads a pattern, the
whole reader `xsd11Re` gives exactly that regex, so adding the F&O 4.0
fallback changed nothing for a pattern that was read before.
Does not say: that either reader accepts exactly the XSD 1.1 Appendix G
language, or that the two parsers agree on a pattern both could read. -/
theorem xsd11Re_of_compileXsd11 (p : String) (r : Re)
    (h : compileXsd11 p = .ok r) : xsd11Re p = some r := by
  simp [xsd11Re, h]

/-- Kind: totality of the fallback's refusal.
Says: a pattern that neither the restricted profile nor the rewriting for
the F&O 4.0 parser admits has no regex (`xsd11Re p = none`), so a caller
sees it as unreadable and never as a regex that matches something else.
Does not say: which patterns those are. -/
theorem xsd11Re_none_of_refused (p : String) (e : Error)
    (h : compileXsd11 p = .error e) (hx : xsdForXPath40 p.toList 0 false [] = none) :
    xsd11Re p = none := by
  simp [xsd11Re, h, hx]

end L4Factoidal.Regex.Profiles
