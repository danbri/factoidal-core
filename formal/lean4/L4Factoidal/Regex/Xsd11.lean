/- XSD 1.1 (2012), G.4.2.5 and K.1: name escapes use the XML
1.0 Fifth Edition NameStartChar/NameChar tables already in XSDPattern.
This separate admission adapter preserves the XSD 1.0 profile unchanged.
Digit/word category escapes still require Unicode category tables and are
refused. The parser and derivative matcher remain shared; this is a
restricted profile, not a proof of complete XSD regex conformance.
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

end L4Factoidal.Regex.Profiles
