/-
L4Factoidal.XSD11.Pattern — the `pattern` facet (XML Schema 1.1 Part 2
§4.3.4) over the project's shared regular-expression engine
(`L4Factoidal.Regex`).

A pattern is read by `Regex.Profiles.xsd11Re`, which `XSD.SimpleType`
also uses: first the restricted XSD 1.1 profile
(`Regex.Profiles.compileXsd11`). That
profile refuses some of the XSD 1.1 grammar (multi-character escapes such
as `\d` and `\w`, category escapes, class subtraction). For those the
F&O 4.0 parser (`Regex.XPath40`) is used: its grammar is the XSD 1.1
Appendix G grammar with additions, so the additions are refused first
(reluctant quantifiers, `(?`, `(*`, back-references, `\b`, `\B`, `\k`,
`\$`, `\#`), and `^` and `$` outside a character class, which are plain
characters in XSD, are escaped. A pattern is matched against the WHOLE
literal (Appendix G: an XSD regular expression is implicitly anchored).

`Theorems.lean` proves that the pattern test of this module is the one of
`XSD.SimpleType` for every pattern (`patternOk11_eq`; `patternOk11_shared`
is the earlier, conditional statement).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Regex.Xsd11
import L4Factoidal.Regex.XPath40

namespace L4Factoidal.XSD11

open L4Factoidal.Regex

/-- The derivative regex of an XSD 1.1 pattern, or `none` when it is not
a valid pattern: the shared reader `Regex.Profiles.xsd11Re`, which
`XSD.SimpleType` also uses. -/
def xsdPatternRe (p : String) : Option Re := Profiles.xsd11Re p

/-- XSD 1.0 uses the shared compiler with its stricter character-class
grammar. In the default edition the existing compiler is unchanged. -/
def xsdPatternReVersion (version : XSD.Version) (p : String) : Option Re :=
  if version == .v10 && !XPath40.xsd10Admitted p "" then none else xsdPatternRe p

@[simp] theorem xsdPatternReVersion_default (p : String) :
    xsdPatternReVersion .v11 p = xsdPatternRe p := rfl

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

def patternOkVersion (version : XSD.Version) (groups : List (List String)) (lit : String) : Bool :=
  if version == .v10 then
    groups.flatten.all (fun p => XPath40.xsd10Admitted p "") && patternOk11 groups lit
  else patternOk11 groups lit

@[simp] theorem patternOkVersion_default (groups : List (List String)) (lit : String) :
    patternOkVersion .v11 groups lit = patternOk11 groups lit := rfl

theorem patternOkVersion_common (groups : List (List String)) (lit : String)
    (h : groups.flatten.all (fun p => XPath40.xsd10Admitted p "") = true) :
    patternOkVersion .v10 groups lit = patternOk11 groups lit := by
  simp [patternOkVersion, h]

def unreadablePatternsVersion (version : XSD.Version) (groups : List (List String)) : List String :=
  groups.flatMap (fun alts => alts.filter (fun p => (xsdPatternReVersion version p).isNone))

end L4Factoidal.XSD11
