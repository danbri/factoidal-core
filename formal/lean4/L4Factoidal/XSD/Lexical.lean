/- Shared lexical adapters with an explicit XSD edition.
   XSD 1.0 Part 2 (2004-10-28) §§3.2.7, 3.2.4–5; XSD 1.1 Part 2
   (2012-04-05) §§3.3.4–8. Whitespace preprocessing belongs to the caller.
   DTValue uses astronomical year numbering internally, including year zero. -/
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.XSD

inductive Edition where
  | xsd10 | xsd11
deriving DecidableEq, Repr, Inhabited

/-- Translate the XSD 1.0 year (no year zero) into the shared calendar.
    This also makes end-of-day rollover across 1 BCE/1 CE use one calendar. -/
def dateLexicalForEdition (edition : Edition) (kind : DTKind) (s : String) : Option String :=
  if edition == .xsd11 || kind == .time || kind == .gMonth ||
      kind == .gMonthDay || kind == .gDay then some s
  else do
    let (year, rest) ← parseYearFrag s.toList
    if year == 0 then none
    else some (padYear (if year < 0 then year + 1 else year) ++ String.ofList rest)

def parseDateTimeFor (edition : Edition) (kind : DTKind) (s : String) : Option DTValue :=
  (dateLexicalForEdition edition kind s).bind (parseDateTimeLex kind)

/-- Convert the internal calendar year back to a consumer's edition. -/
def yearForEdition (edition : Edition) (v : DTValue) : Option Int :=
  v.year.map (fun y => if edition == .xsd10 && y ≤ 0 then y - 1 else y)

/-- Shared built-in lexical decision. Unknown type names remain `none`.
    The 1.0 adapter includes the F&O duration extensions used by SPARQL;
    it is not a declaration that those types occur in XSD 1.0 itself. -/
def lexicalFor (edition : Edition) (b : Builtin) (s : String) : Option Val :=
  match dtKindOf? b with
  | some kind => do
      let v ← parseDateTimeFor edition kind s
      if b == .dateTimeStamp && v.tz.isNone then none else some (.dt kind v)
  | none =>
      if edition == .xsd10 && (b == .float || b == .double) && s == "+INF"
      then none else lexicalMap b s

def validLexicalFor (edition : Edition) (name s : String) : Option Bool :=
  (builtinOfName? name).map (fun b => (lexicalFor edition b s).isSome)

/-- Exact decimal/exponent comparison substrate; no IEEE rounding. -/
def decimalOrScientific (s : String) : Option Dec := do
  let parts := (s.replace "E" "e").splitOn "e"
  match parts with
  | [mantissa] => parseDecimalLex mantissa
  | [mantissa, exponent] =>
      let d ← parseDecimalLex mantissa
      let e ← parseIntegerLex exponent
      let scale : Int := (d.scale : Int) - e
      if scale ≥ 0 then some (Dec.norm ⟨d.mantissa, scale.toNat⟩)
      else some (Dec.ofInt (d.mantissa * (10 : Int) ^ (-scale).toNat))
  | _ => none

end L4Factoidal.XSD
