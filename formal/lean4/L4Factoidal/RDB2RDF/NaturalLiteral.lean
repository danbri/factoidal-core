/-
L4Factoidal.RDB2RDF.NaturalLiteral — the natural RDF literal of a SQL value.

Spec: R2RML: RDB to RDF Mapping Language, W3C Recommendation 27 September 2012,
§10.2 "Natural Mapping of SQL Values" (Table 1, the natural RDF datatype of
each SQL datatype, and the canonical lexical forms of XML Schema). A Direct
Mapping of Relational Data to RDF, W3C Recommendation 27 September 2012, §2.3
uses the same mapping for its literal triples.

Canonical forms (XML Schema 1.1 Part 2): `xsd:integer` §3.4.13 (no leading
zeros, no `+`); `xsd:decimal` §3.3.3.2 (an integer value has no decimal
point; otherwise no trailing zeros); `xsd:double` §3.3.5.2 (one non-zero digit
before the point, at least one digit after it, no trailing zeros after the
first, `E` and an exponent with no `+` and no leading zeros; zero is
`0.0E0`); `xsd:dateTime` §3.3.7 (`T` between date and time); `xsd:hexBinary`
§3.3.15.2 (upper-case digits).

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.SQL.Database
import L4Factoidal.RML.Value

namespace L4Factoidal.RDB2RDF.R2RML2012

open L4Factoidal.SQL
open L4Factoidal.RML

def xsd (name : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ name

def digitsOf (n : Nat) : String := toString n

/-- Canonical `xsd:decimal` of `m × 10^(-s)`. -/
def decimalCanonical (m : Int) (s : Nat) : String :=
  let (m, s) := trimDec m s
  if s == 0 then toString m
  else
    let neg := m < 0
    let ds := digitsOf m.natAbs
    let ds := if ds.length ≤ s then String.ofList (List.replicate (s + 1 - ds.length) '0') ++ ds else ds
    let ip := ds.take (ds.length - s)
    let fp := ds.drop (ds.length - s)
    (if neg then "-" else "") ++ ip.toString ++ "." ++ fp.toString

/-- Canonical `xsd:double` of the exact decimal `m × 10^(-s)`. -/
def doubleCanonical (m : Int) (s : Nat) : String :=
  if m == 0 then "0.0E0"
  else
    let neg := m < 0
    -- Remove trailing zeros of the digit string, moving them into the exponent.
    let ds0 := digitsOf m.natAbs
    let digits := String.ofList (ds0.toList.reverse.dropWhile (· == '0')).reverse
    let zeros := ds0.length - digits.length
    -- value = digits × 10^(zeros - s); in d.ddd form the exponent is
    -- (digits.length - 1) + zeros - s.
    let e : Int := (digits.length : Int) - 1 + zeros - s
    let first := digits.take 1
    let rest := digits.drop 1
    let frac := if rest.isEmpty then "0" else rest.toString
    (if neg then "-" else "") ++ first.toString ++ "." ++ frac ++ "E" ++ toString e

/-- The natural RDF literal of a non-NULL SQL value (R2RML 2012 §10.2):
    the lexical form and the natural RDF datatype (`none` for a plain
    literal, which is a character string). NULL has none. -/
def naturalRVal : Value → Option RVal
  | .null => none
  | .int i => some { lexical := toString i, natural := some (xsd "integer") }
  | .dec m s => some { lexical := decimalCanonical m s, natural := some (xsd "decimal") }
  | .dbl m s => some { lexical := doubleCanonical m s, natural := some (xsd "double") }
  | .str s => some { lexical := s }
  | .bool b => some { lexical := if b then "true" else "false", natural := some (xsd "boolean") }
  | .date s => some { lexical := s, natural := some (xsd "date") }
  | .timestamp s => some { lexical := s.replace " " "T", natural := some (xsd "dateTime") }
  | .bin h => some { lexical := h.toUpper, natural := some (xsd "hexBinary") }

/-! ## Build-time checks: the values of the test databases -/

#guard doubleCanonical 8025 2 == "8.025E1"
#guard doubleCanonical 165 2 == "1.65E0"
#guard doubleCanonical 30 0 == "3.0E1"
#guard doubleCanonical (-5) 1 == "-5.0E-1"
#guard decimalCanonical 1500 2 == "15"
#guard decimalCanonical 1550 2 == "15.5"
#guard decimalCanonical 5 2 == "0.05"
#guard (naturalRVal (.timestamp "2009-10-10 12:12:22")).map (·.lexical) == some "2009-10-10T12:12:22"
#guard naturalRVal .null == none

end L4Factoidal.RDB2RDF.R2RML2012
