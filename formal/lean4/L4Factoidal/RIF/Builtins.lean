/-
L4Factoidal.RIF.Builtins — the RIF-DTB built-in predicates and
functions.

Spec: RIF Datatypes and Built-Ins 1.0 (https://www.w3.org/TR/rif-dtb/).

## Three answers, not two

A built-in call returns `yes`, `no`, or `unknown`. `unknown` is not a
failure: it means THIS module does not decide that built-in, and a
rule whose body needs it cannot fire. The engine then reports the
whole entailment as UNDECIDED rather than as "does not hold" —
because a closure computed without a rule is not the closure, and
answering `false` from it would be a guess dressed as a verdict.

RIF-DTB defines 197 built-ins. Naming which ones are decided here, and
returning `unknown` for the rest, is what keeps the score honest as
the list grows.
-/
import L4Factoidal.RIF.Syntax
import L4Factoidal.XSD.ValueSpace
import L4Factoidal.Fn.Arithmetic
import L4Factoidal.Fn.Comparison
import L4Factoidal.Fn.Cast

namespace L4Factoidal.RIF

inductive Ans where
  | yes | no | unknown
deriving Repr, DecidableEq, Inhabited

def funcNs : String := "http://www.w3.org/2007/rif-builtin-function#"
def predNs : String := "http://www.w3.org/2007/rif-builtin-predicate#"

/-- The local name of a built-in IRI, or `none` when it is not one. -/
def builtinName (iri : String) : Option String :=
  if iri.startsWith funcNs then some (String.ofList (iri.toList.drop funcNs.length))
  else if iri.startsWith predNs then some (String.ofList (iri.toList.drop predNs.length))
  else if iri.startsWith xsdNs then some ("cast-" ++ String.ofList (iri.toList.drop xsdNs.length))
  else none

/-- The XSD local name of a datatype IRI. -/
def xsdLocal (dt : String) : Option String :=
  if dt.startsWith xsdNs then some (String.ofList (dt.toList.drop xsdNs.length)) else none

/-- RIF-DTB Second Edition §2.2.1 references XSD 1.1. This adapter uses
    the shared lexical decision; unknown datatype names remain undecided.
    As in the shared API, callers supply lexical forms without XML whitespace
    preprocessing. This does not implement value-space membership or casts. -/
def inLexicalSpace (base lex : String) : Option Bool :=
  XSD.validLexicalFor .xsd11 base lex

/-- Compatibility view of primitive families from the shared hierarchy.
    Numeric operations and datatype guards consume parsed values below. -/
def xsdFamily (b : String) : Option String :=
  ((XSD.builtinOfName? b).bind (·.primitive)).map (·.localName)

/-- Membership for a parsed XSD value. PlainLiteral includes the string
    value space; XMLLiteral is disjoint from these XSD spaces. -/
def xsdValueMembership (base : String) (v : XSD.Val) : Option Bool :=
  if base == "PlainLiteral" then
    some (match v with | .str .string _ => true | _ => false)
  else if base == "XMLLiteral" then some false
  else (XSD.builtinOfName? base).bind (fun b => XSD.valueInBuiltin b v)

private def guardAnswer (negative : Bool) : Option Bool → Ans
  | none => .unknown
  | some member => if member != negative then .yes else .no

/-- Decoded values used by RIF datatype guards and identity. Empty-language
    PlainLiteral maps to an XSD string; tagged values retain their text and
    lowercase tag. Full BCP 47 validation remains a caller precondition. -/
inductive LiteralValue where
  | xsd (value : XSD.Val)
  | tagged (text language : String)
deriving Repr

def literalValue? : GTerm → Option LiteralValue
  | .const lex sp =>
      if sp == rdfNs ++ "PlainLiteral" then
        match (lex.splitOn "@").reverse with
        | tag :: textParts =>
            if textParts.isEmpty then none
            else
              let text := String.intercalate "@" textParts.reverse
              if tag.isEmpty then some (.xsd (.str .string text))
              else some (.tagged text tag.toLower)
        | [] => none
      else do
        let cb ← xsdLocal sp
        let source ← XSD.builtinOfName? cb
        let value ← XSD.checkedLexicalValue .xsd11 source lex
        some (.xsd value)
  | _ => none

def LiteralValue.identical : LiteralValue → LiteralValue → Bool
  | .xsd a, .xsd b => XSD.valIdentical a b
  | .tagged a al, .tagged b bl => a == b && al == bl
  | _, _ => false

def LiteralValue.membership (base : String) : LiteralValue → Option Bool
  | .xsd v => xsdValueMembership base v
  | .tagged _ _ => some (base == "PlainLiteral")

/-- RIF-DTB §4.1.1.1 tests distinct VALUES, with both arguments in DTS.
    Lists are outside DTS. Unknown/invalid source mappings and XMLLiteral
    canonical identity remain undecided; raw lexical inequality is no proof. -/
def literalNotIdentical (a b : GTerm) : Ans :=
  match a, b with
  | .list _, _ | _, .list _ => .no
  | _, _ =>
      match literalValue? a, literalValue? b with
      | some x, some y => if x.identical y then .no else .yes
      | _, _ => .unknown

/-- RIF-DTB §§4.2–4.3: positive guards test values; negative guards additionally
    require membership in DTS. Lists are outside DTS. IRI/local constants and
    uninterpreted applications have no fixed datatype interpretation here, so
    both polarities remain unknown (RIF-BLD §3.2).

    As before, rdf:XMLLiteral and language-tagged rdf:PlainLiteral inputs assume
    well-formed constants; XML canonical lexical validation and complete BCP 47
    validation are not implemented here. XSD source validity IS checked. -/
def literalGuard (negative : Bool) (base : String) (g : GTerm) : Ans :=
  let knownTarget := base == "PlainLiteral" || base == "XMLLiteral" ||
    ((XSD.builtinOfName? base).any XSD.valueMembershipSupported)
  if !knownTarget then .unknown
  else match g with
  | .list _ => .no
  | .fapp .. => .unknown
  | .const lex sp =>
      if sp == rdfNs ++ "XMLLiteral" then
        guardAnswer negative (some (base == "XMLLiteral"))
      else guardAnswer negative ((literalValue? (.const lex sp)).bind (LiteralValue.membership base))

/-- RIF-DTB positive datatype guard. -/
def isLiteralOf (base : String) (g : GTerm) : Ans := literalGuard false base g

/-- RIF-DTB negative datatype guard, restricted to the datatype domain. -/
def isLiteralNotOf (base : String) (g : GTerm) : Ans := literalGuard true base g

/-- RIF-DTB §4.5: decode and validate through the common XSD value adapter.
    Integer-derived bounds and IEEE rounding apply before operations. -/
def numericValue? (g : GTerm) : Option XSD.Val := do
  match ← literalValue? g with
  | .xsd (.dec d) => some (.dec d)
  | .xsd (.flt f) => some (.flt f)
  | .xsd (.dbl f) => some (.dbl f)
  | _ => none

/-- Compatibility lexical view of the decoded numeric value. IEEE inputs
    reflect their rounded value, not the original decimal spelling. -/
def numericLex (g : GTerm) : Option String := do
  match ← numericValue? g with
  | .dec d => some d.canonical
  | .flt f | .dbl f =>
      let lex := XSD.canonicalFval f
      some (((XSD.decimalOrScientific lex).map XSD.Dec.canonical).getD lex)
  | _ => none

/-- Result typing is separate from value validation (RIF-DTB §4.5.1). -/
def integerOperand (g : GTerm) : Bool := match g with
  | .const _ sp => (XSD.builtinOfIri? sp).any (fun b => (XSD.intBounds b).isSome)
  | _ => false

/-- Serialize numeric results using the shared XSD formatter. -/
def numericResult (integer : Bool) : XSD.Val → Option GTerm
  | .dec d => if integer then (d.toInt?).map (fun n => gLit (toString n) (xsdNs ++ "integer"))
              else some (gLit d.canonical (xsdNs ++ "decimal"))
  | .flt f => some (gLit (XSD.canonicalFval f) (xsdNs ++ "float"))
  | .dbl f => some (gLit (XSD.canonicalFval f) (xsdNs ++ "double"))
  | _ => none

/-- Decimal division policy: at least 16 significant digits, truncating.
    Extra fractional places preserve small results; integers are unbounded.
    This is the implementation precision permitted by F&O §6.2. -/
def divisionPlaces (a b : XSD.Dec) : Nat :=
  max 16 ((17 : Int) + (toString b.mantissa.natAbs).length + a.scale
    - (toString a.mantissa.natAbs).length - b.scale).toNat

/-- RIF-DTB §4.5.1: the same IEEE arithmetic as SPARQL, with exact decimal
    addition/subtraction/multiplication and explicit decimal division precision. -/
def numericArithmetic (op : Fn.Arithmetic.Op) (a b : GTerm) : Option GTerm := do
  let x ← numericValue? a
  let y ← numericValue? b
  let v ← match x, y with
    | .dec p, .dec q => (Fn.Arithmetic.decimal (divisionPlaces p q) op p q).map XSD.Val.dec
    | _, _ => Fn.Arithmetic.floating op x y
  numericResult (op != .div && integerOperand a && integerOperand b) v

/-- RIF-DTB §4.5.1: truncating integer division, including decimal/IEEE inputs. -/
def numericIntegerDivide (a b : GTerm) : Option GTerm := do
  let q ← Fn.Arithmetic.integerDivide (← numericValue? a) (← numericValue? b)
  some (gLit (toString q) (xsdNs ++ "integer"))

/-- RIF-DTB §4.5.1: shared F&O remainder and result typing. -/
def numericMod (a b : GTerm) : Option GTerm := do
  let v ← Fn.Arithmetic.modulo (← numericValue? a) (← numericValue? b)
  numericResult (integerOperand a && integerOperand b) v

def isStringy (g : GTerm) : Option String :=
  match g with
  | .const lex sp => if sp == xsdNs ++ "string" then some lex else none
  | _ => none

/-- The VALUE of an `xs:boolean` constant. `1` and `true` are the same
    value and `0` and `false` are the same value; comparing lexical
    forms made `pred:boolean-less-than("0"^^xs:boolean
    "1"^^xs:boolean)` false, which is the one the corpus writes. -/
def boolValue (g : GTerm) : Option Bool :=
  match g with
  | .const lex sp =>
      if sp != xsdNs ++ "boolean" then none
      else XSD.parseBooleanLex lex
  | _ => none

/-- RIF-DTB §4.5.2: F&O comparison, including NaN and mixed numeric promotion. -/
def cmpNum (a b : GTerm) (op : Fn.Comparison.Op) : Ans :=
  match (do Fn.Comparison.numericCompare (← numericValue? a) (← numericValue? b) op) with
  | some true => .yes
  | some false => .no
  | none => .unknown

/-- Compatibility decimal helpers now share F&O arithmetic. -/
def decimalLexArithmetic (op : Fn.Arithmetic.Op) (a b : String) : Option String := do
  let x ← XSD.parseDecimalLex a
  let y ← XSD.parseDecimalLex b
  (Fn.Arithmetic.decimal (divisionPlaces x y) op x y).map XSD.Dec.canonical

def addDec := decimalLexArithmetic .add
def subDec := decimalLexArithmetic .sub
def mulDec := decimalLexArithmetic .mul

/-- A built-in PREDICATE. -/
def evalPred (name : String) (args : List GTerm) : Ans :=
  match name, args with
  | "literal-not-identical", [a, b] => literalNotIdentical a b
  | "numeric-equal", [a, b] => cmpNum a b .eq
  | "numeric-not-equal", [a, b] => cmpNum a b .ne
  | "numeric-less-than", [a, b] => cmpNum a b .lt
  | "numeric-greater-than", [a, b] => cmpNum a b .gt
  | "numeric-less-than-or-equal", [a, b] => cmpNum a b .le
  | "numeric-greater-than-or-equal", [a, b] => cmpNum a b .ge
  | "boolean-equal", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if x == y then .yes else .no
       | _, _ => .unknown)
  | "boolean-less-than", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if !x && y then .yes else .no
       | _, _ => .unknown)
  | "boolean-greater-than", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if x && !y then .yes else .no
       | _, _ => .unknown)
  | "is-list", [a] => (match a with | .list _ => .yes | _ => .no)
  | "list-contains", [a, b] =>
      (match a with | .list xs => (if xs.contains b then .yes else .no) | _ => .no)
  | "iri-string", [a, b] =>
      (match a, b with
       | .const i sp, .const s sp2 =>
           if sp == iriSpace && sp2 == xsdNs ++ "string"
           then (if i == s then .yes else .no) else .unknown
       | _, _ => .unknown)
  | "contains", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if (x.splitOn y).length > 1 then .yes else .no
       | _, _ => .unknown)
  | "starts-with", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if x.startsWith y then .yes else .no
       | _, _ => .unknown)
  | "ends-with", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if x.endsWith y then .yes else .no
       | _, _ => .unknown)
  | _, [a] =>
      if name.startsWith "is-literal-not-" then
        isLiteralNotOf (String.ofList (name.toList.drop 15)) a
      else if name.startsWith "is-literal-" then
        isLiteralOf (String.ofList (name.toList.drop 11)) a
      else .unknown
  | _, _ => .unknown

/-- RIF-DTB §4.4.1: validate the source, convert its value, then check target
    facets. Empty-tag PlainLiteral shares the string value space. -/
def castXsd (target : String) (g : GTerm) : Option GTerm := do
  let b ← XSD.builtinOfName? target
  let .xsd source ← literalValue? g | none
  let result ← Fn.Cast.cast .xsd11 b source
  some (gLit (Fn.Cast.lexical .xsd11 b result) (xsdNs ++ target))

/-- A built-in FUNCTION. `none` means this module does not decide it,
    which the caller must not read as "no value". -/
def evalFunc (name : String) (args : List GTerm) : Option GTerm :=
  match name, args with
  | "numeric-add", [a, b] => numericArithmetic .add a b
  | "numeric-subtract", [a, b] => numericArithmetic .sub a b
  | "numeric-multiply", [a, b] => numericArithmetic .mul a b
  | "numeric-divide", [a, b] => numericArithmetic .div a b
  | "numeric-integer-divide", [a, b] => numericIntegerDivide a b
  -- The native suite uses the historical integer-mod spelling.
  | "numeric-mod", [a, b] | "numeric-integer-mod", [a, b] => numericMod a b
  | "string-length", [a] =>
      (isStringy a).map (fun s => gLit (toString s.toList.length) (xsdNs ++ "integer"))
  | "upper-case", [a] => (isStringy a).map (fun s => gStr s.toUpper)
  | "lower-case", [a] => (isStringy a).map (fun s => gStr s.toLower)
  | "concat", args' | "concatenate", args' =>
      (args'.foldl (fun acc g => match acc, isStringy g with
        | some s, some t => some (s ++ t)
        | _, _ => none) (some "")).map gStr
  | "count", [a] =>
      (match a with
       | .list xs => some (gLit (toString xs.length) (xsdNs ++ "integer"))
       | _ => none)
  | "make-list", xs => some (.list xs)
  | "reverse", [a] => (match a with | .list xs => some (.list xs.reverse) | _ => none)
  | "concatenate-lists", [a, b] =>
      (match a, b with | .list x, .list y => some (.list (x ++ y)) | _, _ => none)
  | "PlainLiteral-from-string-lang", [a, b] =>
      (match isStringy a, isStringy b with
       | some s, some l => some (.const (s ++ "@" ++ l) (rdfNs ++ "PlainLiteral"))
       | _, _ => none)
  | "string-from-PlainLiteral", [a] =>
      (match a with
       | .const lex sp =>
           if sp == rdfNs ++ "PlainLiteral" then
             some (gStr (match (lex.splitOn "@").reverse with
                         | _ :: rest => String.intercalate "@" rest.reverse
                         | []        => lex))
           else none
       | _ => none)
  | "lang-from-PlainLiteral", [a] =>
      (match a with
       | .const lex sp =>
           if sp == rdfNs ++ "PlainLiteral" then
             some (gStr ((lex.splitOn "@").getLast?.getD ""))
           else none
       | _ => none)
  | _, _ =>
      -- A datatype CAST, `External( xs:date ( "…"^^xs:string ) )`.
      if name.startsWith "cast-" then
        let base := String.ofList (name.toList.drop 5)
        (match args with
         | [g] => castXsd base g
         | _ => none)
      else none

end L4Factoidal.RIF
