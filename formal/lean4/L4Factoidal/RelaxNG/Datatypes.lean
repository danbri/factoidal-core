/-
L4Factoidal.RelaxNG.Datatypes — the two datatype libraries a RELAX NG
schema may name.

  * The built-in library, URI `""` (RELAX NG Specification, 3 December
    2001, §6.2.9 "Built-in datatype library"): `string` and `token`, with
    no parameters. A `string` value is the string; a `token` value is the
    string after whitespace collapse.
  * `http://www.w3.org/2001/XMLSchema-datatypes`: the built-in datatypes
    of W3C XML Schema Part 2, as "Guidelines for using W3C XML Schema
    Datatypes with RELAX NG" (OASIS, 7 September 2001) fixes them. Every
    constraining facet except `enumeration` and `whiteSpace` may be given as
    a `param`; `pattern` may be repeated (each one is a further
    restriction); an unknown parameter, a repeated parameter or a facet that
    does not apply to the datatype is an error in the schema. Validation is
    `L4Factoidal.XSD.SimpleType.valueOf`; value equality is
    `XSD.valEqualOrIdentical`. A `QName` or `NOTATION` value is the pair
    (namespace URI, local name), so its prefix is resolved in the context.

A schema that names any other library is incorrect for this processor
(§4.16: "the type attribute must identify a datatype within the datatype
library").
-/
import L4Factoidal.XSD.SimpleType
import L4Factoidal.RelaxNG.Syntax

namespace L4Factoidal.RelaxNG

open L4Factoidal.XSD

/-- The XSD built-in a `type` attribute names in the XSD library. The two
special types `anySimpleType` and `anyAtomicType` are not datatypes of the
library. -/
def xsdBuiltin? (name : String) : Option Builtin :=
  match builtinOfName? name with
  | some .anySimpleType => none
  | some .anyAtomicType => none
  | r => r

/-- The length facets apply to the string family, `anyURI`, the binary
types, `QName`, `NOTATION` and the list types (XSD Part 2 §4.1.5). -/
def lengthApplies (b : Builtin) : Bool :=
  (builtinListItem? b).isSome ||
  match b.primitive with
  | some .string | some .anyURI | some .hexBinary | some .base64Binary
  | some .qname | some .notation => true
  | _ => false

/-- The order facets apply to the ordered primitive types: the numbers,
`duration` and the date and time types. -/
def boundsApply (b : Builtin) : Bool :=
  match b.primitive with
  | some .decimal | some .float | some .double | some .duration
  | some .dateTime | some .time | some .date | some .gYearMonth | some .gYear
  | some .gMonthDay | some .gDay | some .gMonth | some .precisionDecimal => true
  | _ => false

/-- `totalDigits` and `fractionDigits` apply to `decimal` and the types
derived from it. -/
def digitsApply (b : Builtin) : Bool :=
  b.primitive == some .decimal

/-- A non-negative integer parameter value. -/
def paramNat? (v : String) : Option Nat :=
  let t := wsCollapse v
  if !t.isEmpty && t.all (fun c => '0' ≤ c && c ≤ '9') then t.toNat? else none

/-- Add one `param` to the facets of an XSD built-in. -/
def addParam (b : Builtin) (f : Facets) (p : String × String) : Except String Facets :=
  let (n, v) := p
  let nat (k : Nat → Facets) : Except String Facets :=
    match paramNat? v with
    | some m => .ok (k m)
    | none => .error s!"param {n}: not a non-negative integer: {v}"
  let bound (k : String → Facets) : Except String Facets :=
    if !boundsApply b then .error s!"param {n} does not apply to {b.localName}"
    else match lexicalMapWs b v with
      | some _ => .ok (k v)
      | none => .error s!"param {n}: not a value of {b.localName}: {v}"
  match n with
  | "length" => if lengthApplies b then nat (fun m => { f with length := some m })
                else .error s!"param length does not apply to {b.localName}"
  | "minLength" => if lengthApplies b then nat (fun m => { f with minLength := some m })
                   else .error s!"param minLength does not apply to {b.localName}"
  | "maxLength" => if lengthApplies b then nat (fun m => { f with maxLength := some m })
                   else .error s!"param maxLength does not apply to {b.localName}"
  | "totalDigits" =>
      if digitsApply b then
        match paramNat? v with
        | some 0 => .error "param totalDigits must be positive"
        | some m => .ok { f with totalDigits := some m }
        | none => .error s!"param totalDigits: not a positive integer: {v}"
      else .error s!"param totalDigits does not apply to {b.localName}"
  | "fractionDigits" => if digitsApply b then nat (fun m => { f with fractionDigits := some m })
                        else .error s!"param fractionDigits does not apply to {b.localName}"
  | "pattern" =>
      match Regex.Profiles.compileXsd11 v with
      | .ok _ => .ok { f with patterns := f.patterns ++ [[v]] }
      | .error _ => .error s!"param pattern: not a regular expression: {v}"
  | "minInclusive" => bound (fun s => { f with minInclusive := some s })
  | "maxInclusive" => bound (fun s => { f with maxInclusive := some s })
  | "minExclusive" => bound (fun s => { f with minExclusive := some s })
  | "maxExclusive" => bound (fun s => { f with maxExclusive := some s })
  | _ => .error s!"param {n} is not allowed for {b.localName}"

/-- The facets that the `param`s of a `data` pattern give. A parameter
other than `pattern` may appear once. -/
def facetsOf (b : Builtin) (params : List (String × String)) : Except String Facets := do
  let mut f : Facets := {}
  let mut seen : List String := []
  for p in params do
    if p.1 != "pattern" && seen.contains p.1 then
      throw s!"param {p.1} is repeated"
    seen := p.1 :: seen
    f ← addParam b f p
  return f

/-- A QName value whose prefix is not bound in the context is not a value
(XSD Part 2 §3.2.18: the prefix must be declared). -/
def qnameResolves (cx : Context) : Val → Bool
  | .qname p _ _ => (cx.lookup p).isSome
  | _ => true

/-- XSD library: is `s` a literal of built-in `b` restricted by `f`, in
context `cx`? -/
def xsdAllows (b : Builtin) (f : Facets) (cx : Context) (s : String) : Bool :=
  match valueOf (.atomic b f) s with
  | some v => qnameResolves cx v
  | none => false

/-- §4.16: the `type` of a `data` or `value` names a datatype of its library,
and the `param`s of a `data` are allowed for it. -/
def checkDatatype (dt : Datatype) (params : List (String × String)) : Except String Unit :=
  if dt.lib == "" then
    if dt.name != "string" && dt.name != "token" then
      .error s!"datatype {dt.name} is not in the built-in library"
    else if !params.isEmpty then .error "the built-in library has no parameters"
    else .ok ()
  else if dt.lib == xsdLibUri then
    match xsdBuiltin? dt.name with
    | none => .error s!"datatype {dt.name} is not in the XML Schema library"
    | some b => do let _ ← facetsOf b params; pure ()
  else .error s!"datatype library {dt.lib} is not supported"

/-- §6.2.8: does `s` match `data` with these parameters in context `cx`? -/
def dataAllows (dt : Datatype) (params : List (String × String)) (cx : Context)
    (s : String) : Bool :=
  if dt.lib == "" then dt.name == "string" || dt.name == "token"
  else if dt.lib == xsdLibUri then
    match xsdBuiltin? dt.name with
    | some b =>
      match facetsOf b params with
      | .ok f => xsdAllows b f cx s
      | .error _ => false
    | none => false
  else false

/-- §6.2.7: is `s` (in context `cx`) equal to the value `v` of a `value`
pattern (in context `vcx`)? -/
def valueEq (dt : Datatype) (v : String) (vcx : Context) (s : String) (cx : Context) : Bool :=
  if dt.lib == "" then
    if dt.name == "string" then v == s
    else wsCollapse v == wsCollapse s
  else if dt.lib == xsdLibUri then
    match xsdBuiltin? dt.name with
    | some b =>
      match valueOf (.atomic b {}) v, valueOf (.atomic b {}) s with
      | some (.qname p1 l1 _), some (.qname p2 l2 _) =>
        match vcx.lookup p1, cx.lookup p2 with
        | some u1, some u2 => u1 == u2 && l1 == l2
        | _, _ => false
      | some a, some c => valEqualOrIdentical a c
      | _, _ => false
    | none => false
  else false

/-- §4.16: the string of a `value` pattern must be a literal of its
datatype in the context of the `value` element. -/
def checkValue (dt : Datatype) (v : String) (vcx : Context) : Except String Unit := do
  checkDatatype dt []
  if dt.lib == xsdLibUri then
    match xsdBuiltin? dt.name with
    | some b =>
      if !xsdAllows b {} vcx v then
        throw s!"value {v} is not a literal of {dt.name}"
    | none => pure ()

end L4Factoidal.RelaxNG
