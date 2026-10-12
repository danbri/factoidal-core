/-
L4Factoidal.Storage.Sbm11.TermId — 64-bit global term ids and graph ids of
wire version 11 (`docs/designissues/2026-10-11-shardborough-vs-qlever.md`
section 6.1; https://github.com/danbri/factoidal/issues/788).

A term id is a `UInt64`: bits 63..60 are a tag, bits 59..0 the payload.

| Tag | Term | Payload |
|---:|---|---|
| 1 | blank node (dictionary class 1) | rank in the dictionary |
| 2 | IRI (class 2) | rank in the dictionary |
| 3 | literal stored in the dictionary (classes 3 to 6) | rank in the dictionary |
| 4 | inline integer: one of the 13 datatypes of `intTypes`, canonical lexical form, value in `[-2^55, 2^55)` and in the datatype's value space | bits 59..56 the index into `intTypes`, bits 55..0 the value plus `2^55` |
| 5 | inline `xsd:boolean`, lexical form `true` or `false` | 1 or 0 |
| 0, 6..15 | not written by stage 2 (6, 7, 8: decimal, double, date, a later stage; 14: delta terms, stage 5) | |

The rank is the position of the term's key (`TermKey.termKey?`) in the
byte-ordered dictionary, so it is dense and global.

## Canonical forms only

A literal is inline only when its lexical form is the canonical lexical
form of its value: `toString v == lexicalForm` for the integer `v` that
`String.toInt?` reads. `"072"^^xsd:integer` reads as 72, `toString 72` is
`"72"`, so it is NOT inline and goes to the dictionary as a class-5 key:
the id then names exactly that term, and `ofId (toId t) = t` holds. This
is where SBM11 differs from QLever's folding of numeric literals (record
section 6.1).

Theorems (`TermIdTheorems`): `ofCode?_toCode?` (the round trip),
`toCode?_injective`, `ofId?_toId?` and `toId?_eq_iff` (two admitted terms
have the same id if and only if they are the same RDF term).

## Graph ids

`GraphId` is a separate type: 0 is the default graph, every other value is
the term id of the graph name (a term id is never 0).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKey
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF

/-- `2 ^ 60`, the tag unit. `@[noinline]` for the reason of `NatBounds`. -/
@[reducible, noinline] def two60 : Nat := 1152921504606846976
/-- `2 ^ 56`, the integer-subtype unit. -/
@[reducible, noinline] def two56 : Nat := 72057594037927936
/-- `2 ^ 55`, the bias of an inline integer. -/
@[reducible, noinline] def two55Int : Int := 36028797018963968

theorem two60_eq : two60 = 1152921504606846976 := rfl
theorem two56_eq : two56 = 72057594037927936 := rfl
theorem two55Int_eq : two55Int = 36028797018963968 := rfl

def tagBnode : Nat := 1
def tagIri : Nat := 2
def tagLit : Nat := 3
def tagInt : Nat := 4
def tagBool : Nat := 5

/-! ## The integer datatypes that inline -/

/-- An integer datatype and its value space bounds (XML Schema 1.1 Part 2,
    sections 3.4.13 to 3.4.25). -/
structure IntType where
  iri : WfIri
  lo : Option Int
  hi : Option Int

def IntType.admits (e : IntType) (v : Int) : Bool :=
  (match e.lo with | none => true | some lo => decide (lo ≤ v)) &&
  (match e.hi with | none => true | some hi => decide (v ≤ hi))

def xsdIri (local_ : String) (h : isIri ("http://www.w3.org/2001/XMLSchema#" ++ local_) = true) : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#" ++ local_, h⟩

/-- The 13 types; the position is the subtype field of a tag-4 id. -/
def intTypesList : List IntType :=
  [ { iri := xsdInteger, lo := none, hi := none },
    { iri := xsdIri "long" rfl, lo := some two63NegInt, hi := some two63m1Int },
    { iri := xsdIri "int" rfl, lo := some two31NegInt, hi := some 2147483647 },
    { iri := xsdIri "short" rfl, lo := some (-32768), hi := some 32767 },
    { iri := xsdIri "byte" rfl, lo := some (-128), hi := some 127 },
    { iri := xsdIri "nonNegativeInteger" rfl, lo := some 0, hi := none },
    { iri := xsdIri "positiveInteger" rfl, lo := some 1, hi := none },
    { iri := xsdIri "nonPositiveInteger" rfl, lo := none, hi := some 0 },
    { iri := xsdIri "negativeInteger" rfl, lo := none, hi := some (-1) },
    { iri := xsdIri "unsignedLong" rfl, lo := some 0, hi := some two64m1Int },
    { iri := xsdIri "unsignedInt" rfl, lo := some 0, hi := some two32m1Int },
    { iri := xsdIri "unsignedShort" rfl, lo := some 0, hi := some 65535 },
    { iri := xsdIri "unsignedByte" rfl, lo := some 0, hi := some 255 } ]

/-- The position and entry of datatype `dt` in `intTypesList` from `i`. -/
def findIntTypeGo (dt : WfIri) : Nat → List IntType → Option (Nat × IntType)
  | _, [] => none
  | i, e :: es => if e.iri == dt then some (i, e) else findIntTypeGo dt (i + 1) es

def findIntType? (dt : WfIri) : Option (Nat × IntType) := findIntTypeGo dt 0 intTypesList

/-! ## Inline codes -/

def boolCode? (lex : String) : Option Nat :=
  if lex == "true" then some (tagBool * two60 + 1)
  else if lex == "false" then some (tagBool * two60) else none

def intCode? (i : Nat) (e : IntType) (lex : String) : Option Nat :=
  match lex.toInt? with
  | none => none
  | some v =>
    if toString v == lex && e.admits v && decide (-two55Int ≤ v) && decide (v < two55Int) then
      some (tagInt * two60 + i * two56 + (v + two55Int).toNat)
    else none

/-- The inline id (as a number) of a term, when it has one. -/
def inlineCode? : Term → Option Nat
  | .literal l =>
    if l.val.langTag.isNone && l.val.direction.isNone then
      if l.val.datatype == xsdBoolean then boolCode? l.val.lexicalForm
      else
        match findIntType? l.val.datatype with
        | some (i, e) => intCode? i e l.val.lexicalForm
        | none => none
    else none
  | _ => none

/-- The term of an inline id. -/
def ofInlineCode? (n : Nat) : Option Term :=
  let tag := n / two60
  if tag == tagBool then
    let p := n % two60
    if p == 1 then mkLit "true" xsdBoolean.val none none
    else if p == 0 then mkLit "false" xsdBoolean.val none none else none
  else if tag == tagInt then
    let sub := (n / two56) % 16
    let p := n % two56
    let v : Int := (p : Int) - two55Int
    match intTypesList[sub]? with
    | none => none
    | some e => if e.admits v then mkLit (toString v) e.iri.val none none else none
  else none

/-! ## Dictionary codes -/

/-- The tag of a dictionary key's class. -/
def classTag (k : Key) : Nat :=
  match k with
  | c :: _ => if c == classBnode then tagBnode else if c == classIri then tagIri else tagLit
  | [] => tagLit

def dictCode (k : Key) (r : Nat) : Nat := classTag k * two60 + r

/-- The id (as a number) of a term in dictionary `d` (keys in rank order).
    Inline terms never enter the dictionary. -/
def toCode? (d : List Key) (t : Term) : Option Nat :=
  match inlineCode? t with
  | some c => some c
  | none =>
    match termKey? t with
    | none => none
    | some k =>
      let r := d.idxOf k
      if r < d.length && decide (r < two60) then some (dictCode k r) else none

/-- The term of an id (as a number) in dictionary `d`. -/
def ofCode? (d : List Key) (n : Nat) : Option Term :=
  let tag := n / two60
  if tag == tagBool || tag == tagInt then ofInlineCode? n
  else if tag == tagBnode || tag == tagIri || tag == tagLit then
    match d[n % two60]? with
    | none => none
    | some k => if classTag k == tag then decodeKey? k else none
  else none

/-! ## The id types -/

/-- A 64-bit global term id. -/
structure TermId where
  bits : UInt64
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A graph id: 0 is the default graph, any other value is the term id of
    the graph name. A separate type from `TermId`. -/
structure GraphId where
  bits : UInt64
  deriving DecidableEq, Hashable, Repr, Inhabited

def GraphId.default : GraphId := ⟨0⟩
def GraphId.ofName (i : TermId) : GraphId := ⟨i.bits⟩
def GraphId.name? (g : GraphId) : Option TermId := if g.bits == 0 then none else some ⟨g.bits⟩

def TermId.tag (i : TermId) : Nat := (i.bits >>> 60).toNat
def TermId.payload (i : TermId) : Nat := (i.bits &&& 0x0FFFFFFFFFFFFFFF).toNat

def toId? (d : List Key) (t : Term) : Option TermId :=
  (toCode? d t).map fun n => ⟨UInt64.ofNat n⟩

def ofId? (d : List Key) (i : TermId) : Option Term := ofCode? d i.bits.toNat

/-! ## Unit tests -/

private def lit (lex dt : String) : Term :=
  match mkLit lex dt none none with
  | some t => t
  | none => .bnode "bad"

private def xsd (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

#guard inlineCode? (lit "072" (xsd "integer")) == none
#guard inlineCode? (lit "+72" (xsd "integer")) == none
#guard inlineCode? (lit "-0" (xsd "integer")) == none
#guard (inlineCode? (lit "72" (xsd "integer"))).isSome
#guard (inlineCode? (lit "-72" (xsd "int"))).isSome
#guard inlineCode? (lit "-1" (xsd "nonNegativeInteger")) == none
#guard inlineCode? (lit "300" (xsd "unsignedByte")) == none
#guard inlineCode? (lit "36028797018963968" (xsd "integer")) == none
#guard (inlineCode? (lit "36028797018963967" (xsd "integer"))).isSome
#guard (inlineCode? (lit "-36028797018963968" (xsd "long"))).isSome
#guard inlineCode? (lit "1" (xsd "boolean")) == none
#guard inlineCode? (lit "7.0E1" (xsd "double")) == none
#guard (inlineCode? (lit "true" (xsd "boolean"))).map (· / two60) == some 5
#guard [lit "0" (xsd "integer"), lit "-72" (xsd "int"), lit "255" (xsd "unsignedByte"),
        lit "36028797018963967" (xsd "integer"), lit "-36028797018963968" (xsd "long"),
        lit "true" (xsd "boolean"), lit "false" (xsd "boolean")].all fun t =>
  match inlineCode? t with
  | some n => ofInlineCode? n == some t
  | none => false
-- the same value in two datatypes: two ids
#guard inlineCode? (lit "72" (xsd "integer")) != inlineCode? (lit "72" (xsd "int"))

private def dict : List Key :=
  [[1, 98], [2, 104, 58, 97], [2, 104, 58, 98], [3, 120]]

#guard (toCode? dict (.bnode "b")).map (· / two60) == some 1
#guard (toCode? dict (.iri ⟨"h:b", rfl⟩)) == some (2 * two60 + 2)
#guard ofCode? dict (2 * two60 + 2) == some (.iri ⟨"h:b", rfl⟩)
#guard ofCode? dict (1 * two60 + 2) == none  -- tag disagrees with the key's class
#guard ofCode? dict (3 * two60 + 3) == some (.literal (Literal.string "x"))
#guard toCode? dict (.iri ⟨"h:c", rfl⟩) == none
#guard (toId? dict (.literal (Literal.string "x"))).map TermId.tag == some 3
#guard (toId? dict (.literal (Literal.string "x"))).map TermId.payload == some 3
#guard GraphId.default.name? == none

end L4Factoidal.Storage.Sbm11
