/-
L4Factoidal.Storage.Sbm11.TermKey — the byte key of an RDF term in the
SBM11 global dictionary (GDV1), wire version 11
(`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.2;
stage 2 of https://github.com/danbri/factoidal/issues/787, work issue
https://github.com/danbri/factoidal/issues/788).

The dictionary is sorted by unsigned byte comparison of these keys. A key
is a class byte and then a body:

| Class | Term | Body |
|---:|---|---|
| 1 | blank node | UTF-8 label |
| 2 | IRI | UTF-8 IRI |
| 3 | literal of datatype `xsd:string` | UTF-8 lexical form |
| 4 | language-tagged string (`rdf:langString`) | lexical form, `0x00`, language tag |
| 5 | literal of any other datatype | datatype IRI, `0x00`, lexical form |
| 6 | directional language-tagged string (`rdf:dirLangString`) | lexical form, `0x00`, language tag, `0x00`, direction byte (1 `ltr`, 2 `rtl`) |

Class 5 puts the datatype IRI first, so the literals of one datatype are one
contiguous range of the dictionary (section 6.1 asks for that; the key text
of section 6.2 has the lexical form first, and this module follows 6.1 and
records the choice in the stage 2 record).

Within a class, unsigned byte order of UTF-8 is Unicode code point order.

## Admission

Encoder admission equals decoder admission:

1. A triple term (RDF 1.2) has no key. Stage 2 refuses it.
2. The datatype IRI of a class-5 literal and every language tag contain no
   `0x00` byte, so the separator is found by the first (class 5) or last
   (classes 4 and 6) `0x00` of the body. A lexical form may contain `0x00`.
3. A language tag is in lower case (`String.toLower`, ASCII): RDF 1.1
   Concepts section 3.3 makes the value space of language tags lower case.
   The packer folds tags with `normalizeTerm` before it builds a key, so
   `@en-US` and `@en-us` are one key and one id.
4. A class-5 literal is not of datatype `xsd:string` (that literal is
   class 3), and the decoder rebuilds the literal through `RDF.literalWf`.

The decoder checks the same conditions on what it read. The round trip is
`TermKeyTheorems.decodeKey?_termKey?`; injectivity of keys on admitted
terms follows from it (`termKey?_injective`).

## Loops

`splitFirstGo` and `lowerTermTag` are tail calls; every other function is
straight-line. No `sorry`, no user `axiom`, no `native_decide`, no
`partial`.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.Storage.DeltaLog

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF
open L4Factoidal.Storage (bytesOfString stringOfBytes?)

/-- A dictionary key: class byte and body. -/
abbrev Key := List UInt8

def classBnode : UInt8 := 1
def classIri : UInt8 := 2
def classString : UInt8 := 3
def classLang : UInt8 := 4
def classTyped : UInt8 := 5
def classDirLang : UInt8 := 6

/-- No byte of `bs` is `0x00`. -/
def noZero (bs : List UInt8) : Bool := bs.all (· != 0)

def dirByte : TextDirection → UInt8
  | .ltr => 1
  | .rtl => 2

def dirOfByte? (b : UInt8) : Option TextDirection :=
  if b == 1 then some .ltr else if b == 2 then some .rtl else none

/-- A language tag the dictionary admits: no `0x00` byte, lower case. -/
def tagAdmitted (tag : String) : Bool :=
  noZero (bytesOfString tag) && tag.toLower == tag

/-- The key of a literal (`none`: not admitted). -/
def literalKey? (l : Literal) : Option Key :=
  let lex := bytesOfString l.lexicalForm
  match l.langTag, l.direction with
  | none, none =>
      if l.datatype == xsdString then some (classString :: lex)
      else
        let dt := bytesOfString l.datatype.val
        if noZero dt then some (classTyped :: (dt ++ 0 :: lex)) else none
  | some tag, none =>
      if tagAdmitted tag then some (classLang :: (lex ++ 0 :: bytesOfString tag)) else none
  | some tag, some d =>
      if tagAdmitted tag then
        some (classDirLang :: ((lex ++ 0 :: bytesOfString tag) ++ [0, dirByte d]))
      else none
  | none, some _ => none

/-- The key of a term (`none`: not admitted, see the module header). -/
def termKey? : Term → Option Key
  | .bnode b => some (classBnode :: bytesOfString b)
  | .iri i => some (classIri :: bytesOfString i.val)
  | .literal l => literalKey? l.val
  | .tripleTerm _ _ _ => none

/-! ## Splitting a body at a `0x00` separator -/

/-- The bytes before the first `0x00` (reversed in `accRev`) and the bytes
    after it. -/
def splitFirstGo : List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | _, [] => none
  | accRev, x :: xs => if x == 0 then some (accRev.reverse, xs) else splitFirstGo (x :: accRev) xs

def splitFirst (bs : List UInt8) : Option (List UInt8 × List UInt8) := splitFirstGo [] bs

/-- Split at the LAST `0x00`. -/
def splitLast (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  (splitFirst bs.reverse).map fun p => (p.2.reverse, p.1.reverse)

/-! ## Decoding -/

/-- Rebuild a literal from its strings; refuses a datatype string that is
    not an IRI and a combination `RDF.literalWf` refuses. -/
def mkLit (lex dt : String) (tag : Option String) (dir : Option TextDirection) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩, langTag := tag, direction := dir }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

def decodeIri? (body : List UInt8) : Option Term :=
  match stringOfBytes? body with
  | none => none
  | some s => if h : isIri s then some (.iri ⟨s, h⟩) else none

def decodeLang? (body : List UInt8) : Option Term :=
  match splitLast body with
  | none => none
  | some (lexB, tagB) =>
    match stringOfBytes? lexB, stringOfBytes? tagB with
    | some lex, some tag =>
        if tagAdmitted tag then mkLit lex rdfLangString.val (some tag) none else none
    | _, _ => none

def decodeTyped? (body : List UInt8) : Option Term :=
  match splitFirst body with
  | none => none
  | some (dtB, lexB) =>
    match stringOfBytes? dtB, stringOfBytes? lexB with
    | some dt, some lex =>
        if noZero dtB && dt != xsdString.val then mkLit lex dt none none else none
    | _, _ => none

def decodeDirLang? (body : List UInt8) : Option Term :=
  match splitLast body with
  | none => none
  | some (front, dB) =>
    match dB with
    | [d] =>
      match dirOfByte? d, splitLast front with
      | some dir, some (lexB, tagB) =>
        match stringOfBytes? lexB, stringOfBytes? tagB with
        | some lex, some tag =>
            if tagAdmitted tag then mkLit lex rdfDirLangString.val (some tag) (some dir) else none
        | _, _ => none
      | _, _ => none
    | _ => none

/-- The term of a key; inverse of `termKey?` on admitted terms. -/
def decodeKey? (k : Key) : Option Term :=
  match k with
  | [] => none
  | c :: body =>
    if c == classBnode then (stringOfBytes? body).map Term.bnode
    else if c == classIri then decodeIri? body
    else if c == classString then (stringOfBytes? body).map fun s => .literal (Literal.string s)
    else if c == classLang then decodeLang? body
    else if c == classTyped then decodeTyped? body
    else if c == classDirLang then decodeDirLang? body
    else none

/-! ## The executable key as bytes, and the tag fold -/

/-- The key as a `ByteArray` (the packer's form). -/
def termKeyBytes? (t : Term) : Option ByteArray := (termKey? t).map fun k => ⟨k.toArray⟩

/-- Fold the language tag of a literal to lower case (RDF 1.1 Concepts
    section 3.3). Every other term is unchanged. -/
def normalizeTerm : Term → Term
  | .literal l =>
    match l.val.langTag with
    | none => .literal l
    | some tag =>
      let v : Literal := { l.val with langTag := some tag.toLower }
      if h : literalWf v then .literal ⟨v, h⟩ else .literal l
  | t => t

/-! ## Unit tests -/

private def iriT (s : String) : Term :=
  if h : isIri s then .iri ⟨s, h⟩ else .bnode s

private def typedT (lex dt : String) : Term :=
  match mkLit lex dt none none with
  | some t => t
  | none => .bnode "bad"

private def rt (t : Term) : Bool :=
  match termKey? t with
  | some k => decodeKey? k == some t
  | none => false

#guard rt (iriT "http://example.org/a")
#guard rt (.bnode "b0")
#guard rt (.literal (Literal.string "plain"))
#guard rt (.literal (Literal.string "with\u0000zero"))
#guard rt (.literal (Literal.langString "chat" "fr"))
#guard rt (.literal (Literal.langString "a\u0000b" "en-us"))
#guard rt (.literal (Literal.dirLangString "x" "ar" .rtl))
#guard rt (typedT "072" "http://www.w3.org/2001/XMLSchema#integer")
#guard rt (typedT "7.0E1" "http://www.w3.org/2001/XMLSchema#double")
-- an upper-case tag is not admitted until normalised
#guard termKey? (.literal (Literal.langString "x" "en-US")) == none
#guard rt (normalizeTerm (.literal (Literal.langString "x" "en-US")))
#guard normalizeTerm (.literal (Literal.langString "x" "en-US")) ==
  normalizeTerm (.literal (Literal.langString "x" "en-us"))
#guard termKey? (.tripleTerm (.bnode "s") ⟨"http://p", rfl⟩ (.bnode "o")) == none
-- classes sort bnode < IRI < string < lang < typed < dirLang
#guard (termKey? (.bnode "z")).map (·.head?) == some (some 1)
#guard (termKey? (typedT "1" "http://www.w3.org/2001/XMLSchema#integer")).map (·.take 4) ==
  some [5, 104, 116, 116]
#guard splitLast [1, 0, 2, 0, 3] == some ([1, 0, 2], [3])
#guard splitFirst [1, 0, 2, 0, 3] == some ([1], [2, 0, 3])
#guard decodeKey? [9, 1] == none
#guard decodeKey? [] == none

end L4Factoidal.Storage.Sbm11
