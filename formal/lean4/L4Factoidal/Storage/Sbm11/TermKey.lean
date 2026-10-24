/-
L4Factoidal.Storage.Sbm11.TermKey — the byte key of an RDF term in the
SBM11 global dictionary (GDV1), wire version 11
(`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.2;
stage 2 of https://github.com/danbri/factoidal/issues/787, work issue
https://github.com/danbri/factoidal/issues/788; class 7, triple terms:
https://github.com/danbri/factoidal/issues/792 item 1).

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
| 7 | triple term (RDF 1.2 Concepts section 3.1) | `len(sk)`, `sk`, `len(pk)`, `pk`, `ok` |

Class 5 puts the datatype IRI first, so the literals of one datatype are one
contiguous range of the dictionary (section 6.1 asks for that; the key text
of section 6.2 has the lexical form first, and this module follows 6.1 and
records the choice in the stage 2 record).

Within classes 1 to 6, unsigned byte order of UTF-8 is Unicode code point
order.

## Class 7: triple terms

`sk` is the key of the subject (class 1 or 2), `pk` the key of the predicate
(class 2), `ok` the key of the object (any class, 7 included), and `len` is
the byte count of the part that follows it as a u32, little-endian
(`writeU32LE`, the integer encoding of GDV1). The object key has no length
field: it ends where the key ends, and the dictionary stores the length of
every key. A triple term whose object is a triple term therefore has the
object's whole key as the suffix of its own key:

    <<( s p <<( s' p' o' )>> )>>  ↦  7 len(sk) sk len(pk) pk 7 len(sk') sk' len(pk') pk' ok'

The key holds the keys of the parts, not their ids, so it decodes without
the dictionary and does not depend on the rank assignment (the stage 2
record, section 7, gives the reasons).

Order within class 7: unsigned byte order of the body, so first by the four
length bytes of the subject key (little-endian: this is not the numeric
order of the lengths), then by the subject key, then by the four length
bytes and the bytes of the predicate key, then by the object key. The keys
with one subject key are one contiguous range of the dictionary, and so are
the keys with one subject key and one predicate key.

## Admission

Encoder admission equals decoder admission:

1. The datatype IRI of a class-5 literal and every language tag contain no
   `0x00` byte, so the separator is found by the first (class 5) or last
   (classes 4 and 6) `0x00` of the body. A lexical form may contain `0x00`.
2. A language tag is in lower case (`String.toLower`, ASCII): RDF 1.1
   Concepts section 3.3 makes the value space of language tags lower case.
   The packer folds tags with `normalizeTerm` before it builds a key (inside
   triple terms too), so `@en-US` and `@en-us` are one key and one id.
3. A class-5 literal is not of datatype `xsd:string` (that literal is
   class 3), and the decoder rebuilds the literal through `RDF.literalWf`.
4. Class 7: the subject key and the predicate key each have fewer than
   `2^32` bytes (`partFits`, the width of `len`). The decoder admits a
   subject part that decodes to an IRI or a blank node, a predicate part
   that decodes to an IRI, and an object part that decodes to any admitted
   term. `RDF.Term.tripleTerm` already fixes the subject to an IRI or a
   blank node and the predicate to an IRI.

The decoder checks the same conditions on what it read. The round trip is
`TermKeyTheorems.decodeKey?_termKey?`; injectivity of keys on admitted
terms follows from it (`termKey?_injective`).

A decoder of the stage 2 code returns `none` for class byte 7
(`decodeAtom?` is that decoder: `TermKeyTheorems.decodeAtom?_classTriple`),
so class 7 adds keys without changing the meaning of a byte an older reader
admits.

## Loops

Nesting of triple terms grows with the input, so every function over it is a
loop: `decodeTripleGo` is a tail call with fuel (the key length), and
`termKey?` and `normalizeTerm` (structural recursion on the object position,
the specification) run as the tail-recursive twins `termKeyGo` and
`normalizeGo` through the `@[csimp]` theorems `termKey?_eq_impl` and
`normalizeTerm_eq_impl`, proved below. `wrapLevels` is a `List.foldl`.
`splitFirstGo` is a tail call; every other function is straight-line.
`tests/stack/run.sh` case `sbm11-triple-term` encodes and decodes a triple
term nested 300,000 deep under a 512 KB stack. No `sorry`, no user `axiom`,
no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.Storage.Bytes
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF
open L4Factoidal.Storage (bytesOfString stringOfBytes? readU32LE writeU32LE)
open L4Factoidal (two32)

/-- A dictionary key: class byte and body. -/
abbrev Key := List UInt8

def classBnode : UInt8 := 1
def classIri : UInt8 := 2
def classString : UInt8 := 3
def classLang : UInt8 := 4
def classTyped : UInt8 := 5
def classDirLang : UInt8 := 6
def classTriple : UInt8 := 7

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

/-- The key of a term that is not a triple term (classes 1 to 6); `none` for
    a triple term and for a literal that is not admitted. -/
def atomKey? : Term → Option Key
  | .bnode b => some (classBnode :: bytesOfString b)
  | .iri i => some (classIri :: bytesOfString i.val)
  | .literal l => literalKey? l.val
  | .tripleTerm _ _ _ => none

/-! ## Class 7: the parts of a triple term -/

/-- The key of a subject (class 1 or 2). -/
def subjectKey : Subject → Key
  | .iri i => classIri :: bytesOfString i.val
  | .bnode b => classBnode :: bytesOfString b

/-- The key of a predicate (class 2). -/
def iriKey (p : WfIri) : Key := classIri :: bytesOfString p.val

/-- A part fits its u32 length field. -/
def partFits (k : List UInt8) : Bool := k.length < two32

/-- A part with its length field. -/
def lenPart (k : List UInt8) : List UInt8 := writeU32LE (UInt32.ofNat k.length) ++ k

/-- The bytes of a class-7 key after the class byte and before the object
    key: `len(sk) sk len(pk) pk`; `none` when a part does not fit its length
    field. -/
def tripleHead? (s : Subject) (p : WfIri) : Option (List UInt8) :=
  if partFits (subjectKey s) && partFits (iriKey p) then
    some (lenPart (subjectKey s) ++ lenPart (iriKey p))
  else none

/-- The key of a term (`none`: not admitted, see the module header). This is
    the specification; the compiled code runs `termKeyImpl`
    (`termKey?_eq_impl`). -/
def termKey? : Term → Option Key
  | .tripleTerm s p o =>
    match tripleHead? s p, termKey? o with
    | some h, some ok => some (classTriple :: (h ++ ok))
    | _, _ => none
  | t => atomKey? t

/-- `termKey?` as a loop down the object positions: `accRev` holds the bytes
    of the enclosing triple terms, reversed. -/
def termKeyGo (accRev : List UInt8) : Term → Option Key
  | .tripleTerm s p o =>
    match tripleHead? s p with
    | some h => termKeyGo (List.reverseAux (classTriple :: h) accRev) o
    | none => none
  | t => (atomKey? t).map (List.reverseAux accRev)

def termKeyImpl (t : Term) : Option Key := termKeyGo [] t

theorem termKeyGo_eq (t : Term) :
    ∀ accRev, termKeyGo accRev t = (termKey? t).map (accRev.reverse ++ ·) := by
  induction t with
  | iri i => intro accRev; simp [termKeyGo, termKey?, atomKey?, List.reverseAux_eq]
  | bnode b => intro accRev; simp [termKeyGo, termKey?, atomKey?, List.reverseAux_eq]
  | literal l =>
    intro accRev
    show (literalKey? l.val).map (List.reverseAux accRev) = (literalKey? l.val).map _
    cases literalKey? l.val <;> simp [List.reverseAux_eq]
  | tripleTerm s p o ih =>
    intro accRev
    simp only [termKeyGo, termKey?]
    cases h : tripleHead? s p with
    | none => simp
    | some hd =>
      simp only
      rw [ih]
      cases termKey? o with
      | none => simp
      | some ok => simp [List.reverseAux_eq]

@[csimp] theorem termKey?_eq_impl : @termKey? = @termKeyImpl := by
  funext t
  simp [termKeyImpl, termKeyGo_eq]

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

/-- The term of a key of classes 1 to 6; inverse of `atomKey?`. This is the
    whole decoder of stage 2: it returns `none` for class 7. -/
def decodeAtom? (k : Key) : Option Term :=
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

/-- A subject part: a key that decodes to an IRI or a blank node. -/
def subjectOfKey? (k : Key) : Option Subject :=
  match decodeAtom? k with
  | some (.iri i) => some (.iri i)
  | some (.bnode b) => some (.bnode b)
  | _ => none

/-- A predicate part: a key that decodes to an IRI. -/
def iriOfKey? (k : Key) : Option WfIri :=
  match decodeAtom? k with
  | some (.iri i) => some i
  | _ => none

/-- A part with its length field: the part and the bytes after it. -/
def splitPart? (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match readU32LE bs 0 with
  | none => none
  | some n =>
    let rest := bs.drop 4
    let part := rest.take n.toNat
    if part.length == n.toNat then some (part, rest.drop n.toNat) else none

/-- The triple terms around an object, innermost first, put back around it. -/
def wrapLevels (levels : List (Subject × WfIri)) (o : Term) : Term :=
  levels.foldl (fun acc sp => .tripleTerm sp.1 sp.2 acc) o

/-- Decode a class-7 body (the bytes after the class byte): read the subject
    and the predicate part; an object key of class 7 continues the loop one
    level down, any other is decoded and the levels are put around it.
    `fuel` bounds the levels; `decodeKey?` passes the body length plus one,
    and each level reads at least ten bytes. -/
def decodeTripleGo : Nat → List (Subject × WfIri) → List UInt8 → Option Term
  | 0, _, _ => none
  | fuel + 1, levels, body =>
    match splitPart? body with
    | none => none
    | some (sk, r1) =>
      match splitPart? r1 with
      | none => none
      | some (pk, ok) =>
        match subjectOfKey? sk, iriOfKey? pk with
        | some s, some p =>
          match ok with
          | c :: body' =>
            if c == classTriple then decodeTripleGo fuel ((s, p) :: levels) body'
            else (decodeAtom? ok).map (wrapLevels ((s, p) :: levels))
          | [] => none
        | _, _ => none

/-- The term of a key; inverse of `termKey?` on admitted terms. -/
def decodeKey? (k : Key) : Option Term :=
  match k with
  | [] => none
  | c :: body =>
    if c == classTriple then decodeTripleGo (body.length + 1) [] body else decodeAtom? k

/-! ## The executable key as bytes, and the tag fold -/

/-- The key as a `ByteArray` (the packer's form). -/
def termKeyBytes? (t : Term) : Option ByteArray := (termKey? t).map fun k => ⟨k.toArray⟩

/-- Fold the language tag of a literal to lower case (RDF 1.1 Concepts
    section 3.3); `normalizeTerm` of a literal. -/
def normalizeLit (l : WfLiteral) : Term :=
  match l.val.langTag with
  | none => .literal l
  | some tag =>
    let v : Literal := { l.val with langTag := some tag.toLower }
    if h : literalWf v then .literal ⟨v, h⟩ else .literal l

/-- `normalizeLit` with a fast path: a language tag that is already in lower
    case (the common case) gives the literal back without a new `Literal` and
    without the `literalWf` test (`normalizeLit_eq_fast`;
    https://github.com/danbri/factoidal/issues/900). -/
def normalizeLitFast (l : WfLiteral) : Term :=
  match l.val.langTag with
  | none => .literal l
  | some tag => if tag.toLower == tag then .literal l else normalizeLit l

theorem normalizeLit_eq_fast (l : WfLiteral) : normalizeLit l = normalizeLitFast l := by
  obtain ⟨⟨lex, dt, lt, dir⟩, hl⟩ := l
  cases lt with
  | none => rfl
  | some tag =>
    simp only [normalizeLitFast]
    by_cases h : tag.toLower = tag
    · simp only [h, beq_self_eq_true, if_true, normalizeLit]
      rw [dif_pos (by simpa [h] using hl)]
    · simp [h]

/-- Fold every language tag of a term to lower case, inside triple terms
    too (the object position is the only one that can hold a literal). This
    is the specification; the compiled code runs `normalizeImpl`
    (`normalizeTerm_eq_impl`). -/
def normalizeTerm : Term → Term
  | .literal l => normalizeLit l
  | .tripleTerm s p o => .tripleTerm s p (normalizeTerm o)
  | t => t

/-- `normalizeTerm` as a loop down the object positions: `levels` holds the
    enclosing triple terms, innermost first. -/
def normalizeGo (levels : List (Subject × WfIri)) : Term → Term
  | .tripleTerm s p o => normalizeGo ((s, p) :: levels) o
  | .literal l => wrapLevels levels (normalizeLitFast l)
  | t => wrapLevels levels t

def normalizeImpl (t : Term) : Term := normalizeGo [] t

theorem wrapLevels_cons (s : Subject) (p : WfIri) (ls : List (Subject × WfIri)) (x : Term) :
    wrapLevels ((s, p) :: ls) x = wrapLevels ls (.tripleTerm s p x) := by
  simp [wrapLevels]

theorem normalizeGo_eq (t : Term) :
    ∀ levels, normalizeGo levels t = wrapLevels levels (normalizeTerm t) := by
  induction t with
  | iri i => intro levels; rfl
  | bnode b => intro levels; rfl
  | literal l => intro levels; simp only [normalizeGo, normalizeTerm, normalizeLit_eq_fast]
  | tripleTerm s p o ih =>
    intro levels
    simp only [normalizeGo, normalizeTerm]
    rw [ih, wrapLevels_cons]

@[csimp] theorem normalizeTerm_eq_impl : @normalizeTerm = @normalizeImpl := by
  funext t
  simp [normalizeImpl, normalizeGo_eq, wrapLevels]

/-! ## Unit tests -/

private def iriT (s : String) : Term :=
  if h : isIri s then .iri ⟨s, h⟩ else .bnode s

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"x:invalid", rfl⟩

private def typedT (lex dt : String) : Term :=
  match mkLit lex dt none none with
  | some t => t
  | none => .bnode "bad"

private def rt (t : Term) : Bool :=
  match termKey? t with
  | some k => decodeKey? k == some t
  | none => false

/-- `<<( s p o )>>` with an IRI subject. -/
private def tt (s p : String) (o : Term) : Term := .tripleTerm (.iri (iriW s)) (iriW p) o

/-- A triple term nested `n` deep in the object position, by a loop. -/
private def nestGo : Nat → Term → Term
  | 0, t => t
  | n + 1, t => nestGo n (tt "http://ex/s" "http://ex/p" t)

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
-- triple terms (class 7): every object class, a blank-node subject, nesting
#guard rt (.tripleTerm (.bnode "s") ⟨"http://p", rfl⟩ (.bnode "o"))
#guard rt (tt "http://ex/s" "http://ex/p" (iriT "http://ex/o"))
#guard rt (tt "http://ex/s" "http://ex/p" (.literal (Literal.string "with\u0000zero")))
#guard rt (tt "http://ex/s" "http://ex/p" (.literal (Literal.langString "chat" "fr")))
#guard rt (tt "http://ex/s" "http://ex/p" (.literal (Literal.dirLangString "x" "ar" .ltr)))
#guard rt (tt "http://ex/s" "http://ex/p" (typedT "1" "http://www.w3.org/2001/XMLSchema#integer"))
#guard rt (tt "http://ex/s" "http://ex/p" (tt "http://ex/s2" "http://ex/p2" (.bnode "o")))
#guard rt (nestGo 3 (.literal (Literal.langString "x" "en")))
#guard rt (nestGo 2000 (iriT "http://ex/o"))
-- an upper-case tag inside a triple term: not admitted until normalised, and
-- the fold reaches the innermost object
#guard termKey? (nestGo 2 (.literal (Literal.langString "x" "EN"))) == none
#guard rt (normalizeTerm (nestGo 2 (.literal (Literal.langString "x" "EN"))))
#guard normalizeTerm (nestGo 2 (.literal (Literal.langString "x" "EN"))) ==
  nestGo 2 (.literal (Literal.langString "x" "en"))
-- the key layout: 7, u32 length, subject key, u32 length, predicate key, object key
#guard termKey? (.tripleTerm (.bnode "s") ⟨"a:p", rfl⟩ (.bnode "o")) ==
  some [7, 2, 0, 0, 0, 1, 115, 4, 0, 0, 0, 2, 97, 58, 112, 1, 111]
-- a nested key ends with the object's whole key
#guard (termKey? (tt "a:s" "a:p" (tt "a:t" "a:q" (.bnode "o")))).map (·.drop 17) ==
  termKey? (tt "a:t" "a:q" (.bnode "o"))
-- the decoder refuses: a short length field, a length past the end, a
-- literal subject part, a blank-node predicate part, an empty object, an
-- unknown object class, an empty body
#guard decodeKey? [7, 2, 0, 0] == none
#guard decodeKey? [7, 9, 0, 0, 0, 1, 115, 4, 0, 0, 0, 2, 97, 58, 112, 1, 111] == none
#guard decodeKey? [7, 2, 0, 0, 0, 3, 115, 4, 0, 0, 0, 2, 97, 58, 112, 1, 111] == none
#guard decodeKey? [7, 2, 0, 0, 0, 1, 115, 4, 0, 0, 0, 1, 97, 58, 112, 1, 111] == none
#guard decodeKey? [7, 2, 0, 0, 0, 1, 115, 4, 0, 0, 0, 2, 97, 58, 112] == none
#guard decodeKey? [7, 2, 0, 0, 0, 1, 115, 4, 0, 0, 0, 2, 97, 58, 112, 9, 111] == none
#guard decodeKey? [7] == none
-- the stage 2 decoder refuses class 7
#guard decodeAtom? [7, 2, 0, 0, 0, 1, 115, 4, 0, 0, 0, 2, 97, 58, 112, 1, 111] == none
-- classes sort bnode < IRI < string < lang < typed < dirLang < triple
#guard (termKey? (.bnode "z")).map (·.head?) == some (some 1)
#guard (termKey? (typedT "1" "http://www.w3.org/2001/XMLSchema#integer")).map (·.take 4) ==
  some [5, 104, 116, 116]
#guard (termKey? (tt "a:s" "a:p" (.bnode "o"))).map (·.head?) == some (some 7)
#guard splitLast [1, 0, 2, 0, 3] == some ([1, 0, 2], [3])
#guard splitFirst [1, 0, 2, 0, 3] == some ([1], [2, 0, 3])
#guard decodeKey? [9, 1] == none
#guard decodeKey? [] == none

end L4Factoidal.Storage.Sbm11
