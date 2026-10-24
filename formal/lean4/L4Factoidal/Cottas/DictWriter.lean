/-
L4Factoidal.Cottas.DictWriter — the COTTAS `.dict` serialiser.

Port of `formal/fstar/RDF.CottasStore.DictWriter.fst` (669 lines). The
writer whose reader is `Cottas/OnDiskIndex.lean`.

```
Header (32 bytes, little-endian throughout):
  [  0: magic        u32  'COTD' = 0x44544F43 ]
  [  4: version      u32 ]
  [  8: n            u32  token count ]
  [ 12: padding      u32  reserved 0 ]
  [ 16: idsOffset    u64  = 32 ]
  [ 24: tokensOffset u64  = 32 + 4n ]

ids:        u32[n]      ids[i] = i, because the tokens are stored
                        sorted and ids are assigned in that order
tokenOffs:  u64[n + 1]  absolute byte offsets into the file, the last
                        one the end sentinel
token data: the UTF-8 bytes of the tokens, concatenated
```

## Byte lengths, and a defect class that cannot arise here

The offsets are UTF-8 BYTE lengths. The F\* module's own comment
records that it had the codepoint-versus-byte defect
(<https://github.com/danbri/factoidal/issues/445>) latently until
`RDF.Bytes.fst` stopped agreeing with `String.length` by accident: the
two coincided while `bytes_of_string` WAS `String.list_of_string`, and
that holds only for ASCII. This is the same defect class as
<https://github.com/danbri/factoidal/issues/551> in `HDT.Dictionary`.

In Lean the writer works from `String.toUTF8` and the reader from
`String.fromUTF8?`, so there is no length to pick wrongly. A `#guard`
below round-trips non-ASCII tokens through the whole file to keep that
checked rather than assumed.

## No live callers, in either tree

The F\* header says so: "This module has zero live callers today (the
current `import` write path uses
`RDF.CottasStore.BaseWriter.serialize_cottas_v2`, not this `.dict`
format)". Nothing in the Lean tree calls it either. It is the writer
half of the format `OnDiskIndex` reads, and the two are checked
against each other below.

## The sortedness invariant stays a caller obligation

`ids[i] = i` is only correct when the tokens are stored in ascending
order, and the F\* module makes that the caller's job. So does this one.

That differs from `OffsetsWriter` and `CompoundPresenceWriter`, where
the same kind of invariant was moved INTO the writer and proved. The
difference is the key type: those sort by a `Nat` and
`Cottas/SortByKey.lean` proves that sort correct. Sorting by `String`
needs the trichotomy and transitivity of `String`'s `compare`, which
nothing in this tree has proved. `sortTokens` below is provided and
`#guard`-checked; it is not proved sorted, and that is what would close
the gap.
-/
import L4Factoidal.Cottas.OnDiskIndex
import L4Factoidal.Cottas.OffsetsWriter
import L4Factoidal.NatBounds
import L4Factoidal.RDF.TermJson

namespace L4Factoidal.Cottas

def dictWriterHeaderSize : Nat := 32
def dictIdSize : Nat := 4
def dictOffsetSize : Nat := 8

/-- UTF-8 byte length, which is what the offsets count. -/
def tokByteLen (t : String) : Nat := t.toUTF8.size

def buildDictIds (n : Nat) : List UInt8 :=
  (List.range n).flatMap (fun i => writeU32Le (UInt32.ofNat i))

/-- The `n + 1` absolute offsets: the start of each token's bytes, then
    the end sentinel. -/
def buildDictOffs (tokenDataOffset : Nat) (tokens : List String) : List Nat :=
  prefixOffsets tokenDataOffset (tokens.map tokByteLen)

def buildDictData (tokens : List String) : List UInt8 :=
  tokens.flatMap (fun t => t.toUTF8.toList)

def buildDictHeader (n idsOffset tokensOffset : Nat) : List UInt8 :=
  writeU32Le cotdMagicU32 ++ writeU32Le layoutVersion ++
  writeU32Le (UInt32.ofNat n) ++ writeU32Le 0 ++
  writeU64Le idsOffset ++ writeU64Le tokensOffset

/-- The whole `.dict` file. `none` when the token count overflows u32
    or the data offset overflows u64.

    ⚠️ CALLER OBLIGATION: `tokens` must be in ascending order. `ids[i]
    = i` depends on it, and so does the reader's binary search. -/
def serializeDict (sortedTokens : List String) : Option ByteArray :=
  let n := sortedTokens.length
  if n ≥ two32 then none
  else
    let idsOffset := dictWriterHeaderSize
    let tokensOffset := idsOffset + dictIdSize * n
    let dataOffset := tokensOffset + dictOffsetSize * (n + 1)
    if dataOffset ≥ two64 then none
    else some ⟨(buildDictHeader n idsOffset tokensOffset ++
                buildDictIds n ++
                (buildDictOffs dataOffset sortedTokens).flatMap writeU64Le ++
                buildDictData sortedTokens).toArray⟩

/-! ## Reading it back -/

def parseDict (bs : ByteArray) : Option (List String) := do
  let h ← readDictHeader bs
  if !h.ok then none else do
  let offs ← (List.range (h.numTokens + 1)).mapM
               (fun i => readDictU64Le bs (h.tokensOffset + 8 * i))
  (List.range h.numTokens).mapM (fun i => do
    let s := offs[i]!
    let e := offs[i + 1]!
    if e < s || e > bs.size then none else String.fromUTF8? (bs.extract s e))

/-! ## An unproved sort

Provided so a caller has one to hand. Its output is `#guard`-checked
below; it carries no sortedness theorem, for the reason in the module
header. -/

def insertToken (x : String) : List String → List String
  | []      => [x]
  | y :: ys => match compare x y with
               | .lt => x :: y :: ys
               | .eq => y :: ys
               | .gt => y :: insertToken x ys

def sortTokens : List String → List String
  | []      => []
  | x :: xs => insertToken x (sortTokens xs)

/-! ## RDF terms: one token per RDF term (https://github.com/danbri/factoidal/issues/977)

A token is a string, so `serializeDict` gives `"x"@en` and `"x"@EN` two ids
when it is given both spellings. The term layer below writes the token of
the fold of each term (`Storage.TermFold.foldTerm`, language tags in lower
case, RDF 1.1 Concepts section 3.3) in RDF 1.2 N-Triples term syntax, so the
two literals are one token; `sortTokens` removes the repeat. A reader folds
the term of a token it decodes and the term it looks up.

No COTD file was written before this layer (the module header: no live
callers), so there is no earlier file whose meaning could change. A file from
another writer with an upper-case tag in a token decodes with the tag in
lower case and fails `termRoundTripsAll` (the lookup of the folded term does
not find the stored token); `DictTheorems.cotd_dictInjective` applies only
when that test holds. -/

/-- The token of an RDF term: the RDF 1.2 N-Triples form of its fold. -/
def termToken? (t : RDF.Term) : Option String :=
  (Syntax.Term.toNTriples .rdf12 (Storage.TermFold.foldTerm t)).toOption

/-- The term of a token, folded. -/
def tokenTerm? (tok : String) : Option RDF.Term :=
  (RDF.TermJson.readTermString tok).map Storage.TermFold.foldTerm

/-- The `.dict` file of a list of RDF terms: one token per RDF term, sorted. -/
def serializeTermDict (terms : List RDF.Term) : Option ByteArray := do
  let toks ← terms.mapM termToken?
  serializeDict (sortTokens toks)

/-- The id of an RDF term in a `.dict` file. -/
def dictEncodeTerm (bs : ByteArray) (h : DictHeader) (t : RDF.Term) : Option Nat :=
  (termToken? t).bind (dictEncodeToken bs h)

/-- The RDF term of an id in a `.dict` file, folded. -/
def dictDecodeTerm (bs : ByteArray) (h : DictHeader) (id : Nat) : Option RDF.Term :=
  (dictDecodeToken bs h id).bind tokenTerm?

/-- Every id decodes to a term whose id is that id: one id per RDF term. -/
def termRoundTripsAll (bs : ByteArray) (h : DictHeader) : Bool :=
  (List.range h.numTokens).all fun i =>
    match dictDecodeTerm bs h i with
    | some t => dictEncodeTerm bs h t == some i
    | none => false

/-! ## Build-time checks

### The round trip -/

private def dtoks : List String := sortTokens ["zebra", "apple", "mango", "banana"]

#guard dtoks == ["apple", "banana", "mango", "zebra"]

private def dwBytes : ByteArray := (serializeDict dtoks).getD ByteArray.empty

#guard parseDict dwBytes == some dtoks
#guard (serializeDict []).isSome
#guard parseDict ((serializeDict []).getD ByteArray.empty) == some []

/-! ### The file this writer produces is the file `OnDiskIndex` reads

Two modules ported separately, checked against each other rather than
each against a restatement of the format. -/

private def dwHeader : DictHeader := (readDictHeader dwBytes).getD default

#guard dwHeader.ok
#guard dwHeader.numTokens == 4
#guard dwHeader.idsOffset == 32
#guard dwHeader.tokensOffset == 32 + 4 * 4

#guard (dtoks.zipIdx).all (fun (t, i) => dictDecodeToken dwBytes dwHeader i == some t)
#guard (dtoks.zipIdx).all (fun (t, i) => dictEncodeToken dwBytes dwHeader t == some i)
#guard (dictEncodeToken dwBytes dwHeader "durian").isNone

/-! `ids[i] = i` here, because the writer stores the tokens sorted.
    The reader does not require that — `OnDiskIndex`'s own fixture uses
    a permuted `ids` — so this pins the writer's choice, not the
    format's. -/

#guard (List.range 4).all (fun i => readIdAt dwBytes dwHeader i == some i)

/-! ### Non-ASCII tokens survive, offsets and all

The F\* module had the codepoint-versus-byte defect latently. Here the
offsets come from `String.toUTF8` and the reader from
`String.fromUTF8?`, and this checks the whole file rather than the
lengths alone. Every token below is multi-byte, and `"日本語"` is three
bytes per character. -/

private def utoks : List String := sortTokens ["é", "ü", "中", "日本語", "a"]
private def uBytes : ByteArray := (serializeDict utoks).getD ByteArray.empty
private def uHeader : DictHeader := (readDictHeader uBytes).getD default

#guard parseDict uBytes == some utoks
#guard (utoks.zipIdx).all (fun (t, i) => dictDecodeToken uBytes uHeader i == some t)
#guard (utoks.zipIdx).all (fun (t, i) => dictEncodeToken uBytes uHeader t == some i)

/-! And the offsets really are byte counts, not character counts: the
    file is longer than a character-counted one would be. -/

#guard tokByteLen "日本語" == 9
#guard "日本語".length == 3
#guard uBytes.size == 32 + 4 * 5 + 8 * 6 + (utoks.map tokByteLen).foldl (· + ·) 0

/-! ### Empty tokens and duplicates

An empty token is a zero-length slice, which must decode as `""` rather
than as a failure. `sortTokens` drops duplicates, so a caller handing
duplicates to `serializeDict` directly is the case that would break
`ids[i] = i`'s intent — the writer does not check it, exactly as F\*
does not. -/

private def etoks : List String := ["", "a"]
private def eBytes : ByteArray := (serializeDict etoks).getD ByteArray.empty

#guard parseDict eBytes == some ["", "a"]
#guard dictDecodeToken eBytes ((readDictHeader eBytes).getD default) 0 == some ""
#guard sortTokens ["b", "a", "b"] == ["a", "b"]

/-! ### A `.presence` or `.p.offsets` file is not a `.dict` file -/

#guard (parseDict (mkPresence 2 2 [])).isNone
#guard (parseDict ((buildOffsets 1 1 [[3]]).getD ByteArray.empty)).isNone

/-! ### A truncated file is refused, not read short -/

#guard (parseDict (dwBytes.extract 0 (dwBytes.size - 3))).isNone

/-! ### RDF terms: one token per RDF term -/

private def litEN : RDF.Term := .literal (RDF.Literal.langString "x" "EN")
private def liten : RDF.Term := .literal (RDF.Literal.langString "x" "en")
private def exA : RDF.Term := .iri ⟨"http://example.org/a", by decide⟩

-- tokens are strings: the two spellings are two tokens, two ids
#guard (sortTokens ["\"x\"@EN", "\"x\"@en"]).length == 2
-- the term layer writes one token per RDF term, with the tag in lower case
private def tBytes : ByteArray := (serializeTermDict [litEN, exA, liten]).getD ByteArray.empty
private def tHeader : DictHeader := (readDictHeader tBytes).getD default
#guard tHeader.numTokens == 2
#guard parseDict tBytes == some ["\"x\"@en", "<http://example.org/a>"]
#guard dictEncodeTerm tBytes tHeader litEN == dictEncodeTerm tBytes tHeader liten
#guard (dictEncodeTerm tBytes tHeader litEN).isSome
#guard (List.range 2).all fun i => (dictDecodeTerm tBytes tHeader i).isSome
#guard dictDecodeTerm tBytes tHeader 0 == some liten
#guard termRoundTripsAll tBytes tHeader
-- a file from another writer with both spellings: two ids, one term, refused by the test
private def fBytes : ByteArray := (serializeDict ["\"x\"@EN", "\"x\"@en"]).getD ByteArray.empty
private def fHeader : DictHeader := (readDictHeader fBytes).getD default
#guard dictDecodeTerm fBytes fHeader 0 == dictDecodeTerm fBytes fHeader 1
#guard !termRoundTripsAll fBytes fHeader

end L4Factoidal.Cottas
