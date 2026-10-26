/-
L4Factoidal.RDF.QuadsBin — the quads of a dataset as one byte region, for a
host that builds RDF/JS term objects
(https://github.com/danbri/factoidal/issues/900).

The compact form of `TermJson` (a table of the distinct terms and each quad as
indices into it) written as bytes. The host copies the region out of the wasm
memory once and reads it with a `DataView` and a `TextDecoder`; it parses no
JSON and no RDF syntax.

Layout (`binSpec`), every number a u32 little-endian:

    "FQB1"  nTerms  nQuads
    nTerms terms, each in the term codec of DLOG version 2
      (`Storage.serializeDeltaTerm?`: tag 0 IRI, 1 blank node, 2 literal,
       3 triple term; a string is its u32 byte length and its UTF-8 bytes;
       a literal is its lexical form, its datatype IRI, a flag 0/1/2 and,
       for flag 1 and 2, the language tag, for flag 2 a direction byte
       1 ltr or 2 rtl)
    nQuads quads, each four u32: subject, predicate, object, graph, the
      first three an index into the terms, the graph 0 for the default
      graph and 1 + an index for a named graph.

Theorems (in `L4Factoidal/RDF/QuadsBinTheorems.lean`), so no run-time check
is needed (the JSON form `TermJson.compactCertified` checks at run time):
* `decodeBin_binSpec` (`QuadsBinTheorems`): the bytes of `binSpec` read back
  (`decodeBin`) as the table and indices they were written from;
* `quadsBin_binSpec`: the one-pass `ByteArray` writer `quadsBin` writes the
  bytes of `binSpec` for a table and index lists that read back as the quads
  (`TermJson.decodeCompactArr`);
* `decodeBin_quadsBin`: together, the region of `quadsBin qs` reads back as
  exactly the folded quads `qs.map Storage.TermFold.foldQuad` (language tags in
  lower case; one table entry per RDF term,
  https://github.com/danbri/factoidal/issues/977).
-/
import L4Factoidal.RDF.TermJson
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.RDF.QuadsBin

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.RDF.TermJson

/-! ## The specification: bytes as a list -/

def magic : List UInt8 := [0x46, 0x51, 0x42, 0x31]

/-- One quad of indices: `[s, p, o]` (default graph) or `[s, p, o, g]`. -/
def ixSpec : List Nat → Option (List UInt8)
  | [s, p, o] =>
      if s < two32 ∧ p < two32 ∧ o < two32 then
        some (writeU32LE (UInt32.ofNat s) ++ writeU32LE (UInt32.ofNat p) ++
          writeU32LE (UInt32.ofNat o) ++ writeU32LE 0)
      else none
  | [s, p, o, g] =>
      if s < two32 ∧ p < two32 ∧ o < two32 ∧ g + 1 < two32 then
        some (writeU32LE (UInt32.ofNat s) ++ writeU32LE (UInt32.ofNat p) ++
          writeU32LE (UInt32.ofNat o) ++ writeU32LE (UInt32.ofNat (g + 1)))
      else none
  | _ => none

/-- The bytes of the terms, one after another. -/
def serTerms : List Term → Option (List UInt8)
  | [] => some []
  | t :: ts =>
      match serializeDeltaTerm? t, serTerms ts with
      | some a, some r => some (a ++ r)
      | _, _ => none

/-- The bytes of the index lists, one after another. -/
def serIxs : List (List Nat) → Option (List UInt8)
  | [] => some []
  | ix :: r =>
      match ixSpec ix, serIxs r with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- **The layout.** -/
def binSpec (tbl : Array Term) (ixs : List (List Nat)) : Option (List UInt8) :=
  if tbl.size < two32 ∧ ixs.length < two32 then
    match serTerms tbl.toList, serIxs ixs with
    | some ts, some qs =>
        some (magic ++ writeU32LE (UInt32.ofNat tbl.size) ++ writeU32LE (UInt32.ofNat ixs.length) ++
          ts ++ qs)
    | _, _ => none
  else none

/-! ## The reader of the specification -/

def parseTermsGo : Nat → List UInt8 → Array Term → Option (Array Term × List UInt8)
  | 0, bs, acc => some (acc, bs)
  | n + 1, bs, acc =>
      match parseDeltaTerm bs with
      | some (t, r) => parseTermsGo n r (acc.push t)
      | none => none

def ixOf (s p o g : UInt32) : List Nat :=
  if g = 0 then [s.toNat, p.toNat, o.toNat] else [s.toNat, p.toNat, o.toNat, g.toNat - 1]

def parseIxsGo : Nat → List UInt8 → Array (List Nat) → Option (List (List Nat))
  | 0, [], acc => some acc.toList
  | 0, _ :: _, _ => none
  | n + 1, bs, acc =>
      match readU32LE bs 0, readU32LE bs 4, readU32LE bs 8, readU32LE bs 12 with
      | some s, some p, some o, some g => parseIxsGo n (bs.drop 16) (acc.push (ixOf s p o g))
      | _, _, _, _ => none

def decodeBin (bs : List UInt8) : Option (Array Term × List (List Nat)) :=
  if bs.take 4 = magic then
    match readU32LE bs 4, readU32LE bs 8 with
    | some nt, some nq =>
        match parseTermsGo nt.toNat (bs.drop 12) #[] with
        | some (tbl, rest) => (parseIxsGo nq.toNat rest #[]).map (tbl, ·)
        | none => none
    | _, _ => none
  else none

/-! ## The executable writer -/

@[inline] def putU32 (b : ByteArray) (n : UInt32) : ByteArray :=
  (((b.push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

def putLString (b : ByteArray) (s : String) : Option ByteArray :=
  let u := s.toUTF8
  if u.size < two32 then some (putU32 b (UInt32.ofNat u.size) ++ u) else none

def putLiteral (b : ByteArray) (l : WfLiteral) : Option ByteArray :=
  match putLString (b.push termTagLiteral) l.val.lexicalForm with
  | none => none
  | some b =>
    match putLString b l.val.datatype.val with
    | none => none
    | some b =>
      match l.val.langTag, l.val.direction with
      | none, none => some (b.push 0)
      | some tag, none => putLString (b.push 1) tag
      | some tag, some d => (putLString (b.push 2) tag).map (·.push (dirByte d))
      | none, some _ => none

def putTerm (b : ByteArray) : Term → Option ByteArray
  | .iri i => putLString (b.push termTagIri) i.val
  | .bnode x => putLString (b.push termTagBnode) x
  | .literal l => putLiteral b l
  | t@(.tripleTerm _ _ _) => (serializeDeltaTerm? t).map (fun l => b ++ ⟨l.toArray⟩)

/-! ## The executable writer: one pass over the quads

`BinState` holds the index of each IRI and blank-node label seen (a literal or
a triple term gets a new table entry each time, as in `TermJson.compactFast`),
the table, the term bytes written so far and the quad bytes written so far.
Each quad looks its three or four terms up, writes a new term's bytes when it
is first seen, and writes its four indices. The region is the header, the
term bytes and the quad bytes. -/

structure BinState where
  iris : Std.HashMap String Nat := {}
  bnodes : Std.HashMap String Nat := {}
  /-- The index of each literal and triple term seen (folded). Until
      2026-10-23 these got a new table entry at every occurrence
      (https://github.com/danbri/factoidal/issues/977). -/
  others : Std.HashMap Term Nat := {}
  tbl : Array Term := #[]
  terms : ByteArray := ByteArray.empty
  quads : ByteArray := ByteArray.empty

/-- A new table entry for `t`; refused when the table would reach 2^32 - 1
entries (a graph index is written as 1 + its index) or the term's bytes do not
fit their length fields. -/
@[inline] def BinState.add (st : BinState) (t : Term) : Option (Nat × BinState) :=
  if st.tbl.size + 1 < two32 then
    match putTerm st.terms t with
    | none => none
    | some b => some (st.tbl.size, { st with tbl := st.tbl.push t, terms := b })
  else none

/-- The index of a literal or a triple term: its entry when it was seen,
else a new entry. -/
@[inline] def BinState.indexOther (st : BinState) (t : Term) : Option (Nat × BinState) :=
  match st.others[t]? with
  | some k => some (k, st)
  | none =>
    match st.add t with
    | none => none
    | some (k, st') => some (k, { st' with others := st'.others.insert t k })

@[inline] def BinState.index (st : BinState) (t : Term) : Option (Nat × BinState) :=
  match t with
  | .iri i =>
      match st.iris[i.val]? with
      | some k => some (k, st)
      | none =>
        match st.add t with
        | none => none
        | some (k, st') => some (k, { st' with iris := st'.iris.insert i.val k })
  | .bnode b =>
      match st.bnodes[b]? with
      | some k => some (k, st)
      | none =>
        match st.add t with
        | none => none
        | some (k, st') => some (k, { st' with bnodes := st'.bnodes.insert b k })
  | _ => st.indexOther t

/-- One quad: its terms in the order of `TermJson.quadTerms`, then its four
u32 fields. The object is folded first (`Storage.TermFold.foldTerm`, language
tags in lower case; issue 977); a subject, a predicate and a graph name hold
no literal. -/
def BinState.quad (st : BinState) (q : Quad) : Option BinState :=
  match st.index (subjectToTerm q.2.s) with
  | none => none
  | some (si, st) =>
  match st.index (.iri q.2.p) with
  | none => none
  | some (pi, st) =>
  match st.index (Storage.TermFold.foldTerm q.2.o) with
  | none => none
  | some (oi, st) =>
  match q.1 with
  | none =>
      some { st with quads := putU32 (putU32 (putU32 (putU32 st.quads (UInt32.ofNat si))
        (UInt32.ofNat pi)) (UInt32.ofNat oi)) 0 }
  | some g =>
    match st.index (subjectToTerm g) with
    | none => none
    | some (gi, st) =>
      some { st with quads := putU32 (putU32 (putU32 (putU32 st.quads (UInt32.ofNat si))
        (UInt32.ofNat pi)) (UInt32.ofNat oi)) (UInt32.ofNat (gi + 1)) }

/-- The empty state for `n` quads, with the maps, the table and the byte
buffers allocated for `n` quads, so that none of them grows during the loop
(https://github.com/danbri/factoidal/issues/900). -/
def BinState.init (n : Nat) : BinState :=
  { iris := Std.HashMap.emptyWithCapacity n,
    bnodes := Std.HashMap.emptyWithCapacity (n / 4),
    others := Std.HashMap.emptyWithCapacity n,
    tbl := Array.emptyWithCapacity n,
    terms := ByteArray.emptyWithCapacity (32 * n),
    quads := ByteArray.emptyWithCapacity (16 * n) }

def binLoop (st : BinState) : List Quad → Option BinState
  | [] => some st
  | q :: qs =>
      match st.quad q with
      | none => none
      | some st => binLoop st qs

/-! ## A page of the quads of a dataset, with no whole quad list

`Dataset.quadList` builds every quad; an op that serves a page of it
(`offset`, `limit`) builds the page only (`quadPage_eq`, `quadCount_eq` in
`QuadsBinTheorems`; https://github.com/danbri/factoidal/issues/900). -/

/-- The graphs of a dataset in the order of `Dataset.quadList`: the default
graph, then each named graph. -/
def segs (ds : Dataset) : List (Option Subject × List Triple) :=
  (none, ds.default) :: ds.named.map (fun ng => (some ng.name, ng.graph))

/-- Push the first `n` triples of `ts`, in graph `g`, onto `acc`. -/
def pushTake (g : Option Subject) : List Triple → Nat → Array Quad → Array Quad
  | [], _, acc => acc
  | _ :: _, 0, acc => acc
  | t :: ts, n + 1, acc => pushTake g ts n (acc.push (g, t))

/-- The quads after the first `off`, at most `lim` of them, one loop step per
graph. -/
def pageAcc : List (Option Subject × List Triple) → Nat → Nat → Array Quad → Array Quad
  | [], _, _, acc => acc
  | s :: rest, off, lim, acc =>
    if lim = 0 then acc
    else
      let k := s.2.length
      if k ≤ off then pageAcc rest (off - k) lim acc
      else pageAcc rest 0 (lim - min lim (k - off)) (pushTake s.1 (s.2.drop off) lim acc)

/-- `((Dataset.quadList ds).drop off).take lim` (`quadPage_eq`). -/
def quadPage (ds : Dataset) (off lim : Nat) : List Quad :=
  (pageAcc (segs ds) off lim #[]).toList

def quadCountGo : List (Option Subject × List Triple) → Nat → Nat
  | [], a => a
  | s :: rest, a => quadCountGo rest (a + s.2.length)

/-- `(Dataset.quadList ds).length` (`quadCount_eq`). -/
def quadCount (ds : Dataset) : Nat := quadCountGo (segs ds) 0

/-- The region of the quads `qs` (`none` only when a count or a string length
does not fit its u32 field). -/
def quadsBin (qs : List Quad) : Option ByteArray :=
  let n := qs.length
  if n < two32 then
    match binLoop (BinState.init n) qs with
    | none => none
    | some st =>
      some ((putU32 (putU32 (putU32 (ByteArray.emptyWithCapacity (12 + st.terms.size + st.quads.size))
        0x31425146) (UInt32.ofNat st.tbl.size)) (UInt32.ofNat n)) ++ st.terms ++ st.quads)
  else none

end L4Factoidal.RDF.QuadsBin
