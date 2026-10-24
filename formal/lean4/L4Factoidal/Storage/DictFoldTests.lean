/-
L4Factoidal.Storage.DictFoldTests — one id per RDF term in every store
dictionary (https://github.com/danbri/factoidal/issues/977; issue 975 phase
B4).

For each store: a graph or a quad list with `"x"@en` and `"x"@EN` (one RDF
term under `Term.eqb`, RDF 1.2 Concepts section 3.4) gets one dictionary
entry, the stored tag is the lower-case one (RDF 1.1 Concepts section 3.3),
and the encoded form reads back. Before the fold every "one id" guard below
failed: the dictionaries gave the two literals two ids.

This module is imported by the umbrella `L4Factoidal` and by no executable.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.PagedTermDictionaryV2
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.RDF.QuadsBin

namespace L4Factoidal.Storage.DictFoldTests

open L4Factoidal.RDF
open L4Factoidal.Storage

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def litEN : Term := .literal (Literal.langString "x" "EN")
private def liten : Term := .literal (Literal.langString "x" "en")
private def litEn : Term := .literal (Literal.langString "x" "En")
private def sA : Subject := .iri (exI "http://ex.org/a")
private def sB : Subject := .iri (exI "http://ex.org/b")
private def pP : WfIri := exI "http://ex.org/p"
private def gG : Subject := .iri (exI "http://ex.org/g")
/-- A triple term whose object has an upper-case tag. -/
private def ttEN : Term := .tripleTerm sB pP litEN
private def tten : Term := .tripleTerm sB pP liten

private def g2 : Graph := [⟨sA, pP, litEN⟩, ⟨sB, pP, liten⟩, ⟨sA, pP, ttEN⟩, ⟨sB, pP, tten⟩]
private def g2folded : Graph := [⟨sA, pP, liten⟩, ⟨sB, pP, liten⟩, ⟨sA, pP, tten⟩, ⟨sB, pP, tten⟩]

/-! ## IBK (in memory) and IBK3 (PTD1 dictionary) -/

private def ibk : IndexedBlock.Block := IndexedBlock.fromGraph g2

-- one id: a, b, p, "x"@en, the triple term
#guard ibk.dict.size == 5
#guard ibk.rows.toList.map (·.o) == [2, 2, 4, 4]
#guard ibk.dict.contains liten && !ibk.dict.contains litEN
#guard ibk.denotes == g2folded
-- IBK3 round trip (the v1 term codec of PTD1 has no triple terms)
private def g3 : Graph := [⟨sA, pP, litEN⟩, ⟨sB, pP, liten⟩, ⟨sB, pP, litEn⟩]
#guard (IndexedBlock.fromGraph g3).dict.size == 4
#guard ((IndexedBlockWireV3.encode? (IndexedBlock.fromGraph g3)).bind IndexedBlockWireV3.decode).map
  (·.denotes) == some [⟨sA, pP, liten⟩, ⟨sB, pP, liten⟩, ⟨sB, pP, liten⟩]

-- a file written before the fold (`encodeList`, the unchecked assembler,
-- writes the dictionary as given): it reads back with the tag folded; a file
-- with both spellings is refused
private def oldBlock (dict : Array Term) (rows : Array IndexedBlock.IdTriple) : IndexedBlock.Block :=
  { dict := dict, idByTerm := ∅, rows := rows, byPredicate := ∅ }
private def oldBytes (b : IndexedBlock.Block) : ByteArray :=
  IndexedBlockWireV3.byteArrayOfList (IndexedBlockWireV3.encodeList b)
#guard (IndexedBlockWireV3.encode? (oldBlock #[.iri (exI "http://ex.org/a"), .iri pP, litEN] #[⟨0, 1, 2⟩])).isNone
#guard (IndexedBlockWireV3.decode (oldBytes (oldBlock #[.iri (exI "http://ex.org/a"), .iri pP, litEN]
  #[⟨0, 1, 2⟩]))).map (·.denotes) == some [⟨sA, pP, liten⟩]
#guard (IndexedBlockWireV3.decode (oldBytes (oldBlock #[.iri (exI "http://ex.org/a"), .iri pP, litEN, liten]
  #[⟨0, 1, 2⟩, ⟨0, 1, 3⟩]))).isNone

/-! ## IBK4 (quads, PTD1 dictionary) -/

private def q4 : List IndexedBlockWireV4.QuadRow :=
  [(none, ⟨sA, pP, litEN⟩), (some gG, ⟨sB, pP, liten⟩), (some gG, ⟨sA, pP, litEn⟩)]

private def ibk4 : IndexedBlockWireV4.QuadBlock := IndexedBlockWireV4.fromQuads q4

#guard ibk4.dict.size == 5
#guard ibk4.rows.toList.map (·.o) == [2, 2, 2]
#guard ibk4.denotes == [(none, ⟨sA, pP, liten⟩), (some gG, ⟨sB, pP, liten⟩), (some gG, ⟨sA, pP, liten⟩)]
#guard ((IndexedBlockWireV4.encode? ibk4).bind IndexedBlockWireV4.decode).map (·.denotes) ==
  some ibk4.denotes

-- an IBK4 file written before the fold reads back folded
private def oldBlock4 : IndexedBlockWireV4.QuadBlock :=
  { dict := #[.iri (exI "http://ex.org/a"), .iri pP, litEN], idByTerm := ∅,
    rows := #[{ g := none, s := 0, p := 1, o := 2 }], byPredicate := ∅ }
#guard (IndexedBlockWireV4.decode (IndexedBlockWireV3.byteArrayOfList
  (IndexedBlockWireV4.encodeList oldBlock4))).map (·.denotes) == some [(none, ⟨sA, pP, liten⟩)]

/-! ## IBK5 (quads, PTD2 dictionary of wire terms) -/

private def q5 : List (Option GraphRef × Triple) :=
  [(none, ⟨sA, pP, litEN⟩), (none, ⟨sB, pP, liten⟩), (none, ⟨sA, pP, ttEN⟩)]

private def ibk5 : IndexedBlockWireV5.QuadBlock := IndexedBlockWireV5.fromRdfQuads TermWireV2.specHash q5

#guard ibk5.dict.size == 5
#guard ibk5.rows.toList.map (·.o) == [2, 2, 4]
#guard ibk5.dict.contains (.inline liten) && !ibk5.dict.contains (.inline litEN)
#guard ((IndexedBlockWireV5.encode? ibk5).bind IndexedBlockWireV5.decode).map (·.dict) == some ibk5.dict

/-! ## PTD1 and PTD2 on their own -/

-- a lookup folds the wanted term
#guard PagedTermDictionary.findTermId? #[.iri pP, liten] litEN == some 1
#guard PagedTermDictionaryV2.findTermId? #[.inline (.iri pP), .inline liten] (.inline litEN) == some 1
-- a dictionary written before the fold: the lookup compares folds, so the
-- stored `"x"@EN` is found for `"x"@en`, and the bytes read back unchanged
#guard PagedTermDictionary.findTermId? #[.iri pP, litEN] liten == some 1
#guard PagedTermDictionaryV2.findTermId? #[.inline (.iri pP), .inline litEN] (.inline liten) == some 1
#guard ((PagedTermDictionary.encode? #[.iri pP, litEN]).bind PagedTermDictionary.decode?) ==
  some #[.iri pP, litEN]
-- round trip of a folded dictionary
#guard ((PagedTermDictionary.encode? #[.iri pP, liten, .bnode "b"]).bind PagedTermDictionary.decode?) ==
  some #[.iri pP, liten, .bnode "b"]
#guard ((PagedTermDictionaryV2.encode? #[.inline (.iri pP), .inline liten]).bind
  PagedTermDictionaryV2.decode?) == some #[.inline (.iri pP), .inline liten]

/-! ## TLI1 -/

private def tliTerms : Array Term := #[.iri pP, liten, .bnode "b"]
private def tli : TermLocalIndexWire.Index :=
  { targetIBKSha256 := ByteArray.mk (Array.replicate 32 7), entries := TermLocalIndex.entriesOf tliTerms }

#guard TermLocalIndex.lookup? tli.entries litEN == some 1
#guard TermLocalIndex.lookup? tli.entries liten == some 1
#guard TermLocalIndex.lookup? tli.entries (.bnode "b") == some 2
#guard ((TermLocalIndexWire.encode? tli).bind TermLocalIndexWire.decode?) == some tli
-- the encoder refuses entries whose terms are not folded
#guard (TermLocalIndexWire.encode?
  { tli with entries := TermLocalIndex.entriesOf #[.iri pP, litEN] }).isNone

/-! ## TermJson (compact form) and QuadsBin -/

private def qj : List TermJson.Quad :=
  [(none, ⟨sA, pP, litEN⟩), (none, ⟨sB, pP, liten⟩), (some gG, ⟨sA, pP, liten⟩),
   (none, ⟨sA, pP, ttEN⟩), (none, ⟨sB, pP, tten⟩)]
private def qjFolded : List TermJson.Quad :=
  [(none, ⟨sA, pP, liten⟩), (none, ⟨sB, pP, liten⟩), (some gG, ⟨sA, pP, liten⟩),
   (none, ⟨sA, pP, tten⟩), (none, ⟨sB, pP, tten⟩)]

-- a, p, "x"@en, b, g, the triple term: one table entry each
#guard (TermJson.compactCertified qj).map (·.1.size) == some 6
#guard (TermJson.compactSpec qj).1.length == 6
#guard (TermJson.compactCertified qj).bind (fun c => TermJson.decodeCompactArr c.1 c.2) == some qjFolded
#guard TermJson.decodeCompact (TermJson.compactSpec qj).1 (TermJson.compactSpec qj).2 == some qjFolded

#guard ((QuadsBin.quadsBin qj).bind (fun b => QuadsBin.decodeBin b.data.toList)).map (·.1.size) == some 6
#guard ((QuadsBin.quadsBin qj).bind (fun b => QuadsBin.decodeBin b.data.toList)).bind
  (fun c => TermJson.decodeCompactArr c.1 c.2) == some qjFolded

end L4Factoidal.Storage.DictFoldTests
