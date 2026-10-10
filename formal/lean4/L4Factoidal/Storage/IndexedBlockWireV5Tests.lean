/-
L4Factoidal.Storage.IndexedBlockWireV5Tests -- the build-time checks of `L4Factoidal.Storage.IndexedBlockWireV5`.

These checks were the last section of `L4Factoidal.Storage.IndexedBlockWireV5`. They were moved
here on 2026-10-10 because their fixtures (70,000-byte literals, blobs
hashed with SHA-256, encoded blocks) are top-level constants, and Lean
evaluates a top-level constant when its module is initialised, in every
executable that links the module. Five modules (`TermWireV2`,
`IndexedBlockWireV5`, `PagedTermDictionaryV2`, `BlockV5Plan`, `Codec.Inflate`)
held such fixtures. `l4factoidal version` executed 304,962,107 instructions
(43 ms of CPU time; the F* binary needs 6 ms) before the move and 25,590,678
(7 ms) after it, measured with callgrind and with the minimum of 15 runs. The
same initialisation runs when the wasm module is instantiated. This module is
imported by the umbrella `L4Factoidal`, so `lake build` still runs every
`#guard`, and by no executable.
-/
import L4Factoidal.Storage.IndexedBlockWireV5

namespace L4Factoidal.Storage.IndexedBlockWireV5

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlock (TermId)
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?)
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad PositionedIdQuad graphField graphOfField
  distinctGraphs encodeRow encodeGraphEntry canonicalOrder predicateLocal
  graphEntryBytes rowBytes prefixBytes magicVersionBytes crcBytes
  decodeGraphsGo decodeGraphSummary decodeRowsGo decodeRows orderedRows?)

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def g1 : GraphRef := .iri ⟨"http://example.org/g1", by simp [isIri]⟩

private def rtlLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

/-- Three RDF 1.2 objects the v1 codec refuses and IBK5 stores: a triple
    term, a directional language literal, and a 70,000-byte literal that goes
    out of line. -/
private def rdfQuads : List (Option GraphRef × Triple) :=
  [(none, { s := alice, p := pName,
            o := .tripleTerm bob pName (.literal (Literal.string "nested")) }),
   (some g1, { s := bob, p := pName, o := .literal rtlLit }),
   (some g1, { s := alice, p := pName, o := .literal (Literal.string bigLexical) })]

private def sampleBlock : QuadBlock := fromRdfQuads specHash rdfQuads
private def sampleBytes : ByteArray := (encode? sampleBlock).getD ByteArray.empty

/-- The lookup a packer holds: every literal of the source quads, by digest. -/
private def sampleLookup : ByteArray → Option ByteArray :=
  fun d => rdfQuads.findSome? (fun quad => lookupOf specHash quad.2.o d)

#guard (encode? sampleBlock).isSome
#guard sampleBlock.rows.size == 3
#guard (sampleBytes.extract 0 4).toList == [0x49, 0x42, 0x4B, 0x35]
#guard sampleBytes[4]! == 5

-- The block round-trips at the wire-term level.
#guard ((decode sampleBytes).map (·.dict)) == some sampleBlock.dict
#guard ((decode sampleBytes).map (·.rows)) == some sampleBlock.rows
#guard ((decode sampleBytes).map QuadBlock.denotes) == some sampleBlock.denotes

-- The 70,000-byte literal is the block's one out-of-line literal.
#guard (blobDigests sampleBlock).length == 1
#guard ((blobDigests sampleBlock).head?.map (·.size)) == some 32

-- Resolving the decoded block gives the original RDF quads back.
#guard ((decode sampleBytes).bind (resolveBlock specHash sampleLookup)) == some rdfQuads

-- Without the blob bytes the object cannot be resolved, and the block is not
-- silently returned with a fabricated literal.
#guard ((decode sampleBytes).bind (resolveBlock specHash (fun _ => none))).isNone

-- Zone-map keys exist for every row.
#guard (subjectKeys sampleBlock).map List.length == some 3
#guard (objectKeys sampleBlock).map List.length == some 3

-- The planner reads the graph set from the header plus the summary array
-- alone, with no row or dictionary byte.
#guard (decodeGraphSet? (sampleBytes.extract 0 prefixBytes)
    (sampleBytes.extract prefixBytes (prefixBytes + 2 * graphEntryBytes))).map Prod.snd
  == some (distinctGraphs sampleBlock.rows.toList)

/-- A blob may not be a subject. -/
private def blobTerm : WireTerm := toWire specHash (.literal (Literal.string bigLexical))

private def blobSubjectBlock : QuadBlock :=
  { dict := #[blobTerm, .inline (.iri pName), .inline (.literal (Literal.string "A"))]
    idByTerm := ∅
    rows := #[{ g := none, s := 0, p := 1, o := 2 }]
    byPredicate := ∅ }

#guard (encode? blobSubjectBlock).isNone
#guard (decode (byteArrayOfList (encodeList blobSubjectBlock))).isNone

/-- A row whose graph ID the dictionary never assigned. -/
private def oneQuadBlock : QuadBlock :=
  fromQuads [(none, { s := alice, p := pName,
                      o := .inline (.literal (Literal.string "A")) })]

#guard oneQuadBlock.dict.size == 3

private def badGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := some 3, s := 0, p := 1, o := 2 }] }

private def goodGraphBlock : QuadBlock :=
  { oneQuadBlock with rows := #[{ g := none, s := 0, p := 1, o := 2 }] }

#guard (encode? badGraphBlock).isNone
#guard (decode (byteArrayOfList (encodeList badGraphBlock))).isNone
#guard (encode? goodGraphBlock).isSome
#guard (decode (byteArrayOfList (encodeList goodGraphBlock))).isSome

end L4Factoidal.Storage.IndexedBlockWireV5
