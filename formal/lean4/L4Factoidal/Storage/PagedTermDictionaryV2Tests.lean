/-
L4Factoidal.Storage.PagedTermDictionaryV2Tests -- the build-time checks of `L4Factoidal.Storage.PagedTermDictionaryV2`.

These checks were the last section of `L4Factoidal.Storage.PagedTermDictionaryV2`. They were moved
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
import L4Factoidal.Storage.PagedTermDictionaryV2

namespace L4Factoidal.Storage.PagedTermDictionaryV2

open L4Factoidal.RDF
open L4Factoidal.Storage.TermWireV2

private def ex : WfIri := ⟨"https://example.test/t", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/u", by decide⟩
private def dirLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩
private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def sample : Array WireTerm :=
  #[.inline (.iri ex), .inline (.iri ex2), .inline (.literal dirLit),
    .inline (.tripleTerm (.iri ex) ex2 (.literal dirLit)),
    toWire specHash (.literal (Literal.string bigLexical))]
private def sampleBytes : ByteArray := (encode? sample).getD ByteArray.empty

private def twoPageSample : Array WireTerm :=
  ((List.range (defaultPageTerms + 1)).map
    (fun index => WireTerm.inline (.bnode s!"page-{index}"))).toArray
private def twoPageBytes : ByteArray := (encode? twoPageSample).getD ByteArray.empty

#guard decode? sampleBytes == some sample
#guard (decodePrefix (sampleBytes.extract 0 prefixBytes)).map (fun p => p.termCount) == some 5
#guard (sampleBytes.extract 0 4).toList == [0x50, 0x54, 0x44, 0x32]
#guard sampleBytes[4]! == 2
#guard findTermId? sample (.inline (.iri ex2)) == some 1
#guard decode? twoPageBytes == some twoPageSample
#guard (decodePrefix (twoPageBytes.extract 0 prefixBytes)).map (fun p => p.pageCount) == some 2

end L4Factoidal.Storage.PagedTermDictionaryV2
