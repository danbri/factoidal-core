/-
L4Factoidal.Storage.TermWireV2Tests -- the build-time checks of `L4Factoidal.Storage.TermWireV2`.

These checks were the last section of `L4Factoidal.Storage.TermWireV2`. They were moved
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
import L4Factoidal.Storage.TermWireV2

namespace L4Factoidal.Storage.TermWireV2

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## Samples -/

private def ex : WfIri := ⟨"https://example.test/s", by decide⟩
private def exp : WfIri := ⟨"https://example.test/p", by decide⟩

private def plain : WireTerm := .inline (.literal (Literal.string "hello"))

private def dirLit : WfLiteral :=
  ⟨{ lexicalForm := "שלום", datatype := rdfDirLangString,
     langTag := some "he", direction := some .rtl }, by decide⟩

private def ltrLit : WfLiteral :=
  ⟨{ lexicalForm := "bonjour", datatype := rdfDirLangString,
     langTag := some "fr", direction := some .ltr }, by decide⟩

private def nested : WireTerm :=
  .inline (.tripleTerm (.iri ex) exp (.tripleTerm (.bnode "b0") exp (.literal dirLit)))

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def blobTerm : WireTerm := toWire specHash (.literal (Literal.string bigLexical))

private def roundTrip (w : WireTerm) : Option WireTerm :=
  (serializeTerm? w).bind (fun bs => (parseTerm bs).map Prod.fst)

#guard roundTrip (.inline (.iri ex)) == some (.inline (.iri ex))
#guard roundTrip (.inline (.bnode "b1")) == some (.inline (.bnode "b1"))
#guard roundTrip plain == some plain
#guard roundTrip (.inline (.literal dirLit)) == some (.inline (.literal dirLit))
#guard roundTrip (.inline (.literal ltrLit)) == some (.inline (.literal ltrLit))
#guard roundTrip nested == some nested
#guard roundTrip blobTerm == some blobTerm
#guard (match blobTerm with | .blob b => b.byteLength == 70000 | _ => false)
#guard (match blobTerm with | .blob b => b.sha256.size == 32 | _ => false)
#guard toWire specHash (.literal (Literal.string "hello")) == plain
#guard resolve specHash (lookupOf specHash (.literal (Literal.string bigLexical))) blobTerm
  == some (.literal (Literal.string bigLexical))
#guard (resolve specHash (fun _ => none) blobTerm).isNone
#guard (keyBytes (.inline (.iri ex))).isSome

end L4Factoidal.Storage.TermWireV2
