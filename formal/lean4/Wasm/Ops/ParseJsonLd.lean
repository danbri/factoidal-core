/-
Wasm.Ops.ParseJsonLd — the JSON-LD 1.1 reader of the full dispatch, and the
document-reading functions of `Wasm/Ops/Parse.lean` with that reader bound.

`Wasm/Ops/Parse.lean` keeps JSON-LD out of its own table and takes an
`ExtraReader` for it, so that the core dispatch (`Wasm/CoreDispatch.lean`)
links without the JSON-LD library
(https://github.com/danbri/factoidal/issues/713 stage 4). This module is the
JSON-LD side: `jsonLdReader` reads JSON-LD 1.1 ("Deserialize JSON-LD to RDF")
through `JSONLD.parseJsonLd` with no document loader — the F* entry installs
none either, so a remote `@context` is the JSON-LD error `loading remote
context failed`. The names below (`parseTextToDataset`, `parseToDatasetJson`,
`parseDocumentOutcome`, `parseToDatasetJsonWith`, `parseToDatasetJsonScoped`,
and `lenientDocumentOutcome` of `Wasm/Ops/Lenient.lean`) are the ones those
modules defined before 2026-10-10, with the same behaviour; the full dispatch (`Wasm/Dispatch.lean`) and the native command
line (`Wasm/Cli.lean`) call them.
-/
import Wasm.Ops.Parse
import Wasm.Ops.Lenient
import L4Factoidal.JSONLD.ToRdf

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- JSON-LD 1.1 for the tags of `jsonLdFormatTags`; `none` for every other
tag. -/
def jsonLdReader : ExtraReader := fun tag text base =>
  if jsonLdFormatTags.contains tag then
    some (match L4Factoidal.JSONLD.parseJsonLd L4Factoidal.JSONLD.Loader.none text base
                  none none none with
          | .ok ds   => .ok ds
          | .error e => .error s!"invalid or unsupported JSON-LD ({e.code})")
  else none

/-- `parseTextToDatasetBy` with JSON-LD. -/
def parseTextToDataset (text formatTag baseIRI : String) : Except String Dataset :=
  parseTextToDatasetBy jsonLdReader text formatTag baseIRI

/-- `parseToDatasetJson(text, formatTag, baseIRI)` with JSON-LD. -/
def parseToDatasetJson (text formatTag baseIRI : String) : String :=
  parseToDatasetJsonBy jsonLdReader text formatTag baseIRI

/-- `parseDocumentOutcomeBy` with JSON-LD. -/
def parseDocumentOutcome (text formatTag baseIRI : String) :
    Except ParseFailure ParseOutcome :=
  parseDocumentOutcomeBy jsonLdReader text formatTag baseIRI

/-- `parseToDatasetJsonWithBy` with JSON-LD. -/
def parseToDatasetJsonWith (scope : Option String) (text formatTag baseIRI : String) :
    String :=
  parseToDatasetJsonWithBy jsonLdReader scope text formatTag baseIRI

/-- `parseToDatasetJsonScopedBy` with JSON-LD. -/
def parseToDatasetJsonScoped (text formatTag baseIRI : String) : IO String :=
  parseToDatasetJsonScopedBy jsonLdReader text formatTag baseIRI

/-- `lenientDocumentOutcomeBy` with JSON-LD. -/
def lenientDocumentOutcome (text formatTag baseIRI : String) (opts : L4Factoidal.Syntax.LenientOptions) :
    Except ParseFailure (ParseOutcome × List L4Factoidal.Syntax.Diagnostic) :=
  lenientDocumentOutcomeBy jsonLdReader text formatTag baseIRI opts

/-! ## Build-time checks -/

private def jlDoc : String :=
  "{\"@id\":\"http://e/a\",\"http://e/p\":\"v\"}"

-- The JSON-LD reader reads the JSON-LD tags and no other.
#guard (parseToDatasetJson jlDoc "jsonld" "").startsWith "{\"ok\":true,\"count\":1"
#guard (parseToDatasetJson jlDoc "application/ld+json" "").startsWith "{\"ok\":true,\"count\":1"
#guard (parseToDatasetJson "{" "jsonld" "").startsWith "{\"ok\":false"
#guard (jsonLdReader "turtle" jlDoc none).isNone
-- Without the reader, JSON-LD is an unknown tag.
#guard (parseToDatasetJsonBy noExtraReader jlDoc "jsonld" "").startsWith
         "{\"ok\":false,\"error\":\"unknown format tag"

end L4Wasm.Ops
