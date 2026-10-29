/-
L4Factoidal.YAMLLD.Api — YAML-LD 1.0 (W3C JSON-LD Working Group Editor's
Draft, https://w3c.github.io/yaml-ld/ , test suite and text at
json-ld/yaml-ld commit `fafcf7ae`, 2026-10-24) over the JSON-LD 1.1 API of
`L4Factoidal.JSONLD`.

YAML-LD defines no algorithm of its own. It fixes how a YAML 1.2 stream
becomes the JSON-LD internal representation (§4 "Core Requirements"), and
then the JSON-LD 1.1 API runs unchanged. So this module is three steps:

  1. `decodeUtf8`: §4.1.1, a stream that is not UTF-8 is an
     `invalid-encoding` error.
  2. `documents` and `internalRepresentation`: the YAML 1.2.2 loader of
     `L4Factoidal.YAML.Loader` (Core Schema, anchors and aliases, no cycles,
     string keys), the top-level check of §4.4.1, and the stream rule of
     §4.4.2 (`extractAllScripts`).
  3. The JSON-LD 1.1 algorithms on that value: `expandRoot` and
     `parseJsonLdRoot` take the value itself; compaction, flattening and
     framing take its JSON text (`Json.toString`), because their entry
     points in `L4Factoidal.JSONLD` read a text.

`L4Factoidal.YAMLLD.Theorems` states the relation to JSON-LD 1.1: a YAML-LD
document and a JSON-LD document with the same internal representation
expand to the same value and give the same dataset.

The informative Extended Profile (`extendedYAML` in the test manifest) is
the option `Options.extended`: a tag outside the Core Schema is dropped
and the node is resolved as if it had no tag. This is how the suite's
extended-profile fixtures read; the profile's text is a placeholder.
-/
import L4Factoidal.YAML.Loader
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Flatten
import L4Factoidal.JSONLD.Frame
import L4Factoidal.JSONLD.Html

namespace L4Factoidal.YAMLLD

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.YAML
open L4Factoidal.RDF

/-- The YAML-LD error codes (§5 `YamlLdErrorCode`) and the JSON-LD 1.1
codes that YAML-LD reuses. -/
inductive YamlLdError where
  | invalidEncoding
  | mappingKey (detail : String)
  | loadingDocumentFailed (detail : String)
  | jsonLd (e : JsonLdError)

/-- The code as the test manifest spells it (`expectErrorCode`). -/
def YamlLdError.code : YamlLdError → String
  | .invalidEncoding => "invalid encoding"
  | .mappingKey _ => "mapping-key-error"
  | .loadingDocumentFailed _ => "loading document failed"
  | .jsonLd e => e.code

def YamlLdError.detail : YamlLdError → String
  | .invalidEncoding => "the stream is not UTF-8"
  | .mappingKey d => d
  | .loadingDocumentFailed d => d
  | .jsonLd e => e.code

structure Options where
  /-- JSON-LD 1.1 API `extractAllScripts`, applied to the stream (§4.4.2). -/
  extractAllScripts : Bool := false
  /-- The informative Extended Profile (see the module header). -/
  extended : Bool := false

def ofYamlError (e : YamlError) : YamlLdError :=
  match e with
  | .mappingKey _ => .mappingKey e.message
  | _ => .loadingDocumentFailed e.message

/-- A JSON-LD API result as a YAML-LD result. -/
def liftJsonLd {α : Type} : Res α → Except YamlLdError α
  | .ok v => .ok v
  | .error e => .error (.jsonLd e)

/-! ## §4.1 Presentation: encoding -/

/-- §4.1.1: a YAML-LD stream MUST be UTF-8, else `invalid-encoding`. -/
def decodeUtf8 (b : ByteArray) : Except YamlLdError String :=
  match String.fromUTF8? b with
  | some s => .ok s
  | none => .error .invalidEncoding

/-! ## §4.3 Representation and §4.4 Native data structure -/

/-- §4.4.1: the top-level node of each document is a mapping, a sequence,
or a scalar that resolves to null. -/
def checkTop (j : Json) : Except YamlLdError Json :=
  match j with
  | .object _ | .array _ | .null => .ok j
  | _ => .error (.loadingDocumentFailed "the top-level node is a scalar that is not null (YAML-LD 1.0 §4.4.1)")

def checkAll : List Json → List Json → Except YamlLdError (List Json)
  | [], acc => .ok acc.reverse
  | j :: rest, acc =>
    match checkTop j with
    | .ok v => checkAll rest (v :: acc)
    | .error e => .error e

/-- The constructed value of each document of the stream. -/
def documents (text : String) (opts : Options := {}) : Except YamlLdError (List Json) :=
  match loadStream text opts.extended with
  | .error e => .error (ofYamlError e)
  | .ok docs => checkAll docs []

/-- §4.4.2 Stream processing: with `extractAllScripts`, the array of every
document's value (empty for no document); without it, the first
document's value (null for no document). -/
def internalRepresentation (docs : List Json) (extractAll : Bool) : Json :=
  if extractAll then .array docs
  else match docs with
    | [] => .null
    | d :: _ => d

/-- The JSON-LD internal representation of a YAML-LD stream. -/
def load (text : String) (opts : Options := {}) : Except YamlLdError Json :=
  match documents text opts with
  | .error e => .error e
  | .ok docs => .ok (internalRepresentation docs opts.extractAllScripts)

/-- The internal representation as a JSON text. -/
def toJsonText (text : String) (opts : Options := {}) : Except YamlLdError String :=
  match load text opts with
  | .error e => .error e
  | .ok j => .ok j.toString

/-! ## Document loading -/

/-- The path of an IRI without query and fragment. -/
def pathPart (url : String) : String :=
  let cs := url.toList
  String.ofList (cs.takeWhile (fun c => c != '#' && c != '?'))

/-- A document whose IRI ends in `.yamlld`, `.yaml` or `.yml` is YAML-LD
(§7 IANA considerations: file extensions; `.yml` is the usual YAML one). -/
def isYamlUrl (url : String) : Bool :=
  let p := pathPart url
  p.endsWith ".yamlld" || p.endsWith ".yaml" || p.endsWith ".yml"

/-- A documentLoader that gives the JSON text of a YAML-LD document's
internal representation (first document of the stream), so that a
`@context` reference to a YAML-LD document works. -/
def yamlAwareLoader (inner : Loader) (extended : Bool := false) : Loader := fun url =>
  match inner url with
  | none => none
  | some body =>
    if isYamlUrl url then
      match toJsonText body { extended := extended } with
      | .ok t => some t
      | .error _ => none
    else some body

/-! ## The JSON-LD 1.1 API on YAML-LD input -/

/-- JSON-LD 1.1 API §5.1 expansion of a YAML-LD stream. -/
def expandYamlLd (loader : Loader) (text : String) (base : Option String)
    (expandContext : Option String) (processingMode : Option String) (opts : Options := {})
    : Except YamlLdError Json :=
  match load text opts with
  | .error e => .error e
  | .ok root => liftJsonLd (expandRoot loader root base expandContext processingMode)

/-- JSON-LD 1.1 API §8.2 deserialization (toRdf) of a YAML-LD stream. -/
def toRdfYamlLd (loader : Loader) (text : String) (base : Option String)
    (rdfDirection : Option String) (expandContext : Option String)
    (processingMode : Option String) (opts : Options := {}) : Except YamlLdError Dataset :=
  match load text opts with
  | .error e => .error e
  | .ok root => liftJsonLd (parseJsonLdRoot loader root base rdfDirection expandContext processingMode)

/-- The JSON text of a document that is YAML-LD when `isYaml`, else JSON. -/
def jsonTextOf (text : String) (isYaml : Bool) (opts : Options := {}) : Except YamlLdError String :=
  if isYaml then toJsonText text opts else .ok text

/-- JSON-LD 1.1 API §6 compaction of a YAML-LD stream; the context
document is YAML-LD when `ctxIsYaml`. -/
def compactYamlLd (loader : Loader) (text ctxDoc : String) (ctxIsYaml : Bool)
    (base ctxUrl : Option String) (compactArrays compactToRelative : Bool)
    (processingMode : Option String) (opts : Options := {}) : Except YamlLdError Json :=
  match toJsonText text opts, jsonTextOf ctxDoc ctxIsYaml { opts with extractAllScripts := false } with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok t, .ok c =>
    liftJsonLd (compactDocument loader t c base ctxUrl compactArrays compactToRelative processingMode)

/-- JSON-LD 1.1 API §7 flattening of a YAML-LD stream. -/
def flattenYamlLd (loader : Loader) (text : String) (ctxDoc : Option (String × Bool))
    (base ctxUrl : Option String) (compactArrays : Bool) (processingMode : Option String)
    (opts : Options := {}) : Except YamlLdError Json :=
  match toJsonText text opts with
  | .error e => .error e
  | .ok t =>
    match ctxDoc with
    | none => liftJsonLd (flattenDocument loader t none base ctxUrl compactArrays processingMode)
    | some (c, isYaml) =>
      match jsonTextOf c isYaml { opts with extractAllScripts := false } with
      | .error e => .error e
      | .ok cj => liftJsonLd (flattenDocument loader t (some cj) base ctxUrl compactArrays processingMode)

/-- JSON-LD 1.1 Framing §4.1 framing of a YAML-LD stream with a frame. -/
def frameYamlLd (loader : Loader) (text frame : String) (frameIsYaml : Bool)
    (base : Option String) (processingMode : Option String) (opts : Options := {})
    : Except YamlLdError Json :=
  match toJsonText text opts, jsonTextOf frame frameIsYaml { opts with extractAllScripts := false } with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok t, .ok f => liftJsonLd (frameDocument loader t f base processingMode)

/-! ## §6 Embedding YAML-LD in HTML -/

/-- `(id?, isYaml, content)` of every `<script>` whose type is
`application/ld+yaml` or `application/ld+json`, in document order. The
content is kept as it is, white space included (§6). -/
def collectScripts (cs : List Char) : Nat → Nat → List (Option String × Bool × String)
    → List (Option String × Bool × String)
  | _, 0, acc => acc.reverse
  | pos, fuel + 1, acc =>
    match Html.ciFind "<script".toList cs pos (cs.length + 1) with
    | none => acc.reverse
    | some sp =>
      match Html.findChar '>' cs (sp + 7) with
      | none => acc.reverse
      | some gt =>
        let opentag := Html.sliceStr cs sp (Html.satSub gt sp + 1)
        let cstart := gt + 1
        match Html.ciFind "</script".toList cs cstart (cs.length + 1) with
        | none => acc.reverse
        | some ep =>
          let content := Html.sliceStr cs cstart (Html.satSub ep cstart)
          let otcs := opentag.toList
          let isYaml := (Html.ciFind "application/ld+yaml".toList otcs 0 (otcs.length + 1)).isSome
          let isJson := (Html.ciFind "application/ld+json".toList otcs 0 (otcs.length + 1)).isSome
          let acc' := if isYaml || isJson then (Html.extractId opentag, isYaml, content) :: acc else acc
          collectScripts cs (ep + 8) fuel acc'

/-- The values one script element contributes: each document of a YAML-LD
stream "as if it was included in a separate script tag" (§6); a JSON-LD
script's one value. -/
def scriptValues (opts : Options) (s : Option String × Bool × String) : Except YamlLdError (List Json) :=
  let (_, isYaml, content) := s
  if isYaml then documents content opts
  else match parseJson content with
    | .ok j => .ok [j]
    | .error _ => .error (.jsonLd .invalidScriptElement)

/-- A top-level array's members are spliced into the combined array, as
for JSON-LD scripts (`Html.spliceIfArray`). -/
def splice (vs : List Json) : List Json :=
  vs.foldr (fun v acc => match v with
    | .array xs => xs ++ acc
    | _ => v :: acc) []

def allValues (opts : Options) : List (Option String × Bool × String) → List Json
    → Except YamlLdError (List Json)
  | [], acc => .ok acc
  | s :: rest, acc =>
    match scriptValues opts s with
    | .error e => .error e
    | .ok vs => allValues opts rest (acc ++ vs)

/-- The JSON-LD 1.1 API's HTML document loading for YAML-LD and JSON-LD
scripts. `.ok none`: no script and no fragment, under `extractAllScripts`
false (the caller decides, as for JSON-LD). -/
def loadHtml (html : String) (fragment : Option String) (opts : Options)
    : Except YamlLdError (Option Json) :=
  let cs := html.toList
  let scripts := collectScripts cs 0 (cs.length + 1) []
  match fragment with
  | some fid =>
    match scripts.find? (fun s => s.1 == some fid) with
    | none => .error (.jsonLd .loadingDocumentFailed)
    | some s =>
      match scriptValues opts s with
      | .error e => .error e
      | .ok vs => .ok (some (internalRepresentation vs opts.extractAllScripts))
  | none =>
    if opts.extractAllScripts then
      match allValues opts scripts [] with
      | .error e => .error e
      | .ok vs => .ok (some (.array (splice vs)))
    else
      match scripts with
      | [] => .ok none
      | s :: _ =>
        match scriptValues opts s with
        | .error e => .error e
        | .ok vs => .ok (some (internalRepresentation vs false))

/-! ## Checks -/

private def expandsTo (y : String) (opts : Options) (expected : String) : Bool :=
  match expandYamlLd Loader.none y (some "http://example.org/") none none opts, parseJson expected with
  | .ok v, .ok w => expandedEqual v w
  | _, _ => false

#guard expandsTo "\"@context\":\n  \"@vocab\": http://ex/\nname: x\n" {}
  "[{\"http://ex/name\":[{\"@value\":\"x\"}]}]"
#guard expandsTo "\"@id\": http://ex/a\nhttp://ex/p: 1\n---\n\"@id\": http://ex/b\nhttp://ex/p: true\n"
  { extractAllScripts := true }
  "[{\"@id\":\"http://ex/a\",\"http://ex/p\":[{\"@value\":1}]},{\"@id\":\"http://ex/b\",\"http://ex/p\":[{\"@value\":true}]}]"
#guard ((load "text\n").toOption.isNone)
#guard (match load "1: x\n" with | .error e => e.code == "mapping-key-error" | .ok _ => false)
#guard (match decodeUtf8 (ByteArray.mk #[0xFF, 0xFE, 0x23, 0x00]) with
        | .error e => e.code == "invalid encoding" | .ok _ => false)

end L4Factoidal.YAMLLD
