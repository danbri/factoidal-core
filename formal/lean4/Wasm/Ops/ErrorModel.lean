/-
Wasm.Ops.ErrorModel — one error model for every op of the dispatch ABI
(https://github.com/danbri/factoidal/issues/882 item 4,
https://github.com/danbri/factoidal/issues/901 KR 3.1).

Every error envelope of an op carries, besides its human message `error`:

  * `code`: a stable machine code from `errorCodeTable` (for example
    `parse.syntax`, `query.syntax`, `handle.disposed`);
  * `spec`: the URL of the specification section that defines the failed
    condition, when one applies (absent otherwise);
  * `position`: `{"line":L,"column":C,"offset":O,"byteOffset":B}` when the
    input defines a position: `line` and `column` are 1-based, `column` and
    `offset` count Unicode scalar values, `byteOffset` counts UTF-8 bytes from
    the start of the input text.

The engine decides all three. A host copies them (iron rule 7, anti-pattern
36). Two places decide:

  1. An op site that knows its condition builds the envelope with `errCoded`
     (for example `handle.disposed` in `Wasm/Ops/Handles.lean`, the option
     checks of `apiCheck`).
  2. `attachCode`, which the four dispatch entries of `Wasm/Dispatch.lean` and
     `Wasm/CoreDispatch.lean` apply to every answer, gives a code to an error
     envelope that has none. It reads the engine's own message texts (each
     producer is bound to its code by a `#guard` in `Wasm/ErrorModelTests.lean`)
     and, when nothing more specific matches, the op family (`familyCode`).
     It also adds the position of a parse failure (from the `offset` member
     the parse ops write, or the ` (offset N)` suffix of `fmtParseError`)
     and the specification section of the code.

So every error envelope of every op of the table has a code from
`errorCodeTable`; `npm/factoidal/test/errors.test.mjs` checks it against the
`ops` reflection of a loaded engine.

The LWS and Solid ops (`lwsSolidOpNames`) are not changed here: their HTTP
answers have their own status model, and their hosts are another work stream.

`query.unknown-function` is not a code: an IRI call with no definition is an
expression error inside the evaluation (SPARQL 1.1 §17.3 and §17.6), which
leaves a variable unbound or a FILTER false. It never fails the operation.
-/
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Wasm.Ops

open L4Factoidal.JSON

/-- One declared error code: its name, the specification section that
defines the condition (when one does), and a one-line summary for the
package README's table. -/
structure ErrorCodeInfo where
  code : String
  spec : Option String
  summary : String

/-- Every code an error envelope can carry. The README table of the npm
package is generated from this list (op `engineTables`, member
`errorCodes`). -/
def errorCodeTable : List ErrorCodeInfo :=
  [ ⟨"parse.syntax", some "https://www.w3.org/TR/rdf12-turtle/#sec-grammar",
      "The input text does not match the grammar of its RDF syntax."⟩
  , ⟨"parse.rdf12-required", some "https://www.w3.org/TR/rdf12-concepts/#section-triple-terms",
      "The text uses an RDF 1.2 form (triple term, reified triple, base direction) and was read as RDF 1.1."⟩
  , ⟨"term.invalid-iri", some "https://www.w3.org/TR/rdf12-concepts/#section-IRIs",
      "A term that must be an IRI is not one."⟩
  , ⟨"term.invalid-langtag", some "https://www.w3.org/TR/rdf12-concepts/#section-Graph-Literal",
      "A language tag is not well-formed (BCP 47)."⟩
  , ⟨"term.invalid", some "https://www.w3.org/TR/sparql11-results-json/#select-encode-terms",
      "A term or quad given as JSON is not an RDF term or quad."⟩
  , ⟨"query.syntax", some "https://www.w3.org/TR/sparql11-query/#grammar",
      "The SPARQL query does not match the SPARQL grammar."⟩
  , ⟨"query.failed", some "https://www.w3.org/TR/sparql11-query/#sparqlDefinition",
      "The SPARQL query parsed but its evaluation was refused."⟩
  , ⟨"update.syntax", some "https://www.w3.org/TR/sparql11-update/#grammar",
      "The SPARQL update does not match the SPARQL Update grammar."⟩
  , ⟨"update.failed", some "https://www.w3.org/TR/sparql11-update/#updateLanguage",
      "The SPARQL update parsed but was refused."⟩
  , ⟨"format.unknown", none,
      "The format name is not one the engine reads or writes."⟩
  , ⟨"serialize.unsupported-rdf12", some "https://www.w3.org/TR/rdf12-concepts/#section-triple-terms",
      "The data holds an RDF 1.2 term and the requested RDF 1.1 output has no form for it."⟩
  , ⟨"serialize.failed", none,
      "The writer refused the data."⟩
  , ⟨"canon.unsupported-rdf12", some "https://www.w3.org/TR/rdf-canon/#canon-algorithm",
      "RDFC-1.0 defines no canonical labelling for RDF 1.2 triple terms or directional strings."⟩
  , ⟨"canon.failed", some "https://www.w3.org/TR/rdf-canon/#canon-algorithm",
      "Canonicalization was refused."⟩
  , ⟨"owl.unsupported-rdf12", some "https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification",
      "OWL 2 Direct Semantics has no rule for RDF 1.2 triple terms or directional strings."⟩
  , ⟨"reason.failed", none,
      "A closure or entailment check was refused."⟩
  , ⟨"regime.refused", some "https://www.w3.org/TR/sparql11-entailment/",
      "The entailment regime is not implemented."⟩
  , ⟨"validate.failed", none,
      "A validation (SHACL, ShEx, JSON Schema, Schematron) could not run on its inputs."⟩
  , ⟨"xml.failed", some "https://www.w3.org/TR/xml/#sec-well-formed",
      "An XML, XPath, XSLT, MathML or XForms input was refused."⟩
  , ⟨"crypto.failed", none,
      "A cryptographic or Verifiable Credentials operation refused its inputs."⟩
  , ⟨"store.failed", none,
      "A persisted-store, pack or HDT operation was refused."⟩
  , ⟨"registry.failed", some "https://www.w3.org/TR/sparql11-query/#extensionFunctions",
      "An extension-function or SERVICE registration was refused."⟩
  , ⟨"handle.unknown", none,
      "The handle was never issued by this engine."⟩
  , ⟨"handle.disposed", none,
      "The handle was issued and then closed."⟩
  , ⟨"option.unknown", none,
      "The options object has a key the function does not take."⟩
  , ⟨"option.invalid-value", none,
      "An option or mode argument has a value outside its table."⟩
  , ⟨"option.conflict", none,
      "Two options were given that cannot be combined."⟩
  , ⟨"capacity.exceeded", none,
      "The input is above a fixed size limit of the engine."⟩
  , ⟨"call.arity", none,
      "The op was called with the wrong number of arguments."⟩
  , ⟨"call.arguments", none,
      "The arguments document is not a JSON array of strings."⟩
  , ⟨"op.unknown", none,
      "The loaded engine has no op of this name."⟩
  , ⟨"op.failed", none,
      "Any other refusal of an op."⟩
  , ⟨"host.io", none,
      "The host could not read or write a file, a store or a log (no engine decision)."⟩ ]

/-- The declared code names. -/
def errorCodes : List String := errorCodeTable.map (·.code)

/-- The specification section of `code`, when one applies. -/
def specOfCode (code : String) : Option String :=
  ((errorCodeTable.find? (·.code == code)).bind (·.spec))

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-! ## Positions -/

private def utf8Width (c : Char) : Nat :=
  let n := c.toNat
  if n < 0x80 then 1 else if n < 0x800 then 2 else if n < 0x10000 then 3 else 4

/-- Line, column and UTF-8 byte offset of the character at scalar `offset`. -/
def positionAcc : List Char → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | [], _, line, col, bytes => (line, col, bytes)
  | _ :: _, 0, line, col, bytes => (line, col, bytes)
  | c :: rest, k + 1, line, col, bytes =>
      if c == '\n' then positionAcc rest k (line + 1) 1 (bytes + 1)
      else positionAcc rest k line (col + 1) (bytes + utf8Width c)

/-- `(line, column, byteOffset)` of scalar `offset` in `text`; an offset past
the end gives the position just after the last character. -/
def positionOf (text : String) (offset : Nat) : Nat × Nat × Nat :=
  positionAcc text.toList offset 1 1 0

/-- The `position` member for scalar `offset` in `text`. -/
def positionJson (text : String) (offset : Nat) : Json :=
  let (line, col, bytes) := positionOf text offset
  .object [ ("line", .number (toString line)), ("column", .number (toString col))
          , ("offset", .number (toString offset)), ("byteOffset", .number (toString bytes)) ]

/-- The offset at the end of a message in the form of `fmtParseError`
(`<msg> (offset N)`). -/
def messageOffset? (msg : String) : Option Nat :=
  match (msg.splitOn " (offset ").getLast? with
  | none => none
  | some tail =>
      if (msg.splitOn " (offset ").length < 2 then none
      else (String.ofList (tail.toList.takeWhile Char.isDigit)).toNat?

/-! ## Building a coded envelope -/

/-- `{"ok":false,"error":msg,"code":code,"spec"?:…, …extra}`. -/
def errCoded (code msg : String) (extra : List (String × Json) := []) : String :=
  let spec := match specOfCode code with
    | some s => [("spec", Json.string s)]
    | none => []
  (Json.object ([("ok", .bool false), ("error", .string msg), ("code", .string code)]
    ++ spec ++ extra)).toString

/-! ## Classification of an envelope without a code -/

/-- The syntax specification of a parse format tag (`format` member). -/
def parseSpecOfFormat (fmt : String) : Option String :=
  let f := fmt.toLower
  if f.startsWith "turtle" || f.startsWith "ttl" || f == "" then
    some "https://www.w3.org/TR/rdf12-turtle/#sec-grammar"
  else if f.startsWith "ntriples" || f.startsWith "nt" then
    some "https://www.w3.org/TR/rdf12-n-triples/#n-triples-grammar"
  else if f.startsWith "nquads" || f.startsWith "nq" then
    some "https://www.w3.org/TR/rdf12-n-quads/#sec-grammar"
  else if f.startsWith "trig" then some "https://www.w3.org/TR/rdf12-trig/#sec-grammar"
  else if f.startsWith "rdf" then some "https://www.w3.org/TR/rdf12-xml/#section-Infoset-Grammar"
  else if f.startsWith "json" || f == "application/ld+json" then
    some "https://www.w3.org/TR/json-ld11-api/#deserialize-json-ld-to-rdf-algorithm"
  else none

/-- The ops whose `n`-th argument is the input text an error position counts
into. -/
def opTextArg (op : String) : Option Nat :=
  if ["parseToDatasetJson", "datasetOpen", "parseDocument", "parseQuadsJson",
      "deltaLogEncode", "serializeNQuads", "serializeTurtle", "serializeTurtleWith",
      "canonicalizeToNQuads"].contains op then some 0
  else if ["queryDataset", "queryDataset12", "updateDataset", "datasetQuery",
           "datasetQuery12", "datasetUpdate", "queryRaw", "datasetQueryRaw",
           "storeQuery", "storeQueryPlan"].contains op then some 1
  else if op == "queryHdt" then some 0
  else none

/-- The default code of an op family, for a refusal no message rule names. -/
def familyCode (op : String) : String :=
  let p (xs : List String) := xs.any fun x => op.startsWith x
  let c (xs : List String) := xs.any fun x => has op x
  -- dataset-handle forms of the producers: the part after `dataset` names it
  if p ["dataset"] && c ["FromJsonLd", "FromCsvw", "FromRml", "FromJsonld"] then "parse.syntax"
  else if p ["dataset"] && c ["Rif", "Owl", "Tableau", "Closure", "Rdfs", "RhoDf"] then
    "reason.failed"
  else if p ["dataset"] && c ["Shacl", "Shex"] then "validate.failed"
  else if p ["parse", "detectFormat", "jsonldToRdf", "csvwToRdf", "rmlMap"] then "parse.syntax"
  else if op == "datasetOpen" then "parse.syntax"
  else if p ["deltaLog", "updateDataset", "datasetUpdate"] then "update.failed"
  else if p ["query", "datasetQuery", "storeQuery"] then "query.failed"
  else if p ["serialize", "datasetSerialize", "quadsToNQuads", "termsToNTriples",
             "jsonldFromRdf", "datasetToJsonLd"] then "serialize.failed"
  else if p ["canonical", "datasetCanonical", "datasetIsomorphic"] then "canon.failed"
  else if p ["owl", "rhoDf", "rdfsPlus", "datasetClosure", "tableau", "rifEval",
             "coreRdfs"] then "reason.failed"
  else if p ["shacl", "shex", "datasetShacl", "datasetShex", "jsonSchema", "schematron"] then
    "validate.failed"
  else if p ["xml", "xpath", "xslt", "mathml", "xforms"] then "xml.failed"
  else if p ["vc", "did", "aead", "hpke"] then "crypto.failed"
  else if p ["store", "activateVerify", "scanIBK", "queryIBK", "pack", "tdb2", "blob",
             "queryHdt"] then "store.failed"
  else if p ["ext", "registerService", "clearService"] then "registry.failed"
  else if p ["dataset", "resolveIri"] then "term.invalid"
  else "op.failed"

/-- The code of an error message of op `op`; `positioned` is true when the
envelope carries a parse position. Each rule matches a message the engine
itself writes; `Wasm/ErrorModelTests.lean` binds every producer to its code. -/
def classify (op msg : String) (positioned : Bool) : String :=
  if has msg "requires RDF 1.2 mode" || has msg "requires mode .rdf12" then
    "parse.rdf12-required"
  else if positioned then
    -- This parser message lists allowed alternatives. Mentioning IRIREF here
    -- does not mean an IRI was present or invalid.
    if msg.startsWith "expected object (" then "parse.syntax"
    else if has msg "IRIREF" || has msg "relative IRI" || has msg "invalid IRI" then "term.invalid-iri"
    else if has msg "language tag" || has msg "LANGTAG" then "term.invalid-langtag"
    else "parse.syntax"
  else if msg.startsWith "unknown op '" || has msg "is not in the core engine" then "op.unknown"
  else if msg.startsWith "argsJson" then "call.arguments"
  else if has msg " expects " && has msg " argument" then "call.arity"
  else if has msg "unknown dataset handle" || has msg "unknown store handle"
       || has msg "unknown pack handle" || has msg "unknown serve handle" then "handle.unknown"
  else if has msg "SPARQL update parse error" then "update.syntax"
  else if has msg "SPARQL parse error" then "query.syntax"
  else if has msg "unknown format" || has msg "unknown writer" then "format.unknown"
  else if has msg "RDFC-1.0" && has msg "triple term" then "canon.unsupported-rdf12"
  else if has msg "OWL 2 Direct" && has msg "triple term" then "owl.unsupported-rdf12"
  else if has msg "in RDF 1.1 has no form" then "serialize.unsupported-rdf12"
  else if has msg "invalid IRI" then "term.invalid-iri"
  else if has msg "is not implemented" && has msg "entail" then "regime.refused"
  else if has msg "-byte limit" || has msg "above the limit" || has msg "the cap is" then
    "capacity.exceeded"
  else if has msg "not a quad" || has msg "not a term" then "term.invalid"
  else familyCode op

/-- Ops whose envelopes this model leaves as they are (HTTP status model). -/
def uncodedOps : List String :=
  [ "lwsOpen", "lwsStep", "lwsClose", "lwsSnapshot", "lwsFetched", "lwsDelivered", "lwsFlush", "lwsLoad", "lwsPersist", "lwsRead", "solidOpen", "solidStep",
    "solidClose", "solidSnapshot", "solidFetched", "solidClientRequest", "solidClientResponse",
    "authzOpen", "authzStep", "authzFetched", "authzKeys", "authzRotate", "authzOwns", "authzClose",
    "webdavOpen", "webdavLoad", "webdavStep", "webdavResume", "webdavClose" ]

private def isErrorEnvelope (s : String) : Bool := s.startsWith "{\"ok\":false"

private def numField? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number n) => n.toNat?
  | _ => none

/-- The spec of `code` for this envelope: a parse code reads the format. -/
private def specFor (code : String) (op : String) (j : Json) : Option String :=
  if code == "parse.syntax" then
    match j.getString? "format" with
    | some f => (parseSpecOfFormat f).orElse fun _ => specOfCode code
    | none => specOfCode code
  else if (code == "query.syntax") && (op.endsWith "12") then
    some "https://www.w3.org/TR/sparql12-query/#grammar"
  else specOfCode code

/-- Give `envelope`, the answer of `op` to `args`, a code, a specification
section and a position when it is an error envelope without a code. Any other
answer is returned unchanged. -/
def attachCode (op : String) (args : List String) (envelope : String) : String :=
  if !isErrorEnvelope envelope || uncodedOps.contains op then envelope
  else
    match parseJson? envelope with
    | some (.object fields) =>
        if fields.any (·.1 == "code") then envelope
        else
          let j := Json.object fields
          let msg := (j.getString? "error").getD ""
          let parseOffset := numField? j "offset"
          let offset := parseOffset.orElse fun _ => messageOffset? msg
          let code := classify op msg
            (parseOffset.isSome || (offset.isSome && familyCode op == "parse.syntax"))
          let text := (opTextArg op).bind fun i => args[i]?
          let pos : List (String × Json) := match offset, text with
            | some o, some t => [("position", positionJson t o)]
            | _, _ => []
          let spec := match specFor code op j with
            | some s => [("spec", Json.string s)]
            | none => []
          (Json.object (fields ++ [("code", .string code)] ++ spec ++ pos)).toString
    | _ => envelope

/-- `attachCode` with the arguments read only when the answer is an error
envelope that needs a code. The dispatch entries pass `argsForCode`, which
decodes the whole argument envelope a second time; for a store manifest of
1.5 million hexadecimal digits that was paid on every call, error or not
(https://github.com/danbri/factoidal/issues/1039). -/
def attachCodeLazy (op : String) (args : Unit → List String) (envelope : String) : String :=
  if !isErrorEnvelope envelope || uncodedOps.contains op then envelope
  else attachCode op (args ()) envelope

/-- It is `attachCode`. -/
theorem attachCodeLazy_eq (op : String) (args : List String) (envelope : String) :
    attachCodeLazy op (fun _ => args) envelope = attachCode op args envelope := by
  unfold attachCodeLazy attachCode
  split <;> simp_all

/-- The code an envelope carries, if any. -/
def codeOf? (envelope : String) : Option String :=
  (parseJson? envelope).bind (·.getString? "code")

/-! ## Build-time checks (positive and negative) -/

#guard positionOf "ab\ncd" 4 == (2, 2, 4)
#guard positionOf "é\nx" 3 == (2, 2, 4)
#guard positionOf "abc" 10 == (1, 4, 3)
#guard messageOffset? "expected X (offset 14)" == some 14
#guard messageOffset? "no offset here" == none
#guard classify "parseToDatasetJson" "triple term <<( )>> requires RDF 1.2 mode" true
  == "parse.rdf12-required"
#guard classify "parseToDatasetJson" "expected prefixed name" true == "parse.syntax"
#guard classify "parseToDatasetJson" "expected object (IRIREF, BLANK_NODE_LABEL, or literal)" true
  == "parse.syntax"
#guard classify "parseToDatasetJson" "expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term)" true
  == "parse.syntax"
#guard classify "parseToDatasetJson" "invalid character in IRIREF" true == "term.invalid-iri"
#guard classify "parseToDatasetJson" "language tag must start with a letter" true
  == "term.invalid-langtag"
#guard classify "queryDataset" "SPARQL parse error: x (offset 0)" false == "query.syntax"
#guard classify "updateDataset" "SPARQL update parse error: x (offset 0)" false == "update.syntax"
#guard classify "nope" "unknown op 'nope'" false == "op.unknown"
#guard classify "queryDataset" "queryDataset expects 2 arguments, got 0" false == "call.arity"
#guard classify "xpathEval" "xpathEval: XPath parse error" false == "xml.failed"
#guard classify "frobnicate" "it failed" false == "op.failed"
#guard familyCode "datasetRifEval" == "reason.failed"
#guard familyCode "datasetFromJsonLd" == "parse.syntax"
#guard familyCode "datasetMatch" == "term.invalid"
#guard errorCodes.all fun c => errorCodes.count c == 1
#guard (errorCodes.map familyCode).all fun _ => true
#guard ["parseToDatasetJson", "queryDataset", "xyz"].all fun op => errorCodes.contains (familyCode op)
#guard codeOf? (attachCode "queryDataset" ["", "SELEC"] (Json.object [("ok", .bool false), ("error", .string "SPARQL parse error: e (offset 0)")]).toString) == some "query.syntax"
#guard codeOf? (attachCode "queryDataset" [] "{\"ok\":true}") == none
#guard codeOf? (attachCode "lwsStep" [] "{\"ok\":false,\"error\":\"x\"}") == none
#guard codeOf? (errCoded "handle.disposed" "closed") == some "handle.disposed"

end L4Wasm.Ops
