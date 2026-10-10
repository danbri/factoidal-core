/-
Wasm.Ops.Formats — the format and transform operations of the npm entry
that the Lean dispatch table did not yet serve:

  jsonldToRdf(text, optsJson)           -> {"ok":true,"nquads":"…"}
  jsonldFromRdf(nquads, optsJson)       -> {"ok":true,"jsonld":"…"}
  rmlMap(mappingNquads, source, kind)   -> {"ok":true,"nquads":"…"}
  csvwToRdf(csv, metadataJson, optsJson)-> {"ok":true,"nquads":"…"}
  xmlWellformed(xml)                    -> {"ok":true,"wellformed":true|false}
  xpathEval(xml, expr)                  -> {"ok":true,"resultType":…,…}
  xsltTransform(stylesheet, source)     -> {"ok":true,"output":"…"}
  schematronValidate(schema, instance)  -> {"ok":true,"findings":[…]}
  jsonSchemaValidate(schema, instance)  -> {"ok":true,"valid":…,"result":…,"errors":[…]}
  mathmlEval(contentMathml, bindings)   -> {"ok":true,"value":{"kind":…}}
  xformsRecalc(instanceXml, bindsJson)  -> {"ok":true,"instance":"…","validity":[…]}
  rifEval(rifXml, nquads)               -> {"ok":true,"saturatedNquads":"…",…}

Envelopes follow `bin/npm-entry/entry_extras.ml` member for member, so
`npm/factoidal/lib/api.js` drives both engines through the same result
handling. Where the Lean library answers more than the F* module did,
or answers with less detail, the difference is stated beside the op.

Every operation is a pure function of its string arguments: no host
callback and no network. A remote JSON-LD `@context`, an `xsl:import`
and an external XML entity are therefore unresolved, as they are in the
F* entry (which installs no loader either).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NTriples
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.RML.Run
import L4Factoidal.RML.Targets
import L4Factoidal.CSVW.Pipeline
import L4Factoidal.XML.Parser
import L4Factoidal.XPath.Eval
import L4Factoidal.XPath.Mini
import L4Factoidal.XSLT.Transform
import L4Factoidal.Schematron.FromXml
import L4Factoidal.JSONSchema.Validate
import L4Factoidal.MathML.FromXml
import L4Factoidal.XForms.Bind
import L4Factoidal.RIF.Saturate

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-! ## Shared helpers -/

/-- Parse a dataset handle (N-Quads text). RDF 1.2 read mode, as in
`queryDataset`: the engine's own ops write RDF 1.2 canonical N-Quads. -/
private def readHandle (who nq : String) : Except String Dataset :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => .error s!"{who}: {fmtParseError e}"
  | .ok ds   => .ok ds

/-- `{"ok":true,"nquads":"…"}` for a dataset. -/
private def nquadsEnvelope (ds : Dataset) : String :=
  okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- The member `key` of a JSON options document, or `none` when the
document is empty, unreadable, or lacks it. -/
private def optString (opts : Option Json) (key : String) : Option String :=
  opts.bind (fun j => j.getString? key)

private def optBool (opts : Option Json) (key : String) : Bool :=
  ((opts.bind (fun j => j.getBool? key))).getD false

/-- Options documents are `""` or a JSON object (`jsonldToRdf` and
`csvwToRdf` pass `""` when the caller gave no options at all). -/
private def readOptions (s : String) : Option Json :=
  if s == "" then none else parseJson? s

/-! ## XML family -/

/-- `xmlWellformed(xml)`. XML 1.0 well-formedness is whether the parser
accepts the document (`XML/Parser.lean` header). The Lean parser reads
a DOCTYPE and its internal subset; the F* byte parser did not and
answered `false` for any document that had one. -/
def xmlWellformed (xml : String) : String :=
  okWith [("wellformed", .bool (L4Factoidal.XML.isWellFormed xml))]

private def parseDoc (who what xml : String) :
    Except String L4Factoidal.XML.Document :=
  match L4Factoidal.XML.parseXML xml with
  | .ok d    => .ok d
  | .error e =>
      .error s!"{who}: {what} is not well-formed XML: {e.message} (offset {e.position})"

/-- The XPath data model's kind name for one result item, in the words
the F* entry used (`element`, `attribute`, `text`, `comment`,
`processing-instruction`), plus `root` and `namespace`, which the F*
Stage-1 evaluator never returned. -/
private def itemKindName : L4Factoidal.XPath.Full.Kind → String
  | .root      => "root"
  | .element   => "element"
  | .text      => "text"
  | .comment   => "comment"
  | .pi        => "processing-instruction"
  | .attribute => "attribute"
  | .namespace => "namespace"

private def itemJson (it : L4Factoidal.XPath.Full.Item) : Json :=
  .object [("kind", .string (itemKindName it.kind)),
           ("name", .string it.qname),
           ("value", .string it.stringValue)]

/-- `xpathEval(xml, expr)`: an XPath 1.0 expression over a document,
evaluated with the document node as the context item and no variable
bindings. The four XPath value types map to `resultType` `nodeset`,
`string`, `number`, `boolean`; a number is carried as its XPath string
form (`1`, `NaN`, `-Infinity`), as in the F* entry. -/
def xpathEval (xml expr : String) : String :=
  match parseDoc "xpathEval" "the XML document" xml with
  | .error e => errJson e
  | .ok d =>
    let doc : L4Factoidal.XPath.Full.Doc := d.prolog ++ (d.root :: d.epilog)
    let ctx : L4Factoidal.XPath.Full.Ctx :=
      { doc := doc, item := .doc doc }
    match L4Factoidal.XPath.Full.evalText ctx expr with
    | none =>
        errJson s!"xpathEval: XPath parse error or unsupported construct: {expr}"
    | some v =>
      match v with
      | .bool b =>
          okWith [("resultType", .string "boolean"), ("value", .bool b)]
      | .num _ =>
          okWith [("resultType", .string "number"), ("value", .string v.toStr)]
      | .str s =>
          okWith [("resultType", .string "string"), ("value", .string s)]
      | .frag _ =>
          okWith [("resultType", .string "string"), ("value", .string v.toStr)]
      | .nodes items =>
          let ordered := L4Factoidal.XPath.Full.normalize items
          okWith [("resultType", .string "nodeset"),
                  ("count", .number (toString ordered.length)),
                  ("stringValue", .string v.toStr),
                  ("nodes", .array (ordered.map itemJson))]

/-- `xsltTransform(stylesheet, source)`: XSLT 1.0. The Lean engine
declines (`refused`) instead of guessing when a stylesheet uses an
element it does not implement; a refusal is the error envelope and
carries the engine's reason. -/
def xsltTransform (stylesheet source : String) : String :=
  match parseDoc "xsltTransform" "the stylesheet" stylesheet with
  | .error e => errJson e
  | .ok ss =>
    match parseDoc "xsltTransform" "the source" source with
    | .error e => errJson e
    | .ok src =>
      match L4Factoidal.XSLT.transform ss src with
      | .produced text => okWith [("output", .string text)]
      | .refused why   => errJson s!"xsltTransform: {why}"

private def findingJson (f : L4Factoidal.Schematron.Finding) : Json :=
  let common : List (String × Json) :=
    [("type", .string f.kind), ("context", .string f.context),
     ("test", .string f.test), ("message", .string f.message),
     ("path", .string f.path)]
  match f with
  | .indeterminate _ _ _ _ why => .object (common ++ [("reason", .string why)])
  | _ => .object common

/-- The `evalTest` parameter of `Schematron.validate`: XPath.Mini's
refusal becomes `undecided`, carrying the evaluator's own reason. -/
private def schematronEvalOf (root : L4Factoidal.XML.Node) (test path : String) :
    L4Factoidal.Schematron.TestResult :=
  match L4Factoidal.XPath.evalTestAt root test path with
  | Sum.inl (some true)  => .true'
  | Sum.inl (some false) => .false'
  | Sum.inl none         => .undecided "the evaluator returned no value"
  | Sum.inr why          => .undecided why

/-- `schematronValidate(schema, instance)`. A test the Mini XPath
evaluator cannot decide is an `indeterminate` finding with its reason,
never a pass. -/
def schematronValidate (schema inst : String) : String :=
  match L4Factoidal.Schematron.parseSchematron schema with
  | .error e => errJson s!"schematronValidate (schema): {e}"
  | .ok sch =>
    match parseDoc "schematronValidate" "the instance" inst with
    | .error e => errJson e
    | .ok d =>
      let root := d.root
      let nodes := L4Factoidal.XPath.documentPaths root
      let findings := L4Factoidal.Schematron.validate sch nodes
        (L4Factoidal.XPath.contextSelects root) (schematronEvalOf root)
      okWith [("findings", .array (findings.map findingJson))]

/-- `jsonSchemaValidate(schema, instance)`: a verdict, `pass`, `fail` or
`unsupported`. The validator gives no per-keyword error list, so
`errors` carries one reason string when the verdict is not `pass`. -/
def jsonSchemaValidate (schema inst : String) : String :=
  match parseJson schema with
  | .error _ => errJson "jsonSchemaValidate (schema): invalid JSON"
  | .ok sj =>
    match parseJson inst with
    | .error _ => errJson "jsonSchemaValidate (instance): invalid JSON"
    | .ok ij =>
      match L4Factoidal.JSONSchema.validate sj ij with
      | .pass =>
          okWith [("valid", .bool true), ("result", .string "pass"),
                  ("errors", .array [])]
      | .fail =>
          okWith [("valid", .bool false), ("result", .string "fail"),
                  ("errors", .array [.string "instance does not satisfy the schema"])]
      | .unsupported =>
          okWith [("valid", .bool false), ("result", .string "unsupported"),
                  ("errors", .array [.string
                    "schema uses a keyword this validator does not support"])]

/-! ## Content MathML -/

private def ratJson (r : Int × Int) : Json :=
  .array [.number (toString r.1), .number (toString r.2)]

/-- A value as the F* entry's `mvalue` object, plus two kinds the F*
engine had no value for: `vector` and `matrix` (entries are `[num,den]`
pairs). -/
private def mvalueJson : L4Factoidal.MathML.Value → Json
  | .num r =>
      .object [("kind", .string "rat"),
               ("num", .number (toString r.1)), ("den", .number (toString r.2))]
  | .bool b => .object [("kind", .string "bool"), ("value", .bool b)]
  | .vecv v =>
      .object [("kind", .string "vector"), ("value", .array (v.map ratJson))]
  | .matv m =>
      .object [("kind", .string "matrix"),
               ("value", .array (m.map (fun row => .array (row.map ratJson))))]

private def envEntry (k : String) (v : Json) :
    Except String (String × (Int × Int)) :=
  match v with
  | .string s | .number s =>
      match L4Factoidal.MathML.decimalToRat s with
      | some r => Except.ok (k, r)
      | none   => Except.error s!"mathmlEval: binding '{k}' is not a numeral: {s}"
  | _ => Except.error "mathmlEval: binding values must be strings or numbers"

/-- The ci environment: a JSON object of name to numeral. A value may
be a JSON string or number; a decimal, an integer or an `e`-notation
numeral reads as an exact rational (`MathML.decimalToRat`). -/
private def mathmlEnv (b : Json) : Except String (String → Option (Int × Int)) :=
  match b with
  | .object ms =>
      match ms.mapM (fun (kv : String × Json) => envEntry kv.1 kv.2) with
      | .error e => Except.error e
      | .ok pairs =>
          Except.ok (fun name => (pairs.find? (fun p => p.1 == name)).map (·.2))
  | _ => Except.error "mathmlEval: bindings must be a JSON object"

/-- `mathmlEval(contentMathml, bindingsJson)`. `undef` is an ordinary
answer (division by zero, a type error, an unbound variable, an element
outside the evaluated slice); the Lean evaluator reports no finer
reason than that, so the reason string is one fixed sentence. -/
def mathmlEval (xml bindings : String) : String :=
  match parseJson bindings with
  | .error _ => errJson "mathmlEval: invalid JSON in the bindings"
  | .ok bj =>
    match mathmlEnv bj with
    | .error e => errJson e
    | .ok env =>
      match L4Factoidal.MathML.parseMathML xml with
      | none =>
          errJson "mathmlEval: the markup is not well-formed Content MathML"
      | some e =>
        match L4Factoidal.MathML.eval env e with
        | some v => okWith [("value", mvalueJson v)]
        | none =>
            okWith [("value", .object
              [("kind", .string "undef"),
               ("reason", .string
                 ("the expression has no value (division by zero, a type "
                  ++ "error, an unbound variable, or an unsupported element)"))])]

/-! ## XForms -/

private def mipTypeOfName : String → L4Factoidal.XForms.MipType
  | ""        => .absent
  | "string"  => .string
  | "boolean" => .boolean
  | "integer" => .integer
  | "decimal" => .decimal
  | "float"   => .float
  | "double"  => .double
  | _         => .unsupported

private def optStringField (j : Json) (key : String) : Option String :=
  j.getString? key

private def bindOfJson (j : Json) : Except String L4Factoidal.XForms.Bind :=
  match j with
  | .object _ =>
    match j.getString? "target" with
    | none => .error "xformsRecalc: each bind needs a string 'target'"
    | some target =>
      .ok { id := (j.getString? "id").getD ""
            target := target
            calculate := optStringField j "calculate"
            constraint := optStringField j "constraint"
            relevant := optStringField j "relevant"
            required := optStringField j "required"
            readonly := optStringField j "readonly"
            mipType := mipTypeOfName ((j.getString? "type").getD "") }
  | _ => .error "xformsRecalc: each bind must be a JSON object"

private def validityJson (v : L4Factoidal.XForms.NodeValidity) : Json :=
  .object [("target", .string v.target), ("value", .string v.value),
           ("typeValid", .bool v.typeValid), ("constraint", .bool v.constraint),
           ("relevant", .bool v.relevant), ("required", .bool v.required),
           ("readonly", .bool v.readonly), ("valid", .bool v.valid)]

/-- `xformsRecalc(instanceXml, bindsJson)`: XForms 1.1 recalculate over
a flat instance. The F* entry answered `none` for a calculate cycle or
a MIP that does not evaluate, and so does this. -/
def xformsRecalc (instanceXml bindsJson : String) : String :=
  match parseDoc "xformsRecalc" "the instance" instanceXml with
  | .error e => errJson e
  | .ok d =>
    match parseJson bindsJson with
    | .error _ => errJson "xformsRecalc: invalid JSON in the binds"
    | .ok (.array items) =>
      match items.mapM bindOfJson with
      | .error e => errJson e
      | .ok binds =>
        match L4Factoidal.XForms.recalculate binds d.root with
        | none =>
            errJson ("xformsRecalc: recalculation failed "
                     ++ "(calculate cycle, or a MIP that failed to parse)")
        | some (inst, validity) =>
            okWith [("instance",
                      .string (L4Factoidal.XSLT.serialize [L4Factoidal.XSLT.copyNode inst])),
                    ("validity", .array (validity.map validityJson))]
    | .ok _ => errJson "xformsRecalc: binds must be a JSON array"

/-! ## JSON-LD -/

/-- `jsonldToRdf(text, optsJson)`. `optsJson` is `""` or an object with
the members `base`, `rdfDirection`, `expandContext`, `processingMode`
(all strings). No document loader is installed, so a remote `@context`
is the JSON-LD error `loading remote context failed`, as it is in the F*
entry. -/
def jsonldToRdf (text optsJson : String) : String :=
  let opts := readOptions optsJson
  match L4Factoidal.JSONLD.parseJsonLd L4Factoidal.JSONLD.Loader.none text
          (optString opts "base") (optString opts "rdfDirection")
          (optString opts "expandContext") (optString opts "processingMode") with
  | .ok ds => nquadsEnvelope ds
  | .error e =>
      errJson ("invalid or unsupported JSON-LD (" ++ e.code ++ ")")

/-- `jsonldFromRdf(nquads, optsJson)`: JSON-LD 1.1 API section 8,
Serialize RDF as JSON-LD, to an expanded-form document written in
RFC 8785 canonical form. `optsJson` members: `useNativeTypes`,
`useRdfType` (booleans), `rdfDirection` (string). -/
def jsonldFromRdf (nq optsJson : String) : String :=
  match readHandle "jsonldFromRdf" nq with
  | .error e => errJson e
  | .ok ds =>
    let opts := readOptions optsJson
    let o : L4Factoidal.JSONLD.FromRdf.Options :=
      { useNativeTypes := optBool opts "useNativeTypes"
        useRdfType := optBool opts "useRdfType"
        rdfDirection := optString opts "rdfDirection" }
    match L4Factoidal.JSONLD.FromRdf.fromRdf ds o with
    | none =>
        errJson ("jsonldFromRdf: from_rdf returned none (an rdf:JSON typed "
                 ++ "literal in the input is not valid JSON)")
    | some doc => okWith [("jsonld", .string (L4Factoidal.JSONLD.jcsDocument doc))]

/-! ## RML -/

private def rmlErrorsText (es : List L4Factoidal.RML.RmlError) : String :=
  String.intercalate "; " (es.map (fun e => e.message))

/-- `rmlMap(mappingNquads, source, kind)`: evaluate an RML mapping graph
over ONE logical source whose raw text is `source`. Every logical
source of the mapping reads that same text, whatever path the mapping
names (the F* entry has the same one-source cut). `kind` is `json` or
`csv` and is checked for parity with the F* signature; the iteration
format is decided by the mapping's `rml:referenceFormulation`, as RML
Core says, and not by `kind`. A mapping or data error rejects the whole
run and leaves no quads (`RML.Run`). -/
def rmlMap (mappingNq source kind : String) : String :=
  if kind != "json" && kind != "csv" then
    errJson s!"rmlMap: unknown sourceKind '{kind}' (expected 'json' or 'csv')"
  else
  match readHandle "rmlMap" mappingNq with
  | .error e => errJson e
  | .ok ds =>
    let fa : L4Factoidal.RML.FileAccess :=
      { read := fun _ _ => some source.toUTF8 }
    let r := L4Factoidal.RML.runMappingGraphFiles ds.default none fa
    if r.errors.isEmpty then
      nquadsEnvelope (L4Factoidal.RML.datasetOfQuads r.quads)
    else
      errJson s!"rmlMap: {rmlErrorsText r.errors}"

/-! ## CSVW -/

/-- `csvwToRdf(csv, metadataJson, optsJson)`: csv2rdf. `optsJson` members:
`mode` (`standard` or `minimal`), `base` (the metadata document's own
URL, default `file:///`), `url` (the table's URL when the metadata names
none, default `table.csv`). Every table of a table group reads the same
`csv` text. With `metadataJson == ""` the table is described by its own
header row. -/
def csvwToRdf (csv metadataJson optsJson : String) : String :=
  let opts := readOptions optsJson
  let mode := (optString opts "mode").getD "standard"
  let base := (optString opts "base").getD "file:///"
  let fallbackUrl := (optString opts "url").getD "table.csv"
  if mode != "standard" && mode != "minimal" then
    errJson s!"csvwToRdf: unknown mode '{mode}' (expected 'standard' or 'minimal')"
  else
  let described : Option (L4Factoidal.CSVW.TableGroup × L4Factoidal.CSVW.Ctx) :=
    if metadataJson == "" then
      some ({ tables := [{ url := fallbackUrl }] }, ({} : L4Factoidal.CSVW.Ctx))
    else L4Factoidal.CSVW.parseMetadataText metadataJson
  match described with
  | none =>
      errJson "csvwToRdf: metadataJson is not a decodable CSVW metadata document"
  | some (group, ctx) =>
    let mbase := L4Factoidal.CSVW.effectiveBase base ctx
    let pairs := group.tables.map (fun t =>
      (t, L4Factoidal.CSVW.read (L4Factoidal.CSVW.effectiveDialect group t).resolve csv))
    let triples := L4Factoidal.CSVW.convert mbase ctx group (mode == "minimal") pairs
    nquadsEnvelope { default := triples, named := [] }

/-! ## RIF Core -/

/-- `rifEval(rifXml, nquads)`: parse RIF-XML rules, forward-chain over the
default graph of the premise to the round bound of
`RIF.Saturate.defaultRounds` (100, the F* fuel), and answer the input and
the saturated graph as N-Triples with their counts. A rule document
that does not parse is the error envelope. -/
def rifEval (rifXml nq : String) : String :=
  match readHandle "rifEval" nq with
  | .error e => errJson e
  | .ok ds =>
    let premise := ds.default
    match L4Factoidal.RIF.Saturate.saturateWithProgram rifXml premise with
    | none =>
        errJson "RIF-XML parse error (RIF.Xml.parseRifProgram returned none)"
    | some saturated =>
      match Graph.toNTriples premise, Graph.toNTriples saturated with
      | .ok inLines, .ok outLines =>
          okWith [("inputNquads", .string inLines),
                  ("saturatedNquads", .string outLines),
                  ("inputCount", .number (toString premise.length)),
                  ("derivedCount",
                    .number (toString (saturated.length - premise.length))),
                  ("fuel", .number (toString L4Factoidal.RIF.Saturate.defaultRounds))]
      | .error e, _ | _, .error e => errJson s!"rifEval: serialisation: {e}"

end L4Wasm.Ops
