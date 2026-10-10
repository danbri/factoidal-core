/-
Harness.ProtocolRun — the three protocol-shaped sparql11 test types:
`ProtocolTest` (sparql11/protocol, 34 entries),
`GraphStoreProtocolTest` (sparql11/graph-store-protocol, 4 + 9 entries;
the deprecated sparql11/http-rdf-update, 19 entries) and
`ServiceDescriptionTest` (sparql11/service-description, 3 entries).

THE STRUCTURED FORM (w3c/rdf-tests `c7817c2` and later for Protocol,
`02f98ff` and later for the Graph Store). `mf:action` is an
`ht:Connection`; its `ht:requests` list is run IN ORDER against one
store, and every request's `ht:resp` is checked: `mf:expectedStatus`
(an `hts:` class such as `StatusCode2xx` or a code such as `Created`;
several values mean any of them), `mf:expectedFormat` and
`mf:expectedBoolean` (Protocol), `mf:expectedLocation` and an RDF
`ht:body` the response must be isomorphic to (Graph Store). The runner
only reads the manifest and compares: the request is executed by the
library — `SPARQL/ProtocolService.lean` for Protocol tests, over a
Graph Store loaded from the entry's `ut:graphData`, and
`SPARQL/GraphStoreService.lean` for Graph Store tests, over an empty
store per entry. A test that `mf:requires` a feature the service does
not offer is `unsupported`.

THE MARKDOWN FORM, below, is kept for the manifests that still use it
(the deprecated http-rdf-update suite).

Each clause reproduces the corresponding clause of
`bin/w3c-runner/w3c_runner.ml` — `run_protocol_test` (~line 1714),
`run_gsp_test` (~line 2094) and `run_service_description_test`
(~line 2175) — so the two trees' numbers mean the same thing. No HTTP
server is started in either tree: the tests are request/response
decoding over the Markdown in each entry's `rdfs:comment`, with the
request handed to the pure decoder (`SPARQL/Protocol.lean`), the
store model (`SPARQL/GraphStore.lean`) or the description builder
(`SPARQL/ServiceDescription.lean`).

Rules kept from `Harness/Run.lean`: a missing or empty `rdfs:comment`
is a FAIL (a manifest-shape regression, as the F* runner scores it).
The F* runner parses the decoded query or update with the service IRI
as BASE, evaluates it over an EMPTY dataset (`apply_update` for an
update) and drops the result: every evaluation outcome — rows, a
raised exception, an unsupported feature — scores PASS when a 2xx is
expected ("the evaluator gap is orthogonal to protocol shape"), so the
verdict depends on the decoder and the parser only. This port does
the same evaluation (`SPARQL/Query.lean`, `SPARQL/Update.lean`) and
carries its summary into the FAIL text of an accepted-but-4xx-expected
entry, which is the only place it can show. Only the FIRST request
block of an entry is decoded, as in the F* runner: the
`update_dataset_*` entries are UPDATE-then-ASK sequences whose second
block is not replayed in either tree.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Manifest
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.SPARQL.GraphStore
import L4Factoidal.SPARQL.ProtocolService
import L4Factoidal.SPARQL.GraphStoreService
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.SPARQL.ServiceDescription
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.Update

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.GraphStore
open L4Factoidal.SPARQL.ServiceDescription

namespace Harness

/-! ## ProtocolTest — port of `run_protocol_test` -/

/-- The service IRI a request implies: `http://<Host>/<path>`, with
the W3C manifest's `www.example` and `/sparql/` as defaults. Protocol
§6.1 / Query §4.1.1.1: an implementation MAY use the service URI as
the BASE of a query with no BASE directive; the `update_base_uri`
test asserts exactly this. -/
def serviceIriOf (req : ProtoRequest) : String :=
  let h := header req.headers "host"
  let host := if h.isEmpty then "www.example" else h
  let path := if req.path.isEmpty then "/sparql/" else req.path
  "http://" ++ host ++ path

/-- `NOW()` for a protocol evaluation: fixed, so a run is reproducible. -/
def protocolNow : String := "2026-08-22T00:00:00Z"

/-- Evaluate a parsed query over the empty dataset; the summary is
informational (see the module header). -/
def evalQueryNote (serviceIri : String) (q : Query) : String :=
  let env : EvalEnv := { now := some protocolNow, base := q.base.orElse (fun _ => some serviceIri) }
  match q.form with
  | .select _    => s!"SELECT evaluated: {(evalSelect env Dataset.empty q).2.length} rows"
  | .ask         => s!"ASK evaluated: {evalAsk env Dataset.empty q}"
  | .construct _ => s!"CONSTRUCT evaluated: {(evalConstruct env Dataset.empty q).length} triples"
  | .describe _  => s!"DESCRIBE evaluated: {(evalDescribe env Dataset.empty q).length} triples"

/-- Apply a parsed update to the empty dataset; the summary is
informational. -/
def applyUpdateNote (serviceIri : String) (u : Update) : String :=
  let env : EvalEnv := { now := some protocolNow, base := u.base.orElse (fun _ => some serviceIri) }
  match applyUpdateIn env Dataset.empty u with
  | .ok ds   => s!"update applied: {ds.default.length} default triples, {ds.named.length} named graphs"
  | .error e => s!"update error: {repr e}"

/-- The protocol verdict for one decoded request against the expected
status class. Pure, so the rule table is `#guard`-able:

  * `bad` → PASS iff 4xx expected;
  * `query` → parse with the service IRI as BASE: a parse error is a
    rejection (PASS iff 4xx expected); a parse is an acceptance
    (PASS iff 2xx/3xx expected), evaluated over the empty dataset;
  * `update` → the same through `parseSparqlUpdate` / `applyUpdateIn`. -/
def protocolVerdict (req : ProtoRequest) (expected : StatusClass) : Outcome :=
  let ct := header req.headers "content-type"
  let decoded := decodeRequest req.method req.path req.qs ct req.body
  let serviceIri := serviceIriOf req
  let passIf2or3 (note : String) : Outcome :=
    match expected with
    | .s2or3 => .pass
    | .s4xx  => .fail s!"Expected 4xx but decode_request accepted ({req.method} {req.path}; {note})"
    | _      => .fail s!"Expected status class unknown; decode_request accepted ({note})"
  let passIf4xx (reason : String) : Outcome :=
    match expected with
    | .s4xx => .pass
    | e     => .fail s!"Expected {e.label} but request was rejected: {reason}"
  match decoded with
  | .bad reason => passIf4xx reason
  | .query qtext _ _ =>
    match parseSparql qtext (some serviceIri) with
    | .error e => passIf4xx s!"parse error: {e.msg} (offset {e.pos})"
    | .ok q    => passIf2or3 (evalQueryNote serviceIri q)
  | .update utext _ _ =>
    match parseSparqlUpdate utext (some serviceIri) with
    | .error e => passIf4xx s!"update parse error: {e.msg} (offset {e.pos})"
    | .ok u    => passIf2or3 (applyUpdateNote serviceIri u)

/-! ## The structured form: shared checks -/

/-- The status code an `hts:` term names (W3C HTTP Vocabulary in RDF,
the status codes of RFC 2616 §10 by reason phrase). -/
def statusCodeOfTerm : String → Option Nat
  | "Continue" => some 100 | "SwitchingProtocols" => some 101
  | "OK" => some 200 | "Created" => some 201 | "Accepted" => some 202
  | "NonAuthoritativeInformation" => some 203 | "NoContent" => some 204
  | "ResetContent" => some 205 | "PartialContent" => some 206
  | "MultipleChoices" => some 300 | "MovedPermanently" => some 301 | "Found" => some 302
  | "SeeOther" => some 303 | "NotModified" => some 304 | "UseProxy" => some 305
  | "TemporaryRedirect" => some 307
  | "BadRequest" => some 400 | "Unauthorized" => some 401 | "PaymentRequired" => some 402
  | "Forbidden" => some 403 | "NotFound" => some 404 | "MethodNotAllowed" => some 405
  | "NotAcceptable" => some 406 | "ProxyAuthenticationRequired" => some 407
  | "RequestTimeout" => some 408 | "Conflict" => some 409 | "Gone" => some 410
  | "LengthRequired" => some 411 | "PreconditionFailed" => some 412
  | "RequestEntityTooLarge" => some 413 | "RequestURITooLong" => some 414
  | "UnsupportedMediaType" => some 415 | "RequestedRangeNotSatisfiable" => some 416
  | "ExpectationFailed" => some 417
  | "InternalServerError" => some 500 | "NotImplemented" => some 501
  | "BadGateway" => some 502 | "ServiceUnavailable" => some 503
  | "GatewayTimeout" => some 504 | "HTTPVersionNotSupported" => some 505
  | _ => none

/-- Does an `hts:` term admit a status code? A `StatusCodeNxx` term
admits its class. `none` for a term this table does not know — a
manifest the runner cannot read, which must not score as a pass. -/
def statusTermAdmits (term : String) (code : Nat) : Option Bool :=
  match term with
  | "StatusCode1xx" => some (100 ≤ code && code < 200)
  | "StatusCode2xx" => some (200 ≤ code && code < 300)
  | "StatusCode3xx" => some (300 ≤ code && code < 400)
  | "StatusCode4xx" => some (400 ≤ code && code < 500)
  | "StatusCode5xx" => some (500 ≤ code && code < 600)
  | other => (statusCodeOfTerm other).map (· == code)

/-- `mf:expectedStatus`: the code must be admitted by one of the terms.
An absent `mf:expectedStatus` constrains nothing. -/
def checkStatus (terms : List String) (code : Nat) : Except String Unit :=
  if terms.isEmpty then .ok ()
  else
    match terms.mapM (fun t => (statusTermAdmits t code).map (fun b => (t, b))) with
    | none => .error s!"unknown hts: status term among {terms}"
    | some rs =>
      if rs.any (·.2) then .ok ()
      else .error s!"expected status {String.intercalate " or " terms}, got {code}"

/-- Split `ht:absolutePath` at its first `?`. -/
def splitAbsolutePath (p : String) : String × String :=
  match p.splitOn "?" with
  | [] => (p, "")
  | path :: rest => (path, String.intercalate "?" rest)

/-- Header lookup by lower-cased name, `""` when absent. -/
def headerValue (hdrs : List (String × String)) (name : String) : String :=
  (hdrs.find? (fun kv => kv.1 == name)).map (·.2) |>.getD ""

/-- Parse an RDF data file by extension (`.nt`, else Turtle). -/
def parseGraphFile (path text : String) : Except String Graph :=
  if path.endsWith ".nt" then (L4Factoidal.Syntax.parseNTriples text).mapError (·.msg)
  else (L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path))).mapError (·.msg)

/-! ## ProtocolTest, structured form -/

/-- Load the entry's `ut:graphData` files into a Graph Store, each as a
named graph under its `rdfs:label` IRI. -/
def loadProtocolStore (graphData : List (String × String)) : IO (Except Outcome Dataset) := do
  let mut named : List NamedGraph := []
  for (iri, path) in graphData do
    match ← readOpt path with
    | none => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseGraphFile path text with
      | .error e => return .error (.fail s!"graph data parse error in {basename path}: {e}")
      | .ok g =>
        if h : isIri iri then named := named ++ [{ name := .iri ⟨iri, h⟩, graph := g }]
        else return .error (.fail s!"ut:graphData label is not an IRI: {iri}")
  return .ok { default := [], named := named }

/-- Check one Protocol response against `ht:resp`. -/
def checkProtocolResponse (exp : ExpectedResponse) (r : ProtocolService.Response) :
    Except String Unit := do
  checkStatus exp.statuses r.status
  if let some fmt := exp.format then
    if r.payload.formatName != fmt then
      throw s!"expected result format {fmt}, got '{r.payload.formatName}'"
  if let some b := exp.boolean then
    match r.payload with
    | .boolean b' => if b' != b then throw s!"expected boolean {b}, got {b'}"
    | _ => throw s!"expected boolean {b}, got a '{r.payload.formatName}' result"

def runProtocolExchanges (tc : TestCase) : IO Outcome := do
  match ← loadProtocolStore tc.entryGraphData with
  | .error o => return o
  | .ok store0 =>
    let authority := tc.connectionAuthority.getD "www.example"
    let env : EvalEnv := { now := some protocolNow }
    let mut store := store0
    let mut i := 0
    for ex in tc.exchanges do
      i := i + 1
      let (path, qs) := splitAbsolutePath ex.absolutePath
      let serviceIri := "http://" ++ authority ++ path
      let (store', r) := ProtocolService.serve env store serviceIri ex.method path qs
                           (headerValue ex.headers "content-type") (ex.body.getD "")
      store := store'
      match checkProtocolResponse ex.resp r with
      | .ok () => pure ()
      | .error e =>
        let why := if r.message.isEmpty then "" else s!" ({r.message})"
        return .fail s!"request {i} of {tc.exchanges.length} ({ex.method} {ex.absolutePath}): {e}{why}"
    return .pass

def runProtocolTest (tc : TestCase) : IO Outcome := do
  if !tc.exchanges.isEmpty then runProtocolExchanges tc
  else
  match tc.comment with
  | none => return .fail "Protocol test has neither ht:requests nor an rdfs:comment request (manifest-shape regression)"
  | some comment =>
    match extractRequest comment with
    | none     => return .fail "Protocol test: could not extract request block from rdfs:comment"
    | some req => return protocolVerdict req (extractStatusClass comment)

/-! ## GraphStoreProtocolTest — port of `run_gsp_test`

The http-rdf-update suite is ONE sequence of requests against one
store: `GET of PUT - Initial state` asserts the state `PUT - Initial
state` (an earlier entry) established. The store therefore lives
across entries of a manifest (an `IO.Ref` created per manifest in
`Harness.Main`) and is reset when the suite's first entry, `PUT -
Initial state`, is seen.

Three pieces of manifest-shape glue the F* runner carries, reproduced
here and not in the library:

  1. placeholder canonicalisation — the manifest names the same graph
     as `$GRAPHSTORE$/person/1.ttl` (direct) and as
     `?graph=http://$HOST$/$GRAPHSTORE$/person/1.ttl` (indirect);
     both collapse to `/person/1.ttl`; a bare `$GRAPHSTORE$` POST
     (create new graph) is rebound to `$NEWPATH$`, the placeholder
     the follow-up GET uses;
  2. seeding from the entry name — an entry naming an "existing
     graph" / "graph already in store" whose graph is absent gets a
     seed graph first, counted in `HARNESS-DIAG gsp_seeded`;
  3. `PUT - mismatched payload` — GSP §5.3 says a payload whose graph
     IRI differs from the request URI SHOULD be a 400, but plain
     Turtle has no syntax for a graph IRI and the entry's body and
     URL are byte-identical to `PUT - Initial state`'s (201). The
     entry NAME is the only discriminator the manifest offers; the F*
     runner dispatches on it and so does this.

The payload is NOT parsed as Turtle (the F* runner's choice too): the
suite asserts status codes only, and one entry's payload is
`multipart/form-data`, so the body is stored as one sentinel triple
carrying the text. -/

/-- Collapse the manifest's URL shapes to one key (the F* runner's
`_gsp_canonical_key`): strip `http://<host>`, strip a leading
`$GRAPHSTORE$`, rebind the bare container to `$NEWPATH$`. -/
def gspCanonicalKey (raw : String) : String :=
  let s := if raw.startsWith "http://" then
             let rest := String.ofList (raw.toList.drop 7)
             match rest.toList.findIdx? (· == '/') with
             | some i => String.ofList (rest.toList.drop i)
             | none   => "/"
           else raw
  let s := if s.startsWith "/$GRAPHSTORE$" then String.ofList (s.toList.drop 13)
           else if s.startsWith "$GRAPHSTORE$" then String.ofList (s.toList.drop 12)
           else s
  if s.isEmpty || s == "/" then "$NEWPATH$" else s

def gspCanonicalTarget : Target → Target
  | .default => .default
  | .named k => .named (gspCanonicalKey k)

/-- Does the entry name say the graph pre-exists? `GET of DELETE` and
`non-existing` are excluded (the F* runner's `_gsp_should_seed`). -/
def gspShouldSeed (name : String) : Bool :=
  if Protocol.strContains name "GET of DELETE" then false
  else if Protocol.strContains name "non-existing" || Protocol.strContains name "nonexisting" ||
          Protocol.strContains name "non-existent" || Protocol.strContains name "nonexistent" then false
  else Protocol.strContains name "existing graph" || Protocol.strContains name "already in store"

def gspIsMismatchedPayload (name : String) : Bool := Protocol.strContains name "mismatched payload"

/-- The payload as one sentinel triple carrying the body text. -/
def gspSentinel (body : String) : Graph :=
  [{ s := .iri ⟨"urn:gsp:sentinel:body", rfl⟩, p := ⟨"urn:gsp:sentinel:body", rfl⟩,
     o := .literal (Literal.string body) }]

def gspSeedGraph : Graph :=
  [{ s := .iri ⟨"urn:gsp:seed:s", rfl⟩, p := ⟨"urn:gsp:seed:p", rfl⟩, o := .iri ⟨"urn:gsp:seed:o", rfl⟩ }]

/-- A server may answer 200 where the manifest says 201/204 on a
write (the F* runner's `_gsp_status_matches`). -/
def gspStatusMatches (expected actual : Nat) : Bool :=
  expected == actual ||
  (expected == 200 && (actual == 201 || actual == 204)) ||
  (actual == 200 && (expected == 201 || expected == 204))

/-- One Graph Store request against the store. Pure: returns the new
store, the outcome, and whether a seed was manufactured. -/
def gspStep (store : GraphStore) (name : String) (req : ProtoRequest) (expectedCode : Nat) :
    GraphStore × Outcome × Bool :=
  match Method.ofString req.method with
  | none | some .patch =>
    (store, .fail s!"GSP test: unrecognised HTTP method '{req.method}'", false)
  | some m =>
    -- The suite's first entry resets the store.
    let store := if name == "PUT - Initial state" then GraphStore.empty else store
    match decodeTarget req.path req.qs with
    | .error code =>
      (store, (if gspStatusMatches expectedCode code then .pass
               else .fail s!"GSP {req.method}: expected {expectedCode}, got {code} (malformed graph identification)"),
       false)
    | .ok rawTarget =>
      let target := gspCanonicalTarget rawTarget
      let (store, seeded) :=
        if gspShouldSeed name && !(head target store) then ((put target gspSeedGraph store).1, true)
        else (store, false)
      let (store, actual) :=
        if (m == .put || m == .post) && gspIsMismatchedPayload name then (store, 400)
        else handle m target (gspSentinel req.body) store
      let outcome :=
        if gspStatusMatches expectedCode actual then Outcome.pass
        else .fail s!"GSP {req.method}: expected {expectedCode}, got {actual} (target={target.show}, seeded={seeded})"
      (store, outcome, seeded)

/-! ## GraphStoreProtocolTest, structured form -/

/-- The path prefix of the Graph Store endpoint. The manifest:
"Each request has a ht:absolutePath value that starts with `/gsp`". -/
def gspEndpointPath : String := "/gsp"

/-- The `mf:requires` features `GraphStoreService` offers. -/
def gspSupportedFeatures : List String :=
  ["DirectGraphIdentification", "IndirectGraphIdentification", "POSTGraphCreation"]

/-- Replace every template variable bound so far (`$LOCATION$` → the
`Location` value an earlier response returned). -/
def substTemplateVars (vars : List (String × String)) (s : String) : String :=
  vars.foldl (fun acc kv => acc.replace kv.1 kv.2) s

/-- Check one Graph Store response against `ht:resp`; returns the
template variable binding `mf:expectedLocation` asks for. `base` is the
request IRI, the base for parsing both bodies. -/
def checkGspResponse (exp : ExpectedResponse) (base : String) (r : L4Factoidal.HTTP.Response) :
    Except String (Option (String × String)) := do
  checkStatus exp.statuses r.status
  if let some body := exp.body then
    let expMt := match headerValue exp.headers "content-type" with
                 | "" => "text/turtle"
                 | ct => contentTypeBase ct
    let actMt := contentTypeBase (headerValue r.headers "content-type")
    let parse (mt text : String) : Except String Graph :=
      match GraphStoreService.parseRdfAs mt base text with
      | some (.ok g)    => .ok g
      | some (.error e) => .error e
      | none            => .error s!"media type {mt} not readable"
    let expected ← (parse expMt body).mapError (fun e => s!"expected body does not parse: {e}")
    let actual ← (parse actMt r.body).mapError (fun e => s!"response body does not parse: {e}")
    if !(Graph.isomorphic? actual expected) then
      throw s!"response graph ({actual.length} triples) is not isomorphic to the expected graph ({expected.length} triples)"
  match exp.location with
  | none => return none
  | some var =>
    match headerValue r.headers "location" with
    | "" => throw "expected a Location header"
    | loc => return some (var, loc)

def runGspExchanges (tc : TestCase) : IO Outcome := do
  match tc.requires.find? (fun f => !gspSupportedFeatures.contains f) with
  | some f => return .unsupported s!"mf:requires {f}"
  | none =>
    let ep : GraphStoreService.Endpoint :=
      { authority := tc.connectionAuthority.getD "www.example", path := gspEndpointPath }
    let mut store : GraphStore := {}
    let mut vars : List (String × String) := []
    let mut i := 0
    for ex in tc.exchanges do
      i := i + 1
      let absPath := substTemplateVars vars ex.absolutePath
      let (path, qs) := splitAbsolutePath absPath
      let (store', r) := GraphStoreService.serve ep store ex.method path qs ex.headers
                           (substTemplateVars vars (ex.body.getD ""))
      store := store'
      match checkGspResponse ex.resp (ep.iriOf absPath) r with
      | .ok none => pure ()
      | .ok (some b) => vars := vars ++ [b]
      | .error e => return .fail s!"request {i} of {tc.exchanges.length} ({ex.method} {absPath}): {e}"
    return .pass

def runGspTest (storeRef : IO.Ref GraphStore) (tc : TestCase) : IO (Outcome × Bool) := do
  if !tc.exchanges.isEmpty then return (← runGspExchanges tc, false)
  match tc.comment with
  | none => return (.fail "GSP test has neither ht:requests nor an rdfs:comment request (manifest-shape regression)", false)
  | some comment =>
    match extractRequest comment, extractResponseStatus comment with
    | none, _ => return (.fail "GSP test: could not extract HTTP request from rdfs:comment", false)
    | _, none => return (.fail "GSP test: could not detect numeric response status in rdfs:comment", false)
    | some req, some code =>
      let store ← storeRef.get
      let (store', outcome, seeded) := gspStep store tc.name req code
      storeRef.set store'
      return (outcome, seeded)

/-! ## ServiceDescriptionTest — port of `run_service_description_test`

The suite ships no query, data or result files — the entries carry
only `mf:name`. The W3C SPARQL WG approved them as structural checks:
an implementation passes when it can produce a description of the
required shape. -/

def sdEndpoint : WfIri := ⟨"http://localhost:3030/sparql", rfl⟩

def serviceDescriptionVerdict (name : String) : Outcome :=
  let g := buildSd sdEndpoint
  if name == "GET on endpoint returns RDF" then
    if returnsRdf g then .pass else .fail "buildSd returned an empty graph"
  else if name == "Service description contains a matching sd:endpoint triple" then
    if hasEndpointTriple sdEndpoint g then .pass
    else .fail "buildSd output is missing the <endpoint> sd:endpoint <endpoint> triple"
  else if name == "Service description conforms to schema" then
    if conformsToSchema sdEndpoint g then .pass
    else .fail "buildSd output does not conform to sd: schema (missing rdf:type sd:Service, sd:endpoint, or sd:supportedLanguage)"
  else .fail s!"Unknown ServiceDescriptionTest name: {name}"

def runServiceDescriptionTest (tc : TestCase) : IO Outcome :=
  return serviceDescriptionVerdict tc.name

end Harness
