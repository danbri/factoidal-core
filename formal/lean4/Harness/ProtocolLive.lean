/-
Harness.ProtocolLive — the W3C SPARQL 1.1 Protocol, Graph Store Protocol
and Service Description tests replayed against a LIVE `factoidal serve`
over a socket (https://github.com/danbri/factoidal/issues/669 step 1).

`Harness/ProtocolRun.lean` scores the same manifests by calling the library
directly (`ProtocolService.serve`, `GraphStoreService.serve`, `buildSd`). This
runner checks the same expectations against the bytes a running server
writes on a TCP connection:

  * for each test, the entry's `ut:graphData` files are written as named
    graphs into one N-Quads file, packed into a quad generation
    (`l4block-shard-pack … ibk5`) and activated (`l4block-shard-activate`);
    a test with no data gets an empty generation;
  * `node npm/factoidal/bin/factoidal.mjs serve COLLECTION --port 0
    --gsp-path /gsp` serves it, and the origin it prints is the endpoint;
  * every `ht:Request` of the entry is sent IN ORDER with `curl` (HTTP/1.1,
    `Host` set to the entry's `ht:connectionAuthority`, the manifest's own
    header fields and body, nothing added); the raw response is parsed with
    `HTTP.Client.parseHttpResponse` and checked: `mf:expectedStatus`,
    `mf:expectedFormat` (by the response media type), `mf:expectedBoolean`
    (from the SPARQL Results JSON or XML body), `mf:expectedLocation` and an
    RDF `ht:body` the response must be isomorphic to (`checkGspResponse`);
  * a Service Description test fetches `GET /sparql` from the live server
    and applies the suite's three structural checks to the graph it answers.

The manifests say each `ht:absolutePath` prefix (`/sparql/`, `/gsp`) is to be
replaced by the endpoint's own; the server is started with `--gsp-path /gsp`
and its query endpoint accepts `/sparql/`, so no path is rewritten.

Expected failures are listed in `expectedFailures` with the issue that
tracks each one. An expected failure that passes is STALE and fails the run,
so the row and the issue cannot be forgotten (CLAUDE.md, "A stated shortfall
is a failing test plus an open issue").

Usage:
  l4protocol-live --cli npm/factoidal/bin/factoidal.mjs --bin .lake/build/bin
                  --work /tmp/dir MANIFEST...

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.ProtocolRun
import L4Factoidal.HTTP.Client
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.Turtle
import L4Factoidal.JSON.Parser

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.ServiceDescription

namespace Harness.ProtocolLive

structure LiveConfig where
  cli : String
  bin : String
  work : String

/-- Tests expected to fail against the live server, each with the issue that
tracks it. Empty when every test passes. -/
def expectedFailures : List (String × String) := []

/-! ## The collection and the server -/

/-- The entry's `ut:graphData` as one dataset of named graphs. -/
def datasetOf (graphData : List (String × String)) : IO (Except String Dataset) := do
  match ← loadProtocolStore graphData with
  | .error o => return .error (match o with
      | .fail r => r | .skip r => r | .unsupported r => r | .pass => "")
  | .ok ds => return .ok ds

private def run (cmd : String) (args : Array String) : IO (Except String String) := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode == 0 then return .ok out.stdout
  else return .error s!"{cmd} exited {out.exitCode}: {out.stderr.trimAscii}{out.stdout.trimAscii}"

/-- Pack `ds` as a quad generation under `dir/col` and activate it. -/
def buildCollection (cfg : LiveConfig) (dir : String) (ds : Dataset) : IO (Except String String) := do
  let col := dir ++ "/col"
  if ← System.FilePath.pathExists dir then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  match L4Factoidal.Syntax.Dataset.toNQuads ds with
  | .error e => return .error s!"N-Quads serialisation: {e}"
  | .ok text =>
    IO.FS.writeFile (dir ++ "/data.nq") text
    match ← run (cfg.bin ++ "/l4block-shard-pack") #[dir ++ "/data.nq", col ++ "/gen-1", "ibk5"] with
    | .error e => return .error e
    | .ok _ =>
      match ← run (cfg.bin ++ "/l4block-shard-activate") #[col, "gen-1"] with
      | .error e => return .error e
      | .ok _ => return .ok col

/-- Run `k` against a live server over `col`; the server is stopped after. -/
def withServer (cfg : LiveConfig) (col : String) (k : String → IO Outcome) : IO Outcome := do
  let child ← IO.Process.spawn
    { cmd := "node", args := #[cfg.cli, "serve", col, "--port", "0", "--quiet", "--gsp-path", "/gsp"]
      stdin := .null, stdout := .piped, stderr := .inherit }
  let line := (← child.stdout.getLine).trimAscii.toString
  let outcome ←
    if line.startsWith "http://" then
      try k line catch e => pure (.fail s!"live request failed: {e}")
    else pure (.fail s!"factoidal serve did not start (printed '{line}')")
  child.kill
  let _ ← child.wait
  return outcome

/-! ## One request over the socket -/

/-- The path and query of a manifest `ht:absolutePath`, which after a
`$LOCATION$` substitution may be an absolute IRI. -/
def pathPart (p : String) : String :=
  if p.startsWith "http://" then
    let rest := p.toList.drop 7
    match rest.findIdx? (· == '/') with
    | some i => String.ofList (rest.drop i)
    | none => "/"
  else p

/-- Send one request with curl and parse the raw response. `authority` is
the `Host` field; `none` keeps curl's own (the live origin). -/
def send (cfg : LiveConfig) (origin : String) (authority : Option String) (method absPath : String)
    (headers : List (String × String)) (body : Option String) : IO (Except String L4Factoidal.HTTP.Response) := do
  let bodyFile := cfg.work ++ "/request-body"
  let mut args : Array String := #["-s", "-g", "-i", "--http1.1", "--max-time", "60"]
  args := if method == "HEAD" then args.push "-I" else args ++ #["-X", method]
  if let some a := authority then args := args ++ #["-H", s!"Host: {a}"]
  -- Exactly the manifest's header fields: curl's own Accept, Content-Type
  -- and Expect are removed unless the manifest names them.
  for name in ["accept", "content-type", "expect"] do
    if !(headers.any (·.1 == name)) then args := args ++ #["-H", s!"{name}:"]
  for (n, v) in headers do args := args ++ #["-H", s!"{n}: {v}"]
  if let some b := body then
    IO.FS.writeFile bodyFile b
    args := args ++ #["--data-binary", "@" ++ bodyFile]
  args := args.push (origin ++ pathPart absPath)
  let out ← IO.Process.output { cmd := "curl", args }
  if out.exitCode != 0 then return .error s!"curl exited {out.exitCode}: {out.stderr.trimAscii}"
  match L4Factoidal.HTTP.Client.parseHttpResponse out.stdout 1048576 67108864 with
  | .error e => return .error s!"response does not parse: {repr e}"
  | .ok r => return .ok { status := r.status, headers := r.headers, body := r.body }

/-! ## Checks -/

/-- The kind of result a response media type carries, as the protocol
manifest names kinds (`mf:expectedFormat`). -/
def resultKindOf (r : L4Factoidal.HTTP.Response) : String :=
  let ct := contentTypeBase (headerValue r.headers "content-type")
  if ct == "application/sparql-results+json" || ct == "application/json" then
    match L4Factoidal.JSON.parseJson r.body with
    | .ok j => if (j.field? "boolean").isSome then "boolean" else "tabular"
    | .error _ => ""
  else if ct == "application/sparql-results+xml" || ct == "application/xml" || ct == "text/xml" then
    if Protocol.strContains r.body "<boolean>" then "boolean" else "tabular"
  else if ct == "text/csv" || ct == "text/tab-separated-values" then "tabular"
  else if ct == "text/turtle" || ct == "application/n-triples" || ct == "application/rdf+xml" then "RDF"
  else ""

/-- The ASK answer a results document carries. -/
def booleanOf (r : L4Factoidal.HTTP.Response) : Option Bool :=
  let ct := contentTypeBase (headerValue r.headers "content-type")
  if ct == "application/sparql-results+json" || ct == "application/json" then
    match L4Factoidal.JSON.parseJson r.body with
    | .ok j => match j.field? "boolean" with
      | some (.bool b) => some b
      | _ => none
    | .error _ => none
  else if Protocol.strContains r.body "<boolean>true</boolean>" then some true
  else if Protocol.strContains r.body "<boolean>false</boolean>" then some false
  else none

def checkProtocolLive (exp : ExpectedResponse) (r : L4Factoidal.HTTP.Response) : Except String Unit := do
  checkStatus exp.statuses r.status
  if let some fmt := exp.format then
    let kind := resultKindOf r
    if kind != fmt then throw s!"expected result format {fmt}, got '{kind}' ({headerValue r.headers "content-type"})"
  if let some b := exp.boolean then
    match booleanOf r with
    | some b' => if b' != b then throw s!"expected boolean {b}, got {b'}"
    | none => throw s!"expected boolean {b}, the body carries none"

/-! ## The three test types -/

def runProtocolLive (cfg : LiveConfig) (ix : Nat) (tc : TestCase) : IO Outcome := do
  match ← datasetOf tc.entryGraphData with
  | .error e => return .fail s!"graph data: {e}"
  | .ok ds =>
  match ← buildCollection cfg s!"{cfg.work}/t{ix}" ds with
  | .error e => return .fail s!"pack: {e}"
  | .ok col =>
    withServer cfg col fun origin => do
      let authority := tc.connectionAuthority.getD "www.example"
      let mut i := 0
      for ex in tc.exchanges do
        i := i + 1
        match ← send cfg origin (some authority) ex.method ex.absolutePath ex.headers ex.body with
        | .error e => return .fail s!"request {i}: {e}"
        | .ok r =>
          match checkProtocolLive ex.resp r with
          | .ok () => pure ()
          | .error e =>
            return .fail s!"request {i} of {tc.exchanges.length} ({ex.method} {ex.absolutePath}): {e} [{r.status}: {r.body.take 200}]"
      return .pass

def runGspLive (cfg : LiveConfig) (ix : Nat) (tc : TestCase) : IO Outcome := do
  match tc.requires.find? (fun f => !gspSupportedFeatures.contains f) with
  | some f => return .unsupported s!"mf:requires {f}"
  | none =>
  match ← buildCollection cfg s!"{cfg.work}/t{ix}" Dataset.empty with
  | .error e => return .fail s!"pack: {e}"
  | .ok col =>
    withServer cfg col fun origin => do
      let authority := tc.connectionAuthority.getD "www.example"
      let ep : GraphStoreService.Endpoint := { authority, path := gspEndpointPath }
      let mut vars : List (String × String) := []
      let mut i := 0
      for ex in tc.exchanges do
        i := i + 1
        let absPath := substTemplateVars vars ex.absolutePath
        let body := ex.body.map (substTemplateVars vars)
        match ← send cfg origin (some authority) ex.method absPath ex.headers body with
        | .error e => return .fail s!"request {i}: {e}"
        | .ok r =>
          match checkGspResponse ex.resp (ep.iriOf (pathPart absPath)) r with
          | .ok none => pure ()
          | .ok (some b) => vars := vars ++ [b]
          | .error e => return .fail s!"request {i} of {tc.exchanges.length} ({ex.method} {absPath}): {e} [{r.status}]"
      return .pass

def runServiceDescriptionLive (cfg : LiveConfig) (ix : Nat) (tc : TestCase) : IO Outcome := do
  match ← buildCollection cfg s!"{cfg.work}/t{ix}" Dataset.empty with
  | .error e => return .fail s!"pack: {e}"
  | .ok col =>
    withServer cfg col fun origin => do
      match ← send cfg origin none "GET" "/sparql" [("accept", "application/n-triples")] none with
      | .error e => return .fail e
      | .ok r =>
        if r.status != 200 then return .fail s!"GET /sparql answered {r.status}"
        match L4Factoidal.Syntax.parseNTriples r.body with
        | .error e => return .fail s!"the description does not parse as N-Triples: {e.msg}"
        | .ok g =>
          let endpoint := origin ++ "/sparql"
          if h : isIri endpoint then
            let e : WfIri := ⟨endpoint, h⟩
            if tc.name == "GET on endpoint returns RDF" then
              return (if returnsRdf g then .pass else .fail "the description is an empty graph")
            else if tc.name == "Service description contains a matching sd:endpoint triple" then
              return (if hasEndpointTriple e g then .pass else .fail s!"no <{endpoint}> sd:endpoint <{endpoint}> triple")
            else if tc.name == "Service description conforms to schema" then
              return (if conformsToSchema e g then .pass else .fail "the description does not conform to the sd: schema")
            else return .fail s!"Unknown ServiceDescriptionTest name: {tc.name}"
          else return .fail s!"{endpoint} is not an IRI"

/-! ## The run -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  unsupported : Nat := 0
  xfail : Nat := 0
  stale : Nat := 0

def runManifestLive (cfg : LiveConfig) (path : String) (t : Tally) (start : Nat) : IO (Tally × Nat) := do
  match ← loadManifest path with
  | none => IO.println s!"MISSING {path}"; return ({ t with fail := t.fail + 1 }, start)
  | some (.error e) => IO.println s!"MANIFEST ERROR {path}: {e}"; return ({ t with fail := t.fail + 1 }, start)
  | some (.ok (tests, _)) =>
    let mut t := t
    let mut ix := start
    for tc in tests do
      ix := ix + 1
      let outcome ←
        if tc.testType == "ProtocolTest" then runProtocolLive cfg ix tc
        else if tc.testType == "GraphStoreProtocolTest" then runGspLive cfg ix tc
        else if tc.testType == "ServiceDescriptionTest" then runServiceDescriptionLive cfg ix tc
        else pure (.unsupported s!"test type {tc.testType}")
      let xfail := expectedFailures.find? (·.1 == tc.name)
      match outcome, xfail with
      | .pass, none => t := { t with pass := t.pass + 1 }; IO.println s!"PASS {tc.name}"
      | .pass, some (_, issue) =>
        t := { t with stale := t.stale + 1 }
        IO.println s!"STALE {tc.name}: passes, but is listed as an expected failure ({issue})"
      | .fail r, some (_, issue) =>
        t := { t with xfail := t.xfail + 1 }; IO.println s!"XFAIL {tc.name} ({issue}): {r}"
      | .fail r, none => t := { t with fail := t.fail + 1 }; IO.println s!"FAIL {tc.name}: {r}"
      | .unsupported r, _ => t := { t with unsupported := t.unsupported + 1 }; IO.println s!"UNSUPPORTED {tc.name}: {r}"
      | .skip r, _ => t := { t with fail := t.fail + 1 }; IO.println s!"FAIL {tc.name} (skipped: {r})"
    return (t, ix)

def main (args : List String) : IO UInt32 := do
  let rec scan : List String → LiveConfig → List String → LiveConfig × List String
    | "--cli" :: v :: rest, c, ms => scan rest { c with cli := v } ms
    | "--bin" :: v :: rest, c, ms => scan rest { c with bin := v } ms
    | "--work" :: v :: rest, c, ms => scan rest { c with work := v } ms
    | m :: rest, c, ms => scan rest c (ms ++ [m])
    | [], c, ms => (c, ms)
  let (cfg, manifests) := scan args { cli := "", bin := "", work := "" } []
  if cfg.cli.isEmpty || cfg.bin.isEmpty || cfg.work.isEmpty || manifests.isEmpty then
    IO.eprintln "usage: l4protocol-live --cli FACTOIDAL_MJS --bin LEAN_BIN_DIR --work DIR MANIFEST..."
    return 2
  IO.FS.createDirAll cfg.work
  let mut t : Tally := {}
  let mut ix := 0
  for m in manifests do
    let (t', ix') ← runManifestLive cfg m t ix
    t := t'
    ix := ix'
  let total := t.pass + t.fail + t.xfail + t.stale
  IO.println s!"l4protocol-live: {t.pass} pass, {t.fail + t.xfail + t.stale} fail (out of {total}); expected failures {t.xfail}, stale {t.stale}, unsupported {t.unsupported}"
  return (if t.fail == 0 && t.stale == 0 then 0 else 1)

end Harness.ProtocolLive

def main (args : List String) : IO UInt32 := Harness.ProtocolLive.main args
