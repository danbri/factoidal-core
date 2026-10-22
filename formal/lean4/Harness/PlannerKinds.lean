/-
Harness/PlannerKinds — the source-kind test set of the capability-aware
planner, OKR batch 2, KR 2.3: https://github.com/danbri/factoidal/issues/801.
Design record `docs/designissues/2026-10-12-capability-aware-planner.md`,
section 10. Run from `l4planner-test` (`Harness/PlannerTest.lean`).

Six source kinds, each described from its description document by the
`describe` function of `L4Factoidal/Planner/Kinds/*.lean`:

| kind | description document | implementation in this test |
|---|---|---|
| `sbm11` | the manifest of a generation packed here (`Sbm11Pack.runPack`), and the predicate probe (the distinct first column of PSO) | `graphSource` over the rows read through the id path; a differential test against keyed id-path scans |
| `memory` | the dataset | `graphSource` over the dataset |
| `sparql` | a SPARQL 1.1 Service Description in Turtle, with VoID property partitions | `serviceImpl`: a SPARQL query through SERVICE, evaluated with a mock endpoint map |
| `facadex` | a SPARQL Anything IRI and the CSV header row | `graphSource` over the Façade-X triples of the CSV text |
| `rest` | an OpenAPI-like JSON document | `restImpl` over a mock HTTP function |
| `mcp` | MCP tool declarations | `mcpImpl` over a mock `tools/call` function |

No network. The cases check: the description parses; the planner
(`search`) finds the expected plan family for at least two requirements
per kind, and for two requirements that need three and five kinds in one
plan; each exact plan's `Plan.exec` gives the reference evaluator's
answers over the materialised declared graph (`PlannerCheck.runCase`).

Expected failures name https://github.com/danbri/factoidal/issues/801
and turn the run red when they pass (`PlannerCheck.XCase`).
-/
import Harness.PlannerCheck
import Harness.Sbm11Query
import Harness.Sbm11PackLib
import Harness.PlannerSbm11IO
import L4Factoidal.Planner.Kinds.Sbm11
import L4Factoidal.Planner.Kinds.Memory
import L4Factoidal.Planner.Kinds.Sparql
import L4Factoidal.Planner.Kinds.FacadeX
import L4Factoidal.Planner.Kinds.Rest
import L4Factoidal.Planner.Kinds.Mcp
import L4Factoidal.Syntax.NTriples

namespace PlannerKinds

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds PlannerCheck
open L4Factoidal.JSON (Json parseJson)

/-! ## Terms -/

def exNs : String := "http://example.org/"
def ex (n : String) : Term := .iri (mkWf (exNs ++ n))
def exP (n : String) : WfIri := mkWf (exNs ++ n)
def lit (s : String) : Term := .literal (Literal.string s)

def pKnows : WfIri := exP "knows"
def pManages : WfIri := exP "manages"
def pLivesIn : WfIri := exP "livesIn"
def pCountry : WfIri := exP "country"
def pName : WfIri := exP "name"
def pEmail : WfIri := exP "email"
def pTemperature : WfIri := exP "temperature"
def pPopulation : WfIri := exP "population"
def xyzName : WfIri := mkWf (FacadeX.xyzNs ++ "name")
def xyzTeam : WfIri := mkWf (FacadeX.xyzNs ++ "team")

def tr (s : String) (p : WfIri) (o : Term) : Triple := { s := .iri (mkWf (exNs ++ s)), p := p, o := o }

/-! ## Data and description documents -/

/-- The data packed into the SBM11 generation. -/
def sbmGraph : Graph :=
  [tr "alice" pKnows (ex "bob"), tr "bob" pKnows (ex "carol"), tr "carol" pKnows (ex "dave"),
   tr "alice" pManages (ex "carol")]

/-- The in-memory dataset. -/
def memGraph : Graph :=
  [tr "alice" pLivesIn (ex "rome"), tr "bob" pLivesIn (ex "london"),
   tr "carol" pLivesIn (ex "paris"), tr "dave" pLivesIn (ex "london")]

def endpointIri : WfIri := mkWf "https://sparql.example.org/sparql"

/-- The graph behind the mock SPARQL endpoint. -/
def endpointGraph : Graph :=
  [tr "london" pCountry (ex "uk"), tr "paris" pCountry (ex "fr"), tr "rome" pCountry (ex "it")]

def sdText : String :=
  "@prefix sd: <http://www.w3.org/ns/sparql-service-description#> .\n" ++
  "@prefix void: <http://rdfs.org/ns/void#> .\n" ++
  "@prefix fmt: <http://www.w3.org/ns/formats/> .\n" ++
  "<https://sparql.example.org/sparql> a sd:Service ;\n" ++
  "  sd:endpoint <https://sparql.example.org/sparql> ;\n" ++
  "  sd:supportedLanguage sd:SPARQL11Query ;\n" ++
  "  sd:resultFormat fmt:SPARQL_Results_JSON , fmt:SPARQL_Results_XML ;\n" ++
  "  sd:feature sd:BasicFederatedQuery ;\n" ++
  "  sd:defaultDataset [ a sd:Dataset ;\n" ++
  "    sd:defaultGraph [ a sd:Graph ; void:triples 3 ;\n" ++
  "      void:propertyPartition [ void:property <http://example.org/country> ; void:triples 3 ] ] ] .\n"

/-- A description without a query language: refused. -/
def sdNoQueryText : String :=
  "@prefix sd: <http://www.w3.org/ns/sparql-service-description#> .\n" ++
  "<https://sparql.example.org/update> a sd:Service ;\n" ++
  "  sd:endpoint <https://sparql.example.org/update> ;\n" ++
  "  sd:supportedLanguage sd:SPARQL11Update ;\n" ++
  "  sd:resultFormat <http://www.w3.org/ns/formats/SPARQL_Results_JSON> .\n"

def fxIri : String := "x-sparql-anything:location=file:///data/people.csv,csv.headers=true"
def csvText : String := "name,team\nBob,Red\nCarol,Blue\nDave,Red\n"
def fxJsonIri : String := "x-sparql-anything:location=file:///data/people.json"

def openApiText : String := "{
  \"openapi\": \"3.1.0\",
  \"servers\": [ { \"url\": \"https://api.example.org\" } ],
  \"paths\": {
    \"/people/{id}\": { \"get\": {
      \"operationId\": \"getPerson\",
      \"parameters\": [ { \"name\": \"id\", \"in\": \"path\", \"required\": true, \"schema\": { \"type\": \"string\" } } ],
      \"x-rdf-subject\": \"http://example.org/{id}\",
      \"x-cost\": { \"perCall\": 50, \"perRow\": 1, \"callQuota\": 1000 },
      \"responses\": { \"200\": { \"content\": { \"application/json\": { \"schema\": {
        \"type\": \"object\",
        \"properties\": {
          \"name\":  { \"type\": \"string\", \"x-rdf-predicate\": \"http://example.org/name\" },
          \"email\": { \"type\": \"string\", \"x-rdf-predicate\": \"http://example.org/email\", \"x-rdf-object\": \"iri\" },
          \"internalId\": { \"type\": \"integer\" } } } } } } } } } } }"

/-- An operation with two path parameters: refused today. -/
def openApiTwoParamsText : String := "{
  \"servers\": [ { \"url\": \"https://api.example.org\" } ],
  \"paths\": { \"/orgs/{org}/people/{id}\": { \"get\": {
      \"operationId\": \"getMember\",
      \"parameters\": [ { \"name\": \"org\", \"in\": \"path\", \"required\": true },
                        { \"name\": \"id\", \"in\": \"path\", \"required\": true } ],
      \"x-rdf-subject\": \"http://example.org/{id}\",
      \"responses\": { \"200\": { \"content\": { \"application/json\": { \"schema\": {
        \"properties\": { \"name\": { \"x-rdf-predicate\": \"http://example.org/name\" } } } } } } } } } } }"

def peopleJson : List (String × String) :=
  [("alice", "{\"name\": \"Alice\", \"email\": \"mailto:alice@example.org\", \"internalId\": 1}"),
   ("bob",   "{\"name\": \"Bob\", \"email\": \"mailto:bob@example.org\", \"internalId\": 2}"),
   ("carol", "{\"name\": \"Carol\", \"internalId\": 3}"),
   ("dave",  "{\"name\": \"Dave\", \"email\": \"mailto:dave@example.org\", \"internalId\": 4}")]

/-- The mock HTTP function: GET of a URL to a response body. -/
def mockHttp (url : String) : Option String :=
  (peopleJson.find? (fun (id, _) => url == "https://api.example.org/people/" ++ id)).map (·.2)

def weatherTool : String := "{
  \"name\": \"get_weather\",
  \"title\": \"Current weather\",
  \"description\": \"Current temperature in degrees Celsius for a city\",
  \"inputSchema\": { \"type\": \"object\",
    \"properties\": { \"city\": { \"type\": \"string\" } }, \"required\": [\"city\"] },
  \"outputSchema\": { \"type\": \"object\",
    \"properties\": { \"temperature\": { \"type\": \"number\" } }, \"required\": [\"temperature\"] },
  \"annotations\": { \"readOnlyHint\": true, \"openWorldHint\": true },
  \"_meta\": { \"org.factoidal/rdf\": {
    \"subject\": \"city\", \"subjectTemplate\": \"http://example.org/{city}\",
    \"predicates\": { \"temperature\": \"http://example.org/temperature\" },
    \"cost\": { \"perCall\": 100, \"perRow\": 0, \"callQuota\": 60 } } } }"

/-- A tool whose answer a model makes: approximate. -/
def populationTool : String := "{
  \"name\": \"estimate_population\",
  \"description\": \"Population estimate for a city, from a language model\",
  \"inputSchema\": { \"type\": \"object\",
    \"properties\": { \"city\": { \"type\": \"string\" } }, \"required\": [\"city\"] },
  \"outputSchema\": { \"type\": \"object\", \"properties\": { \"population\": { \"type\": \"integer\" } } },
  \"_meta\": { \"org.factoidal/rdf\": {
    \"subject\": \"city\", \"subjectTemplate\": \"http://example.org/{city}\",
    \"predicates\": { \"population\": \"http://example.org/population\" },
    \"exactness\": \"approximate\", \"cost\": { \"perCall\": 2000, \"perRow\": 0 } } } }"

/-- A tool with two required inputs: refused today. -/
def distanceTool : String := "{
  \"name\": \"distance\",
  \"inputSchema\": { \"type\": \"object\",
    \"properties\": { \"from\": { \"type\": \"string\" }, \"to\": { \"type\": \"string\" } },
    \"required\": [\"from\", \"to\"] },
  \"_meta\": { \"org.factoidal/rdf\": {
    \"subject\": \"from\", \"subjectTemplate\": \"http://example.org/{from}\",
    \"predicates\": { \"km\": \"http://example.org/distanceKm\" } } } }"

/-- A WebMCP-style tool declaration with no RDF mapping. -/
def plainTool : String := "{
  \"name\": \"get_weather\",
  \"description\": \"Current temperature for a city\",
  \"inputSchema\": { \"type\": \"object\",
    \"properties\": { \"city\": { \"type\": \"string\" } }, \"required\": [\"city\"] },
  \"outputSchema\": { \"type\": \"object\", \"properties\": { \"temperature\": { \"type\": \"number\" } } } }"

def weatherData : List (String × String) := [("london", "12"), ("paris", "15"), ("rome", "21")]
def populationAnswers : List (String × String) := [("paris", "2100000"), ("rome", "2800000")]

/-- The mock `tools/call`: tool name and arguments to a `CallToolResult`. -/
def mockMcp (name : String) (args : Json) : Option Json :=
  let city := (args.getString? "city").getD ""
  let answer (key : String) (table : List (String × String)) : Json :=
    match table.lookup city with
    | some n => .object [("content", .array [.object [("type", .string "text"), ("text", .string n)]]),
                         ("structuredContent", .object [(key, .number n)]), ("isError", .bool false)]
    | none => .object [("content", .array []), ("isError", .bool true)]
  if name == "get_weather" then some (answer "temperature" weatherData)
  else if name == "estimate_population" then some (answer "population" populationAnswers)
  else none

def intLit (n : String) : Term := (JsonTerms.numberTerm? n).getD (lit n)

/-- The declared extension of the approximate tool (Paris: 2102650); the
mock model answers 2100000. -/
def populationDeclared : List Tuple := [[ex "paris", intLit "2102650"], [ex "rome", intLit "2800000"]]

/-! ## Catalogs -/

def ok {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- A catalog with the source kind of each entry. -/
abbrev KCat := List (String × Source)

def kindOf (s : Source) : String := (s.cap.name.splitOn ":").headD "?"

def graphCat (ds : List Described) (g : Graph) : Catalog := ds.map (graphSource · g)

structure Built where
  sbm : List Described
  sbmGraph : Graph
  mem : List Described
  sparql : List Described
  fx : List Described
  fxGraph : Graph
  rest : List Described
  restOps : List Rest.Op
  weather : Mcp.Tool
  population : Mcp.Tool
  mcp : List Described
  manifest : L4Factoidal.Storage.Sbm11.Manifest.Manifest

def memDescribed : Except String (List Described) := Memory.describe memGraph

def sparqlSources (ds : List Described) : Catalog :=
  ds.map (Sparql.serviceSource [(endpointIri.val, endpointGraph)] endpointIri endpointGraph)

def restSources (b : Built) (ds : List Described) : Catalog :=
  ds.filterMap (fun d => b.restOps.findSome? (fun op =>
    if (Rest.describeOp op).any (·.cap.name == d.cap.name) then
      Rest.restSource mockHttp (peopleJson.map (·.1)) op d else none))

def mcpSources (b : Built) (ds : List Described) : Catalog :=
  ds.filterMap (fun d =>
    if d.cap.name.startsWith "mcp:get_weather." then
      Mcp.mcpSource mockMcp (weatherData.map (·.1)) b.weather d
    else if d.cap.name.startsWith "mcp:estimate_population." then
      Mcp.mcpSource mockMcp [] b.population d (declared := some populationDeclared)
    else none)

def Built.sbmCat (b : Built) (ds : List Described := b.sbm) : Catalog := graphCat ds b.sbmGraph
def Built.memCat (b : Built) (ds : List Described := b.mem) : Catalog := graphCat ds memGraph
def Built.fxCat (b : Built) (ds : List Described := b.fx) : Catalog := graphCat ds b.fxGraph

/-! ## SBM11: pack, open, probe, read -/

/-- Run `x` with standard output sent to a buffer (the packer prints its
statistics). -/
def silently {α : Type} (x : IO α) : IO α := do
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStdout (IO.FS.Stream.ofBuffer buf)
  try x finally discard <| IO.setStdout old

open Harness.Sbm11Query in
/-- The rows of permutation `perm` with key `key`, as triples. -/
def scanTriples (ss : Session) (perm : Nat) (key : Array UInt64) : IO (List Triple) := do
  let acc ← IO.mkRef (#[] : Array (UInt64 × UInt64 × UInt64))
  scanAll ss perm key (fun cols n => do
    for i in [0:n] do
      acc.modify (·.push (L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[0]! i,
        L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[1]! i,
        L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[2]! i)))
  let ord := L4Factoidal.Storage.Sbm11.IdQuery.permOrder[perm]!
  let mut out : Array Triple := #[]
  for (a, b, c) in ← acc.get do
    let cols := #[a, b, c]
    let pick (pos : Nat) : UInt64 := cols[((List.range 3).find? (fun j => ord[j]! == pos)).getD 0]!
    let s ← subjectOf (← ss.termOf (pick 0))
    let p ← match ← ss.termOf (pick 1) with
      | .iri i => pure i
      | _ => throw (IO.userError "a predicate that is not an IRI")
    let o ← ss.termOf (pick 2)
    out := out.push { s := s, p := p, o := o }
  pure out.toList

/-- Pack `g` into `dir/gen` with the SBM11 packer. -/
def packGeneration (dir : String) (g : Graph) : IO String := do
  let nt ← ok "N-Triples" (L4Factoidal.Syntax.Graph.toNTriples g)
  let src := dir ++ "/source.nt"
  let gen := dir ++ "/gen"
  IO.FS.writeFile src nt
  let rc ← silently (Sbm11Pack.runPack src gen 1 262144 4096 524288)
  if rc != 0 then throw (IO.userError s!"sbm11 pack exit {rc}")
  pure gen

def sameTripleSet (a b : Graph) : Bool := a.all b.contains && b.all a.contains && a.length == b.length

def sameTuples (a b : List Tuple) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- The values tried at each input position: the graph's terms at that
position, and one term that is not in the graph. -/
def sampleValues (part : Option WfIri) (g : Graph) (pos : Nat) : List Term :=
  let triples : List Triple := g.filter (keeps part)
  let vals : List Term := match part, pos with
    | none, 0 | some _, 0 => triples.map (fun (t : Triple) => t.s.toTerm)
    | none, 1 => triples.map (fun (t : Triple) => Term.iri t.p)
    | _, _ => triples.map (fun (t : Triple) => t.o)
  vals.eraseDups ++ [ex "nobody"]

def inputCombos (part : Option WfIri) (g : Graph) (positions : List Nat) : List InputBinding :=
  positions.foldr (fun i acc => acc.flatMap (fun rest => (sampleValues part g i).map (fun t => (i, t) :: rest))) [[]]

open Harness.Sbm11Query in
/-- The id path for one capability and one input: the keyed scan of the
capability's permutation, as tuples of its mapping. -/
def idPathTuples (ss : Session) (m : L4Factoidal.Storage.Sbm11.Manifest.Manifest) (d : Described)
    (inp : InputBinding) : IO (Option (List Tuple)) := do
  let some sh := Sbm11.shapeOf? m d | return none
  let some perm := Sbm11.permIndex? sh.perm | return none
  let some ord := Sbm11.permOrder? sh.perm | return none
  -- the key: the input value of each leading column's triple position
  let mut key : Array UInt64 := #[]
  for c in [0:sh.keyLen] do
    let pos := ord[c]!
    let val? : Option Term := match d.partition with
      | none => inp.lookup pos
      | some p => if pos == 1 then some (.iri p) else inp.lookup (if pos == 0 then 0 else 1)
    let some val := val? | return none
    match ← ss.idOf val with
    | some x => key := key.push x
    | none => return some []
  let rows ← scanTriples ss perm key
  return some ((rows.filter (keeps d.partition)).map (tupleOf d.partition))

/-! ## Cases -/

/-- A case with the source kinds the first plan must use (sorted). -/
structure KCase where
  base : Case
  kinds : Option (List String) := none

def firstKinds (c : Case) : Option (List String) := do
  let req ← c.req
  let r ← (search c.cat req c.k).head?
  pure ((r.rewriting.steps.filterMap (fun a => c.cat[a.src]?.map kindOf)).eraseDups.mergeSort (· ≤ ·))

def runKCase (c : KCase) : List String :=
  let errs := runCase c.base
  match c.kinds with
  | none => errs
  | some want =>
    match firstKinds c.base with
    | some got => if got == want then errs else errs ++ [s!"first plan kinds {got}, want {want}"]
    | none => errs ++ ["no first plan"]

def req (bgp : Bgp) (proj : List VarName) : Option Requirement := some { bgp := bgp, projection := proj }

def kcases (b : Built) : List KCase :=
  let sbmP := b.sbmCat (partitioned b.sbm)
  let sbmT := b.sbmCat (b.sbm.filter (·.partition.isNone))
  let memP := b.memCat (partitioned b.mem)
  let memT := b.memCat (b.mem.filter (·.partition.isNone))
  let sp := sparqlSources (partitioned b.sparql)
  let spT := sparqlSources (b.sparql.filter (·.partition.isNone))
  let fxP := b.fxCat (partitioned b.fx)
  let fxT := b.fxCat (b.fx.filter (·.partition.isNone))
  let rs := restSources b b.rest
  let weather := mcpSources b (b.mcp.filter (·.cap.name.startsWith "mcp:get_weather."))
  let pop := mcpSources b (b.mcp.filter (·.cap.name.startsWith "mcp:estimate_population."))
  [ -- SBM11
    { base := { id := "sbm11-predicate-scan", cat := sbmP, k := 1, answerable := true,
                req := req [tp (sv "x") pKnows (v "y")] ["x", "y"],
                first := some ["sbm11:pso/1[knows]"], minPlans := 1 } },
    { base := { id := "sbm11-subject-then-lookup", cat := sbmP, k := 2, answerable := true,
                req := req [tp (si (ex "alice")) pKnows (v "y"), tp (sv "y") pKnows (v "z")] ["y", "z"],
                first := some ["sbm11:pso/2[knows]", "sbm11:pso/2[knows]"] } },
    { base := { id := "sbm11-object-key", cat := sbmP, k := 1, answerable := true,
                req := req [tp (sv "x") pKnows (oi (ex "carol"))] ["x"],
                first := some ["sbm11:pos/2[knows]"] } },
    { base := { id := "sbm11-variable-predicate", cat := sbmT, k := 1, answerable := true,
                req := some { bgp := [{ s := sv "s", p := v "p", o := v "o" }], projection := ["s", "p", "o"] },
                first := some ["sbm11:pso/0"] } },
    -- in-memory dataset
    { base := { id := "memory-predicate-scan", cat := memP, k := 1, answerable := true,
                req := req [tp (sv "x") pLivesIn (v "c")] ["x", "c"],
                first := some ["memory:scan[livesIn]"] } },
    { base := { id := "memory-object-lookup", cat := memP, k := 1, answerable := true,
                req := req [tp (sv "x") pLivesIn (oi (ex "london"))] ["x"],
                first := some ["memory:o[livesIn]"] } },
    { base := { id := "memory-variable-predicate", cat := memT, k := 1, answerable := true,
                req := some { bgp := [{ s := si (ex "bob"), p := v "p", o := v "o" }], projection := ["p", "o"] },
                first := some ["memory:s"] } },
    -- SPARQL endpoint through SERVICE
    { base := { id := "sparql-partition-scan", cat := sp, k := 1, answerable := true,
                req := req [tp (sv "c") pCountry (v "k")] ["c", "k"], minPlans := 1 } },
    { base := { id := "sparql-subject-bound", cat := sp, k := 1, answerable := true,
                req := req [tp (si (ex "paris")) pCountry (v "k")] ["k"], minPlans := 2 } },
    { base := { id := "sparql-triple-scan", cat := spT, k := 1, answerable := true,
                req := some { bgp := [{ s := sv "s", p := v "p", o := v "o" }], projection := ["s", "p", "o"] },
                first := some ["sparql:triples"] } },
    -- Façade-X file
    { base := { id := "facadex-column", cat := fxP, k := 1, answerable := true,
                req := req [tp (sv "r") xyzName (v "n")] ["n"], first := some ["facadex:name"] } },
    { base := { id := "facadex-two-columns", cat := fxP, k := 2, answerable := true,
                req := req [tp (sv "r") xyzName (v "n"), tp (sv "r") xyzTeam (ol "Red")] ["n"] } },
    { base := { id := "facadex-triple-scan", cat := fxT, k := 1, answerable := true,
                req := some { bgp := [{ s := sv "r", p := v "p", o := ol "Blue" }], projection := ["r", "p"] },
                first := some ["facadex:scan"] } },
    -- REST API
    { base := { id := "rest-lookup", cat := rs, k := 1, answerable := true,
                req := req [tp (si (ex "bob")) pName (v "n")] ["n"], first := some ["rest:getPerson.name"] } },
    { base := { id := "rest-two-properties", cat := rs, k := 2, answerable := true,
                req := req [tp (si (ex "dave")) pName (v "n"), tp (si (ex "dave")) pEmail (v "m")] ["n", "m"] } },
    { base := { id := "rest-input-never-bound", cat := rs, k := 2, answerable := false,
                req := req [tp (sv "x") pName (v "n")] ["x", "n"] } },
    -- MCP tool
    { base := { id := "mcp-tool-call", cat := weather, k := 1, answerable := true,
                req := req [tp (si (ex "paris")) pTemperature (v "t")] ["t"],
                first := some ["mcp:get_weather.temperature"] } },
    { base := { id := "mcp-approximate-marked", cat := pop, k := 1, answerable := true,
                req := req [tp (si (ex "paris")) pPopulation (v "n")] ["n"], firstApprox := some true } },
    { base := { id := "mcp-input-never-bound", cat := weather, k := 2, answerable := false,
                req := req [tp (sv "c") pTemperature (v "t")] ["c", "t"] } },
    -- Mixed: three kinds in one plan
    { base := { id := "mixed-sbm11-rest-facadex", cat := sbmP ++ rs ++ fxP, k := 4, answerable := true,
                req := req [tp (sv "x") pKnows (v "y"), tp (sv "y") pName (v "n"),
                            tp (sv "r") xyzName (v "n"), tp (sv "r") xyzTeam (v "t")] ["x", "n", "t"],
                first := some ["sbm11:pso/1[knows]", "rest:getPerson.name", "facadex:name", "facadex:team"] },
      kinds := some ["facadex", "rest", "sbm11"] },
    -- Mixed: five kinds in one plan
    { base := { id := "mixed-five-kinds", cat := sbmP ++ memP ++ sp ++ weather ++ rs, k := 5,
                answerable := true,
                req := req [tp (sv "x") pKnows (v "y"), tp (sv "y") pLivesIn (v "c"),
                            tp (sv "c") pCountry (v "k"), tp (sv "c") pTemperature (v "t"),
                            tp (sv "y") pName (v "n")] ["x", "n", "k", "t"] },
      kinds := some ["mcp", "memory", "rest", "sbm11", "sparql"] },
    -- Mixed with the approximate tool: marked, the exact plan first when one exists
    { base := { id := "mixed-approximate-marked", cat := memP ++ pop, k := 2, answerable := true,
                req := req [tp (sv "x") pLivesIn (v "c"), tp (sv "c") pPopulation (v "n")] ["x", "n"],
                firstApprox := some true } }
  ]

/-- Description checks: each document parses and gives the expected
capability names. -/
def describeChecks (b : Built) : List (String × List String) :=
  let names (ds : List Described) := ds.map (·.cap.name)
  let inputSets (ds : List Described) := (ds.filter (·.partition.isNone)).map (·.cap.inputs)
  [ ("describe-sbm11",
      (if (inputSets b.sbm).length == 8 && Memory.subsets3.all (inputSets b.sbm).contains then []
       else [s!"triple-form input sets {inputSets b.sbm}"]) ++
      (if (b.sbm.filter (·.partition == some pKnows)).length == 4 then [] else ["not 4 knows shapes"]) ++
      (if Sbm11.manifestPerms b.manifest == ["pso", "pos", "spo", "osp"] then []
       else [s!"perms {Sbm11.manifestPerms b.manifest}"])),
    ("describe-memory",
      (if (b.mem.filter (·.partition.isNone)).length == 8 &&
          (b.mem.filter (·.partition == some pLivesIn)).length == 4 then [] else [s!"{names b.mem}"])),
    ("describe-sparql",
      (match Sparql.readDescription sdText with
       | .ok e => (if e.endpoint == endpointIri then [] else ["endpoint"]) ++
                  (if e.triples == some 3 then [] else ["void:triples"]) ++
                  (if e.partitions.map (·.1) == [pCountry] then [] else ["partitions"]) ++
                  (if e.features.length == 1 then [] else ["features"])
       | .error err => [err]) ++
      (if names b.sparql == ["sparql:triples", "sparql:country/scan", "sparql:country/s", "sparql:country/o"]
       then [] else [s!"{names b.sparql}"])),
    ("describe-sparql-refuses-update-only",
      (match Sparql.describe sdNoQueryText with
       | .ok _ => ["accepted a description with no query language"]
       | .error _ => [])),
    ("sparql-service-query-text",
      (match Sparql.callQuery? endpointIri (some pCountry) [(0, ex "paris")] with
       | some (q, outs) =>
         (if outs == [1] then [] else ["outputs"]) ++
         (match parseSparql q with | .ok _ => [] | .error _ => [s!"query does not parse: {q}"])
       | none => ["no query"])),
    ("describe-facadex",
      (if names b.fx == ["facadex:scan", "facadex:name", "facadex:team"] then [] else [s!"{names b.fx}"]) ++
      (if b.fxGraph.length == 1 + 3 + 6 then [] else [s!"{b.fxGraph.length} triples"])),
    ("describe-rest",
      (if names b.rest == ["rest:getPerson.name", "rest:getPerson.email"] then [] else [s!"{names b.rest}"]) ++
      (if b.rest.all (·.cap.inputs == [0]) then [] else ["inputs"]) ++
      (if b.rest.all (·.cap.cost.callQuota == some 1000) then [] else ["x-cost"])),
    ("describe-mcp",
      (if names b.mcp == ["mcp:get_weather.temperature", "mcp:estimate_population.population"] then []
       else [s!"{names b.mcp}"]) ++
      (if b.mcp.map (·.cap.exactness) == [.exact, .approximate] then [] else ["exactness"]) ++
      (if b.weather.cost.callQuota == some 60 then [] else ["cost"])),
    ("describe-mcp-refuses-unmapped-required-input",
      (match Mcp.describe distanceTool with
       | .ok _ => ["accepted a second required input"]
       | .error _ => []))
  ]

def implementedKinds : List String := ["sbm11", "memory", "sparql", "facadex", "rest", "mcp"]

def xcases (b : Built) : List XCase :=
  let rs := restSources b b.rest
  let fxAll := b.fxCat
  let sbmAll := b.sbmCat
  [ { id := "triple-form-in-mixed-catalog", issue := issue801,
      what := "source content constraints: with triple-form capabilities in a mixed catalog, every plan of the family gives the reference answers",
      test := fun _ =>
        let cat := sbmAll ++ rs ++ fxAll
        let r : Requirement := { bgp := [tp (sv "x") pKnows (v "y"), tp (sv "y") pName (v "n"),
                                         tp (sv "r") xyzName (v "n")], projection := ["x", "n"] }
        let fam := search cat r 3
        !fam.isEmpty && fam.all (fun p => sameMultiset (planRows cat r p.rewriting) (refRows cat r)) },
    { id := "facadex-json", issue := issue801,
      what := "Façade-X mapping of a JSON file",
      test := fun _ => (FacadeX.describe fxJsonIri (some "{\"name\": \"Bob\"}")).toBool },
    { id := "rest-two-path-parameters", issue := issue801,
      what := "a REST operation with two path parameters (two required inputs)",
      test := fun _ => (Rest.describe openApiTwoParamsText).toBool },
    { id := "mcp-two-required-inputs", issue := issue801,
      what := "an MCP tool with two required inputs",
      test := fun _ => (Mcp.describe distanceTool).toBool },
    { id := "tool-without-rdf-mapping", issue := issue801,
      what := "an MCP or WebMCP tool declaration with no RDF mapping (mapping from the output schema)",
      test := fun _ => (Mcp.describe plainTool).toBool },
    { id := "sparql-endpoint-over-http", issue := issue801,
      what := "a SPARQL endpoint call over HTTP (the SERVICE call with no mock endpoint map answers)",
      test := fun _ => !(Sparql.serviceImpl [] endpointIri (some pCountry) [(0, ex "paris")]).isEmpty },
    { id := "service-description-fetch", issue := issue801,
      what := "the service description fetched from the endpoint IRI (no document text given)",
      test := fun _ => (Sparql.describe "").toBool },
    { id := "sql-source-kind", issue := issue801,
      what := "an SQL engine as a source kind",
      test := fun _ => implementedKinds.contains "sql" } ]

/-! ## Run -/

structure Counts where
  pass : Nat := 0
  fail : Nat := 0
  xfail : Nat := 0
  xpass : Nat := 0

def Counts.record (c : Counts) (id : String) (errs : List String) : IO Counts := do
  if errs.isEmpty then
    IO.println s!"PASS {id}"
    pure { c with pass := c.pass + 1 }
  else
    IO.println s!"FAIL {id}: {errs}"
    pure { c with fail := c.fail + 1 }

def Counts.recordX (c : Counts) (x : XCase) (holds : Bool) : IO Counts := do
  if holds then
    IO.println s!"XPASS {x.id}: {x.what} now holds; flip to an assertion and update {x.issue}"
    pure { c with xpass := c.xpass + 1 }
  else
    IO.println s!"xfail {x.id}: {x.what} ({x.issue})"
    pure { c with xfail := c.xfail + 1 }

def debug : IO Bool := return (← IO.getEnv "PLANNER_KINDS_DEBUG").isSome

open Harness.Sbm11Query in
def run : IO Counts := do
  let tmp ← IO.FS.createTempDir
  try
    let genDir ← packGeneration tmp.toString sbmGraph
    let ss ← openSession .merkle genDir
    let m := ss.g.manifest
    -- the predicate probe: the distinct first column of PSO
    let pso ← scanTriples ss 0 #[]
    let preds := (pso.map (·.p)).eraseDups
    let sbm ← ok "sbm11 describe" (Sbm11.describe m (some preds))
    -- the rows, read through the id path (full SPO scan)
    let rows ← scanTriples ss 2 #[]
    let mem ← ok "memory describe" memDescribed
    let sparql ← ok "sparql describe" (Sparql.describe sdText)
    let fxOpts ← ok "facadex options" (FacadeX.readOptions fxIri)
    let fx ← ok "facadex describe" (FacadeX.describe fxIri (some csvText))
    let fxGraph ← ok "facadex triples" (FacadeX.triplesOf fxOpts csvText)
    let restOps ← ok "rest describe" (Rest.readOps openApiText)
    let weather ← ok "mcp weather" (Mcp.readTool weatherTool)
    let population ← ok "mcp population" (Mcp.readTool populationTool)
    let b : Built := { sbm := sbm, sbmGraph := rows, mem := mem, sparql := sparql, fx := fx,
                       fxGraph := fxGraph, rest := restOps.flatMap Rest.describeOp, restOps := restOps,
                       weather := weather, population := population,
                       mcp := Mcp.describeTool weather ++ Mcp.describeTool population, manifest := m }
    let mut c : Counts := {}
    -- SBM11: the generation's rows are the packed triples
    c ← c.record "sbm11-pack-read-round-trip"
      (if sameTripleSet rows sbmGraph then [] else [s!"{rows.length} rows read, {sbmGraph.length} packed"])
    -- SBM11: each capability's pure implementation equals the keyed id-path scan
    let mut compared := 0
    let mut diffs : List String := []
    for d in sbm do
      let src := graphSource d rows
      for inp in inputCombos d.partition rows d.cap.inputs do
        match ← idPathTuples ss m d inp with
        | none => diffs := diffs ++ [s!"{d.cap.name}: no shape"]
        | some ids =>
          compared := compared + 1
          if !sameTuples ids (src.sem.impl inp) then
            diffs := diffs ++ [s!"{d.cap.name} {repr inp}: id path {ids.length} rows, pure {(src.sem.impl inp).length}"]
    c ← c.record s!"sbm11-id-path-differential ({compared} calls)" (diffs.take 5)
    for (id, errs) in describeChecks b do
      c ← c.record id errs
    let dbg ← debug
    for kc in kcases b do
      if dbg then
        match kc.base.req with
        | some r => IO.println s!"debug {kc.base.id}: {(search kc.base.cat r kc.base.k).map (fun x => (srcNames kc.base.cat x.rewriting, x.cost, x.approx))}"
        | none => pure ()
      c ← c.record kc.base.id (runKCase kc)
    for x in xcases b do
      c ← c.recordX x (x.test ())
    -- SBM11 through IO at call time (KR 4.1, issue 875): every plan of the
    -- family of each requirement run with `Plan.runM` over the id-path calls
    -- reads PRB1 bytes during the run and gives the rows of the pure run.
    -- First the hypothesis of `execM_eq_exec` for every catalog source and
    -- sampled input: the IO call returns the pure implementation's tuples.
    let ioReqs : List (String × Requirement) :=
      [("knows", { bgp := [tp (sv "x") pKnows (v "y")], projection := ["x", "y"] }),
       ("alice-knows-knows", { bgp := [tp (si (ex "alice")) pKnows (v "y"), tp (sv "y") pKnows (v "z")],
                               projection := ["y", "z"] }),
       ("knows-carol", { bgp := [tp (sv "x") pKnows (oi (ex "carol"))], projection := ["x"] }),
       ("manages-knows", { bgp := [tp (sv "x") pManages (v "y"), tp (sv "y") pKnows (v "z")],
                           projection := ["x", "z"] })]
    let sbmDs := partitioned b.sbm
    let sbmCat := b.sbmCat sbmDs
    let mut ioErrs : List String := []
    let mut ioCalls := 0
    for ((d, src), i) in (sbmDs.zip sbmCat).zipIdx do
      for inp in inputCombos d.partition rows d.cap.inputs do
        ioCalls := ioCalls + 1
        match ← (PlannerSbm11IO.idPathCalls ss m sbmDs i inp).run with
        | .ok tups =>
          if !sameTuples tups (src.sem.impl inp) then
            ioErrs := ioErrs ++ [s!"call {d.cap.name} {repr inp} differs from the pure implementation"]
        | .error e => ioErrs := ioErrs ++ [s!"call {d.cap.name}: {e}"]
    let mut plans := 0
    for (name, r) in ioReqs do
      let fam := search sbmCat r r.bgp.length
      if fam.isEmpty then ioErrs := ioErrs ++ [s!"{name}: no plan"]
      for rk in fam do
        plans := plans + 1
        let p := rk.rewriting.toPlan r
        let (ioRows, bytes) ← PlannerSbm11IO.runIO ss m sbmDs sbmCat p
        if bytes == 0 then ioErrs := ioErrs ++ [s!"{name}: no PRB1 bytes read during the run"]
        if !PlannerSbm11IO.sameMultiset (PlannerSbm11IO.canonRows r.projection ioRows)
            (PlannerSbm11IO.canonRows r.projection (p.run sbmCat)) then
          ioErrs := ioErrs ++ [s!"{name}: IO run differs from the pure run"]
    c ← c.record s!"sbm11-io-at-call-time ({ioCalls} calls, {plans} plans)" (ioErrs.take 5)
    -- Stack use of `Plan.execM` in `ExceptT String IO` over a join whose
    -- left side gives 1,000,000 rows (the rows go through `List.mapM`): the
    -- run completes and gives every row.
    let bigN := 1000000
    let bigExt : List Tuple := (List.range bigN).map (fun i => [ex s!"s{i}", ex "o"])
    let bigSrc : Source := { cap := { name := "big", arity := 2, inputs := [], location := "test",
                                      cost := { perCall := 1, perRow := 1 }, exactness := .exact },
                             mapping := graphMapping (some pKnows),
                             sem := { ext := bigExt, impl := fun _ => bigExt } }
    let bigPlan : Plan := .join (.access { src := 0, args := [.var "x", .var "y"] }) .unit
    let bigErrs : List String ← match ← (bigPlan.runM [bigSrc] (pureCalls (m := ExceptT String IO) [bigSrc])).run with
      | .ok rows => pure (if rows.length == bigN then [] else [s!"{rows.length} rows, want {bigN}"])
      | .error e => pure [e]
    c ← c.record s!"execm-io-large-join ({bigN} rows)" bigErrs
    -- The execution state machine driver (`Exec.run`) still takes tuples from
    -- `Source.sem.impl` and failures from a fault schedule.
    c ← c.recordX { id := "exec-driver-io", issue := "https://github.com/danbri/factoidal/issues/933",
                    what := "Exec.run makes its Call/Receive/Fail steps through IO calls (a call error is a Fail)",
                    test := fun _ => false } false
    pure c
  finally
    IO.FS.removeDirAll tmp

end PlannerKinds
