import FoafGraph
open FoafGraph

private def prefixes := "@prefix f: <http://xmlns.com/foaf/0.1/> . @prefix e: <https://example.org/> . "
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def parse (text : String) (base : Option String := none)
    (limits : Limits := {}) : IO Data :=
  match fromTurtle text base limits with
  | .ok graph => pure graph
  | .error error => throw (IO.userError error)
private def person (g : Data) (id : String) : IO Person :=
  match g.people.find? (·.id == id) with
  | some p => pure p
  | none => throw (IO.userError ("missing person " ++ id))
private def hasLink (g : Data) (source target : String) : Bool :=
  g.links.any fun link =>
    (g.people[link.source]?.map (·.id)) == some source &&
    (g.people[link.target]?.map (·.id)) == some target

private def fixture (filename : String) : IO Unit := do
  let g ← parse (← IO.FS.readFile filename)
  check (g.people.size == 8 && g.links.size == 7) "fixture people/links"
  check ((← person g "iri:https://example.org/people/alice").label == "Alice") "fixture label"
  check ((← person g "iri:https://example.org/people/carol").label == "https://example.org/people/carol") "missing-label fallback"
  check (g.people.any (fun p => match p.subject with | .bnode _ => true | _ => false)) "blank identity retained"
  check ((← person g "iri:https://example.org/people/erin").label == "Zoë") "Turtle Unicode escape"

private def direction : IO Unit := do
  let g ← parse (prefixes ++ "e:a f:knows e:b, e:a . e:b f:knows e:a .")
  check (g.people.size == 2 && g.links.size == 3) "directed/self edge count"
  check (hasLink g "iri:https://example.org/a" "iri:https://example.org/a") "self edge missing"
  check (hasLink g "iri:https://example.org/b" "iri:https://example.org/a") "reverse edge missing"
  check (g.links.all fun l => l.source < g.people.size && l.target < g.people.size) "link bounds"

private def determinism : IO Unit := do
  let a ← parse (prefixes ++ "e:b f:name \"Bee\" . e:a f:knows e:b . e:a f:name \"Ay\" .")
  let b ← parse (prefixes ++ "e:a f:name \"Ay\" . e:a f:knows e:b . e:b f:name \"Bee\" . e:a f:knows e:b .")
  check (decide (a = b)) "triple permutation/duplicate changes output"
  check (a.people.toList.map (·.id) == ["iri:https://example.org/a","iri:https://example.org/b"]) "identity ordering"

private def labels : IO Unit := do
  let g ← parse (prefixes ++ "@prefix r: <http://www.w3.org/2000/01/rdf-schema#> . " ++
    "e:a a f:Person; f:name \"Zulu\"@en, \"Alpha\"@fr; r:label \"AAA\" . " ++
    "e:b a f:Person; r:label \"Fallback\" . e:c a f:Person; f:name \"Alpha\" .")
  check ((← person g "iri:https://example.org/a").label == "Alpha") "name priority/lexical choice"
  check ((← person g "iri:https://example.org/b").label == "Fallback") "rdfs label"
  check (g.people.size == 3) "same display label merged identities"
  check (!(← person g "iri:https://example.org/a").labelIsFallback) "literal marked fallback"

private def labelProvenance : IO Unit := do
  let g ← parse (prefixes ++ "e:a a f:Person; f:name \"https://example.org/a\" . e:b a f:Person .")
  let explicit ← person g "iri:https://example.org/a"
  let fallback ← person g "iri:https://example.org/b"
  check (explicit.label == "https://example.org/a" && !explicit.labelIsFallback) "URI-valued literal misclassified"
  check (fallback.label == "https://example.org/b" && fallback.labelIsFallback) "generated fallback provenance"
  check (decide (Data.decode g.encode = .ok g)) "label provenance JSON roundtrip"

private def blankIdentity : IO Unit := do
  let g ← parse (prefixes ++ "_:a f:knows e:a . e:a f:knows _:a . [] a f:Person . [] a f:Person .")
  check (g.people.size == 4 && g.links.size == 2) "blank and IRI identity/anonymous allocation"
  check ((g.people.filter fun p => match p.subject with | .bnode _ => true | _ => false).size == 3) "blank node identities lost"
  check (g.people.all fun p => match p.subject with
    | .bnode b => p.id == "bnode:" ++ b && p.label == "_:" ++ b
    | .iri i => p.id == "iri:" ++ i.val) "constructor-aware IDs/fallback"

private def exactPredicates : IO Unit := do
  let g ← parse (prefixes ++ "e:a e:knows e:b . e:c a e:Person . " ++
    "e:d f:knows \"not a resource\" . e:d f:knows \"not a resource\" . e:e f:name \"Only name\" .")
  check (g.people.isEmpty && g.links.isEmpty && g.ignoredKnows == 1) "lookalikes/invalid object policy"

private def baseResolution : IO Unit := do
  let g ← parse ("@prefix f: <http://xmlns.com/foaf/0.1/> . <alice> f:knows <bob> .") (some "https://example.org/people/")
  check (hasLink g "iri:https://example.org/people/alice" "iri:https://example.org/people/bob") "retrieval base not resolved"
  check ((fromTurtle "<alice> <knows> <bob> .").isOk == false) "unresolved relative IRI accepted"

private def syntaxErrors : IO Unit := do
  check ((fromTurtle (prefixes ++ "e:a f:knows")).isOk == false) "malformed Turtle accepted"
  check ((fromTurtle "@prefix f: <http://xmlns.com/foaf/0.1/> . <<( <https://e/a> f:knows <https://e/b> )>> f:name \"x\" .").isOk == false) "RDF1.2 accepted in RDF1.1 adapter"

private def limits : IO Unit := do
  check ((fromTurtle "" none {maxChars:=0}).isOk) "empty graph rejected"
  check ((fromTurtle " " none {maxChars:=0}).isOk == false) "character bound ignored"
  let text := prefixes ++ "e:a f:knows e:b, e:c ."
  check ((fromTurtle text none {maxPeople:=2}).isOk == false) "person bound ignored"
  check ((fromTurtle text none {maxLinks:=1}).isOk == false) "link bound ignored"
  let g ← parse text none {maxPeople:=3,maxLinks:=2}
  check (g.people.size == 3 && g.links.size == 2) "exact limit rejected"
  check ((fromTurtle text none {maxStringChars:=2}).isOk == false) "string bound ignored"

private def replaceField (j : L4Factoidal.JSON.Json) (key : String)
    (value : L4Factoidal.JSON.Json) : L4Factoidal.JSON.Json :=
  match j with
  | .object fs => .object (fs.map fun (k,v) => (k,if k == key then value else v))
  | _ => j

private def jsonRoundtrip : IO Unit := do
  let g ← parse (prefixes ++ "e:a f:knows _:b ; f:name \"Zo\\u00EB 李 \\\"Q\\\" \\n \\t \\\\ \\u0001\" .")
  let encoded := g.encode
  match Data.decode encoded with
  | .ok decoded => check (decide (g = decoded)) "RDF identity/Unicode/control JSON roundtrip"
  | .error e => throw (IO.userError e)
  check (encoded.toList.all fun c => c.toNat >= 32) "unescaped JSON control character"
  check ((Data.decode encoded {maxJsonChars:=1}).isOk == false) "JSON character bound ignored"

private def jsonValidation : IO Unit := do
  let g ← parse (prefixes ++ "e:a f:knows e:b .")
  let j := g.toJson
  check ((Data.fromJson (replaceField j "people" (.array [g.toJson,g.toJson]))).isOk == false) "wrong person schema accepted"
  let pj := match j with
    | .object fs => match fs.lookup "people" with | some (.array (p::_)) => p | _ => .null
    | _ => .null
  check ((Data.fromJson (replaceField j "people" (.array [pj,pj]))).isOk == false) "duplicate person accepted"
  check ((Data.fromJson (replaceField j "people" (.array [replaceField pj "id" (.string "wrong")]))).isOk == false) "inconsistent id accepted"
  check ((Data.fromJson (replaceField j "people" (.array [replaceField pj "labelIsFallback" (.string "true")]))).isOk == false) "nonboolean provenance accepted"
  check ((Data.fromJson (replaceField j "people" (.array [replaceField pj "label" (.string "Wrong fallback")]))).isOk == false) "inconsistent fallback accepted"
  let badLink : L4Factoidal.JSON.Json := .object [("source",.number "0"),("target",.number "2")]
  check ((Data.fromJson (replaceField j "links" (.array [badLink]))).isOk == false) "out-of-range link accepted"
  let link : L4Factoidal.JSON.Json := .object [("source",.number "0"),("target",.number "1")]
  check ((Data.fromJson (replaceField j "links" (.array [link,link]))).isOk == false) "duplicate link accepted"
  let badNumber : L4Factoidal.JSON.Json := .object [("source",.number "0.0"),("target",.number "1")]
  check ((Data.fromJson (replaceField j "links" (.array [badNumber]))).isOk == false) "fractional endpoint accepted"
  check ((Data.decode "{\"people\":[],\"links\":[],\"ignoredKnows\":0,\"ignoredKnows\":0}").isOk == false) "duplicate key accepted"
  check ((Data.fromJson j {maxPeople:=1}).isOk == false) "JSON people bound ignored"
  check ((Data.fromJson j {maxLinks:=0}).isOk == false) "JSON link bound ignored"
  check ((Data.fromJson j {maxStringChars:=1}).isOk == false) "JSON string bound ignored"

def main (args : List String) : IO Unit := do
  let some filename := args.head? | throw (IO.userError "supply fixture path")
  let cases : List (String × IO Unit) := [
    ("fixture",fixture filename), ("directed/self links",direction),
    ("deterministic RDF set view",determinism), ("label policy",labels), ("label provenance",labelProvenance),
    ("blank identity",blankIdentity), ("exact predicates",exactPredicates),
    ("base resolution",baseResolution), ("syntax errors",syntaxErrors), ("limits",limits),
    ("JSON Unicode roundtrip",jsonRoundtrip), ("JSON validation",jsonValidation)]
  for (name,test) in cases do
    test
    IO.println ("PASS " ++ name)
  IO.println s!"{cases.length} FOAF adapter test groups passed (native Lean; no GPU)"
