/-
Harness.DatasetSetRegression — observable cardinality of the dataset handle
store (41 assertions).

RDF 1.1 Concepts and Abstract Syntax §3 and RDF 1.1 Semantics §4: an RDF graph
is a set of triples. A theorem stated with membership (`Graph.mem`) cannot
tell `[t]` from `[t, t]`; these checks observe the number of quads through the
same handle operations the wasm module exports (`datasetOpen` count,
`datasetQuadsJson` length, `SELECT (COUNT(*) ...)`, serializer output), after
open, clone, update, add and delete, for Turtle, N-Triples, N-Quads, JSON-LD,
RDF/XML and TriG input. They also check what a set must NOT do: distinct
lexical forms stay distinct, the same triple in two graphs stays two quads,
an empty named graph stays, and a SPARQL solution sequence keeps its
multiplicities (UNION, VALUES). A second group (16 assertions) checks the
parse entry points that answer quads without storing them
(`parseToDatasetJson`, `parseQuadsJson`, lenient `parseDocument`).

The assertions came from an unmerged prototype (2026-10-21, npm review finding
R02: `<urn:s> <urn:p> "x", "x" .` opened with size 2 and COUNT 2). Every
assertion runs; the exit code is 1 when one or more fail.

Run: `lake build l4dataset-set-regression && .lake/build/bin/l4dataset-set-regression`.
-/
import Wasm.Ops.Handles
import Wasm.Ops.ParseJsonLd

open L4Factoidal.RDF L4Factoidal.JSON L4Wasm.Ops

initialize failures : IO.Ref (List String) ← IO.mkRef []
initialize passes : IO.Ref Nat ← IO.mkRef 0

private def expect (label : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    passes.modify (· + 1)
    IO.println s!"PASS: {label}"
  else
    failures.modify (· ++ [label])
    IO.println s!"FAIL: {label}{if detail.isEmpty then "" else " — " ++ detail}"

/-- The parsed envelope, or `none` (an error envelope or invalid JSON). -/
private def envelope (text : String) : Option Json :=
  match parseJson? text with
  | some j => if j.getBool? "ok" == some true then some j else none
  | none => none

private def countOf (j : Option Json) : String :=
  match j.bind (·.field? "count") with
  | some (.number n) => n
  | _ => "?"

private def expectCount (label : String) (text : String) (n : Nat) : IO Unit :=
  let c := countOf (envelope text)
  expect label (c == toString n) s!"count {c}, expected {n}; envelope {text.take 200}"

private def handleOf (text : String) : String :=
  ((envelope text).bind (·.getString? "handle")).getD ""

private def countQuery (label h body : String) (expected : Nat) : IO Unit := do
  let text ← datasetQuery h ("SELECT (COUNT(*) AS ?n) WHERE { " ++ body ++ " }")
  let value := do
    let j ← envelope text
    let srj ← j.field? "srj"
    let results ← srj.field? "results"
    let rows ← results.getArray? "bindings"
    let row ← rows.head?
    let n ← row.field? "n"
    n.getString? "value"
  expect label (value == some (toString expected))
    s!"COUNT {value.getD "?"}, expected {expected}"

private def checkOpen (label fmt text : String) (n : Nat) : IO String := do
  let opened ← datasetOpenBy jsonLdReader text fmt ""
  expectCount (label ++ " open count") opened n
  let h := handleOf opened
  let q := envelope (← datasetQuadsJson h "")
  let len := (q.bind (·.getArray? "quads")).map List.length
  expect (label ++ " iteration count") (len == some n) s!"quads {len}, expected {n}"
  countQuery (label ++ " COUNT") h "?s ?p ?o" n
  pure h

def main : IO UInt32 := do
  let t := "<urn:s> <urn:p> \"x\" .\n"
  for fmt in ["turtle", "ntriples", "nquads"] do
    let h ← checkOpen fmt fmt (t ++ t) 1
    let _ ← datasetClose h
  let h ← checkOpen "Turtle object list" "turtle" "<urn:s> <urn:p> \"x\", \"x\" ." 1
  let text := envelope (← datasetSerialize h "nquads")
  let nq := text.bind (·.getString? "nquads")
  expect "serialization emits one triple" (nq == some t) s!"nquads {repr nq}"
  countQuery "UNION preserves SPARQL multiplicity" h
    "{ ?s ?p ?o } UNION { ?s ?p ?o }" 2
  countQuery "VALUES preserves SPARQL multiplicity" h "VALUES ?v { 1 1 } ?s ?p ?o" 2
  let cloned ← datasetClone h
  expectCount "clone count" cloned 1
  let clone := handleOf cloned
  countQuery "clone COUNT" clone "?s ?p ?o" 1
  expectCount "repeated INSERT" (← datasetUpdate h ("INSERT DATA { " ++ t ++ t ++ " }")) 1
  expectCount "repeated add" (← datasetAddQuads h (t ++ t)) 1
  expectCount "delete" (← datasetDeleteQuads h t) 0
  countQuery "delete invalidates cached backend" h "?s ?p ?o" 0
  countQuery "clone remains independent" clone "?s ?p ?o" 1
  let _ ← checkOpen "JSON-LD" "jsonld"
    "{\"@id\":\"urn:s\",\"urn:p\":[{\"@value\":\"x\"},{\"@value\":\"x\"}]}" 1
  let _ ← checkOpen "RDF/XML" "rdfxml"
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"urn:\"><rdf:Description rdf:about=\"urn:s\"><e:p>x</e:p><e:p>x</e:p></rdf:Description></rdf:RDF>" 1
  let trig ← datasetOpenBy jsonLdReader
    (t ++ "<urn:g1> {" ++ t ++ t ++ "} <urn:g2> {" ++ t ++ "} <urn:empty> {}") "trig" ""
  expectCount "graph scope keeps three quads" trig 3
  let gh := handleOf trig
  countQuery "default graph scope" gh "?s ?p ?o" 1
  countQuery "named graph scope" gh "GRAPH ?g { ?s ?p ?o }" 2
  countQuery "empty named graph remains present" gh "GRAPH ?g {}" 3
  let _ ← checkOpen "language-tag case" "turtle" "<urn:s> <urn:p> \"x\"@en, \"x\"@EN ." 1
  let _ ← checkOpen "distinct numeric lexical forms" "turtle"
    "<urn:s> <urn:p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer>, \"01\"^^<http://www.w3.org/2001/XMLSchema#integer> ." 2
  let _ ← checkOpen "distinct XML lexical forms" "turtle"
    "<urn:s> <urn:p> \"<a/>\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>, \"<a></a>\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> ." 2
  let fs ← failures.get
  let ps ← passes.get
  IO.println s!"dataset-set regression: {ps} pass, {fs.length} fail (out of {ps + fs.length})"
  -- Second group: every public parse entry point that answers quads without
  -- storing them gives a set. These do not go through the handle store, so
  -- `CertifiedDataset` does not cover them; the lenient N-Quads and TriG
  -- readers have no set theorem.
  let docs : List (String × String) :=
    [ ("turtle", "<urn:s> <urn:p> \"x\", \"x\" ."), ("ntriples", t ++ t), ("nquads", t ++ t),
      ("trig", "<urn:g> {" ++ t ++ t ++ "}"),
      ("jsonld", "{\"@id\":\"urn:s\",\"urn:p\":[{\"@value\":\"x\"},{\"@value\":\"x\"}]}"),
      ("rdfxml", "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"urn:\"><rdf:Description rdf:about=\"urn:s\"><e:p>x</e:p><e:p>x</e:p></rdf:Description></rdf:RDF>") ]
  for (fmt, text) in docs do
    expectCount s!"parseToDatasetJson {fmt}" (parseToDatasetJson text fmt "") 1
    let q := envelope (← parseQuadsJsonBy jsonLdReader text fmt "")
    let len := (q.bind (·.getArray? "quads")).map List.length
    expect s!"parseQuadsJson {fmt}" (len == some 1) s!"quads {len}, expected 1"
    if fmt != "jsonld" && fmt != "rdfxml" then
      expectCount s!"parseDocument lenient {fmt}"
        (parseDocumentBy jsonLdReader text fmt "" "{\"lenient\":true}") 1
  let fs2 ← failures.get
  let ps2 ← passes.get
  IO.println s!"parse entry points: {ps2 - ps} pass, {fs2.length - fs.length} fail (out of {ps2 - ps + fs2.length - fs.length})"
  let fs := fs2
  for f in fs do IO.println s!"  failed: {f}"
  pure (if fs.isEmpty then 0 else 1)
