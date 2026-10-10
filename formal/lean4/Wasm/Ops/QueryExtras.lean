/-
Wasm.Ops.QueryExtras — `queryRaw`, the query entry of the npm package
that answers serialised text:

  queryRaw(data, sparql, optsJson)
    -> {"ok":true,"text":"…"}

`queryHdt`, the other entry this module held until 2026-10-10, is in
`Wasm/Ops/QueryHdt.lean`, so that the core dispatch (`Wasm/CoreDispatch.lean`,
https://github.com/danbri/factoidal/issues/713 stage 4) serves `queryRaw`
without linking the HDT reader.

`queryRaw` is the "one call, serialised answer" entry that
`npm/factoidal/index.js` has as a legacy export. The F* build answers it
through its command-line driver; here it is a dispatch operation.
`optsJson` is `""` or an object with the members

  dataFormat  turtle (default) | ttl | ntriples | nt | nquads | nq |
              trig | rdfxml | rdf        — how `data` is read (with the
              tags of the `ExtraReader` the caller passes: JSON-LD in the
              full dispatch)
  entail      none (default) | RDFS | OWL-RL | x-rdfscore | x-rdfsplus
              — closure of the DEFAULT graph before the query: the
                `owlClosure` closures of `Wasm/Ops/Reason.lean` for RDFS
                and OWL-RL, its `rhoDfClosure` (core RDFS) and
                `rdfsPlusClosure` (RDFS-Plus) closures for the other two
  output      json (default) | csv | tsv | xml | table | ntriples

`text` is the answer in the requested format. `json`, `csv`, `tsv` and
`xml` are the W3C SPARQL results formats (`SPARQL/ResultsJson`,
`ResultsCsvTsv`, `ResultsXml`); CSV and TSV have no ASK encoding, so an
ASK query with those outputs is an error. A CONSTRUCT or DESCRIBE answer
is a graph and has no results format: with `ntriples` or `table` it is
N-Triples text, with any other output it is an error. `table` and
`ntriples` are display formats of the F* command-line driver, kept for
the same signature: `table` draws the SELECT rows with N-Triples term
syntax, and `ntriples` of a SELECT lists `?var = term` per row.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import Wasm.Ops.Parse
import Wasm.Ops.Query
import Wasm.Ops.ExtFns
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Results
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsCsvTsv
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.OWL.RLClosure
-- The `@[csimp]` theorem that makes `OWL.RL.closureFix` compile to the
-- indexed closure (see the note in `Wasm/Ops/Reason.lean`).
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.RDFSPlus

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.JSON

/-! ## queryRaw -/

private inductive RawAnswer where
  | result (r : QueryResult)
  | graph  (g : Graph)

/-- The `rdf:_n` slice of a graph, as `Wasm/Ops/Reason.lean` computes it. -/
private def containerSlice (g : Graph) : List WfIri :=
  (L4Factoidal.RDFS.containerMembershipIn g).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i])
    [L4Factoidal.RDFS.rdf1]

private def closeDefaultGraph (entail : String) (ds : Dataset) : Except String Dataset :=
  match entail with
  | "none" | "" => .ok ds
  | "RDFS" | "rdfs" =>
      let g := ds.default
      .ok { ds with default :=
        L4Factoidal.RDFS.fullClosure (withMinimalD []) (containerSlice g) g }
  | "OWL-RL" | "owl-rl" | "owl_rl" =>
      .ok { ds with default := L4Factoidal.OWL.RL.closureFix ds.default }
  -- The core-RDFS (rho-df) closure of `rhoDfClosure` and the RDFS-Plus
  -- closure of `rdfsPlusClosure` (`Wasm/Ops/Reason.lean`): the
  -- `x-rdfscore` and `x-rdfsplus` regimes of the npm `query()` option
  -- `entail`, which the F* command-line driver also accepted.
  | "x-rdfscore" =>
      .ok { ds with default := L4Factoidal.RDFS.closureFix ds.default }
  | "x-rdfsplus" =>
      .ok { ds with default := L4Factoidal.RDFS.rdfsPlusClosureFix ds.default }
  | other => .error
      s!"queryRaw: entail must be none, RDFS, OWL-RL, x-rdfscore or x-rdfsplus (got '{other}')"

private def evalRaw (ds : Dataset) (sparql : String) : Except String RawAnswer :=
  match parseSparql sparql with
  | .error e => .error s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    let env : EvalEnv := { base := q.base, ext := extFnsWith [], dataset := some ds }
    match q.form with
    | .ask => .ok (.result (.boolean (evalAsk env ds q)))
    | .select _ =>
        let (vars, rows) := evalSelect env ds q
        .ok (.result (.bindings vars rows))
    | .construct _ => .ok (.graph (evalConstruct env ds q))
    | .describe _  => .ok (.graph (evalDescribe env ds q))

private def termText (t : Term) : String :=
  match L4Factoidal.Syntax.Term.toNTriples .rdf12 t with
  | Except.ok s    => s
  | Except.error _ => "<unserialisable>"

private def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- The SELECT rows as an ASCII table: one `?var` column per variable,
cells in N-Triples term syntax, and a closing count line. -/
private def tableText (vars : List String) (rows : List (List (String × Term))) : String :=
  if rows.isEmpty then "(no results)\n"
  else
    let cell (row : List (String × Term)) (v : String) : String :=
      match row.lookup v with
      | some t => termText t
      | none   => ""
    let widths := vars.map (fun v =>
      rows.foldl (fun m row => max m (cell row v).length) (v.length + 1))
    let sep := "+" ++ String.intercalate "+" (widths.map (fun w =>
      String.ofList (List.replicate (w + 2) '-'))) ++ "+"
    let line (cells : List String) : String :=
      "|" ++ String.join ((cells.zip widths).map (fun (c, w) => " " ++ padRight c w ++ " |"))
    sep ++ "\n" ++ line (vars.map (fun v => "?" ++ v)) ++ "\n" ++ sep ++ "\n"
      ++ String.join (rows.map (fun row => line (vars.map (cell row)) ++ "\n"))
      ++ sep ++ "\n" ++ s!"{rows.length} result(s)\n"

private def varEqualsText (vars : List String) (rows : List (List (String × Term))) : String :=
  String.join (rows.map (fun row =>
    String.join (vars.filterMap (fun v =>
      (row.lookup v).map (fun t => "?" ++ v ++ " = " ++ termText t ++ "  ")) ++ ["\n"])))

private def renderRaw (output : String) (a : RawAnswer) : Except String String :=
  match a with
  | .graph g =>
      if output == "ntriples" || output == "table" then
        Graph.toNTriples g .rdf12
      else
        .error ("queryRaw: a CONSTRUCT or DESCRIBE answer is a graph and has no "
                ++ s!"'{output}' results format; use output 'ntriples'")
  | .result r =>
    match output, r with
    | "json", _ => .ok (r.toSrj)
    | "xml", _  => .ok (r.toSrx)
    | "csv", _  => r.toCsv
    | "tsv", _  => r.toTsv
    | "table", .boolean b | "ntriples", .boolean b => .ok (if b then "true\n" else "false\n")
    | "table", .bindings vars rows => .ok (tableText vars rows)
    | "ntriples", .bindings vars rows => .ok (varEqualsText vars rows)
    | other, _ => .error s!"queryRaw: unknown output format '{other}'"

/-- `queryRaw(data, sparql, optsJson)`; `extra` reads the syntaxes outside
`Wasm/Ops/Parse.lean`'s table. -/
def queryRawBy (extra : ExtraReader) (data sparql optsJson : String) : String :=
  let opts : Option Json := if optsJson == "" then none else parseJson? optsJson
  let field (k d : String) : String :=
    match opts.bind (fun j => j.getString? k) with
    | some v => v
    | none   => d
  let output := field "output" "json"
  if !(["json", "csv", "tsv", "xml", "table", "ntriples"].contains output) then
    errJson s!"queryRaw: output must be json, csv, tsv, xml, table or ntriples (got '{output}')"
  else
  match parseTextToDatasetBy extra data (field "dataFormat" "turtle") "" with
  | .error e => errJson s!"queryRaw: {e}"
  | .ok ds0 =>
    match closeDefaultGraph (field "entail" "none") ds0 with
    | .error e => errJson e
    | .ok ds =>
      match evalRaw ds sparql with
      | .error e => errJson e
      | .ok a =>
        match renderRaw output a with
        | .error e => errJson e
        | .ok text => okWith [("text", .string text)]

/-! ## Build-time checks (positive and negative) -/

private def rawData : String :=
  "<http://e/a> <http://e/name> \"Alice\" .\n<http://e/b> <http://e/name> \"Bob\" .\n"
private def rawQuery : String := "SELECT ?n WHERE { ?p <http://e/name> ?n } ORDER BY ?n"

#guard queryRawBy noExtraReader rawData rawQuery "{\"dataFormat\":\"ntriples\",\"output\":\"csv\"}"
         == "{\"ok\":true,\"text\":\"n\\r\\nAlice\\r\\nBob\\r\\n\"}"
#guard (queryRawBy noExtraReader rawData rawQuery "{\"dataFormat\":\"ntriples\",\"output\":\"yaml\"}").startsWith
         "{\"ok\":false"
#guard (queryRawBy noExtraReader rawData "SELECT WITHOUT" "{\"dataFormat\":\"ntriples\"}").startsWith
         "{\"ok\":false"
-- The entailment regimes: a subclass membership is entailed under RDFS,
-- x-rdfscore and x-rdfsplus and not under none; an owl:inverseOf statement
-- is entailed under x-rdfsplus and not under x-rdfscore; an unknown regime
-- is refused.
private def entailData : String :=
  "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .\n" ++
  "<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .\n" ++
  "<http://e/p> <http://www.w3.org/2002/07/owl#inverseOf> <http://e/q> .\n" ++
  "<http://e/a> <http://e/p> <http://e/b> .\n"
private def askD : String :=
  "ASK { <http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> }"
private def askInv : String := "ASK { <http://e/b> <http://e/q> <http://e/a> }"
private def rawEntail (regime q : String) : String :=
  queryRawBy noExtraReader entailData q ("{\"dataFormat\":\"ntriples\",\"entail\":\"" ++ regime ++ "\"}")
#guard ((rawEntail "x-rdfscore" askD).splitOn "boolean\\\":true").length > 1
#guard ((rawEntail "x-rdfsplus" askD).splitOn "boolean\\\":true").length > 1
#guard ((rawEntail "RDFS" askD).splitOn "boolean\\\":true").length > 1
#guard ((rawEntail "none" askD).splitOn "boolean\\\":false").length > 1
#guard ((rawEntail "x-rdfsplus" askInv).splitOn "boolean\\\":true").length > 1
#guard ((rawEntail "x-rdfscore" askInv).splitOn "boolean\\\":false").length > 1
#guard (rawEntail "x-unknown" askD).startsWith "{\"ok\":false"


end L4Wasm.Ops
