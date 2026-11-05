/-
Harness.ParseBenchQuery — `l4parse-bench-query`: the basic SPARQL path over a
parsed N-Triples file, for `tools/parse-bench.py query`. A separate executable,
so that the start-up of the SPARQL modules is not in `l4parse-bench`.

    l4parse-bench-query run STAGE FILE

STAGE is `null`, `nt` (read and parse only), `sparql-star` (two patterns joined on
`?s`) or `sparql-point` (one subject). The input is `l4parse-bench gen nt`. The
output is as `l4parse-bench run`; `items` is the number of solutions. Results:
`docs/20261105-parse-stack-perf.md`.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.NTriples

namespace Harness.ParseBenchQuery

open L4Factoidal L4Factoidal.RDF L4Factoidal.SPARQL

def starQuery : String :=
  "SELECT * WHERE { ?s <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://example.org/ns#Thing> . " ++
  "?s <http://www.w3.org/2000/01/rdf-schema#label> ?l }"

def pointQuery : String :=
  "SELECT ?l WHERE { <https://example.org/data/item7> <http://www.w3.org/2000/01/rdf-schema#label> ?l }"

def solutions (text : String) (g : Graph) : Nat :=
  match parseSparql text with
  | .ok q => (evalSelect {} { default := g, named := [] } q).2.length
  | .error _ => 0

def stageItems (stage src : String) : Option Nat :=
  let graph : Graph := match Syntax.parseNTriples src with
    | .ok g => g
    | .error _ => []
  match stage with
  | "null" => some src.utf8ByteSize
  | "nt" => some graph.length
  | "sparql-star" => some (solutions starQuery graph)
  | "sparql-point" => some (solutions pointQuery graph)
  | _ => none

def main : List String → IO UInt32
  | ["run", stage, file] => do
    let src := String.fromUTF8! (← IO.FS.readBinFile file)
    let a0 ← IO.getNumHeartbeats
    match (if stage == "null" then some src.utf8ByteSize else stageItems stage src) with
    | none => IO.eprintln s!"unknown stage {stage}"; return 2
    | some n =>
      let a1 ← IO.getNumHeartbeats
      IO.println s!"stage={stage} bytes={src.utf8ByteSize} items={n} allocs={a1 - a0}"
      return 0
  | _ => do
    IO.eprintln "usage: l4parse-bench-query run STAGE FILE"
    return 2

end Harness.ParseBenchQuery

def main (args : List String) : IO UInt32 := Harness.ParseBenchQuery.main args
