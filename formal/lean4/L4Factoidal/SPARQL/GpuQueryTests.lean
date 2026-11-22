import L4Factoidal.SPARQL.GpuQuery
import L4Factoidal.Syntax.NQuads
import L4Factoidal.SPARQL.Parser

/-! Small differential fixtures exercise the *same resumable evaluator* the
shipping ABI drives. The device here is the explicit numeric model; actual
WebGPU execution is covered separately by the browser integration gate. -/

namespace L4Factoidal.SPARQL.GpuQueryTests

open L4Factoidal.RDF L4Factoidal.Dataflow L4Factoidal.SPARQL GpuQuery

private def fixture := "<urn:a> <urn:p> <urn:b> .\n" ++
  "<urn:c> <urn:p> <urn:b> .\n" ++
  "<urn:b> <urn:q> <urn:d> .\n" ++
  "<urn:b> <urn:q> <urn:e> .\n" ++
  "<urn:a> <urn:p> <urn:a> .\n" ++
  "<urn:a> <urn:p> <urn:b> <urn:g1> .\n" ++
  "<urn:b> <urn:q> <urn:d> <urn:g1> .\n" ++
  "<urn:c> <urn:p> <urn:b> <urn:g2> .\n" ++
  "<urn:b> <urn:q> <urn:e> <urn:g2> .\n"

private def force : Config :=
  { available := true, minLeftRows := 1, minRightRows := 1 }

private def agrees (query : String) : Bool :=
  match Syntax.parseNQuads fixture, parseSparql query with
  | .ok ds, .ok q =>
      let env : EvalEnv := { dataset := some ds }
      let p := begin force env ds q
      let expected := referenceAnswer { env, ds, backend := none, query := q }
      p.denote == expected && p.cpu == expected &&
        p.run (fun job => if job.left.size % 2 == 0 then none else some job.pairs) == expected
  | _, _ => false

#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "SELECT ?o WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x } ORDER BY ?s ?x"
#guard agrees "SELECT DISTINCT ?o WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "SELECT ?s WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x } ORDER BY ?s OFFSET 1 LIMIT 2"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "SELECT ?o (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x } GROUP BY ?o"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x . FILTER(?s != ?x) }"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . OPTIONAL { ?o <urn:q> ?x } }"
#guard agrees "SELECT * WHERE { { ?s <urn:p> ?o } UNION { ?s <urn:q> ?o } }"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . MINUS { ?o <urn:q> <urn:d> } }"
#guard agrees "SELECT * WHERE { GRAPH <urn:g1> { ?s <urn:p> ?o . ?o <urn:q> ?x } }"
#guard agrees "SELECT * WHERE { GRAPH ?g { ?s <urn:p> ?o . ?o <urn:q> ?x } }"
#guard agrees "SELECT * FROM <urn:g1> WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "SELECT * FROM NAMED <urn:g2> WHERE { GRAPH ?g { ?s <urn:p> ?o . ?o <urn:q> ?x } }"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . BIND(STR(?s) AS ?name) }"
#guard agrees "SELECT * WHERE { { SELECT ?o WHERE { ?s <urn:p> ?o } } ?o <urn:q> ?x }"
#guard agrees "SELECT * WHERE { VALUES (?s ?o) { (<urn:a> UNDEF) (UNDEF <urn:b>) } ?s <urn:p> ?o }"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?s }"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o . ?x <urn:q> ?y }"
#guard agrees "SELECT * WHERE { ?s <urn:absent> ?o . ?o <urn:q> ?x }"
#guard agrees "ASK { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "ASK { ?s <urn:p> ?o . ?o <urn:q> ?x } LIMIT 0"
#guard agrees "CONSTRUCT { ?s <urn:result> ?x } WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"
#guard agrees "DESCRIBE ?s WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x } ORDER BY ?s LIMIT 1"
#guard agrees "DESCRIBE <urn:a> WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }"

/-- A deliberately colliding key includes every candidate; exact Lean
payload comparison still keeps only the equal pairs. -/
private def collisionPlan : Plan SolutionSeq :=
  candidateJoin force "forced-collision" [1, 2, 2] [2, 3]
    (fun _ : Nat => 0) (fun _ : Nat => 0)
    (fun l r => if l == r then some Binding.empty else none)
    (fun _ => [Binding.empty, Binding.empty])

#guard collisionPlan.denote.length == 2
#guard collisionPlan.cpu.length == 2
#guard ({left := #[0, 4294967296], right := #[4294967296, 0], label := "high-lane", maxPairs := 8} : Job).pairs == [(0, 1), (1, 0)]

private def jobShapes (p : Plan α) : List (Nat × Nat) := go p []
where
  go : Plan α → List (Nat × Nat) → List (Nat × Nat)
    | .done _, acc => acc.reverse
    | .dispatch job resume, acc =>
        go (resume (some job.pairs)) ((job.left.size, job.right.size) :: acc)

/-- Placement is observed, not inferred from answer equality: at least one
request is made and constant predicates reduce every transferred graph. -/
private def placementChecks : Bool :=
  match Syntax.parseNQuads fixture,
      parseSparql "SELECT * WHERE { ?s <urn:p> ?o . ?o <urn:q> ?x }" with
  | .ok ds, .ok q =>
      let env : EvalEnv := { dataset := some ds }
      let shapes := jobShapes (begin force env ds q)
      let backend := StoreDataset.indexedDatasetBackend ds
      !shapes.isEmpty && shapes.all (fun sizes => sizes.2 < ds.default.length) &&
        worthwhile force backend q && !worthwhile {} backend q
  | _, _ => false

#guard placementChecks

/-- Boundary regression for dataset-sized continuation stacks. The smaller
case still submits a numeric job; the larger case returns all named graphs
through the complete CPU operation. -/
private def namedGraphPlacementCheck (n : Nat) (expectGpu : Bool) : Bool :=
  let quads := String.join ((List.range n).map fun i =>
    s!"<urn:a> <urn:p> <urn:b> <urn:g{i}> .\n" ++
    s!"<urn:b> <urn:q> <urn:c> <urn:g{i}> .\n")
  match Syntax.parseNQuads quads,
      parseSparql "SELECT * WHERE { GRAPH ?g { ?s <urn:p> ?o . ?o <urn:q> ?x } }" with
  | .ok ds, .ok q =>
      let env : EvalEnv := { dataset := some ds }
      match begin force env ds q with
      | .dispatch _ _ => expectGpu && ds.named.length == n
      | .done answer =>
          !expectGpu && answer == referenceAnswer { env, ds, backend := none, query := q } &&
            match answer with
            | .select _ rows => rows.length == n
            | _ => false
  | _, _ => false

#guard namedGraphPlacementCheck 256 true
#guard namedGraphPlacementCheck 257 false

end L4Factoidal.SPARQL.GpuQueryTests
