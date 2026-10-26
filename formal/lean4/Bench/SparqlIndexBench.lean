import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

open L4Factoidal.RDF L4Factoidal.SPARQL

private def iri (value : String) : WfIri :=
  if valid : isIri value then ⟨value, valid⟩
  else ⟨"http://example.org/invalid", by decide⟩

private def personIri (person : Nat) : WfIri := iri s!"http://example.org/person/{person}"
private def predicateIri (slot : Nat) : WfIri := iri s!"http://example.org/property/{slot}"

private def mkGraph (people width : Nat) : Graph := Id.run do
  let mut graph : Graph := []
  for person in [0:people] do
    for slot in [0:width] do
      graph := { s := .iri (personIri person), p := predicateIri slot,
                 o := .literal (Literal.string s!"value/{person}/{slot}") } :: graph
  return graph.reverse

private def frozenStep (pattern : TriplePattern) (graph : Graph)
    (rows : SolutionSeq) : SolutionSeq :=
  match rows with
  | [] => []
  | first :: _ =>
      let mask : TpMask :=
        { s := (pattern.s.resolveKey first).isSome
        , p := (pattern.p.resolveKey first).isSome
        , o := (pattern.o.resolveKey first).isSome }
      if mask.s || mask.p || mask.o then
        let index := groupByKey (tripleKey mask) graph
        rows.flatMap (evalTPIdx mask index graph pattern)
      else
        rows.flatMap (evalTP pattern graph)

private def frozenRows (graph : Graph) : Bgp → SolutionSeq → SolutionSeq
  | [], rows => rows
  | pattern :: rest, rows => frozenRows graph rest (frozenStep pattern graph rows)

private def frozenBgp (patterns : Bgp) (graph : Graph) : SolutionSeq :=
  frozenRows graph patterns [Binding.empty]

private def mkBgp (mode : String) (width : Nat) : Bgp :=
  let subject := if mode == "point" then PatternSubject.iri (personIri 0) else .var "s"
  let patterns := (List.range width).map fun slot =>
    { s := subject, p := .iri (predicateIri slot), o := .var s!"value{slot}" : TriplePattern }
  if mode == "missing" then
    patterns ++ [{ s := subject, p := .iri (predicateIri width), o := .var "missing" }]
  else patterns

private def queryText (mode : String) (width : Nat) : String :=
  let subject := if mode == "point" then s!"<{personIri 0}>" else "?s"
  let patterns := (List.range width).map fun slot =>
    s!"{subject} <{predicateIri slot}> ?value{slot} ."
  let patterns := if mode == "missing" then
    patterns ++ [s!"{subject} <{predicateIri width}> ?missing ."] else patterns
  "SELECT * WHERE { " ++ String.intercalate " " patterns ++ " }"

private def median (values : List Nat) : Nat :=
  (values.toArray.qsort (· < ·))[values.length / 2]!

private def timeMedian (runs : Nat) (action : Unit → SolutionSeq) : IO (Nat × Nat) := do
  let _ ← IO.lazyPure fun _ => (action ()).length
  let mut elapsed : List Nat := []
  let mut count := 0
  for _ in [0:runs] do
    let started ← IO.monoNanosNow
    count ← IO.lazyPure fun _ => (action ()).length
    let stopped ← IO.monoNanosNow
    elapsed := (stopped - started) :: elapsed
  return (count, median elapsed)

private def parseNat (name value : String) (minimum maximum : Nat) : Except String Nat :=
  match value.toNat? with
  | some number =>
      if minimum ≤ number && number ≤ maximum then .ok number
      else .error s!"{name} must be between {minimum} and {maximum}"
  | none => .error s!"invalid {name}: {value}"

private structure Config where
  modes : List String
  sizes : List Nat
  runs : Nat
  width : Nat

private def parseConfig (args : List String) : Except String Config := do
  if args.length > 4 then
    throw "usage: l4sparql-index-bench [all|star|point|missing] [people,...] [runs] [width]"
  let mode := args[0]?.getD "all"
  let modes ← if mode == "all" then pure ["star", "point", "missing"]
    else if ["star", "point", "missing"].contains mode then pure [mode]
    else throw s!"unknown mode: {mode}"
  let sizes ← ((args[1]?.getD "100,1000,10000").splitOn ",").mapM
    (fun size => parseNat "people" size 1 100000)
  let runs ← parseNat "runs" (args[2]?.getD "5") 1 20
  let width ← parseNat "width" (args[3]?.getD "8") 2 32
  if sizes.any (fun people => people * width > 1000000) then
    throw "each fixture is capped at 1,000,000 triples; reduce people or width"
  return { modes, sizes, runs, width }

private def measureCase (config : Config) (mode : String) (people : Nat) (graph : Graph) : IO Unit := do
  let patterns := mkBgp mode config.width
  let query ← match parseSparql (queryText mode config.width) with
    | .ok query => pure query
    | .error error => throw (IO.userError s!"benchmark query parse failed: {repr error}")
  let dataset : Dataset := { default := graph, named := [] }
  let env : EvalEnv := {}
  let legacy ← IO.lazyPure fun _ => frozenBgp patterns graph
  let cached ← IO.lazyPure fun _ => evalBgpIdx patterns graph
  let selected ← IO.lazyPure fun _ => (evalSelect env dataset query).2
  let agrees ← IO.lazyPure fun _ => legacy == cached && cached == selected
  unless agrees do
    throw (IO.userError s!"exact result mismatch: mode={mode}, people={people}")
  let expected := if mode == "star" then people else if mode == "point" then 1 else 0
  unless cached.length == expected do
    throw (IO.userError s!"row count mismatch: expected={expected}, actual={cached.length}")
  let (legacyCount, legacyNs) ← timeMedian config.runs (fun _ => frozenBgp patterns graph)
  let (cachedCount, cachedNs) ← timeMedian config.runs (fun _ => evalBgpIdx patterns graph)
  let (selectCount, selectNs) ← timeMedian config.runs (fun _ => (evalSelect env dataset query).2)
  unless legacyCount == expected && cachedCount == expected && selectCount == expected do
    throw (IO.userError "timed evaluation returned a different row count")
  IO.println s!"{mode},{people},{graph.length},{patterns.length},{expected},{config.runs},{legacyNs},{cachedNs},{selectNs}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let config ← match parseConfig args with
    | .ok config => pure config
    | .error error => throw (IO.userError error)
  IO.println "mode,people,triples,patterns,rows,runs,legacy_median_ns,cached_median_ns,select_median_ns"
  for people in config.sizes do
    let graph ← IO.lazyPure fun _ => mkGraph people config.width
    for mode in config.modes do
      measureCase config mode people graph
