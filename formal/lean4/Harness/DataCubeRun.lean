/-
Harness/DataCubeRun — the RDF Data Cube integrity constraints (Recommendation of
16 January 2014, sections 10.1 and 11.1) run over the fixtures of
tests/datacube/.

The manifest has one line per case: a Turtle file (relative to the manifest)
and the constraints that its normalized form must violate, comma-separated, or
`none`. For each case the harness:

  1. normalizes the graph twice, by the section 10.1 updates through the SPARQL
     1.1 Update evaluator and by `DataCube.QB2014.normalize`, and fails the
     case when the two results do not have the same triples;
  2. checks IC-0 to IC-21 twice, by the section 11.1 queries through the SPARQL
     engine and by the direct functions, and fails the case when they disagree;
  3. compares the violated constraints with the manifest.

Usage: `lake exe l4datacube MANIFEST` (exit 0 when every case passes),
`lake exe l4datacube --show FILE.ttl` (print both verdicts for one file), or
`lake exe l4datacube --check-schema cube.ttl` (the vocabulary declarations
that `phase1_rdfs_sound` assumes are in the vocabulary).
Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.DataCube.Constraints
import L4Factoidal.DataCube.NormalizeTheorems
import L4Factoidal.Syntax.Turtle

open L4Factoidal.RDF
open L4Factoidal.DataCube.QB2014

structure CaseResult where
  violated : List String
  problems : List String

def runGraph (g : Graph) : CaseResult := Id.run do
  let mut problems : List String := []
  let gd := normalize g
  match normalizeSparql g with
  | .error e => problems := problems ++ [s!"normalization by SPARQL Update: {e}"]
  | .ok gs =>
    if !sameTriples gd gs then
      let onlyD := (gd.filter fun t => !gs.contains t).length
      let onlyS := (gs.filter fun t => !gd.contains t).length
      problems := problems ++
        [s!"normalization disagrees: {onlyD} triples only in the direct result, {onlyS} only in the SPARQL result"]
  match ic17Verbatim gd with
  | .ok true => problems := problems ++
      ["STALE: the IC-17 query as written answered true; the local variant tests/datacube/local/ic-17-sparql11.rq may no longer be needed"]
  | .ok false => pure ()
  | .error e => problems := problems ++ [s!"IC-17 as written: {e}"]
  let sparql := checkSparql gd
  let direct := checkDirect gd
  let mut violated : List String := []
  for (n, r) in sparql do
    let d := (direct.find? (·.1 == n)).map (·.2)
    match r with
    | .error e => problems := problems ++ [s!"{n}: {e}"]
    | .ok v =>
      if d != some v then
        problems := problems ++ [s!"{n}: SPARQL says {v}, direct says {d}"]
      if v then violated := violated ++ [n]
  return { violated, problems }

def readGraph (path : String) : IO (Except String Graph) := do
  let text ← IO.FS.readFile path
  match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) with
  | .ok g => pure (.ok g)
  | .error e => pure (.error s!"Turtle parse error: {repr e}")

def splitList (s : String) : List String :=
  if s.trimAscii.toString == "none" then []
  else (s.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--show", file] =>
    match ← readGraph file with
    | .error e => IO.eprintln e; pure 2
    | .ok g =>
      let r := runGraph g
      IO.println s!"violated: {if r.violated.isEmpty then "none" else ",".intercalate r.violated}"
      for p in r.problems do IO.println s!"problem: {p}"
      pure (if r.problems.isEmpty then 0 else 1)
  | ["--check-schema", file] =>
    -- `phase1_rdfs_sound` assumes `qbPhase1Schema`; check each triple is in
    -- the vendored Data Cube vocabulary.
    match ← readGraph file with
    | .error e => IO.eprintln e; pure 2
    | .ok g =>
      let missing := qbPhase1Schema.filter fun t => !g.contains t
      for t in missing do IO.println s!"missing from the vocabulary: {repr t}"
      IO.println s!"datacube schema: {qbPhase1Schema.length - missing.length} of {qbPhase1Schema.length} declarations found"
      pure (if missing.isEmpty then 0 else 1)
  | [manifest] =>
    let dir := (System.FilePath.mk manifest).parent.getD "."
    let lines := (← IO.FS.lines manifest).toList.filter fun l =>
      let t := l.trimAscii.toString
      t ≠ "" && !t.startsWith "#"
    let mut pass := 0
    let mut fail := 0
    for line in lines do
      match line.splitOn "\t" with
      | [file, expected] =>
        let path := (dir / file).toString
        match ← readGraph path with
        | .error e =>
          fail := fail + 1
          IO.println s!"FAIL {file}: {e}"
        | .ok g =>
          let r := runGraph g
          let exp := splitList expected
          let ok := r.problems.isEmpty && r.violated.all exp.contains && exp.all r.violated.contains
          if ok then
            pass := pass + 1
            IO.println s!"PASS {file}"
          else
            fail := fail + 1
            IO.println s!"FAIL {file}: expected {exp}, violated {r.violated}"
            for p in r.problems do IO.println s!"  problem: {p}"
      | _ =>
        fail := fail + 1
        IO.println s!"FAIL manifest line (need FILE<TAB>CONSTRAINTS): {line}"
    IO.println s!"datacube: {pass} pass, {fail} fail (out of {pass + fail})"
    pure (if fail == 0 && pass > 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: l4datacube MANIFEST | l4datacube --show FILE.ttl"
    pure 2
