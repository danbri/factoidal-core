/-
Harness/Rdb2RdfRun — the W3C RDB2RDF test cases (R2RML and Direct Mapping
Test Cases, Editor's Draft 24 July 2012) run against the Lean SQL subset and
the Lean Direct Mapping.

For each database directory `D*` the harness reads `manifest.ttl` (Turtle,
read by the Lean Turtle parser), runs `create.sql` through `SQL.runScript`,
and for each `rdb2rdftest:DirectMapping` case compares
`DM2012.directGraph "http://example.com/base/"` with the expected graph
(`rdb2rdftest:output`, Turtle) by `Graph.isomorphicOutcome`. A case whose
`rdb2rdftest:hasExpectedOutput` is false passes when the mapping is rejected.

The R2RML cases (`rdb2rdftest:R2RML`) are counted and listed as "not run";
they run when `RDB2RDF/R2RML.lean` lands (design record
`docs/designissues/2026-11-01-r2rml-and-direct-mapping.md` §4).

Usage: `lake exe l4rdb2rdf DIR` (exit 0 when every Direct Mapping case passes).
Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RDB2RDF.DirectMapping
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.Syntax.Turtle

open L4Factoidal.RDF
open L4Factoidal.SQL
open L4Factoidal.RDB2RDF

def testNs : String := "http://purl.org/NET/rdb2rdf-test#"
def dcIdentifier : String := "http://purl.org/dc/elements/1.1/identifier"
def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

def objectsOf (g : Graph) (s : Subject) (p : String) : List Term :=
  g.filterMap fun t => if t.s == s && t.p.val == p then some t.o else none

def lexOf : Term → Option String
  | .literal l => some l.val.lexicalForm
  | _ => none

def subjectsOfType (g : Graph) (ty : String) : List Subject :=
  g.filterMap fun t =>
    if t.p.val == rdfTypeIri then
      match t.o with
      | .iri i => if i.val == ty then some t.s else none
      | _ => none
    else none

structure Case where
  id : String
  kind : String
  output : Option String
  expectOutput : Bool

def readCases (g : Graph) (kind : String) : List Case :=
  (subjectsOfType g (testNs ++ kind)).map fun s =>
    { id := ((objectsOf g s dcIdentifier).head?.bind lexOf).getD "?"
      kind
      output := (objectsOf g s (testNs ++ "output")).head?.bind lexOf
      expectOutput := ((objectsOf g s (testNs ++ "hasExpectedOutput")).head?.bind lexOf) != some "false" }

def readTurtle (path : String) (base : String) : IO (Except String Graph) := do
  let text ← IO.FS.readFile path
  match L4Factoidal.Syntax.parseTurtle text (some base) with
  | .ok g => pure (.ok g)
  | .error e => pure (.error s!"Turtle parse error in {path}: {repr e}")

def base : String := "http://example.com/base/"

def runDm (dir : System.FilePath) (db : Except String Database) (c : Case) : IO (Bool × String) := do
  let got := db.bind (DM2012.directGraph base)
  if !c.expectOutput then
    return match got with
      | .error e => (true, s!"rejected: {e}")
      | .ok g => (false, s!"expected a rejection, produced {g.length} triples")
  let some out := c.output | return (false, "no rdb2rdftest:output")
  match got with
  | .error e => return (false, e)
  | .ok g =>
    match ← readTurtle (dir / out).toString base with
    | .error e => return (false, e)
    | .ok want =>
      match Graph.isomorphicOutcome g want with
      | .equal => return (true, s!"{g.length} triples")
      | .notEqual =>
        let onlyGot := g.filter (fun t => !want.contains t)
        let onlyWant := want.filter (fun t => !g.contains t)
        let detail := (onlyGot.take 3).map (fun t => s!"    + {repr t}") ++ (onlyWant.take 3).map (fun t => s!"    - {repr t}")
        return (false, s!"produced {g.length}, expected {want.length}\n" ++ "\n".intercalate detail)
      | .budgetExceeded => return (false, "isomorphism budget exceeded")

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := (args.head?.getD "third_party/testing/rdb2rdf-tests")
  let entries ← root.readDir
  let dirs := (entries.filter (·.fileName.startsWith "D")).map (·.path) |>.qsort (fun a b => a.toString < b.toString)
  let mut pass := 0
  let mut fail := 0
  let mut notRun : List String := []
  for dir in dirs do
    let mpath := dir / "manifest.ttl"
    match ← readTurtle mpath.toString ("http://www.w3.org/2001/sw/rdb2rdf/test-cases/") with
    | .error e =>
      fail := fail + 1
      IO.println s!"FAIL {dir.fileName.getD ""}: {e}"
    | .ok mg =>
      let sql ← IO.FS.readFile (dir / "create.sql")
      let db := runScript sql
      for c in readCases mg "DirectMapping" do
        let (ok, msg) ← runDm dir db c
        if ok then
          pass := pass + 1
          IO.println s!"PASS {c.id}"
        else
          fail := fail + 1
          IO.println s!"FAIL {c.id}: {msg}"
      for c in readCases mg "R2RML" do
        notRun := notRun ++ [c.id]
  IO.println s!"rdb2rdf Direct Mapping: {pass} pass, {fail} fail (out of {pass + fail})"
  IO.println s!"rdb2rdf R2RML: {notRun.length} cases not run (R2RML is the next step)"
  pure (if fail == 0 && pass > 0 then 0 else 1)
