/-
Harness.OwlSpeciesFile — the OWL 2 species verdict (DL or Full) of one
ontology document given as N-Triples or N-Quads, with its imported
documents.

    l4owl-species DOC.nt [IMPORTED.nt ...]
    l4owl-species --phases DOC.nt

Prints one JSON object: the verdict, the number of violations, the count
of each violation kind, and the first ten violations. Exit 0 when the
species is DL, 1 when it is Full, 2 on a usage or read error.

The verdict is the library's `L4Factoidal.OWL.SyntaxDL.speciesViolations`,
the same function `l4owl-probe --species` scores against the
`test:species` annotations of the W3C OWL 2 catalogs (488 pass, 0 fail,
1 local-override, out of 489, on 2026-10-10). This file only reads the
documents and prints the result; it holds no OWL logic.

Inputs (OWL 2 Mapping to RDF Graphs §3, Structural Specification §3.4):
`pDoc` is the first document. `pMerged` is the RDF merge (RDF 1.1
Semantics §4.1) of all the documents: each imported document's blank
nodes get the prefix `impN_`, as `l4owl-probe` does for the catalog
imports. The imports that count as available are the `owl:Ontology` IRIs
the imported documents declare; an `owl:imports` of any other IRI is
reported as `unresolved-import`, which makes the verdict Full.

Used by `tools/owl-real-bench.sh` for the species column of
`docs/designissues/2026-10-10-owl-real-ontologies.md`
(https://github.com/danbri/factoidal/issues/651, plan item 4).
-/
import L4Factoidal.OWL.SyntaxDL
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.RDF.Graph
import L4Factoidal.JSON.Serialize

namespace OwlSpeciesFile

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

def rdfType : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def owlOntology : String := "http://www.w3.org/2002/07/owl#Ontology"

/-- The `owl:Ontology` IRIs a document declares. -/
def ontologyIris (g : Graph) : List String :=
  g.filterMap (fun t =>
    match t.s, t.o with
    | .iri s, .iri o =>
        if t.p.val == rdfType && o.val == owlOntology then some s.val else none
    | _, _ => none)

/-- The kind of a violation: its text after the `premise: ` scope,
up to the next `: `. -/
def kindOf (v : String) : String :=
  let body := (v.drop "premise: ".length).toString
  match body.splitOn ": " with
  | k :: _ => k
  | [] => body

/-- Count each kind, in order of first occurrence. -/
def countKinds (vs : List String) : List (String × Nat) :=
  vs.foldl (fun acc v =>
    let k := kindOf v
    if acc.any (·.1 == k) then acc.map (fun (k', n) => if k' == k then (k', n + 1) else (k', n))
    else acc ++ [(k, 1)]) []

def readGraph (path : String) : IO (Except String Graph) := do
  try
    let text ← IO.FS.readFile path
    match parseNQuadsFast text with
    | .ok ds => pure (.ok ds.default)
    | .error e => pure (.error s!"{path}: parse error at {e.pos}: {e.msg}")
  catch e => pure (.error s!"{path}: {e}")

open L4Factoidal.OWL.SyntaxDL in
/-- `--phases DOC.nt`: the wall time of each part of `speciesViolations` on
one document (no imports), in the order the function computes them, with the
number of violations of each part. Each part's result is forced between its
two clock reads by writing its length to an `IO.Ref`
(`skills/measuring-inference` § 9 and § 11); the last line is the whole
function, timed on its own, whose count the parts must add up to. Measurement
only: every part is a library function, called as `speciesViolations` and
`graphBodyViolations` call it. -/
def phasesMain (doc : String) : IO UInt32 := do
  match ← readGraph doc with
  | .error e => IO.eprintln e; pure 2
  | .ok g0 =>
    let sink ← IO.mkRef (0 : Nat)
    let err ← IO.getStderr
    let t00 ← IO.monoNanosNow
    let timed := fun (name : String) (f : Unit → Nat) => do
      let t0 ← IO.monoNanosNow
      let n := f ()
      sink.set n
      let t1 ← IO.monoNanosNow
      err.putStrLn s!"part={name} count={n} ms={(t1 - t0) / 1000000}"
      pure n
    let mut parts := 0
    parts := parts + (← timed "header" (fun _ => (docHeaderViolations g0).length))
    let g := dropTable5Redundant g0
    let _ ← timed "table5" (fun _ => g.length)
    let d := buildDeclIndex g
    let _ ← timed "declindex" (fun _ => d.cls.length + d.restr.length + d.datatype.length +
      d.objProp.length + d.dataProp.length + d.annProp.length + d.charProp.length +
      d.hasDR.length + d.inv.length + d.annSubj.length)
    parts := parts + (← timed "per-triple" (fun _ => (g.flatMap (tripleViolations g d)).length))
    parts := parts + (← timed "punning" (fun _ => (punningViolations d).length))
    let ns := nonsimpleKeys g
    let _ ← timed "nonsimple-keys" (fun _ => ns.length)
    parts := parts + (← timed "top-data" (fun _ => (topDataViolations g).length))
    parts := parts + (← timed "datatype-definitions" (fun _ => (datatypeDefinitionViolations g d).length))
    parts := parts + (← timed "simple-roles" (fun _ => (simpleRoleViolations g ns).length))
    parts := parts + (← timed "regularity" (fun _ => (regularityViolations g).length))
    parts := parts + (← timed "anonymous-individuals" (fun _ => (anonymousIndividualViolations g d).length))
    parts := parts + (← timed "unresolved-imports" (fun _ =>
      (unresolvedImportViolations (some (ontologyIris g0)) (rootOntologyKeys g0) g0).length))
    let t01 ← IO.monoNanosNow
    err.putStrLn s!"part=sum-of-parts count={parts} ms={(t01 - t00) / 1000000}"
    let _ ← timed "whole" (fun _ =>
      (speciesViolations g0 g0 false [] g0 (some (ontologyIris g0))).length)
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4owl-species DOC.nt [IMPORTED.nt ...] | l4owl-species --phases DOC.nt"
      pure 2
  | ["--phases", doc] => phasesMain doc
  | doc :: imports =>
    match ← readGraph doc with
    | .error e => IO.eprintln e; pure 2
    | .ok pDoc =>
      let mut merged : Graph := pDoc
      let mut available : List String := []
      let mut ord := 0
      for f in imports do
        ord := ord + 1
        match ← readGraph f with
        | .error e => IO.eprintln e; return 2
        | .ok g =>
            merged := merged ++ g.prefixBnodes s!"imp{ord}_"
            available := available ++ ontologyIris g
      let viols :=
        L4Factoidal.OWL.SyntaxDL.speciesViolations pDoc merged false [] merged (some available)
      let isDl := viols.isEmpty
      let out := Json.object
        [ ("document", Json.string doc)
        , ("imports", Json.array (imports.map Json.string))
        , ("triples_document", Json.number (toString pDoc.length))
        , ("triples_merged", Json.number (toString merged.length))
        , ("species", Json.string (if isDl then "DL" else "FULL"))
        , ("violations", Json.number (toString viols.length))
        , ("kinds", Json.object ((countKinds viols).map (fun (k, n) => (k, Json.number (toString n)))))
        , ("examples", Json.array ((viols.take 10).map Json.string)) ]
      IO.println out.toString
      pure (if isDl then 0 else 1)

end OwlSpeciesFile

def main (args : List String) : IO UInt32 := OwlSpeciesFile.main args
