/-
Harness.OwlSpeciesFile — the OWL 2 species verdict (DL or Full) of one
ontology document given as N-Triples or N-Quads, with its imported
documents.

    l4owl-species DOC.nt [IMPORTED.nt ...]

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

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4owl-species DOC.nt [IMPORTED.nt ...]"
      pure 2
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
