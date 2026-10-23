/-
L4Factoidal.RDF.NormalizeSetTests — executable checks of `RDF/NormalizeSet.lean`,
evaluated during `lake build`.

`Dataset.normalizeSet` is `normalizeDataset` for a dataset that is already a set
of quads (RDF 1.1 Concepts section 3 and 4): it lower-cases the language tags
(section 3.3) and leaves out the named graphs with no triple, and it does not
index the triples again. These guards compare it with `normalizeDataset` on
datasets that `Dataset.toSet` made, and compare `datasetForOpsSet` with
`datasetForOps` on a dataset that passes `roundTripSafe` and on one that does
not. A function that returned its input fails the guards on upper-case tags and
on empty named graphs. No executable imports this module.
-/
import L4Factoidal.RDF.NormalizeSet
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG

namespace L4Factoidal.RDF.NormalizeSetTests

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The structure of a dataset, for comparison: `Dataset` has no `BEq`. -/
private def shape (ds : Dataset) : Graph × List (Subject × Graph) :=
  (ds.default, ds.named.map fun ng => (ng.name, ng.graph))

private def rawTurtle (s : String) : Dataset :=
  match parseTurtle s none .rdf12 with
  | .ok g => { default := g, named := [] }
  | .error _ => Dataset.empty

private def rawTriG (s : String) : Dataset :=
  match parseTriG s none .rdf12 with
  | .ok ds => ds
  | .error _ => Dataset.empty

private def pre : String := "@prefix e: <http://e/> . "

-- The raw readings (a list may hold a triple two times) and their sets.
private def tagsRaw : Dataset :=
  rawTurtle (pre ++ "e:a e:p \"x\"@EN, \"y\"@En-Gb ; e:q \"z\"@en . e:b e:p \"x\"@EN . e:a e:p \"x\"@en .")
private def graphsRaw : Dataset :=
  rawTriG (pre ++ "e:a e:p \"v\" . e:g { e:a e:p \"x\"@EN } e:h { } e:k { e:b e:p e:c . e:b e:p \"w\" }")
-- A control character in a lexical form: `roundTripSafe` refuses it, so the text round trip runs.
private def controlRaw : Dataset :=
  rawTurtle (pre ++ "e:a e:p \"a\\u0001b\" . e:a e:p \"x\"@DE .")

private def tags : Dataset := tagsRaw.toSet
private def graphs : Dataset := graphsRaw.toSet
private def control : Dataset := controlRaw.toSet

-- The inputs are sets with the shapes the guards are about.
#guard tagsRaw.default.length == 5 && tags.default.length == 4
#guard graphs.named.length == 3 && graphs.named.any (·.graph.isEmpty)
#guard control.default.length == 2

-- A set is normalised as the dataset indexing does.
#guard shape (Dataset.normalizeSet tags) == shape (normalizeDataset tags)
#guard shape (Dataset.normalizeSet graphs) == shape (normalizeDataset graphs)
#guard shape (Dataset.normalizeSet Dataset.empty) == shape (normalizeDataset Dataset.empty)

-- The normalisation changes what it should: tags in lower case, the empty named graph gone.
#guard (Dataset.normalizeSet tags).default.map Triple.toCanonicalNTriples ==
  ["<http://e/a> <http://e/p> \"x\"@en .\n", "<http://e/a> <http://e/p> \"y\"@en-gb .\n",
   "<http://e/a> <http://e/q> \"z\"@en .\n", "<http://e/b> <http://e/p> \"x\"@en .\n"]
#guard (Dataset.normalizeSet tags).default.all fun t =>
  match t.o with
  | .literal l => l.val.langTag == l.val.langTag.map String.toLower
  | _ => true
#guard (Dataset.normalizeSet graphs).named.length == 2
#guard (Dataset.normalizeSet graphs).named.all (fun ng => !ng.graph.isEmpty)

-- `datasetForOpsSet` gives what `datasetForOps` gives, for a dataset that passes
-- `roundTripSafe` and for one that does not.
private def sameOps (mode : Mode) (ds : Dataset) (h : ds.IsSet) : Bool :=
  match datasetForOpsSet mode ds h, datasetForOps mode ds with
  | .ok a, .ok b => shape a == shape b
  | .error a, .error b => a.msg == b.msg && a.pos == b.pos
  | _, _ => false

#guard roundTripSafe .rdf12 tags && roundTripSafe .rdf12 graphs && !roundTripSafe .rdf12 control
#guard sameOps .rdf12 tagsRaw.toSet (Dataset.toSet_isSet _)
#guard sameOps .rdf12 graphsRaw.toSet (Dataset.toSet_isSet _)
#guard sameOps .rdf12 controlRaw.toSet (Dataset.toSet_isSet _)

end L4Factoidal.RDF.NormalizeSetTests
