/-
L4Factoidal.SPARQL.ConstructLabelTests — CONSTRUCT template blank nodes get
N-Triples blank node labels (https://github.com/danbri/factoidal/issues/742).

SPARQL 1.1 §16.2.1: a template blank node is a new blank node for each
solution, and two template blank nodes are two blank nodes. The labels
`freshBnodeFor` gives them must also be RDF 1.1 N-Triples [141s]
BLANK_NODE_LABELs (`isBlankNodeLabel`), so the CONSTRUCT output written as
N-Triples parses back. Before issue 742 a blank node the parser made for a
collection or `[ ]` got `tpl_0__:bnode_13`, which N-Triples rejects at the `:`.

Each template below is parsed by the SPARQL parser and evaluated over a
four-triple graph (the data of W3C `construct/data.ttl`). For each one the
guards check: every output label passes `isBlankNodeLabel`; the N-Triples text
of the output parses back to the same number of triples; and the expected
number of distinct labels is present (one per solution and template blank node).
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.BlankNodeLabel

namespace L4Factoidal.SPARQL.ConstructLabelTests

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Syntax

/-- W3C `construct/data.ttl`: four triples, so four solutions of `?s ?p ?o`. -/
def dataNt : String :=
  "<http://example.org/s1> <http://example.org/p> <http://example.org/o1> .\n" ++
  "<http://example.org/s2> <http://example.org/p> <http://example.org/o1> .\n" ++
  "<http://example.org/s2> <http://example.org/p> <http://example.org/o2> .\n" ++
  "<http://example.org/s3> <http://example.org/p> <http://example.org/o3> .\n"

def dataset : Dataset :=
  match parseNTriples dataNt with
  | .ok g => { default := g, named := [] }
  | .error _ => { default := [], named := [] }

/-- The CONSTRUCT graph of `q` over `dataset`, or `none` when `q` does not parse. -/
def constructOf (q : String) : Option Graph :=
  match parseSparql q with
  | .ok query => some (evalConstruct {} dataset query)
  | .error _ => none

def termLabels : Term → List String
  | .bnode b => [b]
  | .tripleTerm s _ o =>
      (match s with | .bnode b => [b] | _ => []) ++ termLabels o
  | _ => []

/-- Every blank node label in `g`, with repeats. -/
def graphLabels (g : Graph) : List String :=
  g.flatMap fun t => (match t.s with | .bnode b => [b] | _ => []) ++ termLabels t.o

def distinctCount (xs : List String) : Nat := xs.eraseDups.length

/-- The checks for one template: (triples, distinct labels, every label valid,
the N-Triples text parses back to the same triple count). -/
def check (q : String) : Option (Nat × Nat × Bool × Bool) :=
  (constructOf q).map fun g =>
    let ls := graphLabels g
    let back := match Graph.toNTriples g with
      | .ok text => match parseNTriples text with
          | .ok g' => g'.length == g.length
          | .error _ => false
      | .error _ => false
    (g.length, distinctCount ls, ls.all isBlankNodeLabel, back)

-- W3C construct/constructlist.rq: a two-element collection in the template.
-- 4 solutions x 5 triples; 2 list cells per solution, so 8 labels.
#guard check "PREFIX : <http://example.org/> CONSTRUCT { (?s ?o) :prop ?p } WHERE { ?s ?p ?o }"
  == some (20, 8, true, true)
-- `[ ]` in the template: one new node per solution.
#guard check "PREFIX : <http://example.org/> CONSTRUCT { [ :q ?o ] :r ?s } WHERE { ?s ?p ?o }"
  == some (8, 4, true, true)
-- A label the query wrote: one node per solution, used by both triples.
#guard check "PREFIX : <http://example.org/> CONSTRUCT { _:b :q ?o . _:b :r ?s } WHERE { ?s ?p ?o }"
  == some (8, 4, true, true)
-- A nested collection with a `[ ]` inside it: the outer list has 3 cells, the
-- inner one 2, and the `[ ]` 1, so 6 new nodes per solution.
#guard check ("PREFIX : <http://example.org/> " ++
    "CONSTRUCT { ?s :q ( 1 ( 2 3 ) [ :r ?o ] ) } WHERE { ?s ?p ?o }")
  == some (4 * 12, 24, true, true)
-- A written label next to a collection: the two kinds stay apart.
#guard check ("PREFIX : <http://example.org/> " ++
    "CONSTRUCT { _:bnode_5 :q ( ?o ) } WHERE { ?s ?p ?o }")
  == some (12, 8, true, true)
-- An RDF 1.2 annotation with a template reifier blank node (SPARQL 1.2).
#guard (match parseSparql ("PREFIX : <http://example.org/> " ++
    "CONSTRUCT { ?s :q ?o {| :src [ :at ?p ] |} } WHERE { ?s ?p ?o }") none .v12 with
  | .ok query =>
      let g := evalConstruct {} dataset query
      (graphLabels g).all isBlankNodeLabel && !(graphLabels g).isEmpty
  | .error _ => false)

-- A collection cell and a `[ ]` element in it are two nodes (SPARQL 1.1
-- §4.1.4): the cell's `rdf:first` is the `[ ]` node, never the cell itself.
#guard (constructOf ("PREFIX : <http://example.org/> " ++
    "CONSTRUCT { ?s :q ( [ :r ?o ] ) } WHERE { ?s ?p ?o }")).map (fun g =>
      g.all fun t => match t.s, t.o with
        | .bnode a, .bnode b => a != b
        | _, _ => true) == some true
-- The same in a WHERE pattern: a list whose element is a blank node matches.
#guard (match parseNTriples ("<http://e/s> <http://e/q> _:c .\n" ++
      "_:c <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:e .\n" ++
      "_:c <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n" ++
      "_:e <http://e/r> <http://e/o> .\n"), parseSparql "SELECT ?o WHERE { ?s <http://e/q> ( [ <http://e/r> ?o ] ) }" with
  | .ok g, .ok q => (evalSelect {} { default := g, named := [] } q).2.length == 1
  | _, _ => false)

-- The label map: distinct per solution and per template label (§16.2.1),
-- and the generated and written kinds never meet.
#guard freshBnodeFor 0 "b" == "tpl_0_b"
#guard freshBnodeFor 0 "_:bnode_13" == "tpl_0g_bnode_13"
#guard freshBnodeFor 0 "bnode_13" != freshBnodeFor 0 "_:bnode_13"
#guard freshBnodeFor 1 "2_x" != freshBnodeFor 12 "_x"
#guard freshBnodeFor 0 "b" != freshBnodeFor 1 "b"
#guard isBlankNodeLabel (freshBnodeFor 7 "_:bnode_42")
-- Negative: the check rejects the label the generator made before the fix.
#guard !isBlankNodeLabel ("tpl_0_" ++ "_:bnode_13")

end L4Factoidal.SPARQL.ConstructLabelTests
