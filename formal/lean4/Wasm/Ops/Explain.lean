/-
Wasm.Ops.Explain — the `explainGraph` op: is a description (a graph, with
shared blank nodes) RDFS-entailed by the sources, and the evidence
(https://github.com/danbri/factoidal/issues/1002, first step).

  explainGraph(sourcesNQuads, descriptionNQuads)
    -> {"ok":true,"profile":"rdfs","entailed":B,
        "bundle":null|{"sources":NT,"description":NT,
                       "mapping":[{"bnode":L,"term":T}],
                       "steps":[{"rule":R,"conclusion":NT,"premises":[N]}],
                       "support":[N]},
        "assumptions":[S],
        "rejection":null|{"kind":"noMatch","index":N,"triple":NT}
                        |{"kind":"noJointMapping"}
                        |{"kind":"checkerRefused","reason":S},
        "entailedMeans":S}
     | {"ok":false,"error":S}

The op reads both texts with the N-Quads reader of the reader table
(`readNQuadsText`), scopes the blank nodes of each document by its own scope
number (`Dataset.scopeDocument`: sources 0, description 1; RDF 1.1 Concepts
section 3.4), selects the default graph and every named graph of the sources,
takes the default graph of the description (a description with a named graph
is refused), and returns `explainGraphOf (withMinimalD []) …` — the run of
`Dataflow.rdfsExplainGraphStage` — encoded. Blank-node labels in the output
carry the scope prefix (`d0_`, `d1_`).

`entailed = true` is worth what `Dataflow.explainGraphOf_spec` says: the
graph checker (`Dataflow.rdfsGraphChecker`) accepted `bundle`, so the sources
RDFS-entail the description. `entailed = false` with `noMatch` or
`noJointMapping` says that no instance of the description is in the RDFS
closure (proved); "not entailed" also needs the named assumption in
`assumptions`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Dataflow.ExplainGraph
import L4Factoidal.RDF.Datatypes
import L4Factoidal.Syntax.NTriples

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.Syntax
open L4Factoidal.JSON
open L4Factoidal.Dataflow

private def ntOfGraph (g : Graph) : Json := .string (Graph.toCanonicalNTriples g)

private def natJson (n : Nat) : Json := .number (toString n)

/-- The JSON form of a graph bundle. -/
def encodeGraphBundle (b : GraphBundle) : Json :=
  .object
    [ ("sources", ntOfGraph b.sources),
      ("description", ntOfGraph b.description),
      ("mapping", .array (b.mapping.map (fun p =>
        .object [("bnode", .string p.1), ("term", .string (Term.toCanonicalNTriples p.2))]))),
      ("steps", .array (b.witness.toList.map (fun st =>
        .object [("rule", .string st.rule.name),
                 ("conclusion", .string (Triple.toCanonicalNTriples st.conclusion)),
                 ("premises", .array (st.premises.map natJson))]))),
      ("support", .array (b.support.map natJson)) ]

/-- The JSON form of a rejection. -/
def encodeGraphRejection : GraphRejection → Json
  | .noMatch i t => .object [("kind", .string "noMatch"), ("index", natJson i),
      ("triple", .string (Triple.toCanonicalNTriples t))]
  | .noJointMapping => .object [("kind", .string "noJointMapping")]
  | .checkerRefused r => .object [("kind", .string "checkerRefused"), ("reason", .string r)]

/-- The envelope of an explain result. -/
def explainGraphEnvelope (r : ExplainGraphResult) : String :=
  okWith
    [ ("profile", .string "rdfs"),
      ("entailed", .bool r.entailed),
      ("bundle", match r.bundle with | some b => encodeGraphBundle b | none => .null),
      ("assumptions", .array (r.assumptions.map Json.string)),
      ("rejection", match r.rejection with | some w => encodeGraphRejection w | none => .null),
      ("entailedMeans", .string "true: the graph checker accepted the bundle, so the sources RDFS-entail the description (Dataflow.explainGraphOf_spec); false with noMatch or noJointMapping: no instance of the description is in the RDFS closure, and not entailed under the listed assumptions") ]

/-- Explain over already-parsed sources and description. -/
def explainGraphParsed (src desc : Dataset) : String :=
  if !desc.named.isEmpty then
    errJson "explainGraph: the description must be a default graph (no named graphs)"
  else
    let s := src.scopeDocument 0
    let d := desc.scopeDocument 1
    let sel : GraphSelection := { default := true, named := s.named.map (·.name) }
    explainGraphEnvelope ((rdfsExplainGraphStage (withMinimalD []) sel).run (s, d.default)
      |>.toOption |>.getD { entailed := false, bundle := none, assumptions := [], rejection := none })

/-- `explainGraph(sourcesNQuads, descriptionNQuads)`. -/
def explainGraph (srcText descText : String) : String :=
  match readNQuadsText .rdf12 srcText with
  | .error e => errJson ("explainGraph: sources: " ++ fmtParseError e)
  | .ok src =>
    match readNQuadsText .rdf12 descText with
    | .error e => errJson ("explainGraph: description: " ++ fmtParseError e)
    | .ok desc => explainGraphParsed src desc

/-! ## Checks -/

private def subOf (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def srcNq : String :=
  "<http://example.org/alice> <http://example.org/worksFor> <http://example.org/acme> .\n" ++
  "<http://example.org/worksFor> <http://www.w3.org/2000/01/rdf-schema#domain> <http://example.org/Employee> .\n" ++
  "<http://example.org/Employee> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Person> .\n"

private def descNq : String :=
  "_:x <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Person> .\n" ++
  "_:x <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Employee> .\n" ++
  "_:x <http://example.org/worksFor> <http://example.org/acme> .\n"

#guard subOf (explainGraph srcNq descNq) "\"entailed\":true"
#guard subOf (explainGraph srcNq descNq) "\"bnode\":\"d1_x\",\"term\":\"<http://example.org/alice>\""
#guard subOf (explainGraph srcNq descNq) "\"rejection\":null"
#guard subOf (explainGraph srcNq
    "_:x <http://example.org/worksFor> <http://example.org/globex> .\n") "\"kind\":\"noMatch\""
#guard subOf (explainGraph srcNq
    "_:x <http://example.org/worksFor> <http://example.org/globex> .\n") "\"entailed\":false"
#guard subOf (explainGraph srcNq "<http://e/a> <http://e/b> <http://e/c> <http://e/g> .\n")
  "the description must be a default graph"
#guard subOf (explainGraph "not n-quads" descNq) "explainGraph: sources:"

end L4Wasm.Ops
