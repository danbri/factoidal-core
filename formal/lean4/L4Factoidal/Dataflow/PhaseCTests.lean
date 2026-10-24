/-
L4Factoidal.Dataflow.PhaseCTests — checks of `Dataflow/PhaseC.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, phase C).

1. Writer round trips, property style: for seeded datasets (`genDataset`:
   a default graph, up to three named graphs, empty named graphs, a blank-node
   graph name, IRIs with a fragment, a percent sign and a non-ASCII letter,
   literals with quotes, line breaks, `<&>` and `]]>`, language tags differing
   only in case, directional language strings, and in RDF 1.2 mode triple
   terms), every writer's output parses back to a dataset isomorphic to the
   writer's projection (`writerRoundTripB`, `streamRoundTripB`). RDF/XML and
   JSON-LD refuse a triple term with an error (outside `writerDomain`).
   Finding: the JSON-LD writer drops the base direction of a directional
   language string with no error (https://github.com/danbri/factoidal/issues/984);
   that case is outside `writerDomain .jsonld` and a guard pins the loss.
   The RDF/XML writer had the same loss; it is fixed in this phase.
2. The projections: N-Quads drops an empty named graph; a triples-only writer
   writes the union of the graphs.
3. Readers: an RDF 1.2 triple term survives each RDF 1.2 reader with its blank
   nodes scoped; a syntax error is an error of the reader with the parser's
   message; two scopes give disjoint blank nodes.
4. Streaming: the streamed N-Quads read (RDF 1.1) of a document cut at every
   position gives the batch reader's dataset.

No executable imports this module.
-/
import L4Factoidal.Dataflow.PhaseC
import L4Factoidal.Testing.Gen

namespace L4Factoidal.Dataflow.PhaseCTests

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.Syntax
open L4Factoidal.Testing
open L4Factoidal.Dataflow

private def iriX (s : String) : WfIri := if h : isIri s then ⟨s, h⟩ else mkIri "fallback"

private def subjects : List Subject :=
  [.iri (mkIri "s1"), .iri (iriX "http://example.org/café"), .iri (iriX "urn:ex:a%20b"),
   .iri (iriX "http://example.org/a#frag"), .bnode "b1", .bnode "b2"]

private def preds : List WfIri :=
  [mkIri "p", iriX "http://example.org/ns#p1", iriX "http://purl.org/dc/terms/title",
   iriX "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"]

private def lits11 : List WfLiteral :=
  literals ++ [Literal.string "q\"uo\\te\nnl\ttab", Literal.string "é ünï 😀",
    Literal.string "", Literal.string "<a&b>]]>", Literal.string "  lead", Literal.langString "x" "en-GB"]

private def lits12 : List WfLiteral :=
  lits11 ++ [Literal.dirLangString "x" "en" .ltr, Literal.dirLangString "y" "ar" .rtl]

private def genSubj : Gen Subject := pick subjects (.bnode "b1")

private def genObj (v12 : Bool) : Gen Term := do
  match ← natLt 5 with
  | 0 => return (← genSubj).toTerm
  | 1 =>
    if v12 then
      let s ← genSubj
      let p ← pick preds (mkIri "p")
      let o ← pick lits12 (Literal.string "a")
      return .tripleTerm s p (.literal o)
    else return (← genSubj).toTerm
  | _ => return .literal (← pick (if v12 then lits12 else lits11) (Literal.string "a"))

private def genTr (v12 : Bool) : Gen Triple := do
  let s ← genSubj
  let p ← pick preds (mkIri "p")
  let o ← genObj v12
  return { s, p, o }

private def genG (v12 : Bool) : Gen Graph := do
  let n ← natLt 6
  let ts ← listOf (n + 1) (genTr v12)
  return ts.foldl (fun g t => g.add t) Graph.empty

private def graphNames : List Subject := [.iri (mkIri "g1"), .iri (mkIri "g2"), .bnode "gb"]

/-- A seeded dataset; one in three named graphs is empty. -/
def genDataset (v12 : Bool) : Gen Dataset := do
  let d ← genG v12
  let k ← natLt 4
  let mut named : List NamedGraph := []
  for i in List.range k do
    let nm := graphNames.getD i (.iri (mkIri "g1"))
    let empty ← natLt 3
    let g ← if empty == 0 then pure [] else genG v12
    named := named ++ [{ name := nm, graph := g }]
  return { default := d, named }

private def seeds : List Nat := List.range 30

private def cases (v12 : Bool) : List Dataset := seeds.map fun s => (genDataset v12).runSeed s

/-- Every case in the writer's domain is written and round trips (`some true`).
The cases outside the domain are checked by the guards after these. -/
private def allRoundTrip (check : RdfFormat → Mode → Dataset → Option Bool) (fmt : RdfFormat)
    (v : Mode) (v12 : Bool) : Bool :=
  (cases v12).all fun ds => !writerDomain fmt ds || check fmt v ds == some true

/-- The domain is not empty on the cases: at least ten of them are in it. -/
private def domainCount (fmt : RdfFormat) (v12 : Bool) : Nat :=
  ((cases v12).filter (writerDomain fmt)).length

/-! ## 1. Writer round trips -/

-- The generator is not vacuous: empty named graphs, blank-node graph names,
-- and triple terms occur.
#guard (cases false).any fun ds => ds.named.any (·.graph.isEmpty)
#guard (cases false).any fun ds => ds.named.any (·.name == .bnode "gb")
#guard (cases true).any fun ds => (Sink.flatten ds).any fun t => Term.hasTripleTermB t.o
#guard (cases false).all fun ds => (Sink.flatten ds).length > 0

#guard [RdfFormat.nt, .nquads, .turtle, .trig, .rdfxml, .jsonld].all fun f =>
  domainCount f false ≥ 10 && domainCount f true ≥ 5
-- Out of the domain, RDF/XML and JSON-LD refuse every case with a triple term.
#guard (cases true).all fun ds =>
  !((Sink.flatten ds).any fun t => Term.hasTripleTermB t.o) ||
    (writerRoundTripB .rdfxml .rdf12 ds == none && writerRoundTripB .jsonld .rdf12 ds == none)

-- Batch writers, RDF 1.1.
#guard allRoundTrip writerRoundTripB .nt .rdf11 false
#guard allRoundTrip writerRoundTripB .nquads .rdf11 false
#guard allRoundTrip writerRoundTripB .turtle .rdf11 false
#guard allRoundTrip writerRoundTripB .trig .rdf11 false
#guard allRoundTrip writerRoundTripB .rdfxml .rdf11 false
#guard allRoundTrip writerRoundTripB .jsonld .rdf11 false
-- Batch writers, RDF 1.2 (triple terms, directional language strings).
#guard allRoundTrip writerRoundTripB .nt .rdf12 true
#guard allRoundTrip writerRoundTripB .nquads .rdf12 true
#guard allRoundTrip writerRoundTripB .turtle .rdf12 true
#guard allRoundTrip writerRoundTripB .trig .rdf12 true
#guard allRoundTrip writerRoundTripB .rdfxml .rdf12 true
#guard allRoundTrip writerRoundTripB .jsonld .rdf12 true
-- Stream writers.
#guard allRoundTrip streamRoundTripB .nt .rdf12 true
#guard allRoundTrip streamRoundTripB .nquads .rdf12 true
#guard allRoundTrip streamRoundTripB .turtle .rdf12 true
#guard allRoundTrip streamRoundTripB .trig .rdf12 true
#guard allRoundTrip streamRoundTripB .rdfxml .rdf11 false
#guard allRoundTrip streamRoundTripB .jsonld .rdf11 false
-- RDF/JSON (triples only): the union of the graphs.
#guard (cases false).all fun ds =>
  rdfJsonRoundTripB (({ default := Sink.flatten ds, named := [] } : Dataset).toSet).default == some true

-- RDF/XML and JSON-LD refuse a triple term with an error.
private def withTripleTerm : Dataset :=
  { default := [{ s := .iri (mkIri "s1"), p := mkIri "p",
                  o := .tripleTerm (.iri (mkIri "s2")) (mkIri "q") (.literal (Literal.string "a")) }],
    named := [] }
#guard writerRoundTripB .rdfxml .rdf12 withTripleTerm == none
#guard writerRoundTripB .jsonld .rdf12 withTripleTerm == none
#guard writerRoundTripB .trig .rdf12 withTripleTerm == some true

-- Directional language strings (RDF 1.2). RDF/XML keeps the base direction
-- (fixed in this phase). JSON-LD writes the literal WITHOUT its direction:
-- finding https://github.com/danbri/factoidal/issues/984. The case is outside
-- `writerDomain .jsonld`; this guard pins the loss and fails when it changes.
private def withDir : Dataset :=
  { default := [{ s := .iri (mkIri "s1"), p := mkIri "p", o := .literal (Literal.dirLangString "y" "ar" .rtl) }],
    named := [] }
#guard writerRoundTripB .rdfxml .rdf12 withDir == some true
#guard writerRoundTripB .turtle .rdf12 withDir == some true
#guard !writerDomain .jsonld withDir
#guard writerRoundTripB .jsonld .rdf12 withDir == some false

-- Blank-node labels outside BLANK_NODE_LABEL [141s] (https://github.com/danbri/factoidal/issues/986).
-- A blank-node label is local to its document (RDF 1.1 Concepts section 3.4), so the
-- N-Triples, N-Quads, Turtle and TriG writers write a fresh valid label for each label
-- outside the production: the same label for each occurrence, and a label that no other
-- blank node of the document has. A valid label is written as it is. The case is in the
-- writer domain, and the text parses back to an isomorphic dataset.
private def badLabel : Dataset :=
  { default := [{ s := .bnode "", p := mkIri "p", o := .iri (mkIri "s2") }], named := [] }
private def badLabels : Dataset :=
  { default := [{ s := .bnode "", p := mkIri "p", o := .bnode "a b" },
                { s := .bnode "a b", p := mkIri "p", o := .bnode "a." },
                { s := .bnode "b1", p := mkIri "q", o := .iri (mkIri "s2") },
                { s := .bnode "rrrr0", p := mkIri "q", o := .bnode "a:b" }],
    named := [{ name := .bnode "g 1", graph := [{ s := .bnode "a b", p := mkIri "p", o := .bnode "b1" }] },
              { name := .bnode "g1", graph := [{ s := .bnode "a.", p := mkIri "p", o := .bnode "g 1" }] }] }
private def badNested : Dataset :=
  { default := [{ s := .bnode "x y", p := mkIri "p",
                  o := .tripleTerm (.bnode "x y") (mkIri "q") (.tripleTerm (.bnode "") (mkIri "q") (.bnode "x y")) }],
    named := [] }
#guard writerDomain .nt badLabel && writerRoundTripB .nt .rdf11 badLabel == some true
#guard writerDomain .nt badLabels && writerDomain .nquads badLabels
#guard [RdfFormat.nt, .nquads, .turtle, .trig].all fun f => [Mode.rdf11, .rdf12].all fun v =>
  writerRoundTripB f v badLabels == some true && streamRoundTripB f v badLabels == some true
#guard [RdfFormat.nt, .nquads, .turtle, .trig].all fun f =>
  writerRoundTripB f .rdf12 badNested == some true && streamRoundTripB f .rdf12 badNested == some true
-- The text: the valid labels `b1` and `rrrr0` are kept; `a b` becomes a label longer than
-- every label of the document, the same at each of its occurrences.
#guard (Sink.serializeDataset Sink.withJsonLd .nt .rdf11
    { default := [{ s := .bnode "a b", p := mkIri "p", o := .bnode "b1" },
                  { s := .bnode "b1", p := mkIri "p", o := .bnode "a b" }], named := [] }).toOption ==
  some ("_:rrrr0 <" ++ (mkIri "p").val ++ "> _:b1 .\n_:b1 <" ++ (mkIri "p").val ++ "> _:rrrr0 .\n")
#guard (Sink.serializeDataset Sink.withJsonLd .nquads .rdf11
    { default := [], named := [{ name := .bnode "g 1", graph := [{ s := .bnode "b1", p := mkIri "p", o := .iri (mkIri "s2") }] }] }).toOption ==
  some ("_:b1 <" ++ (mkIri "p").val ++ "> <" ++ (mkIri "s2").val ++ "> _:rrrr0 .\n")

-- Language tags outside LANGTAG [144s] (RDF 1.2 mode: also a subtag of 1 to 8 characters,
-- BCP 47 section 2.1). A tag has no valid rewrite, so every writer of the N-Triples family
-- refuses the dataset with an error that names the tag. The case stays outside the domain.
private def tagged (tag : String) : Dataset :=
  { default := [{ s := .iri (mkIri "s1"), p := mkIri "p", o := .literal (Literal.langString "x" tag) }],
    named := [] }
private def badTag : Dataset := tagged "en US"
private def namesTag (tag : String) : Except String String → Bool
  | .error e => (e.splitOn ("\"" ++ tag ++ "\"")).length > 1
  | .ok _ => false
#guard !writerDomain .nt badTag
#guard ["en US", "", "en-", "en--x", "-en", "e\nn", "1a"].all fun tag =>
  [RdfFormat.nt, .nquads, .turtle, .trig].all fun f => [Mode.rdf11, .rdf12].all fun v =>
    namesTag tag (Sink.serializeDataset Sink.withJsonLd f v (tagged tag)) &&
      namesTag tag (Sink.streamDataset Sink.withJsonLd f { version := v, graphs := .union } (tagged tag))
-- A subtag of nine characters: RDF 1.1 mode writes it (the RDF 1.1 reader keeps it); RDF 1.2
-- mode refuses it.
#guard [RdfFormat.nt, .nquads, .turtle, .trig].all fun f =>
  writerRoundTripB f .rdf11 (tagged "abcdefghi") == some true &&
    namesTag "abcdefghi" (Sink.serializeDataset Sink.withJsonLd f .rdf12 (tagged "abcdefghi"))
#guard [RdfFormat.nt, .nquads, .turtle, .trig].all fun f => [Mode.rdf11, .rdf12].all fun v =>
  writerRoundTripB f v (tagged "en-GB-oxendict") == some true

/-! ## 2. Projections -/

private def oneEmpty : Dataset :=
  { default := [{ s := .iri (mkIri "s1"), p := mkIri "p", o := .iri (mkIri "s2") }],
    named := [{ name := .iri (mkIri "g1"), graph := [] },
              { name := .iri (mkIri "g2"), graph := [{ s := .bnode "b1", p := mkIri "q", o := .iri (mkIri "s3") }] }] }

#guard (writerProjection .nquads oneEmpty).names == [.iri (mkIri "g2")]
#guard (writerProjection .trig oneEmpty).names == oneEmpty.names
#guard (writerProjection .nt oneEmpty).names == []
#guard (writerProjection .nt oneEmpty).default.length == 2
-- N-Quads loses the empty named graph; TriG keeps it.
#guard match Sink.serializeDataset Sink.withJsonLd .nquads .rdf11 oneEmpty with
  | .ok t => (match parseDocument Source.withJsonLd .nquads .rdf11 none t with
    | .ok b => b.names == [.iri (mkIri "g2")] | .error _ => false)
  | .error _ => false
#guard match Sink.serializeDataset Sink.withJsonLd .trig .rdf11 oneEmpty with
  | .ok t => (match parseDocument Source.withJsonLd .trig .rdf11 none t with
    | .ok b => b.names.length == 2 | .error _ => false)
  | .error _ => false
-- The empty dataset.
#guard [RdfFormat.nt, .nquads, .turtle, .trig, .rdfxml, .jsonld].all fun f =>
  writerRoundTripB f .rdf11 Dataset.empty == some true

/-! ## 3. Readers -/

private def okVal? {β : Type} : Except String β → Option β
  | .ok b => some b
  | .error _ => none

private def hasTT (ds : Dataset) : Bool := (Sink.flatten ds).any fun t => Term.hasTripleTermB t.o

private def bnodesScoped (n : Nat) (ds : Dataset) : Bool :=
  ds.bnodes.all fun b => b.startsWith (docScope n)

#guard match okVal? ((ntriplesReader .rdf12 3).run
    "_:x <http://e/p> <<( _:y <http://e/q> \"v\"@en--ltr )>> .\n") with
  | some ds => hasTT ds && bnodesScoped 3 ds && ds.bnodes.length == 2
  | none => false
#guard match okVal? ((nquadsReader .rdf12 3).run
    "_:x <http://e/p> <<( _:y <http://e/q> <http://e/o> )>> _:g .\n") with
  | some ds => hasTT ds && bnodesScoped 3 ds && ds.names == [.bnode (docLabel 3 "g")]
  | none => false
#guard match okVal? ((turtleReader .rdf12 none 4).run
    "<http://e/s> <http://e/p> <<( _:y <http://e/q> 1 )>> .") with
  | some ds => hasTT ds && bnodesScoped 4 ds
  | none => false
#guard match okVal? ((trigReader .rdf12 none 4).run
    "<http://e/g> { <http://e/s> <http://e/p> <<( _:y <http://e/q> 1 )>> . }") with
  | some ds => hasTT ds && bnodesScoped 4 ds && ds.names.length == 1
  | none => false
#guard match okVal? ((jsonldReader .rdf11 none 5).run
    "{\"@id\":\"_:a\",\"http://e/p\":{\"@id\":\"_:b\"}}") with
  | some ds => bnodesScoped 5 ds && ds.bnodes.length == 2
  | none => false
#guard match okVal? ((rdfxmlReader .rdf11 none 6).run
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\"><rdf:Description rdf:nodeID=\"a\"><e:p>v</e:p></rdf:Description></rdf:RDF>") with
  | some ds => bnodesScoped 6 ds && (Sink.flatten ds).length == 1
  | none => false
#guard match okVal? ((rdfJsonReader 7).run
    "{\"_:a\":{\"http://e/p\":[{\"type\":\"bnode\",\"value\":\"_:b\"}]}}") with
  | some ds => bnodesScoped 7 ds && ds.bnodes.length == 2
  | none => false
-- A repeated triple is one quad (the set contract).
#guard match okVal? ((ntriplesReader .rdf11 0).run
    "<http://e/s> <http://e/p> \"x\" .\n<http://e/s> <http://e/p> \"x\" .\n") with
  | some ds => ds.default.length == 1
  | none => false
-- An error of the parser is an error of the reader, with the parser's message.
#guard match (ntriplesReader .rdf11 0).run "<http://e/s> <http://e/p> .\n",
    parseDocumentRaw {} .nt .rdf11 none "<http://e/s> <http://e/p> .\n" with
  | .error m, .error e => m == e.msg
  | _, _ => false
#guard match (turtleReader .rdf11 none 0).run "<http://e/s> <http://e/p> " with
  | .error _ => true
  | .ok _ => false
-- RDF 1.1 mode refuses a triple term.
#guard match (ntriplesReader .rdf11 0).run "<http://e/s> <http://e/p> <<( <http://e/a> <http://e/b> <http://e/c> )>> .\n" with
  | .error _ => true
  | .ok _ => false
-- Two scopes: no shared blank node.
#guard match okVal? ((ntriplesReader .rdf11 1).run "_:a <http://e/p> _:b .\n"),
    okVal? ((ntriplesReader .rdf11 2).run "_:a <http://e/p> _:b .\n") with
  | some a, some c => a.bnodes.all fun b => !c.bnodes.contains b
  | _, _ => false

/-! ## 4. Streaming -/

private def nqDoc : String :=
  "_:a <http://e/p> \"x\\ny\" <http://e/g> .\n<http://e/s> <http://e/p> _:a .\n<http://e/s> <http://e/p> _:a .\n"

#guard (List.range (nqDoc.length + 1)).all fun i =>
  let chunks := [(nqDoc.take i).toString, (nqDoc.drop i).toString]
  match nquads11StreamStage.run chunks, (nquadsReader .rdf11 0).run nqDoc with
  | .ok out, .ok batch => out.scopeDocument 0 == batch
  | _, _ => false

#guard (streamSetStage.run [[{ s := .iri (mkIri "s1"), p := mkIri "p", o := .iri (mkIri "s2") }],
    [{ s := .iri (mkIri "s1"), p := mkIri "p", o := .iri (mkIri "s2") }]]).toOption.map List.length == some 1

end L4Factoidal.Dataflow.PhaseCTests
