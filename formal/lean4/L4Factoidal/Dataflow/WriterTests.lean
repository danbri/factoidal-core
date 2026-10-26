/-
L4Factoidal.Dataflow.WriterTests — checks of `Dataflow/Writer.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, item 2,
the writer kind).

1. The table: `writers` has one writer for each syntax (`writers_fmt`); with
   the default options its text is `Sink.serializeDataset`'s.
2. The bases: the N-Triples and N-Quads writers are proved in both modes; the
   five others are assumed, each under its own name. The list of assumed
   writers is pinned (`assumedWriters`, `assumedWriters12`): it may only shrink.
3. Round trips through the table, on datasets read from text: the text of each
   writer is read by the matching reader of `readers`, and the result is
   isomorphic (`Dataset.isomorphic?`) to the writer's projection.
4. The writer-side checks of issue 986 hold through the table: a blank-node
   label outside BLANK_NODE_LABEL is relabelled, a language tag outside LANGTAG
   is an error that names it.
5. Turtle options reach the text: a caller prefix is declared.
6. The canonical N-Quads writer writes `Dataset.toCanonicalNQuads` of the
   relabelled dataset.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Writer
import L4Factoidal.Dataflow.PhaseC
import L4Factoidal.Testing.Gen

namespace L4Factoidal.Dataflow.WriterTests

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.Syntax
open L4Factoidal.Testing
open L4Factoidal.Dataflow

/-- The datasets of the tests, read from text. -/
private def ds! (fmt : RdfFormat) (text : String) : Dataset :=
  match parseDocument Source.withJsonLd fmt .rdf12 none text with
  | .ok d => d
  | .error _ => Dataset.empty

private def sample : Dataset := ds! .trig
  "@prefix ex: <http://example.org/> .
   ex:s ex:p \"a\\\"b\\nc\" , \"x\"@en-GB , 42 , ex:o , _:b1 .
   _:b1 ex:q ex:s .
   ex:g1 { ex:s2 ex:p ex:o2 . _:b1 ex:r \"v\" . }
   ex:g2 { ex:s3 ex:p ex:o3 . }"

private def sx := Sink.withJsonLd
private def rx := Source.withJsonLd

/-! ## 1. The table -/

#guard allFormats.all fun f => (writers sx rx f).fmt == f
#guard allFormats.all fun f =>
  (writers sx rx f).run .rdf12 {} sample == Sink.serializeDataset sx f .rdf12 sample
#guard allFormats.all fun f =>
  (writers sx rx f).run .rdf11 {} sample == Sink.serializeDataset sx f .rdf11 sample

/-! ## 2. The bases -/

#guard (writers sx rx .nt).assumption? .rdf11 == none
#guard (writers sx rx .nt).assumption? .rdf12 == none
#guard (writers sx rx .nquads).assumption? .rdf11 == none
#guard (writers sx rx .nquads).assumption? .rdf12 == none

/- The assumptions the writers carry, pinned. A change here is a change of
the ratchet: it may only shrink. -/
#guard assumedWriters ==
  [(.turtle, ``TurtleWriterRoundTrip), (.trig, ``TrigWriterRoundTrip),
   (.rdfxml, ``RdfXmlWriterRoundTrip), (.jsonld, ``JsonLdWriterRoundTrip),
   (.nquads, ``CanonicalNQuadsWriterRoundTrip)]
#guard assumedWriters12 == assumedWriters

/- The table does not depend on the libraries linked in for the base. -/
#guard (assumedWritersIn .rdf11).length == 5

/-! ## 3. Round trips through the table -/

/-- Write with the table, read with the matching reader of the table. `none`:
the writer refused the dataset. -/
private def roundTrip (sx : Sink.Extra) (rx : Source.Extra) (fmt : RdfFormat) (v : Syntax.Mode)
    (ds : Dataset) : Option Bool :=
  let w := writers sx rx fmt
  match w.run v {} ds with
  | .error _ => none
  | .ok text =>
    match (readers rx fmt).dataset { text, mode := v } with
    | .error _ => some false
    | .ok back => some (Dataset.isomorphic? back (w.projection ds).toSet)

private def triplesOnly : Dataset := ds! .turtle
  "@prefix ex: <http://example.org/> .
   ex:s ex:p \"lit\"@en , 1.5 , ex:o , [ ex:q ex:r ] ."

#guard allFormats.all fun f => roundTrip sx rx f .rdf11 sample == some true
#guard allFormats.all fun f => roundTrip sx rx f .rdf12 sample == some true
#guard allFormats.all fun f => roundTrip sx rx f .rdf11 triplesOnly == some true
#guard allFormats.all fun f => roundTrip sx rx f .rdf12 triplesOnly == some true

/- The empty dataset round trips in every syntax. -/
#guard allFormats.all fun f => roundTrip sx rx f .rdf12 Dataset.empty == some true

/- A triple term: RDF/XML and JSON-LD refuse it (outside their domains), the
others keep it. -/
private def withTripleTerm : Dataset := ds! .nquads
  "<http://e/s> <http://e/p> <<( <http://e/a> <http://e/b> \"c\" )>> .\n"

#guard roundTrip sx rx .nt .rdf12 withTripleTerm == some true
#guard roundTrip sx rx .nquads .rdf12 withTripleTerm == some true
#guard roundTrip sx rx .turtle .rdf12 withTripleTerm == some true
#guard roundTrip sx rx .trig .rdf12 withTripleTerm == some true
#guard roundTrip sx rx .rdfxml .rdf12 withTripleTerm == none
#guard roundTrip sx rx .jsonld .rdf12 withTripleTerm == none
#guard (writerDomain .rdfxml withTripleTerm) == false
#guard (writerDomain .jsonld withTripleTerm) == false

/- The core build links no JSON-LD library: its JSON-LD writer refuses. -/
#guard ((writers {} {} .jsonld).run .rdf12 {} sample == .error "JSON-LD is not available in this build")

/-! ## 4. Issue 986 through the table -/

private def badLabel : Dataset :=
  { default := [{ s := .bnode "a b", p := mkIri "http://e/p", o := .iri (mkIri "http://e/o") }],
    named := [] }

private def badTag : Dataset :=
  { default := [{ s := .iri (mkIri "http://e/s"), p := mkIri "http://e/p",
                  o := .literal (Literal.langString "x" "en-abcdefghi") }], named := [] }

#guard (match (writers sx rx .nt).run .rdf12 {} badLabel with
  | .ok t => !(t.splitOn "a b").length != 1 && roundTrip sx rx .nt .rdf12 badLabel == some true
  | .error _ => false)
#guard (match (writers sx rx .turtle).run .rdf12 {} badLabel with
  | .ok t => (t.splitOn "a b").length == 1
  | .error _ => false)
#guard roundTrip sx rx .nquads .rdf12 badLabel == some true

/-! ## 5. Turtle options -/

#guard (match (writers sx rx .turtle).run .rdf12 { prefixes := [("http://example.org/", "zz:")] } sample with
  | .ok t => (t.splitOn "@prefix zz: <http://example.org/> .").length == 2
  | .error _ => false)
#guard (match (writers sx rx .turtle).run .rdf12 { prefixes := [("http://example.org/", "zz:")] } sample,
    (writers sx rx .turtle).run .rdf12 {} sample with
  | .ok a, .ok b => a != b
  | _, _ => false)
#guard (writers sx rx .turtle).run .rdf12 { literalShorthand := false } triplesOnly !=
  (writers sx rx .turtle).run .rdf12 {} triplesOnly

/-! ## 6. The canonical N-Quads writer -/

#guard (canonicalNQuadsRdfWriter sx rx).run .rdf12 {} sample ==
  .ok (Dataset.toCanonicalNQuads sample.relabelForWrite)
#guard (match (canonicalNQuadsRdfWriter sx rx).run .rdf12 {} badLabel with
  | .ok t => (t.splitOn "a b").length == 1
  | .error _ => false)
#guard (match (canonicalNQuadsRdfWriter sx rx).run .rdf12 {} badTag with
  | .error e => (e.splitOn "abcdefghi").length == 2
  | .ok _ => false)
#guard (canonicalNQuadsRdfWriter sx rx).run .rdf12 {} sample ==
  (match Sink.checkLangTags .rdf12 sample with
   | .error e => .error e
   | .ok () => .ok (Dataset.toCanonicalNQuads sample.relabelForWrite))

end L4Factoidal.Dataflow.WriterTests
