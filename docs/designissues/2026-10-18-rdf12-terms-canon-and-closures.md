# RDF 1.2 triple terms in canonicalisation and the reasoning ops

Date: 2026-10-18. Issue: https://github.com/danbri/factoidal/issues/873.

## The defect

The Lean wasm and command-line ops `canonicalizeToNQuads`, `owlClosure`,
`rhoDfClosure`, `rdfsPlusClosure`, `owlIsConsistent`, `owlEntails` (and the
verbs `canonicalize`, `closure`, `owl-consistent`, `owl-entails`) read their
input in RDF 1.1 mode (`parseNQuadsFast nq`, default `.rdf11`). A dataset with
an RDF 1.2 triple term gave "invalid character in IRIREF (offset N)".

The library closures (`RDFS.closureFix`, `RDFS.fullClosure`,
`RDFS.rdfsPlusClosureFix`, `OWL.RL.closureFix`) are defined over
`L4Factoidal.RDF.Term`, which has had the constructor `tripleTerm` since the
RDF 1.2 port. No rule of these closures matches that constructor. Only the
ops' reader mode refused the input.

## RDFS and OWL 2 RL closures: accepted

Specification:

- RDF 1.2 Concepts, section "Triple Terms": a triple term is an RDF term that can
  be the object of a triple.
- RDF 1.2 Semantics, section "Simple Interpretations": a triple term denotes a
  proposition. A triple term is not asserted: the graph
  `ex:a ex:says <<( ex:s rdf:type ex:C )>>` does not entail
  `ex:s rdf:type ex:C` (W3C rdf12 rdf-semantics test
  `triple-term-not-asserted`).
- The entailment patterns of RDF 1.2 Semantics §8 (RDF) and §9 (RDFS), and
  the OWL 2 RL rules (OWL 2 Profiles §4.3), match asserted triples. A triple
  term matches a rule variable in object position as one term.

Rule implemented: the ops read RDF 1.2 N-Quads and write RDF 1.2 N-Triples
(`Wasm/Ops/Reason.lean`, `Wasm/Cli.lean`). A triple term is an opaque object
term. The closure keeps every asserted triple, makes every derivation from
asserted triples, and derives nothing from the triple inside a triple term.

Tests:

- `L4Factoidal/RDFS/TripleTermClosureTests.lean`: `#guard`s over the four
  closures. Positive: the asserted triples with a triple term (IRI subject and
  blank-node subject inside) stay; `ex:x rdf:type ex:D` is derived. Negative:
  no `ex:s rdf:type ex:C`, `ex:s rdf:type ex:D`, `_:b1 rdf:type ex:C|D`, and
  no new triple term `<<( ex:s rdf:type ex:D )>>`.
- `Wasm/Ops/Reason.lean`: the same checks on the op envelopes.
- `npm/factoidal/test/rdf12-terms.test.js`, `Wasm/cli-smoke.sh`: the same on
  the wasm and on the command line.

On RDF 1.1 input the output text does not change: the RDF 1.2 reader gives
the same dataset for an RDF 1.1 document, and `Term.toNTriples` writes an
RDF 1.1 term with the same text in both modes (it differs only by refusing a
triple term or a directional literal under `.rdf11`).

Entailments that the closure ops do not compute:

- rdfs14 and rdfs14a (RDF 1.2 Semantics §9.2.1) replace a triple term with a
  new blank node typed `rdfs:Proposition`. The closures mint no blank nodes
  (`RDF/Entailment.lean`, `Regime.closure`); `RDF.regimeEntails` applies
  these patterns before the closure, on the graph-entailment path the W3C
  `rdf-semantics` suite runs.
- `owl:sameAs` substitution inside a triple term. RDF 1.2 Semantics makes the
  IRIs inside a triple term transparent, so `ex:clark owl:sameAs ex:superman`
  with `ex:clark ex:reports <<( ex:superman ex:can ex:fly )>>` entails
  `ex:clark ex:reports <<( ex:clark ex:can ex:fly )>>` (W3C test `opaque-iri`;
  the manifest lists it but leaves it out of its entries, "relies on
  non-standard entailment regime"). `RDF.regimeEntails .rdfsPlus` decides
  it. The OWL 2 RL closure applies the rule table of OWL 2 Profiles §4.3,
  whose eq-rep-o replaces a whole object term. Expected failure:
  `npm/factoidal/test/rdf12-terms.test.js`, issue 873.

## RDFC-1.0: refused, with the missing rule named

Specification: RDF Dataset Canonicalization (RDFC-1.0), W3C Recommendation,
21 May 2024. Its "Status of this document" names RDF 1.1 Concepts as the
data model and says an update will follow the RDF-star Working Group's
specifications. The hashing algorithms (§4.6 Hash First Degree Quads, §4.7
Hash Related Blank Node, §4.8 Hash N-Degree Quads) serialise quads whose
blank nodes are subject, object or graph name; they have no rule for a blank
node inside a triple term. The W3C test suite
(`third_party/testing/rdf-canon/tests/manifest.ttl`, 86 tests under
`rdfc10/`) has no test with a triple term.

Neither the specification nor the test suite defines the rule. The op
refuses a dataset with a triple term (or a directional language-tagged
string, also an RDF 1.2 term) with a message that names RDFC-1.0 §4.6 and
§4.8 and the issue (`Wasm/Ops/Canon.lean`, `canonRdf12Refusal`;
`L4Factoidal/RDF/Rdf11Terms.lean`, `Dataset.isRdf11`). The text is read in
RDF 1.2 mode so that the refusal replaces the parse error. Expected
failures: `npm/factoidal/test/rdf12-terms.test.js` and `Wasm/cli-smoke.sh`
("canonicalize labels blank nodes inside a triple term"). The W3C RDFC-1.0
suite score is unchanged (the harness calls `RDF.Canonical.canonicalize`).

When the W3C publishes a rule (an RDFC update, or rdf-canon tests with
triple terms), implement it and flip the expected failures.

## OWL 2 Direct Semantics checks: refused, with the missing rule named

`owlIsConsistent` and `owlEntails` give OWL 2 Direct Semantics verdicts. The
graph is read as an ontology by OWL 2 Mapping to RDF Graphs §3 (Mapping from
RDF Graphs to the Structural Specification), which is stated on RDF 1.1
graphs and has no rule for a triple term; the Direct Semantics has no
interpretation of one. The ops refuse such input with a message that names
the mapping and the issue (`Wasm/Ops/ReasonDl.lean`, `owlDlRdf12Refusal`).
Expected failures: `npm/factoidal/test/rdf12-terms.test.js`,
`Wasm/cli-smoke.sh`.

## Theorems

The closure soundness and fixpoint theorems are stated over `Term`, which
admits triple terms; they cover inputs with triple terms without change. The
op-level theorems `owlClosureOf_eq`, `rhoDfClosureOf_eq`,
`rdfsPlusClosureOf_eq`, `closureEnvelopeOf_stream`, `canonicalizeOf_eq`,
`owlIsConsistentOf_eq`, `owlEntailsOf_eq` are restated for mode `.rdf12`
and build.
