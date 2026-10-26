# RDF 1.2 triple terms in canonicalisation and the reasoning ops

Date: 2026-10-18. Issue: https://github.com/danbri/factoidal/issues/873.

## Rule per operation (status 2026-10-23)

| Operation | Input with a triple term | Rule | Tests |
|---|---|---|---|
| `owlClosure` mode `RDFS` | accepted | RDF 1.2 Semantics §9: opaque object term; RDFS axiomatic triples include `rdf:reifies rdfs:range rdfs:Proposition` | `RDFS/TripleTermClosureTests.lean`, `Wasm/Ops/Reason.lean`, npm `rdf12-terms.test.js`, `cli-smoke.sh` (W3C `reifies-range`, `triple-term-not-asserted`, `triple-terms-no-spurious`) |
| `owlClosure` mode `OWL-RL` | accepted | OWL 2 Profiles §4.3 rule table plus the `[ext]` row eq-rep-tt (RDF 1.2 Semantics: IRIs inside a triple term are transparent) | same, plus W3C `opaque-iri` |
| `rhoDfClosure` | accepted | ρdf rows (Muñoz, Pérez, Gutierrez, "Simple and efficient minimal RDFS", 2009; a subset of the RDFS patterns of RDF 1.2 Semantics §9) over asserted triples; opaque object term; no axiomatic triples; no `owl:sameAs` semantics | same (negative W3C cases) |
| `rdfsPlusClosure` | accepted | RDFS-Plus rows (Allemang and Hendler; `RDFS/RDFSPlus.lean`) over asserted triples, plus eq-rep-tt (since 2026-10-23; W3C `opaque-iri` has regime "RDFS-Plus") | same, plus W3C `opaque-iri` |
| CLI `closure` (`--regime rdfs`, `owl-rl`, `rho-df`, `rdfs-plus`) | accepted with `--format nquads12` / `turtle12` | as the op of that regime | `cli-smoke.sh` |
| `canonicalizeToNQuads` | refused, rule named | RDFC-1.0 (2024) §4.6, §4.8 define no label for a blank node inside a triple term | expected failure, https://github.com/danbri/factoidal/issues/957 |
| CLI `canonicalize` | refused, rule named | as above | expected failure, https://github.com/danbri/factoidal/issues/957 |
| `owlIsConsistent`, `owlEntails` (CLI `owl-consistent`, `owl-entails`) | refused, rule named | OWL 2 Mapping to RDF Graphs §3 has no rule for a triple term | expected failures, https://github.com/danbri/factoidal/issues/958 |

Issue https://github.com/danbri/factoidal/issues/873 tracked the first
step (every operation either accepts under a stated rule or refuses with the
rule named). The two refusals are tracked by issues 957 and 958 from
2026-10-23.

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

Entailments that the closure ops do not compute (a stated rule of the
closure ops, the same as for RDF 1.1 rdfD1):

- rdfs14 and rdfs14a (RDF 1.2 Semantics §9.2.1) replace a triple term with a
  new blank node typed `rdfs:Proposition`. The closures mint no blank nodes
  (`RDF/Entailment.lean`, `Regime.closure`); `RDF.regimeEntails` applies
  these patterns before the closure, on the graph-entailment path the W3C
  `rdf-semantics` suite runs.

## `owl:sameAs` inside a triple term in the OWL 2 RL closure (2026-10-19)

Decision: CLAUDE.md, "Triple-term transparency and the isomorphism row
(2026-10-19)". RDF 1.2 Semantics makes the IRIs inside a triple term
transparent, so `ex:clark owl:sameAs ex:superman` with
`ex:clark ex:reports <<( ex:superman ex:can ex:fly )>>` entails
`ex:clark ex:reports <<( ex:clark ex:can ex:fly )>>` (W3C test
`opaque-iri`). The OWL 2 Profiles §4.3 rule table is the floor.

Rule implemented: the `[ext]` row eq-rep-tt.

- Specification relation: `OWL.RL.TtRep x y o o'` (`o'` is the triple term
  `o` with one occurrence of the IRI `x`, in subject, predicate or object
  position, at any nesting depth, replaced by `y`) and the constructor
  `Derives.eqRepTt` (premises `x owl:sameAs y`, both IRIs, and `s p o`).
- Engine row: `RLClosure.eqRepTtFor` and `RLClosureIndexed.eqRepTtForS`,
  appended last in `conclusionsList`, `conclusionsListS` and `rowTable`
  (`RowSpec.additive owlSameAs`). Driven by an `owl:sameAs` triple between
  two distinct IRIs; it scans the round's graph for triples whose object is
  a triple term. It emits nothing on a graph with no triple term, so the
  closure of such a graph is the same list as before.
- Model theory: `RlCondEqRepTt` over `SemTtRep` (the replacement on
  `iTt` denotations), a field of `RlConditions`; `rl_derives_holds` covers
  the row. The Herbrand completeness model satisfies it because its `iTt`
  is constant. In the unified schema the row is in `OwlRlInterpCond`,
  because a `DTerm` has no function symbol for `iTt`.
- Nothing else is derived from inside a triple term: the negative guards of
  `RDFS/TripleTermClosureTests.lean` stay, and new ones check that the
  substituted inner triple is not asserted and that a blank node inside a
  triple term is not replaced.
- The RDFS closures (`RDFS.closureFix`, `fullClosure`) have no
  `owl:sameAs` semantics and do not substitute.
- 2026-10-23: `RDFS.rdfsPlusClosureFix` runs the row too
  (`rdfsPlusConclusions`, last row `eqRepTtFor`). Until then the
  `rdfsPlusClosure` op substituted `owl:sameAs` in subject, predicate and
  object position of asserted triples (eq-rep-s, -p, -o) but not inside a
  triple term, so it did not give the W3C `opaque-iri` entailment, whose
  manifest regime is "RDFS-Plus". Only `RDF.regimeEntails .rdfsPlus` gave it.
  Soundness of the row is the same lemma (`eqRepTtFor_sound`). The Datalog
  program `rdfsPlusProgram` (`Unified/DatalogClosures.lean`) has no such
  rule, because a `DTerm` has no function symbol for a triple term; its
  agreement theorems are on demo graphs with no triple term, where the row
  emits nothing.

## The W3C RDF 1.2 rdf-semantics tests

`l4rdf-semantics` runs the 29 entries of
`third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl` through
`RDF.regimeEntails`: 29 pass, 0 fail (out of 29), 2026-10-23.

The closure verbs are also run on the same W3C files (`Wasm/cli-smoke.sh`,
section "The W3C RDF 1.2 rdf-semantics test files"):

| W3C test | Regime | Closure verb checked | Kind |
|---|---|---|---|
| `opaque-iri` | RDFS-Plus | `rdfs-plus`, `owl-rl` | positive |
| `reifies-range` | RDFS | `rdfs` | positive |
| `triple-term-not-asserted` | simple | all four | negative |
| `triple-terms-no-spurious` | simple | all four | negative |

`triple-terms-propositions` (rdfs14) needs a new blank node, which no closure
makes; only `l4rdf-semantics` decides it. The other entries are simple or
RDF entailment over literals and JSON values, not closure cases.

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

Neither the specification nor the test suite defines the rule. The
editor's draft (https://w3c.github.io/rdf-canon/spec/, read 2026-10-23) still
has no such rule. The op
refuses a dataset with a triple term (or a directional language-tagged
string, also an RDF 1.2 term) with a message that names RDFC-1.0 §4.6 and
§4.8 and the issue https://github.com/danbri/factoidal/issues/957
(`Wasm/Ops/Canon.lean`, `canonRdf12Refusal`;
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
the mapping and the issue https://github.com/danbri/factoidal/issues/958
(`Wasm/Ops/ReasonDl.lean`, `owlDlRdf12Refusal`).
Expected failures: `npm/factoidal/test/rdf12-terms.test.js`,
`Wasm/cli-smoke.sh`.

## Theorems

The closure soundness and fixpoint theorems are stated over `Term`, which
admits triple terms; they cover inputs with triple terms without change. The
op-level theorems `owlClosureOf_eq`, `rhoDfClosureOf_eq`,
`rdfsPlusClosureOf_eq`, `closureEnvelopeOf_stream`, `canonicalizeOf_eq`,
`owlIsConsistentOf_eq`, `owlEntailsOf_eq` are restated for mode `.rdf12`
and build.

2026-10-19, eq-rep-tt: `Derives` has the new constructor `eqRepTt`. Every
induction over it was extended and builds: `Derives.mono`, `Derives.cut`,
`conclusionsFrom_sound` (closure soundness), the saturated-closure
completeness induction in `RLTheorems.lean`, `derives_irisNonReserved` and
`rl_derives_holds` (`RLSemantics.lean`), `rlHerb_conditions`. The
semi-naive equality `indexedClosureSN_eq` holds with the row in `rowTable`
(`eqRepTtForS_add`). New lemmas: `mem_ttRepAll`, `ttRepAll_of_ttRep`,
`ttRep_self`, `eqRepTtFor_sound`, `ttRep_termIris`, `semTtRep_of_ttRep`.
