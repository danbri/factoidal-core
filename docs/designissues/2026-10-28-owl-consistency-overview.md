# OWL consistency in Factoidal: what `owlIsConsistent` answers and how each answer is checked

Date: 2026-10-28. For developers who know OWL 2 and basic Lean 4. Owner,
2026-10-28: "explain the OWL thing clearly here as if to a general developer
audience familiar with owl and lean basica". This record collects the parts of
earlier records into one account; the details stay in the records linked at
the end.

## 1. The function

```js
import { owlIsConsistent } from '@factoidal/core'
await owlIsConsistent(text, { format: 'nquads', fuel: 64 })
// { consistent: true }
// { consistent: false, reason: '...' }
// { consistent: null,  reason: 'unsupported-syntax: ...' | 'budget-out: ...'
//                       | 'incomplete-search: ...' }
```

The question is OWL 2 Direct Semantics consistency: has the ontology in the
**default graph** of the input at least one model? Named graphs add no axioms.

There are three answers:

| answer | meaning (Lean, `AtomicDirect.Meaning`) |
| --- | --- |
| `true` | the whole default graph is in the admitted fragment, and it has a model |
| `false` | the whole default graph is in the admitted fragment, and it has no model |
| `null` | no claim; `reason` says why: syntax outside the fragment (`unsupported-syntax`), the fuel ran out (`budget-out`), or the search ended with no checked model and no checked certificate (`incomplete-search`) |

`null` is never a guess. The engine does not fall back to an OWL 2 RL closure
or to any other procedure that could answer wrongly.

## 2. The admitted fragment

`formal/lean4/L4Factoidal/OWL/AtomicDirect.lean` reads the RDF graph with the
OWL 2 Mapping to RDF Graphs (2012) and admits only:

- named atomic classes, `owl:Thing`, `owl:Nothing`;
- `rdfs:subClassOf` and class assertions (`rdf:type`);
- `owl:sameAs` and `owl:differentFrom` between individuals;
- `ObjectSomeValuesFrom(p A)` (an `owl:Restriction` with `owl:onProperty` and
  `owl:someValuesFrom`, `A` atomic), as the super-class of a subclass axiom or
  as the class of an assertion;
- `owl:TransitiveProperty`;
- annotations (the nine built-in annotation properties, declared annotation
  properties, annotated axioms, `owl:versionIRI`). Annotations have no logical
  effect (Direct Semantics section 1).

If **any** triple of the default graph is outside this list (for example an
`owl:NegativePropertyAssertion`, `owl:equivalentClass`, `owl:imports`), the
answer is `null` with reason `unsupported-syntax`. The reader does not drop the
triples it cannot read, because a dropped axiom could change the answer.

## 3. What the answers mean, in Lean

The specification of a model is stated directly over the RDF triples:

```lean
-- AtomicDirect.lean
def SourceModel (I : Interp δ) (ν : Ind → δ) (graph : Graph) : Prop :=
  ∀ triple ∈ graph, ∀ clause, MapsTo graph triple clause → axiomHolds I ν clause

def Satisfiable (graph : Graph) : Prop :=
  ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), SourceModel I ν graph

def Meaning (graph : Graph) : Option Bool → Prop
  | some true  => Accepted graph ∧ Satisfiable graph
  | some false => Accepted graph ∧ ¬ Satisfiable graph
  | none       => True
```

`MapsTo` is the Mapping tables (which axiom a triple states) and `axiomHolds`
is the Direct Semantics conditions (Tables 4, 5 and 10). Neither depends on
the reader or the reasoner, so the theorems below say something about the
input text, not about an internal data structure.

## 4. How each answer is produced

The search is untrusted; a small checker is trusted, and its soundness is a
theorem.

- **`true`**: a search builds a candidate finite model (domain, class and
  property extensions, an individual assignment). `AtomicModel.checkModel`
  tests every triple of the graph against it.
  `checkModel_sound : checkModel graph M = true → SourceModel M.interp M.assign graph`.
- **`false`**: the reader compiles the graph to a description-logic ontology
  (`readOntology`); a tableau search produces a refutation certificate;
  `DirectCert.checkCertFuel` checks it.
  `checkCertFuel_sound : checkCertFuel O fuel c = true → ¬ ∃ δ I ν, DirectModel I ν O`.
  The bridge back to the triples is `AtomicDirect.readOntology_preserves_models`:
  a model of the source graph is a model of the compiled ontology, so "no model
  of the ontology" gives "no model of the graph".
- **`null`**: the reader refused the graph (`unsupported-syntax`), the
  `fuel` rounds were used up (`budget-out`), or the search ended with neither
  a checked model nor a checked certificate (`incomplete-search`).

`someValuesFrom` needs new individuals in a model. The search adds them with
blocking by filler, so a cycle such as `A ⊑ ∃p.A` with `i : A` has a finite
model (case `cyclic-some-values-from`, answer `true`).

The theorem chain ends at the JSON field that the wasm returns:

```lean
-- AtomicModel.lean
theorem decideFuel_sound (graph : Graph) (fuel : Nat) :
    Meaning graph (decideFuel graph fuel).consistent

-- Wasm/Ops/ReasonDlCertified.lean
theorem owlConsistencyJson_sound (ds : Dataset) (fuel : Nat) :
    AtomicDirect.Meaning ds.default ((owlConsistencyJson ds fuel).getBool? "consistent")
```

These theorems use only `propext`, `Classical.choice` and `Quot.sound`.

## 5. What the proofs do not cover

- Parsing the RDF text, writing the JSON text, the Lean-to-C-to-wasm
  compilation, and the JavaScript facade (`npm/factoidal/lib/api.mjs`).
- Completeness: a consistent graph can still get `null` (fuel, or syntax
  outside the fragment).
- OWL 2 DL as a whole, imports, the RDF-Based Semantics.
- `owlEntails`: it returns `false` only from a checked countermodel
  (`entailsFuel_sound`); it never returns a checked `true`.

The tests in sections 6 and 7 cover the first item for a fixed set of cases.

## 6. Check 1: the source boundary gate (core CI)

`tools/check-owl-public-boundary.py` (run by `verify-lean4.yml`):

- 23 fixed cases, each with an expected answer, run through the Lean producer
  and its adapter (`tests/assurance/OwlPublicBoundary.lean`). Examples:
  `same-different` (`a owl:sameAs b`, `a owl:differentFrom b`) gives `false`;
  `annotation-domain` (an `rdfs:domain owl:Nothing` on an annotation property)
  gives `true`, because annotations have no logical effect;
  `unsupported-negative-property` gives `null`.
- 5 proof mutations: the gate edits the producer (for example it inverts the
  Boolean, or reasons over the named graphs in place of the default graph) and
  requires that `lake build` then fails on the soundness theorems. A mutation
  that still builds means the theorems do not constrain that code.

## 7. Check 2: the packed npm package (factoidal-builds CI)

The proofs and check 1 are about Lean source. Users install a tarball that
holds the compiled wasm and the JavaScript facade. `factoidal-builds`
(`build.yml`, job `web-gates`, since https://github.com/danbri/factoidal-builds/pull/1)
packs that tarball for every build, extracts it, and runs:

- `tools/check-owl-public-artifact.mjs`: each of the 23 cases through the
  low-level op and through the public `owlIsConsistent` of the unpacked
  package. Each case runs in its own process with a 15 s deadline and
  `SIGKILL`, because a synchronous wasm call that does not end cannot be
  stopped from inside the process. The expected answer of each case is pinned
  in a table (`EXPECTED`); a changed source inventory stops the check until
  the table is reviewed.
- `tools/test-owl-public-artifact.mjs`: checks the checker on a synthetic
  package that has no engine: a correct baseline, an exception with no ABI
  envelope (must fail), and a hang that ignores `SIGTERM` (must be killed and
  fail).

Known defects are expected failures with an issue (`KNOWN_DEFECTS`); a known
defect that starts to pass fails the run.

## 8. What check 2 found on 2026-10-28

- No CI job ran the two package tools before builds PR 1. When commit
  `a701bef1` (https://github.com/danbri/factoidal/issues/960) added the
  checked `true` answer and 3 cases, the two tools were not updated, and both
  stopped before they checked any case. Repair:
  https://github.com/danbri/factoidal-core/pull/178.
- After the repair, the package check found a defect in the 0.20.0 package:
  https://github.com/danbri/factoidal/issues/1118. For RDF 1.2 input (for
  example `"x"@en--ltr`) the low-level op refuses correctly with
  `owl.unsupported-rdf12`, but the public `owlIsConsistent` parses the text and
  writes it again as RDF 1.1 N-Quads before the OWL call. That write fails,
  and the caller gets `serialize.failed` from the wrong layer. The two cases
  are expected failures until the facade passes the data without that
  re-serialisation.

## Records

- Reader and fragment: `docs/20261021-owl-reader-preservation.md`.
- Certificate boundary: `docs/20261021-certified-owl-boundary.md`.
- Model certificates, someValuesFrom, fuel, countermodels:
  `docs/designissues/2026-10-24-owl-model-certificates.md`.
- Gate design: `docs/20261022-owl-pr-reconciliation.md`; skill
  `skills/semantic-assurance/SKILL.md`.
