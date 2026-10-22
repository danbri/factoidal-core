# Enforce semantic claims at the public API

Date: 2026-10-21. Status: methodology requirements and checked interface
example. The production proof chain is not implemented by this record.

The owner reports that pragmatic release work is sufficient to move on and
asks for the deeper Lean and QA correction. This record addresses that
correction. Earlier audit results remain versioned evidence, not a blanket
description of another branch or a later artifact.

## What is proved, and what is unfinished

There is no demonstrated pair of Lean proofs of `P` and `Not P` for the
same input, definitions and assumptions. The defect is a computation
making a stronger semantic claim than the theorem available for it.
An executable definition in Lean does not acquire its intended semantic
specification merely because it compiles.

By "the project's certificate design" we mean the existing document
[OWL DL refutation certificates — 2026-10-10](2026-10-10-owl-dl-refutation-certificates.md),
and its implementations `OWL/DirectCert.lean` and `OWL/RefuteCert.lean`.
A certificate records choices in the refutation search; a separate checker
validates them. It is not a signature, audit approval or release certificate.

The checker has a substantial completed theorem. At `DirectCert.lean:1503`,
`checkCert_sound` proves that an accepted certificate implies no model of
the supplied `DlOntology`. That fragment includes class axioms, role
axioms, inverse properties, same-individual assertions and an ABox. Its
models have arbitrary domains, not just finite domains. The total individual
assignment supplies a domain inhabitant. The limitation is the supported
language and its connection to input RDF, not a finite-model assumption.

Section 9 of the existing design lists three **unfinished proof obligations**:

- O1: the ontology reader preserves the required meaning of the RDF input.
- O2: preprocessing preserves models under Direct Semantics.
- O3: generated refutation goals justify the resulting entailment claim.

"Open obligation" in that record means a required statement has not yet
been proved. It does not mean a completed proof is "open to refutation".
The missing statements are not hidden `sorry` terms in `checkCert_sound`;
that theorem checks, but says something narrower than the complete API
claim. Axiom hygiene cannot detect a theorem that was never required.

These are not merely unfinished documents. The probes below contradict
unrestricted preservation claims for the present transformations. Those
transformations or their admitted scope must change before the required
statements can be proved. No completed Lean proof is being described as
refuted.

## Fresh source inspection and concrete probes

GitHub main was inspected at
`3a38e658c372b111132eb08237ff01a245abd960`. Its `DirectCert`, `RefuteCert`
and `DirectMappingFilter` files have the same Git blob hashes as the local
modules used in the probes. At that head, `Wasm/Ops/ReasonDl.lean:86–96`
constructs the public consistency Boolean from `tableauConsistent`, without
requiring `checkCert` or `RefuteCert.certify`. The native harness records
certificate results but explicitly does not let them alter its verdicts.
This source inspection is not a new npm artifact acceptance run.

The npm registry returned version `0.11.0` with the original audit's SHA-512
integrity; the npm web page returned HTTP 403. These observations do not
identify which working branch contains the owner's pragmatic fixes. Source
reads and metadata are retained under the review's `logs/methodology-*`.

Two bounded Lean probes demonstrate why adding a checker call alone is
insufficient:

| Input | Observation | Missing guarantee |
| --- | --- | --- |
| An annotation property with domain `owl:Nothing`, used in an annotation assertion | On the raw graph, `checkCert.close=false` and `certify=unchecked`; after RL closure, `checkCert.close=true` and `certify=proved` | Preprocessing changed the ontology before a sound checker refuted it; O2 is required |
| A class IRI `urn:factoidal:owl-cert:one-of:urn:a`, declared a subclass of `owl:Nothing` | The reader invents membership of `urn:a` in that class; `checkCert.close=true` on the read ontology | User-controlled names collided with an internal convention; O1 is required |

The second input permits the class to be empty. The probe includes a Lean
proof of a Unit-domain model of that intended structural ontology. The
read ontology contains an extra ABox assertion and has no model. These
are different ontologies, so the two proofs do not contradict each other.
The full `certify(raw)` returns `notRefuted` in the second probe: this is
a reader/checker-boundary defect, not a demonstrated public API failure.

The [probe source](../audits/npm-0.11.0/20261021-methodology/audit/owl-proof-boundary-probe.lean),
[successful log](../audits/npm-0.11.0/20261021-methodology/logs/owl-proof-boundary-probe.log)
and [evidence manifest](../audits/npm-0.11.0/20261021-methodology/manifest.json)
are preserved with the fetched source and npm metadata. The earlier evidence
archive is unchanged.

The probe exits 0. Axiom reports for `checkCert_sound`,
`detectClashPlus_sound` and `detectClashPlusI_eq` contain only the standard
`propext`, `Classical.choice` and `Quot.sound`. The RL detector theorem
concludes `Clash g ∨ ExtClash g`, a statement about specified graph
patterns. Separate RL semantic theorems require their own interpretation
conditions; neither theorem silently supplies Direct Semantics preservation.

## Require the theorem at the actual public boundary

For accepted input `x`, fixed regime `r`, datatype map, imports closure and
vocabulary, define `Sat r x` from independently reviewed declarative
semantics. Require both implications for the actual public producer:

```text
publicVerdict r x = consistent   -> Sat r x
publicVerdict r x = inconsistent -> Not (Sat r x)
```

Entailment needs analogous implications for `Entails r premise conclusion`
and its negation. Unknown asserts neither. Soundness does not require a
bounded procedure to be complete; its coverage is a separate obligation.

Use a result type indexed by the input and semantics:

```text
VerifiedVerdict r x
  consistent   (proof : Sat r x)
  inconsistent (proof : Not (Sat r x))
  unknown      (reason : UnknownReason)
```

The adapter erases the proof to a wire verdict. Prove that this conversion
preserves meaning and require every export to use it. Lean then rejects
turning an unverified search outcome into a definitive result. A universal
theorem on a plain-result producer is also acceptable; the requirement is
the closed semantic guarantee, not a particular syntax for the datatype.
Do not let another wrapper construct an arbitrary Boolean around it.

Keep a fast search that proposes untrusted certificates. A total checker,
with its soundness theorem, validates each proposal against the correctly
bound input. Rejection, budget exhaustion and unsupported syntax remain
distinct unknown outcomes. A rejected refutation is not proof of a model.
Proof fields can be erased during compilation; a runtime certificate check
is still required for proposals produced by an untrusted search.

## Prove transformations in the direction actually needed

For a refutation reader `lower x = y`, prove:

```text
SatSource x -> SatFragment y
```

Then no model of `y` implies no model of `x`. Dropping constraints may be
sound in this direction. A model of that weakened fragment does not prove
the original input consistent. Consistency claims need the reverse
model-lifting implication, or another justified model/decision procedure.
Prove both directions when claiming equivalence. A condition assumed in a
composition lemma is not a completed proof until the actual caller supplies it.

For entailment by refutation, prove that every countermodel yields a model
of at least one generated goal. This must also cover an empty goal list,
fresh names, anonymous individuals and rejected conclusion forms. Refuting
all goals then excludes every countermodel. Failure to find a conclusion
in a partial closure is not non-entailment.

Complete O1/O2/O3 against the actual representations. Checking a certificate
for an incorrectly read or strengthened ontology proves the wrong input
unsatisfiable. Binding a saved certificate to hashes of input, ontology,
regime and checker version helps reproducibility; hashes cannot replace
the semantic relationship between those objects.

## Preserve regimes, roles and generated-name identity

Index models, ontologies, certificates and verdicts by semantic regime.
Cross-regime use requires an explicit theorem with checked scope. Give
class names, individual names and property roles distinct syntax types;
plain aliases of `String` do not enforce that distinction. Legal punning
may reuse an IRI while its class and individual interpretations remain
separate. Generated names need tagged constructors or proved freshness,
not a string prefix presumed absent from user data.

For Direct Semantics, annotations do not add logical class membership.
An RDF-based domain rule applied to an annotation property cannot justify
a Direct Semantics refutation. Individual equality also does not identify
class extensions merely because the same IRIs are used in both roles.
Sources: [Direct Semantics §§1–2.5](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/)
and [Mapping to RDF Graphs §3](https://www.w3.org/TR/2012/REC-owl2-mapping-to-rdf-20121211/#Mapping_from_RDF_Graphs_to_the_Structural_Specification).

## Semantic review, audits and QA

Review the declarative definitions separately from the implementation, with
normative citations and imported definitions. Changes to those definitions
and to the public theorem statements need review; do not weaken them just
to accommodate a failing implementation. Exhibit models of the annotation
and punning controls in the same theory used by the API theorem. A claimed
refutation of either must then fail the soundness proof.

| Control | Required evidence |
| --- | --- |
| Export contract audit | Actual dispatch producer, its full theorem statement, semantic definition, scope, discharged assumptions and adapter; theorem-name matching is insufficient |
| Proof dependency audit | Imported/built contracts, axiom lists and named opaque/host/compiler trust boundaries; clean axioms alone do not validate the standard's transcription |
| Transformation audit | Reader, normalization, closure and goal-building theorems composed all the way to the original input |
| Semantic model review | Inhabited scope, nonempty domains, correct datatype conditions, no accidental unique-name or finite-model assumption, correct imports and roles |
| Mutation checks | Forged Boolean, swapped regime, checker bypass, dropped constraint or budget exhaustion cannot be promoted to a justified verdict |
| Artifact checks | Exact packed engine, wrapper routing, options, refusal behavior and independent suite results |
| Release enforcement | Failed obligations stop claims and publication as required by the stated policy; recording a red diagnostic is not enforcement |

Generate the export inventory from elaborated declarations and dispatch
entry points; do not maintain another manually ticked theorem count. Reuse
existing hygiene, unbuilt-module and compiled-replacement audits, while
keeping their limited purpose explicit. The
[Lean validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
also recommends replaying built proofs with `lean4checker`. This cannot
supply a missing theorem or repair a wrong definition.

Use the same semantic decision function from harness and public API.
Generate well-formed ontologies with known models and perturb them within
proved model-preserving rules. Include annotations, punning and adversarial
names. Retain W3C suites and independent comparisons; agreement between two
engines remains test evidence, not a proof.

## Executable interface example and acceptance

The isolated `CertifiedVerdictContract` example demonstrates the indexed
result, checker and wire-erasure pattern. It compiles in Lean 4.33.1 with
seven value guards and five rejected-construction checks. Three mutations
are rejected: swapped wire Booleans, swapped fixture semantics and a forged
false checker result. The generic safety theorems use no axioms. The finite
fixture checker uses only standard `propext`.

Project fixture:
[CertifiedVerdictContract.lean](../../tests/assurance/CertifiedVerdictContract.lean).
Run the [bounded mutation checker](../../tools/check-semantic-verdict-contract.py)
from the repository root:

```sh
python3 tools/check-semantic-verdict-contract.py --lean /path/to/lean
```

The runner requires a successful baseline and the expected axiom audits.
It rejects absent or ambiguous mutation anchors, missing Lean, timeouts,
and syntax/import failures masquerading as successful mutation checks.
Each mutation must fail inside the affected proof with a type/proof error.

This is an interface demonstration, not a W3C formalization or a theorem
about the product's reader, search or adapter. The checker soundness field
is deliberately an obligation that a real implementation must discharge.

The implementation sequence is: review `Sat` and `Entails`; prove the
reader/preprocessing/goal bridges; require certified results from actual
producers; prove wire conversion; demonstrate that bypass mutations fail;
then enforce the contract and artifact checks in publication. Track unknown
counts separately so an implementation answering unknown everywhere cannot
be presented as complete reasoning support.

This prevents unchecked definitive verdicts within the reviewed formal
scope and stated trust assumptions. Adequacy to W3C prose and the compiled
artifact remain named review and testing boundaries.

## Concrete reader pattern and review corrections

The [restricted reader implementation record](../20261021-owl-reader-preservation.md)
documents `OWL/AtomicDirect.lean`, which connects a reviewed source relation
to the existing checker without assuming a reader-preservation theorem.
This closes a limited fragment, not general O1/O2/O3 or the public adapter.

Three separate obligations emerged during review:

1. Source annotation roles are original-graph declaration membership, not
   the executable lookup's result. `isAnnotation_sound` proves the lookup
   against that independent relation.
2. Both definitive verdict constructors require whole-input admission.
   A partial model can ignore an unsupported equivalentClass contradiction;
   such a model must not authorize a consistency verdict.
3. `accepted_covers_triples` proves that admission accounts for each original
   triple. Source-model preservation alone allows dropping clauses. An edit
   that returns an empty axiom list is rejected inside this coverage proof.

Proof-bearing decoding, compilation preservation, actual checker acceptance
and wire-erasure soundness form the remaining chain. Independent models of
the two original satisfiable controls exclude an inconsistency verdict for
every certificate. Reversible tagged names separately prevent source IRIs
from being interpreted as generated nominal/cardinality atoms.

The real-definition mutation runner checks all of these boundaries with
seven deliberate defects. It requires a successful baseline and failure in
the relevant proof, and retains raw compiler output. W3C corpus measurement
is separate: unsupported inputs and unknown answers are not successful
conformance results. None of these checks certifies an unconnected npm API.

The [public consistency integration](../20261021-owl-public-boundary.md)
now connects that reader to the actual local string-returning operation.
Its JSON-field meaning theorem is accompanied by explicit success/refusal
schemas: the semantic lookup's none result cannot distinguish null from a
missing or non-Boolean field. The public-function theorem requires its
returned string to serialize the certified object; bypassing that producer
breaks the proof. Parsed-dataset, dispatch and package tests cover the
remaining serialization/extraction boundaries separately.

Integration found a distinct equality-coverage bug: applying a merge to
assertions without renaming remaining same-individual pairs can lose a
representative. The repaired algorithm preserves models and passes chain
permutation controls, but general equality-closure completeness is a
separate obligation. This is an example of a defect that a soundness theorem
was never intended to rule out.

Audit the mutation runner too. Heartbeat/recursion/OOM failures must not
count as proof rejection. Exact inventories must include null expectations
and reject duplicate JSON fields. The independent runner controls are part
of the preserved evidence, not a substitute for actual Lean compilation.

Compiled-artifact testing exposed a separate test-adapter error: the loader
throws error envelopes, and the public API parses malformed input before the
OWL call. The corrected runner checks the retained ABI envelope and structured
public ParseError separately. Six synthetic controls reject unrelated runtime
errors, returned refusals and wrong error contents. Universal unique-key
proofs also prevent disagreement between formal first-match field lookup and
an external JSON parser's duplicate-key convention. These are distinct
obligations from the meaning of a Boolean verdict.
