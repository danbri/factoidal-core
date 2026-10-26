# OWL reader preservation: atomic fragment and generated names

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

Date: 2026-10-21. Status: local implementation and checked library build; public integration unfinished.
This continues the [certified boundary](20261021-certified-owl-boundary.md).
The later [public-boundary record](20261021-owl-public-boundary.md) connects
this restricted reader to the local consistency operation and records the
resulting scope reduction. Counts below describe this reader-stage checkpoint.
The [focused reader note](20261021-atomic-direct-reader.md) gives the proof structure.
The local checkout remains based on `d83100e6`; it must be reconciled with
current core main before integration. No published package is changed by
this work.

## What the proof must connect

The [OWL 2 Direct Semantics Recommendation, §1](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/#Introduction)
gives annotations no semantic effect. Its Tables 5 and 10 specify class
inclusion and individual assertions. The
[RDF mapping, §3](https://www.w3.org/TR/2012/REC-owl2-mapping-to-rdf-20121211/#Mapping_from_RDF_Graphs_to_the_Structural_Specification)
distinguishes annotation-property domain/range axioms from object-property
domain/range axioms. A generic RDF rule closure cannot erase that distinction
and still claim to preserve Direct Semantics without a proof.

The new proof starts at an actual `RDF.Graph`, with independently
stated satisfaction conditions for a restricted structural fragment. It
connects every accepted input to the actual `DirectModel` used by
`DirectCert.checkCert_sound`. The reader's output is not itself the
definition of source satisfiability. Unsupported syntax rejects the whole
input at this boundary. A rejected certificate yields unknown.

This is a restricted reader, not completion of the general O1 reader proof,
the O2 closure/materialisation proof, or the O3 entailment-goal proof. There
is no RL preprocessing on this path. The original legacy acceptance test
must remain intact so a successful new path cannot hide a failing old one.

## Generated identifiers

The legacy reader used plausible-looking URN prefixes to distinguish
generated nominal and data-cardinality atoms from ordinary source class
IRIs. An input can legally use those IRIs. A corpus having no such names
does not establish freshness.

The replacement design uses distinct constructors for source names,
nominals, minimum data cardinalities and maximum data cardinalities. Since
`Concept.atom` currently takes a string, every constructor, including source
names, crosses that boundary through a reversible encoding. The proved
round-trip theorem establishes injectivity and separation for arbitrary
payload strings. List boundaries, delimiters, Unicode, empty fields and
large cardinalities must remain distinct. This naming theorem is separate
from the unfinished semantic proof of the legacy reader as a whole.

## QA and counts

- `tests/assurance/AtomicDirectAcceptance.lean` exercises parsed RDF inputs,
  annotations, declaration order, valid class/individual punning, genuine
  contradictions and unsupported syntax. Expected observations are separate
  from the implementation. Unknown is not called consistent.
- `tools/check-atomic-direct-corpus.py` reads the unchanged vendored W3C
  `all.rdf` catalog and retains each test IRI. It selects Approved, DIRECT,
  DL consistency/inconsistency test units. Initial census: 266 units;
  246 have RDF/XML premise serializations; 20 do not. The latter remain
  visible as missing serializations.
- `tests/assurance/AtomicDirectCorpus.lean` invokes the actual RDF/XML
  parser, restricted reader and certified decision on the original embedded
  ontology strings. It tries `Cert.close` only: this is reader/checker QA,
  not full refutation search or OWL decision completeness.
- The corpus runner rejects empty/duplicate/missing result inventories,
  malformed verdicts and definitive answers on unsupported inputs. All
  selected units are accounted for; unsupported and unknown are not
  conformance passes. An exit 0 means a completed run with no observed
  incorrect definitive verdict, not a declaration of OWL conformance.

The naming repair passes `lake build L4Factoidal.OWL.RefuteCertTests`
(33 jobs). The unchanged legacy model-preservation gate now passes the
user-name collision case and still fails the annotation/RL-preprocessing
case. Report: `logs/owl-model-preservation-after-names.json` in the review
workspace. Its nonzero exit is retained; this is not an XFAIL pass.

Two destructive mutations of the actual name encoder (source names made
nominals; maximum names made minimum names) are rejected inside the
round-trip proof. `logs/owl-name-proof-mutations.json` preserves the compiler
output. These are proof failures, not merely failing example guards.

Review of the first restricted-reader draft found that its annotation role
predicate reused the operational HashSet index. That would let a wrong
index change the supposed source semantics too. The implemented correction
states annotation roles by original-graph declaration membership and
proves the operational lookup sound for that independent predicate.
This review finding is preserved even after the implementation is repaired.

## Implemented source-to-verdict chain

`OWL/AtomicDirect.lean` contains:

1. `MapsClass`, `MapsTo`, `classHolds` and `axiomHolds`: a separately stated
   structural mapping and denotation for the fragment. Source satisfaction
   does not invoke the reader, compiler or target ontology.
2. `isAnnotation_sound`: executable lookup implies actual declaration
   membership, or a recognized built-in annotation property. Lookup is
   initially quadratic in the worst case; no performance claim is made.
3. `readTriple`: decoding returns a mapping proof with each structural axiom.
   `readAxioms` rejects the whole graph if any triple cannot be decoded.
4. `compileClass_correct`, `addAxiom_preserves_model` and
   `readOntology_preserves_models`: every accepted input preserves each
   source model in the existing `DirectModel` predicate. No caller supplies
   a reader-correctness assumption.
5. `checkedRefutation` and `decide_sound`: an actual checker acceptance
   yields a justified no-model verdict for this source relation.
6. `Accepted`, `definitive_admitted` and `unsupported_is_unknown`: both
   definitive constructors and the wire theorem require whole-input
   admission. The actual producer returns unknown on unsupported input.
7. `accepted_covers_triples`: successful admission gives an independent
   structural mapping witness for every original triple, proved through
   the actual reader traversal.

A second review caught why (6) is essential. With only mapped clauses in
`SourceModel`, an unsupported graph containing `C equivalentClass Thing`
and `C equivalentClass Nothing` has a vacuous partial-source model. It is
an inconsistent OWL ontology. The actual producer already refused it, but
an exposed model-verdict constructor could have wrapped that partial model.
Both definitive constructors now require successful-reader evidence; source
meaning remains separate. This closes the constructor hole as well as
preserving the existing producer refusal.

A third review added (7): one-way model preservation still permits a
reader to drop clauses. Admission must have a separate coverage guarantee.
The real traversal is now mutated to return an empty clause list; Lean
rejects that edit inside `accepted_covers_triples`. The original preservation
theorem alone does not reject it. This is admission coverage, not a proof
of complete reasoning or a reverse model-lifting theorem.

The compiler adds `"" : Thing` as a universally true initial assertion.
Its model-preservation proof makes the nonempty domain available to the
checker even for `Thing subClassOf Nothing` with no asserted individual.
This name needs no freshness assumption: every assigned element is in Top.
Interpretation domains are arbitrary; there is no finite-domain restriction
or unique-name assumption.

## Exact scope and unfinished work

Accepted logical clauses are named atomic subclass and class assertions,
Thing/Nothing, and named-individual same/different assertions. Class/individual
punning keeps separate interpretation positions. The reader supports class,
named-individual and annotation declarations, ontology-header triples, and
annotation assertions/domain/range. The automatic built-ins are rdfs:label,
rdfs:comment and owl:versionInfo. Six other built-in annotation properties
are explicitly unsupported, along with imports, object/data-property
axioms, restrictions, most blank-node syntax and RDF 1.2 annotation values.

Admission permits missing or multiple ontology headers and implicit class
names. It recognizes this logical fragment, not the complete W3C OWL 2 DL
reverse-mapping grammar. Reserved individual names are refused. The
correspondence of the separate mapping relation to the cited W3C clauses
has been manually reviewed; it is not a mechanized transcription theorem
about all OWL. The source theorem starts at `RDF.Graph`; it is not a proof
of the byte parser, dataset adapter or JavaScript wrapper. Graph-only test
helpers now reject named graphs instead of silently discarding them.

General legacy reader O1, preprocessing O2, entailment-goal O3 and the
public verdict adapters remain unfinished. A caller still using legacy
RL closure gains no assurance from this new path. The legacy annotation
failure stays red. No npm artifact was rebuilt or retested for these changes.

## Verification and workflow drafts

- Full `lake build L4Factoidal`: **808 jobs, exit 0**; new modules are
  imported by the library. Import audit: **815 modules, 815 reachable**.
  Existing unrelated deprecation warnings remain. Evidence:
  `logs/owl-reader-library-coverage-build.log`.
- **45/45** parser/reader/verdict acceptance cases and a named-graph scope
  refusal control pass. `logs/owl-reader-contracts-coverage-final.json`.
- Independent `SourceModel` witnesses for the original annotation and
  user-name-collision graphs compile. The gate checks eight axiom reports,
  six value guards and a rejected constructor in
  `tests/assurance/AtomicDirect.lean`. Universal corollaries rule out a false
  inconsistency verdict for either graph for **every certificate**. The
  unsupported equivalentClass counterexample has a partial-source model,
  but is proved unadmitted and unable to yield any definitive certified
  verdict. These proofs do not rely on failed refutation search.
- **7/7** mutations fail in the relevant real definition/proof: source
  name→nominal, maximum→minimum name, arbitrary annotation recognition,
  reversed subclass compilation, dropping every input clause,
  certificate-check bypass, inverted
  wire verdict. The runner also checks a whitelist of standard axioms.
- W3C corpus on the final admission-aware producer:
  **266 selected; 246 executed; 232 unsupported; 14 supported unknown;
  20 missing RDF/XML serializations; zero definitive answers**. This
  provides no conformance success or completeness claim. Evidence:
  `logs/atomic-direct-w3c-coverage-final.json` retains all original case IRIs,
  raw execution and catalog/input digests. Its selected-source hashes do
  not cover the entire transitive build/compiler closure. This final run
  includes the coverage theorem and corrected mapping-table citation.
- The csimp reachability audit passes after building the previously absent
  `Harness.CryptoProbe` prerequisite. Initial failure and final log are
  retained. The new encoder's generated C calls its proved tail-recursive
  replacement. The 100,000-character round trip passes.
- Runner controls reject missing/duplicate cases, malformed observations,
  weakened expectations, missing/custom axiom audits and missing Lake.
  Missing Lake exits 2; semantic acceptance failure exits 1. Earlier failed
  development runs, including a dependent-match proof attempt and a fixture
  accessor typo, remain in separate reports; they are not overwritten.
- Local core `verify-lean4.yml` and builds `build.yml` now call the new
  contract gate and W3C measurement as blocking steps, preserving reports
  even after failure. Core PR path filters include the fixtures/tools/catalog.
  YAML and blocking-step checks pass. These workflows have not been pushed
  or run remotely; they enforce only the stated new-reader/name scope when
  integrated, not the unresolved legacy route or npm wrapper.

The original acceptance failures and all superseded reports remain preserved.
The development report `owl-reader-drop-all-before-coverage.json` has a
misleading filename: its recorded source hash already includes the coverage
theorem, and it records rejection in that proof. It does not establish a
successful pre-theorem mutation run. The final gate records the same mutation
with its exact proof range and source hashes.
