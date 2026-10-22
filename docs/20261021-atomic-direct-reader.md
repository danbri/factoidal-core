# Restricted RDF-to-Direct reader

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

`OWL/AtomicDirect.lean` proves a model-preservation bridge for an executable,
restricted reader. It follows the atomic declaration/assertion patterns in
[Mapping to RDF Graphs, Tables 7 and 16](https://www.w3.org/TR/2012/REC-owl2-mapping-to-rdf-20121211/),
with class and assertion conditions from
[Direct Semantics, Tables 4, 5 and 10](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/).
Annotations have no logical effect under Direct Semantics §1.

The reader accepts named class declarations, atomic subclass axioms,
Thing/Nothing, named-individual class assertions, sameAs/differentFrom,
named-individual declarations, and named or blank ontology headers.
Declared annotation properties and builtin label/comment/versionInfo accept
IRI, blank-node or ordinary literal values; annotation domain/range statements
have no logical effect. Directional literals and triple terms are rejected.
Declarations can follow their uses. Reserved logical names cannot become
annotation properties or named individuals. Class/individual punning and
ordinary user IRIs containing internal-looking prefixes remain ordinary.

Every supplied triple is decoded. An unsupported triple rejects the whole
Graph. Imports, restrictions, lists, undeclared properties and object/data
properties are unsupported. No named graph is projected by this Graph API.
Admission deliberately permits missing or multiple ontology headers and
implicit class declarations; it is not the full OWL DL RDF syntax validator.

`MapsTo` is an independent structural mapping relation. `classHolds` and
`axiomHolds` interpret its clauses independently of compilation. Annotation
roles are stated by original-triple membership; the executable lookup has a
separate soundness proof. `SourceModel` mentions neither reader output nor
`DirectModel`. Unsupported triples can have vacuous limited semantics, so
both definitive verdict constructors also require `Accepted` evidence.

`accepted_covers_triples` separately proves that admission supplies a
mapping witness for every original triple. Its proof follows the actual
successful `mapM` traversal. The contract gate mutates that traversal to
return an empty clause list and requires failure inside this proof.

`readOntology_preserves_models` maps every original source model of every
accepted graph to the actual `DirectModel`, using the same interpretation
and assignment. `readOntology_hasModel` packages that result. `decide_sound`
composes it with the actual `checkCert_sound`; it needs no caller-supplied
reader preservation premise. Rejected certificates and unsupported input
produce distinct unknown reasons. This refutation producer supplies no
positive consistency decisions.

Compilation adds only the input clauses and a universally true top assertion
at the empty-string name. `initialOntology_model` proves that seed valid for
every interpretation/assignment. It gives the checker an active domain
element for top-subclass-bottom contradictions and needs no freshness claim.

The [source-model fixture](../tests/assurance/AtomicDirect.lean) proves Unit
models of the original annotation-domain and user-prefix collision graphs.
Its corollaries exclude a false verdict for every certificate. An unsupported
equivalentClass contradiction deliberately has a limited SourceModel; separate
proofs establish read rejection, absence of admission and impossibility of
any definitive certified verdict.

Focused validation, from `formal/lean4/`:

```sh
lake env lean L4Factoidal/OWL/AtomicDirect.lean
lake env lean ../../tests/assurance/AtomicDirect.lean
```

Both compile with Lean 4.33.1. The fixture's six value guards and rejected
constructor check pass. Axiom reports contain only standard `propext`,
`Classical.choice` and `Quot.sound`. The initial annotation lookup scans the
graph and has quadratic worst-case time; no performance claim is made.
This closes the bridge for this reviewed fragment. It does not prove full
O1/O2, parser adequacy, complete OWL reasoning, compiled-artifact correctness,
or adoption by an existing public API.
