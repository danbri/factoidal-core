# OWL DL refutation certificates — 2026-10-10

Issue: <https://github.com/danbri/factoidal/issues/651> (plan of
2026-10-10, item 2: refuter soundness). Also unblocks
<https://github.com/danbri/factoidal/issues/732> (item 3 of its "done
when") and is follow-up 6 of
<https://github.com/danbri/factoidal/issues/586> (the certificate-checker
rung that `OWL/Tableau.lean`'s header names).

## 1. The problem

The DL regime (`l4owl-probe --dl`) decides units by refutation. Measured
at `db3f045f` (engine), corpus `third_party/testing/owl`,
`--refute-ms 3000`:

| Catalog | closure alone | closure or refutation | decided by refutation |
| --- | --- | --- | --- |
| type-inconsistency | 49 pass, 78 fail, 1 skip (out of 128) | 126 pass, 1 fail, 1 skip (out of 128) | 77 |
| type-positive-entailment | 345 pass, 67 fail (out of 412) | 400 pass, 12 fail (out of 412) | 55 |

`OWL/Refute.lean` (3,395 lines) has no theorem that a refutation means
"no model" under the OWL 2 Direct Semantics. The clash calculus
`OWL/Tableau.lean` has one (`refuted_sound`), but nothing connects the
two: `Refute.lean`'s header lists the correspondence rule by rule, as
prose. So the 77 and the 55 are measured, not proved.

This record does not try to prove the search. The search is a
`partial def` over a mutable-style state with caps, hash indexes and
read-time identification; a proof of it would be a proof about those
data structures. The approach is certificate checking: the search
emits what it decided, and a small total checker, proved sound once,
accepts or rejects it. A rejected certificate changes no verdict; it
changes what the harness may say about that verdict.

## 2. The chain from a premise to "no model"

```
premise RDF graph P
   │  RL closure; one class-expression materialisation pass; RL closure   (O2)
   ▼
graph g  (what `Refute.refute` receives)
   │  readOntology g                                                      (O1)
   ▼
ontology O : DlOntology  (TBox, role box, ABox over `Concept`)
   │  the refuter's search trace → certificate c
   ▼
checkCert O c = true   ──THEOREM──▶   ¬ ∃ δ I ν, DirectModel I ν O
```

This landing proves the arrow marked THEOREM. The arrows marked O1 and
O2 are open obligations, each with its own issue (§ 9). O1 is a
statement about reading RDF; O2 is a statement about the RL closure,
whose truth layer (`OWL/RLSemantics.lean`) is proved for a different
condition bundle. Neither one contains a clash rule.

`readOntology` returns a SUBSET of the
axioms the graph states (every axiom it cannot express in the fragment
is left out). A model of the full ontology is a model of every subset,
so "no model of the subset" implies "no model of the full ontology".
Dropping an axiom can only make a certificate fail to check.

For an entailment test the harness asks the refuter about
`closure ++ goal` for each negation goal of `OWL/NegationGoals.lean`.
A goal certificate proves "no model of O(closure ++ goal)". That this
means `P ⊨ conclusion` is obligation O3 (§ 9): the form laws are proved
(`TableauTheorems.disjointGoal_iff` and its five siblings), the RDF
goal builder is not.

## 3. The Direct Semantics fragment

The fragment is the `Concept` type of `OWL/Tableau.lean`, unchanged,
with the interpretation `Interp.sem` unchanged. Each constructor is a
row of OWL 2 Direct Semantics Table 4 ("Interpreting Class
Expressions", <https://www.w3.org/TR/owl2-direct-semantics/#Class_Expressions>):

| `Concept` | Table 4 row |
| --- | --- |
| `atom c` | a class `C`: `(C)^C` |
| `top`, `bot` | `owl:Thing`, `owl:Nothing` (§ 2.2: `(owl:Thing)^C = Δ_I`, `(owl:Nothing)^C = ∅`) |
| `neg c` | `ObjectComplementOf(CE)`: `Δ_I \ (CE)^C` |
| `conj c d`, `disj c d` | `ObjectIntersectionOf`, `ObjectUnionOf` (binary; an n-ary one is a right fold) |
| `all r c`, `ex r c` | `ObjectAllValuesFrom`, `ObjectSomeValuesFrom` |
| `atLeast n r`, `atMost n r` | `ObjectMinCardinality(n OPE)`, `ObjectMaxCardinality(n OPE)` |
| `atLeastQ n r c`, `atMostQ n r c` | the qualified forms |

`ObjectExactCardinality(n …)` is read as the conjunction of the min and
max forms, which is the Table 4 definition (`= n` is `≥ n` and `≤ n`).

The `Tableau.lean` header cites "Table 5" for class expressions. In the
current Recommendation, Table 5 is "Satisfaction of Class Expression
Axioms"; class expressions are Table 4. This landing corrects the
citation.

The ontology type the checker reads (`OWL/DirectCert.lean`):

```lean
structure DlOntology where
  tbox  : List (Concept × Concept)  -- SubClassOf(C D), Table 5
  rbox  : RoleAxioms                -- SubObjectPropertyOf, TransitiveObjectProperty, Table 6
  abox  : List Assertion            -- ClassAssertion, ObjectPropertyAssertion,
                                    -- DifferentIndividuals, Table 10

def RespectsTBox (I : Interp δ) (T : List (Concept × Concept)) : Prop :=
  ∀ ax ∈ T, ∀ x, I.sem ax.1 x → I.sem ax.2 x

def DirectModel (I : Interp δ) (ν : Ind → δ) (O : DlOntology) : Prop :=
  RespectsRBox I O.rbox ∧ RespectsTBox I O.tbox ∧ SatAll I ν O.abox
```

The axioms the reader produces, each with its Direct Semantics
condition:

| RDF (Mapping to RDF Graphs, Tables 16–18) | axiom | condition |
| --- | --- | --- |
| `C rdfs:subClassOf D` | `(C, D)` | Table 5, `SubClassOf` |
| `C owl:equivalentClass D` | `(C, D)`, `(D, C)` | Table 5, `EquivalentClasses` |
| `C owl:disjointWith D` | `(C ⊓ D, ⊥)` | Table 5, `DisjointClasses` |
| `C owl:complementOf D`, `C owl:unionOf L`, `C owl:intersectionOf L` on an IRI `C` | `(C, E)`, `(E, C)` | Table 5, `EquivalentClasses(C E)` |
| `p rdfs:domain C` | `(∃p.⊤, C)` | Table 6, `ObjectPropertyDomain` |
| `p rdfs:range C` | `(⊤, ∀p.C)` | Table 6, `ObjectPropertyRange` |
| `p rdf:type owl:FunctionalProperty` | `(⊤, ≤1 p)` | Table 6, `FunctionalObjectProperty` |
| `p rdfs:subPropertyOf q` | role box `(p, q)` | Table 6, `SubObjectPropertyOf` |
| `p rdf:type owl:TransitiveProperty` | role box `trans p` | Table 6, `TransitiveObjectProperty` |
| `a rdf:type C` | `inst a C` | Table 10, `ClassAssertion` |
| `a p b`, `p` an object property, `b` not a literal | `rel p a b` | Table 10, `ObjectPropertyAssertion` |
| `a owl:differentFrom b`, `owl:AllDifferent` members | `diff a b` | Table 10, `DifferentIndividuals` |

Every class expression is put in negation normal form by `Concept.nnf`,
a total function with the proved law
`I.sem (Concept.nnf c) x ↔ I.sem c x`. The refuter's labels are in
negation normal form, so the checker must be too, or the certificate's
branch concepts would not match the checker's derived facts.

Outside the fragment, and dropped by the reader: `ObjectOneOf`,
`ObjectHasValue`, `ObjectHasSelf`, inverse object properties (and so
`owl:inverseOf`, `owl:SymmetricProperty`,
`owl:InverseFunctionalProperty`), every data range and data property,
`HasKey`, `SameIndividual`, negative property assertions, property
chains, disjoint properties, reflexive, irreflexive and asymmetric
properties. A refutation that needs one of them does not check.

A blank node in the graph is an individual name of the ABox. Direct
Semantics § 2.4 makes an interpretation a model when SOME
interpretation of the anonymous individuals satisfies the ontology;
`DirectModel` quantifies the assignment `ν` over all names, blank nodes
included, so "no `I`, no `ν`" is exactly "no model" in the § 2.4 sense.

## 4. The rules

A certificate replays the search's CHOICES. The checker recomputes
everything deterministic itself, by a saturation with these forward
rules (each one a constructor-level soundness lemma):

| Rule | From | Infer | Soundness argument |
| --- | --- | --- | --- |
| hypothesis | `φ ∈ A` | `φ` | the model satisfies `A` |
| `conjE` | `a : C ⊓ D` | `a : C`, `a : D` | Table 4, intersection |
| `allE` | `a : ∀r.C`, `r(a, b)` | `b : C` | Table 4, all-values-from |
| `subRoleE` | `r(a, b)`, `r ⊑ s` | `s(a, b)` | Table 6 |
| `transE` | `r(a, b)`, `r(b, e)`, `trans r` | `r(a, e)` | Table 6 |
| `allTransE` | `a : ∀r.C`, `trans r`, `r(a, b)` | `b : ∀r.C` | Table 6 and Table 4 |
| `topI` (new) | `a` named in `A` | `a : ⊤` | `(owl:Thing)^C = Δ_I` |
| `tboxE` (new) | `a : C`, `(C, D) ∈ T` | `a : D` | Table 5, `SubClassOf` |
| `tboxContraE` (new) | `a : nnf(¬D)`, `(C, D) ∈ T` | `a : nnf(¬C)` | Table 5 and the nnf law |
| `exI` (new) | `r(a, b)`, `b : C` | `a : ∃r.C` | Table 4, some-values-from |

and these branching and clash rules, which the certificate names:

| Certificate node | Calculus rule | Soundness argument |
| --- | --- | --- |
| `close` | `clash`, `botClash`, `minMaxClash`, `minMaxClashQ`, `minQMaxClash`, `maxClash`, `maxClashQ` | as in `refuted_sound` |
| `split a C D` | `disjSplit` | one disjunct holds of `ν a` |
| `exWit a r C x` | `exWitness` | `x` fresh; the assignment is changed at `x` only |
| `merge a n r l` | `leqMerge`, over UNORDERED pairs | pigeonhole; `satAll_mergeInds` needs only `ν b = ν c`, which is symmetric |

The `merge` rule asks for one sub-certificate per unordered pair
`{b, c}` of `l`, where `Refuted.leqMerge` asks for both orders. The
pigeonhole step gives a colliding pair with `ν b = ν c`, and the merged
ABox is satisfied for either direction of the merge, so one direction
is enough. The refuter's merge branching explores one direction.

## 5. The certificate and the checker

```lean
inductive Cert where
  | close
  | split (a : Ind) (c d : Concept) (l r : Cert)
  | exWit (a : Ind) (r : Role) (c : Concept) (x : Ind) (k : Cert)
  | merge (a : Ind) (n : Nat) (r : Role) (l : List Ind) (subs : List (Ind × Ind × Cert))

def checkCert (O : DlOntology) (c : Cert) : Bool
```

`checkCert` is total: structural recursion on `Cert`, and the
saturation runs a bounded number of rounds (the bound is a parameter of
the check, not of the certificate, so a certificate cannot ask for an
unbounded computation). Each round applies every forward rule to the
current fact list. `close` asks the saturated facts for a clash.

The theorem (`OWL/DirectCert.lean`):

```lean
theorem checkCert_sound {O : DlOntology} {c : Cert}
    (h : checkCert O c = true) :
    ¬ ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), DirectModel I ν O
```

The proof is the invariant "every fact in the saturation holds in every
model of the current ABox", by induction on the rounds, and then
structural induction on the certificate with the arguments of
`refuted_sound`, case by case.

## 6. Emission

`Refute.search` returns, as an extra output, a trace of what closed:
the state at each clash leaf, and at each union or merge branch point
the state, the node and the alternatives. The verdict and the budget
are computed exactly as before; `tableauConsistent` and `refute`
project them. `OWL/RefuteCert.lean` turns a trace into a certificate:

* the minted existential witnesses of the state (the expansion edges
  that do not count) become `exWit` steps, in creation order, each
  placed before the first branch point whose state contains it;
* a union branch point on `C₁ ⊔ … ⊔ Cₙ` becomes nested `split`s;
* a merge branch point becomes `merge`;
* a clash leaf becomes `close`.

A refutation decided by the graph-level checks (`immediateInconsistency`)
or by the counting rung (`countingRefutes`) has no search trace, so it
has no certificate in this landing.

## 7. Harness reporting

Under `--dl`, for every unit decided by refutation the probe prints one
of

```
PROVED-BY-CERTIFICATE <id>
DECIDED-BY-REFUTER (unchecked) <id>: <reason>
```

and per catalog

```
CERTIFICATE: N certificate-checked, M unchecked (out of T decided by refutation)
```

The verdict is never changed. A unit whose certificate does not check
keeps its pass.

## 8. Measured

(Filled in by the measurement commit of this landing.)

## 9. Open obligations

* O1 — the reader is sound: every axiom `readOntology g` returns is in
  the axiom closure of the ontology that the OWL 2 Mapping to RDF
  Graphs (§ 3, the reverse mapping) assigns to `g`. Issue: (opened with
  this landing).
* O2 — the DL regime's preprocessing preserves Direct Semantics models:
  every model of `Ont(P)` is a model of `Ont(g)`, for the RL closure,
  the class-expression materialisation pass and the re-closure. Issue:
  (opened with this landing).
* O3 — the negation-goal builder is sound: if `Ont(P) ∪ Ont(goal)` has
  no model for every goal of `negationGoals C`, then `Ont(P) ⊨ Ont(C)`.
  Issue: (opened with this landing).
