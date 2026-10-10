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
O2 are open obligations, each with its own issue (§ 9):
<https://github.com/danbri/factoidal/issues/761> and
<https://github.com/danbri/factoidal/issues/762>. O1 is a
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
means `P ⊨ conclusion` is obligation O3 (§ 9,
<https://github.com/danbri/factoidal/issues/763>): the form laws are proved
(`TableauTheorems.disjointGoal_iff` and its five siblings), the RDF
goal builder is not.

## 3. The Direct Semantics fragment

The class expressions are the `Concept` type of `OWL/Tableau.lean`,
unchanged, with the interpretation `Interp.sem` unchanged. Each
constructor is a row of OWL 2 Direct Semantics Table 4 ("Interpreting
Class Expressions",
<https://www.w3.org/TR/owl2-direct-semantics/#Class_Expressions>):

| `Concept` | Table 4 row |
| --- | --- |
| `atom c` | a class `C`: `(C)^C` |
| `top`, `bot` | `owl:Thing`, `owl:Nothing` (§ 2.2: `(owl:Thing)^C = Δ_I`, `(owl:Nothing)^C = ∅`) |
| `neg c` | `ObjectComplementOf(CE)`: `Δ_I \ (CE)^C` |
| `conj c d`, `disj c d` | `ObjectIntersectionOf`, `ObjectUnionOf` (binary; an n-ary one is nested to the right) |
| `all r c`, `ex r c` | `ObjectAllValuesFrom`, `ObjectSomeValuesFrom` |
| `atLeast n r`, `atMost n r` | `ObjectMinCardinality(n OPE)`, `ObjectMaxCardinality(n OPE)` |
| `atLeastQ n r c`, `atMostQ n r c` | the qualified forms |

`ObjectExactCardinality(n …)` is read as the conjunction of the min and
max forms (`= 0` as `≤ 0`, as the refuter's negation normal form does).

Until this landing the `Tableau.lean` header cited "Table 5" for class
expressions. In the current Recommendation, Table 5 is "Satisfaction of
Class Expression Axioms"; class expressions are Table 4. The header is
corrected.

The ontology type (`OWL/DirectCert.lean`):

```lean
structure DlOntology where
  tbox : List (Concept × Concept) := []   -- SubClassOf(C D), Table 5
  rbox : RoleAxioms := RoleAxioms.empty   -- SubObjectPropertyOf, TransitiveObjectProperty, Table 6
  abox : List Assertion := []             -- ClassAssertion, ObjectPropertyAssertion,
                                          -- DifferentIndividuals, Table 10
  inv  : List (Role × Role) := []         -- InverseObjectProperties, Table 6
  same : List (Ind × Ind) := []           -- SameIndividual, Table 10

def RespectsTBox (I : Interp δ) (T) : Prop := ∀ ax ∈ T, ∀ x, I.sem ax.1 x → I.sem ax.2 x
def RespectsInv  (I : Interp δ) (P) : Prop := ∀ q ∈ P, ∀ x y, I.role q.1 x y ↔ I.role q.2 y x
def RespectsSame (ν : Ind → δ) (P)  : Prop := ∀ q ∈ P, ν q.1 = ν q.2

def DirectModel (I : Interp δ) (ν : Ind → δ) (O : DlOntology) : Prop :=
  RespectsRBox I O.rbox ∧ RespectsTBox I O.tbox ∧ RespectsInv I O.inv ∧
  RespectsSame ν O.same ∧ SatAll I ν O.abox
```

A blank node in the graph is an individual name. Direct Semantics § 2.4
makes an interpretation a model when SOME interpretation of the
anonymous individuals satisfies the ontology; `DirectModel` quantifies
the assignment `ν` over all names, blank nodes included, so "no `I`, no
`ν`" is "no model" in the § 2.4 sense.

### What the reader reads

`readOntology` (`OWL/RefuteCert.lean`) reads these rows. A property is
an object property when the graph types it `owl:ObjectProperty` or a
characteristic only object properties carry (transitive, symmetric,
asymmetric, reflexive, irreflexive, inverse-functional), and is not
also typed a data or annotation property. A data property is one typed
`owl:DatatypeProperty`.

| RDF (OWL 2 Mapping to RDF Graphs § 3) | read as | Direct Semantics |
| --- | --- | --- |
| `C rdfs:subClassOf D` | `(C, D)` | Table 5, `SubClassOf` |
| `C owl:equivalentClass D` | `(C, D)`, `(D, C)` | Table 5, `EquivalentClasses` |
| `C owl:disjointWith D`, `owl:AllDisjointClasses` | `(C, ¬D)`, `(D, ¬C)` | Table 5, `DisjointClasses` |
| `C owl:disjointUnionOf (C₁ … Cₙ)` | `C ≡ C₁ ⊔ … ⊔ Cₙ`, `(Cᵢ, ¬Cⱼ)` | Table 5, `DisjointUnion` |
| `C owl:unionOf` / `intersectionOf` / `complementOf` on an IRI `C` | `C ≡ CE` | Table 5, `EquivalentClasses(C CE)` |
| `p rdfs:domain C` | `(∃p.⊤, C)`, `(≥ 1 p, C)` | Table 6, `ObjectPropertyDomain` |
| `p rdfs:range C` | `(⊤, ∀p.C)` | Table 6, `ObjectPropertyRange` |
| `p rdf:type owl:FunctionalProperty` | `(⊤, ≤ 1 p)` | Table 6, `FunctionalObjectProperty` |
| `p rdfs:subPropertyOf q`, `p owl:equivalentProperty q` | role box | Table 6 |
| `p rdf:type owl:TransitiveProperty` | role box | Table 6 |
| `p owl:inverseOf q`; `p rdf:type owl:SymmetricProperty` | `inv (p, q)`; `inv (p, p)` | Table 6 |
| `a rdf:type C` | `inst a C` | Table 10, `ClassAssertion` |
| `a p b`, `p` an object property, `b` not a literal | `rel p a b` | Table 10, `ObjectPropertyAssertion` |
| `a owl:differentFrom b`, `owl:AllDifferent` | `diff a b` | Table 10, `DifferentIndividuals` |
| `a owl:sameAs b` | `same (a, b)` | Table 10, `SameIndividual` |

Two readings are WEAKENINGS, sound for refutation because the read
ontology has a model whenever the original has one:

* **Nominals as class names.** `ObjectOneOf(a₁ … aₙ)` is read as a
  class name `N` (in a `urn:factoidal:owl-cert:one-of:` namespace), and
  `aᵢ : N` is asserted for each member; `ObjectHasValue(p a)` is
  `∃p.N` with `a : N`. From a model of the original, setting
  `(N)^C := {(a₁)^I … (aₙ)^I}` gives a model of the read ontology.
  `Concept` has no nominal constructor; the reading keeps the
  certificate inside `Concept`. This is the shape of the negation goal
  `≤ 0 p.{y}` that `OWL/NegationGoals.lean` writes for `¬p(x, y)`.
* **Data cardinalities as class names.** `DataMinCardinality(n DP)` and
  `DataMaxCardinality(n DP)` are read as class names (namespace
  `urn:factoidal:owl-cert:data-min:` / `data-max:`), with the bridge
  axioms `¬(≥ n DP) ⊑ ≤ n-1 DP`, `¬(≤ m DP) ⊑ ≥ m+1 DP` and
  `≥ n DP ⊑ ¬(≤ m DP)` for `m < n`. Each bridge axiom holds in every
  interpretation (a set of data values has at least `n` elements or at
  most `n - 1`, and not both). `Concept` has one sort, so a data
  property cannot be a role of it.

Every class expression is put in negation normal form by `Concept.nnf`
(`Concept.nnfP`), a total function with the proved law `sem_nnfP`:
`nnfP true c` denotes `c` and `nnfP false c` denotes its complement. The
refuter's labels are in negation normal form, so the checker reads the
TBox in it as well, with each axiom's contrapositive beside it
(`normTBox`, `respects_normTBox`).

Outside the fragment, and dropped by the reader: `ObjectHasSelf`, data
ranges and data property assertions, `HasKey`, negative property
assertions, property chains, disjoint properties, reflexive,
irreflexive and asymmetric properties, and every construct on a
property that is not declared. A refutation that needs one of them does
not check.

## 4. The rules

A certificate replays the search's CHOICES. The checker computes
everything deterministic itself by `saturate`: rounds of the forward
rules, to a fixpoint or `certFuel = 64` rounds. Each rule is a case of
`gen_sound`.

| Rule | From | Infer | Soundness argument |
| --- | --- | --- | --- |
| hypothesis | `φ ∈ A` | `φ` | the model satisfies `A` |
| `conjE` | `a : C ⊓ D` | `a : C`, `a : D` | Table 4, intersection |
| `allE` | `a : ∀r.C`, `r(a, b)` | `b : C` | Table 4, all-values-from |
| `allTransE` | `a : ∀r.C`, `trans r`, `r(a, b)` | `b : ∀r.C` | Table 6 and Table 4 |
| `subRoleE` | `r(a, b)`, `r ⊑ s` | `s(a, b)` | Table 6 |
| `transE` | `r(a, b)`, `r(b, e)`, `trans r` | `r(a, e)` | Table 6 |
| `tboxE` | `a : C`, `(C, D)` in the normalised TBox | `a : D` | Table 5 and the nnf law |
| `topI` | `a` named in a fact | `a : ⊤` | `(owl:Thing)^C = Δ_I` |
| `exI` | `r(a, b)`, `b : C`, `∃r.C` (or `≥ 1 r`, `≥ 1 r.C`) a TBox left-hand side | `a : ∃r.C` | Table 4 |
| `invE` | `r(a, b)`, `inv (r, s)` | `s(b, a)` | Table 6, `InverseObjectProperties` |
| `conjI`, `disjI` | `a : C`, `a : D`, the conjunction (disjunction) a Boolean subterm of a TBox left-hand side | `a : C ⊓ D`; `a : C ⊔ D` | Table 4 |

The clash rules (`clashIn`, `clashIn_sound`): `a : ⊥`; `a : C` beside
`a : ¬C`; `diff a a`; a lower bound against a smaller upper bound on one
role at one individual (`≥ n r`, `≥ n r.C` or `∃r.C` against `≤ m r` or
`≤ m r.C`, `m < n`, the qualified bound only with the same filler); an
upper bound `≤ m r` (`≤ m r.C`) with `m + 1` named successors (in `C`)
that are pairwise `diff`.

The certificate nodes:

| Node | Calculus rule | Soundness argument |
| --- | --- | --- |
| `close` | the clash rules | as in `refuted_sound` |
| `split a C D l r` | `disjSplit` | one disjunct holds of `ν a` |
| `exWit a r C x k` | `exWitness` (from `∃r.C`, `≥ k r.C`, or `≥ k r` / any `∃r.C'` when `C = ⊤`) | `x` fresh; `ν` is changed at `x` only (`satAll_bend`) |
| `merge a n r l cases` | `leqMerge` over UNORDERED pairs, with a `≤ n r` or a `≤ n r.C` bound | pigeonhole; `satAll_mergeInds` needs only `ν b = ν c`, which is symmetric (`boundAt_sound`) |

`checkCert` starts from the ABox in negation normal form with the
`SameIndividual` pairs applied as renamings (`mergeAll`,
`satAll_mergeAll`).

## 5. The checker and the theorem

```lean
mutual
inductive Cert where
  | close
  | split (a : Ind) (c d : Concept) (l r : Cert)
  | exWit (a : Ind) (r : Role) (c : Concept) (x : Ind) (k : Cert)
  | merge (a : Ind) (n : Nat) (r : Role) (l : List Ind) (cases : MergeCases)
inductive MergeCases where
  | nil
  | cons (b c : Ind) (k : Cert) (rest : MergeCases)
end

def checkCert (O : DlOntology) (c : Cert) : Bool :=
  checkF (Ctx.ofOntology O) certFuel (mergeAll O.same (O.abox.map normAssertion)) c

theorem checkCert_sound {O : DlOntology} {c : Cert} (h : checkCert O c = true) :
    ¬ ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), DirectModel I ν O
```

`checkF` is total: structural recursion on the certificate, and the
saturation is bounded by `certFuel`. The proof (`checkF_sound`,
`checkCases_sound`) is the invariant "a model of the current fact list
satisfies every saturated fact", carried by `saturate_sound`, then
structural induction on the certificate. `#print axioms checkCert_sound`
names `propext`, `Classical.choice`, `Quot.sound` (checked by
`#guard_msgs` in `OWL/DirectCertTests.lean`).

## 6. Emission

`Refute.search` returns, beside its verdict and budget, a `SearchTrace`
of what closed: the state at each clash leaf; at each union or merge
branch point the state and the alternatives; and each forced
identification step. The trace of a forced step is passed down as a
continuation, so every self-call of `search` that was a tail call stays
one. `tableauConsistent` is the first projection of
`tableauConsistentTraced`; `refute_eq_false_iff` is unchanged.

`OWL/RefuteCert.lean`:

* the minted existential witnesses of a state become `exWit` steps, in
  creation order, placed before the first branch point that has them
  (a witness on a data property is skipped: it is no individual of the
  fragment);
* a union branch point on `C₁ ⊔ … ⊔ Cₙ` becomes nested `split`s;
* a ≤-rule branch point becomes `merge`, with a bare `close` case for
  each pair the refuter did not branch on (provably different there);
* each forced identification becomes a one-case `merge` at a node with a
  `≤ 1 p` (or `≤ 1 p.C`) label that has both terms as successors;
* a counting-clash leaf (`countingClash`: `≤ k p` against `k + 1`
  pairwise-disjoint existentials) becomes `k + 1` fresh witnesses and a
  `merge` over them;
* a refutation by a graph-level check is tried with a bare `close`
  (the `owl:AllDifferent` with `owl:sameAs` shape checks this way).

The emitter is not trusted: a defect in it can only make a certificate
fail to check.

## 7. Harness reporting

Under `--dl`, for every unit decided by refutation the probe prints,
after the existing `DECIDED-BY-REFUTER` line, one of

```
PROVED-BY-CERTIFICATE <id> [<type>]
DECIDED-BY-REFUTER (unchecked) <id> [<type>]: <reason>
```

then `REFUTATION-PROFILE <id> [<type>]: <clash sources and branch counts>`,
and per catalog

```
CERTIFICATE <catalog>: N certificate-checked, M unchecked (out of T decided by refutation)
  CERTIFICATE-UNCHECKED <catalog> (count): <reason>
  REFUTATION-USES <catalog> (count): <clash source or branch kind>
```

For an entailment the certificate line covers every negation goal; one
goal without a checked certificate makes the unit unchecked. The
verdict is never changed: every line the probe printed before this
landing is byte-identical (§ 8). `OWL_CERT_DEBUG=1` prints, for an
unchecked unit, the read ontology's size, the certificate, the
refuter's clash site and the checker's facts about that node.

## 8. Measured

FILLED_BY_MEASUREMENT

## 9. Open obligations and open rules

* O1 — the reader is sound: every axiom `readOntology g` returns holds
  in every Direct Semantics model of the ontology the OWL 2 Mapping to
  RDF Graphs (§ 3, the reverse mapping) assigns to `g`, including the
  two weakenings of § 3.
  <https://github.com/danbri/factoidal/issues/761>
* O2 — the DL regime's preprocessing (RL closure, class-expression
  materialisation, RL closure) keeps Direct Semantics models.
  <https://github.com/danbri/factoidal/issues/762>
* O3 — the negation-goal builder is sound: if every goal ontology has
  no model, the premise entails the conclusion.
  <https://github.com/danbri/factoidal/issues/763>
* The refutations the checker cannot certify yet (datatype value spaces,
  the counting rung, the propositional clash, nominal identity, the
  min-sum counting clash and the `≥ k` generating rule with
  pairwise-different witnesses, two graph-level checks).
  <https://github.com/danbri/factoidal/issues/764>. The expected-failure
  guard in `OWL/RefuteCertTests.lean` names it.

No sub-lemma of the checker was left open: every rule in § 4 has its
soundness case in `checkF_sound`, and no `sorry`, `axiom`,
`native_decide`, `unsafe`, `implemented_by` or new `partial def` was
added.
