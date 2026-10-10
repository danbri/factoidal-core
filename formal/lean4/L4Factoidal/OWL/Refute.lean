/-
L4Factoidal.OWL.Refute — the OWL DL REFUTATION calculus, wave 1.

Port of `formal/fstar/Tableau.Refute.fst` — step 3 of
https://github.com/danbri/factoidal/issues/548 . Where
`L4Factoidal/OWL/Materialise.lean` is positive-sound only (it writes
entailed memberships and never detects unsatisfiability), this module
answers the other question: does this graph have a model?

## The verdicts (three-valued since 2026-08-25, issue 586)

`tableauConsistent` answers `Option Bool`, with the SAME meanings as
the F* `Tableau_Refute.tableau_consistent` verdict it mirrors:

* `some false` — REFUTED. A clash was derived on every branch, or a
  graph-level violation was found. The contract is that `some false`
  implies the graph has no model under OWL 2 Direct Semantics, and
  every rule that can contribute to one carries its model-theoretic
  argument beside it. This is the only verdict wired into suite
  scoring.
* `some true` — the expansion saturated and every branch point was
  explored to quiescence with no clash: the search state IS a
  candidate model. NOT a completeness guarantee — the calculus
  derives fewer consequences than OWL 2 DL, so an unsatisfiable
  graph outside its reach also answers `some true`. Callers may
  report it (the wire contract's `consistent: true`) but must not
  score "consistent" on it beyond what they already do by default.
* `none` — the budget ran out before the answer was determined.
  Indeterminate, never to be collapsed into either Boolean.

`refute` is the refutation-only VIEW of the same search (defined
through `tableauConsistent`; one search path, no duplicate
dispatch): `some false` = refuted, `none` = not refuted, quiescence
and budget-out deliberately indistinguishable. The harness's
inconsistency judges consume this view.

An earlier revision of this header argued for withholding
`some true` entirely. The wire contract decided otherwise
(`owlIsConsistent` must report `consistent: true|false|null`,
matching `bin/npm-entry/entry_jsoo.ml`), and the misuse the argument
feared is prevented by contract instead: the `some true` doc above
and the F* original both pin what it does NOT mean.

## Relation to the declarative calculus (`OWL/Tableau.lean`)

`OWL/Tableau.lean` is the PROOF HOME: the `Derives`/`Refuted` clash
calculus over the OWL 2 Direct Semantics fragment of names, Boolean
connectives, value restrictions and (qualified) cardinality, with
soundness proofs in `TableauTheorems.lean`. This module is the
EXECUTABLE engine over RDF graphs. On the shared fragment each
procedural clash source corresponds to a `Refuted` constructor:

* `clashForLabel` complement arm ↔ `Refuted.clash`;
* `owl:Nothing` label arm ↔ `Refuted.botClash`;
* min/max label pairs (`existsMaxLt`/`existsMaxQualLt`) ↔
  `Refuted.minMaxClash` / `.minMaxClashQ` / `.minQMaxClash`;
* counted provably-distinct successors over a `≤ k` label ↔
  `Refuted.maxClash` / `.maxClashQ`;
* `search`'s union branching ↔ `Refuted.disjSplit`;
* the ≤-rule witness merge (`pendingMerge`/`mergeInto`) ↔
  `Refuted.leqMerge`;
* `ensureWitnesses` ↔ `Refuted.exWitness`.

The procedural fragment is WIDER (nominal size rules, the datatype
value-space clashes C5/C6, the graph-level violations G1–G9, TBox
unfolding via `collectAxioms`, inverse roles) and, inside the shared
fragment, weaker only through its caps (witness depth ≤ 3, ≤ 6
generated witnesses, the threaded budget) — caps withhold
refutations, never invent them. `RefuteTests.lean` keeps an
instance-level paired witness: one input refuted here by `#guard`
and refuted in the calculus by an explicit `Refuted` derivation. The
general linkage — an abstraction from a clash trace to a serialisable
`Refuted` derivation, `refute g b = some false → Refuted R A` on the
shared fragment — is the certificate-checker rung
`OWL/Tableau.lean`'s header names; tracked as follow-up 6 on
https://github.com/danbri/factoidal/issues/586 .

## What is NOT here, named

The F* module carries several more waves. Each ABSENCE only makes
refutation harder — the calculus derives fewer clashes, never wrong
ones — so this port is sound with respect to the `some false`
contract while answering `none`/`some true` where the F* engine
answers `Some false`:

* nominal (`owl:oneOf`) BRANCHING: the choice of member is decided
  instead by the identity clash (`nominalClash`, a clause search over
  "these two terms denote one element"), and a node with a singleton
  nominal is identified with its member (`forcedIdentifications`);
* DPLL-style branch ordering for unions: the propositional clash
  (`propositionalClash`) decides a node's disjunction labels and TBox
  clauses by unit propagation instead.

Landed 2026-10-10 (`docs/designissues/2026-09-07-lean-owl-corpus-gap.md`
§ 14): the `≥ k` generating rule with pairwise-different witnesses,
`∃p.{a}` as a counted edge to `a`, deterministic identification under
`≤ 1` bounds, the propositional and nominal clashes, the
disjoint-data-property and negative-assertion value exclusions with the
`xsd:pattern` language check, and the class-size counting rung
(`countingRefutes`). (The ≤-rule itself and the datatype
facet/cardinality clashes were on this list until 2026-08-23.)

## Every label is in negation normal form

After `nnf`, `complement` wraps only a named class, a `hasValue`, a
`oneOf` or a `dataRestriction` — so the complement clash reduces to
structural matching rather than a search. `nnfNeg` of an unreadable
expression is `unknown`, which DROPS the constraint: dropping one can
only lose clashes, never invent them.
-/
import L4Factoidal.OWL.ClassExpr
import L4Factoidal.XSD.Facets
import L4Factoidal.Regex.XSDPattern
import L4Factoidal.Regex.Exec
import L4Factoidal.OWL.CountingOracle

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.XSD

/-! ## Vocabulary this module needs and `OWL/Vocabulary.lean` does not
carry -/

def owlAllDifferent : WfIri := ⟨"http://www.w3.org/2002/07/owl#AllDifferent", rfl⟩
def owlDistinctMembers : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#distinctMembers", rfl⟩
def owlHasSelf : WfIri := ⟨"http://www.w3.org/2002/07/owl#hasSelf", rfl⟩
def owlAllDisjointProperties : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AllDisjointProperties", rfl⟩
def owlBottomObjectProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#bottomObjectProperty", rfl⟩
def owlBottomDataProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#bottomDataProperty", rfl⟩
def owlTopObjectProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#topObjectProperty", rfl⟩

/-- `EXT(owl:bottomObjectProperty) = EXT(owl:bottomDataProperty) = ∅`
    in every model, so any obligation to HAVE a successor on one is
    unsatisfiable and any asserted triple over one is false. -/
def isBottomProp (p : WfIri) : Bool :=
  p == owlBottomObjectProperty || p == owlBottomDataProperty

/-! ## Negation normal form

Each rewrite is the corresponding Direct Semantics identity:
`¬⊤ = ⊥`, `¬¬C = C`, `¬(C ⊓ D) = ¬C ⊔ ¬D`, `¬∃p.C = ∀p.¬C`,
`¬(≥ k p) = (≤ k-1 p)` for `k ≥ 1` and `⊥` for `k = 0`,
`¬(≤ k p) = (≥ k+1 p)`, and `= k p` is `(≥ k p) ⊓ (≤ k p)`. -/

mutual

partial def nnf : ClassExpr → ClassExpr
  | .complement d      => nnfNeg d
  | .intersection cs   => .intersection (cs.map nnf)
  | .union cs          => .union (cs.map nnf)
  | .someOf p d        => .someOf p (nnf d)
  | .allOf p d         => .allOf p (nnf d)
  | .minQualCard k p d => .minQualCard k p (nnf d)
  | .maxQualCard k p d => .maxQualCard k p (nnf d)
  -- `= 0 p` is `≤ 0 p` EXACTLY: `≥ 0 p` holds of every individual in
  -- every model, so keeping it as a conjunct puts a tautology into
  -- the label set. That is not cosmetic — an axiom's left-hand side
  -- is matched by structural equality, so a node that derives
  -- `≤ 0 p` could never match an axiom written `⊓[≥ 0 p, ≤ 0 p]`.
  | .exactCard k p     =>
      if k == 0 then .maxCard 0 p
      else .intersection [.minCard k p, .maxCard k p]
  | .exactQualCard k p d =>
      let d' := nnf d
      if k == 0 then .maxQualCard 0 p d'
      else .intersection [.minQualCard k p d', .maxQualCard k p d']
  | c => c

partial def nnfNeg : ClassExpr → ClassExpr
  | .named x =>
      if x == owlThing then .named owlNothing
      else if x == owlNothing then .named owlThing
      else .complement (.named x)
  | .complement d      => nnf d
  | .intersection cs   => .union (cs.map nnfNeg)
  | .union cs          => .intersection (cs.map nnfNeg)
  | .someOf p d        => .allOf p (nnfNeg d)
  | .allOf p d         => .someOf p (nnfNeg d)
  | .hasValue p v      => .complement (.hasValue p v)
  | .minCard k p       => if k == 0 then .named owlNothing else .maxCard (k - 1) p
  | .maxCard k p       => .minCard (k + 1) p
  | .exactCard k p     =>
      if k == 0 then .minCard 1 p
      else .union [.maxCard (k - 1) p, .minCard (k + 1) p]
  | .minQualCard k p d =>
      if k == 0 then .named owlNothing else .maxQualCard (k - 1) p (nnf d)
  | .maxQualCard k p d => .minQualCard (k + 1) p (nnf d)
  | .exactQualCard k p d =>
      let d' := nnf d
      if k == 0 then .minQualCard 1 p d'
      else .union [.maxQualCard (k - 1) p d', .minQualCard (k + 1) p d']
  -- A nominal and a facet-restricted datatype have no closed-form
  -- negation in this AST, so they are WRAPPED and treated as atomic.
  -- Nothing is dropped.
  | .oneOf ms          => .complement (.oneOf ms)
  | .dataRestriction dt fs => .complement (.dataRestriction dt fs)
  -- An unreadable expression's negation DROPS the constraint. Fewer
  -- constraints means fewer clashes, never a wrong one.
  | .unknown           => .unknown

end

/-! ## Structural equality, and why `unknown` is not equal to itself

`ClassExpr.beq` says two `unknown`s match, which is the right answer
for a syntactic comparison. It is the wrong one HERE: two
unparseable expressions are no evidence of denoting the same class,
and a refuter that treated them as one could close a branch on a
coincidence of failure. `ceEq` is `beq` with that one case removed,
and it is what every clash and axiom match uses. -/

mutual

partial def ceDefinite : ClassExpr → Bool
  | .unknown            => false
  | .someOf _ d         => ceDefinite d
  | .allOf _ d          => ceDefinite d
  | .complement d       => ceDefinite d
  | .minQualCard _ _ d  => ceDefinite d
  | .maxQualCard _ _ d  => ceDefinite d
  | .exactQualCard _ _ d => ceDefinite d
  | .intersection ds    => ceListDefinite ds
  | .union ds           => ceListDefinite ds
  | _                   => true

partial def ceListDefinite : List ClassExpr → Bool
  | []      => true
  | c :: tl => ceDefinite c && ceListDefinite tl

end

def ceEq (a b : ClassExpr) : Bool := ceDefinite a && ClassExpr.beq a b

/-- A shallow key: the constructor, with the property or class IRI it
    carries. `ClassExpr.beq a b` implies `ceIndexKey a = ceIndexKey b`,
    because the key reads only fields `beq` compares for equality, so
    a label meets every antecedent it can equal in its own bucket. -/
def ceIndexKey : ClassExpr → String
  | .named c                => "N" ++ c.val
  | .complement (.named c)  => "C" ++ c.val
  | .complement _           => "C"
  | .someOf p _             => "S" ++ p.val
  | .allOf p _              => "A" ++ p.val
  | .hasValue p _           => "H" ++ p.val
  | .intersection _         => "I"
  | .union _                => "U"
  | .minCard _ p            => "m" ++ p.val
  | .maxCard _ p            => "x" ++ p.val
  | .exactCard _ p          => "e" ++ p.val
  | .minQualCard _ p _      => "q" ++ p.val
  | .maxQualCard _ p _      => "r" ++ p.val
  | .exactQualCard _ p _    => "s" ++ p.val
  | .oneOf _                => "O"
  | .dataRestriction d _    => "D" ++ d.val
  | .unknown                => "?"

/-- The index property `applyAxioms` relies on: an antecedent equal
    to a label under `ClassExpr.beq` is in the label's bucket. -/
theorem ceIndexKey_of_beq (a b : ClassExpr) (h : ClassExpr.beq a b = true) :
    ceIndexKey a = ceIndexKey b := by
  cases a <;> cases b <;> simp_all [ClassExpr.beq, ceIndexKey]
  rename_i a' b'
  cases a' <;> cases b' <;> simp_all [ClassExpr.beq]


mutual
/-- A structural hash of a class expression, for the per-node label
    index (`RNode.byHash`). It reads every field `ClassExpr.beq`
    compares, so `beq`-equal expressions hash alike
    (`ClassExpr.hashCe_of_beq`) and a label is always in the bucket of
    its own hash. -/
def ClassExpr.hashCe : ClassExpr → UInt64
  | .named c              => mixHash 1 (hash c.val)
  | .someOf p c           => mixHash (mixHash 2 (hash p.val)) (ClassExpr.hashCe c)
  | .allOf p c            => mixHash (mixHash 3 (hash p.val)) (ClassExpr.hashCe c)
  | .hasValue p v         => mixHash (mixHash 4 (hash p.val)) (hash v)
  | .intersection cs      => mixHash 5 (ClassExpr.hashCeList cs)
  | .union cs             => mixHash 6 (ClassExpr.hashCeList cs)
  | .complement c         => mixHash 7 (ClassExpr.hashCe c)
  | .minCard n p          => mixHash (mixHash 8 (hash n)) (hash p.val)
  | .maxCard n p          => mixHash (mixHash 9 (hash n)) (hash p.val)
  | .exactCard n p        => mixHash (mixHash 10 (hash n)) (hash p.val)
  | .minQualCard n p c    => mixHash (mixHash (mixHash 11 (hash n)) (hash p.val)) (ClassExpr.hashCe c)
  | .maxQualCard n p c    => mixHash (mixHash (mixHash 12 (hash n)) (hash p.val)) (ClassExpr.hashCe c)
  | .exactQualCard n p c  => mixHash (mixHash (mixHash 13 (hash n)) (hash p.val)) (ClassExpr.hashCe c)
  | .oneOf vs             => mixHash 14 (hash vs)
  | .dataRestriction d f  => mixHash (mixHash 15 (hash d.val)) (hash f)
  | .unknown              => 16

def ClassExpr.hashCeList : List ClassExpr → UInt64
  | []      => 17
  | x :: xs => mixHash (ClassExpr.hashCe x) (ClassExpr.hashCeList xs)
end

mutual
theorem ClassExpr.hashCe_of_beq : (a b : ClassExpr) → ClassExpr.beq a b = true →
    ClassExpr.hashCe a = ClassExpr.hashCe b
  | .someOf p a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.and_eq_true, Bool.false_eq_true] at h
      rename_i q c
      have ih := ClassExpr.hashCe_of_beq a c h.2
      simp_all [ClassExpr.hashCe]
  | .allOf p a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.and_eq_true, Bool.false_eq_true] at h
      rename_i q c
      have ih := ClassExpr.hashCe_of_beq a c h.2
      simp_all [ClassExpr.hashCe]
  | .complement a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.false_eq_true] at h
      rename_i c
      have ih := ClassExpr.hashCe_of_beq a c h
      simp_all [ClassExpr.hashCe]
  | .minQualCard n p a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.and_eq_true, Bool.false_eq_true] at h
      rename_i m q c
      have ih := ClassExpr.hashCe_of_beq a c h.2
      simp_all [ClassExpr.hashCe]
  | .maxQualCard n p a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.and_eq_true, Bool.false_eq_true] at h
      rename_i m q c
      have ih := ClassExpr.hashCe_of_beq a c h.2
      simp_all [ClassExpr.hashCe]
  | .exactQualCard n p a, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.and_eq_true, Bool.false_eq_true] at h
      rename_i m q c
      have ih := ClassExpr.hashCe_of_beq a c h.2
      simp_all [ClassExpr.hashCe]
  | .intersection as, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.false_eq_true] at h
      rename_i bs
      have ih := ClassExpr.hashCeList_of_beqList as bs h
      simp_all [ClassExpr.hashCe]
  | .union as, b, h => by
      cases b <;> simp only [ClassExpr.beq, Bool.false_eq_true] at h
      rename_i bs
      have ih := ClassExpr.hashCeList_of_beqList as bs h
      simp_all [ClassExpr.hashCe]
  | .named _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .hasValue _ _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .oneOf _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .dataRestriction _ _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .minCard _ _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .maxCard _ _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .exactCard _ _, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]
  | .unknown, b, h => by cases b <;> simp_all [ClassExpr.beq, ClassExpr.hashCe]

theorem ClassExpr.hashCeList_of_beqList : (as bs : List ClassExpr) →
    ClassExpr.beqList as bs = true → ClassExpr.hashCeList as = ClassExpr.hashCeList bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [ClassExpr.beqList, Bool.and_eq_true] at h
      have ih1 := ClassExpr.hashCe_of_beq a b h.1
      have ih2 := ClassExpr.hashCeList_of_beqList as bs h.2
      simp [ClassExpr.hashCeList, ih1, ih2]
  | [], _ :: _, h => by simp [ClassExpr.beqList] at h
  | _ :: _, [], h => by simp [ClassExpr.beqList] at h
end

/-! ## The tableau state -/

structure RNode where
  id     : Subject
  /-- Invariant: every label is in negation normal form. -/
  labels : List ClassExpr
  /-- The labels by `ClassExpr.hashCe`. Invariant (kept by
      `RNode.ofLabels` and `addLabel`): `byHash` holds exactly the
      labels, each in the bucket of its hash. The duplicate test of
      `addLabel` reads one bucket instead of the whole label list: a
      node of the wine fixtures carries 150 labels, and the test ran
      for every label every rule wrote, every round. -/
  byHash : Std.HashMap UInt64 (List ClassExpr) := {}

/-- A node with the given labels and their hash index. -/
def RNode.ofLabels (i : Subject) (ls : List ClassExpr) : RNode :=
  { id := i, labels := ls,
    byHash := ls.foldl (fun m l =>
      let h := ClassExpr.hashCe l
      m.insert h (l :: m.getD h [])) {} }

/-- An edge the expansion created. `counts` separates a
    `hasValue`-derived edge, which holds in EVERY model and may
    therefore be counted against a cardinality bound, from an
    existential witness, which may coincide with an existing
    successor in some model and is used only to carry `∀`
    propagation. Counting a witness would fabricate cardinality
    clashes. -/
structure REdge where
  s      : Subject
  p      : WfIri
  o      : Term
  counts : Bool

structure RState where
  /-- The nodes in creation order. `pos` maps a node's subject to its
      index here; `addLabel`, `addNode` and `initState` keep the two in
      step, and nothing else adds a node. The list scans these replace
      (`find?` per label read, `map` per label write) made every label
      operation linear in the node count, which is what an expansion
      round spends its time on. -/
  nodes      : Array RNode := #[]
  pos        : Std.HashMap Subject Nat := {}
  /-- The expansion's edges in creation order, and the same edges by
      subject and by object (`pushEdge` writes all three). The
      successor and predecessor reads go through the two maps. -/
  extra      : Array REdge := #[]
  extraOut   : Std.HashMap Subject (Array REdge) := {}
  extraIn    : Std.HashMap Term (Array REdge) := {}
  fresh      : Nat := 0
  /-- Witness depth per minted blank node. An ABox individual is at
      depth 0. The cap is what stops a cyclic TBox (`X ⊑ ∃p.X`) from
      growing an infinite `∃`-chain. Refusing a witness only
      withholds labels. -/
  wdepth     : Std.HashMap BNodeId Nat := {}
  inv        : List (WfIri × WfIri) := []
  subprop    : List (WfIri × WfIri) := []
  transProps : List WfIri := []
  funcProps  : List WfIri := []
  /-- Declared `owl:InverseFunctionalProperty` IRIs: every element has
      at most one `p`-PREDECESSOR (`forcedIdentifications`,
      `inverseFunctionalClash`). -/
  invFuncProps : List WfIri := []
  /-- Declared `rdfs:range` pairs. A range confines a property's
      fillers to a datatype, which is what lets the value-space rules
      bound them. -/
  ranges     : List (WfIri × WfIri) := []
  /-- `p ↦ {q | q ⊑* p}` and `p ↦ {q | p ⊑* q}`, computed ONCE at
      `initState` for every property the subproperty table mentions.
      Both closures are fixpoints over that table, and the clash rules
      ask for them once per property per node per ROUND — recomputing
      them there put `type-inconsistency` from 6 seconds to 79. A
      property in no subproperty pair is absent from the table and
      falls back to `[p]`, which is what the fixpoint returns for
      it. -/
  subClosure : List (WfIri × List WfIri) := []
  supClosure : List (WfIri × List WfIri) := []
  /-- The INDEXED view of the input graph, built once. The successor
      lookups and the `owl:differentFrom` test run per label per node
      per round, and a list scan of the whole graph at each of them
      is what made `type-inconsistency` take 78 seconds. -/
  store      : Store := Store.ofGraph []
  /-- Terms this branch HYPOTHESISES to denote one domain element,
      as (absorbed, representative) pairs. The ≤-rule writes them;
      `labelsOf` and `successorsOf` read them.

      Identification is done at READ TIME, not by rewriting edges.
      An edge asserted in the input graph cannot be rewritten at all,
      and the materialisation pass puts its own existential witnesses
      INTO the graph — so an edge-rewriting merge silently missed
      every successor that came from there, which is most of them on
      the real path. Pooling at read time covers both.

      Invariant (kept by `mergeInto`): the representative of every
      pair is a ROOT, a term absorbed by no pair. So `repOf` is one
      lookup and a group is read in one pass over the list. -/
  ident      : List (Term × Term) := []
  /-- The TBox `collectAxioms` read, as (antecedent, consequent)
      pairs. `search` carries it as an argument; the clash rules need
      it too, and a clash rule cannot take one more argument without
      threading it through `clashNodes`, so it is carried here as
      well. Written once, by `tableauConsistent`. -/
  tbox       : List (ClassExpr × ClassExpr) := []
  /-- Groups of witnesses that ONE firing of the `≥ k p` generating
      rule minted, `k ≥ 2`. OWL 2 Direct Semantics §2.2 interprets
      `ObjectMinCardinality(k p)` at `x` as `#{y | ⟨x,y⟩ ∈ (p)ᴵ} ≥ k`:
      in every model `x` has `k` PAIRWISE DIFFERENT `p`-successors. The
      group's members stand for those `k` elements, so two members of
      one group are provably different (`genDistinct`). Port of the F*
      `rs_gendistinct` field (`Tableau.Refute.fst`). -/
  distinctGroups : List (List Term) := []

def maxWitnessDepth : Nat := 3
def maxGeneratedWitnesses : Nat := 6

/-! ## Label bookkeeping -/

def memCe (c : ClassExpr) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => ceEq c l)

/-- The representative of a term under this branch's
    identifications. One lookup, by the `RState.ident` invariant: the
    representative stored in a pair is already a root. -/
def repOf (st : RState) (t : Term) : Term :=
  match st.ident.find? (fun q => q.1 == t) with
  | some (_, r) => r
  | none        => t

/-- Every term identified with `t`, `t` included: the root and every
    term the root absorbed. -/
def identifiedWith (st : RState) (t : Term) : List Term :=
  if st.ident.isEmpty then [t]
  else
    let r := repOf st t
    r :: st.ident.filterMap (fun q => if q.2 == r then some q.1 else none)

/-- One node per identification group, the first in node order.

    Every rule reads a node's labels and successors POOLED across its
    group (`labelsOf`, `successorsOf`), so visiting a second member of
    a group repeats the first member's work on the same pooled sets.
    With a group of `n` members that is `n` times the work, and a
    nominal can put dozens of witnesses in one group with a named
    individual (`WebOnt-description-logic-910`). The rules visit the
    leaders. -/
def groupLeaders (st : RState) : List RNode :=
  if st.ident.isEmpty then st.nodes.toList
  else
    (st.nodes.foldl (fun (acc : List RNode × List Term) n =>
      let r := repOf st n.id.toTerm
      if acc.2.contains r then acc else (n :: acc.1, r :: acc.2)) ([], [])).1.reverse

/-- `addLabel` keeps ONE entry per subject, so the unidentified case
    is a LOOKUP and not a gather. The `filter`-then-`flatMap` version
    this replaces scanned the whole node list to the end every time,
    and `clashNodes` calls it once per node — quadratic in the node
    count, per round.

    With identifications present the read is POOLED across the group:
    once two terms are identified, a clash entailed by the UNION of
    their labels has to be visible from either one. -/
def labelsOf (st : RState) (i : Subject) : List ClassExpr :=
  let own (j : Subject) : List ClassExpr :=
    match st.pos.get? j with
    | some k => (st.nodes[k]?.map (·.labels)).getD []
    | none   => []
  if st.ident.isEmpty then own i
  else ((identifiedWith st i.toTerm).filterMap termAsSubject).flatMap own

/-- `(labelsOf st i).any (ClassExpr.beq c)`, read through the label
    hash index of each node in `i`'s identification group: by
    `ClassExpr.hashCe_of_beq` a label equal to `c` is in the bucket of
    `c`'s hash. -/
def hasLabel (st : RState) (i : Subject) (c : ClassExpr) : Bool :=
  let h := ClassExpr.hashCe c
  let own (j : Subject) : Bool :=
    match st.pos.get? j with
    | some k =>
      match st.nodes[k]? with
      | some n => (n.byHash.getD h []).any (ClassExpr.beq c)
      | none   => false
    | none => false
  if st.ident.isEmpty then own i
  else ((identifiedWith st i.toTerm).filterMap termAsSubject).any own

/-- Add one label. `unknown` is never stored: it constrains nothing
    and would only make the label sets longer. The Boolean says
    whether the state changed, which is what the expansion loop's
    stopping rule reads. -/
def addLabel (st : RState) (i : Subject) (c : ClassExpr) : RState × Bool :=
  match c with
  | .unknown => (st, false)
  | _ =>
    -- The duplicate test is SYNTACTIC (`ClassExpr.beq`), not `ceEq`:
    -- `ceEq` refuses to equate two expressions containing `unknown`
    -- (the right answer for a clash), so with it a label such as
    -- `∀p.unknown` was never found present, was re-added on every
    -- pass, and the expansion reported a change forever until the
    -- budget ran out. Storing a label once is a bookkeeping question,
    -- not a semantic one.
    if hasLabel st i c then (st, false)
    else
      let h := ClassExpr.hashCe c
      -- Take the array out of the state before changing it, so the
      -- update is done in place when nothing else holds the array.
      let nodes := st.nodes
      let st := { st with nodes := #[] }
      match st.pos.get? i with
      | some k =>
          ({ st with nodes := nodes.modify k (fun n =>
               { n with labels := n.labels ++ [c],
                        byHash := n.byHash.insert h (c :: n.byHash.getD h []) }) },
           true)
      | none =>
          ({ st with nodes := nodes.push (RNode.ofLabels i [c]),
                     pos := st.pos.insert i nodes.size }, true)

/-! ## The role box

A declared `owl:inverseOf` or `rdfs:subPropertyOf` pair is schema
level: collected once and read-only for the rest of the run. The RL
closure already applies them to the triples the document asserts;
these tables are what makes the edges the EXPANSION creates
role-aware, which the closure never sees. -/

def collectPairs (g : Graph) (pred : WfIri) : List (WfIri × WfIri) :=
  g.filterMap (fun t =>
    if t.p == pred then
      match t.s, t.o with
      | .iri a, .iri b => some (a, b)
      | _, _           => none
    else none)

def collectTypedIris (g : Graph) (cls : WfIri) : List WfIri :=
  g.filterMap (fun t =>
    if t.p == rdfType && t.o == Term.iri cls then
      match t.s with
      | .iri a   => some a
      | .bnode _ => none
    else none)

def inversesOf (inv : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  inv.filterMap (fun (a, b) =>
    if a == p then some b else if b == p then some a else none)

/-- The reflexive-transitive closure of `rdfs:subPropertyOf` BELOW
    `p`: every `q` with `EXT(q) ⊆ EXT(p)` in every model, so a
    `q`-edge counts wherever a `p`-successor is asked for. -/
partial def subpropertiesOfRaw (sp : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  let rec go (acc : List WfIri) (fuel : Nat) : List WfIri :=
    match fuel with
    | 0     => acc
    | n + 1 =>
      let more := sp.filterMap (fun (a, b) =>
        if acc.contains b && !(acc.contains a) then some a else none)
      if more.isEmpty then acc else go (acc ++ more.eraseDups) n
  go [p] (sp.length + 1)

/-- The reflexive-transitive closure of `rdfs:subPropertyOf` ABOVE
    `p`: every `q` with `EXT(p) ⊆ EXT(q)`, so a `∀q.D` binds every
    `p`-filler too. -/
partial def superpropertiesOfRaw (sp : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  let rec go (acc : List WfIri) (fuel : Nat) : List WfIri :=
    match fuel with
    | 0     => acc
    | n + 1 =>
      let more := sp.filterMap (fun (a, b) =>
        if acc.contains a && !(acc.contains b) then some b else none)
      if more.isEmpty then acc else go (acc ++ more.eraseDups) n
  go [p] (sp.length + 1)

/-- The memoised lookups. A property absent from the table is in no
    subproperty pair, and the fixpoint returns `[p]` for it. -/
def subsOf (st : RState) (p : WfIri) : List WfIri :=
  match st.subClosure.find? (fun q => q.1 == p) with
  | some (_, xs) => xs
  | none         => [p]

def supsOf (st : RState) (p : WfIri) : List WfIri :=
  match st.supClosure.find? (fun q => q.1 == p) with
  | some (_, xs) => xs
  | none         => [p]

/-- The `p`-successors of `i`: the graph's `q`-edges for every
    `q ⊑* p`, the inverse direction of each, and the expansion's own
    edges. `counted` restricts the result to what a cardinality bound
    may be measured against. -/
def successorsOf (_g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (counted : Bool) : List Term :=
  let roles := subsOf st p
  let selves := (identifiedWith st i.toTerm).filterMap termAsSubject
  let fromGraph := selves.flatMap (fun j =>
    roles.flatMap (fun r => (st.store.withSubjPred j r).map (·.o)))
  let viaInverse := selves.flatMap (fun j =>
    roles.flatMap (fun r =>
      (inversesOf st.inv r).flatMap (fun r' =>
        (st.store.withPredObj r' j.toTerm).map (·.s.toTerm))))
  let fromExtra := selves.flatMap (fun j =>
    (st.extraOut.getD j #[]).toList.filterMap (fun e =>
      if roles.contains e.p && (!counted || e.counts) then some e.o else none))
  -- The inverse direction of an EXPANSION edge. `viaInverse` above
  -- reads it off the input graph only, so a witness minted on `invR`
  -- was invisible when the witness's own `r`-successors were asked
  -- for. That is the shape of the OilEd inverse-role fixtures:
  -- `x invR y` mints `y`, and `y`'s `r`-successors must include `x`.
  -- `Inv(r') = r` holds in every model, so the edge `(a, r', b)`
  -- entails `(b, r, a)` and reading it back is sound.
  let inverseRoles := roles.flatMap (fun r => inversesOf st.inv r)
  let fromExtraInverse := selves.flatMap (fun j =>
    (st.extraIn.getD j.toTerm #[]).toList.filterMap (fun e =>
      if inverseRoles.contains e.p && (!counted || e.counts)
      then some e.s.toTerm else none))
  let raw := (fromGraph ++ viaInverse ++ fromExtra ++ fromExtraInverse).eraseDups
  -- Identified successors collapse to ONE term, which is what makes a
  -- merge REDUCE the count a `≤ k` bound is measured against.
  if st.ident.isEmpty then raw else (raw.map (repOf st)).eraseDups

/-- `Trans(r)` holds for `r` and for its inverse alike. -/
def roleIsTransitive (st : RState) (r : WfIri) : Bool :=
  st.transProps.contains r || (inversesOf st.inv r).any (st.transProps.contains ·)

/-! ## Provable distinctness

No unique-name assumption: two different IRIs may denote one
individual. Distinctness must be PROVED, and there are two ways to
prove it here — an `owl:differentFrom` assertion, and two literals
whose lexical forms differ under the same datatype. -/

def differentFromAsserted (g : Graph) (a b : Term) : Bool :=
  g.any (fun t =>
    t.p == owlDifferentFrom &&
    ((t.s.toTerm == a && t.o == b) || (t.s.toTerm == b && t.o == a)))


/-- Datatypes whose LEXICAL MAPPING is injective: distinct literals
    in the lexical space map to distinct members of the value space,
    so lexical inequality entails value inequality.

    XSD Datatypes §2.1 to §2.3 give each datatype a lexical space, a
    value space, and a lexical mapping from the first to the second.
    That mapping is many-to-one for most datatypes. `"1"` and `"01"`
    are distinct literals in the lexical space of `xsd:integer` and
    map to one value; `"1.0"` and `"1.00"` likewise for
    `xsd:decimal`; two `rdf:XMLLiteral` literals differing only in
    insignificant whitespace map to one value after exclusive XML
    canonicalization.

    The lexical mapping of `xsd:string` is injective, so `"colour"`
    and `"color"` are distinct values there. That is why the test is
    per-datatype and not general.

    The first version of this predicate returned `true` for every
    datatype. `WebOnt-miscellaneous-202` asserts a CONSISTENT premise
    with a functional datatype property whose two asserted values are
    the same `rdf:XMLLiteral` written with different whitespace. The
    predicate reported them distinct, the cardinality clash fired,
    and the refuter reported no model for a premise that has one.

    Kept for the record of that incident. `literalValuesDistinct`
    below is what `provablyDistinct` now calls; this predicate decides
    a LEXICAL question and could never see the value-level cases. -/
def lexicalMappingIsInjective (dt : WfIri) : Bool := dt == xsdString

/-! ### Literal distinctness decided on VALUES, not on lexical forms

`lexicalMappingIsInjective` answers a lexical question, and only for
`xsd:string`. It cannot see that `"18"^^xsd:integer` and
`"19"^^xsd:integer` denote different integers, which is what
`functionality-clash` needs, and it cannot see that two
`rdf:XMLLiteral` literals with DIFFERENT canonical forms denote
different values, which is what `WebOnt-miscellaneous-203` and
`-204` need.

The predicates below decide the same question one level lower, on the
data value. Each arm returns `true` only where the OWL 2 datatype map
fixes the two values as different, and `false` — WITHHOLD — everywhere
it cannot decide. Withholding costs refutations; a wrong `true` costs
soundness, and `WebOnt-miscellaneous-202` is the standing witness for
that direction. -/

/-- The part of the `xsd:float` / `xsd:double` value space this module
    decides exactly.

    XSD Datatypes §3.2.4 (float) and §3.2.5 (double) give the value
    space as the IEEE single/double grid together with
    `positiveZero`, `negativeZero`, `positiveInfinity`,
    `negativeInfinity` and `NaN`, and state that positive zero and
    negative zero are two DISTINCT values. OWL 2 Syntax §4.3 adopts
    those value spaces unchanged.

    The lexical-to-value map of the finite non-zero part ROUNDS to the
    nearest grid point, so two different decimal lexical forms can
    denote one value. This classifier therefore names only the values
    it can read off the lexical form with no rounding: the two
    infinities, `NaN`, and the two zeroes. Everything else is `none`
    and the caller withholds. -/
inductive FpExact where
  | posZero | negZero | posInf | negInf | nan
  deriving DecidableEq, Repr

def fpExactValue (lex : String) : Option FpExact :=
  if lex == "NaN" then some .nan
  else if lex == "INF" || lex == "+INF" then some .posInf
  else if lex == "-INF" then some .negInf
  else match parseDecimalRat lex with
    | some r =>
        if r.num == 0 then
          some (if lex.startsWith "-" then .negZero else .posZero)
        else none
    | none => none

/-- The exact rational a literal on the `owl:real` line denotes.
    `xsd:float` and `xsd:double` are absent for the reason
    `XSD.termExactRat` states: their value is the ROUNDED grid point,
    in a different value space. `owl:real` itself has no lexical
    space in OWL 2 Syntax §4.1, so it is absent too. -/
def literalExactRat (l : Literal) : Option XSD.Rat :=
  if isIntegerFamilyDatatype l.datatype then
    (parseFacetInt l.lexicalForm).map (fun v => { num := v, den := 1 })
  else if l.datatype == xsdDecimal then parseDecimalRat l.lexicalForm
  else if l.datatype == owlRational then parseRationalLex l.lexicalForm
  else none

def literalBoolValue (l : Literal) : Option Bool :=
  if l.datatype == xsdBoolean then
    if l.lexicalForm == "true" || l.lexicalForm == "1" then some true
    else if l.lexicalForm == "false" || l.lexicalForm == "0" then some false
    else none
  else none

/-- Do these two literals denote DIFFERENT data values?

    `rdf:XMLLiteral` first: RDF 1.1 Concepts §5.1 maps a well-formed
    lexical form to its exclusive canonical XML form, and that map is
    injective on canonical forms — so two XMLLiterals denote different
    values exactly when their canonical forms differ. This arm keeps
    `WebOnt-miscellaneous-202` (same canonical form, no clash) apart
    from `-203` and `-204` (different canonical forms, clash), which a
    lexical comparison cannot do in either direction.

    Otherwise the two datatypes are placed in the value-space families
    of `XSD.classifyFamily`, whose members OWL 2 Syntax §4 fixes as
    PAIRWISE DISJOINT. Two literals in different families therefore
    denote different values. Inside one family the value is computed
    and compared: exact rationals on the `owl:real` line, the Boolean
    pair, `xsd:string` (whose lexical map is the identity), and the
    exactly-readable part of the floating-point grid. A datatype
    outside every family, or a lexical form the arm cannot read,
    withholds. -/
def literalValuesDistinct (a b : Literal) : Bool :=
  if a.datatype == rdfXMLLiteral && b.datatype == rdfXMLLiteral then
    !XmlCanon.xmlCanonEq a.lexicalForm b.lexicalForm
  else
    match classifyFamily a.datatype, classifyFamily b.datatype with
    | some fa, some fb =>
        if fa != fb then true
        else match fa with
          | .string  => a.lexicalForm != b.lexicalForm
          | .boolean =>
              match literalBoolValue a, literalBoolValue b with
              | some x, some y => x != y
              | _,      _      => false
          | .numeric =>
              match literalExactRat a, literalExactRat b with
              | some x, some y => !ratEq x y
              | _,      _      => false
          | .float | .double =>
              match fpExactValue a.lexicalForm, fpExactValue b.lexicalForm with
              | some x, some y => x != y
              | _,      _      => false
    | _, _ => false

def provablyDistinct (g : Graph) (a b : Term) : Bool :=
  if a == b then false
  else match a, b with
    | .literal x, .literal y =>
        literalValuesDistinct x.val y.val || differentFromAsserted g a b
    | _, _ => differentFromAsserted g a b

/-- `differentFromAsserted` read through a store's membership test: the
    graph holds `a owl:differentFrom b` or `b owl:differentFrom a`. Over
    the index store each test is a hash lookup; `differentFromAsserted`
    scans the whole graph, and the tableau asks it for every pair of
    successors it compares. -/
def differentFromAssertedS (st : Store) (a b : Term) : Bool :=
  (match termAsSubject a with
   | some sa => st.memB ⟨sa, owlDifferentFrom, b⟩
   | none    => false) ||
  (match termAsSubject b with
   | some sb => st.memB ⟨sb, owlDifferentFrom, a⟩
   | none    => false)

/-- `provablyDistinct` with the asserted-difference test read through
    a store (`differentFromAssertedS`). -/
def provablyDistinctS (st : Store) (a b : Term) : Bool :=
  if a == b then false
  else match a, b with
    | .literal x, .literal y =>
        literalValuesDistinct x.val y.val || differentFromAssertedS st a b
    | _, _ => differentFromAssertedS st a b

/-- The search behind `existsDistinctSubsetBy`: `chosen` are the
    members taken so far, pairwise different; `need` more are wanted
    from `rest`. A member is taken only if `d` holds between every
    earlier choice and it. Structural on `rest`. -/
def distinctSubsetGo (d : Term → Term → Bool) (chosen : List Term)
    : List Term → Nat → Bool
  | _,       0        => true
  | [],      _ + 1    => false
  | t :: tl, m + 1    =>
      -- Fewer candidates left than members wanted: no subset exists.
      -- Without this cut the search walks every pairwise-different
      -- subset of the list before answering `false`.
      if tl.length < m then false
      else
        (chosen.all (fun c => d c t) && distinctSubsetGo d (t :: chosen) tl m)
        || distinctSubsetGo d chosen tl (m + 1)

/-- Is there a subset of `ts` of size `n` whose members are PAIRWISE
    different under the relation `d`? Every member is either taken
    (when `d` holds between each earlier choice and it) or skipped, so
    a `true` names a pairwise-different subset. -/
def existsDistinctSubsetBy (d : Term → Term → Bool) (ts : List Term) (n : Nat) : Bool :=
  distinctSubsetGo d [] ts n

/-- `existsDistinctSubsetBy` over `provablyDistinct`: the graph-only
    reading, with no branch state. -/
def existsDistinctSubset (g : Graph) (ts : List Term) (n : Nat) : Bool :=
  existsDistinctSubsetBy (provablyDistinct g) ts n

/-- Two members of one generating-rule group (`RState.distinctGroups`)
    denote different elements in every model. -/
def genDistinct (st : RState) (a b : Term) : Bool :=
  a != b && st.distinctGroups.any (fun grp => grp.contains a && grp.contains b)

/-- Do `a` and `b` denote different elements under THIS BRANCH?

    A branch identifies terms (`RState.ident`), so the question is
    asked of the two identification GROUPS: if some member of `a`'s
    group is provably different from some member of `b`'s group, the
    two groups denote different elements. The reasons a pair of
    members is different are the graph's (`provablyDistinct`, read
    through the index store as `provablyDistinctS`) and the
    generating rule's (`genDistinct`). Two terms the branch has already
    identified are one element, so the answer for them is `false`.

    This is the group-aware reading the F* tableau calls
    `provably_distinct_grouped`. Reading the members one by one, as
    `provablyDistinct` alone does, misses a difference that holds of a
    group through a member other than its representative. -/
def distinctIn (_g : Graph) (st : RState) (a b : Term) : Bool :=
  if repOf st a == repOf st b then false
  else
    let as := identifiedWith st a
    let bs := identifiedWith st b
    as.any (fun x => bs.any (fun y => provablyDistinctS st.store x y || genDistinct st x y))

/-! ## Clash rules

Each returns `true` only when the label set it is given cannot be
satisfied in ANY model. -/

def existsMaxLt (k : Nat) (p : WfIri) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => match l with
                   | .maxCard k' p' => p' == p && k' < k
                   | _              => false)

def existsMaxQualLt (k : Nat) (p : WfIri) (c : ClassExpr) (ls : List ClassExpr)
    : Bool :=
  ls.any (fun l => match l with
                   | .maxQualCard k' p' c' => p' == p && k' < k && ClassExpr.beq c c'
                   | _                     => false)

/-- Successors PROVABLY in the filler: the successor's own node
    carries the filler as a label. Labels are entailed memberships, so
    this under-counts, which is the direction that keeps a `≤ k`
    clash sound. -/
def successorsInFiller (st : RState) (c : ClassExpr) (ts : List Term) : List Term :=
  ts.filter (fun t =>
    match termAsSubject t with
    | some j => memCe c (labelsOf st j)
    | none   => false)

/-! ### The min-sum counting clash

`≤ k r` on a node beside obligations `≥ mᵢ pᵢ` with every `pᵢ ⊑* r`
and the `pᵢ` pairwise different with provably DISJOINT ranges: a
`pᵢ`-successor and a `pⱼ`-successor lie in disjoint classes, so they
are different elements, and each `pᵢ` contributes `mᵢ` different
`r`-successors. If `Σ mᵢ > k` no model has the node (OWL 2 Direct
Semantics §2.2, `ObjectMinCardinality` / `ObjectMaxCardinality`, with
`ObjectPropertyRange` §2.3.2). The counts need no witnesses, which is
what lets `WebOnt-description-logic-903`'s `≥ 200 p`, `≥ 300 q` against
`≤ 499 r` be decided at all. Port of the F* `min_sum_counting_clash`. -/

/-- The obligation a label puts on a property: `(m, p)` for `≥ m p`
    and `≥ m p.C`; `∃p.C` and `∋p.v` oblige one successor. -/
def minObligation : ClassExpr → Option (Nat × WfIri)
  | .minCard m p       => if m ≥ 1 then some (m, p) else none
  | .minQualCard m p _ => if m ≥ 1 then some (m, p) else none
  | .someOf p _        => some (1, p)
  | .hasValue p _      => some (1, p)
  | _                  => none

/-- Two classes the graph declares disjoint (`owl:disjointWith`, or the
    disjointness half of `owl:complementOf`). -/
def classesDeclaredDisjoint (st : RState) (a b : WfIri) : Bool :=
  ((st.store.withSubjPred (.iri a) owlDisjointWith) ++
   (st.store.withSubjPred (.iri a) owlComplementOf)).any (·.o == Term.iri b) ||
  ((st.store.withSubjPred (.iri b) owlDisjointWith) ++
   (st.store.withSubjPred (.iri b) owlComplementOf)).any (·.o == Term.iri a)

/-- Some declared range of `p` is disjoint from some declared range of
    `q`. Every declared range confines the fillers, so one pair is
    enough. -/
def rangesDisjoint (st : RState) (p q : WfIri) : Bool :=
  let rp := st.ranges.filterMap (fun (x, d) => if x == p then some d else none)
  let rq := st.ranges.filterMap (fun (x, d) => if x == q then some d else none)
  rp.any (fun a => rq.any (fun b => classesDeclaredDisjoint st a b))

/-- Is there a choice of obligations, on pairwise different properties
    with pairwise disjoint ranges, whose counts reach `need`? `chosen`
    holds the properties taken so far. Structural on the list. -/
def minSumGo (st : RState) (chosen : List WfIri) : List (Nat × WfIri) → Nat → Bool
  | _,            0        => true
  | [],           _ + 1    => false
  | (m, p) :: tl, need + 1 =>
      (chosen.all (fun q => q != p && rangesDisjoint st q p) &&
        minSumGo st (p :: chosen) tl (need + 1 - m))
      || minSumGo st chosen tl (need + 1)

def minSumClash (st : RState) (ls : List ClassExpr) (k : Nat) (r : WfIri) : Bool :=
  let subs := subsOf st r
  let cands := ls.filterMap (fun l => match minObligation l with
    | some (m, p) => if subs.contains p then some (m, p) else none
    | none        => none)
  cands.length ≥ 2 && minSumGo st [] cands (k + 1)

/-- One label's clash against the whole label set of its node. -/
def clashForLabel (g : Graph) (st : RState) (i : Subject)
    (lsAll : List ClassExpr) (l : ClassExpr) : Bool :=
  match l with
  -- `owl:Nothing` is empty in every model.
  | .named x => x == owlNothing
  -- `¬C` beside `C`, or `¬⊤`.
  | .complement c =>
      memCe c lsAll || (match c with
                        | .named x => x == owlThing
                        -- `i : ¬{a₁ … aₘ}` with `i` identified with some
                        -- `aⱼ`: the branch says `iᴵ = aⱼᴵ ∈ {a₁ … aₘ}ᴵ`.
                        | .oneOf ms => ms.any (fun m => repOf st m == repOf st i.toTerm)
                        | _        => false)
  -- An obligation to HAVE a successor on the bottom property cannot
  -- be met: `EXT(owl:bottomObjectProperty)` is empty in every model.
  | .minCard k p        => k ≥ 1 && (isBottomProp p || existsMaxLt k p lsAll)
  | .someOf p c         =>
      isBottomProp p || existsMaxLt 1 p lsAll || existsMaxQualLt 1 p c lsAll
  | .hasValue p _       => isBottomProp p || existsMaxLt 1 p lsAll
  | .minQualCard k p c  =>
      k ≥ 1 &&
      (isBottomProp p || existsMaxLt k p lsAll || existsMaxQualLt k p c lsAll ||
       -- A nominal `{a₁ … aₘ}` denotes at most `m` individuals in
       -- every model — that is the whole content of `owl:oneOf`. So
       -- `≥ k p.{a₁ … aₘ}` with `k > m` demands more pairwise-
       -- distinct fillers than the set can hold, with no
       -- `owl:differentFrom` needed.
       (match c with
        | .oneOf ms => k > ms.length
        | _         => false))
  -- `i : {a₁ … aₘ}` forces `i` to BE one of the members. If `i` is
  -- provably distinct from every member, no member can be `i`. The
  -- test is group-aware: a branch that identified `i` with a term
  -- forced apart from a member has excluded that member too.
  | .oneOf ms =>
      !ms.isEmpty && ms.all (distinctIn g st i.toTerm ·)
  | .maxCard k p =>
      let succs := successorsOf g st i p true
      (if k == 0 then !succs.isEmpty
       else existsDistinctSubsetBy (distinctIn g st) succs (k + 1))
      || minSumClash st lsAll k p
  | .maxQualCard k p c =>
      let succs := successorsInFiller st c (successorsOf g st i p true)
      if k == 0 then !succs.isEmpty
      else existsDistinctSubsetBy (distinctIn g st) succs (k + 1)
  | _ => false

/-! ## Datatype value spaces

Two rules over the concrete domain, both reading
`L4Factoidal/XSD/Facets.lean`.

**C6, the range clash.** Every `∀p.D` label on a node constrains ALL
its `p`-fillers, and several of them combine by INTERSECTION — "all
fillers in D₁" and "all fillers in D₂" together mean "all fillers in
D₁ ∩ D₂". A `hasValue p v` or a `∃p.D₀` label each separately FORCE
a filler to exist, and that filler must also lie in the intersected
`∀`-constraint. If it cannot, no filler can exist: clash.

Soundness-critical: two DIFFERENT existence obligations on one
property are NEVER combined WITH EACH OTHER — only each one against
the shared `∀`-intersection. Combining two `∃p.Dᵢ` would assume they
share one filler, which is false for a non-functional property.

**C5, the cardinality clash.** A `≥ k p` (k ≥ 1) demands `k` pairwise
distinct fillers. When `p`'s fillers are confined to a value space of
provable size `M < k`, that is impossible. `valueSetMaxSize` is an
OVER-approximation, so `k > M` implies `k` exceeds the true size and
never the reverse: an over-count only withholds a clash. A dense
range answers `none` and makes the rule inert there, which is right —
a min-cardinality on `xsd:decimal` is satisfiable.
-/

/-- Fold one class expression into the value space its fillers must
    lie in. Every shape the datatype layer does not recognise leaves
    the accumulator untouched, so this rule is inert on the ordinary
    class-expression corpus by construction. -/
partial def foldDatatypeConstraint (acc : ValueSet) : ClassExpr → ValueSet
  | .dataRestriction dt facets =>
      if isIntegerFamilyDatatype dt then
        valueSetIntersect acc (.interval (facetsToInterval dt facets fullInterval))
      else if isDateTimeDatatype dt then
        valueSetIntersect acc (.dateInterval (dateTimeFacetsToInterval facets fullInterval))
      -- A restriction over `xsd:float` is DISCRETE: an open interval
      -- whose endpoints are adjacent representable floats is EMPTY
      -- though the same real interval is not.
      else if isFloatDatatype dt then
        (if floatRestrictionProvablyEmpty dt facets then .empty else acc)
      -- A DENSE base folds to a rational-endpoint interval on the
      -- owl:real line, where adjacency never empties anything.
      else if isDenseNumericDatatype dt then
        valueSetIntersect acc (.dense (denseFacetsToQInterval facets fullQInterval))
      else acc
  | .oneOf members =>
      if !members.isEmpty && members.all (fun t => match t with
                                                   | .literal _ => true
                                                   | _          => false)
      then valueSetIntersect acc (.enum members) else acc
  | .named dt =>
      if isDateTimeDatatype dt then valueSetIntersect acc (.dateInterval fullInterval)
      else if isDenseNumericDatatype dt then
        valueSetIntersect acc (.dense fullQInterval)
      else
        (match classifyFamily dt with
         | some .numeric => valueSetIntersect acc (.interval (baseIntervalFor dt))
         -- WITHHELD deliberately for the two floating-point families.
         -- The RDFS closure derives `xsd:byte rdfs:subClassOf
         -- xsd:double`, and range propagation turns one asserted
         -- `p rdfs:range xsd:byte` into a DERIVED `p rdfs:range
         -- xsd:double`. Reading that derived range as a disjointness
         -- constraint would empty the value space of a CONSISTENT
         -- premise. The float/real disjointness is still used where
         -- it is read off an asserted literal's OWN datatype, never
         -- off a derived range triple.
         | some .float  => acc
         | some .double => acc
         | some f       => valueSetIntersect acc (.family f)
         | none         => acc)
  | .complement inner =>
      valueSetSubtract acc (foldDatatypeConstraint .unconstrained inner)
  | _ => acc

/-- The intersection of every `∀q.D` label whose `q` constrains `p`'s
    fillers — `p ⊑* q`, so every `p`-filler is a `q`-filler. -/
def universalForProperty (st : RState) (p : WfIri)
    (ls : List ClassExpr) (acc : ValueSet) : ValueSet :=
  let sups := supsOf st p
  ls.foldl (fun a l => match l with
    | .allOf q d => if sups.contains q then foldDatatypeConstraint a d else a
    | _          => a) acc

/-- `q rdfs:range d` constrains `p`'s fillers when `p ⊑* q`. -/
def rangeValueSet (st : RState) (ranges : List (WfIri × WfIri))
    (p : WfIri) (acc : ValueSet) : ValueSet :=
  let sups := supsOf st p
  ranges.foldl (fun a (q, d) =>
    if sups.contains q then foldDatatypeConstraint a (.named d) else a) acc

def collectDtProperties (ls : List ClassExpr) : List WfIri :=
  ls.filterMap (fun l => match l with
    | .someOf p _   => some p
    | .allOf p _    => some p
    | .hasValue p _ => some p
    | _             => none)

/-! ### Values a node cannot have on a property

Two kinds of assertion forbid a data value to `i` on `p`:

* a NEGATIVE property assertion (OWL 2 Syntax §9.6.8,
  `NegativeDataPropertyAssertion(q i v)`, read from its RDF form
  `owl:sourceIndividual` / `owl:assertionProperty` / `owl:targetValue`)
  says `⟨i, v⟩ ∉ (q)ᴰ`; for `p ⊑* q` then `⟨i, v⟩ ∉ (p)ᴰ` too;
* a DISJOINTNESS (OWL 2 Syntax §9.2.3, `DisjointDataProperties`, as
  `owl:propertyDisjointWith` or an `owl:AllDisjointProperties` group)
  between `q` and some `p' ⊒ p` with `⟨i, v⟩ ∈ (q)ᴰ` asserted: the
  pair cannot also be in `(p')ᴰ ⊇ (p)ᴰ`.

The values are literals the branch holds in every model (graph edges,
or counted expansion edges through `successorsOf … true`), so every
value collected here is excluded in every model of the branch. -/

/-- The members of every `owl:AllDisjointProperties` list, read
    through the store's index. -/
def allDisjointGroupsS (s : Store) : List (List WfIri) :=
  (s.withPredObj rdfType (.iri owlAllDisjointProperties)).filterMap (fun t =>
    match firstObject s t.s owlMembers with
    | some head => some ((walkRdfList s head 64).filterMap (fun x =>
        match x with
        | .iri i => some i
        | _      => none))
    | none => none)

/-- The properties declared disjoint from `p`. -/
def disjointPartners (st : RState) (p : WfIri) : List WfIri :=
  let pairs := (st.store.withPred owlPropertyDisjointWith).filterMap (fun t =>
    match t.s, t.o with
    | .iri a, .iri b => if a == p then some b else if b == p then some a else none
    | _, _           => none)
  let groups := (allDisjointGroupsS st.store).flatMap (fun grp =>
    if grp.contains p then grp.filter (· != p) else [])
  (pairs ++ groups).eraseDups

/-- The literal values `i` is forced NOT to have on `p`. -/
def excludedValues (g : Graph) (st : RState) (i : Subject) (p : WfIri) : List Term :=
  let sups := supsOf st p
  let selves := identifiedWith st i.toTerm
  let negated := selves.flatMap (fun j =>
    (st.store.withPredObj owlSourceIndividual j).filterMap (fun t =>
      match firstObject st.store t.s owlAssertionProperty,
            firstObject st.store t.s owlTargetValue with
      | some (.iri q), some (.literal l) =>
          if sups.contains q then some (Term.literal l) else none
      | _, _ => none))
  let viaDisjoint := sups.flatMap (fun p' =>
    (disjointPartners st p').flatMap (fun q =>
      (successorsOf g st i q true).filter (fun v => match v with
        | .literal _ => true
        | _          => false)))
  (negated ++ viaDisjoint).eraseDups

/-- `vs` with the values `ex` removed. Exact on a literal enumeration
    and on a finite integer interval that `ex` covers entirely; a sound
    no-op on every other shape. A value is removed only when PROVABLY
    equal to an excluded one. -/
def valueSetMinusValues (vs : ValueSet) (ex : List Term) : ValueSet :=
  if ex.isEmpty then vs
  else match vs with
    | .enum xs =>
        let rest := xs.filter (fun t => !(ex.any (termProvablyEqual t)))
        if rest.isEmpty then .empty else .enum rest
    | .interval iv =>
        let inside := (ex.filterMap termIntOpt).eraseDups.filter (valueInInterval · iv)
        match intervalCount iv with
        | some k => if inside.length ≥ k then .empty else vs
        | none   => vs
    | _ => vs


/-- The `xsd:pattern` facets of a string restriction. -/
def stringPatterns (dt : WfIri) (facets : List (WfIri × Term)) : List String :=
  if dt != xsdString then []
  else facets.filterMap (fun (f, v) =>
    if f == facetPatternIri then
      match v with
      | .literal l => some l.val.lexicalForm
      | _          => none
    else none)

/-- Is every string a pattern admits among `ex`? `L(P) ⊆ E` with `E`
    the finite set of excluded `xsd:string` values, decided as the
    emptiness of `L(P) ∩ ¬E` on the verified derivative engine. The
    engine answers "not empty" when its fuel runs out, which withholds
    the clash. Other facets of the restriction are not read; they can
    only shrink the set, so ignoring them can only withhold. -/
def patternCoveredBy (pat : String) (ex : List Term) : Bool :=
  let strs := ex.filterMap (fun t => match t with
    | .literal l => if l.val.datatype == xsdString then some l.val.lexicalForm else none
    | _          => none)
  match L4Factoidal.Regex.XSDPattern.parseXsdPattern pat with
  | none   => false
  | some r =>
    let word (w : String) : L4Factoidal.Regex.Re :=
      (L4Factoidal.Regex.cpsOfString w).foldr
        (fun c acc => .cat (.ranges [(c, c)]) acc) .eps
    let exRe := strs.foldl (fun acc w => .alt acc (word w)) L4Factoidal.Regex.Re.empty
    L4Factoidal.Regex.Exec.isEmpty (.inter r (.compl exRe))

/-- Is some existence obligation on `p` unsatisfiable against the
    shared `∀`-intersection, less the values `ex` the node is forced
    not to have on `p`? Each obligation is checked ALONE against that
    set, never against another obligation. -/
def existsUnsatisfiableWitness (p : WfIri) (ls : List ClassExpr) (universal : ValueSet)
    (ex : List Term := []) : Bool :=
  ls.any (fun l => match l with
    | .someOf q d =>
        q == p &&
        (valueSetIsEmpty (valueSetMinusValues (foldDatatypeConstraint universal d) ex) ||
         (match d with
          | .dataRestriction dt facets =>
              (stringPatterns dt facets).any (patternCoveredBy · ex)
          | _ => false))
    | .hasValue q v =>
        q == p && (match v with
                   | .literal _ => valueSetIsEmpty (valueSetMinusValues
                                     (valueSetIntersect universal (.enum [v])) ex)
                   | _          => false)
    | _ => false)

/-- The value space every `p`-filler must lie in: the `∀`-intersection
    of the node's own labels, MET with the asserted `rdfs:range` of `p`
    and of every super-property of `p`.

    The range half was missing until 2026-09-04, and only from this
    rule: `datatypeCardinalityClash` below already read `st.ranges`.
    OWL 2 Syntax §9.2.5 `DataPropertyRange( DPE DR )` is satisfied only
    when every filler of `DPE` is in the data range, so the range
    constrains a filler exactly as a `∀` label does, and the two
    combine by intersection. `string-integer-clash` is the shape it
    could not see: `DataPropertyRange(:hasAge xsd:integer)` with an
    asserted `xsd:string` filler.

    A range triple can be DERIVED, never invented: the RL rows widen a
    range to a superclass (scm-rng1) or carry it down to a
    sub-property (scm-rng2), and both readings are sound here. The
    float and double families stay withheld inside
    `foldDatatypeConstraint` for the reason recorded there. -/
def fillerValueSet (st : RState) (p : WfIri) (ls : List ClassExpr) : ValueSet :=
  valueSetIntersect (universalForProperty st p ls .unconstrained)
                    (rangeValueSet st st.ranges p .unconstrained)

def datatypeRangeClash (g : Graph) (st : RState) (i : Subject) (ls : List ClassExpr)
    : Bool :=
  (collectDtProperties ls).any (fun p =>
    existsUnsatisfiableWitness p ls (fillerValueSet st p ls) (excludedValues g st i p))

/-- Every label that demands `k` pairwise different `p`-fillers:
    `(k, p, none)` for `≥ k p` and `= k p`, `(k, p, some D)` for the
    QUALIFIED forms `≥ k p.D` and `= k p.D`.

    OWL 2 Direct Semantics §2.2.3 (class expressions):
    `DataMinCardinality(n DPE DR)` is
    `{x | #{y | ⟨x,y⟩ ∈ (DPE)ᴰᴾ ∧ y ∈ (DR)ᴰᵀ} ≥ n}`. The `n` values
    lie in `(DR)ᴰᵀ` AND in every space a filler of `DPE` is confined
    to, so the qualified form meets the filler space with `DR`. A
    filler the datatype layer does not read (an object class
    expression, a datatype outside the map) leaves the space as it is,
    which over-counts and withholds the clash.

    Until 2026-10-10 the qualified forms were not collected, so
    `DataExactCardinality(2 dp xsd:boolean)` beside
    `NegativeDataPropertyAssertion(dp a "true"^^xsd:boolean)` was not
    refuted (`Qualified-cardinality-boolean`,
    https://github.com/danbri/factoidal/issues/709). -/
def collectCardProps (ls : List ClassExpr) : List (Nat × WfIri × Option ClassExpr) :=
  ls.filterMap (fun l => match l with
    | .minCard k p         => some (k, p, none)
    | .exactCard k p       => some (k, p, none)
    | .minQualCard k p d   => some (k, p, some d)
    | .exactQualCard k p d => some (k, p, some d)
    | _                    => none)

/-- An upper bound on the values left in `vs` once `ex` is removed.
    For a finite integer interval it is the count less the excluded
    integers inside it; for an enumeration the enumeration's own bound
    after removal. Every other shape keeps its bound without the
    exclusion, which is an over-count, the withholding direction. -/
def valueSetMaxSizeExcluding (vs : ValueSet) (ex : List Term) : Option Nat :=
  match vs with
  | .interval iv =>
      match intervalCount iv with
      | some k =>
          let inside := (ex.filterMap termIntOpt).eraseDups.filter (valueInInterval · iv)
          some (k - inside.length)
      | none => none
  | .enum _ => valueSetMaxSize (valueSetMinusValues vs ex)
  -- `xsd:boolean` has the value space `{true, false}` (XSD 1.1 Part 2
  -- §3.3.2); an excluded boolean value, read through its lexical
  -- mapping (`"1"` and `"true"` are one value), removes one of them.
  | .family .boolean =>
      some (2 - (ex.filterMap termBoolOpt).eraseDups.length)
  | _ => valueSetMaxSize vs

def datatypeCardinalityClash (g : Graph) (st : RState) (i : Subject) (ls : List ClassExpr)
    : Bool :=
  (collectCardProps ls).any (fun (k, p, d?) =>
    k ≥ 1 &&
    (let vs := fillerValueSet st p ls
     let vs := match d? with
       | some d => foldDatatypeConstraint vs d
       | none   => vs
     match valueSetMaxSizeExcluding vs (excludedValues g st i p) with
     | some m => k > m
     | none   => false))

/-! ## The counting clash: pairwise-disjoint existentials against `≤ k`

The ≤-rule below closes a `≤ k p` by MERGING successors and asking
every merge to clash. That search is a partition enumeration —
`WebOnt-description-logic-019` records 301 partitions for its
unsatisfiable case and `-022` records 42,525 for its satisfiable one —
so on the OilEd fixtures it does not finish inside any budget worth
giving it.

The rule here decides the same clash analytically, and it is the
standard ≥/≤ counting argument of the `SHIQ` calculus (Horrocks,
Sattler and Tobies, "Practical Reasoning for Very Expressive
Description Logics", LJ IGPL 8(3), 2000, §3, the `≥`/`≤` clash
condition; the same argument the `choose`-free counting optimisation
of FaCT and RACER uses).

    If `x` carries `∃p.C₁ … ∃p.Cₘ` with the `Cᵢ` PAIRWISE DISJOINT,
    then in every model `x` has `m` p-successors that are pairwise
    distinct, because a shared successor would lie in two disjoint
    classes. A `≤ k p` on `x` with `k < m` therefore has no model.

Under OWL 2 Direct Semantics §2.2 that reads
`ObjectSomeValuesFrom(p Cᵢ) ⊆ {x | ∃y. ⟨x,y⟩ ∈ p ∧ y ∈ Cᵢ}` and
`ObjectMaxCardinality(k p) ⊆ {x | #{y | ⟨x,y⟩ ∈ p} ≤ k}`, so the
argument is a counting one over `p`'s extension at `x` and needs no
choice of witnesses.

Both directions of approximation withhold the clash rather than
invent one: `ceDisjoint` proves disjointness structurally and answers
`false` where it cannot, and `disjointClique` takes a GREEDY
pairwise-disjoint subset, which is a lower bound on the largest one. -/

/-- `ls` with `news` appended, skipping what is already there. -/
def addCes (ls : List ClassExpr) (news : List ClassExpr) : List ClassExpr :=
  news.foldl (fun acc c => if memCe c acc then acc else acc ++ [c]) ls

/-- The labels a node must carry if it carries every member of `ls`:
    the conjuncts of each intersection, and the consequent of each
    TBox axiom whose antecedent is present, to a fixpoint under
    `fuel`. Running out of fuel DROPS labels, which can only lose a
    clash. -/
def ceLabelClosure (tb : List (ClassExpr × ClassExpr))
    : Nat → List ClassExpr → List ClassExpr
  | 0,     ls => ls
  | n + 1, ls =>
    let ls' := addCes ls
      ((ls.flatMap (fun l => match l with
                             | .intersection cs => cs
                             | _                => [])) ++
       tb.filterMap (fun q => if memCe q.1 ls then some q.2 else none))
    if ls'.length == ls.length then ls else ceLabelClosure tb n ls'

/-- A label set that no node can carry: a complement pair, or
    `owl:Nothing`. The structural core of `clashForLabel`, without the
    parts that read the graph. -/
def cesClash (ls : List ClassExpr) : Bool :=
  ls.any (fun l => match l with
                   | .complement c => memCe c ls
                   | .named x      => x == owlNothing
                   | _             => false)

/-- Are `a` and `b` disjoint — is `a ⊓ b` unsatisfiable? Proved by
    closing the pair's label set under the TBox and finding a
    structural clash in it. `false` where no proof is found. -/
def ceDisjoint (tb : List (ClassExpr × ClassExpr)) (a b : ClassExpr) : Bool :=
  ceDefinite a && ceDefinite b &&
  cesClash (ceLabelClosure tb 8 (addCes [a] [b]))

/-- The fillers of the existential obligations on `p`. A
    `minQualCard k p C` with `k ≥ 1` obliges one filler in `C` the
    same way `∃p.C` does; the extra `k - 1` are not used here. -/
def existentialFillersOn (p : WfIri) (ls : List ClassExpr) : List ClassExpr :=
  ls.filterMap (fun l => match l with
    | .someOf q c        => if q == p then some c else none
    | .minQualCard k q c => if q == p && k ≥ 1 then some c else none
    | _                  => none)

/-- A pairwise-disjoint subset of `cs`, taken greedily in list order.
    Any pairwise-disjoint subset is a valid lower bound on the number
    of successors the obligations force apart, so a greedy one is
    sound; a maximum one would only find more clashes. -/
def disjointClique (tb : List (ClassExpr × ClassExpr)) (cs : List ClassExpr)
    : List ClassExpr :=
  cs.foldl (fun acc c =>
    if acc.all (fun d => ceDisjoint tb c d) then acc ++ [c] else acc) []

/-- `≤ k p` (or `= k p`) against the existential obligations on `p`.
    The cheap length test runs first: with `m ≤ k` obligations no
    clique can exceed `k`, so no disjointness is computed at all. -/
def countingClash (st : RState) (ls : List ClassExpr) : Bool :=
  ls.any (fun l =>
    match l with
    | .maxCard k p | .exactCard k p =>
        let cs := existentialFillersOn p ls
        cs.length > k && (disjointClique st.tbox cs).length > k
    | _ => false)

/-! ## The propositional clash on one node

A node's labels are memberships its element has in every model of the
branch. Read as propositions about that one element, they are
clauses: a label `C₁ ⊔ … ⊔ Cₙ` says the element is in some `Cᵢ`, and
any other label is a unit clause. A TBox axiom `A ⊑ D` holds of EVERY
element, so it is the clause `¬A ∨ D` about this one too.

If no truth assignment to the class expressions satisfies all the
clauses, no element can carry all the labels: for any model `I` and
the element `x`, the assignment `v(C) = [x ∈ Cᴵ]` would satisfy every
clause, because each clause is a membership `x` has in `I`, and it
respects complement because `x ∈ (¬C)ᴵ ↔ x ∉ Cᴵ`. So an unsatisfiable
clause set is a clash. This is the propositional half of the
union rule, decided without spending a branch of the search on each
disjunct.

`WebOnt-description-logic-040` is the shape it exists for: one node
carries 32 independent `Aᵢ ⊔ Bᵢ` unions, and a witness carries the
four clauses `A ∨ B`, `A ∨ ¬B`, `¬A ∨ B`, `¬A ∨ ¬B`. Branching in node
order explores `2³²` assignments of the first node before it reaches
the second; the clause set of the second is unsatisfiable on its own.
`WebOnt-description-logic-504` is a 3-SAT instance written as
`rdfs:subClassOf` unions on one individual, with `owl:disjointWith`
pairs; its axioms enter as clauses.

Every approximation withholds a clash rather than invents one. A
class expression that is not a literal is an ATOM the assignment may
set freely, and two atoms are the same variable only when they are
structurally equal (`ceEq`), so equal classes written differently
become two variables, which can only make a set satisfiable. An
axiom whose sides are not of the shapes below contributes no clause.
The search is fuel-bounded and a run out of fuel answers
"satisfiable". -/

/-- A literal: an atom and its polarity. `¬C` is `C` with polarity
    `false`; `owl:Nothing` is `¬owl:Thing`. -/
structure PLit where
  atom : ClassExpr
  pos  : Bool

def litOf : ClassExpr → PLit
  | .complement c => ⟨c, false⟩
  | .named x =>
      if x == owlNothing then ⟨.named owlThing, false⟩ else ⟨.named x, true⟩
  | c => ⟨c, true⟩

/-- The literal's negation. -/
def PLit.neg (l : PLit) : PLit := ⟨l.atom, !l.pos⟩

/-- The literals of a disjunction label, or of any other label as a
    one-literal clause. -/
def clauseOfLabel : ClassExpr → List PLit
  | .union cs => cs.map litOf
  | c         => [litOf c]

/-- The clauses an axiom `a ⊑ d` contributes. `a` must be a literal,
    a union of them (one clause per disjunct) or an intersection of
    them (one clause negating all conjuncts); `d` a literal, a union of
    literals, or an intersection (one clause per conjunct). -/
def axiomClauses (a d : ClassExpr) : List (List PLit) :=
  let rhs : List (List PLit) := match d with
    | .intersection ds => ds.map clauseOfLabel
    | _                => [clauseOfLabel d]
  let lhs : List (List PLit) := match a with
    | .union as         => as.map (fun x => [(litOf x).neg])
    | .intersection as  => [as.map (fun x => (litOf x).neg)]
    | _                 => [[(litOf a).neg]]
  lhs.flatMap (fun l => rhs.map (fun r => l ++ r))

/-- The atoms an axiom's left-hand side mentions. -/
def axiomLhsAtoms : ClassExpr → List ClassExpr
  | .union as        => as.map (fun x => (litOf x).atom)
  | .intersection as => as.map (fun x => (litOf x).atom)
  | a                => [(litOf a).atom]

/-- The atoms a clause set mentions. -/
def clauseAtoms (cs : List (List PLit)) : List ClassExpr :=
  cs.foldl (fun acc c => c.foldl (fun a2 l =>
    if a2.any (fun x => ClassExpr.beq x l.atom) then a2 else a2 ++ [l.atom]) acc) []

/-- A literal over an interned atom: the atom's index and polarity. -/
structure ILit where
  v   : Nat
  pos : Bool

/-- Intern the atoms of a clause set. Each clause becomes `none` when
    it holds of every element (it contains `owl:Thing` positively), and
    otherwise loses its `¬owl:Thing` literals, which hold of none.
    Atoms are one variable when `ceEq` says so; an indefinite atom
    gets a variable of its own at every occurrence. -/
def internClauses (cs : List (List PLit)) : List (List ILit) × Nat :=
  let isTop (c : ClassExpr) : Bool := match c with
    | .named x => x == owlThing
    | .intersection [] => true
    | _ => false
  let (out, atoms) := cs.foldl (fun (acc : List (List ILit) × Array ClassExpr) c =>
    let (outs, atoms0) := acc
    let r := c.foldl (fun (a2 : Option (List ILit) × Array ClassExpr) l =>
      match a2 with
      | (none, ats) => (none, ats)
      | (some ls, ats) =>
        if isTop l.atom then
          (if l.pos then (none, ats) else (some ls, ats))
        else
          match ats.findIdx? (fun x => ceEq x l.atom) with
          | some i => (some (ls ++ [⟨i, l.pos⟩]), ats)
          | none   => (some (ls ++ [⟨ats.size, l.pos⟩]), ats.push l.atom))
      (some [], atoms0)
    match r with
    | (some ls, ats) => (outs ++ [ls], ats)
    | (none, ats)    => (outs, ats)) ([], #[])
  (out, atoms.size)

def ilitValue (asg : Array (Option Bool)) (l : ILit) : Option Bool :=
  (asg.getD l.v none).map (fun b => if l.pos then b else !b)

/-- DPLL with unit propagation, fuel threaded. `some true`: an
    assignment satisfies every clause; `some false`: none does;
    `none`: out of fuel. -/
def dpll (fuel : Nat) (cs : List (List ILit)) (asg : Array (Option Bool))
    : Option Bool × Nat :=
  match fuel with
  | 0     => (none, 0)
  | n + 1 =>
    -- Reduce each clause under the assignment.
    let open_ : List (List ILit) := cs.filterMap (fun c =>
      if c.any (fun l => ilitValue asg l == some true) then none
      else some (c.filter (fun l => ilitValue asg l == none)))
    if open_.any (·.isEmpty) then (some false, n)
    else
      -- Every unit clause forces its literal in any satisfying
      -- extension of `asg`, so all of them are assigned in one step;
      -- two units forcing one variable both ways leave no extension.
      -- One unit per step cost one scan of the clause set per forced
      -- literal: 22 seconds per call on the label sets of
      -- `WebOnt-miscellaneous-011`.
      let units := open_.filterMap (fun c => match c with | [u] => some u | _ => none)
      let forced := units.foldl (fun (a : Option (Array (Option Bool))) u =>
        match a with
        | none    => none
        | some a' =>
          match a'.getD u.v none with
          | some b => if b == u.pos then some a' else none
          | none   => some (a'.set! u.v (some u.pos))) (some asg)
      if !units.isEmpty then
        match forced with
        | none    => (some false, n)
        | some a' => dpll n cs a'
      else
        -- No unit clause: branch on the first literal of the first
        -- open clause.
        match open_.head? with
        | none   => (some true, n)
        | some c =>
          match c.head? with
          | none   => (some false, n)
          | some l =>
            match dpll n cs (asg.set! l.v (some l.pos)) with
            | (some true, n')  => (some true, n')
            | (some false, n') => dpll (min n' n) cs (asg.set! l.v (some !l.pos))
            | (none, n')       => (none, n')
termination_by fuel
decreasing_by all_goals omega

/-- Satisfiability of a clause set, by `dpll` over interned atoms. -/
def clausesSatisfiable (fuel : Nat) (cs : List (List PLit)) : Option Bool :=
  let (ics, n) := internClauses cs
  (dpll fuel ics (Array.replicate n none)).1

def propFuel : Nat := 4000

/-- The clause set of one label set: the labels, and the axioms whose
    left-hand side mentions an atom the set already mentions, pulled in
    to a fixpoint of `rounds` steps. -/
def nodeClauses (tb : List (ClassExpr × ClassExpr)) (ls : List ClassExpr)
    (rounds : Nat) : List (List PLit) :=
  let base := ls.map clauseOfLabel
  let rec grow : Nat → List (List PLit) → List (ClassExpr × ClassExpr) → List (List PLit)
    | 0,     cs, _      => cs
    | k + 1, cs, remain =>
      let atoms := clauseAtoms cs
      let (take, keep) := remain.partition (fun (a, _) =>
        (axiomLhsAtoms a).any (fun x => atoms.any (ceEq x)))
      if take.isEmpty then cs
      else grow k (cs ++ take.flatMap (fun (a, d) => axiomClauses a d)) keep
  grow rounds base tb

/-- The TBox as an array, with the indices of the axioms whose
    left-hand side mentions an atom, by the atom's `ceIndexKey`. -/
structure LhsAtomIndex where
  axs    : Array (ClassExpr × ClassExpr) := #[]
  byAtom : Std.HashMap String (List Nat) := {}

def LhsAtomIndex.build (tb : List (ClassExpr × ClassExpr)) : LhsAtomIndex :=
  let axs := tb.toArray
  let byAtom := (List.range axs.size).foldl (fun (m : Std.HashMap String (List Nat)) k =>
    match axs[k]? with
    | none => m
    | some (a, _) =>
      (axiomLhsAtoms a).foldl (fun m x =>
        let key := ceIndexKey x
        let ks := m.getD key []
        -- An axiom whose antecedent repeats an atom key is listed once.
        if ks.head? == some k then m else m.insert key (k :: ks)) m) {}
  { axs := axs, byAtom := byAtom }

/-- The clause set `propositionalClash` decides for a SATURATED label
    set: the labels, and the axioms pulled in, to `rounds` steps, by an
    atom that no single-literal label FIXES.

    A round takes, in TBox order, every axiom not yet taken whose
    left-hand side mentions such an atom. The index offers the axioms
    that mention an atom with the same `ceIndexKey`, and `ceEq`
    decides (`ceIndexKey_of_beq`: an axiom whose antecedent mentions
    the atom is always offered).

    **Why the fixed atoms pull nothing.** The expansion only asks this
    of a node it has run to quiescence. An axiom whose antecedent is a
    literal the node carries has FIRED (`applyAxioms`), so its
    consequent is a label and its clause is already in the set; an
    axiom whose antecedent literal is the negation of a label has a
    clause the unit label satisfies. Neither changes the answer, and
    with ~150 labels per node they were most of the TBox: 3,850
    clauses per node on `WebOnt-miscellaneous-011`, 100 ms of clause
    search each. Any subset of the clauses that has no model proves
    the node has none, so a dropped clause can withhold a clash and
    never invent one. -/
def nodeClausesIx (ix : LhsAtomIndex) (ls : List ClassExpr) (rounds : Nat)
    : List (List PLit) :=
  let base := ls.map clauseOfLabel
  let fixedAtoms := ls.filterMap (fun l => match l with
    | .union _ => none
    | _        => some (litOf l).atom)
  let isFixed (x : ClassExpr) : Bool := fixedAtoms.any (ClassExpr.beq x)
  let rec grow : Nat → List (List PLit) → Std.HashSet Nat → List (List PLit)
    | 0,     cs, _     => cs
    | k + 1, cs, taken =>
      let atoms := (clauseAtoms cs).filter (fun x => !isFixed x)
      let offered := atoms.foldl (fun (acc : Std.HashSet Nat) x =>
        (ix.byAtom.getD (ceIndexKey x) []).foldl (fun acc i =>
          if taken.contains i then acc else acc.insert i) acc) {}
      let take := (offered.toList.mergeSort (· ≤ ·)).filter (fun i =>
        match ix.axs[i]? with
        | some (a, _) => (axiomLhsAtoms a).any (fun x => atoms.any (ceEq x))
        | none        => false)
      if take.isEmpty then cs
      else
        let news := take.flatMap (fun i => match ix.axs[i]? with
          | some (a, d) => axiomClauses a d
          | none        => [])
        grow k (cs ++ news) (take.foldl (fun t i => t.insert i) taken)
  grow rounds base {}

/-- Is one node's label set propositionally unsatisfiable? Asked only
    of a node with at least two disjunction labels: with one, the
    union rule's own branches find the clash as cheaply. -/
def propositionalClashLabels (tb : List (ClassExpr × ClassExpr)) (ls : List ClassExpr)
    : Bool :=
  let unions := ls.filter (fun l => match l with | .union _ => true | _ => false)
  if unions.length < 2 then false
  else clausesSatisfiable propFuel (nodeClauses tb ls 3) == some false

/-- `propositionalClashLabels` over a prebuilt index. -/
def propositionalClashLabelsIx (ix : LhsAtomIndex) (ls : List ClassExpr) : Bool :=
  let unions := ls.filter (fun l => match l with | .union _ => true | _ => false)
  if unions.length < 2 then false
  else clausesSatisfiable propFuel (nodeClausesIx ix ls 3) == some false

/-- A key for a label SET: the sorted printed forms of its labels.
    Two nodes with the same labels in another order get one key. -/
def labelSetKey (ls : List ClassExpr) : String :=
  String.intercalate "\n" ((ls.map (fun l => reprStr l)).mergeSort (· ≤ ·))

/-- Some node's labels are propositionally unsatisfiable. The answer
    depends on the label set and the TBox only, so it is computed once
    per distinct label set: individuals of the same classes carry the
    same set, and the clause search is the expensive part. -/
def propositionalClash (st : RState) : Bool :=
  let ix := LhsAtomIndex.build st.tbox
  ((groupLeaders st).foldl (fun (acc : Std.HashMap String Bool × Bool) n =>
    if acc.2 then acc
    else
      let ls := labelsOf st n.id
      if (ls.filter (fun l => match l with | .union _ => true | _ => false)).length < 2
      then acc
      else
        let key := labelSetKey ls
        match acc.1.get? key with
        | some r => (acc.1, r)
        | none   =>
          let r := propositionalClashLabelsIx ix ls
          (acc.1.insert key r, r)) ({}, false)).2

/-! ## The identity clash over nominals

`i : {m₁ … mₖ}` says `iᴵ` is one of `m₁ᴵ … mₖᴵ`. Over the terms these
labels mention, read the atom `E(a, b)` as "`a` and `b` denote one
element". Every model satisfies:

* for each nominal label on `i`: `E(i, m₁) ∨ … ∨ E(i, mₖ)`;
* `¬E(a, b)` for every pair the branch proves different (`distinctIn`)
  and every pair whose labels contain a complement pair (`cesClash`);
* `E(a, b)` for every pair the branch has identified;
* transitivity: `E(a, b) ∧ E(b, c) → E(a, c)`.

So if the clause set has no satisfying assignment, the branch has no
model. This decides by unit propagation what the nominal choice rule
would decide by branching once per member of each label: on
`WebOnt-description-logic-502`, a 3-SAT instance whose variables are
the identities of `T` with `plus₁ … plus₉` and `minus₁ … minus₉`, the
branching search runs out of budget long before the clause search
does.

Capped at `nominalUniverseCap` terms (the transitivity clauses are
cubic in it); above the cap no clause set is built and nothing is
decided. Out-of-fuel answers "satisfiable". -/

def nominalUniverseCap : Nat := 30

/-- An IRI or a blank node: a term that denotes an individual. A
    literal denotes a data value, which no individual equals. -/
def isResourceTerm : Term → Bool
  | .bnode _ => true
  | .iri _   => true
  | _        => false

def nominalClash (g : Graph) (st : RState) : Bool :=
  -- Negative nominals: `i : ¬{m₁ … mₖ}` gives `¬E(i, mⱼ)` for each
  -- member.
  let negLabelled : List (Subject × List Term) := (groupLeaders st).filterMap (fun n =>
    let ms := (labelsOf st n.id).flatMap (fun l => match l with
      | .complement (.oneOf ms) => ms.filter isResourceTerm
      | _                       => [])
    if ms.isEmpty then none else some (n.id, ms))
  let labelled : List (Subject × List (List Term)) := (groupLeaders st).filterMap (fun n =>
    -- Only a nominal of individuals. A label whose members include a
    -- literal sits on a DATA witness (the existential of a data
    -- property mints one), which denotes a data value, not an
    -- individual; it is not an identity question and is not encoded.
    let os := (labelsOf st n.id).filterMap (fun l => match l with
      | .oneOf ms => if ms.length ≥ 2 && ms.all isResourceTerm then some ms else none
      | _         => none)
    if os.isEmpty then none else some (n.id, os))
  if labelled.isEmpty then false
  else
    -- The universe is the positive nominals' nodes and members only.
    -- A negative nominal adds a clause only between terms already in
    -- it: `E(a, b)` for a term outside the universe occurs in no other
    -- clause, so a clause on it cannot make the set unsatisfiable, and
    -- every extra term costs a cubic number of transitivity clauses.
    let u : List Term := ((labelled.map (fun q => repOf st q.1.toTerm)) ++
      (labelled.flatMap (fun q => q.2.flatten.filter isResourceTerm)).map (repOf st)).eraseDups
    let n := u.length
    if n > nominalUniverseCap then false
    else
      let ix (t : Term) : Option Nat := u.findIdx? (· == repOf st t)
      let e (a b : Nat) (pos : Bool) : ILit :=
        ⟨(min a b) * n + (max a b), pos⟩
      let oneOfClauses : List (List ILit) := labelled.flatMap (fun (i, os) =>
        match ix i.toTerm with
        | none => []
        | some a => os.filterMap (fun ms =>
            -- A member identified with `i` already satisfies the label.
            if ms.any (fun m => isResourceTerm m && ix m == some a) then none
            else some (ms.filterMap (fun m =>
              if isResourceTerm m then (ix m).map (fun b => e a b true) else none))))
      let pairs := (List.range n).flatMap (fun a =>
        (List.range n).filterMap (fun b => if a < b then some (a, b) else none))
      let labelsOfT (t : Term) : List ClassExpr := match termAsSubject t with
        | some j => labelsOf st j
        | none   => []
      let apart : List (List ILit) := pairs.filterMap (fun (a, b) =>
        let ta := u.getD a (.iri owlThing)
        let tb := u.getD b (.iri owlThing)
        if distinctIn g st ta tb || cesClash (labelsOfT ta ++ labelsOfT tb)
        then some [e a b false] else none)
      let trans : List (List ILit) := pairs.flatMap (fun (a, c) =>
        (List.range n).filterMap (fun b =>
          if b == a || b == c then none
          else some [e a b false, e b c false, e a c true]))
      let negClauses : List (List ILit) := negLabelled.flatMap (fun (i, ms) =>
        match ix i.toTerm with
        | none => []
        | some a => ms.filterMap (fun m => (ix m).map (fun b =>
            -- `i` already identified with a member: the clause is
            -- empty, which the clash arm of `clashForLabel` reports too.
            if a == b then [] else [e a b false])))
      let cs := oneOfClauses ++ negClauses ++ apart ++ trans
      (dpll propFuel cs (Array.replicate (n * n) none)).1 == some false

/-- The `p`-PREDECESSORS of `j`'s identification group: subjects of
    `q`-edges into the group for every `q ⊑* p`, from the graph and the
    expansion, and the successors of the group on every inverse of such
    a `q`. Mapped to representatives. -/
def predecessorsOf (st : RState) (j : Subject) (p : WfIri) : List Term :=
  let roles := subsOf st p
  let selves := identifiedWith st j.toTerm
  let fromGraph := selves.flatMap (fun t => roles.flatMap (fun r =>
    (st.store.withPredObj r t).map (·.s.toTerm)))
  let fromExtra := selves.flatMap (fun t =>
    (st.extraIn.getD t #[]).toList.filterMap (fun e =>
      if roles.contains e.p then some e.s.toTerm else none))
  let viaInverse := (selves.filterMap termAsSubject).flatMap (fun s => roles.flatMap (fun r =>
    (inversesOf st.inv r).flatMap (fun r' =>
      (st.store.withSubjPred s r').map (·.o) ++
      (st.extraOut.getD s #[]).toList.filterMap (fun e =>
        if e.p == r' then some e.o else none))))
  (fromGraph ++ fromExtra ++ viaInverse).map (repOf st) |>.eraseDups

/-- `owl:InverseFunctionalProperty p` with two provably different
    `p`-predecessors of one element: OWL 2 Direct Semantics §2.3.2
    (`InverseFunctionalObjectProperty`) makes them one element. -/
def inverseFunctionalClash (g : Graph) (st : RState) : Bool :=
  st.invFuncProps.any (fun p =>
    (groupLeaders st).any (fun n =>
      existsDistinctSubsetBy (distinctIn g st)
        ((predecessorsOf st n.id p).filter (fun t => match t with
          | .literal _ => false
          | _          => true)) 2))

def clashNodes (g : Graph) (st : RState) : Bool :=
  inverseFunctionalClash g st ||
  (groupLeaders st).any (fun n =>
    let ls := labelsOf st n.id
    ls.any (clashForLabel g st n.id ls)
    || datatypeRangeClash g st n.id ls
    || datatypeCardinalityClash g st n.id ls
    || countingClash st ls)

/-! ## Graph-level violations

Five shapes that make a graph unsatisfiable without any expansion at
all. Each is checked once, before the tableau starts. -/

def sameAsLinked (g : Graph) (a b : Term) : Bool :=
  g.any (fun t =>
    t.p == owlSameAs &&
    ((t.s.toTerm == a && t.o == b) || (t.s.toTerm == b && t.o == a)))

/-- G1: `owl:AllDifferent` members must be pairwise distinct, so a
    member listed twice, or two members linked by `owl:sameAs`, has no
    model. Positions `i < j` only — every term is `owl:sameAs` itself
    by reflexivity, and that must not fire. -/
partial def allDiffPairViolation (g : Graph) : List Term → Bool
  | []      => false
  | h :: tl => tl.any (fun o => h == o || sameAsLinked g h o)
               || allDiffPairViolation g tl

def allDifferentViolation (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == rdfType && t.o == Term.iri owlAllDifferent &&
    (((firstObject (Store.ofGraph g) t.s owlMembers).map
        (fun h => allDiffPairViolation g (walkRdfList (Store.ofGraph g) h 64))
        |>.getD false) ||
     ((firstObject (Store.ofGraph g) t.s owlDistinctMembers).map
        (fun h => allDiffPairViolation g (walkRdfList (Store.ofGraph g) h 64))
        |>.getD false)))

/-- G3: `p owl:propertyDisjointWith p` makes `EXT(p)` disjoint from
    itself, so empty. Any triple using `p` is then false in every
    model. The RL marker misses this because it wants two DIFFERENT
    predicates. -/
def selfDisjointPropertyInUse (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlPropertyDisjointWith && t.s.toTerm == t.o &&
    (match t.s with
     | .iri p   => g.any (fun u => u.p == p)
     | .bnode _ => false))

/-- G4: `rdf:nil` is the empty list and has no `rdf:first` or
    `rdf:rest` of its own, under both OWL 2 semantics. -/
def nilStructureViolation (g : Graph) : Bool :=
  g.any (fun t =>
    (t.p == rdfFirst || t.p == rdfRest) &&
    (match t.s with
     | .iri i   => i == rdfNil
     | .bnode _ => false))

/-- G5: a named class disjoint from `ObjectHasSelf(p)`, with an
    individual in that class carrying the reflexive edge `x p x`. The
    class-expression AST has no `hasSelf` constructor, so this narrow
    shape is checked at graph level. -/
def hasSelfRestriction (g : Graph) (r : Subject) : Option WfIri :=
  match firstObject (Store.ofGraph g) r owlOnProperty with
  | some (.iri p) =>
      (match firstObject (Store.ofGraph g) r owlHasSelf with
       | some (.literal l) =>
           if l.val.lexicalForm == "true" || l.val.lexicalForm == "1" then some p
           else none
       | _ => none)
  | _ => none

def hasSelfDisjointFor (g : Graph) (c : WfIri) (r : Subject) : Bool :=
  match hasSelfRestriction g r with
  | none   => false
  | some p =>
      g.any (fun t =>
        t.p == rdfType && t.o == Term.iri c &&
        g.any (fun u => u.p == p && u.s == t.s && u.o == t.s.toTerm))

def hasSelfDisjointViolation (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlDisjointWith &&
    (match t.s, t.o with
     | .iri c, .bnode b => hasSelfDisjointFor g c (.bnode b)
     | .bnode b, .iri c => hasSelfDisjointFor g c (.bnode b)
     | .iri c, .iri r   => hasSelfDisjointFor g c (.iri r)
     | _, _             => false))

/-- G2: `EXT(owl:bottomObjectProperty)` is empty in every model, so
    any triple asserted over it is false in every model. -/
def bottomPropertyAssertion (g : Graph) : Bool :=
  g.any (fun t => isBottomProp t.p)

/-- G6: `owl:Thing owl:equivalentClass owl:Nothing`, in either
    direction. OWL 2 Direct Semantics requires a NON-EMPTY domain and
    interprets `owl:Thing` as the whole of it, so equating it with the
    empty class has no model. -/
def thingIsNothing (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlEquivalentClass &&
    ((t.s == Subject.iri owlThing && t.o == Term.iri owlNothing) ||
     (t.s == Subject.iri owlNothing && t.o == Term.iri owlThing)))

/-- G7: two DIFFERENT properties declared `owl:propertyDisjointWith`
    with a shared subject-object pair. `EXT(p) ∩ EXT(q) = ∅`, and the
    pair is in both. -/
def disjointPropertiesShareAPair (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlPropertyDisjointWith &&
    (match t.s, t.o with
     | .iri p, .iri q =>
         p != q &&
         g.any (fun u => u.p == p &&
           g.any (fun v => v.p == q && v.s == u.s && v.o == u.o))
     | _, _ => false))

/-- The members of every `owl:AllDisjointProperties` list. -/
def allDisjointPropertyGroups (g : Graph) : List (List WfIri) :=
  let st := Store.ofGraph g
  g.filterMap (fun t =>
    if t.p == rdfType && t.o == Term.iri owlAllDisjointProperties then
      match firstObject st t.s owlMembers with
      | some head => some ((walkRdfList st head 64).filterMap (fun x =>
          match x with
          | .iri i => some i
          | _      => none))
      | none      => none
    else none)

/-- G8: two members of one `owl:AllDisjointProperties` sharing a
    pair. The group asserts the extensions are PAIRWISE disjoint, so
    one shared pair has no model. -/
partial def groupPairViolation (g : Graph) : List WfIri → Bool
  | []      => false
  | p :: tl =>
      tl.any (fun q =>
        g.any (fun u => u.p == p &&
          g.any (fun v => v.p == q && v.s == u.s && v.o == u.o)))
      || groupPairViolation g tl

def allDisjointPropertiesViolation (g : Graph) : Bool :=
  (allDisjointPropertyGroups g).any (groupPairViolation g)

/-- G9: an `owl:AsymmetricProperty` with both `x p y` and `y p x`, or
    an `owl:IrreflexiveProperty` with `x p x`. Asymmetry says
    `(x,y) ∈ EXT(p)` implies `(y,x) ∉ EXT(p)`; irreflexivity says no
    pair `(x,x)` is in it. -/
def asymmetryViolation (g : Graph) : Bool :=
  (collectTypedIris g owlAsymmetricProperty).any (fun p =>
    g.any (fun u => u.p == p &&
      g.any (fun v => v.p == p && v.s.toTerm == u.o && v.o == u.s.toTerm)))

def irreflexivityViolation (g : Graph) : Bool :=
  (collectTypedIris g owlIrreflexiveProperty).any (fun p =>
    g.any (fun u => u.p == p && u.o == u.s.toTerm))

/-- G10: an `owl:hasKey` violation.

    OWL 2 Direct Semantics §2.3.5 gives
    `HasKey(CE (p1 … pm) (d1 … dn))` the condition: if `x` and `y` are
    both in `CE`, and for every key property `pi` there is a value `v`
    with `⟨x,v⟩` and `⟨y,v⟩` in `pi`, then `x = y`. Two individuals
    the graph forces apart therefore contradict the key.

    OWL 2 Syntax §9.5 restricts the condition to NAMED individuals —
    "the key is applied only to individuals that are explicitly named
    in the ontology" — which is why only IRI subjects are paired here.
    That restriction is also what makes a graph-level test the right
    shape: no witness needs to be built.

    `owl:Thing` as the class expression is every individual, so the
    membership test is skipped for it. For any other named class the
    membership must be IN THE GRAPH, which after the RL closure is
    where an entailed `rdf:type` is. A membership the closure did not
    derive withholds the violation. -/
def hasKeyViolation (g : Graph) : Bool :=
  let st := Store.ofGraph g
  g.any (fun t =>
    t.p == owlHasKey &&
    (match t.s with
     | .bnode _ => false
     | .iri c =>
       let keys := (walkRdfList st t.o 64).filterMap (fun u =>
         match u with
         | .iri k => some k
         | _      => none)
       if keys.isEmpty then false
       else
         -- Only individuals that carry EVERY key property can share a
         -- value on every one of them, so the pair loop runs over
         -- those alone.
         let named : List Term :=
           (g.filterMap (fun u =>
             match u.s with
             | .iri a => if keys.contains u.p then some (Term.iri a) else none
             | _      => none)).eraseDups
         let cands := named.filter (fun a =>
           (c == owlThing ||
            g.any (fun u => u.p == rdfType && u.o == Term.iri c &&
                            u.s.toTerm == a)) &&
           keys.all (fun k => g.any (fun u => u.p == k && u.s.toTerm == a)))
         cands.any (fun a => cands.any (fun b =>
           provablyDistinct g a b &&
           keys.all (fun k =>
             g.any (fun u => u.p == k && u.s.toTerm == a &&
               g.any (fun v => v.p == k && v.s.toTerm == b && v.o == u.o))))))) 

def immediateInconsistency (g : Graph) : Bool :=
  allDifferentViolation g || bottomPropertyAssertion g ||
  selfDisjointPropertyInUse g ||
  nilStructureViolation g || hasSelfDisjointViolation g ||
  thingIsNothing g || disjointPropertiesShareAPair g ||
  allDisjointPropertiesViolation g ||
  asymmetryViolation g || irreflexivityViolation g ||
  hasKeyViolation g

/-! ## The TBox

Axioms are `(lhs, rhs)` pairs of NNF class expressions. A node whose
label matches `lhs` structurally gains `rhs`. Each pair satisfies
`CEXT(lhs) ⊆ CEXT(rhs)` in every model of the graph:

* `A rdfs:subClassOf B` gives `A ⊑ B`;
* `A owl:equivalentClass B` gives `A ⊑ B` and `B ⊑ A`, and — since
  it is a genuine iff — both contrapositives `¬B ⊑ ¬A` and
  `¬A ⊑ ¬B`. The contrapositives are what let a definition fire
  through a negated name, which plain unfolding never does;
* `A owl:disjointWith B` gives `A ⊑ ¬B` and `B ⊑ ¬A`;
* `A owl:complementOf B` gives the same pair.

The contrapositive is NOT taken for `rdfs:subClassOf`: `¬B ⊑ ¬A`
does not follow from `A ⊑ B` as an unfolding rule the way it does
from an equivalence, because the tableau applies these left to right
on labels a node actually carries. -/

/-! ### Provably empty named classes become `owl:Nothing`

A named class whose superclass restrictions put BOTH a `≥ k p` and a
`≤ j p` on the same property with `j < k` has an empty extension in
every model: a member would need at least `k` and at most `j`
successors at once. Replacing such a class with `owl:Nothing` swaps
one class for another of IDENTICAL extension, so it is sound in
either polarity.

The payoff is syntactic. Axiom left-hand sides are matched
STRUCTURALLY, so a fixture that defines its own bottom class makes
`∀q.first:Nothing` and `∀q.owl:Nothing` — the same extension — two
expressions that never match each other. Normalising makes them one.

Detection is deliberately narrow: only the direct min/max pair, and
only for classes that appear as an `owl:allValuesFrom` filler, which
is where the normalisation pays. MISSING an empty class is sound
(nothing is normalised); claiming one falsely is not, and cannot
happen — the pair is entailed of the class, and `k > j` has no
model. -/

def superclassCes (st : Store) (c : WfIri) : List ClassExpr :=
  (st.withSubjPred (.iri c) rdfsSubClassOf ++ st.withSubjPred (.iri c) owlEquivalentClass).map
    (fun t => parseClassExpr st t.o 8)

def cesMinMaxClash (ces : List ClassExpr) : Bool :=
  ces.any (fun ce => match ce with
    | .minCard k p =>
        k ≥ 1 && ces.any (fun d => match d with
                                   | .maxCard j q => q == p && j < k
                                   | _            => false)
    | _ => false)

/-- Store-parameterised: the graph it reads is `st.graph`. -/
def unsatNamedClassesS (st : Store) : List WfIri :=
  let fillers := (st.graph.filterMap (fun t =>
    if t.p == owlAllValuesFrom then
      match t.o with
      | .iri c => some c
      | _      => none
    else none)).eraseDups
  fillers.filter (fun c => cesMinMaxClash (superclassCes st c))

def unsatNamedClasses (g : Graph) : List WfIri :=
  unsatNamedClassesS (Store.ofGraph g)

mutual

partial def normalizeUnsat (us : List WfIri) : ClassExpr → ClassExpr
  | .named c            => if us.contains c then .named owlNothing else .named c
  | .someOf p c         => .someOf p (normalizeUnsat us c)
  | .allOf p c          => .allOf p (normalizeUnsat us c)
  | .complement c       => .complement (normalizeUnsat us c)
  | .intersection cs    => .intersection (normalizeUnsatList us cs)
  | .union cs           => .union (normalizeUnsatList us cs)
  | .minQualCard k p c  => .minQualCard k p (normalizeUnsat us c)
  | .maxQualCard k p c  => .maxQualCard k p (normalizeUnsat us c)
  | .exactQualCard k p c => .exactQualCard k p (normalizeUnsat us c)
  | ce                  => ce

partial def normalizeUnsatList (us : List WfIri) : List ClassExpr → List ClassExpr
  | []      => []
  | c :: tl => normalizeUnsat us c :: normalizeUnsatList us tl

end

/-- A blank node the OWL RL closure minted as SCAFFOLDING.

    `RLRules.lean` materialises canonical restriction-membership
    blank nodes (`__rl_comp__…`, `__rl_minc1__…`) as SUPPORT triples
    for the corpus's blank-node conclusion matching. Their encoding
    is deliberately loose — membership is asserted on a weaker
    condition than the class expression they resemble would require —
    so reading one literally as a class expression MANUFACTURES
    refutations of consistent premises. Every class expression this
    module parses maps them to `unknown`, which is inert in labels,
    axioms and branching. Dropping a constraint is always sound. -/
def isScaffoldBNode : Term → Bool
  | .bnode b => b.startsWith "__rl_"
  | _        => false

/-- Normalise BETWEEN parse and NNF, so the NNF negation of a
    normalised bottom simplifies (`nnfNeg owl:Nothing = owl:Thing`)
    and the two spellings of a complement pair converge. Normalising
    AFTER the NNF would leave `∃q.¬first:Nothing` beside
    `∃q.owl:Thing` — one extension, two expressions, no match. -/
def parseNnfWith (us : List WfIri) (st : Store) (t : Term) : ClassExpr :=
  if isScaffoldBNode t then .unknown
  else nnf (normalizeUnsat us (parseClassExpr st t 32))

/-- `parseNnfSubjectWith` with the marker-walk fuel given
    (`parseCeOfSubjectFuel`). -/
def parseNnfSubjectWithFuel (us : List WfIri) (st : Store) (fuel : Nat) (sub : Subject)
    : ClassExpr :=
  if isScaffoldBNode sub.toTerm then .unknown
  else nnf (normalizeUnsat us (parseCeOfSubjectFuel st fuel sub))

def parseNnfSubjectWith (us : List WfIri) (st : Store) (sub : Subject) : ClassExpr :=
  parseNnfSubjectWithFuel us st (st.graph.length + 8) sub

def parseNnf (st : Store) (t : Term) : ClassExpr := nnf (parseClassExpr st t 32)

def parseNnfSubject (st : Store) (s : Subject) : ClassExpr :=
  nnf (parseCeOfSubject st s)

/-- A NAMED class that carries the restriction markers itself.

    The OWL 2 RDF mapping (Table 13 of https://www.w3.org/TR/owl2-mapping-to-rdf/)
    reads `z owl:onProperty p . z owl:maxQualifiedCardinality 1 .
    z owl:onClass c` as the class expression, whatever `z` is; when
    `z` is an IRI the triples say that the class `z` IS that
    restriction, so `CEXT(z)` and the restriction's extension are the
    same set and the inclusion holds in both directions.

    `collectAxiomsS` reads axioms off `rdfs:subClassOf`,
    `owl:equivalentClass`, `owl:disjointWith` and `owl:complementOf`
    triples only, so a restriction written directly on a named class,
    with no axiom triple beside it, produced no TBox entry at all: the
    node typed `z` got the label `.named z` from `initState`, the
    bound never became a label, and no cardinality rule could fire.
    That is the shape of `rdfbased-sem-restrict-maxqcr-inst-obj-one`.

    Only `owl:onProperty` subjects are read here. A named-subject
    `owl:unionOf` / `owl:intersectionOf` / `owl:complementOf` /
    `owl:oneOf` marker is left to the arms below, whose treatment of
    it is already decided and measured. -/
def namedRestrictionAxioms (us : List WfIri) (st : Store)
    : List (ClassExpr × ClassExpr) :=
  let subs := (st.graph.filterMap (fun t =>
    if t.p == owlOnProperty then
      match t.s with
      | .iri c   => some c
      | .bnode _ => none
    else none)).eraseDups
  let fuel := st.graph.length + 8
  subs.flatMap (fun c =>
    match parseNnfSubjectWithFuel us st fuel (.iri c) with
    | .unknown => []
    | .named d => if d == c then [] else [(.named c, .named d), (.named d, .named c)]
    | ce       => [(.named c, ce), (ce, .named c)])

/-- A NAMED class that carries `owl:oneOf` itself.

    OWL 2 RDF-Based Semantics §5.6 (and the OWL 1 RDF mapping the
    WebOnt fixtures are written in): `c owl:oneOf (a₁ … aₙ)` makes the
    class extension of `c` exactly `{a₁ … aₙ}`. A class may carry
    several such lists (`WebOnt-description-logic-502` gives `TorF`
    ten), and each one is an equality, so each gives both inclusions
    between `c` and its nominal. -/
def namedOneOfAxioms (st : Store) : List (ClassExpr × ClassExpr) :=
  (st.withPred owlOneOf).flatMap (fun t =>
    match t.s with
    | .bnode _ => []
    | .iri c   =>
      match walkRdfList st t.o 64 with
      | []      => []
      | members => [(.named c, .oneOf members), (.oneOf members, .named c)])

def owlDisjointUnionOf : WfIri := ⟨"http://www.w3.org/2002/07/owl#disjointUnionOf", rfl⟩

/-- A NAMED class that carries a Boolean marker itself:
    `c owl:unionOf L`, `c owl:intersectionOf L` or `c owl:complementOf
    D` with `c` an IRI. The OWL RDF mapping reads the marker as the
    class expression whatever the subject is; on an IRI it says `c` IS
    that expression (OWL 2 RDF-Based Semantics §5.4), so `c ≡ CE` with
    both contrapositives, as `owl:equivalentClass` gives.

    The `owl:complementOf` arm of `collectAxiomsS` could not do this
    for a named subject: it parses the SUBJECT, and the parse of an IRI
    carrying a marker is the marker's expression, so `A owl:complementOf
    B` produced `¬B ⊑ ¬B` and `B ⊑ B` and lost both the disjointness
    and the coverage (`WebOnt-complementOf-001`). -/
def namedBooleanAxioms (us : List WfIri) (st : Store) : List (ClassExpr × ClassExpr) :=
  let subs := ((st.withPred owlUnionOf ++ st.withPred owlIntersectionOf ++
                st.withPred owlComplementOf).filterMap (fun t =>
    match t.s with
    | .iri c   => some c
    | .bnode _ => none)).eraseDups
  let fuel := st.graph.length + 8
  subs.flatMap (fun c =>
    match parseNnfSubjectWithFuel us st fuel (.iri c) with
    | .unknown => []
    | .named d => if d == c then [] else [(.named c, .named d), (.named d, .named c)]
    | ce       =>
      if !ceDefinite ce then []
      else
        let nc := nnfNeg (.named c)
        [(.named c, ce), (ce, .named c), (nnfNeg ce, nc), (nc, nnfNeg ce)])

/-- `c owl:disjointUnionOf (C₁ … Cₙ)` (OWL 2 Syntax §9.1.4,
    `DisjointUnion`): `c ≡ C₁ ⊔ … ⊔ Cₙ` and the `Cᵢ` pairwise disjoint. -/
def disjointUnionAxioms (us : List WfIri) (st : Store) : List (ClassExpr × ClassExpr) :=
  (st.withPred owlDisjointUnionOf).flatMap (fun t =>
    match t.s with
    | .bnode _ => []
    | .iri c =>
      let parts := (walkRdfList st t.o 64).map (parseNnfWith us st)
      if parts.isEmpty || !parts.all ceDefinite then []
      else
        let u : ClassExpr := .union parts
        let nc := nnfNeg (.named c)
        [(.named c, u), (u, .named c), (nnfNeg u, nc), (nc, nnfNeg u)] ++
        (unorderedCePairs parts).flatMap (fun (a, b) => [(a, nnfNeg b), (b, nnfNeg a)]))
where
  unorderedCePairs : List ClassExpr → List (ClassExpr × ClassExpr)
    | []      => []
    | a :: tl => tl.map (fun b => (a, b)) ++ unorderedCePairs tl

/-- Is `d` a datatype, or a class every element is in? A range or
    domain of that kind constrains nothing an individual's label could
    carry: a datatype bounds data values, which no node stands for, and
    `owl:Thing` / `rdfs:Resource` hold of everything. -/
def isTrivialOrDataRangeIri (st : Store) (d : WfIri) : Bool :=
  d == owlThing || d == L4Factoidal.RDFS.rdfsResource || d == L4Factoidal.RDFS.rdfsLiteral ||
  d.val.startsWith "http://www.w3.org/2001/XMLSchema#" ||
  d.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  d == XSD.owlReal || d == XSD.owlRational ||
  (st.withSubjPred (.iri d) rdfType).any (fun t => t.o == Term.iri rdfsDatatype)

/-- `p rdfs:domain C` and `p rdfs:range C` as TBox axioms (OWL 2 Syntax
    §9.2.6, `ObjectPropertyDomain` and `ObjectPropertyRange`, whose
    Direct Semantics conditions are `∃p.⊤ ⊑ C` and `⊤ ⊑ ∀p.C`).

    The RL closure applies both to the triples the premise asserts. The
    expansion creates edges the closure never sees — a goal's fresh
    pair, a generating-rule witness — and without these axioms nothing
    puts a domain or range class on their ends. The range axiom has the
    antecedent `owl:Thing`, so `injectGlobalAxioms` puts `∀p.C` on every
    node and the `∀` rule carries `C` to every `p`-successor; the domain
    axiom's antecedent `≥ 1 p` is proved by an asserted or counted edge
    (`applyAxiomsEdges`). A datatype range or a trivial class gives no
    axiom (`isTrivialOrDataRangeIri`). -/
def domainRangeAxioms (us : List WfIri) (st : Store) : List (ClassExpr × ClassExpr) :=
  let keep (o : Term) : Bool := match o with
    | .iri d   => !isTrivialOrDataRangeIri st d
    | .bnode _ => true
    | _        => false
  ((st.withPred rdfsDomain).filterMap (fun t =>
    match t.s with
    | .iri p =>
        let c := parseNnfWith us st t.o
        if keep t.o && ceDefinite c then some (.minCard 1 p, c) else none
    | .bnode _ => none)) ++
  ((st.withPred rdfsRange).filterMap (fun t =>
    match t.s with
    | .iri p =>
        let c := parseNnfWith us st t.o
        if keep t.o && ceDefinite c then some (.named owlThing, .allOf p c) else none
    | .bnode _ => none))

/-- Store-parameterised: the graph it reads is `st.graph`.

    Every lookup below runs through `st`, so the store decides the
    COST and not the answer. Over `Store.ofGraph g` each lookup is a
    filter of the whole list; over `Store.ofIndex (Index.ofGraph g)`
    each is a hash lookup. `collectAxioms_eq` is the record that the
    two agree. -/
def collectAxiomsS (st : Store) : List (ClassExpr × ClassExpr) :=
  let us := unsatNamedClassesS st
  namedRestrictionAxioms us st ++ namedOneOfAxioms st ++ domainRangeAxioms us st ++
  namedBooleanAxioms us st ++ disjointUnionAxioms us st ++
  -- The subject-parse fuel is the graph's length plus 8, computed
  -- once here and not per triple (`parseCeOfSubject`).
  let fuel := st.graph.length + 8
  st.graph.flatMap (fun t =>
    if t.p == rdfsSubClassOf then
      [(parseNnfSubjectWithFuel us st fuel t.s, parseNnfWith us st t.o)]
    else if t.p == owlEquivalentClass then
      let a := parseNnfSubjectWithFuel us st fuel t.s
      let b := parseNnfWith us st t.o
      [(a, b), (b, a), (nnfNeg b, nnfNeg a), (nnfNeg a, nnfNeg b)]
    else if t.p == owlDisjointWith || t.p == owlComplementOf then
      let a := parseNnfSubjectWithFuel us st fuel t.s
      let b := parseNnfWith us st t.o
      [(a, nnfNeg b), (b, nnfNeg a)]
    else [])

/-- Structural equality of TBox axiom pairs. `ClassExpr.beq` and not
    `ceEq`: `ceEq a b` is `ceDefinite a && ClassExpr.beq a b`, which is
    not reflexive on an indefinite expression, and an axiom must count
    as a duplicate of ITSELF. -/
def axiomBeq (x y : ClassExpr × ClassExpr) : Bool :=
  ClassExpr.beq x.1 y.1 && ClassExpr.beq x.2 y.2

/-- The structurally distinct axioms, FIRST occurrence kept, so the
    order of the distinct axioms is the order `collectAxiomsS` emitted
    them.

    **Why a repeated axiom changes nothing.** `applyAxioms` and
    `injectGlobalAxioms` fold over the TBox calling `addLabel`, and
    `addLabel` returns the state unchanged when the label is already
    present, so the second copy of an axiom adds nothing and reports no
    change. `applyAxiomsEdges` and `applyAxiomsConj` guard on
    `memCe a ls` before firing, so the second copy is skipped there
    too. Nothing else reads the TBox: `pendingUnion`, `pendingMerge`
    and `clashNodes` read labels and nodes.

    **Why the failure direction is safe.** If that argument were wrong,
    dropping a copy could only give a node FEWER labels, hence fewer
    clashes, hence a WITHHELD refutation — never a manufactured one.
    A wrong deduplication loses conformance units, which the corpus
    score sees; it cannot invent an entailment. -/
def dedupAxioms (tb : List (ClassExpr × ClassExpr)) : List (ClassExpr × ClassExpr) :=
  -- An axiom is compared only with the kept axioms of its own
  -- `ceIndexKey` pair: `axiomBeq` implies equal keys
  -- (`ceIndexKey_of_beq`), so no duplicate is missed. The comparison
  -- against EVERY kept axiom this replaces was quadratic in the TBox:
  -- 12 seconds per refuter call on the goal graphs of
  -- `WebOnt-miscellaneous-011`.
  let step (acc : Array (ClassExpr × ClassExpr) ×
                  Std.HashMap String (List (ClassExpr × ClassExpr)))
      (a : ClassExpr × ClassExpr) :=
    let k := ceIndexKey a.1 ++ " " ++ ceIndexKey a.2
    let bucket := acc.2.getD k []
    if bucket.any (axiomBeq a) then acc
    else (acc.1.push a, acc.2.insert k (a :: bucket))
  (tb.foldl step (#[], {})).1.toList

/-- `C₁ ⊔ … ⊔ Cₙ ⊑ D` also gives `Cᵢ ⊑ D` for each `i`. An axiom
    fires when a node's label MATCHES its antecedent, and a node
    labelled `Cᵢ` carries no union label, so the union antecedent never
    fired on it (`WebOnt-unionOf-002`: `John : Human`, with
    `B ≡ Animal ⊔ Human ⊔ Stone`, never became `B`). -/
def splitUnionAntecedents (tb : List (ClassExpr × ClassExpr)) : List (ClassExpr × ClassExpr) :=
  tb ++ tb.flatMap (fun (a, d) => match a with
    | .union ds => ds.map (fun x => (x, d))
    | _         => [])

/-- The TBox of a graph, read through the HASH INDEX.

    `collectAxiomsS` parses a class expression for BOTH sides of every
    `rdfs:subClassOf`, `owl:equivalentClass`, `owl:disjointWith` and
    `owl:complementOf` triple, and each parse makes several
    subject-plus-predicate lookups. Over the list store that is a scan
    of the whole graph per lookup, so the pass is quadratic in the
    graph and the tableau refuter pays it once per goal. Over the index
    each lookup is O(1). -/
def collectAxiomsRaw (g : Graph) : List (ClassExpr × ClassExpr) :=
  collectAxiomsS (Store.ofIndex (Index.ofGraph g))

/-- The index store and the list store give `collectAxiomsS` the same
    value, so `collectAxiomsRaw` is the list-scan definition it
    replaced. -/
theorem collectAxiomsRaw_eq (g : Graph) :
    collectAxiomsRaw g = collectAxiomsS (Store.ofGraph g) := by
  rw [collectAxiomsRaw, Store.ofIndex_eq (Index.Wf.ofGraph g)]

/-- The TBox the tableau runs against: one entry per STRUCTURALLY
    DISTINCT axiom.

    `collectAxiomsS` emits one axiom per triple, so two restriction
    nodes with the same `owl:onProperty` and the same filler produce
    the SAME class-expression pair. Measured over the whole OWL corpus
    with `l4owl-probe --tbox-census`, 214,466 axioms reduce to 73,653
    distinct ones, and on the heaviest case 18,099 reduce to 2,964.
    `onePass` folds over the WHOLE TBox once per node and once per
    label, and `search` runs it up to its budget per goal, so a
    duplicate is paid thousands of times. -/
def collectAxioms (g : Graph) : List (ClassExpr × ClassExpr) :=
  dedupAxioms (splitUnionAntecedents (collectAxiomsRaw g))

/-! ## Expansion -/

def witnessId (i : Subject) (p : WfIri) (n : Nat) : BNodeId :=
  let iStr := match i with
    | .iri s   => s.val
    | .bnode b => b
  "_:tw_" ++ iStr ++ "__" ++ p.val ++ "__" ++ toString n

def depthOf1 (st : RState) (i : Subject) : Nat :=
  match i with
  | .iri _   => 0
  | .bnode b => st.wdepth.getD b 0

/-- The witness depth of `i`'s identification group: the least depth
    of a member. A witness identified with an ABox individual is that
    individual, at depth 0. -/
def depthOf (st : RState) (i : Subject) : Nat :=
  if st.ident.isEmpty then depthOf1 st i
  else
    ((identifiedWith st i.toTerm).filterMap termAsSubject).foldl
      (fun d j => min d (depthOf1 st j)) (depthOf1 st i)

/-- Record an expansion edge in `extra` and in the subject and object
    maps. -/
def pushEdge (st : RState) (e : REdge) : RState :=
  { st with extra := st.extra.push e,
            extraOut := st.extraOut.insert e.s ((st.extraOut.getD e.s #[]).push e),
            extraIn := st.extraIn.insert e.o ((st.extraIn.getD e.o #[]).push e) }

/-- Mint witnesses for `i` on `p` until it has `k` successors, up to
    the depth and count caps. The filler is put on each witness. -/
def ensureWitnesses (g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (k : Nat) (c : ClassExpr) : RState × Bool :=
  -- `∃p.C` is DISCHARGED by a successor that carries `C`, not by any
  -- successor at all. Counting successors alone was the defect that
  -- made the ≤-rule fire and find nothing: the materialisation pass
  -- writes its own `p`-successors into the graph, and an existential
  -- whose filler is anonymous (`∃f2.¬p1`) gets an edge from it but no
  -- type — so the count said "discharged", no witness was minted, and
  -- the filler was never put on any node. Every merge branch then
  -- pooled labels that did not include it and stayed open
  -- (WebOnt-description-logic-003 and its family).
  let succs := successorsOf g st i p false
  let have' := match c with
    | .unknown => succs.length
    | _        => (successorsInFiller st c succs).length
  if have' ≥ k then (st, false)
  else if depthOf st i ≥ maxWitnessDepth then (st, false)
  else
    let want := min (k - have') maxGeneratedWitnesses
    let d := depthOf st i + 1
    (List.range want).foldl (fun (acc : RState × Bool) j =>
      let (s0, ch) := acc
      let b := witnessId i p (s0.fresh + j)
      if s0.extraIn.contains (Term.bnode b) then (s0, ch)
      else
        let s1 := { pushEdge s0 { s := i, p := p, o := .bnode b, counts := false } with
          wdepth := s0.wdepth.insert b d }
        let (s2, _) := addLabel s1 (.bnode b) c
        (s2, true)) (st, false)
    |> (fun (s, ch) => ({ s with fresh := s.fresh + want }, ch))

/-- Add `(i, p, v)` as an edge that holds in EVERY model, which is
    therefore COUNTED against cardinality bounds. -/
def addCountedEdge (st : RState) (i : Subject) (p : WfIri) (v : Term) : RState × Bool :=
  if (st.extraOut.getD i #[]).any (fun e => e.p == p && e.o == v) then (st, false)
  else (pushEdge st { s := i, p := p, o := v, counts := true }, true)

/-- Register `b` as a node with no label. A node is what the global
    rules (`injectGlobalAxioms`, `injectFunctional`) and the clash
    rules visit, so a witness the TBox must reach has to be one. -/
def addNode (st : RState) (b : Subject) : RState :=
  if st.pos.contains b then st
  else { st with nodes := st.nodes.push { id := b, labels := [] },
                 pos := st.pos.insert b st.nodes.size }

/-- The generating rule for `≥ k p` and `≥ k p.C` with `k ≥ 2`.

    OWL 2 Direct Semantics §2.2: `ObjectMinCardinality(k p C)` holds of
    `x` exactly when `#{y | ⟨x,y⟩ ∈ (p)ᴵ ∧ y ∈ (C)ᴵ} ≥ k`. So in every
    model `x` has `k` pairwise different `p`-successors in `C`. The rule
    mints `k` witnesses for them, puts `C` on each, makes each a node,
    and records the group in `RState.distinctGroups`, which is what
    makes the members provably different (`genDistinct`). The edges are
    COUNTED: the `k` successors exist in every model, and two of them
    are counted as different only where the group says so.

    The soundness argument is the standard one for the tableau's
    `≥`-rule: a model of the branch maps the `k` witnesses onto the `k`
    successors the model has, and every label the expansion later puts
    on a witness is a consequence that holds of that successor.

    Before minting, the rule asks whether `x` already has `k` successors
    in `C` that are pairwise different; if so the obligation is met.
    Capped at `maxGeneratedWitnesses` per firing and at
    `maxWitnessDepth`: a cap mints fewer witnesses, which withholds
    consequences and never invents one. Port of the F*
    `ensure_min_witnesses`. -/
def ensureDistinctWitnesses (g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (k : Nat) (c : ClassExpr) : RState × Bool :=
  let want := min k maxGeneratedWitnesses
  let succs := successorsOf g st i p false
  let inFiller := match c with
    | .unknown => succs
    | _        => successorsInFiller st c succs
  if existsDistinctSubsetBy (distinctIn g st) inFiller want then (st, false)
  else if depthOf st i ≥ maxWitnessDepth then (st, false)
  else
    let d := depthOf st i + 1
    let ids := (List.range want).map (fun j => witnessId i p (st.fresh + j))
    let st1 := ids.foldl (fun (s0 : RState) b =>
      let s1 := addNode { pushEdge s0 { s := i, p := p, o := .bnode b, counts := true } with
        wdepth := s0.wdepth.insert b d } (.bnode b)
      (addLabel s1 (.bnode b) c).1) st
    ({ st1 with fresh := st1.fresh + want,
                distinctGroups := st1.distinctGroups ++ [ids.map Term.bnode] }, true)

/-- The deterministic rules of one label. `union` is left alone — it
    is the branching rule and belongs to the search. -/
def applyLabelRules (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : RState × Bool :=
  match l with
  | .intersection cs =>
      cs.foldl (fun (acc : RState × Bool) c =>
        let (s, ch) := addLabel acc.1 i c
        (s, acc.2 || ch)) (st, false)
  | .allOf p c =>
      -- Push the filler across every `p`-successor, WITNESSES
      -- INCLUDED: `∀` constrains successors however they arose.
      let succs := successorsOf g st i p false
      let base := succs.foldl (fun (acc : RState × Bool) y =>
        match termAsSubject y with
        | none   => acc
        | some j => let (s, ch) := addLabel acc.1 j c
                    (s, acc.2 || ch)) (st, false)
      -- The SHIQ ∀⁺ rule: across a TRANSITIVE role `r ⊑* p`, the
      -- whole `∀r.c` label is re-pushed, not only `c` — otherwise a
      -- successor two `r`-steps away escapes the restriction the
      -- transitivity puts it under.
      let transRoles := (subsOf st p).filter (roleIsTransitive st)
      let pushed := transRoles.foldl (fun (acc : RState × Bool) r =>
        (successorsOf g acc.1 i r false).foldl (fun (a2 : RState × Bool) y =>
          match termAsSubject y with
          | none   => a2
          | some j => let (s, ch) := addLabel a2.1 j (.allOf r c)
                      (s, a2.2 || ch)) acc) base
      -- `EXT(owl:topObjectProperty) = Δ × Δ`: every individual is its
      -- own top-successor, so `∀top.C` puts `C` on the node itself.
      if p == owlTopObjectProperty then
        let (s, ch) := addLabel pushed.1 i c
        (s, pushed.2 || ch)
      else pushed
  -- A witness on the bottom property is never minted: the clash rule
  -- fires on the label instead, and a minted successor over an empty
  -- property would be a fabricated edge.
  --
  -- `∃p.{a}` is `p` EXACTLY to `a`: `CEXT({a}) = {aᴵ}` (OWL 2 Direct
  -- Semantics §2.2, `ObjectOneOf`), so `x ∈ ∃p.{a}` holds exactly when
  -- `⟨x, aᴵ⟩ ∈ (p)ᴵ`. The edge to `a` itself is asserted, counted like
  -- a `hasValue` edge, instead of an anonymous witness. That is what
  -- lets a bound on `a` see the edge from its INVERSE side, the
  -- "spy point" of `WebOnt-description-logic-035`. Port of the F*
  -- `ensure_existential`.
  | .someOf p c        =>
      if isBottomProp p then (st, false)
      else match c with
        | .oneOf [a] => addCountedEdge st i p a
        | _          => ensureWitnesses g st i p 1 c
  | .minQualCard k p c =>
      if isBottomProp p then (st, false)
      else if k ≥ 2 then ensureDistinctWitnesses g st i p k c
      else match c with
        | .oneOf [a] => if k == 1 then addCountedEdge st i p a else (st, false)
        | _          => ensureWitnesses g st i p k c
  | .minCard k p       =>
      if isBottomProp p then (st, false)
      else if k ≥ 2 then ensureDistinctWitnesses g st i p k .unknown
      else ensureWitnesses g st i p k .unknown
  -- A `hasValue` edge holds in EVERY model, so it is COUNTED against
  -- cardinality bounds, unlike an existential witness.
  | .hasValue p v => addCountedEdge st i p v
  | _ => (st, false)

/-- A label matching an axiom's left-hand side gains its right-hand
    side. The match is structural: two expressions that denote the
    same class but are written differently do not fire each other,
    which withholds inferences rather than inventing them. -/
def applyAxioms (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    (l : ClassExpr) : RState × Bool :=
  tb.foldl (fun (acc : RState × Bool) (a, d) =>
    if ceEq a l then
      let (s, ch) := addLabel acc.1 i d
      (s, acc.2 || ch)
    else acc) (st, false)

/-! ### Membership proved by asserted EDGES

An axiom fires when a node's LABEL matches its left-hand side. But a
node's asserted successors can PROVE it belongs to that left-hand
side even when no `rdf:type` triple says so, and without this rule
the axiom never fires on it.

Sound per shape, over COUNTED successors only:

* `≥ 1 p` — any asserted successor is a witness;
* `≥ k p` (k ≥ 2) — `k` PAIRWISE PROVABLY DISTINCT successors. A
  plain count of `k` would be unsound: two IRIs may denote one
  individual;
* `∃p.C` — a successor whose node carries `C`, which is an entailed
  membership;
* `hasValue p v` — the edge itself;
* `≥ k p.C` — as `≥ k p` over the `C`-labelled successors.

Everything else is `false`. Withholding is sound. -/
/-- The property an edge-provable antecedent is measured on: the
    shapes `edgeEntailsMembership` can prove, and `none` for every
    other shape (those it answers `false` for). -/
def edgeAntecedentProp : ClassExpr → Option WfIri
  | .minCard k p       => if k == 0 then none else some p
  | .someOf p _        => some p
  | .hasValue p _      => some p
  | .minQualCard k p _ => if k == 0 then none else some p
  | _                  => none

/-- `edgeEntailsMembership` with the node's counted successors on the
    antecedent's property already read (`succ`). The successors do not
    depend on labels, so one read serves every axiom on that
    property. -/
def edgeEntailsMembershipWith (g : Graph) (st : RState) (a : ClassExpr)
    (succ : List Term) : Bool :=
  match a with
  | .minCard k _ =>
      if k == 0 then false
      else if k == 1 then !succ.isEmpty
      else existsDistinctSubsetBy (distinctIn g st) succ k
  | .someOf _ c =>
      ceDefinite c &&
      succ.any (fun o =>
        match termAsSubject o with
        | some j => memCe c (labelsOf st j)
        | none   => false)
  | .hasValue _ v => succ.any (· == v)
  | .minQualCard k _ c =>
      if k == 0 || !(ceDefinite c) then false
      else
        let cs := successorsInFiller st c succ
        if k == 1 then !cs.isEmpty else existsDistinctSubsetBy (distinctIn g st) cs k
  | _ => false

def edgeEntailsMembership (g : Graph) (st : RState) (i : Subject) (a : ClassExpr)
    : Bool :=
  match edgeAntecedentProp a with
  | some p => edgeEntailsMembershipWith g st a (successorsOf g st i p true)
  | none   => false

/-! ### The TBox, indexed for one expansion round

`onePass` asked EVERY axiom whether it fires at every node: once per
label (`applyAxioms`), once for the node's edges
(`applyAxiomsEdges`), once for its conjunctions (`applyAxiomsConj`)
and once for the global axioms. That is `|TBox| * (3 * nodes +
labels)` tests per round. On `WebOnt-miscellaneous-011` (3,281 axioms
after the named-class axiom sources, 818 nodes) one round took 10.6
to 13 seconds, and the search runs up to the budget's rounds per
premise: the `type-consistency` gate exceeded its 1,500-second cap.

An axiom can fire only when its antecedent matches, and most
antecedents cannot match a given label or node at all. The index keeps
the TBox split by the cheap part of the antecedent (`ceIndexKey`), by
the property an edge-provable antecedent is measured on, and into the
intersection and global (`owl:Thing`) antecedents. Each rule reads
the subset that can fire. The axioms each rule fires are the ones it
fired before; only the tests that could not succeed are gone. -/

structure TBoxIndex where
  /-- Axioms by `ceIndexKey` of the antecedent. -/
  byKey      : Std.HashMap String (List (ClassExpr × ClassExpr)) := {}
  /-- Axioms with an edge-provable antecedent, by its property. -/
  edgeByProp : Std.HashMap String (List (ClassExpr × ClassExpr)) := {}
  /-- The keys of `edgeByProp`, each once. -/
  edgeProps  : List WfIri := []
  /-- Axioms whose antecedent is a non-empty intersection, by the
      `ceIndexKey` of its FIRST conjunct. Such an axiom fires only on a
      node that carries every conjunct, the first one included, so a
      node need read only the buckets of its own labels' keys. -/
  conjByKey  : Std.HashMap String (List (ClassExpr × ClassExpr)) := {}
  /-- Axioms whose antecedent is `owl:Thing` (`isTopAntecedent`). -/
  top        : List (ClassExpr × ClassExpr) := []

/-- Build the index. Every bucket keeps the TBox order. -/
def TBoxIndex.build (tb : List (ClassExpr × ClassExpr)) : TBoxIndex :=
  let ix := tb.reverse.foldl (fun (ix : TBoxIndex) (ax : ClassExpr × ClassExpr) =>
    let k := ceIndexKey ax.1
    let ix := { ix with byKey := ix.byKey.insert k (ax :: ix.byKey.getD k []) }
    let ix := match edgeAntecedentProp ax.1 with
      | some p =>
          let isNew := !ix.edgeByProp.contains p.val
          { ix with edgeByProp := ix.edgeByProp.insert p.val (ax :: ix.edgeByProp.getD p.val []),
                    edgeProps := if isNew then p :: ix.edgeProps else ix.edgeProps }
      | none => ix
    let ix := match ax.1 with
      | .intersection (c :: _) =>
          let k := ceIndexKey c
          { ix with conjByKey := ix.conjByKey.insert k (ax :: ix.conjByKey.getD k []) }
      | _ => ix
    match ax.1 with
    | .named c         => if c == owlThing then { ix with top := ax :: ix.top } else ix
    | .intersection [] => { ix with top := ax :: ix.top }
    | _                => ix) {}
  ix

/-- Fire the axioms whose left-hand side the node's EDGES prove. The
    left-hand side is added as a label too, so the label-level clash
    rules see it. Only the properties some edge-provable antecedent
    mentions are read, each once, and a property with no counted
    successor skips its axioms: every shape `edgeEntailsMembership`
    proves needs at least one successor. -/
def applyAxiomsEdges (ix : TBoxIndex) (g : Graph) (st : RState)
    (i : Subject) : RState × Bool :=
  -- The node's label read is HOISTED and refreshed only when an axiom
  -- actually fires — the sole way the labels change in this loop.
  -- Reading them per AXIOM costs one node-list walk per axiom per
  -- node per round. Adding a label adds no edge, so the successors
  -- read for a property stay valid through its bucket.
  let (st', ch, _) := ix.edgeProps.foldl (fun (acc : RState × Bool × List ClassExpr) p =>
    let succ := successorsOf g acc.1 i p true
    if succ.isEmpty then acc
    else
      (ix.edgeByProp.getD p.val []).foldl (fun (acc : RState × Bool × List ClassExpr) (a, d) =>
        let (s0, c0, ls) := acc
        if !(memCe a ls) && edgeEntailsMembershipWith g s0 a succ then
          let (s1, c1) := addLabel s0 i a
          let (s2, c2) := addLabel s1 i d
          (s2, c0 || c1 || c2, labelsOf s2 i)
        else acc) acc) (st, false, labelsOf st i)
  (st', ch)

/-- Fire an axiom whose left-hand side is an INTERSECTION when every
    conjunct is present as a SEPARATE label.

    `applyAxioms` matches one stored label against a whole left-hand
    side, so `z ≡ C₁ ⊓ C₂` never fires on a node carrying `C₁` and
    `C₂` apart. Labels are entailed memberships, and being in each
    `Cᵢ` IS being in the intersection, so the node is entailed in the
    left-hand side and hence in the right-hand side.

    Only the axioms filed under the key of one of the node's labels
    are read (`TBoxIndex.conjByKey`), and membership is read through
    the label hash index (`hasLabel`). Reading all 1,447 intersection
    axioms of `WebOnt-miscellaneous-011` at every node, each against
    the node's label list, was 2 of the 2.1 seconds of one round. -/
def applyAxiomsConj (ix : TBoxIndex) (st : RState) (i : Subject) : RState × Bool :=
  let has (s : RState) (c : ClassExpr) : Bool := ceDefinite c && hasLabel s i c
  let keys := ((labelsOf st i).map ceIndexKey).foldl
    (fun (acc : List String × Std.HashSet String) k =>
      if acc.2.contains k then acc else (k :: acc.1, acc.2.insert k)) ([], {})
  keys.1.reverse.foldl (fun (acc : RState × Bool) k =>
    (ix.conjByKey.getD k []).foldl (fun (acc : RState × Bool) (a, d) =>
      let (s0, c0) := acc
      match a with
      | .intersection cs =>
          if cs.isEmpty || has s0 a then acc
          else if cs.all (has s0) then
            let (s1, c1) := addLabel s0 i a
            let (s2, c2) := addLabel s1 i d
            (s2, c0 || c1 || c2)
          else acc
      | _ => acc) acc) (st, false)

/-- A TBox axiom whose antecedent is `owl:Thing` is a GLOBAL
    constraint, not one keyed on a label. `owl:Thing` is interpreted
    as the whole domain in every interpretation, so `owl:Thing ⊑ C`
    puts `C` on EVERY individual.

    `applyAxioms` fires an axiom only when a node's label
    structurally matches the antecedent, and no node carries
    `owl:Thing` as an asserted label, so such an axiom never fired at
    all. `owl:Thing ⊑ ≤1 f` is how the OilEd t7.3 fixture
    (`WebOnt-description-logic-030`) makes `f` functional; without it
    nothing bounds `f`, the two `f`-successors of the inner witness
    are never merged, and `p1` never meets `¬p1`.

    An empty intersection is `owl:Thing` too (`ClassExpr`), so both
    spellings fire. Sound for the same reason `injectFunctional` is:
    the consequent holds of every element, so writing it on every
    node adds a label the model already satisfies. -/
def isTopAntecedent : ClassExpr → Bool
  | .named c         => c == owlThing
  | .intersection [] => true
  | _                => false

def injectGlobalAxioms (tb : List (ClassExpr × ClassExpr)) (st : RState)
    : RState × Bool :=
  (groupLeaders st).foldl (fun (acc : RState × Bool) n =>
    tb.foldl (fun (a2 : RState × Bool) (a, d) =>
      if isTopAntecedent a then
        let (s, ch) := addLabel a2.1 n.id d
        (s, a2.2 || ch)
      else a2) acc) (st, false)

/-- `owl:FunctionalProperty p` is a global `≤ 1 p` on every node,
    which folds the functionality constraint into the existing
    max-cardinality clash rule with no new machinery. -/
def injectFunctional (st : RState) : RState × Bool :=
  (groupLeaders st).foldl (fun (acc : RState × Bool) n =>
    st.funcProps.foldl (fun (a2 : RState × Bool) p =>
      let (s, ch) := addLabel a2.1 n.id (.maxCard 1 p)
      (s, a2.2 || ch)) acc) (st, false)

/-- One saturation pass over every node and every label it carries. -/
def onePass (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    : RState × Bool :=
  let ix := TBoxIndex.build tb
  let (st0, ch0) := injectFunctional st
  let (st1, chG) := injectGlobalAxioms ix.top st0
  let ch1 := ch0 || chG
  (groupLeaders st1).foldl (fun (acc : RState × Bool) n =>
    let byLabel := (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let (s1, c1) := applyLabelRules g a2.1 n.id l
      let (s2, c2) := applyAxioms (ix.byKey.getD (ceIndexKey l) []) s1 n.id l
      (s2, a2.2 || c1 || c2)) acc
    let (s3, c3) := applyAxiomsEdges ix g byLabel.1 n.id
    let (s4, c4) := applyAxiomsConj ix s3 n.id
    (s4, byLabel.2 || c3 || c4)) (st1, ch1)

/-! ## The ≤-rule: merging witness successors

`clashForLabel`'s `maxCard` case fires only on PROVABLY DISTINCT
successors, and it never counts witnesses. So a node with more
successors than `≤ k p` allows, whose successors are not forced
apart, is not caught by it at all — and the commonest shape is
exactly that: two separate `∃`-witnesses, or a witness and an
asserted successor of a subrole, widened together by a role
hierarchy or an `owl:FunctionalProperty` declaration. Seventeen of
the `WebOnt-description-logic` inconsistency fixtures are that shape.

The standard SHIQ ≤-rule closes it: pick two successors not yet
forced apart and IDENTIFY them, merging labels and redirecting
edges, until the count is within `k` or a clash appears.

**Why triggering on witnesses is sound.** If `≤ k p` holds of `i` in
every model and `i` has more than `k` successors as TERMS, then in
every model some two of those terms denote one domain element — that
is what `≤ k p` says, by pigeonhole. WHICH pair coincides is a
choice the rule makes arbitrarily, so for REFUTATION every choice
must close: the search branches over every mergeable pair and
requires ALL of them to clash, exactly as it does for a union's
disjuncts.

**Why only witnesses may be merged.** A witness blank node never
appears in the input graph, so every edge that could mention it
lives in `extra` and can be COMPLETELY redirected. A named
individual's graph-asserted edges cannot be rewritten this way, so
merging one in would leave a half-merged state — and a clash read
off a half-merged state is fabricated. Excluding named individuals
withholds refutations; including them would invent them.

A pair already forced apart is never offered: merging a provably
distinct pair is unsound, not merely unhelpful. -/

/-- A term the ≤-rule may identify with another: a blank node or a
    named individual, never a literal.

    **Named individuals were excluded until 2026-09-07, and excluding
    them was not the safe direction.** The header's argument was that
    a named individual's graph-asserted edges cannot be rewritten, so
    a merge would leave a half-merged state. That argument describes
    the REWRITING merge this module no longer has: `mergeInto` records
    an identification pair, and `labelsOf` / `successorsOf` pool the
    group across the input graph as well as the expansion edges
    (`identifiedWith`, used in both). Nothing is rewritten, so nothing
    is half-rewritten.

    The exclusion was also unsound in the direction that matters. The
    ≤-rule refutes a node only when EVERY offered merge closes, and
    that is an argument only if the offered merges COVER every
    coincidence a model could choose. With `≤ k p` and more than `k`
    successors, pigeonhole says some two successor TERMS denote one
    element; if the pair a model picks is not offered, "every offered
    merge closes" proves nothing. Offering only blank nodes left every
    pair involving a named successor uncovered. Offering every
    non-provably-distinct pair of resource successors restores the
    cover.

    Literals stay out. A literal and an IRI denote in disjoint domains
    under OWL 2 Direct Semantics (§ 2.2, the object domain and the
    data domain), and two literals with different values are already
    `provablyDistinct`, so no pair involving a literal is a
    coincidence a model may choose. A cardinality bound measured over
    a literal successor of an OBJECT property is outside this
    argument; it is recorded as the residual in
    `docs/designissues/2026-09-07-lean-owl-corpus-gap.md` § 11. -/
def isMergeableTerm : Term → Bool
  | .bnode _ => true
  | .iri _   => true
  | _        => false

/-- Every unordered pair of a list, first member earlier in the list.

    Identifying `a` with `b` and identifying `b` with `a` give one
    branch: both add the same identification group, and every read of
    the state (`labelsOf`, `successorsOf`, `distinctIn`) is over the
    group. Offering both doubled the branching factor of the ≤-rule at
    every level for no extra coverage. -/
def unorderedPairs : List Term → List (Term × Term)
  | []      => []
  | a :: tl => tl.map (fun b => (a, b)) ++ unorderedPairs tl

/-- The pairs the ≤-rule branches on: every pair of successors not
    provably different, since in every model of `≤ k p` with more than
    `k` successors SOME such pair denotes one element. The rule closes
    the node only when EVERY branch closes, so the list must hold every
    pair a model may identify.

    A literal is not a node and cannot be merged into one, so a pair
    with a literal member cannot be a branch. Such a pair is not
    dropped from the list: the rule offers NO branch at all when one
    exists, and the search reads that as "no choice forced", which
    withholds the refutation.

    Until 2026-10-10 the literals were filtered out first and the
    remaining pairs offered. `a : ≤ 2 dp`, `a dp 1`, `a dp "x"`,
    `a : ∃dp.xsd:integer`, `a : ∃dp.¬xsd:integer` minted two
    witnesses, offered only the witness pair, merged it into one node
    labelled `xsd:integer` and `¬xsd:integer`, and refuted the graph.
    It has a model: the witnesses are `1` and `"x"`. -/
private def witnessPairs (g : Graph) (st : RState) (succs : List Term) (k : Nat)
    : List (Term × Term) :=
  if succs.length ≤ k then []
  else
    let pairs := (unorderedPairs succs).filter (fun (a, b) =>
      a != b && !(distinctIn g st a b))
    if pairs.any (fun (a, b) => !isMergeableTerm a || !isMergeableTerm b) then []
    else pairs

/-- The witness pairs a `≤ k p` label could be forced to identify.

    The qualified bound counts only the successors PROVABLY in its
    filler, as the clash rule does. A successor not yet known to be in
    the filler may lie outside it in a model, and then nothing forces
    it to coincide with anything. -/
def mergePairsForLabel (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : List (Term × Term) :=
  match l with
  | .maxCard k p       => witnessPairs g st (successorsOf g st i p false) k
  | .maxQualCard k p c =>
      witnessPairs g st (successorsInFiller st c (successorsOf g st i p false)) k
  | _                  => []

/-- Identify `a` with `b`: ONE entry in the branch's identification
    list. Nothing is rewritten — `labelsOf` and `successorsOf` pool
    the group when they read it.

    Rewriting was tried first and does not work here. An edge
    asserted in the INPUT GRAPH cannot be rewritten at all, and the
    materialisation pass writes its own existential witnesses into
    the graph, so a rewriting merge silently missed every successor
    that came from there — which on the real path is most of
    them. -/
def mergeInto (st : RState) (a b : Term) : RState :=
  let ra := repOf st a
  let rb := repOf st b
  if ra == rb then st
  -- Every term `ra` represented is redirected to `rb`, and `ra` joins
  -- them: the `RState.ident` invariant (representatives are roots)
  -- holds afterwards because `rb` is a root and `ra` no longer is one.
  else { st with ident := (st.ident.map (fun q => if q.2 == ra then (q.1, rb) else q))
                          ++ [(ra, rb)] }

/-- The DETERMINISTIC identifications: the ones every model makes, so
    no branch is needed.

    * `≤ 1 p` on `x` (and `≤ 1 p.C`, over the successors provably in
      `C`): `#{y | ⟨x,y⟩ ∈ (p)ᴵ} ≤ 1`, so every `p`-successor of `x`
      denotes ONE element. For `k = 1` the ≤-rule has no choice to
      make: all of the successors coincide. Branching over pairs there
      (as the general ≤-rule does) costs a factorial search for a
      conclusion that holds in every model. A `owl:FunctionalProperty`
      reaches this rule through `injectFunctional`.
    * `{a}` on `x`: `CEXT({a}) = {aᴵ}` (OWL 2 Direct Semantics §2.2,
      `ObjectOneOf`), so `xᴵ = aᴵ`.

    A pair that is `distinctIn` is NOT identified: the bound or the
    nominal then has more different successors than it allows, and the
    clash rules (`clashForLabel`'s `maxCard` and `oneOf` arms) report
    it. Literals are never identified (`isMergeableTerm`). Port of the
    effect of the F* `merge_branch`/`identify_branch` at `k = 1`, where
    those branch over a choice that does not exist. -/
def forcedIdentifications (g : Graph) (st : RState) : RState × Bool :=
  let identifyAll (a2 : RState × Bool) (targets : List Term) : RState × Bool :=
    match targets with
    | []      => a2
    | t0 :: rest =>
      rest.foldl (fun (a3 : RState × Bool) t =>
        let s3 := a3.1
        if repOf s3 t == repOf s3 t0 || distinctIn g s3 t t0 then a3
        else (mergeInto s3 t t0, true)) a2
  -- `owl:InverseFunctionalProperty p`: every `p`-predecessor of one
  -- element is one element.
  let byIfp := (groupLeaders st).foldl (fun (acc : RState × Bool) n =>
    acc.1.invFuncProps.foldl (fun (a2 : RState × Bool) p =>
      identifyAll a2 ((predecessorsOf a2.1 n.id p).filter isMergeableTerm)) acc) (st, false)
  (groupLeaders byIfp.1).foldl (fun (acc : RState × Bool) n =>
    (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let s := a2.1
      let targets : List Term := match l with
        | .maxCard 1 p =>
            (successorsOf g s n.id p false).filter isMergeableTerm
        | .maxQualCard 1 p c =>
            (successorsInFiller s c (successorsOf g s n.id p false)).filter isMergeableTerm
        | .oneOf [a] => if isMergeableTerm a then [n.id.toTerm, a] else []
        -- A nominal with exactly ONE member not provably different
        -- from the node, and none identified with it yet: the node is
        -- that member in every model.
        | .oneOf ms =>
            if !ms.all isMergeableTerm ||
               ms.any (fun m => repOf s m == repOf s n.id.toTerm) then []
            else match ms.filter (fun m => !distinctIn g s n.id.toTerm m) with
              | [m] => [n.id.toTerm, m]
              | _   => []
        | _ => []
      identifyAll a2 targets) acc) byIfp

/-- The nominal choice (the O-rule): the first node carrying a nominal
    `{m₁ … mₖ}` of individuals, identified with none of them, and with
    at least two members not provably different from it. In every
    model the node IS one of those members, so the search branches over
    them and needs every branch to close; a member provably different
    from the node is no branch (no model takes it). One live member is
    `forcedIdentifications`' case, none is `clashForLabel`'s. Port of
    the F* `find_nominal_nodes`. -/
def pendingNominal (g : Graph) (st : RState) : Option (List (Term × Term)) :=
  (groupLeaders st).findSome? (fun n =>
    (labelsOf st n.id).findSome? (fun l =>
      match l with
      | .oneOf ms =>
          if ms.length < 2 || !ms.all isMergeableTerm ||
             ms.any (fun m => repOf st m == repOf st n.id.toTerm) then none
          else
            let live := ms.filter (fun m => !distinctIn g st n.id.toTerm m)
            if live.length ≥ 2 then some (live.map (fun m => (n.id.toTerm, m))) else none
      | _ => none))

/-- The first node whose `≤` label forces a merge, and the choices. -/
def pendingMerge (g : Graph) (st : RState) : Option (List (Term × Term)) :=
  (groupLeaders st).findSome? (fun n =>
    (labelsOf st n.id).findSome? (fun l =>
      match mergePairsForLabel g st n.id l with
      | []    => none
      | pairs => some pairs))

/-! ## The search

Saturate; if a clash appears, this branch closes. Otherwise take the
first unexpanded `union` label and try every disjunct: the node is
refuted only when EVERY disjunct closes. -/

inductive Verdict where
  | clash
  | open'
  | out
  deriving DecidableEq, Repr, Inhabited, Nonempty

/-- The first `(node, disjuncts)` of a `union` label none of whose
    disjuncts is already a label of that node. A union with a disjunct
    already present is satisfied and needs no branch. -/
def pendingUnion (st : RState) : Option (Subject × List ClassExpr) :=
  ((groupLeaders st).findSome? (fun n =>
    (labelsOf st n.id).findSome? (fun l =>
      match l with
      | .union cs =>
          if cs.any (fun c => memCe c (labelsOf st n.id)) then none
          else some (n.id, cs)
      | _ => none)))

/-- The search, with the budget THREADED through the branches rather
    than handed to each in full.

    A per-branch budget lets a node with `d` choices grow a tree of
    `d^budget` states: siblings each get the whole allowance and the
    total is the product. A threaded budget makes them draw from ONE
    pool, so the search costs what the pool says and no more. Running
    out answers `out`, which the caller reads as "not refuted" — the
    same withholding as every other cap here.

    Returns the verdict and what is left. -/
partial def search (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (budget : Nat) : Verdict × Nat :=
  match budget with
  | 0     => (.out, 0)
  | n + 1 =>
    if clashNodes g st then (.clash, n)
    else
      let (st', changed) := onePass tb g st
      if changed then search tb g st' n
      else if clashNodes g st' then (.clash, n)
      else
        -- Identifications every model makes come before any choice.
        let (stF, forced) := forcedIdentifications g st'
        if forced then search tb g stF n
        else if propositionalClash st' || nominalClash g st' then (.clash, n)
        else
        match pendingUnion st' with
        | some (i, cs) =>
          -- EVERY disjunct must close for the union to refute the
          -- node. One branch out of budget makes the whole answer
          -- indeterminate: it might have stayed open.
          let rec tryAll (ds : List ClassExpr) (b : Nat) : Verdict × Nat :=
            match ds with
            | []      => (.clash, b)
            | c :: tl =>
                let (sb, _) := addLabel { st' with
                  nodes := st'.nodes.map (fun m =>
                    if m.id == i then
                      RNode.ofLabels m.id (m.labels.filter (fun l =>
                          match l with
                          | .union es => !(ClassExpr.beqList es cs)
                          | _         => true))
                    else m) } i c
                match search tb g sb b with
                | (.clash, b') => tryAll tl b'
                | (.open', b') => (.open', b')
                | (.out, b')   => (.out, b')
          tryAll cs n
        | none =>
          -- No union left. The ≤-rule may still force a choice, and
          -- every mergeable pair must close; then the nominal choice,
          -- with the same AND over its branches.
          let rec tryMerges (ps : List (Term × Term)) (b : Nat) : Verdict × Nat :=
            match ps with
            | []           => (.clash, b)
            | (x, y) :: tl =>
                match search tb g (mergeInto st' x y) b with
                | (.clash, b') => tryMerges tl b'
                | (.open', b') => (.open', b')
                | (.out, b')   => (.out, b')
          match pendingMerge g st' with
          | some pairs => tryMerges pairs n
          | none =>
            match pendingNominal g st' with
            | some pairs => tryMerges pairs n
            | none       => (.open', n)

/-! ## The entry point -/

/-- A predicate in the RDF, RDFS or OWL namespace: vocabulary, not a
    property assertion between individuals. -/
def isVocabularyPredicate (p : WfIri) : Bool :=
  p.val.startsWith "http://www.w3.org/2002/07/owl#" ||
  p.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  p.val.startsWith "http://www.w3.org/2000/01/rdf-schema#"

def initState (g : Graph) : RState :=
  let sp := collectPairs g rdfsSubPropertyOf
  let props := ((sp.map (·.1)) ++ (sp.map (·.2))).eraseDups
  let st0 : RState :=
    -- A symmetric property is its own inverse (OWL 2 Direct
    -- Semantics §2.3.2: `SymmetricObjectProperty(p)` holds exactly
    -- when `⟨x,y⟩ ∈ (p)ᴵ` implies `⟨y,x⟩ ∈ (p)ᴵ`), so the pair
    -- `(p, p)` makes every edge readable in both directions.
    { inv := collectPairs g owlInverseOf ++
             (collectTypedIris g owlSymmetricProperty).map (fun p => (p, p)),
      invFuncProps := collectTypedIris g owlInverseFunctionalProperty,
      subprop := sp,
      ranges := collectPairs g rdfsRange,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty,
      subClosure := props.map (fun p => (p, subpropertiesOfRaw sp p)),
      supClosure := props.map (fun p => (p, superpropertiesOfRaw sp p)),
      store := Store.ofIndex (Index.ofGraph g) }
  -- Built in ONE pass with a hash map and the index store. The fold
  -- through `addLabel` this replaces scanned the node list per triple
  -- and parsed every type through the LIST store, quadratic in the
  -- graph: on the 30,968-triple closure of `WebOnt-miscellaneous-011`
  -- it did not finish in 95 seconds. The nodes and their labels are
  -- the same: one node per `rdf:type` subject whose type parses, then
  -- one per resource at either end of a property assertion, in first
  -- occurrence order, each label stored once.
  let store := st0.store
  let us := unsatNamedClassesS store
  let addTerm (acc : Array Subject × Std.HashMap Subject (List ClassExpr)) (x : Subject)
      : Array Subject × Std.HashMap Subject (List ClassExpr) :=
    if acc.2.contains x then acc else (acc.1.push x, acc.2.insert x [])
  let (order, labelMap) := g.foldl
    (fun (acc : Array Subject × Std.HashMap Subject (List ClassExpr)) t =>
      if t.p == rdfType then
        match parseNnfWith us store t.o with
        | .unknown => acc
        | c =>
          let (ord, m) := addTerm acc t.s
          let ls := m.getD t.s []
          if ls.any (ClassExpr.beq c) then (ord, m) else (ord, m.insert t.s (ls ++ [c]))
      else acc) (#[], {})
  -- Both ends of a property assertion are individuals, typed or not,
  -- and the global rules (`injectGlobalAxioms`: `owl:Thing ⊑ C`, the
  -- range axioms) hold of them as of every element. A term only ever
  -- seen as the subject or object of an edge was no node, so none of
  -- them reached it: the fresh pair of a `owl:FunctionalProperty`
  -- refutation goal is exactly that shape.
  let (order', labelMap') := g.foldl
    (fun (acc : Array Subject × Std.HashMap Subject (List ClassExpr)) t =>
      if isVocabularyPredicate t.p then acc
      else
        let acc1 := addTerm acc t.s
        match termAsSubject t.o with
        | some o => (match t.o with
                     | .iri _ | .bnode _ => addTerm acc1 o
                     | _ => acc1)
        | none   => acc1) (order, labelMap)
  { st0 with
      nodes := order'.map (fun x => RNode.ofLabels x (labelMap'.getD x [])),
      pos := (order'.foldl (fun (acc : Std.HashMap Subject Nat × Nat) x =>
        (acc.1.insert x acc.2, acc.2 + 1)) ({}, 0)).1 }

/-- The class-size counting rung (`OWL/CountingOracle.lean`), the
    Lean counterpart of the F* owl-runner's `class_size_refutes`.

    `classSizeUnsat g` builds a linear system over the sizes of named
    classes and answers `true` only with a Farkas certificate the
    validator accepts, so "no integer assignment satisfies the system"
    is proved (`classSizeUnsat_sound`). That the system's rows hold in
    every model of `g` is argued per row:

    * FIBER `|D| = k·|X|`: `p` functional with domain `D`,
      `D ⊑ ∃p.X` and `X ⊑ (= k inv(p))`. Every element of `D` has
      exactly one `p`-successor, in `X`, and every element of `X` has
      exactly `k` `p`-predecessors, all in `D`; so `D` is the disjoint
      union of `|X|` fibres of size `k`.
    * BIJECTION `|D| = |Y|`: `p` functional and inverse-functional,
      `D ⊑ ∃p.Y` and `Y ⊑ ∃inv(p).D`; `p` restricted to `D` is then a
      bijection onto `Y`.
    * DISJOINT UNION `|Z| = |m₁| + |m₂|`: `Z ≡ m₁ ⊔ m₂` with `m₁`
      disjoint from `m₂`.
    * BOUNDS `|C| ≥ 1` for a class enumerated by a non-empty `owl:oneOf`
      (its members are elements of it) and for a FINITE class with an
      asserted member.

    A size is an integer only for a class that is finite in every
    model, and the bounds are emitted only for classes the module
    proves finite (an enumeration, and the fibre, bijection and union
    rows propagate finiteness both ways); every equation is homogeneous,
    so a component with no finite class has the all-zero solution and
    cannot make the system unsatisfiable. The row arguments are prose,
    in both trees; the arithmetic is proved. `WebOnt-description-logic-910`
    (`20 · 30 ≠ 601`) and `one=two` are decided here; `-909` is not, and
    the module header says why. -/
def countingRefutes (g : Graph) : Bool := L4Factoidal.OWL.CountingOracle.classSizeUnsat g

/-- The three-valued satisfiability verdict — the Lean counterpart of
    F* `Tableau_Refute.tableau_consistent`, meaning for meaning:

    * `some false` — provably inconsistent: an immediate graph-level
      violation, or a clash on every branch of the search;
    * `some true` — saturated and branched to quiescence with no
      clash. NOT a completeness guarantee (module header);
    * `none` — budget exhausted, indeterminate.

    The budget is the caller's: it is threaded through the whole
    branch search (see `search`), so cost is close to linear in it
    and running out is reported, never silently absorbed. -/
def tableauConsistent (g : Graph) (budget : Nat) : Option Bool :=
  if immediateInconsistency g || countingRefutes g then some false
  else
    let tb := collectAxioms g
    match (search tb g { initState g with tbox := tb } budget).1 with
    | .clash => some false
    | .open' => some true
    | .out   => none

/-- Is this graph provably UNSATISFIABLE?

    The refutation-only view of `tableauConsistent` (one search path —
    this is a projection, not a second procedure): `some false` means
    refuted, no model exists; `none` means not refuted, which covers
    both "the budget ran out" and "the expansion went quiet without a
    clash". Callers that must not act on quiescence (the harness's
    inconsistency judges) consume this view; callers serving the wire
    contract's three-valued verdict use `tableauConsistent`. -/
def refute (g : Graph) (budget : Nat) : Option Bool :=
  match tableauConsistent g budget with
  | some false => some false
  | _          => none

/-- The two views agree on refutation: `refute` says `some false`
    exactly when `tableauConsistent` does. With `refute` defined as a
    projection the proof is case analysis on the shared verdict. -/
theorem refute_eq_false_iff (g : Graph) (budget : Nat) :
    refute g budget = some false ↔ tableauConsistent g budget = some false := by
  unfold refute
  cases h : tableauConsistent g budget with
  | none => simp
  | some b => cases b <;> simp

end L4Factoidal.OWL.Refute
