/-
L4Factoidal.Proof.Syntax — FPP0, the Factoidal Proof Profile, version
0: the bundle vocabulary a heterogeneous proof chain is written in,
and `Derives`, the relation a checked bundle establishes.

Design: `docs/designissues/2026-08-26-proof-profile-fpp0-adoption.md`
sections 1 (four evidence levels), 2 (restricted control), 3 (the
theorem target carries the assumption frontier), 4 (identity is
syntactic), 8a (the degenerate bundle) and 8b (V must cite a
theorem); and
`docs/designissues/2026-08-26-proof-certificate-v1.md` sections 2
(trust model), 3 (RDFC-1.0 graph identity) and 5 (rejection table).

Milestone M0 of the adoption doc: freeze the model.

## What a bundle is

An `Artifact` names a value by its digest. An `Assumption` is an
external fact ENTERING the chain, at an evidence level that is never
foundational. A `BundleStep` is one node of the operation DAG: a
foundational rule application, or an adapter's evidence at V, R or A.
A `Bundle` is the four tables plus the claim it ends at.

## The foundational rule family

FPP0's only foundational rules are the RDF 1.1 Semantics section 8.1
and section 9.2 rows, and they are checked by the RDFS derivation
checker that already landed
(`L4Factoidal.RDFS.DerivationCheck`, commit cb9092d146f). This module
does not restate a single row: `Derives.rdfsRow` carries an
`RDFS.DerivesFull` term, and `Proof/Checker.lean` obtains that term
from `RDFS.stepOk_sound`.

Section 2 of the adoption doc bans a `semanticConsequence` rule. No
constructor below asks whether premises entail a conclusion. Every
foundational check is a finite membership or list test.

## Identity is syntactic (adoption doc section 4)

`Claim` has `DecidableEq`, and that decision is the join. A
`clif` claim carries ALPHA-NORMALISED CLIF text (`CL.Alpha.alphaCanon`
produces it) and joins by string equality; an `rdfDerivable` claim
joins on two RDFC-1.0 digests plus the triple. Nothing here decides
logical equivalence, and no reasoner is consulted to merge two
claims.

DEVIATION from the brief's sketch, recorded because it is visible in
every signature: the sketch spelled claims as `String`. They are a
structured `Claim` here. A bare string would force the kernel either
to PARSE a claim back into a triple before it could check an RDFS
row, or to carry the same content twice and hope the two agree. It
would also put an unproved obligation on the critical path — that the
string rendering is injective — because a non-injective rendering
lets a step derived for one claim be read as a proof of another.
`Claim.render` exists for display and is not the identity.

## Blank nodes are scoped to their artifact (issue 976)

A raw claim is read in a SCOPE before anything joins on it: the
artifact the step reads, or the assumption or adapter step that states
it. Equal blank-node labels in two scopes are different nodes, also
when the two artifacts share an RDFC-1.0 digest (RDF 1.1 Concepts
sections 3.4 and 3.5; RDF 1.1 Semantics section 5.2). Section "Blank-node
scope" below, and adoption doc section 4a.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.DerivationCheck
import L4Factoidal.RDF.Canonical
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.FPP0

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Profile version

Adoption doc section 2: the control structures are a FIXED, VERSIONED
profile. A step naming another profile is rejected rather than read
under this one's rules (certificate v1 section 5, last row). -/

/-- The one profile string this kernel understands. -/
def fpp0Profile : String := "fpp0/1"

/-! ## Evidence levels (adoption doc section 1) -/

/-- The four evidence strengths. A result reports the MIX; it never
collapses them to one green tick.

* `foundational` — this kernel checked the step in a fixed calculus.
* `verifiedReplay` — a verified evaluator established the result for
  the declared semantics. Section 8b: such a step MUST cite a named
  theorem, by fully-qualified name and module.
* `replay` — deterministic and re-runnable with pinned inputs, tool
  and version; the evaluator is not in the trusted kernel.
* `attestation` — a named agent states that an operation was
  performed or a source observed. -/
inductive EvidenceLevel where
  | foundational
  | verifiedReplay
  | replay
  | attestation
  deriving DecidableEq, Repr, Inhabited

/-- What kind of value an artifact names. -/
inductive ArtifactKind where
  /-- An RDF graph, identified by its RDFC-1.0 canonical hash
  (certificate v1 section 3). -/
  | graph
  /-- An opaque byte sequence, identified by SHA-256 of the bytes. -/
  | bytes
  /-- A proposition. -/
  | claim
  /-- A SPARQL solution sequence. -/
  | solutions
  deriving DecidableEq, Repr, Inhabited

/-- The RDFC-1.0 canonical hash of a graph, read as the default graph
of a dataset — certificate v1 section 3. This is the digest an
`ArtifactKind.graph` artifact carries, and the only digest this
module computes. -/
def graphDigest (g : Graph) : String :=
  Dataset.canonicalHash { default := g, named := [] }

/-- A content-addressed value the bundle refers to.

`body` is the OPTIONAL inline graph of certificate v1 section 4
("inline artifact bodies may be omitted when the checker already
holds them; hashes may not"). When it is present the kernel checks
that its RDFC-1.0 digest is the declared one, so an inline body can
never disagree with the identity it is filed under. When it is absent
the digest is a REFERENCE the kernel does not resolve, and any leaf
fact about that graph has to enter as an assumption instead. -/
structure Artifact where
  id : String
  kind : ArtifactKind
  /-- RDFC-1.0 canonical hash for a graph; SHA-256 of the bytes
  otherwise. -/
  digest : String
  /-- Inline graph body, when the producer chose to include one. -/
  body : Option Graph := none
  deriving DecidableEq, Repr, Inhabited

/-- A named Lean statement. DATA: the kernel does NOT check that the
theorem exists or that it says what the name suggests — the same
discipline `checkDerivation_ignores_tags` states for the RDFS
checker's `assurance` field. What the kernel DOES enforce is
adoption-doc section 8b: a step at `verifiedReplay` with no citation
is REJECTED, not quietly re-levelled. -/
structure Citation where
  theoremName : String
  module : String
  deriving DecidableEq, Repr, Inhabited

/-- What a step or an assumption asserts.

Two shapes, and identity is structural equality on them.

* `rdfDerivable graph axioms t` — the triple `t` is derivable by the
  RDF 1.1 Semantics section 8.1 / section 9.2 rows from the graph
  whose RDFC-1.0 digest is `graph`, under the axiom set whose
  RDFC-1.0 digest is `axioms`. The blank nodes of `t` are the
  producer's raw labels; the kernel reads them in the scope of the
  step or assumption that states the claim (issue 976), so a claim
  never names a blank node of another artifact. BOTH digests are part
  of the claim:
  derivability is relative to a regime, so a claim that named only
  the graph would be true under one axiom set and false under
  another, and two such claims must not join.
* `clif p` — a proposition, carried as ALPHA-NORMALISED CLIF text
  (adoption doc section 4). Two `clif` claims join exactly when their
  normalised text is equal. -/
inductive Claim where
  | rdfDerivable (graph : String) (axioms : String) (t : Triple)
  | clif (proposition : String)
  deriving DecidableEq, Repr

/-- A canonical default claim, so `Array` indexing with `[i]!` works
in tests and in a wasm ABI wrapper. Never reaches a reader: every use
is guarded by an in-range test. -/
instance : Inhabited Claim := ⟨.clif ""⟩

/-- Display text for a claim. PRESENTATION ONLY — `DecidableEq` on
`Claim` is the identity the kernel joins on, never this string. -/
def Claim.render : Claim → String
  | .rdfDerivable g a t =>
      "(rdf-derivable " ++ g ++ " " ++ a ++ " "
        ++ Canonical.canonQuad (none, t) ++ ")"
  | .clif p => p

/-- An external fact ENTERING the chain (adoption doc section 3).

`level` is never `foundational` — a fact this kernel checked is a
step, not an assumption. The rule is enforced by the CHECKER
(`Checker.lean`, `assumptionEnv`), not by the type, so that a bundle
declaring a foundational assumption is a REJECTION a test can pin.
Encoding it in the type would make the defect unrepresentable and
therefore untestable. -/
structure Assumption where
  id : String
  /-- What the assumption asserts. -/
  subject : Claim
  level : EvidenceLevel
  deriving DecidableEq, Repr

instance : Inhabited Assumption := ⟨{ id := "", subject := default, level := .attestation }⟩

/-- The claim text of an assumption, for a reader. Presentation only,
as `Claim.render` is. -/
def Assumption.claim (a : Assumption) : String := a.subject.render

/-- What licenses a step.

Adoption doc section 2's grammar has `rule` and `adapterEvidence`,
and nothing else. There is deliberately no rule whose check is "do
the premises entail this".

* `rule r graphArtifact axiomArtifact` — one RDF 1.1 Semantics row,
  read over the graph and axiom set those two artifacts name. Always
  foundational.
* `adapterEvidence adapter detail` — an adapter states its result.
  Never foundational: its conclusion enters the reported frontier as
  a named assumption. -/
inductive Justification where
  | rule (row : RuleId) (graphArtifact : String) (axiomArtifact : String)
  | adapterEvidence (adapter : String) (detail : String)
  deriving DecidableEq, Repr, Inhabited

/-- One node of the operation DAG.

`premises` are step or assumption IDS. The checker resolves each
against the prefix it has already accepted, so a premise can only
ever name something STRICTLY EARLIER — which is what makes a cycle,
a forward reference and a self-justification the same rejection. -/
structure BundleStep where
  id : String
  justification : Justification
  /-- Ids of earlier steps, or of declared assumptions. -/
  premises : List String
  conclusion : Claim
  level : EvidenceLevel
  /-- The profile the step is written in. Must be `fpp0Profile`. -/
  profile : String
  /-- Required at `verifiedReplay` (adoption doc section 8b). -/
  citation : Option Citation := none
  deriving DecidableEq, Repr

instance : Inhabited BundleStep :=
  ⟨{ id := "", justification := default, premises := [], conclusion := default,
     level := .attestation, profile := fpp0Profile, citation := none }⟩

/-- A proof bundle: the artifact table, the declared assumptions, the
steps in topological order, and the claim the bundle ends at. -/
structure Bundle where
  artifacts : Array Artifact
  assumptions : Array Assumption
  steps : Array BundleStep
  conclusion : Claim
  deriving DecidableEq, Repr

/-! ## Blank-node scope (issue 976)

RDF 1.1 Concepts section 3.4: blank-node identifiers are LOCAL to a
concrete syntax document or graph store, and section 3.5 lets an
implementation replace them by others. RDF 1.1 Semantics section 5.2:
the merge of two graphs renames their blank nodes apart before the
union is taken. RDFC-1.0 identifies a graph up to blank-node
isomorphism, so two artifacts with the same digest give NO
correspondence between their raw labels.

The kernel therefore never joins a raw label. A blank node `_:x` read
from the graph artifact with id `G` is the scoped node
`scopeLabel (.artifact "G") "x"`; a blank node in a declared
assumption, or in the conclusion of an adapter step, is scoped by
that assumption's or step's own id (`Scope.frontier`). Equal labels
in two different scopes are different nodes (`scopeLabel_inj`).
There is no relabelling step in FPP0/1: a premise can cross from one
artifact to another only through triples with no blank node, which
every scope leaves unchanged (`Triple.scoped_of_isGround`).

The bundle FORMAT is unchanged. Claims in a bundle still carry the
producer's raw labels; the kernel reads each raw claim in the scope of
the step or assumption that states it. -/

/-- Where the blank nodes of a claim live: a graph artifact, or the
assumption or adapter step that states the claim. -/
inductive Scope where
  | artifact (id : String)
  | frontier (id : String)
  deriving DecidableEq, Repr, Inhabited

/-- The scope as characters, with a one-character tag that keeps the
two constructors apart. -/
def Scope.tag : Scope → List Char
  | .artifact id => 'a' :: id.toList
  | .frontier id => 'f' :: id.toList

theorem Scope.tag_inj : ∀ {s s' : Scope}, s.tag = s'.tag → s = s'
  | .artifact a, .artifact a', h => by
      simp only [Scope.tag, List.cons.injEq, true_and] at h
      rw [String.toList_inj.1 h]
  | .frontier a, .frontier a', h => by
      simp only [Scope.tag, List.cons.injEq, true_and] at h
      rw [String.toList_inj.1 h]
  | .artifact _, .frontier _, h => by simp [Scope.tag] at h
  | .frontier _, .artifact _, h => by simp [Scope.tag] at h

/-- A self-delimiting encoding: every character is followed by `'0'`,
and the end is the pair `'.' '1'`. So the encoded scope ends at a
position the decoder can find, whatever characters the scope id and
the label contain. -/
def encodeScopeChars (l : List Char) : List Char :=
  l.flatMap (fun c => [c, '0']) ++ ['.', '1']

theorem encodeScopeChars_nil : encodeScopeChars [] = ['.', '1'] := rfl

theorem encodeScopeChars_cons (c : Char) (cs : List Char) :
    encodeScopeChars (c :: cs) = c :: '0' :: encodeScopeChars cs := by
  simp [encodeScopeChars]

theorem encodeScopeChars_append_inj :
    ∀ {l l' r r' : List Char},
      encodeScopeChars l ++ r = encodeScopeChars l' ++ r' → l = l' ∧ r = r'
  | [], [], _, _, h => by simpa [encodeScopeChars_nil] using h
  | [], _ :: _, _, _, h => by simp [encodeScopeChars_nil, encodeScopeChars_cons] at h
  | _ :: _, [], _, _, h => by simp [encodeScopeChars_nil, encodeScopeChars_cons] at h
  | c :: cs, c' :: cs', r, r', h => by
      simp only [encodeScopeChars_cons, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hc, hrest⟩ := h
      obtain ⟨h1, h2⟩ := encodeScopeChars_append_inj hrest
      exact ⟨by rw [hc, h1], h2⟩

/-- The label a raw blank-node label `b` gets in scope `s`. -/
def scopeLabel (s : Scope) (b : BNodeId) : BNodeId :=
  String.ofList (encodeScopeChars s.tag ++ b.toList)

/-- **Scoped labels are renamed apart.** Two scoped labels are equal
only when the scopes AND the raw labels are equal. So `_:x` from
artifact `G1` and `_:x` from artifact `G2` are different nodes, and
the scoped artifacts below form an RDF 1.1 Semantics section 5.2
merge, not a union. -/
theorem scopeLabel_inj {s s' : Scope} {b b' : BNodeId}
    (h : scopeLabel s b = scopeLabel s' b') : s = s' ∧ b = b' := by
  have h1 := congrArg String.toList h
  simp only [scopeLabel, String.toList_ofList] at h1
  obtain ⟨ht, hb⟩ := encodeScopeChars_append_inj h1
  exact ⟨Scope.tag_inj ht, String.toList_inj.1 hb⟩

/-- A triple read in scope `s`: every blank node relabelled by
`scopeLabel s`, inside RDF 1.2 triple terms too. -/
def _root_.L4Factoidal.RDF.Triple.scoped (s : Scope) (t : Triple) : Triple :=
  t.renameBnodes (scopeLabel s)

/-- A claim read in scope `s`. A `clif` claim has no RDF blank node
and is unchanged. -/
def Claim.scoped (s : Scope) : Claim → Claim
  | .rdfDerivable gd ad t => .rdfDerivable gd ad (t.scoped s)
  | .clif p => .clif p

theorem _root_.L4Factoidal.RDF.Term.renameBnodes_of_bnodes_nil (f : BNodeId → BNodeId)
    (o : Term) (h : o.bnodes = []) : o.renameBnodes f = o := by
  induction o with
  | iri _ => rfl
  | bnode _ => simp [Term.bnodes] at h
  | literal _ => rfl
  | tripleTerm s p o ih =>
      simp only [Term.bnodes, List.append_eq_nil_iff] at h
      cases s with
      | iri i => simp [Term.renameBnodes, Subject.renameBnodes, ih h.2]
      | bnode _ => simp [Subject.bnodes] at h

/-- **A ground triple is the same in every scope.** This is the only
way a premise crosses from one artifact to another in FPP0/1. -/
theorem _root_.L4Factoidal.RDF.Triple.scoped_of_isGround {t : Triple} (s : Scope)
    (h : t.isGround = true) : t.scoped s = t := by
  simp only [Triple.isGround, Triple.bnodes, List.isEmpty_iff,
    List.append_eq_nil_iff] at h
  obtain ⟨hs, ho⟩ := h
  cases t with
  | mk ts tp to =>
    cases ts with
    | iri i =>
        simp [Triple.scoped, Triple.renameBnodes, Subject.renameBnodes,
          Term.renameBnodes_of_bnodes_nil _ to ho]
    | bnode _ => simp [Subject.bnodes] at hs

/-! ## The merge of the cited artifacts -/

/-- An artifact's inline body, read in the artifact's own scope. A
body-less artifact contributes nothing. -/
def Artifact.scopedBody (a : Artifact) : Graph :=
  match a.body with
  | some g => g.map (Triple.scoped (.artifact a.id))
  | none => []

/-- The RDF 1.1 Semantics section 5.2 MERGE of every artifact filed
under digest `d`: each body renamed apart by its artifact id
(`scopeLabel_inj`), then the union taken. -/
def mergeOf (A : List Artifact) (d : String) : Graph :=
  (A.filter (fun a => a.digest == d)).flatMap Artifact.scopedBody

theorem mem_mergeOf {A : List Artifact} {a : Artifact} {g : Graph} {t : Triple}
    (hA : a ∈ A) (hb : a.body = some g) (ht : t ∈ g) :
    t.scoped (.artifact a.id) ∈ mergeOf A a.digest := by
  refine List.mem_flatMap.2 ⟨a, List.mem_filter.2 ⟨hA, by simp⟩, ?_⟩
  simp only [Artifact.scopedBody, hb]
  exact List.mem_map_of_mem ht

/-! ## `Derives` — what a checked bundle establishes

The FPP0 analogue of `RDFS.DerivesFull`, and the right-hand side of
`checkBundle_sound`. Adoption doc section 3: the theorem target is
`Derives artifacts assumptions conclusion`, NOT "the bundle is true".

Claims here are SCOPED claims (section "Blank-node scope" above). The
artifact table `A` is a parameter: a leaf fact is a triple of an
artifact's own inline body, read in that artifact's scope. Before
issue 976 the leaf constructor accepted ANY graph whose digest matched,
so two labellings of one isomorphism class could both supply leaves
and their raw labels joined; `Derives.toMerge` below is the statement
that rules this out.

⚠️ Adoption doc section 8a: this relation is TRIVIALLY satisfiable by
declaring the conclusion as an assumption — the `assumption`
constructor alone proves it. That is why `CheckResult` reports the
frontier, the per-level counts and `foundationalOnly`, and why a
reader must read those and not `valid` alone. -/
inductive Derives (A : List Artifact) (Γ : List Assumption) : Claim → Prop where
  /-- An external fact, visible in the frontier, read in its own
  scope. -/
  | assumption {a : Assumption} (h : a ∈ Γ) :
      Derives A Γ (a.subject.scoped (.frontier a.id))
  /-- A triple of the inline body of a graph artifact filed under
  digest `gd` — RDFS `base`, read in the artifact's scope. -/
  | rdfsBase {gd ad : String} {art : Artifact} {g : Graph} {t : Triple}
      (hA : art ∈ A) (hb : art.body = some g) (hdig : art.digest = gd) (hmem : t ∈ g) :
      Derives A Γ (Claim.rdfDerivable gd ad (t.scoped (.artifact art.id)))
  /-- A triple of the inline body of the axiom artifact filed under
  digest `ad` — RDFS `axiomatic`, read in that artifact's scope. -/
  | rdfsAxiom {gd ad : String} {art : Artifact} {ax : Graph} {t : Triple}
      (hA : art ∈ A) (hb : art.body = some ax) (hdig : art.digest = ad) (hmem : t ∈ ax) :
      Derives A Γ (Claim.rdfDerivable gd ad (t.scoped (.artifact art.id)))
  /-- One RDF 1.1 Semantics inference row, over SCOPED premises
  already derived about the same digests. `hd` is the landed RDFS
  relation: `t` follows from the premise triples alone, with no
  axioms, so the row composes by `DerivesFull.cut`. -/
  | rdfsRow {gd ad : String} {prem : List Triple} {t : Triple}
      (hp : ∀ u ∈ prem, Derives A Γ (Claim.rdfDerivable gd ad u))
      (hd : DerivesFull [] prem t) :
      Derives A Γ (Claim.rdfDerivable gd ad t)

/-- Weakening: more assumptions never lose a derivation. -/
theorem Derives.weaken {A : List Artifact} {Γ Δ : List Assumption}
    (hsub : ∀ a ∈ Γ, a ∈ Δ) {c : Claim} (h : Derives A Γ c) : Derives A Δ c := by
  induction h with
  | assumption ha => exact Derives.assumption (hsub _ ha)
  | rdfsBase hA hb hdig hmem => exact Derives.rdfsBase hA hb hdig hmem
  | rdfsAxiom hA hb hdig hmem => exact Derives.rdfsAxiom hA hb hdig hmem
  | rdfsRow _ hd ih => exact Derives.rdfsRow ih hd

/-- Monotone in the axiom set. Every constructor but `axiomatic` is
insensitive to it, and `axiomatic` needs only the inclusion. -/
theorem derivesFull_axMono {ax ax' g : Graph} (hsub : ∀ u ∈ ax, u ∈ ax')
    {t : Triple} (h : DerivesFull ax g t) : DerivesFull ax' g t := by
  induction h with
  | base hm => exact DerivesFull.base hm
  | axiomatic hm => exact DerivesFull.axiomatic (hsub _ hm)
  | rdfD2 _ ih => exact DerivesFull.rdfD2 ih
  | rdfs2 _ _ ih1 ih2 => exact DerivesFull.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact DerivesFull.rdfs3 ih1 ih2 hs
  | rdfs4a _ ih => exact DerivesFull.rdfs4a ih
  | rdfs4b _ hs ih => exact DerivesFull.rdfs4b ih hs
  | rdfs5 _ hs _ ih1 ih2 => exact DerivesFull.rdfs5 ih1 hs ih2
  | rdfs6 _ ih => exact DerivesFull.rdfs6 ih
  | rdfs7 _ _ ih1 ih2 => exact DerivesFull.rdfs7 ih1 ih2
  | rdfs8 _ ih => exact DerivesFull.rdfs8 ih
  | rdfs9 _ hs _ ih1 ih2 => exact DerivesFull.rdfs9 ih1 hs ih2
  | rdfs10 _ ih => exact DerivesFull.rdfs10 ih
  | rdfs11 _ hs _ ih1 ih2 => exact DerivesFull.rdfs11 ih1 hs ih2
  | rdfs12 _ ih => exact DerivesFull.rdfs12 ih
  | rdfs13 _ ih => exact DerivesFull.rdfs13 ih

/-- **A scoped FPP0 chain is an RDF 1.1 Semantics derivation from the
MERGE of the cited artifacts.** For a claim about digests `gd` and
`ad`, the scoped triple is `DerivesFull`-derivable with the merge of
the artifacts filed under `ad` as the axiom set and the merge of the
artifacts filed under `gd` as the graph — each body renamed apart by
its artifact id.

No digest-collision hypothesis: a leaf names the artifact it was read
from, so nothing depends on recovering a graph from its digest. The
one hypothesis, `hΓ`, is about the FRONTIER only: each assumption,
read in its own scope, is itself derivable from those merges. It is
vacuous when the frontier is empty (`checkBundle_merge`). -/
theorem Derives.toMerge {A : List Artifact} {Γ : List Assumption}
    (hΓ : ∀ a ∈ Γ, ∀ (gd ad : String) (u : Triple),
        a.subject = Claim.rdfDerivable gd ad u →
        DerivesFull (mergeOf A ad) (mergeOf A gd) (u.scoped (.frontier a.id))) :
    ∀ {c : Claim}, Derives A Γ c → ∀ (gd ad : String) (t : Triple),
      c = Claim.rdfDerivable gd ad t →
      DerivesFull (mergeOf A ad) (mergeOf A gd) t := by
  intro c h
  induction h with
  | @assumption a ha =>
      intro gd ad t heq
      cases hs : a.subject with
      | clif p => rw [hs] at heq; simp [Claim.scoped] at heq
      | rdfDerivable gd' ad' u =>
          rw [hs] at heq
          simp only [Claim.scoped, Claim.rdfDerivable.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact hΓ a ha _ _ u hs
  | @rdfsBase gd ad art g t' hA hb hdig hmem =>
      intro gd0 ad0 t heq
      simp only [Claim.rdfDerivable.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      subst hdig
      exact DerivesFull.base (mem_mergeOf hA hb hmem)
  | @rdfsAxiom gd ad art ax t' hA hb hdig hmem =>
      intro gd0 ad0 t heq
      simp only [Claim.rdfDerivable.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      subst hdig
      exact DerivesFull.axiomatic (mem_mergeOf hA hb hmem)
  | @rdfsRow gd ad prem t' _ hd ih =>
      intro gd0 ad0 t heq
      simp only [Claim.rdfDerivable.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine DerivesFull.cut (fun u hu => ih u hu _ _ u rfl) ?_
      exact derivesFull_axMono (by intro u hu; cases hu) hd

/-! ## Level counts and the check result -/

/-- The mix of evidence levels a result reports. Four numbers, never
one tick (adoption doc section 1). -/
structure LevelCounts where
  foundational : Nat
  verifiedReplay : Nat
  replay : Nat
  attestation : Nat
  deriving DecidableEq, Repr, Inhabited

def LevelCounts.zero : LevelCounts := ⟨0, 0, 0, 0⟩

def LevelCounts.bump (c : LevelCounts) : EvidenceLevel → LevelCounts
  | .foundational => { c with foundational := c.foundational + 1 }
  | .verifiedReplay => { c with verifiedReplay := c.verifiedReplay + 1 }
  | .replay => { c with replay := c.replay + 1 }
  | .attestation => { c with attestation := c.attestation + 1 }

/-- What a caller gets back.

`valid` alone is NOT a verdict that something was proved — adoption
doc section 8a. The fields a reader must combine with it:

* `assumptions` — the frontier, always reported.
* `counts` — the level mix over the steps the conclusion actually
  depends on.
* `foundationalOnly` — true only when the frontier is empty.
* `conclusionIsAssumption` — the degenerate shape, named. -/
structure CheckResult where
  valid : Bool
  conclusion : Claim
  /-- The assumption frontier. Every declared assumption, and every
  non-foundational step promoted to one. -/
  assumptions : Array Assumption
  /-- Level counts over the SUPPORT of the conclusion. -/
  counts : LevelCounts
  /-- The frontier is empty and the bundle is valid. -/
  foundationalOnly : Bool
  /-- The conclusion is itself a declared assumption. -/
  conclusionIsAssumption : Bool
  /-- Why the bundle was refused, when it was: the first failed check,
  in words. DIAGNOSTIC ONLY — `valid` is the verdict, and no theorem
  reads this field. `none` exactly when `valid` is true. -/
  rejection : Option String := none
  deriving DecidableEq, Repr

end L4Factoidal.FPP0
