/-
L4Factoidal.OWL.DirectCert — refutation certificates for the OWL DL
refuter, and the theorem that an accepted certificate means "no model"
under the OWL 2 Direct Semantics.

Design record: `docs/designissues/2026-10-10-owl-dl-refutation-certificates.md`.
Issue: https://github.com/danbri/factoidal/issues/651 (plan item 2).

`OWL/Refute.lean` is a `partial def` search over hash-indexed state with
caps. This module does not reason about it. The search emits a
certificate (`OWL/RefuteCert.lean`); `checkCert` below is a total
function that accepts or rejects it; `checkCert_sound` proves that an
accepted certificate leaves the ontology with no model.

## The ontology and its models

`DlOntology` is a TBox of `SubClassOf` axioms over `Concept`, a role box
and an ABox (OWL 2 Direct Semantics,
https://www.w3.org/TR/owl2-direct-semantics/ : Table 4 interprets the
class expressions, Table 5 `SubClassOf`, Table 6
`SubObjectPropertyOf` and `TransitiveObjectProperty`, Table 10 the
assertions). `DirectModel I ν O` is satisfaction of all three. The
assignment `ν` covers every individual name, anonymous ones included,
which is the "some interpretation of the anonymous individuals" of
Direct Semantics § 2.4.

## The checker

A certificate records the CHOICES of a closed tableau: which union to
split, which existential witness to introduce, which pairs of
successors to identify under a `≤ n` bound. Everything deterministic the
checker computes itself, by `saturate`: a bounded number of rounds of
the forward rules (`stepGen`), each proved sound by its own lemma. A
leaf (`Cert.close`) asks the saturated facts for a clash (`clashIn`).

Every fact list the checker handles satisfies one invariant: in every
interpretation that respects the TBox and the role box, an assignment
that satisfies the list's seed satisfies every fact in it. The soundness
proof is that invariant, carried through the rounds and then through
the certificate by structural induction.

No `sorry`, no `axiom`, no `partial`, no `native_decide`.
-/
import L4Factoidal.OWL.TableauTheorems
import Std.Data.HashSet

namespace L4Factoidal.OWL

deriving instance Hashable for Concept
deriving instance Hashable for Assertion

/-! ## The ontology -/

/-- An ontology in the fragment the checker reads. -/
structure DlOntology where
  /-- `SubClassOf(C D)` axioms, as pairs `(C, D)` (Table 5). -/
  tbox : List (Concept × Concept) := []
  /-- `SubObjectPropertyOf` and `TransitiveObjectProperty` (Table 6). -/
  rbox : RoleAxioms := RoleAxioms.empty
  /-- `ClassAssertion`, `ObjectPropertyAssertion`, `DifferentIndividuals`
      (Table 10). -/
  abox : List Assertion := []
  /-- `InverseObjectProperties(r s)` (Table 6), as pairs `(r, s)`;
      `SymmetricObjectProperty(r)` is the pair `(r, r)`. -/
  inv : List (Role × Role) := []
deriving Repr

/-- Every `SubClassOf(C D)` of the TBox holds: `(C)^C ⊆ (D)^C`. -/
def RespectsTBox {δ : Type} (I : Interp δ) (T : List (Concept × Concept)) : Prop :=
  ∀ ax ∈ T, ∀ x, I.sem ax.1 x → I.sem ax.2 x

/-- Every `InverseObjectProperties(r s)` holds:
    `(r)^OP = {(x, y) | (y, x) ∈ (s)^OP}`. -/
def RespectsInv {δ : Type} (I : Interp δ) (P : List (Role × Role)) : Prop :=
  ∀ q ∈ P, ∀ x y, I.role q.1 x y ↔ I.role q.2 y x

/-- `(I, ν)` satisfies the ontology (Direct Semantics § 2.3.7, with
    § 2.4's anonymous individuals folded into `ν`). -/
def DirectModel {δ : Type} (I : Interp δ) (ν : Ind → δ) (O : DlOntology) : Prop :=
  RespectsRBox I O.rbox ∧ RespectsTBox I O.tbox ∧ RespectsInv I O.inv ∧ SatAll I ν O.abox

/-! ## Negation normal form

`nnfP true c` denotes what `c` denotes; `nnfP false c` denotes the
complement. Each clause is a Table 4 identity: De Morgan for the
Boolean connectives, `¬∀r.C = ∃r.¬C`, `¬(≥ 0 r) = ⊥`,
`¬(≥ n+1 r) = ≤ n r`, `¬(≤ n r) = ≥ n+1 r`, and the same for the
qualified forms. -/

def Concept.nnfP : Bool → Concept → Concept
  | true,  .atom a => .atom a
  | false, .atom a => .neg (.atom a)
  | true,  .top => .top
  | false, .top => .bot
  | true,  .bot => .bot
  | false, .bot => .top
  | p,     .neg c => Concept.nnfP (!p) c
  | true,  .conj c d => .conj (Concept.nnfP true c) (Concept.nnfP true d)
  | false, .conj c d => .disj (Concept.nnfP false c) (Concept.nnfP false d)
  | true,  .disj c d => .disj (Concept.nnfP true c) (Concept.nnfP true d)
  | false, .disj c d => .conj (Concept.nnfP false c) (Concept.nnfP false d)
  | true,  .all r c => .all r (Concept.nnfP true c)
  | false, .all r c => .ex r (Concept.nnfP false c)
  | true,  .ex r c => .ex r (Concept.nnfP true c)
  | false, .ex r c => .all r (Concept.nnfP false c)
  | true,  .atLeast n r => .atLeast n r
  | false, .atLeast 0 _ => .bot
  | false, .atLeast (n + 1) r => .atMost n r
  | true,  .atMost n r => .atMost n r
  | false, .atMost n r => .atLeast (n + 1) r
  | true,  .atLeastQ n r c => .atLeastQ n r (Concept.nnfP true c)
  | false, .atLeastQ 0 _ _ => .bot
  | false, .atLeastQ (n + 1) r c => .atMostQ n r (Concept.nnfP true c)
  | true,  .atMostQ n r c => .atMostQ n r (Concept.nnfP true c)
  | false, .atMostQ n r c => .atLeastQ (n + 1) r (Concept.nnfP true c)

/-- The negation normal form of `c`. -/
def Concept.nnf (c : Concept) : Concept := Concept.nnfP true c

/-- The negation normal form of `¬c`. -/
def Concept.nnfNeg (c : Concept) : Concept := Concept.nnfP false c

/-- The empty list is a witness of `≥ 0`. -/
theorem nil_witness {δ : Type} (P : δ → Prop) :
    ∃ l : List δ, l.length = 0 ∧ l.Pairwise (· ≠ ·) ∧ ∀ y ∈ l, P y :=
  ⟨[], rfl, List.Pairwise.nil, fun _ h => by cases h⟩

/-- THE NNF LAW: `nnfP true c` denotes `c`, `nnfP false c` denotes the
    complement of `c` (Direct Semantics Table 4). -/
theorem sem_nnfP {δ : Type} (I : Interp δ) (c : Concept) :
    (∀ x, I.sem (Concept.nnfP true c) x ↔ I.sem c x) ∧
    (∀ x, I.sem (Concept.nnfP false c) x ↔ ¬ I.sem c x) := by
  induction c with
  | atom a => exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | top =>
      refine ⟨fun _ => Iff.rfl, fun _ => ?_⟩
      simp [Concept.nnfP, Interp.sem]
  | bot =>
      refine ⟨fun _ => Iff.rfl, fun _ => ?_⟩
      simp [Concept.nnfP, Interp.sem]
  | neg c ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show I.sem (Concept.nnfP false c) x ↔ ¬ I.sem c x
        exact ih.2 x
      · show I.sem (Concept.nnfP true c) x ↔ ¬ ¬ I.sem c x
        rw [ih.1 x]
        exact Classical.not_not.symm
  | conj c d ihc ihd =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (I.sem (Concept.nnfP true c) x ∧ I.sem (Concept.nnfP true d) x) ↔ _
        rw [ihc.1 x, ihd.1 x]; rfl
      · show (I.sem (Concept.nnfP false c) x ∨ I.sem (Concept.nnfP false d) x) ↔ _
        rw [ihc.2 x, ihd.2 x]
        exact Classical.not_and_iff_not_or_not.symm
  | disj c d ihc ihd =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (I.sem (Concept.nnfP true c) x ∨ I.sem (Concept.nnfP true d) x) ↔ _
        rw [ihc.1 x, ihd.1 x]; rfl
      · show (I.sem (Concept.nnfP false c) x ∧ I.sem (Concept.nnfP false d) x) ↔ _
        rw [ihc.2 x, ihd.2 x]
        exact not_or.symm
  | all r c ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (∀ y, I.role r x y → I.sem (Concept.nnfP true c) y) ↔ _
        simp only [ih.1]; rfl
      · show (∃ y, I.role r x y ∧ I.sem (Concept.nnfP false c) y) ↔
            ¬ ∀ y, I.role r x y → I.sem c y
        simp only [ih.2]
        constructor
        · intro ⟨y, hr, hn⟩ h; exact hn (h y hr)
        · intro h
          exact Classical.byContradiction (fun hne =>
            h (fun y hr => Classical.byContradiction (fun hc => hne ⟨y, hr, hc⟩)))
  | ex r c ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (∃ y, I.role r x y ∧ I.sem (Concept.nnfP true c) y) ↔ _
        simp only [ih.1]; rfl
      · show (∀ y, I.role r x y → I.sem (Concept.nnfP false c) y) ↔
            ¬ ∃ y, I.role r x y ∧ I.sem c y
        simp only [ih.2]
        constructor
        · intro h ⟨y, hr, hc⟩; exact h y hr hc
        · intro h y hr hc; exact h ⟨y, hr, hc⟩
  | atLeast n r =>
      refine ⟨fun _ => Iff.rfl, fun x => ?_⟩
      cases n with
      | zero =>
          show False ↔ ¬ ∃ l, I.succWitness r x 0 l
          refine ⟨False.elim, fun h => h ?_⟩
          have ⟨l, h1, h2, h3⟩ := nil_witness (fun y => I.role r x y)
          exact ⟨l, h1, h2, h3⟩
      | succ n => exact Iff.rfl
  | atMost n r =>
      refine ⟨fun _ => Iff.rfl, fun x => ?_⟩
      show (∃ l, I.succWitness r x (n + 1) l) ↔ ¬ ¬ ∃ l, I.succWitness r x (n + 1) l
      exact Classical.not_not.symm
  | atLeastQ n r c ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (∃ l : List δ, l.length = n ∧ l.Pairwise (· ≠ ·) ∧
              ∀ y ∈ l, I.role r x y ∧ I.sem (Concept.nnfP true c) y) ↔ _
        simp only [ih.1]; rfl
      · cases n with
        | zero =>
            show False ↔ ¬ ∃ l : List δ, l.length = 0 ∧ l.Pairwise (· ≠ ·) ∧
              ∀ y ∈ l, I.role r x y ∧ I.sem c y
            exact ⟨False.elim, fun h => h (nil_witness _)⟩
        | succ n =>
            show (¬ ∃ l : List δ, l.length = n + 1 ∧ l.Pairwise (· ≠ ·) ∧
              ∀ y ∈ l, I.role r x y ∧ I.sem (Concept.nnfP true c) y) ↔ _
            simp only [ih.1]; rfl
  | atMostQ n r c ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · show (¬ ∃ l : List δ, l.length = n + 1 ∧ l.Pairwise (· ≠ ·) ∧
              ∀ y ∈ l, I.role r x y ∧ I.sem (Concept.nnfP true c) y) ↔ _
        simp only [ih.1]; rfl
      · show (∃ l : List δ, l.length = n + 1 ∧ l.Pairwise (· ≠ ·) ∧
              ∀ y ∈ l, I.role r x y ∧ I.sem (Concept.nnfP true c) y) ↔ _
        simp only [ih.1]
        exact Classical.not_not.symm

theorem sem_nnf {δ : Type} (I : Interp δ) (c : Concept) (x : δ) :
    I.sem (Concept.nnf c) x ↔ I.sem c x := (sem_nnfP I c).1 x

theorem sem_nnfNeg {δ : Type} (I : Interp δ) (c : Concept) (x : δ) :
    I.sem (Concept.nnfNeg c) x ↔ ¬ I.sem c x := (sem_nnfP I c).2 x

/-! ## Normalising the ontology

The checker reads the TBox in negation normal form, with every axiom's
contrapositive beside it: `C ⊑ D` gives `nnf C ⊑ nnf D` and
`nnf ¬D ⊑ nnf ¬C`. Both hold in every model of `C ⊑ D` by the nnf law.
The refuter adds the same contrapositives for `owl:equivalentClass`
and the Boolean class axioms (`Refute.collectAxiomsS`). -/

def normTBox (T : List (Concept × Concept)) : List (Concept × Concept) :=
  T.flatMap (fun ax =>
    [(Concept.nnf ax.1, Concept.nnf ax.2), (Concept.nnfNeg ax.2, Concept.nnfNeg ax.1)])

theorem respects_normTBox {δ : Type} {I : Interp δ} {T : List (Concept × Concept)}
    (h : RespectsTBox I T) : RespectsTBox I (normTBox T) := by
  intro ax hax x hx
  have ⟨ax0, hax0, hin⟩ := List.mem_flatMap.mp hax
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hin
  cases hin with
  | inl he =>
      subst he
      exact (sem_nnf I _ x).2 (h ax0 hax0 x ((sem_nnf I _ x).1 hx))
  | inr he =>
      subst he
      exact (sem_nnfNeg I _ x).2 (fun h1 => (sem_nnfNeg I _ x).1 hx (h ax0 hax0 x h1))

def normAssertion : Assertion → Assertion
  | .inst a c => .inst a (Concept.nnf c)
  | φ         => φ

theorem satisfies_normAssertion {δ : Type} {I : Interp δ} {ν : Ind → δ}
    (φ : Assertion) (h : Satisfies I ν φ) : Satisfies I ν (normAssertion φ) := by
  cases φ with
  | inst a c => exact (sem_nnf I c (ν a)).2 h
  | rel r a b => exact h
  | diff a b => exact h

/-! ## The forward rules

Each generator maps one fact `φ` of the current list `F` to the facts
it yields. `gen_sound` below proves, rule by rule, that a model of `F`
satisfies each yielded fact. -/

/-- What the checker reads besides the facts: the normalised TBox, the
    role box, and the left-hand sides of the TBox that an asserted edge
    can prove (`exGen`). -/
structure Ctx where
  T : List (Concept × Concept)
  R : RoleAxioms
  L : List Concept
  inv : List (Role × Role) := []
  /-- The conjunctions and disjunctions `introGen` may build. -/
  B : List Concept := []

/-- `conjE`: `a : C ⊓ D` gives `a : C` and `a : D`. -/
def conjGen : Assertion → List Assertion
  | .inst a (.conj c d) => [.inst a c, .inst a d]
  | _ => []

/-- The `r`-successors of `a` in `F`, each mapped to the fact `b : k`. -/
def succFacts (F : List Assertion) (r : Role) (a : Ind) (k : Concept) : List Assertion :=
  F.filterMap (fun ψ => match ψ with
    | .rel s a' b => if s = r ∧ a' = a then some (.inst b k) else none
    | _ => none)

/-- `allE`, and `allTransE` when `r` is transitive. -/
def allGen (R : RoleAxioms) (F : List Assertion) : Assertion → List Assertion
  | .inst a (.all r c) =>
      succFacts F r a c ++ (if r ∈ R.trans then succFacts F r a (.all r c) else [])
  | _ => []

/-- `subRoleE`: `r(a, b)` and `r ⊑ s` give `s(a, b)`. -/
def subRoleGen (R : RoleAxioms) : Assertion → List Assertion
  | .rel r a b => R.subRole.filterMap (fun p => if p.1 = r then some (.rel p.2 a b) else none)
  | _ => []

/-- `transE`: `r(a, b)`, `r(b, e)`, `r` transitive give `r(a, e)`. -/
def transGen (R : RoleAxioms) (F : List Assertion) : Assertion → List Assertion
  | .rel r a b =>
      if r ∈ R.trans then
        F.filterMap (fun ψ => match ψ with
          | .rel s b' e => if s = r ∧ b' = b then some (.rel r a e) else none
          | _ => none)
      else []
  | _ => []

/-- `tboxE`: `a : C` and `C ⊑ D` in the TBox give `a : D`. -/
def tboxGen (T : List (Concept × Concept)) : Assertion → List Assertion
  | .inst a c => T.filterMap (fun ax => if ax.1 = c then some (.inst a ax.2) else none)
  | _ => []

/-- `topI`: every named individual is in `owl:Thing`. -/
def topGen (φ : Assertion) : List Assertion :=
  φ.inds.map (fun i => .inst i .top)

/-- `exI`: an edge `r(a, b)` proves `a : ∃r.C` when `b : C` is known,
    and `a : ≥ 1 r` outright. Only the left-hand sides in `L` are
    generated, so the rule adds finitely many facts. -/
def exGen (L : List Concept) (F : List Assertion) : Assertion → List Assertion
  | .rel r a b => L.filterMap (fun e => match e with
      | .ex s c => if s = r ∧ Assertion.inst b c ∈ F then some (.inst a e) else none
      | .atLeast 1 s => if s = r then some (.inst a e) else none
      | .atLeastQ 1 s c => if s = r ∧ Assertion.inst b c ∈ F then some (.inst a e) else none
      | _ => none)
  | _ => []

/-- `invE`: `r(a, b)` and `InverseObjectProperties(r s)` give `s(b, a)`,
    in either position of the pair. -/
def invGen (P : List (Role × Role)) : Assertion → List Assertion
  | .rel r a b => P.flatMap (fun q =>
      (if q.1 = r then [Assertion.rel q.2 b a] else []) ++
      (if q.2 = r then [Assertion.rel q.1 b a] else []))
  | _ => []

/-- `conjI` and `disjI`: `a : C` and `a : D` give `a : C ⊓ D`; `a : C`
    gives `a : C ⊔ D` and `a : D ⊔ C`. Only the conjunctions and
    disjunctions in `B` are built (the Boolean subterms of the TBox
    left-hand sides), so the rule adds finitely many facts. -/
def introGen (B : List Concept) (F : List Assertion) : Assertion → List Assertion
  | .inst a c => B.filterMap (fun e => match e with
      | .conj c' d => if c' = c ∧ Assertion.inst a d ∈ F then some (.inst a e) else none
      | .disj c' d => if c' = c ∨ d = c then some (.inst a e) else none
      | _ => none)
  | _ => []

/-- All forward rules on one fact. -/
def stepGen (C : Ctx) (F : List Assertion) (φ : Assertion) : List Assertion :=
  conjGen φ ++ allGen C.R F φ ++ subRoleGen C.R φ ++ transGen C.R F φ ++
  tboxGen C.T φ ++ topGen φ ++ exGen C.L F φ ++ invGen C.inv φ ++ introGen C.B F φ

/-- The facts of `news` not already in `F` (nor earlier in `news`),
    appended to `F`. The hash set only decides what is kept; soundness
    needs only `mem_addNew`. -/
def addNew (F news : List Assertion) : List Assertion :=
  let st := news.foldl (fun (st : Std.HashSet Assertion × Array Assertion) ψ =>
      if st.1.contains ψ then st else (st.1.insert ψ, st.2.push ψ))
    (Std.HashSet.ofList F, #[])
  F ++ st.2.toList

/-- One round: every rule applied to every fact of `F`. -/
def satRound (C : Ctx) (F : List Assertion) : List Assertion :=
  addNew F (F.flatMap (stepGen C F))

/-- Rounds until nothing new appears, at most `fuel` of them. -/
def saturate (C : Ctx) : Nat → List Assertion → List Assertion
  | 0, F => F
  | n + 1, F =>
      let F' := satRound C F
      if F'.length = F.length then F else saturate C n F'

/-! ### Soundness of the forward rules -/

/-- What every rule soundness lemma assumes: the interpretation respects
    the context's TBox and role box. -/
structure CtxValid {δ : Type} (I : Interp δ) (C : Ctx) : Prop where
  tbox : RespectsTBox I C.T
  rbox : RespectsRBox I C.R
  inv  : RespectsInv I C.inv

theorem mem_succFacts {F : List Assertion} {r : Role} {a : Ind} {k : Concept}
    {ψ : Assertion} (h : ψ ∈ succFacts F r a k) :
    ∃ b, Assertion.rel r a b ∈ F ∧ ψ = .inst b k := by
  have ⟨χ, hχ, he⟩ := List.mem_filterMap.mp h
  cases χ with
  | rel s a' b =>
      simp only at he
      split at he
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨b, hχ, (Option.some.inj he).symm⟩
      · cases he
  | inst _ _ => simp at he
  | diff _ _ => simp at he

theorem gen_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {C : Ctx}
    (hC : CtxValid I C) {F : List Assertion} (hF : SatAll I ν F)
    {φ : Assertion} (hφ : φ ∈ F) {ψ : Assertion} (hψ : ψ ∈ stepGen C F φ) :
    Satisfies I ν ψ := by
  simp only [stepGen, List.mem_append] at hψ
  rcases hψ with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · -- conjE
    cases φ with
    | inst a c =>
        cases c with
        | conj c d =>
            have hs : I.sem c (ν a) ∧ I.sem d (ν a) := hF _ hφ
            simp only [conjGen, List.mem_cons, List.mem_nil_iff, or_false] at h
            rcases h with rfl | rfl
            · exact hs.1
            · exact hs.2
        | _ => simp [conjGen] at h
    | rel _ _ _ => simp [conjGen] at h
    | diff _ _ => simp [conjGen] at h
  · -- allE / allTransE
    cases φ with
    | inst a c =>
        cases c with
        | all r c =>
            have hs : ∀ y, I.role r (ν a) y → I.sem c y := hF _ hφ
            simp only [allGen, List.mem_append] at h
            rcases h with h | h
            · have ⟨b, hb, he⟩ := mem_succFacts h
              subst he
              exact hs _ (hF _ hb)
            · split at h
              · rename_i htr
                have ⟨b, hb, he⟩ := mem_succFacts h
                subst he
                intro z hz
                exact hs _ (hC.rbox.2 r htr _ _ _ (hF _ hb) hz)
              · cases h
        | _ => simp [allGen] at h
    | rel _ _ _ => simp [allGen] at h
    | diff _ _ => simp [allGen] at h
  · -- subRoleE
    cases φ with
    | rel r a b =>
        have hs : I.role r (ν a) (ν b) := hF _ hφ
        simp only [subRoleGen] at h
        have ⟨p, hp, he⟩ := List.mem_filterMap.mp h
        split at he
        · rename_i hpr
          cases he
          exact hC.rbox.1 p hp _ _ (hpr ▸ hs)
        · cases he
    | inst _ _ => simp [subRoleGen] at h
    | diff _ _ => simp [subRoleGen] at h
  · -- transE
    cases φ with
    | rel r a b =>
        have hs : I.role r (ν a) (ν b) := hF _ hφ
        simp only [transGen] at h
        split at h
        · rename_i htr
          have ⟨χ, hχ, he⟩ := List.mem_filterMap.mp h
          cases χ with
          | rel s b' e =>
              simp only at he
              split at he
              · rename_i hc
                obtain ⟨rfl, rfl⟩ := hc
                cases he
                exact hC.rbox.2 s htr _ _ _ hs (hF _ hχ)
              · cases he
          | inst _ _ => simp at he
          | diff _ _ => simp at he
        · cases h
    | inst _ _ => simp [transGen] at h
    | diff _ _ => simp [transGen] at h
  · -- tboxE
    cases φ with
    | inst a c =>
        have hs : I.sem c (ν a) := hF _ hφ
        simp only [tboxGen] at h
        have ⟨ax, hax, he⟩ := List.mem_filterMap.mp h
        split at he
        · rename_i hc
          cases he
          exact hC.tbox ax hax _ (hc ▸ hs)
        · cases he
    | rel _ _ _ => simp [tboxGen] at h
    | diff _ _ => simp [tboxGen] at h
  · -- topI
    have ⟨i, _, he⟩ := List.mem_map.mp h
    subst he
    trivial
  · -- exI
    cases φ with
    | rel r a b =>
        have hs : I.role r (ν a) (ν b) := hF _ hφ
        simp only [exGen] at h
        have ⟨e, _, he⟩ := List.mem_filterMap.mp h
        cases e with
        | ex s c =>
            simp only at he
            split at he
            · rename_i hc
              obtain ⟨rfl, hb⟩ := hc
              cases he
              exact ⟨ν b, hs, hF _ hb⟩
            · cases he
        | atLeast n s =>
            cases n with
            | zero => simp at he
            | succ n =>
                cases n with
                | zero =>
                    simp only at he
                    split at he
                    · rename_i hc
                      subst hc
                      cases he
                      refine ⟨[ν b], rfl, List.pairwise_singleton _ _, ?_⟩
                      intro y hy
                      rw [List.mem_singleton] at hy
                      subst hy
                      exact hs
                    · cases he
                | succ _ => simp at he
        | atLeastQ n s c =>
            cases n with
            | zero => simp at he
            | succ n =>
                cases n with
                | zero =>
                    simp only at he
                    split at he
                    · rename_i hc
                      obtain ⟨rfl, hb⟩ := hc
                      cases he
                      refine ⟨[ν b], rfl, List.pairwise_singleton _ _, ?_⟩
                      intro y hy
                      rw [List.mem_singleton] at hy
                      subst hy
                      exact ⟨hs, hF _ hb⟩
                    · cases he
                | succ _ => simp at he
        | atom _ => simp at he
        | top => simp at he
        | bot => simp at he
        | neg _ => simp at he
        | conj _ _ => simp at he
        | disj _ _ => simp at he
        | all _ _ => simp at he
        | atMost _ _ => simp at he
        | atMostQ _ _ _ => simp at he
    | inst _ _ => simp [exGen] at h
    | diff _ _ => simp [exGen] at h
  · -- invE
    cases φ with
    | rel r a b =>
        have hs : I.role r (ν a) (ν b) := hF _ hφ
        simp only [invGen] at h
        have ⟨q, hq, hin⟩ := List.mem_flatMap.mp h
        simp only [List.mem_append] at hin
        rcases hin with hin | hin
        · split at hin
          · rename_i hr
            simp only [List.mem_singleton] at hin
            subst hin
            exact (hC.inv q hq (ν a) (ν b)).mp (hr ▸ hs)
          · cases hin
        · split at hin
          · rename_i hr
            simp only [List.mem_singleton] at hin
            subst hin
            exact (hC.inv q hq (ν b) (ν a)).mpr (hr ▸ hs)
          · cases hin
    | inst _ _ => simp [invGen] at h
    | diff _ _ => simp [invGen] at h
  · -- conjI / disjI
    cases φ with
    | inst a c =>
        have hs : I.sem c (ν a) := hF _ hφ
        simp only [introGen] at h
        have ⟨e, _, he⟩ := List.mem_filterMap.mp h
        cases e with
        | conj c' d =>
            simp only at he
            split at he
            · rename_i hc
              obtain ⟨rfl, hd⟩ := hc
              cases he
              exact ⟨hs, hF _ hd⟩
            · cases he
        | disj c' d =>
            simp only at he
            split at he
            · rename_i hc
              cases he
              rcases hc with rfl | rfl
              · exact Or.inl hs
              · exact Or.inr hs
            · cases he
        | atom _ => simp at he
        | top => simp at he
        | bot => simp at he
        | neg _ => simp at he
        | all _ _ => simp at he
        | ex _ _ => simp at he
        | atLeast _ _ => simp at he
        | atMost _ _ => simp at he
        | atLeastQ _ _ _ => simp at he
        | atMostQ _ _ _ => simp at he
    | rel _ _ _ => simp [introGen] at h
    | diff _ _ => simp [introGen] at h

/-- Every element `addNew` returns is from `F` or from `news`. -/
theorem mem_addNew {F news : List Assertion} {ψ : Assertion}
    (h : ψ ∈ addNew F news) : ψ ∈ F ∨ ψ ∈ news := by
  simp only [addNew, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    -- Invariant of the fold: every pushed element comes from the list.
    have key : ∀ (l : List Assertion) (st : Std.HashSet Assertion × Array Assertion),
        (∀ x ∈ st.2.toList, x ∈ news) → (∀ x ∈ l, x ∈ news) →
        ∀ x ∈ (l.foldl (fun (st : Std.HashSet Assertion × Array Assertion) ψ =>
            if st.1.contains ψ then st else (st.1.insert ψ, st.2.push ψ)) st).2.toList,
          x ∈ news := by
      intro l
      induction l with
      | nil => intro st hst _ x hx; exact hst x hx
      | cons y ys ih =>
          intro st hst hl
          simp only [List.foldl_cons]
          apply ih
          · intro x hx
            split at hx
            · exact hst x hx
            · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx
              · exact hst x hx
              · subst hx; exact hl _ (List.Mem.head _)
          · intro x hx; exact hl x (List.Mem.tail _ hx)
    exact key news _ (by intro x hx; simp at hx) (fun x hx => hx) ψ h

theorem satRound_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {C : Ctx}
    (hC : CtxValid I C) {F : List Assertion} (hF : SatAll I ν F) :
    SatAll I ν (satRound C F) := by
  intro ψ hψ
  rcases mem_addNew hψ with h | h
  · exact hF ψ h
  · have ⟨φ, hφ, hg⟩ := List.mem_flatMap.mp h
    exact gen_sound hC hF hφ hg

theorem saturate_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {C : Ctx}
    (hC : CtxValid I C) : ∀ (n : Nat) {F : List Assertion}, SatAll I ν F →
    SatAll I ν (saturate C n F) := by
  intro n
  induction n with
  | zero => intro F hF; exact hF
  | succ n ih =>
      intro F hF
      simp only [saturate]
      split
      · exact hF
      · exact ih (satRound_sound hC hF)

/-! ## Clashes

`clashIn F` asks a saturated fact list for a contradiction:

* `a : ⊥`;
* `a : C` beside `a : ¬C`;
* `diff a a`;
* a lower bound against a smaller upper bound on the same role at one
  individual (`≥ n r`, `≥ n r.C` or `∃r.C`, which is `≥ 1 r.C`, against
  `≤ m r` or `≤ m r.C`, `m < n`, the qualified bound only with the same
  filler);
* an upper bound `≤ m r` (or `≤ m r.C`) at `a` with `m + 1` named
  `r`-successors (in `C`) that are pairwise `diff`. -/

/-- A lower bound a concept puts on `r`-successors, with its filler. -/
def minOf : Concept → Option (Nat × Role × Option Concept)
  | .atLeast n r    => some (n, r, none)
  | .atLeastQ n r c => some (n, r, some c)
  | .ex r c         => some (1, r, some c)
  | _               => none

/-- An upper bound a concept puts on `r`-successors, with its filler. -/
def maxOf : Concept → Option (Nat × Role × Option Concept)
  | .atMost m r    => some (m, r, none)
  | .atMostQ m r c => some (m, r, some c)
  | _              => none

/-- `y` is in the filler, when there is one. -/
def InFiller {δ : Type} (I : Interp δ) (oc : Option Concept) (y : δ) : Prop :=
  ∀ c, oc = some c → I.sem c y

theorem minOf_witness {δ : Type} (I : Interp δ) {k : Concept} {x : δ}
    {n : Nat} {r : Role} {oc : Option Concept}
    (hk : minOf k = some (n, r, oc)) (hs : I.sem k x) :
    ∃ l : List δ, l.length = n ∧ l.Pairwise (· ≠ ·) ∧
      ∀ y ∈ l, I.role r x y ∧ InFiller I oc y := by
  cases k with
  | atLeast n' r' =>
      simp only [minOf, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      have ⟨l, hlen, hpw, hall⟩ := hs
      exact ⟨l, hlen, hpw, fun y hy => ⟨hall y hy, fun c hc => by cases hc⟩⟩
  | atLeastQ n' r' c' =>
      simp only [minOf, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      have ⟨l, hlen, hpw, hall⟩ := hs
      exact ⟨l, hlen, hpw, fun y hy =>
        ⟨(hall y hy).1, fun c hc => by cases hc; exact (hall y hy).2⟩⟩
  | ex r' c' =>
      simp only [minOf, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      have ⟨y, hr, hc⟩ := hs
      refine ⟨[y], rfl, List.pairwise_singleton _ _, ?_⟩
      intro z hz
      rw [List.mem_singleton] at hz
      subst hz
      exact ⟨hr, fun c hc' => by cases hc'; exact hc⟩
  | atom _ => simp [minOf] at hk
  | top => simp [minOf] at hk
  | bot => simp [minOf] at hk
  | neg _ => simp [minOf] at hk
  | conj _ _ => simp [minOf] at hk
  | disj _ _ => simp [minOf] at hk
  | all _ _ => simp [minOf] at hk
  | atMost _ _ => simp [minOf] at hk
  | atMostQ _ _ _ => simp [minOf] at hk

theorem maxOf_forbids {δ : Type} (I : Interp δ) {k : Concept} {x : δ}
    {m : Nat} {r : Role} {oc : Option Concept}
    (hk : maxOf k = some (m, r, oc)) (hs : I.sem k x) :
    ¬ ∃ l : List δ, l.length = m + 1 ∧ l.Pairwise (· ≠ ·) ∧
      ∀ y ∈ l, I.role r x y ∧ InFiller I oc y := by
  cases k with
  | atMost m' r' =>
      simp only [maxOf, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      intro ⟨l, hlen, hpw, hall⟩
      exact hs ⟨l, hlen, hpw, fun y hy => (hall y hy).1⟩
  | atMostQ m' r' c' =>
      simp only [maxOf, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      intro ⟨l, hlen, hpw, hall⟩
      exact hs ⟨l, hlen, hpw, fun y hy => ⟨(hall y hy).1, (hall y hy).2 c' rfl⟩⟩
  | atom _ => simp [maxOf] at hk
  | top => simp [maxOf] at hk
  | bot => simp [maxOf] at hk
  | neg _ => simp [maxOf] at hk
  | conj _ _ => simp [maxOf] at hk
  | disj _ _ => simp [maxOf] at hk
  | all _ _ => simp [maxOf] at hk
  | ex _ _ => simp [maxOf] at hk
  | atLeast _ _ => simp [maxOf] at hk
  | atLeastQ _ _ _ => simp [maxOf] at hk

/-- The filler of an upper bound is implied by the filler of a lower
    bound: the bound is unqualified, or both name the same concept. -/
def fillerCovers (omax omin : Option Concept) : Bool :=
  match omax with
  | none   => true
  | some c => omin == some c

theorem fillerCovers_sound {δ : Type} {I : Interp δ} {omax omin : Option Concept}
    (h : fillerCovers omax omin = true) {y : δ} (hy : InFiller I omin y) :
    InFiller I omax y := by
  intro c hc
  subst hc
  simp only [fillerCovers, beq_iff_eq] at h
  exact hy c h

/-- A lower bound `k` and an upper bound `k'` that no element meets. -/
def boundsClash (k k' : Concept) : Bool :=
  match minOf k, maxOf k' with
  | some (n, r, omin), some (m, r', omax) => r == r' && decide (m < n) && fillerCovers omax omin
  | _, _ => false

theorem boundsClash_sound {δ : Type} (I : Interp δ) {k k' : Concept} {x : δ}
    (h : boundsClash k k' = true) (hk : I.sem k x) (hk' : I.sem k' x) : False := by
  unfold boundsClash at h
  split at h
  · rename_i n r omin m r' omax hmin hmax
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hmn⟩, hcov⟩ := h
    have ⟨l, hlen, hpw, hall⟩ := minOf_witness I hmin hk
    apply maxOf_forbids I hmax hk'
    refine ⟨l.take (m + 1), ?_, ?_, ?_⟩
    · rw [List.length_take, hlen]; omega
    · exact hpw.sublist (List.take_sublist _ _)
    · intro y hy
      have hy' := (List.take_sublist _ _).subset hy
      exact ⟨(hall y hy').1, fillerCovers_sound hcov (hall y hy').2⟩
  · cases h

/-- Pick `k` names from `cands`, pairwise accepted by `D`. -/
def pickDistinct (D : Ind → Ind → Bool) : Nat → List Ind → List Ind → Option (List Ind)
  | 0, chosen, _ => some chosen
  | _ + 1, _, [] => none
  | k + 1, chosen, b :: bs =>
      if chosen.all (D b) then
        match pickDistinct D k (b :: chosen) bs with
        | some l => some l
        | none   => pickDistinct D (k + 1) chosen bs
      else pickDistinct D (k + 1) chosen bs

/-- `a` and `b` are different by a `diff` fact, in either order. -/
def diffIn (F : List Assertion) (a b : Ind) : Bool :=
  F.contains (.diff a b) || F.contains (.diff b a)

/-- The named `r`-successors of `a` in `F` that are in the filler. -/
def boundedSuccs (F : List Assertion) (a : Ind) (r : Role) (oc : Option Concept) : List Ind :=
  (F.filterMap (fun ψ => match ψ with
    | .rel s a' b =>
        if s == r && a' == a && (match oc with
                                 | none => true
                                 | some c => F.contains (.inst b c)) then some b else none
    | _ => none)).eraseDups

/-- The check a picked list must pass. Soundness reads only this. -/
def goodSuccList (F : List Assertion) (a : Ind) (r : Role) (oc : Option Concept)
    (m : Nat) (l : List Ind) : Bool :=
  l.length == m + 1 &&
  l.all (fun b => F.contains (.rel r a b) &&
    (match oc with
     | none => true
     | some c => F.contains (.inst b c))) &&
  decide (l.Pairwise (fun x y => diffIn F x y = true))

/-- An upper bound at `a` refuted by named, pairwise different
    successors. -/
def maxClashAt (F : List Assertion) (a : Ind) (k : Concept) : Bool :=
  match maxOf k with
  | some (m, r, oc) =>
      match pickDistinct (diffIn F) (m + 1) [] ((boundedSuccs F a r oc).take 16) with
      | some l => goodSuccList F a r oc m l
      | none   => false
  | none => false

theorem maxClashAt_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {F : List Assertion}
    (hF : SatAll I ν F) {a : Ind} {k : Concept} (hk : Assertion.inst a k ∈ F)
    (h : maxClashAt F a k = true) : False := by
  unfold maxClashAt at h
  split at h
  · rename_i m r oc hmax
    split at h
    · rename_i l _
      simp only [goodSuccList, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨⟨hlen, hall⟩, hpw⟩ := h
      apply maxOf_forbids I hmax (hF _ hk)
      refine ⟨l.map ν, by simp [hlen], ?_, ?_⟩
      · refine pairwise_map_of ν ?_ hpw
        intro x y hxy
        simp only [diffIn, Bool.or_eq_true, List.contains_iff_mem] at hxy
        rcases hxy with hd | hd
        · exact hF _ hd
        · exact fun he => (hF _ hd) he.symm
      · intro y hy
        have ⟨b, hb, hby⟩ := List.mem_map.mp hy
        subst hby
        have ⟨hrel, hfill⟩ := hall b hb
        refine ⟨hF _ (List.contains_iff_mem.mp hrel), ?_⟩
        intro c hc
        subst hc
        simp only [List.contains_iff_mem] at hfill
        exact hF _ hfill
    · cases h
  · cases h

/-- One fact's clashes against the whole list. -/
def clashAt (F : List Assertion) : Assertion → Bool
  | .inst _ .bot => true
  | .inst a (.neg c) => F.contains (.inst a c)
  | .inst a k =>
      (minOf k).isSome && F.any (fun ψ => match ψ with
        | .inst a' k' => a' == a && boundsClash k k'
        | _ => false)
      || maxClashAt F a k
  | .diff a b => a == b
  | .rel _ _ _ => false

def clashIn (F : List Assertion) : Bool := F.any (clashAt F)

theorem clashIn_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {F : List Assertion}
    (hF : SatAll I ν F) (h : clashIn F = true) : False := by
  have ⟨φ, hφ, hc⟩ := List.any_eq_true.mp h
  have hs := hF _ hφ
  cases φ with
  | rel _ _ _ => simp [clashAt] at hc
  | diff a b =>
      simp only [clashAt, beq_iff_eq] at hc
      subst hc
      exact hs rfl
  | inst a k =>
      -- The bound and complement arms, then the generic arm.
      have generic : (((minOf k).isSome && F.any (fun ψ => match ψ with
            | .inst a' k' => a' == a && boundsClash k k'
            | _ => false)) || maxClashAt F a k) = true → False := by
        intro hg
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hg
        rcases hg with ⟨_, hany⟩ | hmx
        · have ⟨ψ, hψ, hcl⟩ := List.any_eq_true.mp hany
          cases ψ with
          | inst a' k' =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hcl
              obtain ⟨rfl, hb⟩ := hcl
              exact boundsClash_sound I hb hs (hF _ hψ)
          | rel _ _ _ => simp at hcl
          | diff _ _ => simp at hcl
        · exact maxClashAt_sound hF hφ hmx
      cases k with
      | bot => exact hs
      | neg c =>
          simp only [clashAt, List.contains_iff_mem] at hc
          exact hs (hF _ hc)
      | atom _ => simp only [clashAt] at hc; exact generic hc
      | top => simp only [clashAt] at hc; exact generic hc
      | conj _ _ => simp only [clashAt] at hc; exact generic hc
      | disj _ _ => simp only [clashAt] at hc; exact generic hc
      | all _ _ => simp only [clashAt] at hc; exact generic hc
      | ex _ _ => simp only [clashAt] at hc; exact generic hc
      | atLeast _ _ => simp only [clashAt] at hc; exact generic hc
      | atMost _ _ => simp only [clashAt] at hc; exact generic hc
      | atLeastQ _ _ _ => simp only [clashAt] at hc; exact generic hc
      | atMostQ _ _ _ => simp only [clashAt] at hc; exact generic hc

/-! ## Certificates -/

mutual

/-- A closed tableau's choices. -/
inductive Cert where
  /-- Saturate, then find a clash. -/
  | close
  /-- `a : C ⊔ D` is derivable; both extensions are refuted
      (`Refuted.disjSplit`). -/
  | split (a : Ind) (c d : Concept) (l r : Cert)
  /-- `a : ∃r.C` (or `≥ k r`, `≥ k r.C` with `k ≥ 1`) is derivable;
      the extension by a fresh `r`-successor `x` in `C` is refuted
      (`Refuted.exWitness`). -/
  | exWit (a : Ind) (r : Role) (c : Concept) (x : Ind) (k : Cert)
  /-- `a : ≤ n r` is derivable and `l` is `n + 1` distinct names of
      `r`-successors of `a`; for every unordered pair of `l` some case
      refutes the merge of the pair (`Refuted.leqMerge`, over unordered
      pairs). -/
  | merge (a : Ind) (n : Nat) (r : Role) (l : List Ind) (cases : MergeCases)

/-- The merge cases of `Cert.merge`: `(b, c, k)` refutes `mergeInds b c`. -/
inductive MergeCases where
  | nil
  | cons (b c : Ind) (k : Cert) (rest : MergeCases)

end

/-- The unordered pairs of a list, each once, earlier element first. -/
def pairsOf : List Ind → List (Ind × Ind)
  | []      => []
  | b :: bs => bs.map (fun c => (b, c)) ++ pairsOf bs

/-- Can `x` be a fresh witness for an `r`-successor in `c` at `a`? -/
def exAvailable (S : List Assertion) (a : Ind) (r : Role) (c : Concept) : Bool :=
  S.contains (.inst a (.ex r c)) ||
  S.any (fun ψ => match ψ with
    | .inst a' (.atLeastQ n r' c') =>
        a' == a && r' == r && (c' == c || c == .top) && decide (1 ≤ n)
    | .inst a' (.atLeast n r') => a' == a && r' == r && c == .top && decide (1 ≤ n)
    | .inst a' (.ex r' _) => a' == a && r' == r && c == .top
    | _ => false)

/-- The bound a `merge` uses: `a : ≤ n r`, or `a : ≤ n r.C` with every
    member of `l` known to be in `C`. -/
def boundAt (S : List Assertion) (a : Ind) (n : Nat) (r : Role) (l : List Ind) : Bool :=
  S.contains (.inst a (.atMost n r)) ||
  S.any (fun ψ => match ψ with
    | .inst a' (.atMostQ n' r' c) =>
        a' == a && n' == n && r' == r && l.all (fun b => S.contains (.inst b c))
    | _ => false)

theorem boundAt_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {S : List Assertion}
    (hS : SatAll I ν S) {a : Ind} {n : Nat} {r : Role} {l : List Ind}
    (h : boundAt S a n r l = true) (hrel : ∀ b ∈ l, Assertion.rel r a b ∈ S)
    (hpw : (l.map ν).Pairwise (· ≠ ·)) (hlen : l.length = n + 1) : False := by
  simp only [boundAt, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with hmax | hq
  · apply hS _ hmax
    refine ⟨l.map ν, by simp [hlen], hpw, ?_⟩
    intro y hy
    have ⟨b, hb, hfb⟩ := List.mem_map.mp hy
    subst hfb
    exact hS _ (hrel b hb)
  · have ⟨ψ, hψ, hm⟩ := List.any_eq_true.mp hq
    cases ψ with
    | inst a' k =>
        cases k with
        | atMostQ n' r' c =>
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
              List.contains_iff_mem] at hm
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hin⟩ := hm
            apply hS _ hψ
            refine ⟨l.map ν, by simp [hlen], hpw, ?_⟩
            intro y hy
            have ⟨b, hb, hfb⟩ := List.mem_map.mp hy
            subst hfb
            exact ⟨hS _ (hrel b hb), hS _ (hin b hb)⟩
        | atom _ => simp at hm
        | top => simp at hm
        | bot => simp at hm
        | neg _ => simp at hm
        | conj _ _ => simp at hm
        | disj _ _ => simp at hm
        | all _ _ => simp at hm
        | ex _ _ => simp at hm
        | atLeast _ _ => simp at hm
        | atMost _ _ => simp at hm
        | atLeastQ _ _ _ => simp at hm
    | rel _ _ _ => simp at hm
    | diff _ _ => simp at hm

/-- `merge`'s side conditions on the saturated facts. -/
def mergeReady (S : List Assertion) (a : Ind) (n : Nat) (r : Role) (l : List Ind) : Bool :=
  boundAt S a n r l && l.length == n + 1 && decide l.Nodup &&
  l.all (fun b => S.contains (.rel r a b))

mutual

/-- The checker over a fact list. -/
def checkF (C : Ctx) (fuel : Nat) (F : List Assertion) : Cert → Bool
  | .close => clashIn (saturate C fuel F)
  | .split a c d l r =>
      let S := saturate C fuel F
      S.contains (.inst a (.disj c d)) &&
      checkF C fuel (.inst a c :: S) l && checkF C fuel (.inst a d :: S) r
  | .exWit a r c x k =>
      let S := saturate C fuel F
      exAvailable S a r c && !(indsOf S).contains x &&
      checkF C fuel (.rel r a x :: .inst x c :: S) k
  | .merge a n r l cases =>
      let S := saturate C fuel F
      mergeReady S a n r l &&
      (pairsOf l).all (fun p => checkCases C fuel S p.1 p.2 cases)

/-- Some case refutes the merge of `b` and `c`, in either direction. -/
def checkCases (C : Ctx) (fuel : Nat) (S : List Assertion) (b c : Ind) : MergeCases → Bool
  | .nil => false
  | .cons b' c' k rest =>
      (((b' == b && c' == c) || (b' == c && c' == b)) && checkF C fuel (mergeInds b' c' S) k) ||
      checkCases C fuel S b c rest

end

/-! ## Soundness of the checker -/

theorem mem_pairsOf_of {b c : Ind} : ∀ {l : List Ind}, b ∈ l → c ∈ l → b ≠ c →
    (b, c) ∈ pairsOf l ∨ (c, b) ∈ pairsOf l := by
  intro l
  induction l with
  | nil => intro hb; cases hb
  | cons x xs ih =>
      intro hb hc hbc
      simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq]
      cases hb with
      | head =>
          cases hc with
          | head => exact absurd rfl hbc
          | tail _ hc' => exact Or.inl (Or.inl ⟨c, hc', rfl, rfl⟩)
      | tail _ hb' =>
          cases hc with
          | head => exact Or.inr (Or.inl ⟨b, hb', rfl, rfl⟩)
          | tail _ hc' =>
              rcases ih hb' hc' hbc with h | h
              · exact Or.inl (Or.inr h)
              · exact Or.inr (Or.inr h)

/-- The fresh-witness step, semantically: bend `ν` at a name the facts
    do not mention. -/
theorem satAll_bend {δ : Type} {I : Interp δ} {ν : Ind → δ} {S : List Assertion}
    (hS : SatAll I ν S) {x : Ind} (hx : x ∉ indsOf S) (y : δ) :
    SatAll I (fun i => if i = x then y else ν i) S := by
  intro φ hφ
  refine satisfies_agree ?_ (hS _ hφ)
  intro i hi
  have hix : i ≠ x := fun h => hx (h ▸ List.mem_flatMap.mpr ⟨_, hφ, hi⟩)
  exact if_neg hix

theorem exAvailable_sound {δ : Type} {I : Interp δ} {ν : Ind → δ} {S : List Assertion}
    (hS : SatAll I ν S) {a : Ind} {r : Role} {c : Concept}
    (h : exAvailable S a r c = true) :
    ∃ y, I.role r (ν a) y ∧ I.sem c y := by
  simp only [exAvailable, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact hS _ h
  · have ⟨ψ, hψ, hm⟩ := List.any_eq_true.mp h
    cases ψ with
    | inst a' k =>
        cases k with
        | atLeastQ n r' c' =>
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
            obtain ⟨⟨⟨rfl, rfl⟩, hc⟩, hn⟩ := hm
            have ⟨l, hlen, _, hall⟩ := hS _ hψ
            match l, hlen with
            | y :: _, _ =>
                rcases hc with rfl | rfl
                · exact ⟨y, hall y (List.Mem.head _)⟩
                · exact ⟨y, (hall y (List.Mem.head _)).1, trivial⟩
            | [], hlen => simp at hlen; omega
        | atLeast n r' =>
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hn⟩ := hm
            have ⟨l, hlen, _, hall⟩ := hS _ hψ
            match l, hlen with
            | y :: _, _ => exact ⟨y, hall y (List.Mem.head _), trivial⟩
            | [], hlen => simp at hlen; omega
        | atom _ => simp at hm
        | top => simp at hm
        | bot => simp at hm
        | neg _ => simp at hm
        | conj _ _ => simp at hm
        | disj _ _ => simp at hm
        | all _ _ => simp at hm
        | ex r' c' =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hm
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
            have ⟨y, hr, _⟩ := hS _ hψ
            exact ⟨y, hr, trivial⟩
        | atMost _ _ => simp at hm
        | atMostQ _ _ _ => simp at hm
    | rel _ _ _ => simp at hm
    | diff _ _ => simp at hm

mutual

theorem checkF_sound {δ : Type} {I : Interp δ} {C : Ctx} (hC : CtxValid I C)
    (fuel : Nat) : ∀ (cert : Cert) (F : List Assertion) (ν : Ind → δ),
    checkF C fuel F cert = true → ¬ SatAll I ν F
  | .close, F, ν, h, hF => clashIn_sound (saturate_sound hC fuel hF) (by simpa [checkF] using h)
  | .split a c d l r, F, ν, h, hF => by
      simp only [checkF, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨⟨hd, hl⟩, hr⟩ := h
      have hS := saturate_sound hC fuel hF
      cases hS _ hd with
      | inl hc =>
          refine checkF_sound hC fuel l _ ν hl ?_
          intro φ hφ
          cases hφ with
          | head => exact hc
          | tail _ h' => exact hS _ h'
      | inr hc =>
          refine checkF_sound hC fuel r _ ν hr ?_
          intro φ hφ
          cases hφ with
          | head => exact hc
          | tail _ h' => exact hS _ h'
  | .exWit a r c x k, F, ν, h, hF => by
      simp only [checkF, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hav, hfresh⟩, hk⟩ := h
      have hS := saturate_sound hC fuel hF
      have hx : x ∉ indsOf (saturate C fuel F) := by
        intro hm
        have : (indsOf (saturate C fuel F)).contains x = true := List.contains_iff_mem.mpr hm
        rw [this] at hfresh
        cases hfresh
      have ⟨y, hry, hcy⟩ := exAvailable_sound hS hav
      -- `a` is named in the saturated facts (`exAvailable` found a fact
      -- about it), so it is not the fresh name.
      have ha : a ∈ indsOf (saturate C fuel F) := by
        simp only [exAvailable, Bool.or_eq_true, List.contains_iff_mem] at hav
        rcases hav with hm | hm
        · exact List.mem_flatMap.mpr ⟨_, hm, by simp [Assertion.inds]⟩
        · have ⟨ψ, hψ, hmm⟩ := List.any_eq_true.mp hm
          cases ψ with
          | inst a' k' =>
              have ha' : a' = a := by
                cases k' <;> simp_all
              exact List.mem_flatMap.mpr ⟨_, hψ, by simp [Assertion.inds, ha']⟩
          | rel _ _ _ => simp at hmm
          | diff _ _ => simp at hmm
      have hax : a ≠ x := fun he => hx (he ▸ ha)
      refine checkF_sound hC fuel k _ (fun i => if i = x then y else ν i) hk ?_
      intro φ hφ
      cases hφ with
      | head =>
          show I.role r (if a = x then y else ν a) (if x = x then y else ν x)
          rw [if_neg hax, if_pos rfl]
          exact hry
      | tail _ hφ' =>
          cases hφ' with
          | head =>
              show I.sem c (if x = x then y else ν x)
              rw [if_pos rfl]
              exact hcy
          | tail _ hφ'' => exact satAll_bend hS hx y _ hφ''
  | .merge a n r l cases, F, ν, h, hF => by
      simp only [checkF, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hready, hpairs⟩ := h
      simp only [mergeReady, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.all_eq_true] at hready
      obtain ⟨⟨⟨hmax, hlen⟩, hnd⟩, hrel0⟩ := hready
      have hrel : ∀ b ∈ l, Assertion.rel r a b ∈ saturate C fuel F :=
        fun b hb => List.contains_iff_mem.mp (hrel0 b hb)
      have hS := saturate_sound hC fuel hF
      by_cases hcoll : ∃ b ∈ l, ∃ c ∈ l, b ≠ c ∧ ν b = ν c
      · have ⟨b, hb, c, hc, hbc, hval⟩ := hcoll
        rcases mem_pairsOf_of hb hc hbc with hp | hp
        · exact checkCases_sound hC fuel cases _ b c ν (Or.inl hval) (hpairs _ hp) hS
        · exact checkCases_sound hC fuel cases _ c b ν (Or.inr hval) (hpairs _ hp) hS
      · refine boundAt_sound hS hmax hrel ?_ hlen
        refine pairwise_map_ne_of_injOn hnd ?_
        intro b hb c hc hbc hEq
        exact hcoll ⟨b, hb, c, hc, hbc, hEq⟩

theorem checkCases_sound {δ : Type} {I : Interp δ} {C : Ctx} (hC : CtxValid I C)
    (fuel : Nat) : ∀ (cases : MergeCases) (S : List Assertion) (b c : Ind) (ν : Ind → δ),
    (ν b = ν c ∨ ν c = ν b) → checkCases C fuel S b c cases = true → ¬ SatAll I ν S
  | .nil, _, _, _, _, _, h, _ => by simp [checkCases] at h
  | .cons b' c' k rest, S, b, c, ν, hval, h, hS => by
      simp only [checkCases, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hnames, hk⟩ | hrest
      · have hv : ν b' = ν c' := by
          rcases hnames with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases hval with h | h
            · exact h
            · exact h.symm
          · rcases hval with h | h
            · exact h.symm
            · exact h
        exact checkF_sound hC fuel k _ ν hk (satAll_mergeInds hv hS)
      · exact checkCases_sound hC fuel rest S b c ν hval hrest hS

end

/-! ## The checker on an ontology, and the theorem -/

/-- The left-hand sides an edge can prove (`exGen`). -/
def edgeLhs (T : List (Concept × Concept)) : List Concept :=
  (T.filterMap (fun ax => match ax.1 with
    | .ex r c => some (Concept.ex r c)
    | .atLeast 1 r => some (Concept.atLeast 1 r)
    | .atLeastQ 1 r c => some (Concept.atLeastQ 1 r c)
    | _ => none)).eraseDups

/-- The Boolean subterms of a concept, through the fillers of `∃` and
    `≥ n r.C` (the shapes `exGen` proves from an edge). -/
def boolSubterms : Concept → List Concept
  | .conj c d => .conj c d :: (boolSubterms c ++ boolSubterms d)
  | .disj c d => .disj c d :: (boolSubterms c ++ boolSubterms d)
  | .ex _ c => boolSubterms c
  | .atLeastQ _ _ c => boolSubterms c
  | _ => []

def Ctx.ofOntology (O : DlOntology) : Ctx :=
  let T := normTBox O.tbox
  { T := T, R := O.rbox, L := edgeLhs T, inv := O.inv,
    B := (T.flatMap (fun ax => boolSubterms ax.1)).eraseDups }

/-- The saturation round bound. The rounds stop earlier at a fixpoint;
    a bound that is too small makes a certificate fail to check, never
    the reverse. -/
def certFuel : Nat := 64

/-- THE CHECKER: total, structural recursion on the certificate. -/
def checkCert (O : DlOntology) (c : Cert) : Bool :=
  checkF (Ctx.ofOntology O) certFuel (O.abox.map normAssertion) c

/-- SOUNDNESS: an accepted certificate leaves the ontology with no
    model under the OWL 2 Direct Semantics (Tables 4, 5, 6 and 10, in
    the fragment of `Concept`). -/
theorem checkCert_sound {O : DlOntology} {c : Cert} (h : checkCert O c = true) :
    ¬ ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), DirectModel I ν O := by
  intro ⟨δ, I, ν, hR, hT, hInv, hA⟩
  have hC : CtxValid I (Ctx.ofOntology O) := ⟨respects_normTBox hT, hR, hInv⟩
  refine checkF_sound hC certFuel c _ ν h ?_
  intro φ hφ
  have ⟨ψ, hψ, he⟩ := List.mem_map.mp hφ
  subst he
  exact satisfies_normAssertion ψ (hA ψ hψ)

/-- The same statement in the shape of `Tableau.Consistent`: an
    ontology with an empty TBox and an accepted certificate is not
    consistent with respect to its role box. -/
theorem checkCert_not_consistent {R : RoleAxioms} {A : List Assertion} {c : Cert}
    (h : checkCert { rbox := R, abox := A } c = true) : ¬ Consistent R A := by
  intro ⟨δ, I, ν, hR, hA⟩
  exact checkCert_sound h ⟨δ, I, ν, hR, (fun _ hax => by cases hax), (fun _ hq => by cases hq), hA⟩

end L4Factoidal.OWL
