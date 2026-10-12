/-
Capability-aware planner, KR 2.1: the requirement.

OKR batch 2, KR 2.1: https://github.com/danbri/factoidal/issues/801
(epic https://github.com/danbri/factoidal/issues/800). Design record:
`docs/designissues/2026-10-12-capability-aware-planner.md`, section
"KR 2.1: Lean definitions".

A requirement is a SPARQL basic graph pattern with filters and a
projection. It reuses the reference evaluator's types (`TriplePattern`,
`Bgp`, `Binding`, `GraphPattern`) and its meaning IS the reference
evaluator's answer sequence: `GraphPattern.eval` over the pattern, then
`projectSolutions` (SPARQL 1.1 section 18.5 and 18.2.5.4). This module
defines no second RDF term type and no second solution type.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.IndexedEvalRefinement

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## Solution mappings as partial functions

SPARQL 1.1 section 18.1.8 defines a solution mapping as a partial
function from variables to RDF terms. The evaluator stores it as an
association list (`Binding`), so two lists with different entry orders
can denote the same mapping. `SolEquiv` is equality of the partial
functions; `SolLe` is the extension order. -/

/-- The two association lists denote the same partial function. -/
def SolEquiv (a b : Binding) : Prop := ∀ v, a.lookup v = b.lookup v

/-- `a` is a restriction of `b`: every variable bound in `a` is bound to
the same term in `b`. -/
def SolLe (a b : Binding) : Prop := ∀ v t, a.lookup v = some t → b.lookup v = some t

theorem SolEquiv.symm {a b : Binding} (h : SolEquiv a b) : SolEquiv b a :=
  fun v => (h v).symm

theorem SolLe.refl (a : Binding) : SolLe a a := fun _ _ h => h

theorem SolLe.trans {a b c : Binding} (h1 : SolLe a b) (h2 : SolLe b c) : SolLe a c :=
  fun v t h => h2 v t (h1 v t h)

theorem lookup_bind (v w : VarName) (t : Term) (mu : Binding) :
    (mu.bind v t).lookup w = if v = w then some t else mu.lookup w := by
  simp [Binding.bind, Binding.lookup]

/-- Binding an unbound variable extends the mapping. -/
theorem SolLe.bind_of_none {mu : Binding} {v : VarName} (t : Term)
    (h : mu.lookup v = none) : SolLe mu (mu.bind v t) := by
  intro w u hw
  rw [lookup_bind]
  by_cases hvw : v = w
  · subst hvw; rw [h] at hw; cases hw
  · simp [hvw, hw]

/-- `projectBinding` (the evaluator's `Project`) as a partial function. -/
theorem lookup_projectBinding (vs : List VarName) (mu : Binding) (v : VarName) :
    (projectBinding vs mu).lookup v = if vs.contains v then mu.lookup v else none := by
  induction mu with
  | nil => simp [projectBinding, Binding.lookup]
  | cons hd rest ih =>
    obtain ⟨w, t⟩ := hd
    by_cases hw : vs.contains w = true
    · have hw' : w ∈ vs := by simpa using hw
      simp only [projectBinding, hw, if_true, Binding.lookup]
      by_cases hwv : w = v
      · subst hwv; simp [hw']
      · simp [hwv, ih]
    · have hw' : w ∉ vs := by simpa using hw
      simp only [projectBinding, hw, Binding.lookup]
      by_cases hwv : w = v
      · subst hwv; simp [ih, hw']
      · simp [hwv, ih]

theorem projectBinding_equiv (vs : List VarName) {a b : Binding} (h : SolEquiv a b) :
    SolEquiv (projectBinding vs a) (projectBinding vs b) := by
  intro v
  rw [lookup_projectBinding, lookup_projectBinding, h v]

/-! ## Filters

A requirement filter is a test on solution mappings that depends only on
the partial function, not on the order of the association list. Every
SPARQL `FILTER` expression has this property (an expression reads a
variable through `Binding.lookup`); the field `respects` makes it a
checked obligation here. The evaluator's `GraphPattern.filter` receives
`fun _ => f.test`. -/
structure RowFilter where
  test : Binding → Bool
  respects : ∀ a b, SolEquiv a b → test a = test b

/-- A filter on the value of one variable (`none` when unbound). -/
def RowFilter.onVar (v : VarName) (pred : Option Term → Bool) : RowFilter where
  test mu := pred (mu.lookup v)
  respects a b h := by simp [h v]

/-! ## Variables of a triple pattern

Only the variables in the three top positions. The rewriting relation
(`Planner.Plan`) covers only triple patterns whose positions are
variables or constants (no triple-term patterns), and for those this is
the full variable set. -/

def subjectVars : PatternSubject → List VarName
  | .var v => [v]
  | _      => []

def termVars : PatternTerm → List VarName
  | .var v => [v]
  | _      => []

def tpVars (tp : TriplePattern) : List VarName :=
  subjectVars tp.s ++ termVars tp.p ++ termVars tp.o

def bgpVars (b : Bgp) : List VarName := b.flatMap tpVars

/-! ## The requirement and its meaning -/

structure Requirement where
  bgp : Bgp
  filters : List RowFilter := []
  projection : List VarName

/-- The requirement as an evaluator graph pattern: the filters, outermost
first, around the basic graph pattern. -/
def Requirement.pattern (r : Requirement) : GraphPattern :=
  r.filters.foldr (fun f p => .filter (fun _ => f.test) p) (.bgp r.bgp)

/-- The answers of the requirement over a graph: the reference
evaluator's solution sequence, projected. -/
def Requirement.answers (r : Requirement) (g : Graph) : SolutionSeq :=
  projectSolutions r.projection (r.pattern.eval g)

end L4Factoidal.Planner
