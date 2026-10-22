/-
Capability-aware planner, OKR batch 3 KR 4.1: a plan executed through a
monad, so that a capability is called at run time (an SBM11 generation read
through the id path, a service, a tool).

https://github.com/danbri/factoidal/issues/875 (epic
https://github.com/danbri/factoidal/issues/800). Design record
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 12.

`Plan.exec` (`Planner/Plan.lean`) is the specification: it reads each
source's tuples from the pure implementation `Source.sem.impl`.
`Plan.execM` is the same plan run in a monad `m`: each access calls
`call src inp : m (List Tuple)` and gives the rows that `Plan.exec` gives
for those tuples (`accessRows`). The catalog gives the capability, the
mapping and the tuple check; the source's `sem` is not read.

Relation to the specification (`execM_eq_exec`): in a lawful monad, when
every call of source `i` returns `pure` of the implementation of the
catalog's source `i` (`CallsDenote`), `execM` returns `pure` of the rows of
`exec`. The hypothesis is about one call of one source; the conclusion is
about every plan (joins run the right side once per left row, filters,
projections, unions). `runM_sound` carries `rewriting_sound` over to the
monadic run.

For `IO` the hypothesis is not a theorem: a call reads bytes from a file.
The test set checks it for SBM11 (`Harness/PlannerKinds.lean`: every keyed
id-path call equals the pure implementation, and every plan run through IO
gives the rows of the pure run), and `tests/planner/sbm11_gate.sh` compares
the IO run with `l4sbm11 query`.

Recursion: `execM` recurses on the plan tree (one level per plan
operator); the rows of a join go through core `List.mapM`.
-/
import L4Factoidal.Planner.Soundness

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- The rows one access gives for the tuples that a call returned: the
same function as the access case of `Plan.exec`. -/
def accessRows (s : Source) (a : Access) (r : Row) (tups : List Tuple) : List Row :=
  tups.filterMap (fun tup =>
    if s.wellTyped tup then
      (bindArgs a.args tup r.binding).map
        (fun b => { binding := b, approx := r.approx || s.cap.exactness.isApprox })
    else none)

/-- Calls of the catalog's sources in monad `m`: source index, input
binding, tuples. -/
abbrev Calls (m : Type → Type) := Nat → InputBinding → m (List Tuple)

/-- `flatMap` through a monad, left to right: core `List.mapM` (a loop
with an accumulator, `List.mapM.loop`), then `flatten`. -/
def flatMapRowsM {m : Type → Type} [Monad m] {α β : Type} (f : α → m (List β)) (xs : List α) :
    m (List β) := do
  let yss ← xs.mapM f
  pure yss.flatten

/-- The plan run in monad `m`; each access calls `call`. -/
def Plan.execM {m : Type → Type} [Monad m] (cat : Catalog) (call : Calls m) : Plan → Row → m (List Row)
  | .unit, r => pure [r]
  | .access a, r =>
    match cat[a.src]? with
    | none => pure []
    | some s =>
      match a.inputs? s.cap r.binding with
      | none => pure []
      | some inp => do
        let tups ← call a.src inp
        pure (accessRows s a r tups)
  | .join l q, r => do
    let xs ← l.execM cat call r
    flatMapRowsM (fun x => q.execM cat call x) xs
  | .filter f p, r => do
    let xs ← p.execM cat call r
    pure (xs.filter (fun x => f.test x.binding))
  | .project vs p, r => do
    let xs ← p.execM cat call r
    pure (xs.map (fun x => { binding := projectBinding vs x.binding, approx := x.approx }))
  | .union l q, r => do
    let xs ← l.execM cat call r
    let ys ← q.execM cat call r
    pure (xs ++ ys)

/-- Run from the empty solution mapping, unmarked. -/
def Plan.runM {m : Type → Type} [Monad m] (cat : Catalog) (call : Calls m) (p : Plan) : m (List Row) :=
  p.execM cat call { binding := [], approx := false }

/-- Every call of source `i` answers as the implementation of the
catalog's source `i`. -/
def CallsDenote {m : Type → Type} [Monad m] (cat : Catalog) (call : Calls m) : Prop :=
  ∀ i s inp, cat[i]? = some s → call i inp = pure (s.sem.impl inp)

/-! ## Theorems -/

theorem flatMapRowsM_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (f : α → m (List β)) (g : α → List β) (hf : ∀ x, f x = pure (g x)) (xs : List α) :
    flatMapRowsM f xs = pure (xs.flatMap g) := by
  have hfg : f = fun x => pure (g x) := funext hf
  subst hfg
  simp [flatMapRowsM, List.mapM_pure, List.flatMap_def]

theorem exec_access_eq (cat : Catalog) (a : Access) (r : Row) :
    (Plan.access a).exec cat r =
      match cat[a.src]? with
      | none => []
      | some s =>
        match a.inputs? s.cap r.binding with
        | none => []
        | some inp => accessRows s a r (s.sem.impl inp) := rfl

/-- The monadic run equals the pure run when every call answers as the
catalog's implementation. -/
theorem execM_eq_exec {m : Type → Type} [Monad m] [LawfulMonad m] (cat : Catalog) (call : Calls m)
    (hcall : CallsDenote cat call) (p : Plan) (r : Row) :
    p.execM cat call r = pure (p.exec cat r) := by
  induction p generalizing r with
  | unit => rfl
  | access a =>
    rw [exec_access_eq]
    simp only [Plan.execM]
    cases hs : cat[a.src]? with
    | none => rfl
    | some s =>
      simp only
      cases hi : a.inputs? s.cap r.binding with
      | none => rfl
      | some inp =>
        simp only [hcall a.src s inp hs, pure_bind]
  | join l q ihl ihq =>
    simp only [Plan.execM, Plan.exec, ihl, pure_bind]
    exact flatMapRowsM_pure _ _ (fun x => ihq x) _
  | filter f p ih =>
    simp only [Plan.execM, Plan.exec, ih, pure_bind]
  | project vs p ih =>
    simp only [Plan.execM, Plan.exec, ih, pure_bind]
  | union l q ihl ihq =>
    simp only [Plan.execM, Plan.exec, ihl, ihq, pure_bind]

theorem runM_eq_run {m : Type → Type} [Monad m] [LawfulMonad m] (cat : Catalog) (call : Calls m)
    (hcall : CallsDenote cat call) (p : Plan) :
    p.runM cat call = pure (p.run cat) :=
  execM_eq_exec cat call hcall p _

/-- Soundness of the monadic run: it returns the rows of `Plan.run`, and
every unmarked one is an answer of the requirement over the declared
graph (`rewriting_sound`). -/
theorem runM_sound {m : Type → Type} [Monad m] [LawfulMonad m] {cat : Catalog} {req : Requirement}
    {p : Plan} (call : Calls m) (hcall : CallsDenote cat call) (hsound : ExactSourcesSound cat)
    (hrw : IsRewriting cat req p) :
    p.runM cat call = pure (p.run cat) ∧ SoundFor cat req p :=
  ⟨runM_eq_run cat call hcall p, rewriting_sound hsound hrw⟩

/-- The calls that answer from the catalog's implementations (in any
monad). They satisfy `CallsDenote`. -/
def pureCalls {m : Type → Type} [Monad m] (cat : Catalog) : Calls m :=
  fun i inp => pure (match cat[i]? with
    | some s => s.sem.impl inp
    | none => [])

theorem pureCalls_denote {m : Type → Type} [Monad m] (cat : Catalog) :
    CallsDenote cat (pureCalls (m := m) cat) := by
  intro i s inp hs
  simp [pureCalls, hs]

end L4Factoidal.Planner
