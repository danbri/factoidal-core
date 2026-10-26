/-
Capability-aware planner, KR 2.1: plans and their execution.

https://github.com/danbri/factoidal/issues/801. A plan is a small typed
tree: access a capability with arguments drawn from constants or from
variables bound by earlier steps (the dependent join of access-pattern
query answering), join, filter, project, union. `Plan.exec` is the
executable semantics over pure capability implementations. Each result
row carries a marker that is `true` when the row depends on an
`approximate` capability.

`Rewriting` is the checkable relation between a requirement and a plan:
a list of access steps, a Boolean check `Rewriting.check`, and the plan
`Rewriting.toPlan` that it denotes (the steps as a chain of dependent
joins, then the requirement's own filters and projection).
-/
import L4Factoidal.Planner.Mapping

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- An argument of an access: a constant, or a variable. In an input
position a variable must be bound by an earlier step; in an output
position it is bound (or checked) by the access. -/
inductive Arg where
  | const (t : Term)
  | var   (v : VarName)
  deriving DecidableEq, Repr

def Arg.resolve (mu : Binding) : Arg → Option Term
  | .const t => some t
  | .var v   => mu.lookup v

def Arg.vars : Arg → List VarName
  | .const _ => []
  | .var v   => [v]

/-- One access: the index of a source in the catalog, and one argument
per position of its relation. -/
structure Access where
  src : Nat
  args : List Arg
  deriving DecidableEq, Repr

def Access.vars (a : Access) : List VarName := a.args.flatMap Arg.vars

/-- Collect the input binding (tail-recursive, accumulator). -/
def inputsGo (args : List Arg) (mu : Binding) : List Nat → InputBinding → Option InputBinding
  | [],      acc => some acc.reverse
  | i :: is, acc =>
    match args[i]? with
    | some a =>
      match a.resolve mu with
      | some t => inputsGo args mu is ((i, t) :: acc)
      | none   => none
    | none => none

/-- The values of the capability's required inputs under `mu`; `none`
when a required input is an unbound variable or is missing. -/
def Access.inputs? (cap : Capability) (a : Access) (mu : Binding) : Option InputBinding :=
  inputsGo a.args mu cap.inputs []

/-- Bind the arguments to one returned tuple: a constant must equal the
tuple value; a bound variable must equal it; an unbound variable is
bound to it. Tail-recursive. -/
def bindArgs : List Arg → Tuple → Binding → Option Binding
  | [],      [],      mu => some mu
  | a :: as, t :: ts, mu =>
    match a with
    | .const c => if c = t then bindArgs as ts mu else none
    | .var v =>
      match mu.lookup v with
      | some e => if e = t then bindArgs as ts mu else none
      | none   => bindArgs as ts (mu.bind v t)
  | _, _, _ => none

/-- A plan. `join l r` is the dependent join: `r` runs once per row of
`l`, with that row's bindings available as inputs. -/
inductive Plan where
  /-- The incoming row, unchanged. -/
  | unit
  | access  (a : Access)
  | join    (l r : Plan)
  | filter  (f : RowFilter) (p : Plan)
  | project (vars : List VarName) (p : Plan)
  | union   (l r : Plan)

/-- A result row: a solution mapping and the approximate marker. -/
structure Row where
  binding : Binding
  approx : Bool

/-- The executable semantics. -/
def Plan.exec (cat : Catalog) : Plan → Row → List Row
  | .unit, r => [r]
  | .access a, r =>
    match cat[a.src]? with
    | none => []
    | some s =>
      match a.inputs? s.cap r.binding with
      | none => []
      | some inp =>
        (s.sem.impl inp).filterMap (fun tup =>
          if s.wellTyped tup then
            (bindArgs a.args tup r.binding).map
              (fun b => { binding := b, approx := r.approx || s.cap.exactness.isApprox })
          else none)
  | .join l q, r => (l.exec cat r).flatMap (fun x => q.exec cat x)
  | .filter f p, r => (p.exec cat r).filter (fun x => f.test x.binding)
  | .project vs p, r =>
    (p.exec cat r).map (fun x => { binding := projectBinding vs x.binding, approx := x.approx })
  | .union l q, r => l.exec cat r ++ q.exec cat r

/-- Run a plan from the empty solution mapping, unmarked. -/
def Plan.run (cat : Catalog) (p : Plan) : List Row :=
  p.exec cat { binding := [], approx := false }

/-! ## Well-formedness: the access-pattern condition

`wfBound cat p bound` returns the variables that are certainly bound
after `p` when `bound` are bound before it, or `none` when some access
has a required input that is neither a constant nor a variable in the
bound set, names no source, or has the wrong number of arguments. -/

def Access.inputsBound (cap : Capability) (a : Access) (bound : List VarName) : Bool :=
  cap.inputs.all (fun i =>
    match a.args[i]? with
    | some (.const _) => true
    | some (.var v)   => bound.contains v
    | none            => false)

def Plan.wfBound (cat : Catalog) : Plan → List VarName → Option (List VarName)
  | .unit, b => some b
  | .access a, b =>
    match cat[a.src]? with
    | none => none
    | some s =>
      if a.args.length = s.cap.arity && a.inputsBound s.cap b then some (b ++ a.vars) else none
  | .join l q, b =>
    match l.wfBound cat b with
    | none    => none
    | some b1 => q.wfBound cat b1
  | .filter _ p, b => p.wfBound cat b
  | .project vs p, b => (p.wfBound cat b).map (fun b1 => vs.filter (fun v => b1.contains v))
  | .union l q, b =>
    match l.wfBound cat b, q.wfBound cat b with
    | some b1, some b2 => some (b1.filter (fun v => b2.contains v))
    | _, _ => none

/-- A plan is well-formed when, started with nothing bound, every access
has its required inputs bound by earlier steps. -/
def Plan.WellFormed (cat : Catalog) (p : Plan) : Prop :=
  (p.wfBound cat []).isSome = true

instance (cat : Catalog) (p : Plan) : Decidable (p.WellFormed cat) := by
  unfold Plan.WellFormed; infer_instance

/-- `true` when some access in the run of `p` from row `r` found a
required input unbound (and so returned no rows). -/
def Plan.inputFailure (cat : Catalog) : Plan → Row → Bool
  | .unit, _ => false
  | .access a, r =>
    match cat[a.src]? with
    | none   => false
    | some s => (a.inputs? s.cap r.binding).isNone
  | .join l q, r => l.inputFailure cat r || (l.exec cat r).any (fun x => q.inputFailure cat x)
  | .filter _ p, r => p.inputFailure cat r
  | .project _ p, r => p.inputFailure cat r
  | .union l q, r => l.inputFailure cat r || q.inputFailure cat r

/-! ## Rewritings

A template, with the access arguments put in for its tuple positions,
is a triple pattern: a variable argument gives a variable, a constant
gives a constant. `Access.covers` says that one template of the
accessed source becomes exactly the given requirement triple pattern. -/

def patternTermOfTerm : Term → Option PatternTerm
  | .iri i     => some (.iri i)
  | .bnode b   => some (.bnode b)
  | .literal l => some (.literal l)
  | .tripleTerm _ _ _ => none

def patternSubjectOfTerm : Term → Option PatternSubject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

def Slot.patternTerm (args : List Arg) : Slot → Option PatternTerm
  | .const t => patternTermOfTerm t
  | .arg i =>
    match args[i]? with
    | some (.var v)   => some (.var v)
    | some (.const t) => patternTermOfTerm t
    | none            => none

def Slot.patternSubject (args : List Arg) : Slot → Option PatternSubject
  | .const t => patternSubjectOfTerm t
  | .arg i =>
    match args[i]? with
    | some (.var v)   => some (.var v)
    | some (.const t) => patternSubjectOfTerm t
    | none            => none

def TripleTemplate.subst (args : List Arg) (tm : TripleTemplate) : Option TriplePattern :=
  match tm.s.patternSubject args, tm.p.patternTerm args, tm.o.patternTerm args with
  | some s, some p, some o => some { s := s, p := p, o := o }
  | _, _, _ => none

def Access.covers (cat : Catalog) (a : Access) (tp : TriplePattern) : Bool :=
  match cat[a.src]? with
  | none   => false
  | some s => s.mapping.templates.any (fun tm => tm.subst a.args == some tp)

/-- A rewriting: the access steps, run left to right as dependent joins. -/
structure Rewriting where
  steps : List Access
  deriving DecidableEq, Repr

def chainPlan (steps : List Access) : Plan :=
  steps.foldr (fun a p => .join (.access a) p) .unit

def filtersPlan (fs : List RowFilter) (p : Plan) : Plan :=
  fs.foldr (fun f q => .filter f q) p

/-- The plan a rewriting denotes: the access chain, then the
requirement's filters (same list, same order), then its projection. -/
def Rewriting.toPlan (req : Requirement) (rw : Rewriting) : Plan :=
  .project req.projection (filtersPlan req.filters (chainPlan rw.steps))

/-- The checkable rewriting relation:
1. every requirement triple pattern is covered by some step;
2. every variable a step binds is a variable of the requirement's BGP;
3. the access chain is well-formed (access-pattern condition). -/
def Rewriting.check (cat : Catalog) (req : Requirement) (rw : Rewriting) : Bool :=
  req.bgp.all (fun tp => rw.steps.any (fun a => a.covers cat tp)) &&
  rw.steps.all (fun a => a.vars.all (fun v => (bgpVars req.bgp).contains v)) &&
  ((chainPlan rw.steps).wfBound cat []).isSome

/-- `p` was produced as a rewriting of `req` over `cat`. -/
def IsRewriting (cat : Catalog) (req : Requirement) (p : Plan) : Prop :=
  ∃ rw : Rewriting, rw.check cat req = true ∧ p = rw.toPlan req

end L4Factoidal.Planner
