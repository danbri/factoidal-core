/-
Capability-aware planner, KR 2.2: the structural planner.

OKR batch 2, KR 2.2: https://github.com/danbri/factoidal/issues/801
(epic https://github.com/danbri/factoidal/issues/800). Design record:
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 9.

The search finds the rewritings (`Planner.Plan`, `Rewriting.check`) of a
requirement over a catalog, in the manner of PDQ's answerability under
access patterns: an access may run only when each of its required inputs
is a constant or a variable that an earlier access bound.

Algorithm.

1. The argument pool of the requirement: the variables of its BGP and the
   constants (IRIs, blank nodes, literals) of its triple patterns.
2. The candidate accesses: for each source of the catalog, each argument
   list of the source's arity over the pool, kept when the access is an
   exact cover (`Access.exactCover`): a template of the source becomes a
   requirement triple pattern under the arguments, and every argument
   position is used by such a template.
3. A depth-first search with fuel `k` (the bound on the number of
   accesses). A state is the list of accesses chosen so far and the
   variables they bind. When the chosen accesses cover every triple
   pattern of the requirement, the state is a result. Otherwise the
   search extends the state with each candidate that is executable (its
   required inputs are bound; `Access.executable`) and useful (it binds a
   new variable or covers a triple pattern that no chosen access covers).
4. Each result that passes `Rewriting.check` and is minimal (no single
   access can be removed with the check still passing) is kept
   (`familyAll`). When some kept rewriting is irredundant in any order
   (`Rewriting.irredundant`), only those are kept. The kept rewritings are
   the plan family, ordered exact before approximate, then by the cost
   estimate (`estCost`), then by length. The order and the preference have
   no effect on correctness.

Theorems.

* `search_check`, `search_isRewriting`, `search_sound`: every rewriting
  the search returns passes `Rewriting.check`, so `rewriting_sound`
  applies to its plan.
* `search_complete`: if some rewriting with at most `k` accesses, each an
  exact cover, passes `Rewriting.check`, then the search with bound `k`
  returns at least one rewriting. `plan_notAnswerable_sound` is the same
  statement read from the verdict.
* `search_mem_of_minimal`: each minimal rewriting of exact covers with at
  most `k` accesses is in `familyAll` (before the irredundancy
  preference).
* `args_mem_pool_of_exactCover`: the arguments of an exact cover are in
  the pool, so step 2 lists every exact cover.

Rewritings outside the space of exact covers pass `Rewriting.check` too:
an access with a position that no requirement pattern names (a required
key, or a column the requirement does not use), and an access that covers
nothing and only binds a variable for a later access (an indirect plan
through an inclusion dependency, which is not modelled). The search does
not return them. Each is open, with an expected-failure case in
`Harness/PlannerTest.lean` naming
https://github.com/danbri/factoidal/issues/801.

Recursion: `dfs` recurses once per chosen access (at most `k`),
`argLists` once per argument position (the arity), `chainOk` once per
access of a rewriting. `estUseGo` and `greedyGo` are tail calls.
-/
import L4Factoidal.Planner.Soundness

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## The argument pool -/

def termOfPatternTerm : PatternTerm → Option Term
  | .iri i     => some (.iri i)
  | .bnode b   => some (.bnode b)
  | .literal l => some (.literal l)
  | _          => none

def termOfPatternSubject : PatternSubject → Option Term
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

def tpConsts (tp : TriplePattern) : List Term :=
  (termOfPatternSubject tp.s).toList ++ (termOfPatternTerm tp.p).toList ++
    (termOfPatternTerm tp.o).toList

def bgpConsts (b : Bgp) : List Term := b.flatMap tpConsts

/-- The variables and constants of the requirement's BGP, as arguments. -/
def Requirement.pool (req : Requirement) : List Arg :=
  (bgpVars req.bgp).eraseDups.map Arg.var ++ (bgpConsts req.bgp).eraseDups.map Arg.const

/-! ## Candidate accesses -/

/-- All argument lists of length `n` over the pool. -/
def argLists (pool : List Arg) : Nat → List (List Arg)
  | 0     => [[]]
  | n + 1 => (argLists pool n).flatMap (fun rest => pool.map (fun x => x :: rest))

/-! ### Exact covers

An access is an exact cover when some template of its source, with the
access arguments put in, is a triple pattern of the requirement, and each
argument position is used by such a template. So every argument of the
access is a term of a requirement triple pattern: the access adds no join
condition and no constant that the requirement does not state. The search
uses only exact covers. A rewriting of exact covers can still return
fewer answers than the requirement over the declared graph (a source may
not list its whole extension for an input), but it does not add a
condition that the requirement lacks. -/

def Slot.argPos : Slot → Option Nat
  | .arg i   => some i
  | .const _ => none

def TripleTemplate.argPositions (tm : TripleTemplate) : List Nat :=
  tm.s.argPos.toList ++ tm.p.argPos.toList ++ tm.o.argPos.toList

/-- The templates of the accessed source that become a requirement triple
pattern under the access arguments. -/
def Access.coveringTemplates (cat : Catalog) (req : Requirement) (a : Access) :
    List TripleTemplate :=
  match cat[a.src]? with
  | none   => []
  | some s => s.mapping.templates.filter (fun tm =>
      match tm.subst a.args with
      | some tp => req.bgp.contains tp
      | none    => false)

def Access.exactCover (cat : Catalog) (req : Requirement) (a : Access) : Bool :=
  !(a.coveringTemplates cat req).isEmpty &&
    (List.range a.args.length).all (fun i =>
      (a.coveringTemplates cat req).any (fun tm => tm.argPositions.contains i))

/-- Every access of the rewriting is an exact cover. -/
def Rewriting.ExactCovers (cat : Catalog) (req : Requirement) (rw : Rewriting) : Prop :=
  ∀ a ∈ rw.steps, a.exactCover cat req = true

def candidates (cat : Catalog) (req : Requirement) : List Access :=
  ((List.range cat.length).flatMap (fun i =>
    match cat[i]? with
    | some s => (argLists req.pool s.cap.arity).map (fun args => { src := i, args := args })
    | none   => [])).filter (·.exactCover cat req)

/-! ## The chain condition as a recursion over the steps -/

/-- The access names a source, has one argument per position, and each
required input is a constant or a bound variable. -/
def Access.executable (cat : Catalog) (bound : List VarName) (a : Access) : Bool :=
  match cat[a.src]? with
  | none   => false
  | some s => decide (a.args.length = s.cap.arity) && a.inputsBound s.cap bound

def chainOk (cat : Catalog) : List VarName → List Access → Bool
  | _, []     => true
  | b, a :: s => a.executable cat b && chainOk cat (b ++ a.vars) s

def coversAll (cat : Catalog) (req : Requirement) (steps : List Access) : Bool :=
  req.bgp.all (fun tp => steps.any (fun a => a.covers cat tp))

/-- The access binds a variable that is not yet bound, or covers a
triple pattern that no chosen access covers. -/
def Access.useful (cat : Catalog) (req : Requirement) (bound : List VarName)
    (steps : List Access) (a : Access) : Bool :=
  a.vars.any (fun v => !bound.contains v) ||
    req.bgp.any (fun tp => a.covers cat tp && !steps.any (fun x => x.covers cat tp))

/-! ## The search -/

/-- Depth-first search with fuel. `steps` are the accesses chosen so far
(in execution order) and `bound` the variables they bind. -/
def dfs (cat : Catalog) (req : Requirement) (cands : List Access) :
    Nat → List Access → List VarName → List (List Access)
  | 0, steps, _ => if coversAll cat req steps then [steps] else []
  | n + 1, steps, bound =>
    if coversAll cat req steps then [steps] else
      cands.flatMap (fun a =>
        if a.executable cat bound && a.useful cat req bound steps then
          dfs cat req cands n (steps ++ [a]) (bound ++ a.vars)
        else [])

/-- No single access can be removed with the check still passing. -/
def Rewriting.isMinimal (cat : Catalog) (req : Requirement) (rw : Rewriting) : Bool :=
  (List.range rw.steps.length).all (fun i => !Rewriting.check cat req ⟨rw.steps.eraseIdx i⟩)

/-! ## Cost estimate and the plan family

The estimate assumes, for each call of an access, the source's statistic
`rowsPerCall` when it has one, and otherwise `fanout` rows for each
variable the access binds for the first time; and one call of an access
per incoming row (the dependent join of `Plan.exec`). It orders the
family and decides admission (below); no theorem uses its numbers.

`estUse` is parameterised by an `EstModel` so that the driver
`Planner.Exec` can use the same walk with measured rows per call,
measured latency and the calls whose answers it already holds. -/

def Access.newVars (bound : List VarName) (a : Access) : Nat :=
  ((a.vars.eraseDups).filter (fun v => !bound.contains v)).length

/-- The estimated use of one access: its source, the calls, the tuples
returned, and the cost. -/
structure UseEst where
  src : Nat
  calls : Nat
  rows : Nat
  cost : Nat
  deriving Repr

/-- How an estimate counts: tuples per call (source index, source, new
variables), the cost of one call, the tuple count of an access whose
answer is already known (it makes no call), and whether an access whose
inputs are all constants is called once (a driver with a cache of call
results) or once per incoming row (`Plan.exec`). -/
structure EstModel where
  rowsPerCall : Nat → Source → Nat → Nat
  callCost : Nat → Source → Nat
  known : Access → Option Nat
  cacheScans : Bool := false

/-- The model of the cost model's own numbers. -/
def statModel (fanout : Nat) : EstModel where
  rowsPerCall := fun _ s nv => s.cap.cost.rowsPerCall.getD (fanout ^ nv)
  callCost := fun _ s => s.cap.cost.perCall
  known := fun _ => none

/-- Tail-recursive walk of a chain; the accumulator is in reverse order. -/
def estUseGo (cat : Catalog) (em : EstModel) :
    List Access → List VarName → Nat → List UseEst → List UseEst
  | [], _, _, acc => acc
  | a :: s, bound, calls, acc =>
    match cat[a.src]? with
    | none => estUseGo cat em s bound calls acc
    | some src =>
      match em.known a with
      | some n =>
        estUseGo cat em s (bound ++ a.vars) (calls * n)
          ({ src := a.src, calls := 0, rows := 0, cost := 0 } :: acc)
      | none =>
        let rpc := em.rowsPerCall a.src src (a.newVars bound)
        let n := if em.cacheScans && (a.inputs? src.cap []).isSome then min calls 1 else calls
        estUseGo cat em s (bound ++ a.vars) (calls * rpc)
          ({ src := a.src, calls := n, rows := n * rpc,
             cost := n * em.callCost a.src src + calls * rpc * src.cap.cost.perRow } :: acc)

def estUse (cat : Catalog) (em : EstModel) (steps : List Access) : List UseEst :=
  estUseGo cat em steps [] 1 []

def totalCost (us : List UseEst) : Nat := us.foldl (fun n u => n + u.cost) 0

/-- The sum of `f` over the uses of source `i`. -/
def sumUse (us : List UseEst) (i : Nat) (f : UseEst → Nat) : Nat :=
  us.foldl (fun n u => if u.src = i then n + f u else n) 0

/-- With `calls0 i` calls and `rows0 i` tuples already used, the estimated
use stays within every call quota and every row quota of the catalog. -/
def withinQuotas (cat : Catalog) (us : List UseEst) (calls0 rows0 : Nat → Nat) : Bool :=
  (List.range cat.length).all (fun i =>
    match cat[i]? with
    | none => true
    | some s =>
      (match s.cap.cost.callQuota with
       | some q => decide (calls0 i + sumUse us i (·.calls) ≤ q)
       | none => true) &&
      (match s.cap.cost.rowQuota with
       | some q => decide (rows0 i + sumUse us i (·.rows) ≤ q)
       | none => true))

def estCost (cat : Catalog) (fanout : Nat) (rw : Rewriting) : Nat :=
  totalCost (estUse cat (statModel fanout) rw.steps)

/-- The rewriting uses an `approximate` source; its rows are marked. -/
def Rewriting.approx (cat : Catalog) (rw : Rewriting) : Bool :=
  rw.steps.any (fun a =>
    match cat[a.src]? with
    | some s => s.cap.exactness.isApprox
    | none   => false)

/-- One member of the plan family. -/
structure Ranked where
  rewriting : Rewriting
  cost : Nat
  approx : Bool
  deriving Repr

def Ranked.le (x y : Ranked) : Bool :=
  (!x.approx && y.approx) ||
    (x.approx == y.approx &&
      (x.cost < y.cost ||
        (x.cost == y.cost && x.rewriting.steps.length ≤ y.rewriting.steps.length)))

def rank (cat : Catalog) (fanout : Nat) (rw : Rewriting) : Ranked :=
  { rewriting := rw, cost := estCost cat fanout rw, approx := rw.approx cat }

def keep (cat : Catalog) (req : Requirement) (fanout : Nat) (steps : List Access) :
    Option Ranked :=
  let rw : Rewriting := ⟨steps⟩
  if rw.check cat req && rw.isMinimal cat req then some (rank cat fanout rw) else none

/-- Every minimal rewriting of exact covers with at most `k` accesses. -/
def familyAll (cat : Catalog) (req : Requirement) (k : Nat) (fanout : Nat := 10) : List Ranked :=
  (dfs cat req (candidates cat req) k [] []).filterMap (keep cat req fanout)

/-! ### Irredundancy in any order

`isMinimal` removes one access and keeps the order of the others. A chain
can be minimal in that sense and still hold an access that is redundant
once the others are put in another order: in `[knows(?y,?x),
people(?y,?n), knows(?x,?y)]` the first access binds `?y` for the
lookup, and without it the lookup can run after the last access. Such a
chain is a rewriting (it passes the check, so it is sound) but it adds a
join condition, here that `knows` holds in both directions.

`greedyOrder` puts accesses in an executable order by choosing, at each
step, the first access whose inputs are bound. `irredundant` is true when
no single access can be removed with the rest, in the greedy order,
passing the check. The family keeps its irredundant members when it has
any, and all its members otherwise; so the filter never empties a
non-empty family and no theorem depends on it. That the greedy order
finds an executable order whenever one exists is not proved here. -/

def greedyGo (cat : Catalog) : Nat → List VarName → List Access → List Access →
    Option (List Access)
  | _, _, [], acc => some acc.reverse
  | 0, _, _ :: _, _ => none
  | n + 1, b, pending, acc =>
    match pending.find? (·.executable cat b) with
    | none   => none
    | some a => greedyGo cat n (b ++ a.vars) (pending.erase a) (a :: acc)

def orderable (cat : Catalog) (req : Requirement) (steps : List Access) : Bool :=
  match greedyGo cat steps.length [] steps [] with
  | some o => Rewriting.check cat req ⟨o⟩
  | none   => false

def Rewriting.irredundant (cat : Catalog) (req : Requirement) (rw : Rewriting) : Bool :=
  (List.range rw.steps.length).all (fun i => !orderable cat req (rw.steps.eraseIdx i))

def preferIrredundant (cat : Catalog) (req : Requirement) (fam : List Ranked) : List Ranked :=
  if (fam.filter (fun r => r.rewriting.irredundant cat req)).isEmpty then fam
  else fam.filter (fun r => r.rewriting.irredundant cat req)

/-- The plan family: the irredundant minimal rewritings of exact covers
with at most `k` accesses (all minimal ones when none is irredundant),
ordered by `Ranked.le`. -/
def search (cat : Catalog) (req : Requirement) (k : Nat) (fanout : Nat := 10) : List Ranked :=
  (preferIrredundant cat req (familyAll cat req k fanout)).mergeSort Ranked.le

theorem mem_preferIrredundant {cat : Catalog} {req : Requirement} {fam : List Ranked}
    {r : Ranked} (h : r ∈ preferIrredundant cat req fam) : r ∈ fam := by
  unfold preferIrredundant at h
  split at h
  · exact h
  · exact (List.mem_filter.mp h).1

theorem preferIrredundant_ne_nil {cat : Catalog} {req : Requirement} {fam : List Ranked}
    (h : fam ≠ []) : preferIrredundant cat req fam ≠ [] := by
  unfold preferIrredundant
  split
  · exact h
  · rename_i hne
    intro hnil
    rw [hnil] at hne
    exact hne rfl

/-! ### Admission by quota

Preparation admits a member of the structural family when its estimated
calls and tuples (`statModel`) are within every call quota and row quota
of the catalog. `search` stays the structural family, so `search_complete`
keeps its statement; `searchAdmitted` is the family that the driver
`Planner.Exec` runs. The estimate can be wrong (a statistic that is too
low); the driver enforces both quotas at run time, so I2 does not depend
on it. -/

def admissible (cat : Catalog) (fanout : Nat) (rw : Rewriting) : Bool :=
  withinQuotas cat (estUse cat (statModel fanout) rw.steps) (fun _ => 0) (fun _ => 0)

def searchAdmitted (cat : Catalog) (req : Requirement) (k : Nat) (fanout : Nat := 10) :
    List Ranked :=
  (search cat req k fanout).filter (fun r => admissible cat fanout r.rewriting)

theorem searchAdmitted_mem {cat : Catalog} {req : Requirement} {k fanout : Nat} {r : Ranked}
    (h : r ∈ searchAdmitted cat req k fanout) :
    r ∈ search cat req k fanout ∧ admissible cat fanout r.rewriting = true :=
  List.mem_filter.mp h

/-- The verdict of the structural planner. -/
inductive Verdict where
  | plans (family : List Ranked)
  | notAnswerable

def Verdict.isAnswerable : Verdict → Bool
  | .plans _       => true
  | .notAnswerable => false

def plan (cat : Catalog) (req : Requirement) (k : Nat) (fanout : Nat := 10) : Verdict :=
  match search cat req k fanout with
  | []  => .notAnswerable
  | fam => .plans fam

/-! ## (a) Every returned rewriting is a rewriting -/

theorem search_check {cat : Catalog} {req : Requirement} {k fanout : Nat} {r : Ranked}
    (h : r ∈ search cat req k fanout) : r.rewriting.check cat req = true := by
  unfold search at h
  rw [List.mem_mergeSort] at h
  have h := mem_preferIrredundant h
  unfold familyAll at h
  rw [List.mem_filterMap] at h
  obtain ⟨steps, _, hk⟩ := h
  unfold keep at hk
  by_cases hc : (Rewriting.check cat req ⟨steps⟩ && Rewriting.isMinimal cat req ⟨steps⟩) = true
  · rw [if_pos hc] at hk
    cases hk
    simp only [Bool.and_eq_true] at hc
    exact hc.1
  · rw [if_neg hc] at hk
    cases hk

theorem search_isRewriting {cat : Catalog} {req : Requirement} {k fanout : Nat} {r : Ranked}
    (h : r ∈ search cat req k fanout) : IsRewriting cat req (r.rewriting.toPlan req) :=
  ⟨r.rewriting, search_check h, rfl⟩

/-! ## Lemmas on the chain condition -/

theorem wfBound_chain_isSome (cat : Catalog) :
    ∀ (s : List Access) (b : List VarName),
      ((chainPlan s).wfBound cat b).isSome = chainOk cat b s
  | [], _ => rfl
  | a :: s, b => by
    rw [chainPlan_cons]
    simp only [Plan.wfBound, chainOk, Access.executable]
    cases h : cat[a.src]? with
    | none => simp
    | some src =>
      simp only
      by_cases hc : (decide (a.args.length = src.cap.arity) && a.inputsBound src.cap b) = true
      · rw [if_pos hc, hc, Bool.true_and]
        exact wfBound_chain_isSome cat s (b ++ a.vars)
      · rw [if_neg hc]
        simp only [Bool.not_eq_true] at hc
        rw [hc, Bool.false_and]
        rfl

theorem check_eq (cat : Catalog) (req : Requirement) (steps : List Access) :
    Rewriting.check cat req ⟨steps⟩ =
      (coversAll cat req steps &&
        steps.all (fun a => a.vars.all (fun v => (bgpVars req.bgp).contains v)) &&
        chainOk cat [] steps) := by
  simp only [Rewriting.check, coversAll, wfBound_chain_isSome]

theorem chainOk_append (cat : Catalog) :
    ∀ (p s : List Access) (b : List VarName),
      chainOk cat b (p ++ s) = (chainOk cat b p && chainOk cat (b ++ p.flatMap Access.vars) s)
  | [], s, b => by simp [chainOk]
  | a :: p, s, b => by
    simp only [List.cons_append, chainOk, List.flatMap_cons]
    rw [chainOk_append cat p s (b ++ a.vars), List.append_assoc, Bool.and_assoc]

theorem inputsBound_mono {cap : Capability} {a : Access} {b1 b2 : List VarName}
    (hsub : ∀ v, v ∈ b1 → v ∈ b2) (h : a.inputsBound cap b1 = true) :
    a.inputsBound cap b2 = true := by
  unfold Access.inputsBound at *
  rw [List.all_eq_true] at *
  intro i hi
  have hi1 := h i hi
  revert hi1
  cases a.args[i]? with
  | none => simp
  | some x =>
    cases x with
    | const _ => simp
    | var v =>
      simp only [List.contains_iff_mem]
      exact hsub v

theorem executable_mono {cat : Catalog} {a : Access} {b1 b2 : List VarName}
    (hsub : ∀ v, v ∈ b1 → v ∈ b2) (h : a.executable cat b1 = true) :
    a.executable cat b2 = true := by
  unfold Access.executable at *
  cases hs : cat[a.src]? with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [Bool.and_eq_true] at *
    exact ⟨h.1, inputsBound_mono hsub h.2⟩

theorem chainOk_mono (cat : Catalog) :
    ∀ (s : List Access) {b1 b2 : List VarName}, (∀ v, v ∈ b1 → v ∈ b2) →
      chainOk cat b1 s = true → chainOk cat b2 s = true
  | [], _, _, _, _ => rfl
  | a :: s, b1, b2, hsub, h => by
    simp only [chainOk, Bool.and_eq_true] at *
    refine ⟨executable_mono hsub h.1, chainOk_mono cat s ?_ h.2⟩
    intro v hv
    simp only [List.mem_append] at *
    rcases hv with hv | hv
    · exact Or.inl (hsub v hv)
    · exact Or.inr hv

theorem executable_of_chainOk (cat : Catalog) :
    ∀ (s : List Access) (b : List VarName), chainOk cat b s = true →
      ∀ a ∈ s, ∃ b', a.executable cat b' = true
  | [], _, _, a, ha => by cases ha
  | x :: s, b, h, a, ha => by
    simp only [chainOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, h.1⟩
    · exact executable_of_chainOk cat s _ h.2 a ha

theorem src_of_executable {cat : Catalog} {a : Access} {b : List VarName}
    (h : a.executable cat b = true) :
    ∃ s, cat[a.src]? = some s ∧ a.args.length = s.cap.arity := by
  unfold Access.executable at h
  cases hs : cat[a.src]? with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨s, rfl, h.1⟩

/-! ## Candidates -/

theorem mem_argLists (pool : List Arg) :
    ∀ (args : List Arg), (∀ x ∈ args, x ∈ pool) → args ∈ argLists pool args.length
  | [], _ => by simp [argLists]
  | x :: rest, h => by
    simp only [List.length_cons, argLists, List.mem_flatMap, List.mem_map]
    refine ⟨rest, mem_argLists pool rest (fun y hy => h y (List.mem_cons_of_mem x hy)), x,
      h x List.mem_cons_self, rfl⟩

theorem mem_candidates {cat : Catalog} {req : Requirement} {a : Access} {s : Source}
    (hs : cat[a.src]? = some s) (hlen : a.args.length = s.cap.arity)
    (hp : ∀ x ∈ a.args, x ∈ req.pool) (hex : a.exactCover cat req = true) :
    a ∈ candidates cat req := by
  unfold candidates
  rw [List.mem_filter]
  refine ⟨?_, hex⟩
  rw [List.mem_flatMap]
  have hlt : a.src < cat.length := by
    rcases List.getElem?_eq_some_iff.mp hs with ⟨h, _⟩
    exact h
  refine ⟨a.src, List.mem_range.mpr hlt, ?_⟩
  rw [hs]
  rw [List.mem_map]
  refine ⟨a.args, ?_, rfl⟩
  rw [← hlen]
  exact mem_argLists req.pool a.args hp

/-! ## Exact covers use only pool arguments -/

theorem mem_pool_var {req : Requirement} {v : VarName} (h : v ∈ bgpVars req.bgp) :
    Arg.var v ∈ req.pool := by
  unfold Requirement.pool
  simp [List.mem_eraseDups, h]

theorem mem_pool_const {req : Requirement} {c : Term} (h : c ∈ bgpConsts req.bgp) :
    Arg.const c ∈ req.pool := by
  unfold Requirement.pool
  simp [List.mem_eraseDups, h]

theorem termOfPatternTerm_of {c : Term} {pt : PatternTerm} (h : patternTermOfTerm c = some pt) :
    termOfPatternTerm pt = some c := by
  cases c <;> simp [patternTermOfTerm] at h <;> subst h <;> rfl

theorem termOfPatternSubject_of {c : Term} {ps : PatternSubject}
    (h : patternSubjectOfTerm c = some ps) : termOfPatternSubject ps = some c := by
  cases c <;> simp [patternSubjectOfTerm] at h <;> subst h <;> rfl

theorem subst_some {args : List Arg} {tm : TripleTemplate} {tp : TriplePattern}
    (h : tm.subst args = some tp) :
    tm.s.patternSubject args = some tp.s ∧ tm.p.patternTerm args = some tp.p ∧
      tm.o.patternTerm args = some tp.o := by
  unfold TripleTemplate.subst at h
  split at h
  · rename_i s p o hs hp ho
    cases h
    exact ⟨hs, hp, ho⟩
  · cases h

theorem mem_bgpVars {b : Bgp} {tp : TriplePattern} {v : VarName} (htp : tp ∈ b)
    (hv : v ∈ tpVars tp) : v ∈ bgpVars b := by
  unfold bgpVars
  exact List.mem_flatMap.mpr ⟨tp, htp, hv⟩

theorem mem_bgpConsts {b : Bgp} {tp : TriplePattern} {c : Term} (htp : tp ∈ b)
    (hc : c ∈ tpConsts tp) : c ∈ bgpConsts b := by
  unfold bgpConsts
  exact List.mem_flatMap.mpr ⟨tp, htp, hc⟩

theorem pool_of_term_slot {req : Requirement} {tp : TriplePattern} (htp : tp ∈ req.bgp)
    {args : List Arg} {i : Nat} {x : Arg} {pt : PatternTerm}
    (hx : args[i]? = some x) (h : Slot.patternTerm args (.arg i) = some pt)
    (hpt : pt = tp.p ∨ pt = tp.o) : x ∈ req.pool := by
  simp only [Slot.patternTerm, hx] at h
  cases x with
  | var v =>
    cases h
    apply mem_pool_var
    apply mem_bgpVars htp
    unfold tpVars
    rcases hpt with hpt | hpt <;> simp [← hpt, termVars]
  | const c =>
    apply mem_pool_const
    apply mem_bgpConsts htp
    have := termOfPatternTerm_of h
    unfold tpConsts
    rcases hpt with hpt | hpt <;> rw [← hpt] <;> simp [this]

theorem pool_of_subject_slot {req : Requirement} {tp : TriplePattern} (htp : tp ∈ req.bgp)
    {args : List Arg} {i : Nat} {x : Arg}
    (hx : args[i]? = some x) (h : Slot.patternSubject args (.arg i) = some tp.s) :
    x ∈ req.pool := by
  simp only [Slot.patternSubject, hx] at h
  cases x with
  | var v =>
    apply mem_pool_var
    apply mem_bgpVars htp
    unfold tpVars
    simp at h
    simp [← h, subjectVars]
  | const c =>
    apply mem_pool_const
    apply mem_bgpConsts htp
    have := termOfPatternSubject_of h
    unfold tpConsts
    simp [this]

/-- Every argument of an exact cover is a variable or a constant of the
requirement. -/
theorem args_mem_pool_of_exactCover {cat : Catalog} {req : Requirement} {a : Access}
    (h : a.exactCover cat req = true) : ∀ x ∈ a.args, x ∈ req.pool := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hx' : a.args[i]? = some x := by rw [List.getElem?_eq_getElem hi, hix]
  unfold Access.exactCover at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨tm, htm, hpos⟩ := h.2 i hi
  unfold Access.coveringTemplates at htm
  cases hs : cat[a.src]? with
  | none => rw [hs] at htm; cases htm
  | some s =>
    rw [hs] at htm
    simp only [List.mem_filter] at htm
    obtain ⟨_, hsub⟩ := htm
    cases hsb : tm.subst a.args with
    | none => rw [hsb] at hsub; cases hsub
    | some tp =>
      rw [hsb] at hsub
      have htp : tp ∈ req.bgp := by simpa using hsub
      obtain ⟨h1, h2, h3⟩ := subst_some hsb
      simp only [TripleTemplate.argPositions, List.contains_iff_mem, List.mem_append,
        Option.mem_toList] at hpos
      rcases hpos with (hpos | hpos) | hpos
      · cases hts : tm.s with
        | const _ => rw [hts] at hpos; simp [Slot.argPos] at hpos
        | arg j =>
          rw [hts] at hpos h1
          simp [Slot.argPos] at hpos
          subst hpos
          exact pool_of_subject_slot htp hx' h1
      · cases htp' : tm.p with
        | const _ => rw [htp'] at hpos; simp [Slot.argPos] at hpos
        | arg j =>
          rw [htp'] at hpos h2
          simp [Slot.argPos] at hpos
          subst hpos
          exact pool_of_term_slot htp hx' h2 (Or.inl rfl)
      · cases hto : tm.o with
        | const _ => rw [hto] at hpos; simp [Slot.argPos] at hpos
        | arg j =>
          rw [hto] at hpos h3
          simp [Slot.argPos] at hpos
          subst hpos
          exact pool_of_term_slot htp hx' h3 (Or.inr rfl)

/-! ## Minimal rewritings -/

theorem exists_minimal (cat : Catalog) (req : Requirement) (P : Access → Prop) :
    ∀ (n : Nat) (steps : List Access), steps.length ≤ n →
      Rewriting.check cat req ⟨steps⟩ = true → (∀ a ∈ steps, P a) →
      ∃ st : List Access, Rewriting.check cat req ⟨st⟩ = true ∧
        Rewriting.isMinimal cat req ⟨st⟩ = true ∧ st.length ≤ steps.length ∧ (∀ a ∈ st, P a)
  | n, steps, hn, hc, hp => by
    by_cases hm : Rewriting.isMinimal cat req ⟨steps⟩ = true
    · exact ⟨steps, hc, hm, Nat.le_refl _, hp⟩
    · have hex : ∃ i, i < steps.length ∧ Rewriting.check cat req ⟨steps.eraseIdx i⟩ = true := by
        simp only [Rewriting.isMinimal, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hm
        exact Classical.byContradiction (fun hne => hm (fun x hx => by
          cases hcx : Rewriting.check cat req ⟨steps.eraseIdx x⟩ with
          | false => rfl
          | true => exact absurd ⟨x, hx, hcx⟩ hne))
      obtain ⟨i, hi, hci⟩ := hex
      have hlen : (steps.eraseIdx i).length + 1 = steps.length := by
        rw [List.length_eraseIdx]; simp [hi]; omega
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨st, h1, h2, h3, h4⟩ := exists_minimal cat req P n (steps.eraseIdx i) (by omega) hci
          (fun a ha => hp a ((List.eraseIdx_sublist steps i).subset ha))
        exact ⟨st, h1, h2, by omega, h4⟩

theorem not_minimal_of_check {cat : Catalog} {req : Requirement} {whole : List Access} {i : Nat}
    (hi : i < whole.length) (hc : Rewriting.check cat req ⟨whole.eraseIdx i⟩ = true) :
    Rewriting.isMinimal cat req ⟨whole⟩ = false := by
  simp only [Rewriting.isMinimal]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  simp [hc] at this

theorem any_covers_append {cat : Catalog} {tp : TriplePattern} {p s : List Access} :
    (p ++ s).any (fun a => a.covers cat tp) =
      (p.any (fun a => a.covers cat tp) || s.any (fun a => a.covers cat tp)) := by
  simp [List.any_append]

/-- A proper prefix that covers the requirement makes a checked chain
not minimal: drop the last access. -/
theorem not_minimal_of_prefix_covers {cat : Catalog} {req : Requirement} {p s : List Access}
    (hs : s ≠ []) (hc : Rewriting.check cat req ⟨p ++ s⟩ = true)
    (hcov : coversAll cat req p = true) :
    Rewriting.isMinimal cat req ⟨p ++ s⟩ = false := by
  obtain ⟨q, z, rfl⟩ : ∃ q z, s = q ++ [z] := by
    rcases List.eq_nil_or_concat s with h | ⟨q, z, h⟩
    · exact absurd h hs
    · exact ⟨q, z, by simpa using h⟩
  have hwhole : p ++ (q ++ [z]) = (p ++ q) ++ z :: [] := by simp
  rw [hwhole] at hc ⊢
  apply not_minimal_of_check (i := (p ++ q).length) (by simp)
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp only [Nat.sub_self, List.eraseIdx_cons_zero, List.append_nil]
  rw [check_eq] at hc ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, List.all_append, List.any_append,
    coversAll] at hc hcov ⊢
  obtain ⟨⟨_, hv⟩, hw⟩ := hc
  refine ⟨⟨?_, hv.1⟩, ?_⟩
  · intro tp htp
    have := hcov tp htp
    simp [this]
  · rw [chainOk_append] at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1

/-- The main search lemma: every minimal checked chain whose accesses are
candidates is produced by `dfs`, from each of its prefixes. -/
theorem mem_dfs_of_minimal (cat : Catalog) (req : Requirement) (cands : List Access)
    (whole : List Access)
    (hchk : Rewriting.check cat req ⟨whole⟩ = true)
    (hmin : Rewriting.isMinimal cat req ⟨whole⟩ = true)
    (hcand : ∀ a ∈ whole, a ∈ cands) :
    ∀ (s p : List Access) (fuel : Nat), whole = p ++ s → s.length ≤ fuel →
      whole ∈ dfs cat req cands fuel p (p.flatMap Access.vars)
  | [], p, fuel, hw, _ => by
    have hcov : coversAll cat req p = true := by
      rw [check_eq] at hchk
      simp only [Bool.and_eq_true] at hchk
      rw [hw, List.append_nil] at hchk
      exact hchk.1.1
    rw [hw, List.append_nil]
    cases fuel with
    | zero => simp [dfs, hcov]
    | succ n => simp [dfs, hcov]
  | a :: s', p, fuel, hw, hlen => by
    cases fuel with
    | zero => simp at hlen
    | succ n =>
      have hncov : coversAll cat req p = false := by
        rw [Bool.eq_false_iff]
        intro hcov
        have := not_minimal_of_prefix_covers (s := a :: s') (by simp) (hw ▸ hchk) hcov
        rw [← hw, hmin] at this
        cases this
      have hparts := hchk
      rw [check_eq] at hparts
      simp only [Bool.and_eq_true] at hparts
      obtain ⟨⟨hcovW, hvarsW⟩, hwfW⟩ := hparts
      rw [hw, chainOk_append] at hwfW
      simp only [Bool.and_eq_true, chainOk, List.nil_append] at hwfW
      obtain ⟨hwfP, hexA, hwfS⟩ := hwfW
      have huse : a.useful cat req (p.flatMap Access.vars) p = true := by
        rw [← Bool.not_eq_false]
        intro hnot
        simp only [Access.useful, Bool.or_eq_false_iff, List.any_eq_false,
          Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and,
          Bool.not_eq_false] at hnot
        obtain ⟨hvs, hcv⟩ := hnot
        -- Removing `a` keeps the check.
        have hrem : Rewriting.check cat req ⟨p ++ s'⟩ = true := by
          rw [check_eq]
          simp only [Bool.and_eq_true]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · simp only [coversAll, List.all_eq_true] at hcovW ⊢
            intro tp htp
            have h1 := hcovW tp htp
            rw [hw] at h1
            simp only [List.any_append, List.any_cons, Bool.or_eq_true] at h1 ⊢
            rcases h1 with h1 | h1 | h1
            · exact Or.inl h1
            · exact Or.inl (by
                have := hcv tp htp h1
                simpa using this)
            · exact Or.inr h1
          · rw [List.all_eq_true] at hvarsW ⊢
            intro x hx
            apply hvarsW x
            rw [hw]
            simp only [List.mem_append, List.mem_cons] at hx ⊢
            rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
          · rw [chainOk_append]
            simp only [Bool.and_eq_true, List.nil_append]
            refine ⟨hwfP, chainOk_mono cat s' ?_ hwfS⟩
            intro v hv
            simp only [List.mem_append] at hv
            rcases hv with hv | hv
            · exact hv
            · have := hvs v hv
              simpa [List.contains_iff_mem] using this
        have hlt : p.length < whole.length := by rw [hw]; simp
        have hnm := not_minimal_of_check hlt (by
          rw [hw, List.eraseIdx_append_of_length_le (Nat.le_refl _)]
          simpa using hrem)
        rw [hmin] at hnm
        cases hnm
      have ih := mem_dfs_of_minimal cat req cands whole hchk hmin hcand s' (p ++ [a]) n
        (by rw [hw]; simp) (by simp at hlen; omega)
      rw [List.flatMap_append, List.flatMap_singleton] at ih
      simp only [dfs, hncov, Bool.false_eq_true, if_false]
      rw [List.mem_flatMap]
      refine ⟨a, hcand a (by rw [hw]; simp), ?_⟩
      rw [if_pos (by simp [hexA, huse])]
      exact ih

/-! ## (b) Completeness relative to the exact covers -/

/-- Every minimal checked rewriting of exact covers with at most `k`
accesses is a member of `familyAll`. -/
theorem search_mem_of_minimal {cat : Catalog} {req : Requirement} {k fanout : Nat}
    {rw : Rewriting} (hchk : rw.check cat req = true) (hmin : rw.isMinimal cat req = true)
    (hk : rw.steps.length ≤ k) (hcov : rw.ExactCovers cat req) :
    rank cat fanout rw ∈ familyAll cat req k fanout := by
  have hcand : ∀ a ∈ rw.steps, a ∈ candidates cat req := by
    intro a ha
    have hw := hchk
    rw [show rw = ⟨rw.steps⟩ from rfl, check_eq] at hw
    simp only [Bool.and_eq_true] at hw
    obtain ⟨b', hb'⟩ := executable_of_chainOk cat rw.steps [] hw.2 a ha
    obtain ⟨s, hs, hlen⟩ := src_of_executable hb'
    exact mem_candidates hs hlen (args_mem_pool_of_exactCover (hcov a ha)) (hcov a ha)
  have hd := mem_dfs_of_minimal cat req (candidates cat req) rw.steps hchk hmin hcand
    rw.steps [] k (by simp) hk
  unfold familyAll
  rw [List.mem_filterMap]
  refine ⟨rw.steps, by simpa using hd, ?_⟩
  unfold keep
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hchk, hmin⟩)]

/-- Completeness of the search relative to the exact covers: when some
rewriting with at most `k` accesses, each an exact cover, passes
`Rewriting.check`, the search returns a rewriting. -/
theorem search_complete {cat : Catalog} {req : Requirement} {k fanout : Nat}
    {rw : Rewriting} (hchk : rw.check cat req = true) (hk : rw.steps.length ≤ k)
    (hcov : rw.ExactCovers cat req) : search cat req k fanout ≠ [] := by
  obtain ⟨st, h1, h2, h3, h4⟩ :=
    exists_minimal cat req (fun a => a.exactCover cat req = true) rw.steps.length rw.steps
      (Nat.le_refl _) hchk hcov
  have hm := search_mem_of_minimal (rw := ⟨st⟩) (k := k) (fanout := fanout) h1 h2
    (by simp; omega) h4
  have hfam : familyAll cat req k fanout ≠ [] := by
    intro hnil
    rw [hnil] at hm
    cases hm
  have hpref := preferIrredundant_ne_nil (cat := cat) (req := req) hfam
  unfold search
  intro hnil
  have hlen := (List.mergeSort_perm (preferIrredundant cat req (familyAll cat req k fanout))
    Ranked.le).length_eq
  rw [hnil] at hlen
  exact hpref (List.eq_nil_of_length_eq_zero hlen.symm)

/-- The verdict "not answerable" is correct relative to the exact covers:
no rewriting of exact covers with at most `k` accesses passes the check. -/
theorem plan_notAnswerable_sound {cat : Catalog} {req : Requirement} {k fanout : Nat}
    (h : plan cat req k fanout = .notAnswerable) :
    ∀ rw : Rewriting, rw.steps.length ≤ k → rw.ExactCovers cat req → rw.check cat req = false := by
  intro rw hk hp
  rw [Bool.eq_false_iff]
  intro hc
  have hne := search_complete (fanout := fanout) hc hk hp
  unfold plan at h
  split at h
  · exact hne (by assumption)
  · cases h

/-- Each plan of the family is sound: under sound exact sources, every
unmarked row it returns is an answer of the requirement over the
declared graph. -/
theorem search_sound {cat : Catalog} {req : Requirement} {k fanout : Nat} {r : Ranked}
    (hsound : ∀ s ∈ cat, s.cap.exactness = .exact → s.sem.Sound)
    (h : r ∈ search cat req k fanout) :
    ∀ x ∈ (r.rewriting.toPlan req).run cat, x.approx = false →
      ∃ ρ ∈ req.answers (declaredGraph cat), SolEquiv x.binding ρ :=
  rewriting_sound hsound (search_isRewriting h)

end L4Factoidal.Planner
