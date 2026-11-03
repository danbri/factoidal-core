/-
L4Factoidal.RIF.Prd — RIF Production Rule Dialect, Second Edition
(W3C Recommendation 2013-02-05, https://www.w3.org/TR/2013/REC-rif-prd-20130205/),
as a layer over the RIF Core engine.

Reused from RIF Core (`RIF/Engine.lean`): the term and atom AST
(`RIF/Syntax.lean`), the matcher `matchFormula` with its built-ins
(`RIF/Builtins.lean`) and value identity (`groundMatch`), grounding
`groundTm`, and the fact representation `GAtom`. This module adds what PRD
has and Core has not:

* conditions with `Not` (inflationary negation, §2.1.2 and §2.2.1:
  "σ matches Not(f) to Φ iff σ does not match f to Φ");
* the membership rule of §2.2.1: `o # c` matches when `o # c` is a fact, or
  when `o # c'` and `c' ## c` are facts for some `c'`;
* actions (§3.1.1): Assert, Retract of a fact, Retract(o s) of all slot
  values, Retract(o) of an object, Modify, Execute, with the compound forms
  expanded as §3.1.1 defines them;
* action blocks with action variables, `New()` and frame slot values
  (§3.1.2, §4.2.3 "Action instance");
* the operational semantics of §4.2: system states, conflict sets, and the
  `rif:forwardChaining` strategy (§4.2.5): refraction, priority, recency,
  tie-break, with recency and lastPicked counted over cycle AND
  transitional states as §4.2.5 defines them;
* the halting test of §4.2.6.

Tie-break (§4.2.5 leaves it to the implementation): the first remaining
instance in rule order (document order), then in the order the matcher
returns substitutions.

A RIF Core rule `Forall ?x (h :- b)` is the PRD rule
`Forall ?x (If b Then Do(Assert(h)))` (`ofCoreRule`); a Core fact is a fact
of the initial state. That is how the shared Core cases of the W3C PRD
manifest run here.
-/
import L4Factoidal.RIF.Engine
import Std.Data.HashMap

namespace L4Factoidal.RIF.Prd

open L4Factoidal.RIF

/-! ## Syntax (§2.1, §3.1) -/

/-- A PRD condition formula (§2.1.2). `core` holds a RIF Core formula, so
the Core matcher evaluates it unchanged; the other constructors are the
PRD connectives over conditions that contain `Not`. -/
inductive Cond where
  | core   (f : Formula)
  | and    (cs : List Cond)
  | or     (cs : List Cond)
  | not    (c : Cond)
  | exists (vars : List String) (c : Cond)
deriving Repr, Inhabited

/-- An atomic action (§3.1.1). Compound actions (a multi-slot Assert or
Retract, Modify) are expanded by the reader into these. -/
inductive Action where
  /-- `Assert(φ)`: φ a positional atom, a single-slot frame or a membership. -/
  | assert      (a : Atom)
  /-- `Retract(φ)`: φ a positional atom or a single-slot frame. -/
  | retract     (a : Atom)
  /-- `Retract(o s)`: every value of slot `s` of object `o`. -/
  | retractSlot (o s : Tm)
  /-- `Retract(o)`: every frame with object `o` and every `o # c`. -/
  | retractObj  (o : Tm)
  /-- `Execute(φ)`: φ an atom naming a built-in action. -/
  | execute     (fn : String) (args : List Tm)
deriving Repr, Inhabited

/-- An action variable binding (§3.1.2). -/
inductive Binding where
  /-- `(?v New())`. -/
  | new
  /-- `(?v o[s->?v])`: the value of slot `s` of the ground frame `o`. -/
  | slot (o s : Tm)
deriving Repr, Inhabited

/-- A production rule: its rule variables, its condition (`none` for an
unconditional action block), the action variable declarations and the
atomic actions of its action block, and its priority (§4.2.5, the
innermost Group that states one, else 0). -/
structure PRule where
  vars     : List String := []
  cond     : Option Cond := none
  actVars  : List (String × Binding) := []
  actions  : List Action := []
  priority : Int := 0
deriving Repr, Inhabited

/-- A PRD document after reading: the initial facts, the rules, and the
imports (location, profile). -/
structure Doc where
  facts   : List GAtom := []
  rules   : List PRule := []
  imports : List (String × Option String) := []
deriving Repr, Inhabited

/-- `Modify(o[s1->v1 … sn->vn])` is `Retract(o s1) … Retract(o sn)` then
`Assert(o[s1->v1]) … Assert(o[sn->vn])` (§3.1.1, "Modify fact"). The
argument is the list of single-slot frames of the target. -/
def modifyActions (slots : List Atom) : List Action :=
  slots.filterMap (fun a => match a with
    | .frame o s _ => some (Action.retractSlot o s)
    | _ => none) ++ slots.map Action.assert

/-- The embedding of a RIF Core rule: `Forall ?x (h :- b)` is
`Forall ?x (If b Then Do(Assert(h)))`. -/
def ofCoreRule (r : Rule) : PRule :=
  { vars := r.vars, cond := r.body.map Cond.core, actions := [.assert r.head] }

/-- The action is an `Assert`. -/
def Action.isAssert : Action → Bool
  | .assert _ => true
  | _ => false

/-! ## Local constants are document-scoped

As in RIF Core (`Engine.qualifyTm`): a `rif:local` constant of one document
is a different symbol from the same name in another. The RIF/XML reader
(`RIF/Xml.lean`) writes such a constant as the IRI `urn:rif-local:name`;
the presentation-syntax reader keeps the `rif:local` space. Both are
qualified with the document. -/

def localIriPrefix : String := "urn:rif-local:"

def qualifyLocalTm (tag : String) : Tm → Tm
  | .const l sp =>
      if sp == iriSpace && l.startsWith localIriPrefix then
        .const (localIriPrefix ++ tag ++ "#" ++ (l.drop localIriPrefix.length).toString) sp
      else qualifyTm tag (.const l sp)
  | .var v => .var v
  | .list xs => .list (xs.attach.map (fun ⟨x, _⟩ => qualifyLocalTm tag x))
  | .fapp f sp xs =>
      .fapp (if sp == localSpace then tag ++ "#" ++ f else f) sp
        (xs.attach.map (fun ⟨x, _⟩ => qualifyLocalTm tag x))
  | .external f xs => .external f (xs.attach.map (fun ⟨x, _⟩ => qualifyLocalTm tag x))

def qualifyLocalAtom (tag : String) : Atom → Atom
  | .pos f sp args =>
      .pos (if sp == localSpace then tag ++ "#" ++ f else f) sp (args.map (qualifyLocalTm tag))
  | .frame o p v => .frame (qualifyLocalTm tag o) (qualifyLocalTm tag p) (qualifyLocalTm tag v)
  | .member o c => .member (qualifyLocalTm tag o) (qualifyLocalTm tag c)
  | .sub c d => .sub (qualifyLocalTm tag c) (qualifyLocalTm tag d)
  | .equal a b => .equal (qualifyLocalTm tag a) (qualifyLocalTm tag b)
  | .externalPred f a => .externalPred f (a.map (qualifyLocalTm tag))

def qualifyLocalFormula (tag : String) : Formula → Formula
  | .atom a => .atom (qualifyLocalAtom tag a)
  | .and fs => .and (fs.attach.map (fun ⟨f, _⟩ => qualifyLocalFormula tag f))
  | .or fs => .or (fs.attach.map (fun ⟨f, _⟩ => qualifyLocalFormula tag f))
  | .exists vs f => .exists vs (qualifyLocalFormula tag f)

def qualifyCond (tag : String) : Cond → Cond
  | .core f => .core (qualifyLocalFormula tag f)
  | .and cs => .and (cs.attach.map (fun ⟨c, _⟩ => qualifyCond tag c))
  | .or cs => .or (cs.attach.map (fun ⟨c, _⟩ => qualifyCond tag c))
  | .not c => .not (qualifyCond tag c)
  | .exists vs c => .exists vs (qualifyCond tag c)

def qualifyAction (tag : String) : Action → Action
  | .assert a => .assert (qualifyLocalAtom tag a)
  | .retract a => .retract (qualifyLocalAtom tag a)
  | .retractSlot o s => .retractSlot (qualifyLocalTm tag o) (qualifyLocalTm tag s)
  | .retractObj o => .retractObj (qualifyLocalTm tag o)
  | .execute fn args => .execute fn (args.map (qualifyLocalTm tag))

def qualifyPRule (tag : String) (r : PRule) : PRule :=
  { r with cond := r.cond.map (qualifyCond tag),
           actVars := r.actVars.map (fun (v, b) => (v, match b with
             | .new => .new
             | .slot o s => .slot (qualifyLocalTm tag o) (qualifyLocalTm tag s))),
           actions := r.actions.map (qualifyAction tag) }

/-! ## Satisfaction of a condition (§2.2.1) -/

/-- The variable name for `c'` in the membership rule. It contains `#`,
which no RIF variable name contains. -/
def memberMidVar : String := "rif-prd#c'"

/-- `o # c` under the membership rule of §2.2.1: the fact itself, or
`o # c'` and `c' ## c`. -/
def matchMember (facts : Facts) (s : Subst) (o c : Tm) : List Subst × Bool :=
  let (direct, b1) := matchAtom facts s (.member o c)
  let (viaSub, b2) := matchFormula facts s
    (.exists [memberMidVar]
      (.and [.atom (.member o (.var memberMidVar)), .atom (.sub (.var memberMidVar) c)]))
  (direct ++ viaSub, b1 || b2)

/-- Rewrite a Core formula so that each membership atom uses the PRD
membership rule. The rewrite is to a disjunction, so the Core matcher
evaluates it. -/
def withMemberRule : Formula → Formula
  | .atom (.member o c) =>
      .or [.atom (.member o c),
           .exists [memberMidVar]
             (.and [.atom (.member o (.var memberMidVar)), .atom (.sub (.var memberMidVar) c)])]
  | .atom a => .atom a
  | .and fs => .and (fs.map withMemberRule)
  | .or fs => .or (fs.map withMemberRule)
  | .exists vs f => .exists vs (withMemberRule f)

/-- Deduplicate substitutions (the membership disjunction can give the same
substitution twice). -/
def dedupSubsts (ss : List Subst) : List Subst :=
  ss.foldl (fun acc s => if acc.any (fun t => t == s) then acc else acc ++ [s]) []

/-- Every substitution extending `s` that matches the condition to the
facts, and whether a built-in blocked evaluation. In an `And`, the Core
conjuncts are matched first as one Core conjunction (so the Core
evaluation order of built-ins and equalities applies), then the other
conjuncts in the order written. -/
def matchCond (facts : Facts) (s : Subst) : Cond → List Subst × Bool
  | .core f => let (ss, b) := matchFormula facts s (withMemberRule f); (dedupSubsts ss, b)
  | .not c =>
      let (ss, b) := matchCond facts s c
      (if ss.isEmpty then [s] else [], b)
  | .and cs =>
      let coreFs : List Formula := cs.filterMap (fun c => match c with
        | .core f => some f
        | _ => none)
      let (ss0, b0) := matchFormula facts s (withMemberRule (.and coreFs))
      cs.foldl (fun (acc, b) c =>
        match c with
        | .core _ => (acc, b)
        | _ =>
          let rs := acc.map (fun s' => matchCond facts s' c)
          (dedupSubsts (rs.flatMap (·.1)), b || rs.any (·.2))) (dedupSubsts ss0, b0)
  | .or cs =>
      let rs := cs.map (fun c => matchCond facts s c)
      (dedupSubsts (rs.flatMap (·.1)), rs.any (·.2))
  | .exists vs c =>
      let (ss, b) := matchCond facts s c
      (dedupSubsts (ss.map (fun s' => s'.filter (fun (k, _) => !(vs.contains k)))), b)

/-- The free variables of a condition that matching binds, in order of
first occurrence. A variable under `Not` is never bound by matching
(§2.2.1), so it is not counted. -/
def condVars : Cond → List String
  | .core f => varsOfFormula f
  | .not _ => []
  | .and cs => cs.flatMap condVars
  | .or cs => cs.flatMap condVars
  | .exists vs c => (condVars c).filter (fun v => !(vs.contains v))

/-! ## Rule instances and conflict sets (§4.2.3) -/

deriving instance Hashable for GTerm

/-- A rule instance: the index of its rule and the constants its
substitution gives the rule variables, in the order of `instVars`. Two
instances of one rule differ iff one of these constants differs (§4.2.3). -/
structure Inst where
  rule : Nat
  vals : List GTerm
deriving Repr, DecidableEq, Hashable, Inhabited

/-- The rule variables of `r`: its declared variables, then any other free
variable of its condition. -/
def instVars (r : PRule) : List String :=
  (r.vars ++ (match r.cond with | some c => condVars c | none => [])).eraseDups

/-- The instances of rule number `i` that match the facts, each with its
substitution, and whether a built-in blocked evaluation. An instance
needs a constant for every rule variable; a substitution that leaves one
unbound is reported as blocked. -/
def ruleInstances (facts : Facts) (i : Nat) (r : PRule) : List (Inst × Subst) × Bool :=
  let (ss, b) := match r.cond with
    | none => ([[]], false)
    | some c => matchCond facts [] c
  let vs := instVars r
  ss.foldl (fun (acc, blk) s =>
    match vs.mapM (lookupVar s) with
    | some vals =>
        let inst : Inst := { rule := i, vals := vals }
        if acc.any (fun (j, _) => j == inst) then (acc, blk) else (acc ++ [(inst, s)], blk)
    | none => (acc, true)) ([], b)

/-- The conflict set (§4.2.3, "Conflict set"): every instance of every rule
that matches the facts, in rule order. -/
def conflictSet (rules : List PRule) (facts : Facts) : List (Inst × Subst) × Bool :=
  (rules.zipIdx.map (fun (r, i) => ruleInstances facts i r)).foldl
    (fun (acc, b) (xs, b2) => (acc ++ xs, b || b2)) ([], false)

/-! ## Ground atomic actions (§3.2) -/

/-- Value identity of two ground atoms of the same kind: each argument
denotes the same value (`groundMatch`). -/
def gAtomSame : GAtom → GAtom → Bool
  | .pos f1 s1 a1, .pos f2 s2 a2 =>
      f1 == f2 && s1 == s2 && a1.length == a2.length &&
        (a1.zip a2).all (fun (x, y) => gEqValue x y)
  | .frame o1 p1 v1, .frame o2 p2 v2 => gEqValue o1 o2 && gEqValue p1 p2 && gEqValue v1 v2
  | .member o1 c1, .member o2 c2 => gEqValue o1 o2 && gEqValue c1 c2
  | .sub c1 d1, .sub c2 d2 => gEqValue c1 c2 && gEqValue d1 d2
  | _, _ => false

/-- A ground atomic action (§3.2). -/
inductive GAction where
  | assert      (f : GAtom)
  | retract     (f : GAtom)
  | retractSlot (o s : GTerm)
  | retractObj  (o : GTerm)
  | execute     (fn : String) (args : List GTerm)
deriving Repr, DecidableEq, Inhabited

/-- The built-in actions this engine executes (§6.1). `act:print` has no
effect on the fact base (§3.2, rule 5). -/
def actNs : String := "http://www.w3.org/2007/rif-builtin-action#"
def knownAction (fn : String) : Bool := fn == actNs ++ "print"

/-- The RIF-PRD transition relation (§3.2), as a function. -/
def applyGAction (facts : Facts) : GAction → Facts
  | .assert f => if facts.contains f then facts else facts ++ [f]
  | .retract f => facts.filter (fun g => !gAtomSame g f)
  | .retractSlot o s => facts.filter (fun g => match g with
      | .frame o2 s2 _ => !(gEqValue o2 o && gEqValue s2 s)
      | _ => true)
  | .retractObj o => facts.filter (fun g => match g with
      | .frame o2 _ _ => !gEqValue o2 o
      | .member o2 _ => !gEqValue o2 o
      | _ => true)
  | .execute _ _ => facts

/-- Ground a term list, threading the blocked flag. -/
def groundTms (s : Subst) (ts : List Tm) : Option (List GTerm) × Bool :=
  let rs := ts.map (groundTm s)
  (rs.mapM (·.1), rs.any (·.2))

/-- The ground atomic action of an atomic action under a substitution;
`none` when a term does not ground or the action is not well-formed. -/
def groundAction (s : Subst) : Action → Option GAction × Bool
  | .assert a =>
      match a with
      | .equal _ _ | .externalPred _ _ | .sub _ _ => (none, true)
      | _ => let (f, b) := instantiate s a; (f.map GAction.assert, b)
  | .retract a =>
      match a with
      | .pos _ _ _ | .frame _ _ _ => let (f, b) := instantiate s a; (f.map GAction.retract, b)
      | _ => (none, true)
  | .retractSlot o sl =>
      match groundTm s o, groundTm s sl with
      | (some o', b1), (some s', b2) => (some (.retractSlot o' s'), b1 || b2)
      | (_, b1), (_, b2) => (none, b1 || b2)
  | .retractObj o =>
      match groundTm s o with
      | (some o', b) => (some (.retractObj o'), b)
      | (none, b) => (none, b)
  | .execute fn args =>
      if knownAction fn then
        let (gs, b) := groundTms s args
        (gs.map (GAction.execute fn), b)
      else (none, true)

/-- A constant that occurs in no fact (§4.2.3, `New()`): the first
`urn:rif-prd:new:k` not in the facts, from a counter. -/
def freshConst (facts : Facts) (k : Nat) : GTerm × Nat :=
  let occurs := fun (t : GTerm) => facts.any (fun f => match f with
    | .pos _ _ args => args.contains t
    | .frame o p v => o == t || p == t || v == t
    | .member o c => o == t || c == t
    | .sub c d => c == t || d == t)
  let rec go : Nat → Nat → GTerm × Nat
    | 0, j => (gIri s!"urn:rif-prd:new:{j}", j + 1)
    | n + 1, j =>
        let c := gIri s!"urn:rif-prd:new:{j}"
        if occurs c then go n (j + 1) else (c, j + 1)
  go (facts.length + 1) k

/-- Extend the instance substitution to the action variables (§4.2.3,
"Action instance"). A slot binding with no matching value has no
semantics in RIF-PRD (same section); it is reported as blocked. -/
def bindActVars (facts : Facts) (s : Subst) (k : Nat) :
    List (String × Binding) → Option Subst × Nat × Bool
  | [] => (some s, k, false)
  | (v, .new) :: rest =>
      let (c, k') := freshConst facts k
      bindActVars facts ((v, c) :: s) k' rest
  | (v, .slot o sl) :: rest =>
      match (matchAtom facts s (.frame o sl (.var v))).1 with
      | s' :: _ => bindActVars facts s' k rest
      | [] => (none, k, true)

/-! ## System states and rif:forwardChaining (§4.2.4 to §4.2.6) -/

/-- What §4.2.5 needs about an instance in the conflict set of the current
system state: `recency` (states it has been continuously in the conflict
set, this one included) and `lastPicked` (states since it was last fired;
`none` if it has not been fired since it entered the conflict set, which
makes it never refracted, because then lastPicked ≥ recency). -/
structure Hist where
  inst       : Inst
  recency    : Nat
  lastPicked : Option Nat
deriving Repr, Inhabited

/-- The history of the next system state, from the conflict set of that
state, the history of the previous state and the instance picked in the
previous state (`none` for a transitional state). -/
def nextHist (cs : List Inst) (prev : List Hist) (picked : Option Inst) : List Hist :=
  let byInst : Std.HashMap Inst Hist := prev.foldl (fun m h => m.insert h.inst h) {}
  cs.map (fun ri =>
    match byInst[ri]? with
    | some h =>
        { inst := ri, recency := h.recency + 1,
          lastPicked := if picked == some ri then some 1 else h.lastPicked.map (· + 1) }
    | none => { inst := ri, recency := 1, lastPicked := none })

/-- The refraction rule of §4.2.5: lastPicked(ri, s) < recency(ri, s). -/
def refracted (h : Hist) : Bool :=
  match h.lastPicked with
  | some lp => lp < h.recency
  | none => false

/-- `rif:forwardChaining` (§4.2.5): refraction, then the highest priority,
then the smallest recency, then the first remaining instance. -/
def pick (rules : List PRule) (hist : List Hist) : Option Inst :=
  let cs := hist.filter (fun h => !refracted h)
  let prio := fun (h : Hist) => (rules[h.inst.rule]?.map (·.priority)).getD 0
  match cs with
  | [] => none
  | h0 :: _ =>
    let top := cs.foldl (fun m h => if prio h > m then prio h else m) (prio h0)
    let cs := cs.filter (fun h => prio h == top)
    match cs with
    | [] => none
    | h1 :: _ =>
      let least := cs.foldl (fun m h => if h.recency < m then h.recency else m) h1.recency
      (cs.find? (fun h => h.recency == least)).map (·.inst)

/-- The state the engine carries: the facts, the history of the current
system state, the `New()` counter, the cycles fired, and whether a
built-in blocked evaluation anywhere. -/
structure St where
  facts   : Facts
  hist    : List Hist
  fresh   : Nat := 0
  cycles  : Nat := 0
  blocked : Bool := false
deriving Inhabited

/-- Execute the ground actions of a picked instance, one system state per
atomic action (the transitional states of §4.2.3). -/
def runActions (rules : List PRule) (picked : Inst) :
    St → List GAction → Bool → St
  | st, [], _ => st
  | st, a :: rest, first =>
      let facts := applyGAction st.facts a
      let (cs, b) := conflictSet rules facts
      let hist := nextHist (cs.map (·.1)) st.hist (if first then some picked else none)
      runActions rules picked { st with facts := facts, hist := hist, blocked := st.blocked || b } rest false

/-- One system cycle: pick an instance, or report a final state. -/
def cycle (rules : List PRule) (st : St) : Option St :=
  match pick rules st.hist with
  | none => none
  | some ri =>
    let (cs, _) := conflictSet rules st.facts
    match (cs.find? (fun (j, _) => j == ri)), rules[ri.rule]? with
    | some (_, s), some r =>
        let (s'?, k, b1) := bindActVars st.facts s st.fresh r.actVars
        match s'? with
        | none => some { st with blocked := true, cycles := st.cycles + 1, fresh := k,
                                 hist := nextHist (st.hist.map (·.inst)) st.hist (some ri) }
        | some s' =>
            let gs := r.actions.map (groundAction s')
            let blocked := b1 || gs.any (·.2)
            match gs.mapM (·.1) with
            | none => some { st with blocked := true, cycles := st.cycles + 1, fresh := k,
                                     hist := nextHist (st.hist.map (·.inst)) st.hist (some ri) }
            | some acts =>
                let st' := runActions rules ri { st with fresh := k, blocked := st.blocked || blocked } acts true
                -- An empty action list leaves the state unchanged; the next
                -- cycle state still records that `ri` was picked.
                let st' := if acts.isEmpty
                  then { st' with hist := nextHist (st.hist.map (·.inst)) st.hist (some ri) }
                  else st'
                some { st' with cycles := st'.cycles + 1 }
    | _, _ => none

/-- A rule set is MONOTONE when every action is an `Assert` (or an
`Execute`, which leaves the facts unchanged) and no condition has `Not`.
Then each state's facts include the facts of every earlier state
(`PrdTheorems.prd2013_monotone_step`). -/
def condMonotone : Cond → Bool
  | .core _ => true
  | .not _ => false
  | .and cs => cs.attach.all (fun ⟨c, _⟩ => condMonotone c)
  | .or cs => cs.attach.all (fun ⟨c, _⟩ => condMonotone c)
  | .exists _ c => condMonotone c

def Action.monotone : Action → Bool
  | .assert _ | .execute _ _ => true
  | _ => false

def rulesMonotone (rules : List PRule) : Bool :=
  rules.all (fun r => r.actions.all Action.monotone && (r.cond.map condMonotone).getD true)

/-- The outcome of a run. -/
structure Outcome where
  facts   : Facts
  final   : Bool
  blocked : Bool
  cycles  : Nat
  /-- The run stopped early because `stopWhen` held of a state. -/
  stopped : Bool := false
deriving Inhabited

/-- Run the rule set from the initial facts (§4.2.4, `Eval`) for at most
`fuel` cycles. `final` says the halting test of §4.2.6 held. `stopWhen`
ends the run early at a cycle state (used only for monotone rule sets,
where a goal that holds keeps holding). -/
def runFrom (rules : List PRule) (stopWhen : Facts → Bool) (fuel : Nat) (st : St) : Outcome :=
  if stopWhen st.facts then
    { facts := st.facts, final := false, blocked := st.blocked, cycles := st.cycles, stopped := true }
  else
  match fuel with
  | 0 => { facts := st.facts, final := false, blocked := st.blocked, cycles := st.cycles }
  | n + 1 =>
      match cycle rules st with
      | none => { facts := st.facts, final := true, blocked := st.blocked, cycles := st.cycles }
      | some st' => runFrom rules stopWhen n st'

def run (rules : List PRule) (facts : Facts) (fuel : Nat)
    (stopWhen : Facts → Bool := fun _ => false) : Outcome :=
  let (cs, b) := conflictSet rules facts
  runFrom rules stopWhen fuel { facts := facts, hist := nextHist (cs.map (·.1)) [] none, blocked := b }

/-- The default cycle bound. -/
def defaultCycles : Nat := 2000

/-- Does the final state satisfy the goal (§2.2.2)? `undecided` when a
built-in blocked evaluation or the cycle bound was reached.

For a monotone rule set (`rulesMonotone`) the facts only grow, so a goal
that a reached state satisfies is satisfied by every later state, a final
one included; the run stops there and answers `holds`. This is also how a
monotone rule set with no final state (`Chaining_strategy_numeric-add_1`:
`ex:a(?x+1) :- ex:a(?x)`) gets the answer of RIF Core. -/
def entailsPrd (rules : List PRule) (facts : Facts) (goal : Cond)
    (fuel : Nat := defaultCycles) : Verdict :=
  let mono := rulesMonotone rules
  let o := run rules facts fuel (fun fs => mono && !(matchCond fs [] goal).1.isEmpty)
  let (ss, gb) := matchCond o.facts [] goal
  if o.stopped && !ss.isEmpty then .holds
  else if !o.final then .undecided s!"the run reached its bound of {fuel} cycles"
  else if !ss.isEmpty && !o.blocked then .holds
  else if o.blocked || gb then
    .undecided "a built-in outside this port's slice blocked a rule, an action or the goal"
  else .doesNotHold

end L4Factoidal.RIF.Prd
