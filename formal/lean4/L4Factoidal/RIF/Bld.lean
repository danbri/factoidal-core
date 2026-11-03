/-
L4Factoidal.RIF.Bld — RIF Basic Logic Dialect (RIF BLD, W3C
Recommendation, 2013 Second Edition), as a layer over the RIF Core
engine of `RIF/Engine.lean`.

Spec: https://www.w3.org/TR/2013/REC-rif-bld-20130205/ — §2 (syntax),
§3.4 (semantic structures), §3.5 (truth valuation). RIF-BLD extends RIF
Core (https://www.w3.org/TR/2013/REC-rif-core-20130205/); every Core
rule set is a BLD rule set.

## What BLD adds to Core, and where each addition is decided

* **Equality in rule conclusions** (`f(?y) = g(?z) :- …`). BLD
  interpretations are not Herbrand: two terms may denote one object.
  The engine keeps EQUALITY CLASSES of ground terms (`Classes`), closed
  under congruence (`f(a)` and `f(b)` are equal once `a` and `b` are)
  and under the injectivity of lists (§3.4, `Ilist` is injective).
  Facts, rules and the goal are read through `canon`, which replaces
  each ground term by its class representative. A class representative
  is a data value when the class holds one, so a built-in receives the
  value (`ex:factorial(5) = 120` gives `120` to `func:numeric-multiply`).
* **Inconsistency.** Data values have fixed identities (§3.4, `IC`
  maps a data constant to its value) and lists are disjoint from data
  values. A class with two different data values, a data value and a
  list, or two lists of different length has no model; then every
  formula is entailed (`Arbitrary_Entailment`, `ListLiteralEquality`).
* **Subclass `##`.** `Isub` is transitive and `Iisa ∘ Isub ⊆ Iisa`
  (§3.4, conditions on `I_isa`/`I_sub`). These are the two rules of
  `bldAxioms`, evaluated by the Core engine like any rule.
* **Rules whose variables the body does not bind** (`Forall ?x (ex:A(?x))`,
  `ex:factorial(?N) = … :- External(pred:numeric-greater-than(?N 0))`).
  Core forbids them (safeness); BLD allows them. Their variables range
  over the whole domain, which no finite closure lists. The engine
  instantiates them over a finite UNIVERSE of ground terms (the terms of
  the facts, the rules and the goal, grown by the values the rules
  compute) and then marks the closure INCOMPLETE: a positive answer is
  sound, and a negative one becomes `undecided`.
* **Named-argument uniterms and open lists** are read by `RIF/Ps.lean`
  into positional terms (`namedArgSpace`, `openListSpace`).

## How it relates to Core

The derivation step for the rules in the Core fragment is the Core
engine's own `matchFormula`; this module adds the equality classes, the
universe and the conclusion forms Core lacks. `canon_nil` states that
with no equalities the reading through `canon` changes no term, which
is the base of the relation "BLD 2013 ⊇ Core 2013 on the Core fragment"
(`Theorems` at the end; the full statement over `entails` is open,
https://github.com/danbri/factoidal/issues/1165).
-/
import L4Factoidal.RIF.Engine

namespace L4Factoidal.RIF.Bld

open L4Factoidal.RIF

/-! ## 1. Equality classes -/

/-- Equality classes of ground terms. The head of each class is its
    representative. Classes are disjoint. -/
abbrev Classes := List (List GTerm)

/-- Representative preference: a data value, then a closed list, then
    any other term. -/
def rank (t : GTerm) : Nat :=
  match t with
  | .const _ _ => if (literalValue? t).isSome then 0 else 2
  | .list _ => 1
  | .fapp _ _ _ => 2

/-- The term of least rank, the first among equals. A left fold: a class
    grows with the data. -/
def best (ts : List GTerm) : Option GTerm :=
  ts.foldl (fun acc t => match acc with
    | none => some t
    | some u => if rank t < rank u then some t else some u) none

/-- The class representative of a term; the term itself when it is in
    no class. -/
def rep (cs : Classes) (t : GTerm) : GTerm :=
  match cs.find? (·.contains t) with
  | some (r :: _) => r
  | _ => t

mutual
/-- A ground term read through the equality classes, bottom up: the
    arguments first (congruence), then the term's own class. -/
def canon (cs : Classes) : GTerm → GTerm
  | .const l sp => rep cs (.const l sp)
  | .list xs => rep cs (.list (canonList cs xs))
  | .fapp f sp xs => rep cs (.fapp f sp (canonList cs xs))

def canonList (cs : Classes) : List GTerm → List GTerm
  | [] => []
  | x :: xs => canon cs x :: canonList cs xs
end

/-- A term with its ARGUMENTS read through the classes, the term itself
    kept. Used to rebuild a class after a merge. -/
def canonArgs (cs : Classes) : GTerm → GTerm
  | .const l sp => .const l sp
  | .list xs => .list (canonList cs xs)
  | .fapp f sp xs => .fapp f sp (canonList cs xs)

/-- A class with its representative in front. -/
def withRep (c : List GTerm) : List GTerm :=
  match best c with
  | none => c
  | some r => r :: c.erase r

/-- Add class `c` to `acc`, merging every class of `acc` it meets. -/
def mergeClass (acc : Classes) (c : List GTerm) : Classes :=
  let hit := acc.filter (fun d => d.any c.contains)
  let miss := acc.filter (fun d => !(d.any c.contains))
  miss ++ [withRep (hit.flatten ++ c).eraseDups]

/-- Record `a = b`. -/
def assertEq (cs : Classes) (a b : GTerm) : Classes :=
  let a := canon cs a
  let b := canon cs b
  if a == b then cs else mergeClass cs [a, b]

/-- One congruence pass: re-read every member's arguments through the
    classes, then merge the classes that now share a member. -/
def rebuild (cs : Classes) : Classes :=
  (cs.map (fun c => (c ++ c.map (canonArgs cs)).eraseDups)).foldl mergeClass []

/-- The element pairs that list injectivity makes equal: two closed lists
    of the same length in one class have equal elements. -/
def listPairs (c : List GTerm) : List (GTerm × GTerm) :=
  let lists := c.filterMap (fun t => match t with | .list xs => some xs | _ => none)
  lists.flatMap (fun xs => lists.flatMap (fun ys =>
    if xs.length == ys.length then xs.zip ys else []))

/-- Close the classes under congruence and list injectivity. `fuel`
    bounds the passes; each pass that changes nothing ends the loop. -/
def closeEq : Nat → Classes → Classes
  | 0, cs => cs
  | fuel + 1, cs =>
      let cs1 := rebuild cs
      let cs2 := (cs1.flatMap listPairs).foldl (fun acc (a, b) => assertEq acc a b) cs1
      if cs2 == cs then cs else closeEq fuel cs2

/-- An open list term (`openListSpace`). -/
def isOpenList : GTerm → Bool
  | .fapp _ sp _ => sp == openListSpace
  | _ => false

/-- Does a class have no model? Two different data values, a data value
    and a list, or two closed lists of different length (§3.4: `IC` is
    fixed on data values, `Ilist` is injective, lists and data values
    are disjoint). -/
def classClash (c : List GTerm) : Bool :=
  let data := c.filterMap literalValue?
  let lists := c.filterMap (fun t => match t with | .list xs => some xs.length | _ => none)
  let anyList := !lists.isEmpty || c.any isOpenList
  data.any (fun x => data.any (fun y => !(x.identical y))) ||
  (!data.isEmpty && anyList) ||
  lists.any (fun n => lists.any (· != n))

def inconsistent (cs : Classes) : Bool := cs.any classClash

/-! ## 2. Reading terms, atoms and formulas through the classes -/

/-- A ground term as a term pattern. -/
def tmOfG : GTerm → Tm
  | .const l sp => .const l sp
  | .list xs => .list (xs.map tmOfG)
  | .fapp f sp xs => .fapp f sp (xs.map tmOfG)

mutual
/-- A term pattern with no variable and no `External` as a ground term. -/
def gOfTm? : Tm → Option GTerm
  | .const l sp => some (.const l sp)
  | .list xs => (gOfTms? xs).map GTerm.list
  | .fapp f sp xs => (gOfTms? xs).map (GTerm.fapp f sp)
  | _ => none

def gOfTms? : List Tm → Option (List GTerm)
  | [] => some []
  | x :: xs => match gOfTm? x, gOfTms? xs with
    | some g, some gs => some (g :: gs)
    | _, _ => none
end

mutual
/-- Replace every ground subterm of a pattern by its representative. -/
def canonTm (cs : Classes) : Tm → Tm
  | .var v => .var v
  | .const l sp => tmOfG (canon cs (.const l sp))
  | .list xs =>
      let ys := canonTms cs xs
      match gOfTms? ys with
      | some gs => tmOfG (canon cs (.list gs))
      | none => .list ys
  | .fapp f sp xs =>
      let ys := canonTms cs xs
      match gOfTms? ys with
      | some gs => tmOfG (canon cs (.fapp f sp gs))
      | none => .fapp f sp ys
  | .external f xs => .external f (canonTms cs xs)

def canonTms (cs : Classes) : List Tm → List Tm
  | [] => []
  | x :: xs => canonTm cs x :: canonTms cs xs
end

def canonAtom (cs : Classes) : Atom → Atom
  | .pos f sp args => .pos f sp (canonTms cs args)
  | .frame o p v => .frame (canonTm cs o) (canonTm cs p) (canonTm cs v)
  | .member o c => .member (canonTm cs o) (canonTm cs c)
  | .sub c d => .sub (canonTm cs c) (canonTm cs d)
  | .equal a b => .equal (canonTm cs a) (canonTm cs b)
  | .externalPred f args => .externalPred f (canonTms cs args)

def canonFormula (cs : Classes) : Formula → Formula
  | .atom a => .atom (canonAtom cs a)
  | .and fs => .and (fs.map (canonFormula cs))
  | .or fs => .or (fs.map (canonFormula cs))
  | .exists vs f => .exists vs (canonFormula cs f)

def canonRule (cs : Classes) (r : Rule) : Rule :=
  { r with head := canonAtom cs r.head, body := r.body.map (canonFormula cs) }

def canonGAtom (cs : Classes) : GAtom → GAtom
  | .pos f sp args => .pos f sp (canonList cs args)
  | .frame o p v => .frame (canon cs o) (canon cs p) (canon cs v)
  | .member o c => .member (canon cs o) (canon cs c)
  | .sub c d => .sub (canon cs c) (canon cs d)

/-! ## 3. Grounding a term with the classes

The Core `groundTm` builds a function term and stops; here each
constructed term is read through the classes at once, so a built-in
whose argument is `ex:factorial(5)` receives `120` when the classes say
so. An open list whose tail is a closed list becomes the closed list. -/

/-- Fold an open list whose tail is a closed list. -/
def normList : GTerm → GTerm
  | .fapp f sp xs =>
      if sp == openListSpace then
        match xs.reverse with
        | .list ys :: revInit => .list (revInit.reverse ++ ys)
        | _ => .fapp f sp xs
      else .fapp f sp xs
  | t => t

mutual
def groundTmC (cs : Classes) (s : Subst) : Tm → Option GTerm × Bool
  | .var v => ((lookupVar s v).map (canon cs), false)
  | .const l sp => (some (canon cs (.const l sp)), false)
  | .list xs =>
      let (r, b) := groundTmsC cs s xs
      (r.map (fun ts => canon cs (.list ts)), b)
  | .fapp f sp xs =>
      let (r, b) := groundTmsC cs s xs
      (r.map (fun ts => canon cs (normList (.fapp f sp ts))), b)
  | .external fn xs =>
      let (r, b) := groundTmsC cs s xs
      match r with
      | none => (none, b)
      | some ts =>
          match builtinName fn with
          | none => (none, true)
          | some nm => match evalFunc nm ts with
            | some v => (some (canon cs v), b)
            | none => (none, true)

def groundTmsC (cs : Classes) (s : Subst) : List Tm → Option (List GTerm) × Bool
  | [] => (some [], false)
  | x :: xs =>
      let (r1, b1) := groundTmC cs s x
      let (r2, b2) := groundTmsC cs s xs
      match r1, r2 with
      | some g, some gs => (some (g :: gs), b1 || b2)
      | _, _ => (none, b1 || b2)
end

mutual
/-- Every ground value a term pattern reaches under `s`: the term, each
    `External` result and each constructed term inside it. This is what
    grows the universe of an unsafe rule. -/
def reached (cs : Classes) (s : Subst) : Tm → List GTerm
  | .list xs => (groundTmC cs s (.list xs)).1.toList ++ reachedList cs s xs
  | .fapp f sp xs => (groundTmC cs s (.fapp f sp xs)).1.toList ++ reachedList cs s xs
  | .external f xs => (groundTmC cs s (.external f xs)).1.toList ++ reachedList cs s xs
  | t => (groundTmC cs s t).1.toList

def reachedList (cs : Classes) (s : Subst) : List Tm → List GTerm
  | [] => []
  | x :: xs => reached cs s x ++ reachedList cs s xs
end

/-! ## 4. Rules -/

/-- The semantic conditions on `##` and `#` (RIF-BLD 2013 §3.4: `I_sub`
    is transitive, and `I_isa(o, a)` with `I_sub(a, b)` gives
    `I_isa(o, b)`), stated as two rules that the engine runs like any
    other. -/
def bldAxioms : List Rule :=
  [ { vars := ["a", "b", "c"], head := .sub (.var "a") (.var "c"),
      body := some (.and [.atom (.sub (.var "a") (.var "b")),
                          .atom (.sub (.var "b") (.var "c"))]) },
    { vars := ["o", "a", "b"], head := .member (.var "o") (.var "b"),
      body := some (.and [.atom (.member (.var "o") (.var "a")),
                          .atom (.sub (.var "a") (.var "b"))]) } ]

def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsSubClassOfIri : String := "http://www.w3.org/2000/01/rdf-schema#subClassOf"

/-- The conditions that every RIF-RDF combination adds (RIF RDF and OWL
    Compatibility 2013, §5.1.1, common-RIF-RDF-interpretations,
    conditions 7 and 8): `rdf:type` and `#` agree in both directions, and
    `a ## b` gives `a rdfs:subClassOf b`. The converse of the last does
    NOT hold (`RDF_Combination_SubClass_5`). -/
def rdfCombinationRules : List Rule :=
  let ty : Tm := .const rdfTypeIri iriSpace
  let sc : Tm := .const rdfsSubClassOfIri iriSpace
  [ { vars := ["x", "y"], head := .frame (.var "x") ty (.var "y"),
      body := some (.atom (.member (.var "x") (.var "y"))) },
    { vars := ["x", "y"], head := .member (.var "x") (.var "y"),
      body := some (.atom (.frame (.var "x") ty (.var "y"))) },
    { vars := ["x", "y"], head := .frame (.var "x") sc (.var "y"),
      body := some (.atom (.sub (.var "x") (.var "y"))) } ]

def tmsOfAtom : Atom → List Tm
  | .pos _ _ args => args
  | .frame o p v => [o, p, v]
  | .member o c => [o, c]
  | .sub c d => [c, d]
  | .equal a b => [a, b]
  | .externalPred _ args => args

def tmsOfFormula : Formula → List Tm
  | .atom a => tmsOfAtom a
  | .and fs => fs.flatMap tmsOfFormula
  | .or fs => fs.flatMap tmsOfFormula
  | .exists _ f => tmsOfFormula f

def tmsOfRule (r : Rule) : List Tm :=
  tmsOfAtom r.head ++ (r.body.map tmsOfFormula).getD []

mutual
/-- The variables of a term outside every `External`: a built-in call
    computes from its arguments, so an atom binds no variable inside one
    (`ex:a(External(func:numeric-add(?x 1)))` does not bind `?x`). -/
def varsOutsideExternal : Tm → List String
  | .var v => [v]
  | .const _ _ => []
  | .list xs => varsOutsideExternalList xs
  | .fapp _ _ xs => varsOutsideExternalList xs
  | .external _ _ => []

def varsOutsideExternalList : List Tm → List String
  | [] => []
  | x :: xs => varsOutsideExternal x ++ varsOutsideExternalList xs
end

/-- The variables a body atom binds by matching facts. -/
def bindsAtom : Atom → List String
  | .externalPred _ _ | .equal _ _ => []
  | a => (tmsOfAtom a).flatMap varsOutsideExternal

/-- The conjuncts of a body that bind or compute, `Or` and `Exists` left
    out: a disjunction binds only what each branch binds, which is not
    needed by any case here and is then left to the universe. -/
def conjuncts : Formula → List Atom
  | .atom a => [a]
  | .and fs => fs.flatMap conjuncts
  | .or _ | .exists _ _ => []

/-- The variables a body binds, in the direction of computation: an atom
    binds the variables outside its `External`s; `?v = t` binds `?v` once
    every variable of `t` is bound; `pred:iri-string` with one variable
    left binds it. Core's `boundFix` also reads `t = ?v` backwards
    (`?N1 = External(func:numeric-subtract(?N 1))` "binds" `?N`), which
    is right for Core safeness and wrong for evaluation. -/
def boundBld : Nat → List Atom → List String → List String
  | 0, _, acc => acc
  | fuel + 1, as, acc =>
      let grown := as.foldl (fun bs a =>
        match a with
        | .equal (.var v) y =>
            if !bs.contains v && (varsOfTm y).all bs.contains then bs ++ [v] else
            (match y with
             | .var w => if !bs.contains w && bs.contains v then bs ++ [w] else bs
             | _ => bs)
        | .equal x (.var v) =>
            if !bs.contains v && (varsOfTm x).all bs.contains then bs ++ [v] else bs
        | .externalPred fn args =>
            if builtinName fn == some "iri-string" then
              let free := ((args.flatMap varsOfTm).filter (fun v => !bs.contains v)).eraseDups
              if free.length == 1 then bs ++ free else bs
            else bs
        | _ => bs) acc
      if grown.length == acc.length then acc else boundBld fuel as grown

/-- Choose the variables to instantiate from the universe: take the
    first unbound variable, count it bound, propagate (`boundBld`), and
    repeat. In `ex:factorial(?N ?F) :- … ?F = External(func:numeric-multiply(?N ?F1))`
    only `?N` is chosen; `?F` is then computed. -/
def chooseSeeds (as : List Atom) (used : List String) : Nat → List String → List String → List String
  | 0, _, chosen => chosen
  | fuel + 1, bound, chosen =>
      match used.find? (fun v => !bound.contains v) with
      | none => chosen
      | some v => chooseSeeds as used fuel (boundBld (as.length + 1) as (bound ++ [v])) (chosen ++ [v])

/-- The variables of a rule that its body does not bind and that are
    instantiated from the universe. Empty for every rule whose body binds
    all its variables, which includes every safe RIF Core rule. -/
def unboundVars (r : Rule) : List String :=
  let used := (varsOfAtom r.head ++ (r.body.map varsOfFormula).getD []).eraseDups
  let as := (r.body.map conjuncts).getD []
  let bound := boundBld (as.length + 1) as (as.flatMap bindsAtom)
  chooseSeeds as used used.length bound []

/-- Every substitution of `vs` by terms of `univ`. -/
def seeds (univ : List GTerm) (vs : List String) : List Subst :=
  vs.foldl (fun acc v => acc.flatMap (fun s => univ.map (fun t => (v, t) :: s))) [[]]

/-- A head atom as a fact, its terms read through the classes. -/
def instantiateC (cs : Classes) (s : Subst) : Atom → Option GAtom × Bool
  | .pos f sp args =>
      let (r, b) := groundTmsC cs s args
      (r.map (GAtom.pos f sp), b)
  | .frame o p v =>
      match groundTmsC cs s [o, p, v] with
      | (some [a, b', c], b) => (some (.frame a b' c), b)
      | (_, b) => (none, b)
  | .member o c =>
      match groundTmsC cs s [o, c] with
      | (some [a, b'], b) => (some (.member a b'), b)
      | (_, b) => (none, b)
  | .sub c d =>
      match groundTmsC cs s [c, d] with
      | (some [a, b'], b) => (some (.sub a b'), b)
      | (_, b) => (none, b)
  | .equal _ _ | .externalPred _ _ => (none, true)

/-- What one rule gives in one round. -/
structure Out where
  facts : Facts := []
  eqs : List (GTerm × GTerm) := []
  univ : List GTerm := []
  blocked : Bool := false
  incomplete : Bool := false

/-- Fire one rule over the facts. A rule with unbound variables is
    instantiated over `univ` first (and the result is marked incomplete);
    every value such an instance computes joins the universe. -/
def fireRule (cs : Classes) (facts : Facts) (univ : List GTerm) (seedCap : Nat)
    (r : Rule) : Out :=
  let free := unboundVars r
  let tooMany := !free.isEmpty && univ.length ^ free.length > seedCap
  let ss0 : List Subst := if tooMany then [] else seeds univ free
  let grow := fun (s : Subst) => if free.isEmpty then [] else (tmsOfRule r).flatMap (reached cs s)
  ss0.foldl (fun out s0 =>
    let (ss, b) : List Subst × Bool := match r.body with
      | none => ([s0], false)
      | some body => matchFormula facts s0 body
    let out := { out with univ := out.univ ++ grow s0, blocked := out.blocked || b }
    ss.foldl (fun out s =>
      let out := { out with univ := out.univ ++ grow s }
      match r.head with
      | .equal x y =>
          (match groundTmC cs s x, groundTmC cs s y with
           | (some a, b1), (some c, b2) =>
               { out with eqs := out.eqs ++ [(a, c)], blocked := out.blocked || b1 || b2 }
           | (_, b1), (_, b2) => { out with blocked := out.blocked || b1 || b2 })
      | h =>
          (match instantiateC cs s h with
           | (some f, b) => { out with facts := out.facts ++ [f], blocked := out.blocked || b }
           | (none, b) => { out with blocked := out.blocked || b })) out)
    { incomplete := !free.isEmpty }

/-! ## 5. The forward chain -/

structure Cfg where
  rounds : Nat := 32
  /-- The most terms the universe of the unsafe rules may hold. -/
  univCap : Nat := 400
  /-- The most instances of one unsafe rule per round. -/
  seedCap : Nat := 20000
  /-- Add the RIF-RDF combination conditions (`rdfCombinationRules`). -/
  rdfCombination : Bool := false
  /-- Facts an imported entailment regime adds to a fact set (the RDFS
      closure under an RDFS import); identity when there is none. -/
  extra : Facts → Facts := fun _ => []

structure St where
  facts : Facts
  cs : Classes := []
  univ : List GTerm := []
  blocked : Bool := false
  incomplete : Bool := false

/-- One round. Returns the new state and whether anything changed. -/
def roundStep (cfg : Cfg) (rules : List Rule) (st : St) : St × Bool :=
  let cs := closeEq 32 st.cs
  let facts := (st.facts.map (canonGAtom cs)).eraseDups
  let univ := (st.univ.map (canon cs)).eraseDups
  let outs := (rules.map (canonRule cs)).map (fireRule cs facts univ cfg.seedCap)
  let derived := (outs.flatMap (·.facts)) ++ cfg.extra facts
  let newFacts := ((derived.map (canonGAtom cs)).filter (fun f => !facts.contains f)).eraseDups
  let cs2 := closeEq 32 ((outs.flatMap (·.eqs)).foldl (fun acc (a, b) => assertEq acc a b) cs)
  let grown := (((outs.flatMap (·.univ)).map (canon cs)).filter (fun t => !univ.contains t)).eraseDups
  let room := cfg.univCap - univ.length
  let st' : St :=
    { facts := facts ++ newFacts, cs := cs2, univ := univ ++ grown.take room,
      blocked := st.blocked || outs.any (·.blocked),
      incomplete := st.incomplete || outs.any (·.incomplete) || grown.length > room }
  (st', !newFacts.isEmpty || cs2 != cs || !(grown.take room).isEmpty)

/-- Rounds until nothing changes, the classes clash, or `n` runs out
    (the second result: the bound was reached). -/
def run (cfg : Cfg) (rules : List Rule) : Nat → St → St × Bool
  | 0, st => (st, true)
  | n + 1, st =>
      let (st', changed) := roundStep cfg rules st
      if inconsistent st'.cs || !changed then (st', false) else run cfg rules n st'

/-- The members of the class of `t`. -/
def membersOf (cs : Classes) (t : GTerm) : List GTerm :=
  (cs.find? (·.contains t)).getD [t]

/-- Every choice of one term from each list, in order. -/
def combos (ms : List (List GTerm)) : List (List GTerm) :=
  ms.reverse.foldl (fun acc m => m.flatMap (fun x => acc.map (x :: ·))) [[]]

/-- A built-in predicate holds of a class when it holds of some members
    (`pred:iri-string(ex:b "…#a")` once `ex:a = ex:b`): a ground call
    becomes the disjunction over the members, at most 64 of them. -/
def expandBuiltins (cs : Classes) : Formula → Formula
  | .atom (.externalPred f args) =>
      match gOfTms? args with
      | some gs =>
          let cands := combos (gs.map (membersOf cs))
          if cands.length ≤ 64 then
            .or (cands.map (fun xs => .atom (.externalPred f (xs.map tmOfG))))
          else .atom (.externalPred f args)
      | none => .atom (.externalPred f args)
  | .atom a => .atom a
  | .and fs => .and (fs.map (expandBuiltins cs))
  | .or fs => .or (fs.map (expandBuiltins cs))
  | .exists vs f => .exists vs (expandBuiltins cs f)

def gTermsOfGAtom : GAtom → List GTerm
  | .pos _ _ args => args
  | .frame o p v => [o, p, v]
  | .member o c => [o, c]
  | .sub c d => [c, d]

/-- Does the BLD closure of `rules` over `facts` entail `goal`?
    `holds` is sound. `doesNotHold` is given only when no rule needed the
    finite universe, no built-in blocked, and the chain reached a fixed
    point; otherwise `undecided`. -/
def entailsBld (cfg : Cfg) (rules : List Rule) (facts : Facts) (goal : Formula) : Verdict :=
  let rules := rules ++ bldAxioms ++ (if cfg.rdfCombination then rdfCombinationRules else [])
  let hasUnsafe := rules.any (fun r => !(unboundVars r).isEmpty)
  let univ0 : List GTerm :=
    if hasUnsafe then
      ((facts.flatMap gTermsOfGAtom).flatMap (fun t => reached [] [] (tmOfG t)) ++
       (rules.flatMap tmsOfRule ++ tmsOfFormula goal).flatMap (reached [] [])).eraseDups
    else []
  let (st, capped) := run cfg rules cfg.rounds { facts := facts, univ := univ0.take cfg.univCap }
  let cs := closeEq 32 st.cs
  if inconsistent cs then .holds
  else
    let fs := (st.facts.map (canonGAtom cs)).eraseDups
    let (ss, gb) := matchFormula fs [] (expandBuiltins cs (canonFormula cs goal))
    if !ss.isEmpty then .holds
    else if st.blocked || gb then
      .undecided "a built-in outside this port's slice blocked a rule or the goal"
    else if st.incomplete then
      .undecided "a rule has a variable its body does not bind; its instances were taken over a finite set of terms"
    else if capped then .undecided "the forward chain reached its round bound"
    else .doesNotHold

/-! ## 6. Well-formedness (RIF-BLD 2013 §2.6)

BLD drops Core's safeness, but keeps the condition that a rule has no
FREE variable: each variable is in its `Forall` list or under an
`Exists` (`No_free_variables`). -/

def freeVarsFormula : Formula → List String
  | .atom a => varsOfAtom a
  | .and fs => fs.flatMap freeVarsFormula
  | .or fs => fs.flatMap freeVarsFormula
  | .exists vs f => (freeVarsFormula f).filter (fun v => !vs.contains v)

def ruleClosed (r : Rule) : Bool :=
  (varsOfAtom r.head ++ (r.body.map freeVarsFormula).getD []).all r.vars.contains

def documentWellFormed (rs : List Rule) : Bool := rs.all ruleClosed

end L4Factoidal.RIF.Bld
