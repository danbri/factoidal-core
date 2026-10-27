/-
L4Factoidal.SPARQLRL.Syntax — the SPARQL 1.2 RL (SPARQL-RL) abstract syntax
and its static analysis: well-formedness, the rule dependency graph with open
and closed dependencies, run-once rules, and stratification.

Source: the W3C Data Shapes Working Group editor's draft "SPARQL 1.2 RL",
https://w3c.github.io/data-shapes/sparql12-rl/ (vendored at
`third_party/testing/sparql-rl/spec/index.html`, data-shapes commit fe4eed4,
2026-10-27). Section names below are the draft's.
Issue: https://github.com/danbri/factoidal/issues/1099 (SPARQL-RL for 0.20.0).

## What this module holds

| Draft section | Here |
|---|---|
| "Elements of the Abstract Syntax" | `STerm`, `STriple`, `AggFn`, `Elt`, `Rule`, `RuleSet` |
| "Run-once rule" | `Rule.runOnce` |
| "Well-formedness Conditions" | `wfSeq`, `Rule.wellFormed`, `RuleSet.wellFormed` |
| "Rule Dependency", "Triple pattern matching" | `patternMatchesTemplate` (unification) |
| "Dependency Graph Algorithm" | `dependencyGraph` |
| "Stratification Algorithm", "Stratification Condition" | `stratify` |

## Representation choices

* One term type, `STerm`, serves data blocks, head templates and body
  patterns. A term may sit in a position that RDF does not allow (a literal
  subject: the grammar allows `123 :q 456` in a `DATA` block, test
  `syntax-data-05`). Evaluation keeps such generalized triples; the
  `Graph` it returns holds only RDF triples (`Eval.lean`).
* Blank nodes in a BODY are variables (draft: "Treating blank nodes as
  variables"). The parser renames them at parse time to variables whose
  names start with `.`, which a SPARQL VARNAME cannot contain, so they never
  clash with a user variable. The fresh variables of a property path
  sequence (`:p/:q`) and of the blank nodes that `[ ]`, `( )` and `{| |}`
  introduce are named the same way. Blank nodes in a head template or a
  data block stay blank nodes; evaluation replaces them with fresh ones.
* A filter or assignment element carries the variables of its expression
  (`vars`), collected by the parser from the expression's tokens. The
  SPARQL-RL expression grammar has no `EXISTS` and no aggregates, so the
  tokens are the whole story.

## Termination

Recursion over `Elt` is structural (nested inductive, one `mutual` block per
function pair). The stratification loop and the unifier take explicit fuel
whose size is stated where it is computed. No `partial def`.
-/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Terms and triples -/

/-- A term of a data block, a head template or a body pattern: a variable,
an RDF term, or a triple-term pattern/template (draft: "Triple pattern",
"Triple template"). -/
inductive STerm where
  | var    (v : String)
  | iri    (i : WfIri)
  | bnode  (b : String)
  | lit    (l : WfLiteral)
  | triple (s p o : STerm)
  deriving Repr, DecidableEq, Inhabited

/-- A triple pattern, triple template or data triple. -/
structure STriple where
  s : STerm
  p : STerm
  o : STerm
  deriving Repr, DecidableEq, Inhabited

def STerm.vars : STerm → List String
  | .var v => [v]
  | .triple s p o => s.vars ++ p.vars ++ o.vars
  | _ => []

def STerm.bnodes : STerm → List String
  | .bnode b => [b]
  | .triple s p o => s.bnodes ++ p.bnodes ++ o.bnodes
  | _ => []

/-- A triple term in which a variable occurs (draft: "Run-once rule", the
fourth condition). -/
def STerm.hasVarTripleTerm : STerm → Bool
  | .triple s p o => !(STerm.triple s p o).vars.isEmpty
  | _ => false

def STriple.vars (t : STriple) : List String := t.s.vars ++ t.p.vars ++ t.o.vars
def STriple.bnodes (t : STriple) : List String := t.s.bnodes ++ t.p.bnodes ++ t.o.bnodes
def STriple.hasVarTripleTerm (t : STriple) : Bool :=
  t.s.hasVarTripleTerm || t.p.hasVarTripleTerm || t.o.hasVarTripleTerm

/-! ## Rule elements -/

/-- An aggregation function (draft: "Aggregation functions"). `count d none`
is `COUNT(*)` / `COUNT(DISTINCT *)`. -/
inductive AggFn where
  | count (distinct : Bool) (arg : Option String)
  | min (v : String)
  | max (v : String)
  | sum (v : String)
  deriving Repr, DecidableEq

def AggFn.vars : AggFn → List String
  | .count _ (some v) => [v]
  | .count _ none => []
  | .min v | .max v | .sum v => [v]

/-- A rule element (draft: "Rule element"). -/
inductive Elt where
  /-- triple pattern element -/
  | triple (t : STriple)
  /-- filter element; `vars` are the variables the expression mentions -/
  | filter (e : Expr) (vars : List String)
  /-- negation element; `evaldata = false` is `NOT DATA` -/
  | neg (evaldata : Bool) (inner : List Elt)
  /-- assignment element `SET (?v := e)` -/
  | assign (v : String) (e : Expr) (vars : List String)
  /-- group element `GROUP BY keys { pattern } [ aggs ]` -/
  | group (keys : List String) (pattern : List Elt) (aggs : List (String × AggFn))
  deriving Inhabited

/-- A rule (draft: "Rule"). `evaldata = false` is `WHERE DATA`. -/
structure Rule where
  id       : Option String := none
  head     : List STriple
  body     : List Elt
  evaldata : Bool := true
  deriving Inhabited

/-- A rule set (draft: "Rule set"): rules, the triples of its data blocks,
and its imports. -/
structure RuleSet where
  rules   : List Rule := []
  data    : List STriple := []
  imports : List String := []
  deriving Inhabited

/-! ## Run-once rules — draft "Run-once rule" -/

mutual
/-- The body has an assignment element (at any depth) or a group element. -/
def Elt.makesRunOnce : Elt → Bool
  | .assign _ _ _ => true
  | .group _ _ _ => true
  | .neg _ inner => Elt.listMakesRunOnce inner
  | _ => false
def Elt.listMakesRunOnce : List Elt → Bool
  | [] => false
  | e :: es => e.makesRunOnce || Elt.listMakesRunOnce es
end

/-- Draft "Run-once rule": an assignment element, a group element, a blank
node in a head template, or a head triple term in which a variable occurs. -/
def Rule.runOnce (r : Rule) : Bool :=
  Elt.listMakesRunOnce r.body ||
  r.head.any (fun t => !t.bnodes.isEmpty || t.hasVarTripleTerm)

/-! ## Well-formedness — draft "Well-formedness Conditions" -/

def addVars (vs xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) vs

def allIn (xs vs : List String) : Bool := xs.all vs.contains

def distinctStrs : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinctStrs xs

mutual
/-- `vars(S, i, V0)` after one element, or `none` when the element breaks a
condition of a well-formed sequence. -/
def wfElt (v : List String) : Elt → Option (List String)
  | .triple t => some (addVars v t.vars)
  | .filter _ xs => if allIn xs v then some v else none
  | .assign x _ xs => if allIn xs v && !v.contains x then some (addVars v [x]) else none
  | .neg _ inner => (wfSeq v inner).map (fun _ => v)
  | .group keys pat aggs =>
      match wfSeq v pat with
      | none => none
      | some vp =>
          let aggVars := aggs.map Prod.fst
          if allIn keys vp && aggVars.all (fun a => !vp.contains a) &&
             distinctStrs aggVars && aggs.all (fun a => allIn a.2.vars vp)
          then some (addVars (addVars v keys) aggVars)
          else none
/-- `vars(S, V0)` when `S` is a well-formed sequence given `V0`, else `none`. -/
def wfSeq (v : List String) : List Elt → Option (List String)
  | [] => some v
  | e :: es =>
      match wfElt v e with
      | none => none
      | some v' => wfSeq v' es
end

/-- Draft: a rule is well-formed when its body is a well-formed sequence from
the empty set and every head variable is in scope after the body. -/
def Rule.wellFormed (r : Rule) : Bool :=
  match wfSeq [] r.body with
  | none => false
  | some vs => r.head.all (fun t => allIn t.vars vs)

def RuleSet.wellFormed (rs : RuleSet) : Bool := rs.rules.all Rule.wellFormed

/-! ## Rule dependency — draft "Rule Dependency"

A triple pattern matches a triple template when the template can generate a
triple that the pattern matches. Both sides are instantiated by independent
substitutions, so the test is unification after the two sides' variables are
renamed apart. A blank node of a template is a fresh term each time: it
equals no constant, and it unifies with a variable only. Body blank nodes
were turned into variables by the parser. -/

/-- A substitution for unification. -/
abbrev Subst := List (String × STerm)

def substLookup (σ : Subst) (x : String) : Option STerm :=
  (σ.find? (fun p => p.1 == x)).map Prod.snd

/-- Resolve a variable through the substitution. Fuel: the length of the
substitution plus one bounds every chain, because the unifier never binds a
variable twice. -/
def walk (σ : Subst) : Nat → STerm → STerm
  | 0, t => t
  | f + 1, .var x =>
      match substLookup σ x with
      | some t => walk σ f t
      | none => .var x
  | _, t => t

/-- `x` occurs in `t` under `σ`. -/
def occurs (σ : Subst) (x : String) : Nat → STerm → Bool
  | 0, _ => true
  | f + 1, t =>
      match walk σ (σ.length + 1) t with
      | .var y => x == y
      | .triple a b c => occurs σ x f a || occurs σ x f b || occurs σ x f c
      | _ => false

/-- Syntactic unification with occurs check. Fuel bounds the term depth. -/
def unify (fuel : Nat) (σ : Subst) (a b : STerm) : Option Subst :=
  match fuel with
  | 0 => none
  | f + 1 =>
    let a' := walk σ (σ.length + 1) a
    let b' := walk σ (σ.length + 1) b
    match a', b' with
    | .var x, .var y => if x == y then some σ else some ((x, .var y) :: σ)
    | .var x, t => if occurs σ x (f + 1) t then none else some ((x, t) :: σ)
    | t, .var y => if occurs σ y (f + 1) t then none else some ((y, t) :: σ)
    | .triple s1 p1 o1, .triple s2 p2 o2 =>
        match unify f σ s1 s2 with
        | none => none
        | some σ1 =>
            match unify f σ1 p1 p2 with
            | none => none
            | some σ2 => unify f σ2 o1 o2
    | .bnode _, _ => none
    | _, .bnode _ => none
    | x, y => if x == y then some σ else none

def STerm.depth : STerm → Nat
  | .triple s p o => 1 + max s.depth (max p.depth o.depth)
  | _ => 1

/-- Rename the variables of a term apart (`tag` is a prefix no parser
variable has, since parser variables never contain U+0001). -/
def STerm.rename (tag : String) : STerm → STerm
  | .var v => .var (tag ++ v)
  | .triple s p o => .triple (s.rename tag) (p.rename tag) (o.rename tag)
  | t => t

def STriple.rename (tag : String) (t : STriple) : STriple :=
  ⟨t.s.rename tag, t.p.rename tag, t.o.rename tag⟩

/-- Draft "Triple pattern matching": the template can generate a triple that
the pattern matches. -/
def patternMatchesTemplate (tp tt : STriple) : Bool :=
  let tag1 := String.singleton (Char.ofNat 1) ++ "p"
  let tag2 := String.singleton (Char.ofNat 1) ++ "t"
  let a := tp.rename tag1
  let b := tt.rename tag2
  -- Fuel: twice the summed depth plus the number of variables on both sides
  -- bounds the recursion of each `unify` call (each call goes one level down
  -- a term that the substitution can at most graft once per variable).
  let fuel := 2 * (a.s.depth + a.p.depth + a.o.depth + b.s.depth + b.p.depth + b.o.depth) +
    a.vars.length + b.vars.length + 4
  match unify fuel [] a.s b.s with
  | none => false
  | some σ1 =>
      match unify fuel σ1 a.p b.p with
      | none => false
      | some σ2 => (unify fuel σ2 a.o b.o).isSome

/-- An edge label (draft "Dependency graph"). -/
inductive DepLabel where
  | openDep
  | closedDep
  deriving Repr, DecidableEq, Inhabited

/-- Draft "mergeLabel": closed overrides open. -/
def mergeLabel : DepLabel → DepLabel → DepLabel
  | .openDep, .openDep => .openDep
  | _, _ => .closedDep

mutual
/-- The triple patterns a rule element contributes to dependencies, with the
label they need (draft "Dependency Graph Algorithm"). -/
def Elt.depPatterns (inClosed : Bool) : Elt → List (STriple × DepLabel)
  | .triple t => [(t, if inClosed then .closedDep else .openDep)]
  | .neg evaldata inner => if evaldata then Elt.listDepPatterns true inner else []
  | .group _ pat _ => Elt.listDepPatterns true pat
  | _ => []
def Elt.listDepPatterns (inClosed : Bool) : List Elt → List (STriple × DepLabel)
  | [] => []
  | e :: es => e.depPatterns inClosed ++ Elt.listDepPatterns inClosed es
end

/-- A dependency edge from rule `src` to rule `dst` (rule indices). -/
structure DepEdge where
  src : Nat
  dst : Nat
  label : DepLabel
  deriving Repr, DecidableEq, Inhabited

def insertEdge (es : List DepEdge) (e : DepEdge) : List DepEdge :=
  match es.find? (fun x => x.src == e.src && x.dst == e.dst) with
  | none => es ++ [e]
  | some old =>
      es.map (fun x => if x.src == e.src && x.dst == e.dst
                       then { x with label := mergeLabel old.label e.label } else x)

/-- Draft "buildDependencyGraph". A rule whose `.evaldata` is false matches the
base graph and has no dependencies. -/
def dependencyGraph (rules : List Rule) : List DepEdge :=
  let indexed := rules.zipIdx
  indexed.foldl (fun acc (r1, i) =>
    if !r1.evaldata then acc else
    let pats := Elt.listDepPatterns false r1.body
    let pats := if r1.runOnce then pats.map (fun p => (p.1, DepLabel.closedDep)) else pats
    pats.foldl (fun acc2 (tp, lbl) =>
      indexed.foldl (fun acc3 (r2, j) =>
        if r2.head.any (patternMatchesTemplate tp) then insertEdge acc3 ⟨i, j, lbl⟩
        else acc3) acc2) acc) []

/-! ## Stratification — draft "Stratification Algorithm" -/

/-- A stratification layer: rule indices, run-once and general. -/
structure Layer where
  once    : List Nat
  general : List Nat
  deriving Repr, DecidableEq, Inhabited

def getD (m : Array Nat) (i : Nat) : Nat := m.getD i 0

/-- One pass over the edges. `none` when a stratum passes `limit` (the
draft's guard: the stratification condition is violated). -/
def strataPass (limit : Nat) (edges : List DepEdge) (m : Array Nat) :
    Option (Array Nat × Bool) :=
  edges.foldl (fun acc e =>
    match acc with
    | none => none
    | some (m, changed) =>
      let p := getD m e.src
      let q := getD m e.dst
      match e.label with
      | .openDep => if p < q then some (m.set! e.src q, true) else some (m, changed)
      | .closedDep =>
          if p ≤ q then
            if q + 1 > limit then none else some (m.set! e.src (q + 1), true)
          else some (m, changed)) (some (m, false))

def strataLoop (limit : Nat) (edges : List DepEdge) : Nat → Array Nat → Option (Array Nat)
  | 0, _ => none
  | f + 1, m =>
      match strataPass limit edges m with
      | none => none
      | some (m', changed) => if changed then strataLoop limit edges f m' else some m'

/-- The stratum number of each rule, or `none` when the rule set does not meet
the stratification condition. Fuel: every pass that changes something raises
at least one stratum by one, and no stratum passes `limit = n + 1`, so
`n * (n + 2) + 1` passes suffice. -/
def stratumNumbers (rules : List Rule) : Option (Array Nat) :=
  let n := rules.length
  strataLoop (n + 1) (dependencyGraph rules) (n * (n + 2) + 1) (Array.replicate n 0)

/-- Draft "Stratification": the layers, lowest first. -/
def stratify (rules : List Rule) : Option (List Layer) :=
  match stratumNumbers rules with
  | none => none
  | some m =>
      let maxS := m.foldl max 0
      let idx := (List.range rules.length)
      some ((List.range (maxS + 1)).map fun s =>
        let rs := idx.filter (fun i => getD m i == s)
        { once := rs.filter (fun i => (rules.getD i default).runOnce)
          general := rs.filter (fun i => !(rules.getD i default).runOnce) })

/-- Draft "Stratification condition": no cycle through a closed dependency. -/
def RuleSet.stratifiable (rs : RuleSet) : Bool := (stratify rs.rules).isSome

end L4Factoidal.SPARQLRL
