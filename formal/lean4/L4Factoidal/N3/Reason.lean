/-
L4Factoidal.N3.Reason — forward chaining over N3 rules.

Specification: Notation3 Semantics § "Log Semantics" (W3C N3 Community Group
editor's draft at commit `1d29dea7` of https://github.com/w3c/N3): for a rule
`{ B } log:implies { H }`, under each assignment of the universal variables
for which `B` holds, `H` holds. Built-ins: `N3/Builtins.lean`, and the `log:`
built-ins below, Notation3 Builtin Functions § "log". Design record:
`docs/designissues/2026-10-28-n3.md` § 4. Tracking:
https://github.com/danbri/factoidal/issues/1171 (step 2).

## Rules

A rule is a triple of the store whose predicate is `log:implies` (`=>`), with
graph terms (or `true`, the empty graph) as subject and object, or a triple
with `log:isImpliedBy` (`<=`), read the other way round. Rules are read from
the store at the start of each round, so a rule that a rule concludes takes
part in the next round.

The variables of a rule body are its quick variables and the blank nodes that
occur directly in the body graph term (they are its existential variables;
matching them as variables is what makes `{ _:x :p :o } => ...` hold when some
`:p :o` triple exists). The blank nodes that occur directly in the head graph
term are existential in the head: each firing gives them fresh labels.

## The body solver

The body triples are solved one at a time, in the order written, with this
exception: a built-in whose input is still a variable is tried after the
others (`BResult.notReady`). A triple that is not a built-in is matched with
the store triples of the same predicate (`unifyTriple`). A rule fires once for
each assignment of the variables its head uses (`firingKey`, `RState.fired`),
so a rule with an existential head does not fire again for the same values.
An N3 list has `rdf:first` and `rdf:rest` (`listAxiom`).

## Rounds

A round fires every rule against the store of the round start (the triples a
round adds are visible from the next round). `chain` repeats rounds until a
round adds nothing, or stops at a bound (`maxRounds` rounds, `maxTriples`
store triples) and says so. The bound exists because an N3 rule set may have
no finite closure (`{ ?x a :N } => { [ :succ ?x ] a :N }`).

## The Datalog fragment and SPARQL-RL

For a rule set with no built-in, no list, no nested graph term and no head
blank node, this is the semi-naive closure of `SPARQLRL/Eval.lean` computed
naively. Theorem 4b of the design record (the two closures are equal) is
step 4b of the tracker.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.N3.Builtins

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- A rule (module header). `bvars`: the body blank nodes, variables of the
body; `hvars`: the head blank nodes, fresh per firing. -/
structure N3Rule where
  body  : List N3Triple
  head  : List N3Triple
  bvars : BVars
  hvars : List BNodeId
  id    : String

def tripleDirectBnodes (t : N3Triple) : List BNodeId :=
  t.1.directBnodes ++ t.2.1.directBnodes ++ t.2.2.directBnodes

/-- The triples of a graph term, or of `true` (the empty graph). -/
def graphTriples? : N3Term → Option (List N3Triple)
  | .graph ts => some ts
  | .lit l => if l.val == trueLit.val then some [] else none
  | _ => none

def dedupStrings (xs : List String) : List String := sortDedup xs

/-- The rules of a graph (module header). -/
def rulesOf (g : List N3Triple) : List N3Rule :=
  let mk (s o : N3Term) : Option N3Rule :=
    match graphTriples? s, graphTriples? o with
    | some b, some h =>
        some { body := b, head := h,
               bvars := dedupStrings (b.flatMap tripleDirectBnodes),
               hvars := dedupStrings (h.flatMap tripleDirectBnodes),
               id := tripleKey (fun x => "_:" ++ x) (s, .iri logImplies, o) }
    | _, _ => none
  g.filterMap fun (s, p, o) =>
    match p with
    | .iri i => if i == logImplies then mk s o else if i == logIsImpliedBy then mk o s else none
    | _ => none

/-! ## The store -/

def predKey : N3Term → String
  | .iri i => i.val
  | _ => ""

def keyOf (t : N3Triple) : String := tripleKey (fun x => "_:" ++ x) (t.1.normalize, t.2.1.normalize, t.2.2.normalize)

/-- A set of triples in insertion order, with an index by predicate. -/
structure Store where
  triples : Array N3Triple := #[]
  keys    : Std.HashSet String := {}
  byPred  : Std.HashMap String (Array N3Triple) := {}
  /-- By predicate and subject (`cmpKey`), for an IRI predicate. -/
  byPS    : Std.HashMap String (Array N3Triple) := {}
  others  : Array N3Triple := #[]

/-- Add a triple; `false` when the store has it already. -/
def Store.add (st : Store) (t : N3Triple) : Store × Bool :=
  let k := keyOf t
  if st.keys.contains k then (st, false)
  else
    let pk := predKey t.2.1
    let st1 := { st with triples := st.triples.push t, keys := st.keys.insert k }
    if pk.isEmpty then ({ st1 with others := st1.others.push t }, true)
    else
      let psk := pk ++ " " ++ cmpKey t.1
      ({ st1 with byPred := st1.byPred.insert pk ((st1.byPred.getD pk #[]).push t),
                  byPS := st1.byPS.insert psk ((st1.byPS.getD psk #[]).push t) }, true)

def Store.ofList (g : List N3Triple) : Store := g.foldl (fun st t => (st.add t).1) {}

/-- The store triples a pattern triple can match: by predicate and subject
when both are known (`ground`: the subject has no variable and is not a graph
term), by predicate when the predicate is an IRI, else all. -/
def Store.candidates (st : Store) (s p : N3Term) (ground : Bool) : Array N3Triple :=
  match p with
  | .iri i =>
      if ground then st.byPS.getD (i.val ++ " " ++ cmpKey s) #[] ++ st.others
      else st.byPred.getD i.val #[] ++ st.others
  | _ => st.triples

/-! ## `log:` built-ins (Builtins § "log") -/

def logNsStr : String := "http://www.w3.org/2000/10/swap/log#"

/-- `log:includes` (Builtins § log:includes): the subject graph term includes
the object graph term, its quick variables and its own blank nodes matched as
variables. -/
def logIncludes (bv : BVars) (s o : N3Term) (σ : Subst) : Option (List Subst) :=
  match graphTriples? s, graphTriples? o with
  | some st, some ot =>
      let obv := bv ++ ot.flatMap tripleDirectBnodes
      some (includesMatch obv ot st σ)
  | _, _ => none

/-- A literal from a lexical form and a datatype IRI or a language tag. -/
def mkLit? (lex : String) (dt : Option WfIri) (lang : Option String) : Option N3Term :=
  let l : Literal := match dt, lang with
    | _, some tag => { lexicalForm := lex, datatype := rdfLangString, langTag := some tag.toLower, direction := none }
    | some d, none => { lexicalForm := lex, datatype := d, langTag := none, direction := none }
    | none, none => { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none }
  match mkLiteral 0 l with
  | .ok wl => some (.lit wl)
  | .error _ => none

/-! ## Rounds -/

/-- Reasoning bounds (module header). -/
def maxRounds : Nat := 200
def maxTriples : Nat := 200000

/-- The most steps one rule body may take in one round. -/
def solveSteps : Nat := 10000000

/-- The first triple of `pending` whose solutions are known now, with its
solutions and the other triples in order. A tail call per triple tried; the
rest of the list is rebuilt only for the triple chosen. -/
def firstReady (try? : N3Triple → Option (List Subst)) :
    List N3Triple → List N3Triple → Option (List Subst × List N3Triple)
  | [], _ => none
  | t :: rest, beforeRev =>
      match try? t with
      | some sols => some (sols, beforeRev.reverse ++ rest)
      | none => firstReady try? rest (t :: beforeRev)

/-- Reasoner state. `added`: the triples the rules concluded, in order. -/
structure RState where
  store : Store
  added : Array N3Triple := #[]
  fired : Std.HashSet String := {}
  fresh : Nat := 0
  /-- A bound stopped the run. -/
  limit : Bool := false

/-- The variable keys a rule head uses: its quick variables and the body
blank nodes that occur in it. -/
def headVarKeys (r : N3Rule) : List String :=
  let vs := r.head.flatMap fun (s, p, o) => s.vars ++ p.vars ++ o.vars
  let bs := r.head.flatMap fun (s, p, o) => s.allBnodes ++ p.allBnodes ++ o.allBnodes
  vs.map ("?" ++ ·) ++ (bs.filter r.bvars.contains).map ("_:" ++ ·)

/-- The firing key: the rule and the values of the variables its head uses.
Two solutions that agree on those give the same conclusions up to the names of
the head's fresh blank nodes, so the rule fires once for them (a lean result:
`{ ?x a :S } => { [] a :G }` concludes one `[] a :G`). -/
def firingKey (r : N3Rule) (σ : Subst) : String :=
  let used := headVarKeys r
  r.id ++ "\n" ++ String.intercalate "\n"
    (sortDedup ((σ.filter fun (k, _) => used.contains k).map fun (k, v) => k ++ "=" ++ cmpKey v))

/-- Fire one rule under one substitution. -/
def fire (pfx : String) (r : N3Rule) (rs : RState) (σ : Subst) : RState :=
  let k := firingKey r σ
  if rs.fired.contains k then rs
  else
    let (ren, n) := r.hvars.foldl (fun (acc : Subst × Nat) b =>
      (("_:" ++ b, .bnode (pfx ++ "sk" ++ toString acc.2)) :: acc.1, acc.2 + 1)) ([], rs.fresh)
    let rs1 := { rs with fired := rs.fired.insert k, fresh := n }
    r.head.foldl (fun acc t =>
      let t1 := substT r.hvars ren (substT r.bvars σ t)
      let (st1, isNew) := acc.store.add t1
      if isNew then { acc with store := st1, added := acc.added.push t1 } else acc) rs1

/-- The `log:` built-ins that need no reasoning (Builtins § "log"), on a
substituted triple named `name` (the local name): `none` when an input is
still a variable, else the solutions; a `log:` name that is not one of them is
matched with the store (`matchStore`). -/
def logBuiltin (bv : BVars) (name : String) (s o : N3Term) (σ : Subst)
    (matchStore : List Subst) : Option (List Subst) :=
  match name with
    | "equalTo" =>
        if !hasVar bv termFuel o then some (unify bv termFuel s o σ)
        else if !hasVar bv termFuel s then some (unify bv termFuel o s σ)
        else none
    | "notEqualTo" =>
        if hasVar bv termFuel s || hasVar bv termFuel o then none
        else some (if termEq s o then [] else [σ])
    | "includes" =>
        if (varKey bv s).isSome then none
        else some ((logIncludes bv s o σ).getD [])
    | "notIncludes" =>
        if (varKey bv s).isSome then none
        else some (match logIncludes bv s o σ with
          | some [] => [σ]
          | _ => [])
    | "conjunction" =>
        match s with
        | .list xs =>
            if xs.any (hasVar bv termFuel) then none
            else match xs.mapM graphTriples? with
              | some gs => some (giveValue bv o (.graph (Store.ofList gs.flatten).triples.toList) σ)
              | none => some []
        | _ => if (varKey bv s).isSome then none else some []
    | "uri" =>
        match s, o with
        | .iri i, _ => some (giveValue bv o (strLit i.val) σ)
        | _, .lit l =>
            if (varKey bv s).isSome then
              match mkIri 0 l.val.lexicalForm with
              | .ok wi => some (unify bv termFuel s (.iri wi) σ)
              | .error _ => some []
            else some []
        | _, _ => if (varKey bv s).isSome then none else some []
    | "dtlit" =>
        match s, o with
        | .list [.lit lex, .iri dt], _ =>
            match mkLit? lex.val.lexicalForm (some dt) none with
            | some v => some (giveValue bv o v σ)
            | none => some []
        | _, .lit l =>
            if l.val.langTag.isSome then some []
            else some (unify bv termFuel s (.list [strLit l.val.lexicalForm, .iri l.val.datatype]) σ)
        | _, _ => none
    | "langlit" =>
        match s, o with
        | .list [.lit lex, .lit tag], _ =>
            match mkLit? lex.val.lexicalForm none (some tag.val.lexicalForm) with
            | some v => some (giveValue bv o v σ)
            | none => some []
        | _, .lit l =>
            match l.val.langTag with
            | some tag => some (unify bv termFuel s (.list [strLit l.val.lexicalForm, strLit tag]) σ)
            | none => some []
        | _, _ => none
    | "semantics" | "content" | "parsedAsN3" | "outputString" | "racine" =>
        -- A retrieval or an output side effect: refused in this layer (module
        -- header of `N3/Builtins.lean`).
        some []
    | _ => some matchStore

mutual

/-- One body triple: the substitutions under which it holds, or `none` when it
is a built-in whose input is still a variable. `depth` bounds the nesting of
`log:conclusion`. -/
def solveOne (depth : Nat) (st : Store) (bv : BVars) (t : N3Triple) (σ : Subst) :
    Option (List Subst) :=
  let (s, p, o) := substT bv σ t
  let pk := predKey p
  let matchStore : List Subst :=
    ((st.candidates s p (!hasVar bv termFuel s && !(s matches .graph _))).toList.flatMap fun u =>
      unifyTriple bv termFuel (s, p, o) u σ).take maxSolutions
  if pk == logNsStr ++ "conclusion" then
    match depth, graphTriples? s with
        | d + 1, some g =>
            let rs := chain d maxRounds false { store := Store.ofList g }
            if rs.limit then some [] else some (giveValue bv o (.graph rs.store.triples.toList) σ)
        | _, _ => if (varKey bv s).isSome then none else some []
  else if pk.startsWith logNsStr then
    logBuiltin bv (pk.drop logNsStr.length |>.toString) s o σ matchStore
  else
    match evalBuiltin bv pk s o σ with
    | .notBuiltin => some matchStore
    | .notReady => none
    | .sols l => some l
termination_by (depth, 0, 0)

/-- Solve a rule body (module header): a worklist of partial solutions, each
with the body triples it has not solved yet; a tail call per step. Gives the
solutions and `true` when a bound stopped it (`maxSolutions` solutions, or
`fuel` steps), which `chain` reports as a limit, never as a complete result. -/
def solveBody (depth : Nat) (st : Store) (bv : BVars) (fuel : Nat)
    (work : List (Subst × List N3Triple)) (out : Array Subst) : Array Subst × Bool :=
  match fuel with
  | 0 => (out, !work.isEmpty)
  | f + 1 =>
    match work with
    | [] => (out, false)
    | (σ, []) :: rest =>
        if out.size ≥ maxSolutions then (out, true)
        else solveBody depth st bv f rest (out.push σ)
    | (σ, pending) :: rest =>
        let chosen := firstReady (fun t => solveOne depth st bv t σ) pending []
        match chosen with
        | none => solveBody depth st bv f rest out
        | some (sols, rem) => solveBody depth st bv f (sols.map (·, rem) ++ rest) out
termination_by (depth, 1, fuel)

/-- Rounds (module header). `once`: one round only (cwm `--rules`). -/
def chain (depth : Nat) (rounds : Nat) (once : Bool) (rs : RState) : RState :=
  match rounds with
  | 0 => { rs with limit := true }
  | n + 1 =>
      let rules := rulesOf rs.store.triples.toList
      let snap := rs.store
      let before := rs.added.size
      let pfx := "n3r" ++ toString depth ++ "x"
      let rs1 := rules.foldl (fun acc r =>
        let (sols, cut) := solveBody depth snap r.bvars solveSteps [([], r.body)] #[]
        let acc1 := sols.foldl (fire pfx r) acc
        if cut then { acc1 with limit := true } else acc1) rs
      if rs1.limit then rs1
      else if rs1.store.triples.size > maxTriples then { rs1 with limit := true }
      else if rs1.added.size == before || once then rs1
      else chain depth n once rs1
termination_by (depth, 2, rounds)

end

/-- What a reasoning run outputs (the N3 suite's `test:options`, the cwm
command-line options of the same names). -/
structure ReasonOptions where
  /-- `test:think`: rounds to a fixpoint. Otherwise one round (`test:rules`). -/
  think       : Bool := true
  /-- `test:conclusions`: output the concluded triples only. -/
  conclusions : Bool := false
  /-- `test:data`: output only triples with no graph term and no variable. -/
  data        : Bool := false

/-- A triple with no graph term and no quick variable at any depth. -/
def isPlainTriple (t : N3Triple) : Bool :=
  let plain : N3Term → Bool := fun x => x.vars.isEmpty && !(x.key (fun _ => "") |>.contains '{')
  plain t.1 && plain t.2.1 && plain t.2.2

/-- The result of reasoning over a graph, and whether a bound stopped it. -/
def reason (opts : ReasonOptions) (g : N3Graph) : N3Graph × Bool :=
  let rs := chain 4 maxRounds (!opts.think) { store := Store.ofList g }
  let out := if opts.conclusions then rs.added.toList else rs.store.triples.toList
  ((if opts.data then out.filter isPlainTriple else out), rs.limit)

end L4Factoidal.N3
