/-
L4Factoidal.SPARQLRL.Eval — SPARQL-RL rule set evaluation: the `infer`
operation of the editor's draft, § "Rule Set Evaluation"
(https://w3c.github.io/data-shapes/sparql12-rl/). Issue:
https://github.com/danbri/factoidal/issues/1099.

## The algorithm

As the draft's "Evaluation of a Rule Set": the data blocks join the base
graph `G0` to make the evaluation graph `GE`; then each stratification layer,
lowest first: every run-once rule once, then the general rules to a fixpoint.
The result is the inference graph, `GE` minus `G0`. The data-block triples
are in it (they are inferred, draft "Data Blocks"; the eval tests'
expected results contain them).

`evalSeq` is the draft's `evalRuleElements`, element by element: a triple
pattern joins with the graph, `FILTER` keeps a solution whose expression has
the effective boolean value true (`SPARQL.ebv`, `SPARQL.Expr.evalIn`),
`NOT` keeps a solution when the inner sequence has no solution from it,
`SET` extends a solution and DROPS it when the expression is an error (draft:
"If evaluating the expression in an assignment causes an error, then the
current solution mapping is rejected"), and a group element groups the
solutions of its pattern, started from the restriction of the solution to
the group keys, and aggregates each group with `SPARQL.evalAggregate`
(`COUNT`, `COUNT DISTINCT`, `MIN`, `MAX`, `SUM`). An aggregate error drops
the group. `WHERE DATA` and `NOT DATA` match `G0` only.

Two consequences of following the draft's group-element algorithm as it is
written (the draft marks `evalAggregate` as not finished; no W3C eval test
has a group element yet, so `SPARQLRL/Tests.lean` has the cases):
* the group pattern starts from the restriction of the solution to the group
  keys, so a variable of the enclosing body that is not a key is unbound
  inside the group, although well-formedness lets the pattern mention it;
* a group pattern with no solution gives no group, so no solution: unlike
  SPARQL, `COUNT(*)` over nothing gives no row, not `0`.

## Semi-naive fixpoint for the general rules

The draft's loop evaluates each general rule against the current `GE` until
a pass adds nothing. Here a round evaluates every general rule of the layer
against the `GE` of the round start; the first round is naive, and a later
round evaluates a rule once per top-level triple-pattern element `k`, with
element `k` matched against the triples the previous round added (`Δ`), the
elements before `k` against `GE \ Δ`, and those after `k` against `GE`. So
every solution that uses at least one triple of `Δ` is found once, and no
solution that uses none of them is recomputed. The fixpoint is the same as
the draft's: a general rule has no blank node in its head and no assignment,
so it produces no new terms, and its `NOT` elements depend only on lower
layers (closed dependencies) or on `G0`, so within a layer the general rules
are monotone and the least fixpoint is independent of the order and of when
new triples become visible. A rule whose body has no triple-pattern element,
or that matches `G0` only (`WHERE DATA`), can produce nothing new after the
first round.

## Blank nodes

A blank node of a head template or a data block is replaced by a fresh blank
node for each solution (draft "replaceBlankNodes"). The fresh labels have a
prefix `srl<i>x` that starts no blank-node label of `G0` (`freshPrefix`).
The data blocks of one document share one label scope, as the triples of one
Turtle document do.

## Generalized triples

The grammar allows a literal subject in a data block (`syntax-data-05`), and
a head can put a literal from a solution into the subject position. Such a
triple stays in `GE` and can be matched by rule bodies; the `Graph` that
`infer` returns holds only RDF triples (IRI or blank-node subject, IRI
predicate). A triple term is built only when it is an RDF 1.2 triple term;
a template instance that is not one is not produced.

## Termination

`generalLoop` takes fuel `N^3 + 2`, `N` an upper bound on the number of RDF
terms that can occur in `GE` during the layer (the terms of `GE` and the
constant terms of the heads): general rules produce no new terms, so each
productive round adds a triple over a universe of at most `N^3`. No
`partial def`.
-/
import L4Factoidal.SPARQLRL.Syntax
import L4Factoidal.SPARQL.Query
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- A generalized triple: any term in any position. -/
abbrev T3 := Term × Term × Term

/-- The evaluation graph: a set, an index on each position, and the triples
in insertion order. -/
structure IGraph where
  set : Std.HashSet T3 := {}
  byS : Std.HashMap Term (Array T3) := {}
  byP : Std.HashMap Term (Array T3) := {}
  byO : Std.HashMap Term (Array T3) := {}
  all : Array T3 := #[]

instance : Inhabited IGraph := ⟨{}⟩

def IGraph.contains (g : IGraph) (t : T3) : Bool := g.set.contains t

def IGraph.insert (g : IGraph) (t : T3) : IGraph :=
  if g.set.contains t then g
  else { set := g.set.insert t
         byS := g.byS.insert t.1 ((g.byS.getD t.1 #[]).push t)
         byP := g.byP.insert t.2.1 ((g.byP.getD t.2.1 #[]).push t)
         byO := g.byO.insert t.2.2 ((g.byO.getD t.2.2 #[]).push t)
         all := g.all.push t }

def IGraph.insertAll (g : IGraph) (ts : Array T3) : IGraph := ts.foldl IGraph.insert g

def IGraph.size (g : IGraph) : Nat := g.all.size

def tripleToT3 (t : Triple) : T3 := (t.s.toTerm, .iri t.p, t.o)

def IGraph.ofGraph (g : Graph) : IGraph := g.foldl (fun acc t => acc.insert (tripleToT3 t)) {}

/-- The RDF triple a generalized triple is, if it is one. -/
def t3ToTriple? : T3 → Option Triple
  | (s, .iri p, o) => s.toSubject?.map fun s' => { s := s', p := p, o := o }
  | _ => none

/-- Where a triple pattern is matched: a graph, less an optional graph. -/
structure Src where
  g : IGraph
  excl : Option IGraph := none

/-- The triples that can match a pattern whose positions are ground as given:
the whole triple when all three are, else the shortest index entry. -/
def Src.candidates (src : Src) (s p o : Option Term) : Array T3 :=
  let g := src.g
  let base := match s, p, o with
    | some s, some p, some o => if g.contains (s, p, o) then #[(s, p, o)] else #[]
    | _, _, _ =>
      let opts := [s.map (fun k => g.byS.getD k #[]), p.map (fun k => g.byP.getD k #[]),
                   o.map (fun k => g.byO.getD k #[])].filterMap id
      match opts with
      | [] => g.all
      | a :: rest => rest.foldl (fun m x => if x.size < m.size then x else m) a
  match src.excl with
  | none => base
  | some ex => base.filter (fun t => !ex.contains t)

/-! ## Matching and instantiation -/

/-- Match a pattern term against a term, extending the solution. -/
def matchTerm (b : Binding) : STerm → Term → Option Binding
  | .var v, t =>
      match b.lookup v with
      | some u => if u == t then some b else none
      | none => some (b.bind v t)
  | .iri i, t => if t == .iri i then some b else none
  | .lit l, t => if t == .literal l then some b else none
  | .bnode _, _ => none
  | .triple s p o, .tripleTerm ts tp to =>
      match matchTerm b s ts.toTerm with
      | none => none
      | some b1 =>
          match matchTerm b1 p (.iri tp) with
          | none => none
          | some b2 => matchTerm b2 o to
  | .triple _ _ _, _ => none

/-- Instantiate a template term; `bn` gives the term for a template blank
node. `none` when a variable is unbound or a triple term would not be an
RDF 1.2 triple term. -/
def inst (b : Binding) (bn : String → Term) : STerm → Option Term
  | .var v => b.lookup v
  | .iri i => some (.iri i)
  | .lit l => some (.literal l)
  | .bnode x => some (bn x)
  | .triple s p o =>
      match inst b bn s, inst b bn p, inst b bn o with
      | some s', some (.iri p'), some o' => s'.toSubject?.map fun ss => .tripleTerm ss p' o'
      | _, _, _ => none

/-- A pattern term with every variable bound, as a term. -/
def ground? (b : Binding) (t : STerm) : Option Term :=
  if !t.bnodes.isEmpty then none else inst b (fun x => .bnode x) t

def matchTriple (src : Src) (b : Binding) (tp : STriple) : List Binding :=
  ((src.candidates (ground? b tp.s) (ground? b tp.p) (ground? b tp.o)).foldl (fun acc (s, p, o) =>
    match matchTerm b tp.s s with
    | none => acc
    | some b1 =>
      match matchTerm b1 tp.p p with
      | none => acc
      | some b2 =>
        match matchTerm b2 tp.o o with
        | none => acc
        | some b3 => acc.push b3) #[]).toList

/-! ## Rule elements — draft `evalRuleElements` -/

/-- The fixed inputs of an evaluation. -/
structure Ctx where
  env : EvalEnv := {}
  /-- the base graph, for `WHERE DATA` and `NOT DATA` -/
  g0  : IGraph := {}

def aggResult (env : EvalEnv) (xs : List Binding) : AggFn → EvalResult
  | .count d none => evalAggregate env .count d (.var "*") ⟨[], xs⟩
  | .count d (some a) => evalAggregate env .count d (.var a) ⟨[], xs⟩
  | .min a => evalAggregate env .min false (.var a) ⟨[], xs⟩
  | .max a => evalAggregate env .max false (.var a) ⟨[], xs⟩
  | .sum a => evalAggregate env .sum false (.var a) ⟨[], xs⟩

/-- The output of a group element for one solution `mu`, given the
solutions `sols` of the group pattern (draft: the group-element arm of
`evalRuleElements`). -/
def groupRows (env : EvalEnv) (keys : List String) (aggs : List (String × AggFn))
    (mu : Binding) (sols : List Binding) : List Binding :=
  let keyOf (x : Binding) : List (Option Term) := keys.map (fun k => x.lookup k)
  let groups : List (List (Option Term) × List Binding) := sols.foldl (fun acc x =>
    let k := keyOf x
    if acc.any (fun g => g.1 == k) then acc.map (fun g => if g.1 == k then (g.1, g.2 ++ [x]) else g)
    else acc ++ [(k, [x])]) []
  groups.filterMap fun (k, xs) =>
    let vals : Option Binding := aggs.foldl (fun acc (v, fn) =>
      match acc with
      | none => none
      | some b => (aggResult env xs fn).toTerm?.map (fun t => b ++ [(v, t)])) (some [])
    vals.map fun z =>
      let kb : Binding := (keys.zip k).filterMap fun (v, t?) => t?.map (fun t => (v, t))
      Binding.merge (Binding.merge z kb) mu

mutual
/-- One rule element. `full` is the graph for nested patterns; `sel i` is
where the top-level triple-pattern element number `i` is matched. Returns
the new solution sequence and the next triple-pattern number. -/
def evalElt (cx : Ctx) (full : IGraph) (sel : Nat → Src) (idx : Nat) (seq : List Binding) :
    Elt → List Binding × Nat
  | .triple tp => (seq.flatMap (fun mu => matchTriple (sel idx) mu tp), idx + 1)
  | .filter e _ => (seq.filter (fun mu => ebv (Expr.evalIn cx.env mu e) == some true), idx)
  | .neg ev inner =>
      let g := if ev then full else cx.g0
      (seq.filter (fun mu => (evalSeq cx g (fun _ => ⟨g, none⟩) 0 [mu] inner).1.isEmpty), idx)
  | .assign v e _ =>
      (seq.filterMap (fun mu => (Expr.evalIn cx.env mu e).toTerm?.map (fun t => mu.bind v t)), idx)
  | .group keys pat aggs =>
      (seq.flatMap (fun mu =>
        let mup := mu.filter (fun (v, _) => keys.contains v)
        groupRows cx.env keys aggs mu (evalSeq cx full (fun _ => ⟨full, none⟩) 0 [mup] pat).1), idx)

def evalSeq (cx : Ctx) (full : IGraph) (sel : Nat → Src) (idx : Nat) (seq : List Binding) :
    List Elt → List Binding × Nat
  | [] => (seq, idx)
  | e :: es =>
      let (seq', idx') := evalElt cx full sel idx seq e
      if seq'.isEmpty then ([], idx') else evalSeq cx full sel idx' seq' es
end

/-- The number of top-level triple-pattern elements of a body. -/
def countTriples (body : List Elt) : Nat :=
  body.foldl (fun n e => match e with | .triple _ => n + 1 | _ => n) 0

/-- The solutions of a rule body. `sel` says where each top-level triple
pattern is matched when the rule matches `GE` (`.evaldata`). -/
def evalBody (cx : Ctx) (r : Rule) (ge : IGraph) (sel : Nat → Src) : List Binding :=
  if r.evaldata then (evalSeq cx ge sel 0 [[]] r.body).1
  else (evalSeq cx cx.g0 (fun _ => ⟨cx.g0, none⟩) 0 [[]] r.body).1

def idxOfStr (x : String) : List String → Nat
  | [] => 0
  | y :: ys => if x == y then 0 else idxOfStr x ys + 1

/-- Draft `evalRule`'s head step: each solution instantiates the head, with
each template blank node replaced by a fresh blank node. `ctr` numbers the
fresh blank nodes. -/
def instHead (r : Rule) (pfx : String) (ctr : Nat) (sols : List Binding) : Array T3 × Nat :=
  let labels := addVars [] (r.head.flatMap STriple.bnodes)
  sols.foldl (fun (out, c) mu =>
    let bn (x : String) : Term := .bnode (pfx ++ toString (c + idxOfStr x labels))
    let out := r.head.foldl (fun o t =>
      match inst mu bn t.s, inst mu bn t.p, inst mu bn t.o with
      | some s, some p, some o' => o.push (s, p, o')
      | _, _, _ => o) out
    (out, c + labels.length)) (#[], ctr)

/-! ## Blank-node labels -/

def termBnodeIds : Term → List String
  | .bnode b => [b]
  | .tripleTerm s _ o => (match s with | .bnode b => [b] | _ => []) ++ termBnodeIds o
  | _ => []

/-- The digits after `srl` and before `x`, if the label has that form. -/
def srlIndex? (s : String) : Option Nat :=
  if !"srl".isPrefixOf s then none else
  let ds := (s.toList.drop 3).takeWhile Char.isDigit
  match (s.toList.drop (3 + ds.length)) with
  | 'x' :: _ => if ds.isEmpty then none else (String.ofList ds).toNat?
  | _ => none

/-- A prefix `srl<i>x` that starts none of `ids`. An id starts with at most one
such prefix, so the least `i` not used is found among `ids.length + 1`
candidates. -/
def freshPrefix (ids : List String) : String :=
  let used : Std.HashSet Nat := ids.foldl (fun s id =>
    match srlIndex? id with | some i => s.insert i | none => s) {}
  let i := ((List.range (ids.length + 1)).find? (fun i => !used.contains i)).getD ids.length
  "srl" ++ toString i ++ "x"

/-! ## Rule set evaluation — draft "Evaluation of a Rule Set" -/

/-- An upper bound on the number of terms of `GE` and of the rule heads. -/
def termBound (ge : IGraph) (rules : List Rule) : Nat :=
  3 * ge.size + 3 * (rules.foldl (fun n r => n + r.head.length) 0) + 1

/-- The general rules of one layer to a fixpoint (semi-naive; see the module
header). `delta` is what the previous round added; `first` marks the naive
first round. -/
def generalLoop (cx : Ctx) (pfx : String) (rules : List Rule) :
    Nat → Bool → IGraph → IGraph → Nat → IGraph × Nat
  | 0, _, ge, _, ctr => (ge, ctr)
  | f + 1, first, ge, delta, ctr =>
    let full : Nat → Src := fun _ => ⟨ge, none⟩
    let (out, ctr') := rules.foldl (fun (acc, c) r =>
      let sols :=
        if first then evalBody cx r ge full
        else if !r.evaldata then []
        else (List.range (countTriples r.body)).flatMap fun k =>
          evalBody cx r ge (fun i =>
            if i < k then ⟨ge, some delta⟩ else if i == k then ⟨delta, none⟩ else ⟨ge, none⟩)
      let (ts, c') := instHead r pfx c sols
      (acc ++ ts, c')) (#[], ctr)
    let delta' : IGraph := out.foldl (fun d t => if ge.contains t then d else d.insert t) {}
    if delta'.size == 0 then (ge, ctr')
    else generalLoop cx pfx rules f false (ge.insertAll delta'.all) delta' ctr'

/-- Evaluate the layers over `GE`. -/
def evalLayers (cx : Ctx) (pfx : String) (rules : List Rule) (layers : List Layer)
    (ge : IGraph) (ctr : Nat) : IGraph × Nat :=
  layers.foldl (fun (ge, ctr) layer =>
    -- run-once rules, each exactly once
    let (ge, ctr) := layer.once.foldl (fun (ge, c) i =>
      let r := rules.getD i default
      let (ts, c') := instHead r pfx c (evalBody cx r ge (fun _ => ⟨ge, none⟩))
      (ge.insertAll ts, c')) (ge, ctr)
    -- general rules to a fixpoint
    let gen := layer.general.map (fun i => rules.getD i default)
    if gen.isEmpty then (ge, ctr) else
    let n := termBound ge gen
    generalLoop cx pfx gen (n * n * n + 2) true ge {} ctr) (ge, ctr)

/-- Why `infer` gives no result. -/
inductive InferError where
  | imports (urls : List String)
  | notWellFormed
  | notStratifiable
  deriving Repr, DecidableEq

def InferError.msg : InferError → String
  | .imports us => s!"IMPORTS not resolved (this processor needs a loader): {us}"
  | .notWellFormed => "the rule set is not well-formed"
  | .notStratifiable => "the rule set does not meet the stratification condition"

/-- The data-block triples, with the blank nodes of the document replaced by
fresh ones. -/
def dataTriples (rs : RuleSet) (pfx : String) (ctr : Nat) : Array T3 × Nat :=
  let labels := addVars [] (rs.data.flatMap STriple.bnodes)
  let bn (x : String) : Term := .bnode (pfx ++ toString (ctr + idxOfStr x labels))
  (rs.data.foldl (fun o t =>
    match inst [] bn t.s, inst [] bn t.p, inst [] bn t.o with
    | some s, some p, some o' => o.push (s, p, o')
    | _, _, _ => o) #[], ctr + labels.length)

/-- The evaluation graph after the whole rule set (base graph included), as
generalized triples. -/
def RuleSet.evalGraph (rs : RuleSet) (base : Graph) (env : EvalEnv := {}) :
    Except InferError (IGraph × IGraph) :=
  if !rs.imports.isEmpty then .error (.imports rs.imports)
  else if !rs.wellFormed then .error .notWellFormed
  else match stratify rs.rules with
    | none => .error .notStratifiable
    | some layers =>
      let g0 := IGraph.ofGraph base
      let pfx := freshPrefix (base.flatMap fun t =>
        (match t.s with | .bnode b => [b] | _ => []) ++ termBnodeIds t.o)
      let (d, ctr) := dataTriples rs pfx 0
      let ge := g0.insertAll d
      let (ge, _) := evalLayers { env, g0 } pfx rs.rules layers ge ctr
      .ok (g0, ge)

/-- Draft "Infer": the inference graph, the triples of the evaluation that
are not in the base graph, as an RDF graph (generalized triples left out). -/
def RuleSet.infer (rs : RuleSet) (base : Graph) (env : EvalEnv := {}) :
    Except InferError Graph := do
  let (g0, ge) ← rs.evalGraph base env
  return ge.all.toList.filterMap fun t => if g0.contains t then none else t3ToTriple? t

end L4Factoidal.SPARQLRL
