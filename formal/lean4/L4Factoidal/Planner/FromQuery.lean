/-
Capability-aware planner, KR 2.2: a requirement from a parsed SPARQL query.

https://github.com/danbri/factoidal/issues/801. `Requirement.ofQuery?`
accepts a SELECT query whose WHERE clause is a basic graph pattern (or a
join of basic graph patterns), with no dataset clause, no GROUP BY, no
HAVING, no solution modifier and no trailing VALUES. It returns `none`
for every other shape.

Two `none` cases are open shortfalls, each with an expected-failure case
in `Harness/PlannerTest.lean` naming
https://github.com/danbri/factoidal/issues/801:

* `FILTER`: there is no `RowFilter` made from a SPARQL `Expr`. It needs a
  proof that expression evaluation reads a solution mapping only through
  `Binding.lookup` (the `respects` field of `RowFilter`).
* `GRAPH`: the declared dataset has only a default graph; mappings do not
  give quads.
-/
import L4Factoidal.Planner.Requirement

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- The triple patterns of a WHERE clause that is a basic graph pattern
or a join of them. Recursion is on the nesting of the pattern. -/
def queryPatternBgp? : QueryPattern → Option Bgp
  | .bgp ps   => some ps
  | .empty    => some []
  | .join l r =>
    match queryPatternBgp? l, queryPatternBgp? r with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | _ => none

/-- The projected variables; `none` for a `SELECT (expr AS ?v)` item.
Tail call with an accumulator. -/
def selectVarsGo : List SelectItem → List VarName → Option (List VarName)
  | [], acc => some acc.reverse
  | .var v :: rest, acc => selectVarsGo rest (v :: acc)
  | .expr _ _ :: _, _ => none

def Requirement.ofQuery? (q : Query) : Option Requirement :=
  let m := q.modifier
  if q.dataset.isEmpty && q.groupBy.isNone && q.having.isEmpty && q.postValues.isNone &&
      m.orderBy.isNone && !m.distinct && !m.reduced && m.offset.isNone && m.limit.isNone then
    match q.form, queryPatternBgp? q.pattern with
    | .select .all, some b => some { bgp := b, projection := (bgpVars b).eraseDups }
    | .select (.vars items), some b =>
      (selectVarsGo items []).map (fun vs => { bgp := b, projection := vs })
    | _, _ => none
  else none

end L4Factoidal.Planner
