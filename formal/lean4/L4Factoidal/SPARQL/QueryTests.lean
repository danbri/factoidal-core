/-
L4Factoidal.SPARQL.QueryTests — compile-time executable checks for the
wider graph-pattern set, the query forms, the solution modifiers, and
aggregation.

Every `#guard` here is evaluated during `lake build`, so a wrong answer
is a BUILD FAILURE. As in `ExprTests.lean`, these are UNIT checks of
the semantics, not a conformance score: this port has no SPARQL parser
and no manifest reader, so it cannot claim a W3C result (iron rule #6).
Several cases are ported from the F* tree's own regression tests —
`tests/unit/lateral_unit.ml`, `tests/unit/lateral_service_unit.ml`, and
`tests/local/sparql/lateral_topn_per_key.rq` — with their data and
expected rows carried over; those are marked at the case.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.Tests

namespace L4Factoidal.SPARQL.QueryTests

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ### Fixtures -/

def iriQ (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def pType   : WfIri := iriQ "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def pLabel  : WfIri := iriQ "https://example.org/label"
def pAge    : WfIri := iriQ "https://example.org/age"
def pVal    : WfIri := iriQ "https://example.org/val"
def pKnows  : WfIri := iriQ "https://example.org/knows"
def cPerson : WfIri := iriQ "https://example.org/Person"
def iAlice  : WfIri := iriQ "https://example.org/alice"
def iBob    : WfIri := iriQ "https://example.org/bob"
def iCarol  : WfIri := iriQ "https://example.org/carol"
def iDave   : WfIri := iriQ "https://example.org/dave"
def iZed    : WfIri := iriQ "https://example.org/zed"
def epOne   : WfIri := iriQ "https://example.org/endpoint1"
def epTwo   : WfIri := iriQ "https://example.org/endpoint2"
def epNone  : WfIri := iriQ "https://example.org/nowhere"
def gOne    : WfIri := iriQ "https://example.org/g1"
def gTwo    : WfIri := iriQ "https://example.org/g2"

def tr (s : WfIri) (p : WfIri) (o : Term) : Triple :=
  { s := .iri s, p := p, o := o }

def sLit (s : String) : Term := .literal (Literal.string s)
def nLit (s : String) : Term := .literal (mkTypedLiteral s xsdInteger)

/-- alice and bob are labelled People; carol is a Person with no
label — the F* `lateral_unit.ml` graph, plus ages. -/
def gMain : Graph :=
  [ tr iAlice pType (.iri cPerson),
    tr iBob   pType (.iri cPerson),
    tr iCarol pType (.iri cPerson),
    tr iAlice pLabel (sLit "aaa"),
    tr iBob   pLabel (sLit "bbb"),
    tr iAlice pLabel (sLit "aab"),
    tr iAlice pAge (nLit "30"),
    tr iBob   pAge (nLit "25") ]

/-- The same graph without carol — `lateral_unit.ml`'s cases (a)–(d). -/
def gNoCarol : Graph :=
  [ tr iAlice pType (.iri cPerson),
    tr iBob   pType (.iri cPerson),
    tr iAlice pLabel (sLit "aaa"),
    tr iBob   pLabel (sLit "bbb") ]

/-- Values for the aggregate cases: two under `:a`, one under `:b`. -/
def gNums : Graph :=
  [ tr iAlice pVal (nLit "1"),
    tr iAlice pVal (nLit "2"),
    tr iBob   pVal (nLit "3") ]

/-- A chain for property paths: alice → bob → carol. -/
def gChain : Graph :=
  [ tr iAlice pKnows (.iri iBob),
    tr iBob   pKnows (.iri iCarol),
    tr iAlice pLabel (sLit "aaa") ]

def dsMain : Dataset := { default := gNoCarol, named := [] }
def dsNums : Dataset := { default := gNums, named := [] }
def dsChain : Dataset := { default := gChain, named := [] }

/-- A dataset whose default graph is empty and whose two named graphs
hold one label each — the §18.6 GRAPH fixture. -/
def dsNamed : Dataset :=
  { default := []
    named := [ { name := .iri gOne, graph := [tr iAlice pLabel (sLit "aaa")] },
               { name := .iri gTwo, graph := [tr iBob pLabel (sLit "bbb")] } ] }

/-- Two SERVICE endpoints, one holding the labels and one holding
carol — `lateral_service_unit.ml`'s remote snapshots. -/
def envSvc : EvalEnv :=
  { services := [ (epOne.val, [tr iAlice pLabel (sLit "aaa"),
                               tr iBob   pLabel (sLit "bbb")]),
                  (epTwo.val, [tr iCarol pLabel (sLit "ccc")]) ] }

/-! ### Pattern-building shorthands -/

def tpv (s : VarName) (p : WfIri) (o : PatternTerm) : TriplePattern :=
  { s := .var s, p := .iri p, o := o }

def tpi (s : WfIri) (p : WfIri) (o : PatternTerm) : TriplePattern :=
  { s := .iri s, p := .iri p, o := o }

/-- `?s a :Person`. -/
def pPersons : QueryPattern := .bgp [tpv "s" pType (.iri cPerson)]
/-- `?s :label ?label`. -/
def pLabels : QueryPattern := .bgp [tpv "s" pLabel (.var "label")]

def qAll (p : QueryPattern) : Query := mkQuery (.select .all) p

/-! ### Runners and readouts -/

def rows (ds : Dataset) (q : Query) : SolutionSeq := (evalSelect emptyEnv ds q).2
def hdr  (ds : Dataset) (q : Query) : List VarName := (evalSelect emptyEnv ds q).1
def rowsIn (env : EvalEnv) (ds : Dataset) (q : Query) : SolutionSeq :=
  (evalSelect env ds q).2

/-- One column, rendered as plain strings so the expectations read
like result rows. An unbound cell is the empty string. -/
def col (v : VarName) (omega : SolutionSeq) : List String :=
  omega.map (fun mu =>
    match mu.lookup v with
    | some (.iri i)     => i.val
    | some (.literal l) => l.val.lexicalForm
    | some (.bnode b)   => "_:" ++ b
    | _                 => "")

/-- Short local names, so the expected rows stay readable. -/
def shortName (s : String) : String :=
  if strStartsWith s "https://example.org/" then String.ofList (s.toList.drop 20) else s

def colS (v : VarName) (omega : SolutionSeq) : List String :=
  (col v omega).map shortName

/-! ## §18.6 GRAPH — named-graph selection -/

-- GRAPH <iri> evaluates its pattern against exactly that graph.
#guard colS "label" (rows dsNamed (qAll (.graph (.iri gOne) pLabels))) == ["aaa"]
#guard colS "label" (rows dsNamed (qAll (.graph (.iri gTwo) pLabels))) == ["bbb"]
#guard colS "s" (rows dsNamed (qAll (.graph (.iri gOne) pLabels))) == ["alice"]
-- An IRI the dataset does not name contributes no solutions.
#guard rows dsNamed (qAll (.graph (.iri epNone) pLabels)) == []
-- The default graph is NOT searched by GRAPH.
#guard rows { default := gNoCarol, named := [] }
         (qAll (.graph (.iri gOne) pLabels)) == []
-- GRAPH ?g iterates every named graph, binding ?g to its name.
#guard (rows dsNamed (qAll (.graph (.var "g") pLabels))).length == 2
#guard colS "g" (rows dsNamed (qAll (.graph (.var "g") pLabels))) == ["g1", "g2"]
#guard colS "label" (rows dsNamed (qAll (.graph (.var "g") pLabels))) == ["aaa", "bbb"]
-- A graph-name binding that CONFLICTS with the inner pattern's own
-- binding of ?g drops the row (the §18.6 compatibility check).
#guard rows dsNamed
    (qAll (.graph (.var "g")
      (.join pLabels (.values ["g"] [[some (.iri epNone)]])))) == []

/-! ## §18.6 BIND -/

-- BIND over the empty pattern produces exactly one row.
#guard colS "n" (rows dsMain
    (qAll (.bind (.arith .add (.numericLit 1) (.numericLit 1)) "n" .empty))) == ["2"]
-- BIND extends every row of its sub-pattern.
#guard (rows dsMain (qAll (.bind (.numericLit 7) "n" pPersons))).length == 2
#guard colS "n" (rows dsMain (qAll (.bind (.numericLit 7) "n" pPersons))) == ["7", "7"]
-- An expression ERROR leaves the variable unbound rather than
-- dropping the row (§18.2.4.2).
#guard colS "n" (rows dsMain (qAll (.bind (.var "nosuch") "n" pPersons))) == ["", ""]
-- BIND never overwrites a variable the pattern already bound.
#guard colS "s" (rows dsMain (qAll (.bind (.iri iZed) "s" pPersons))) == ["alice", "bob"]

/-! ## §10.2 VALUES, including UNDEF -/

#guard (rows dsMain (qAll (.values ["x"] [[some (.iri iAlice)], [some (.iri iBob)]]))).length == 2
#guard colS "x" (rows dsMain (qAll (.values ["x"] [[some (.iri iAlice)], [some (.iri iBob)]])))
         == ["alice", "bob"]
-- UNDEF leaves that cell unbound in that row, and only that row.
#guard colS "y" (rows dsMain
    (qAll (.values ["x", "y"] [[some (.iri iAlice), some (sLit "aaa")],
                               [some (.iri iBob), none]]))) == ["aaa", ""]
-- An all-UNDEF row is the empty solution mapping — one row, no
-- bindings.
#guard rows dsMain (qAll (.values ["x"] [[none]])) == [[]]
-- VALUES joins with a pattern, restricting it.
#guard colS "label" (rows dsMain
    (qAll (.join pLabels (.values ["s"] [[some (.iri iAlice)]])))) == ["aaa"]
-- An UNDEF cell imposes no restriction on the join.
#guard (rows dsMain (qAll (.join pLabels (.values ["s"] [[none]])))).length == 2

/-! ## LATERAL — correlated evaluation

Cases (a)–(e) are the F* tree's `tests/unit/lateral_unit.ml` §5
end-to-end block, with its graph and its expected rows. -/

-- (a) A plain correlated BGP: LATERAL degenerates to a join, 2 rows,
-- each subject paired with its OWN label.
#guard colS "s" (rows dsMain (qAll (.lateral pPersons pLabels))) == ["alice", "bob"]
#guard colS "label" (rows dsMain (qAll (.lateral pPersons pLabels))) == ["aaa", "bbb"]
-- (b) A sub-SELECT projecting only ?label MASKS the outer ?s, so the
-- inner query runs unconstrained for every outer row: 2 × 2 = 4 rows.
#guard (rows dsMain (qAll (.lateral pPersons
    (.subSelect (mkQuery (.select (.vars [.var "label"])) pLabels))))).length == 4
-- (c) `SELECT *` projects ?s too, so the outer row IS substituted in
-- and the correlation is back: 2 rows.
#guard (rows dsMain (qAll (.lateral pPersons
    (.subSelect (qAll pLabels))))).length == 2
#guard colS "label" (rows dsMain (qAll (.lateral pPersons
    (.subSelect (qAll pLabels))))) == ["aaa", "bbb"]
-- (d) An empty LHS means the RHS is never reached.
#guard rows dsMain (qAll (.lateral (.bgp [tpv "s" pType (.iri iZed)]) pLabels)) == []
-- (e) LATERAL is inner-join shaped: a Person with no label
-- contributes ZERO rows, not a null row. (carol is in `gMain`.)
#guard (rows { default := gMain, named := [] }
    (qAll (.lateral pPersons pLabels))).length == 3
#guard !((colS "s" (rows { default := gMain, named := [] }
    (qAll (.lateral pPersons pLabels)))).contains "carol")
-- The Jena "top-N per key" query, ported from
-- tests/local/sparql/lateral_topn_per_key.rq: one label per subject,
-- chosen by ORDER BY + LIMIT 1 INSIDE the LATERAL sub-SELECT.
-- `SELECT *` is required — see case (b) for the masked contrast.
def qTopN : Query :=
  qAll (.lateral pPersons
    (.subSelect (mkQuery (.select .all) pLabels
      (modifier := { orderBy := some [.asc (.var "label")], limit := some 1 }))))
#guard (rows { default := gMain, named := [] } qTopN).length == 2
#guard colS "s" (rows { default := gMain, named := [] } qTopN) == ["alice", "bob"]
-- alice has both "aaa" and "aab"; ORDER BY picks the smaller.
#guard colS "label" (rows { default := gMain, named := [] } qTopN) == ["aaa", "bbb"]
-- The same sub-SELECT under a plain JOIN applies LIMIT GLOBALLY, so
-- only one row survives in total — the contrast LATERAL exists for.
#guard (rows { default := gMain, named := [] }
    (qAll (.join pPersons
      (.subSelect (mkQuery (.select .all) pLabels
        (modifier := { orderBy := some [.asc (.var "label")], limit := some 1 })))))).length == 1
-- An empty RHS per row yields no rows at all
-- (tests/local/sparql/lateral_empty_rhs_per_row.rq).
#guard rows dsMain (qAll (.lateral pPersons (.bgp [tpv "s" pKnows (.var "k")]))) == []
-- A RHS that REASSIGNS the correlated name SHADOWS it: `?s` inside
-- that sub-SELECT is a fresh, deeper-scoped variable, so the outer
-- row's `?s` is NOT substituted in and the sub-SELECT runs
-- uncorrelated (2 rows for every outer row). The merge's §18.3
-- compatibility check then keeps only the rows whose `?s` agrees, so
-- 2 × 2 candidate merges collapse back to 2 rows.
#guard (rows dsMain (qAll (.lateral pPersons
    (.subSelect (mkQuery (.select .all)
      (.bind (.iri iZed) "s" pLabels)))))).length == 2
-- The shadowing is visible when the reassigned value CONFLICTS with
-- every outer row: nothing merges.
#guard rows dsMain (qAll (.lateral pPersons
    (.subSelect (mkQuery (.select .all) (.values ["s"] [[some (.iri iZed)]]))))) == []

/-! ## SERVICE — SPARQL 1.1 Federated Query §2

Cases from the F* tree's `tests/unit/lateral_service_unit.ml`. -/

-- A registered endpoint: the inner pattern is evaluated against the
-- remote graph, not the local one.
#guard colS "label" (rowsIn envSvc { default := [], named := [] }
    (qAll (.service epOne false pLabels))) == ["aaa", "bbb"]
#guard colS "label" (rowsIn envSvc { default := [], named := [] }
    (qAll (.service epTwo false pLabels))) == ["ccc"]
-- SERVICE SILENT to an UNREGISTERED endpoint yields one EMPTY
-- solution mapping, so outer rows survive unextended.
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.service epNone true pLabels)) == [[]]
#guard colS "s" (rowsIn envSvc dsMain
    (qAll (.join pPersons (.service epNone true pLabels)))) == ["alice", "bob"]
-- Non-SILENT to an unregistered endpoint: the rows of `evalSelect` are
-- empty, and the query's answer is the §2.3 error (the
-- `Query.serviceFailure` guards below).
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.service epNone false pLabels)) == []
#guard rowsIn envSvc dsMain (qAll (.join pPersons (.service epNone false pLabels))) == []
-- LATERAL over SERVICE: each outer row correlates into the remote
-- pattern.
#guard colS "label" (rowsIn envSvc dsMain
    (qAll (.lateral pPersons (.service epOne false pLabels)))) == ["aaa", "bbb"]
-- SERVICE ?v: the endpoint comes from a binding, so each row is
-- dispatched to its OWN endpoint.
#guard colS "label" (rowsIn envSvc { default := [], named := [] }
    (qAll (.join (.values ["ep"] [[some (.iri epOne)], [some (.iri epTwo)]])
                 (.serviceVar "ep" false pLabels)))) == ["aaa", "bbb", "ccc"]
-- An UNBOUND SERVICE ?v outside a join: SILENT gives one empty row,
-- non-SILENT gives none.
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.serviceVar "ep" true pLabels)) == [[]]
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.serviceVar "ep" false pLabels)) == []
-- A bound-but-UNREGISTERED endpoint: SILENT keeps the outer row,
-- non-SILENT drops it.
#guard colS "ep" (rowsIn envSvc { default := [], named := [] }
    (qAll (.join (.values ["ep"] [[some (.iri epNone)]])
                 (.serviceVar "ep" true pLabels)))) == ["nowhere"]
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.join (.values ["ep"] [[some (.iri epNone)]])
                 (.serviceVar "ep" false pLabels))) == []
-- An endpoint variable bound to a LITERAL is not dispatchable.
#guard rowsIn envSvc { default := [], named := [] }
    (qAll (.join (.values ["ep"] [[some (sLit "not-an-iri")]])
                 (.serviceVar "ep" false pLabels))) == []

/-! ### A failed SERVICE call fails the query — Federated Query §2.3, §3.2

https://github.com/danbri/factoidal/issues/717. `failIn` is the error
the query answers; `none` means the query answers the rows above. Each
error case is beside the same query with SILENT (no error) or with a
registered endpoint (no error), so an evaluator that always fails, or
never fails, breaks the build. -/

def failIn (env : EvalEnv) (ds : Dataset) (q : Query) : Option ServiceFailure :=
  q.serviceFailure env ds

def dsEmpty : Dataset := { default := [], named := [] }

-- Fixed endpoint, unregistered: error without SILENT, none with it.
#guard failIn envSvc dsEmpty (qAll (.service epNone false pLabels)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsEmpty (qAll (.service epNone true pLabels)) == none
-- Registered endpoint: no error, with or without SILENT.
#guard failIn envSvc dsEmpty (qAll (.service epOne false pLabels)) == none
-- Joined with local rows: the error is the answer, the rows are not.
#guard failIn envSvc dsMain (qAll (.join pPersons (.service epNone false pLabels))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.join pPersons (.service epNone true pLabels))) == none
-- Under OPTIONAL and UNION the call is still made, so it still fails.
#guard failIn envSvc dsMain (qAll (.leftJoin pPersons (.service epNone false pLabels)
    (.boolLit true))) == some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.union pPersons (.service epNone false pLabels))) ==
  some (.unreachable epNone.val)
-- The first failure in evaluation order is the one reported.
#guard failIn envSvc dsEmpty (qAll (.join (.service epNone false pLabels)
    (.service (iriQ "https://example.org/other") false pLabels))) ==
  some (.unreachable epNone.val)
-- A nested SERVICE without SILENT inside a reachable endpoint's body
-- fails the outer call (§3.2), and the outer call has no SILENT here,
-- so the query fails. (Outer SILENT: the guards in the issue 735
-- section below.)
#guard failIn envSvc dsEmpty (qAll (.service epOne false
    (.join pLabels (.service epNone false pLabels)))) == some (.unreachable epNone.val)
#guard failIn envSvc dsEmpty (qAll (.service epOne false
    (.join pLabels (.service epNone true pLabels)))) == none
-- GRAPH ?g evaluates its body once per named graph: with no named graph
-- the SERVICE inside is never invoked, so nothing fails.
#guard failIn envSvc dsEmpty (qAll (.graph (.var "g") (.service epNone false pLabels))) == none
#guard failIn envSvc { default := [], named := [{ name := .iri gOne, graph := [] }] }
    (qAll (.graph (.var "g") (.service epNone false pLabels))) == some (.unreachable epNone.val)
-- SERVICE ?v (§4): one invocation per solution. Every endpoint
-- registered: no error.
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)], [some (.iri epTwo)]])
                 (.serviceVar "ep" false pLabels))) == none
-- One solution names an unregistered endpoint: error without SILENT,
-- none with it.
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)], [some (.iri epNone)]])
                 (.serviceVar "ep" false pLabels))) == some (.unreachable epNone.val)
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)], [some (.iri epNone)]])
                 (.serviceVar "ep" true pLabels))) == none
-- No solution: no invocation, no error.
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] []) (.serviceVar "ep" false pLabels))) == none
-- `?v` bound to a literal, or unbound: no endpoint to invoke.
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (sLit "not-an-iri")]])
                 (.serviceVar "ep" false pLabels))) == some (.noEndpoint "ep")
#guard failIn envSvc dsEmpty (qAll (.serviceVar "ep" false pLabels)) == some (.noEndpoint "ep")
#guard failIn envSvc dsEmpty (qAll (.serviceVar "ep" true pLabels)) == none
-- LATERAL: one invocation per left solution; none when there is none.
#guard failIn envSvc dsMain (qAll (.lateral pPersons (.service epNone false pLabels))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsEmpty (qAll (.lateral pPersons (.service epNone false pLabels))) == none
-- Inside a sub-SELECT the call is made too.
#guard failIn envSvc dsMain (qAll (.subSelect (qAll (.service epNone false pLabels)))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.subSelect (qAll (.service epNone true pLabels)))) == none
-- No SERVICE: no error.
#guard failIn envSvc dsMain (qAll pPersons) == none
-- ASK and CONSTRUCT fail the same way; a DESCRIBE of IRIs alone does
-- not evaluate its WHERE clause, so it invokes nothing.
#guard failIn envSvc dsEmpty (mkQuery .ask (.service epNone false pLabels)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsEmpty (mkQuery (.describe [.iri epOne]) (.service epNone false pLabels)) == none
#guard failIn envSvc dsEmpty (mkQuery (.describe [.var "s"]) (.service epNone false pLabels)) ==
  some (.unreachable epNone.val)
-- The checked evaluators answer the error, or exactly the rows.
#guard (match evalSelectChecked envSvc dsEmpty (qAll (.service epNone false pLabels)) with
        | .error (.unreachable i) => i == epNone.val
        | _ => false)
#guard (match evalSelectChecked envSvc dsEmpty (qAll (.service epOne false pLabels)) with
        | .ok (_, r) => colS "label" r == ["aaa", "bbb"]
        | _ => false)
#guard (match evalAskChecked envSvc dsEmpty (mkQuery .ask (.service epNone true pLabels)) with
        | .ok b => b
        | _ => false)

/-! ### A failed SERVICE call inside EXISTS, and under an outer SILENT

https://github.com/danbri/factoidal/issues/735, Federated Query §2.3 and
§3.2. Each error case is beside the same query with SILENT, or with a
registered endpoint, or with no row to evaluate the expression on, so an
evaluator that always fails, or never fails, breaks the build. -/

/-- `EXISTS { SERVICE [SILENT] <ep> { ?s :label ?label } }`. -/
def exSvc (ep : WfIri) (silent : Bool) : Expr := .existsPat (.service ep silent pLabels)
/-- `NOT EXISTS { SERVICE [SILENT] <ep> { ?s :label ?label } }`. -/
def notExSvc (ep : WfIri) (silent : Bool) : Expr := .notExistsPat (.service ep silent pLabels)
/-- `ORDER BY ASC(e)`. -/
def orderAsc (e : Expr) : SolutionModifier := { orderBy := some [.asc e] }
/-- `GROUP BY ?s`. -/
def groupS : Option (List GroupCondition) := some [.var "s"]

-- 1. FILTER EXISTS. Without SILENT the failed call fails the query; with
-- SILENT, or with a registered endpoint, it does not.
#guard failIn envSvc dsMain (qAll (.filter (exSvc epNone false) pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.filter (exSvc epNone true) pPersons)) == none
#guard failIn envSvc dsMain (qAll (.filter (exSvc epOne false) pPersons)) == none
-- The rows are unchanged: EXISTS over the registered endpoint keeps
-- alice and bob; over SILENT it sees Ω0, one solution, so it is true.
#guard colS "s" (rowsIn envSvc dsMain (qAll (.filter (exSvc epOne false) pPersons))) ==
  ["alice", "bob"]
#guard colS "s" (rowsIn envSvc dsMain (qAll (.filter (exSvc epNone true) pPersons))) ==
  ["alice", "bob"]
-- No row reaches the FILTER: the EXISTS is never evaluated, nothing fails.
#guard failIn envSvc dsEmpty (qAll (.filter (exSvc epNone false) pPersons)) == none
-- Every EXISTS in the expression is evaluated, also the right operand of
-- an `||` whose left operand is true.
#guard failIn envSvc dsMain
    (qAll (.filter (.or (.boolLit true) (exSvc epNone false)) pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (qAll (.filter (.or (.boolLit true) (exSvc epNone true)) pPersons)) == none
-- An expression with no EXISTS gets no failure twin.
#guard failIn envSvc dsMain (qAll (.filter (.boolLit true) pPersons)) == none

-- 2. FILTER NOT EXISTS, the same three ways.
#guard failIn envSvc dsMain (qAll (.filter (notExSvc epNone false) pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.filter (notExSvc epNone true) pPersons)) == none
#guard failIn envSvc dsMain (qAll (.filter (notExSvc epTwo false) pPersons)) == none
-- epTwo holds a label for carol only, so NOT EXISTS keeps alice and bob;
-- the SILENT call is Ω0, so NOT EXISTS is false for every row.
#guard colS "s" (rowsIn envSvc dsMain (qAll (.filter (notExSvc epTwo false) pPersons))) ==
  ["alice", "bob"]
#guard rowsIn envSvc dsMain (qAll (.filter (notExSvc epNone true) pPersons)) == []

-- 3. BIND(EXISTS { ... } AS ?e).
#guard failIn envSvc dsMain (qAll (.bind (exSvc epNone false) "e" pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.bind (exSvc epNone true) "e" pPersons)) == none
#guard failIn envSvc dsMain (qAll (.bind (notExSvc epOne false) "e" pPersons)) == none
#guard colS "e" (rowsIn envSvc dsMain (qAll (.bind (notExSvc epOne false) "e" pPersons))) ==
  ["false", "false"]

-- 4. An OPTIONAL condition: evaluated on every compatible merge.
#guard failIn envSvc dsMain (qAll (.leftJoin pPersons pLabels (exSvc epNone false))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (qAll (.leftJoin pPersons pLabels (exSvc epNone true))) == none
#guard failIn envSvc dsMain (qAll (.leftJoin pPersons pLabels (notExSvc epOne false))) == none
-- No compatible merge (no ages in this graph): the condition is never
-- evaluated, so nothing fails.
#guard failIn envSvc dsMain
    (qAll (.leftJoin pPersons (.bgp [tpv "s" pAge (.var "a")]) (exSvc epNone false))) == none

-- 5. HAVING, for SELECT and for ASK.
#guard failIn envSvc dsMain
    (mkQuery (.select .all) pPersons (groupBy := groupS) (having := [exSvc epNone false])) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (mkQuery (.select .all) pPersons (groupBy := groupS) (having := [exSvc epNone true])) == none
#guard failIn envSvc dsMain
    (mkQuery (.select .all) pPersons (groupBy := groupS) (having := [exSvc epOne false])) == none
#guard failIn envSvc dsMain (mkQuery .ask pPersons (having := [notExSvc epNone false])) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain (mkQuery .ask pPersons (having := [notExSvc epNone true])) == none

-- 6. ORDER BY, for SELECT and for CONSTRUCT.
#guard failIn envSvc dsMain
    (mkQuery (.select .all) pPersons (modifier := orderAsc (exSvc epNone false))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (mkQuery (.select .all) pPersons (modifier := orderAsc (exSvc epNone true))) == none
#guard failIn envSvc dsMain
    (mkQuery (.construct []) pPersons (modifier := orderAsc (notExSvc epNone false))) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (mkQuery (.construct []) pPersons (modifier := orderAsc (notExSvc epOne false))) == none
-- No row to order: nothing fails.
#guard failIn envSvc dsEmpty
    (mkQuery (.select .all) pPersons (modifier := orderAsc (exSvc epNone false))) == none

-- 7. A SELECT expression, at the top and inside a sub-SELECT.
#guard failIn envSvc dsMain
    (mkQuery (.select (.vars [.var "s", .expr (exSvc epNone false) "e"])) pPersons) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (mkQuery (.select (.vars [.var "s", .expr (exSvc epNone true) "e"])) pPersons) == none
#guard failIn envSvc dsMain
    (qAll (.subSelect (mkQuery (.select (.vars [.var "s", .expr (exSvc epNone false) "e"]))
      pPersons))) == some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (qAll (.subSelect (mkQuery (.select .all) pPersons (groupBy := groupS)
      (having := [exSvc epNone false])))) == some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (qAll (.subSelect (mkQuery (.select .all) pPersons (groupBy := groupS)
      (having := [exSvc epNone true])))) == none

-- 8. EXISTS nested in EXISTS, one and two levels.
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.filter (exSvc epNone false) pLabels)) pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.filter (exSvc epNone true) pLabels)) pPersons)) == none
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.filter (.notExistsPat (.filter (exSvc epNone false) pLabels))
      pLabels)) pPersons)) == some (.unreachable epNone.val)

-- 9. §3.2, one level: a failed SERVICE nested in an outer SERVICE SILENT
-- is a failure of the outer call, so the outer SILENT gives one
-- solution with no bindings. Without SILENT on the outer call the query
-- fails.
#guard failIn envSvc dsEmpty (qAll (.service epOne true (.service epNone false pLabels))) ==
  none
#guard rowsIn envSvc dsEmpty (qAll (.service epOne true (.service epNone false pLabels))) ==
  [[]]
#guard failIn envSvc dsEmpty (qAll (.service epOne false (.service epNone false pLabels))) ==
  some (.unreachable epNone.val)
-- A nested call that succeeds: the outer SILENT gives the body's rows.
#guard failIn envSvc dsEmpty (qAll (.service epOne true (.service epTwo false pLabels))) ==
  none
#guard colS "label" (rowsIn envSvc dsEmpty
    (qAll (.service epOne true (.service epTwo false pLabels)))) == ["ccc"]
-- Joined with local rows: Ω0 keeps them unextended.
#guard colS "s" (rowsIn envSvc dsMain
    (qAll (.join pPersons (.service epOne true (.service epNone false pLabels))))) ==
  ["alice", "bob"]
#guard failIn envSvc dsMain
    (qAll (.join pPersons (.service epOne true (.service epNone false pLabels)))) == none
-- The failure inside the body may sit in an EXISTS.
#guard failIn envSvc dsEmpty
    (qAll (.service epOne true (.filter (exSvc epNone false) pLabels))) == none
#guard rowsIn envSvc dsEmpty
    (qAll (.service epOne true (.filter (exSvc epNone false) pLabels))) == [[]]
#guard failIn envSvc dsEmpty
    (qAll (.service epOne false (.filter (exSvc epNone false) pLabels))) ==
  some (.unreachable epNone.val)
-- SERVICE ?v: each invocation is covered by its own SILENT.
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)]])
                 (.serviceVar "ep" true (.service epNone false pLabels)))) == none
#guard colS "ep" (rowsIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)]])
                 (.serviceVar "ep" true (.service epNone false pLabels))))) == ["endpoint1"]
#guard failIn envSvc dsEmpty
    (qAll (.join (.values ["ep"] [[some (.iri epOne)]])
                 (.serviceVar "ep" false (.service epNone false pLabels)))) ==
  some (.unreachable epNone.val)

-- 10. §3.2, two levels: the innermost SILENT that encloses the failure
-- covers it.
#guard failIn envSvc dsEmpty
    (qAll (.service epOne true (.service epTwo false (.service epNone false pLabels)))) == none
#guard rowsIn envSvc dsEmpty
    (qAll (.service epOne true (.service epTwo false (.service epNone false pLabels)))) == [[]]
#guard failIn envSvc dsEmpty
    (qAll (.service epOne false (.service epTwo true (.service epNone false pLabels)))) == none
#guard rowsIn envSvc dsEmpty
    (qAll (.service epOne false (.service epTwo true (.service epNone false pLabels)))) == [[]]
#guard failIn envSvc dsEmpty
    (qAll (.service epOne false (.service epTwo false (.service epNone false pLabels)))) ==
  some (.unreachable epNone.val)
-- Two levels with no failure: the rows come through both SILENT calls.
#guard colS "label" (rowsIn envSvc dsEmpty
    (qAll (.service epOne true (.service epTwo true (.service epOne false pLabels))))) ==
  ["aaa", "bbb"]

-- 11. Both together: an outer SILENT inside an EXISTS covers the nested
-- failure, so the EXISTS sees Ω0 and is true; without it the query fails.
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.service epOne true (.service epNone false pLabels)))
      pPersons)) == none
#guard colS "s" (rowsIn envSvc dsMain
    (qAll (.filter (.existsPat (.service epOne true (.service epNone false pLabels)))
      pPersons))) == ["alice", "bob"]
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.service epOne false
      (.service epTwo false (.service epNone false pLabels)))) pPersons)) ==
  some (.unreachable epNone.val)
#guard failIn envSvc dsMain
    (qAll (.filter (.existsPat (.service epOne false
      (.service epTwo true (.service epNone false pLabels)))) pPersons)) == none

-- 12. The checked evaluators answer the error for an EXISTS failure.
#guard (match evalSelectChecked envSvc dsMain
          (qAll (.filter (exSvc epNone false) pPersons)) with
        | .error (.unreachable i) => i == epNone.val
        | _ => false)
#guard (match evalAskChecked envSvc dsMain
          (mkQuery .ask (.filter (notExSvc epNone false) pPersons)) with
        | .error (.unreachable i) => i == epNone.val
        | _ => false)
#guard (match evalSelectChecked envSvc dsEmpty
          (qAll (.service epOne true (.service epNone false pLabels))) with
        | .ok (_, r) => r == [[]]
        | _ => false)

/-! ## §18.2.4 projection and SELECT expressions -/

def qAgeDouble : Query :=
  mkQuery (.select (.vars [.var "s", .expr (.arith .mul (.var "a") (.numericLit 2)) "d"]))
    (.bgp [tpv "s" pAge (.var "a")])

#guard colS "d" (rows { default := gMain, named := [] } qAgeDouble) == ["60", "50"]
-- The projection drops ?a: it is neither in the header nor in a row.
#guard hdr { default := gMain, named := [] } qAgeDouble == ["s", "d"]
#guard colS "a" (rows { default := gMain, named := [] } qAgeDouble) == ["", ""]
-- SELECT * reports syntactically in-scope variables, including ones
-- unbound in every result. We choose first occurrence in the query.
#guard hdr dsMain (qAll pLabels) == ["s", "label"]
-- An expression error leaves the alias unbound; the row survives.
#guard colS "e" (rows dsMain
    (mkQuery (.select (.vars [.var "s", .expr (.var "nosuch") "e"])) pPersons)) == ["", ""]
-- A later SELECT expression can see an earlier one's binding.
#guard colS "t" (rows dsMain
    (mkQuery (.select (.vars [.expr (.numericLit 5) "u",
                              .expr (.arith .add (.var "u") (.numericLit 1)) "t"]))
      .empty)) == ["6"]

/-! ## §18.4 DISTINCT / REDUCED -/

/-- Both UNION arms bind ?x to the same term, so DISTINCT must collapse
them to one row. -/
def qDistinct (distinct reduced : Bool) : Query :=
  mkQuery (.select .all)
    (.union (.values ["x"] [[some (.iri iAlice)]]) (.values ["x"] [[some (.iri iAlice)]]))
    (modifier := { distinct := distinct, reduced := reduced })

#guard (rows dsMain (qDistinct false false)).length == 2
#guard (rows dsMain (qDistinct true false)).length == 1
-- REDUCED is specified as "may remove duplicates"; keeping them all is
-- conformant and is what this port does.
#guard (rows dsMain (qDistinct false true)).length == 2
-- §18.3: binding ORDER carries no meaning, so two rows that bind the
-- same variables in a different order are ONE row under DISTINCT.
#guard (distinctSolutions [[("x", .iri iAlice), ("y", .iri iBob)],
                           [("y", .iri iBob), ("x", .iri iAlice)]]).length == 1
-- Rows with different domains are different rows.
#guard (distinctSolutions [[("x", .iri iAlice)],
                           [("x", .iri iAlice), ("y", .iri iBob)]]).length == 2

/- The HashMap-backed runtime path retains the reference DISTINCT survivor
order (last representative in each §18.3-equivalence class) for deliberately
mixed binding layouts.  These executable cases are not a substitute for the
pending general refinement theorem, but keep the optimized path in the normal
`lake build` gate while that proof is developed. -/
def distinctFastCases : SolutionSeq :=
  [[("x", .iri iAlice), ("y", .iri iBob)],
   [("y", .iri iBob), ("x", .iri iAlice)],
   [("x", .iri iCarol)],
   [("x", .iri iAlice), ("y", .iri iBob)],
   [("x", .iri iCarol)],
   [("x", .iri iDave), ("z", sLit "one")],
   [("z", sLit "one"), ("x", .iri iDave)]]

#guard distinctSolutionsFast distinctFastCases == distinctSolutions distinctFastCases
#guard (distinctSolutionsFast distinctFastCases).length == 3

-- A malformed association-list layout with a shadowed duplicate variable is
-- still interpreted through first-match `lookup`; the fixed-universe key has
-- the same interpretation rather than depending on list length or order.
def duplicateVarRow : Binding :=
  [("x", .iri iAlice), ("x", .iri iBob)]
def canonicalVarRow : Binding :=
  [("x", .iri iAlice)]

#guard duplicateVarRow.equiv canonicalVarRow
#guard duplicateVarRow.distinctKeyFor ["missing", "x"] ==
  canonicalVarRow.distinctKeyFor ["missing", "x"]

-- Language-tag case is deliberately non-structural RDF term equality.  The
-- canonical key lowercases it, keeping equivalent rows in one candidate
-- bucket while the bucket still runs full `Binding.equiv`.
def langLowerRow : Binding :=
  [("label", .literal (Literal.langString "chat" "en-GB"))]
def langUpperRow : Binding :=
  [("label", .literal (Literal.langString "chat" "EN-gb"))]

#guard langLowerRow.equiv langUpperRow
#guard langLowerRow.distinctKeyFor ["label"] == langUpperRow.distinctKeyFor ["label"]

/-! ## §15.1 ORDER BY -/

def qOrder (c : OrderCondition) : Query :=
  mkQuery (.select .all) pLabels (modifier := { orderBy := some [c] })

#guard colS "label" (rows { default := gMain, named := [] } (qOrder (.asc (.var "label"))))
         == ["aaa", "aab", "bbb"]
#guard colS "label" (rows { default := gMain, named := [] } (qOrder (.desc (.var "label"))))
         == ["bbb", "aab", "aaa"]
-- The §15.1 kind hierarchy: unbound < blank node < IRI < literal.
#guard sparqlOrder .error (.term (.bnode "b")) == -1
#guard sparqlOrder (.term (.bnode "b")) (.term (.iri iAlice)) == -1
#guard sparqlOrder (.term (.iri iAlice)) (.term (.literal (Literal.string "a"))) == -1
#guard sparqlOrder (.num 1) (.num 2) == -1
#guard sparqlOrder (.num 2) (.num 1) == 1
#guard sparqlOrder (.num 1) (.dec "1.0") == 0
#guard sparqlOrder (.bool false) (.bool true) == -1
#guard sparqlOrder .error .error == 0
-- An UNBOUND value sorts FIRST under ASC: the two UNION arms bind
-- different variables, so ?label is unbound in one of them.
#guard colS "label" (rows dsMain
    (mkQuery (.select .all)
      (.union pLabels (.values ["s"] [[some (.iri iCarol)]]))
      (modifier := { orderBy := some [.asc (.var "label")] })))
    == ["", "aaa", "bbb"]
-- Multi-key ORDER BY is lexicographic: the first non-equal condition
-- decides.
#guard colS "label" (rows { default := gMain, named := [] }
    (mkQuery (.select .all) pLabels
      (modifier := { orderBy := some [.desc (.var "s"), .asc (.var "label")] })))
    == ["bbb", "aaa", "aab"]
-- ORDER BY runs BEFORE projection, so it may name a dropped variable.
#guard colS "label" (rows { default := gMain, named := [] }
    (mkQuery (.select (.vars [.var "label"])) pLabels
      (modifier := { orderBy := some [.desc (.var "s")] })))
    == ["bbb", "aaa", "aab"]

/-! ## §18.4 OFFSET / LIMIT -/

def qSlice (off lim : Option Nat) : Query :=
  mkQuery (.select .all) pLabels
    (modifier := { orderBy := some [.asc (.var "label")], offset := off, limit := lim })

#guard colS "label" (rows { default := gMain, named := [] } (qSlice none (some 1))) == ["aaa"]
#guard colS "label" (rows { default := gMain, named := [] } (qSlice (some 1) none)) == ["aab", "bbb"]
#guard colS "label" (rows { default := gMain, named := [] } (qSlice (some 1) (some 1))) == ["aab"]
#guard (rows { default := gMain, named := [] } (qSlice none (some 99))).length == 3
#guard rows { default := gMain, named := [] } (qSlice (some 99) none) == []
#guard rows { default := gMain, named := [] } (qSlice none (some 0)) == []

/-! ## §18.5.1 GROUP BY and aggregates -/

def aggQuery (fn : AggregateFn) (distinct : Bool) (e : Expr) : Query :=
  mkQuery (.select (.vars [.var "s", .expr (.aggregate fn distinct e) "r"]))
    (.bgp [tpv "s" pVal (.var "v")])
    (groupBy := some [.var "s"])

def aggCol (fn : AggregateFn) (distinct : Bool) (e : Expr) : List String :=
  colS "r" (rows dsNums (aggQuery fn distinct e))

-- GROUP BY ?s makes two groups (alice has two values, bob one).
#guard (rows dsNums (aggQuery .count false (.var "*"))).length == 2
#guard colS "s" (rows dsNums (aggQuery .count false (.var "*"))) == ["alice", "bob"]
#guard aggCol .count false (.var "*") == ["2", "1"]
#guard aggCol .count false (.var "v") == ["2", "1"]
#guard aggCol .sum false (.var "v") == ["3", "3"]
#guard aggCol .min false (.var "v") == ["1", "3"]
#guard aggCol .max false (.var "v") == ["2", "3"]
-- §18.5.1.5: AVG of integers is a DECIMAL, never an integer.
#guard aggCol .avg false (.var "v") == ["1.5", "3.0"]
#guard aggCol .sample false (.var "v") == ["1", "3"]
#guard aggCol (.groupConcat none) false (.var "v") == ["1 2", "3"]
#guard aggCol (.groupConcat (some ",")) false (.var "v") == ["1,2", "3"]
-- COUNT(DISTINCT ?v) over a group whose values repeat.
#guard colS "r" (rows { default := gNums ++ [tr iAlice pVal (nLit "1")], named := [] }
    (aggQuery .count false (.var "v"))) == ["3", "1"]
#guard colS "r" (rows { default := gNums ++ [tr iAlice pVal (nLit "1")], named := [] }
    (aggQuery .count true (.var "v"))) == ["2", "1"]
-- §18.5.1.4: a non-numeric operand makes SUM an error, so the alias
-- is left unbound.
#guard colS "r" (rows { default := gMain, named := [] }
    (mkQuery (.select (.vars [.expr (.aggregate .sum false (.var "label")) "r"]))
      pLabels (groupBy := some [.var "s"]))) == ["", ""]
-- An aggregate with NO GROUP BY groups over the whole sequence
-- (§18.5.1) — one row out.
#guard colS "r" (rows dsNums
    (mkQuery (.select (.vars [.expr (.aggregate .count false (.var "*")) "r"]))
      (.bgp [tpv "s" pVal (.var "v")]))) == ["3"]
-- GROUP BY (expr AS ?alias) binds the alias in the group's rows.
#guard colS "k" (rows dsNums
    (mkQuery (.select (.vars [.var "k", .expr (.aggregate .count false (.var "*")) "r"]))
      (.bgp [tpv "s" pVal (.var "v")])
      (groupBy := some [.expr (.str (.var "s")) (some "k")])))
    == ["alice", "bob"]
-- An aggregate inside a larger expression is computed, then folded in.
#guard colS "r" (rows dsNums
    (mkQuery (.select (.vars [.var "s",
                              .expr (.arith .mul (.aggregate .count false (.var "*"))
                                                 (.numericLit 10)) "r"]))
      (.bgp [tpv "s" pVal (.var "v")])
      (groupBy := some [.var "s"]))) == ["20", "10"]

/-! ## §18.5.1 HAVING -/

def qHaving (h : List Expr) : Query :=
  mkQuery (.select (.vars [.var "s", .expr (.aggregate .count false (.var "*")) "c"]))
    (.bgp [tpv "s" pVal (.var "v")])
    (groupBy := some [.var "s"]) (having := h)

#guard colS "s" (rows dsNums (qHaving [])) == ["alice", "bob"]
#guard colS "s" (rows dsNums
    (qHaving [.compare .gt (.aggregate .count false (.var "*")) (.numericLit 1)])) == ["alice"]
#guard rows dsNums
    (qHaving [.compare .gt (.aggregate .count false (.var "*")) (.numericLit 99)]) == []
#guard (rows dsNums (qHaving [.boolLit true])).length == 2

/-! ## §18.2.4.3 the trailing VALUES clause at a grouping level

SPARQL 1.1 §18.2.4.3 (1.2 §18.3.4.3): the VALUES rows join AFTER
GROUP BY and HAVING and BEFORE the SELECT expressions. The grouped
solution binds the named GROUP BY variables only, so compatibility is
decided on those. W3C sparql11 `bindings/values-group-by-*`. -/

def qGroupValues (items : List SelectItem) (vals : List Binding)
    (md : SolutionModifier := {}) : Query :=
  mkQuery (.select (.vars items)) (.bgp [tpv "s" pVal (.var "v")])
    (groupBy := some [.var "s"]) (modifier := md) (postValues := some vals)

def countItem : SelectItem := .expr (.aggregate .count false (.var "*")) "c"

-- A VALUES variable the WHERE pattern never binds reaches the
-- projection of every group.
#guard colS "w" (rows dsNums (qGroupValues [.var "s", .var "w"] [[("w", nLit "7")]]))
    == ["7", "7"]
#guard colS "x" (rows dsNums (qGroupValues [.var "s", .expr (.str (.var "w")) "x"]
    [[("w", nLit "7")]])) == ["7", "7"]
-- The join is on the grouping variable: only alice's group survives.
#guard colS "s" (rows dsNums (qGroupValues [.var "s", countItem]
    [[("s", .iri iAlice)], [("s", .iri iZed)]])) == ["alice"]
#guard colS "c" (rows dsNums (qGroupValues [.var "s", countItem]
    [[("s", .iri iAlice)], [("s", .iri iZed)]])) == ["2"]
-- `?v` is not in scope after GROUP BY ?s, so a VALUES row binding it
-- does not filter any group, and every count stays whole. Joining the
-- VALUES rows BEFORE grouping would keep only bob's row (`?v = 3`).
#guard colS "s" (rows dsNums (qGroupValues [.var "s", countItem] [[("v", nLit "3")]]))
    == ["alice", "bob"]
#guard colS "c" (rows dsNums (qGroupValues [.var "s", countItem] [[("v", nLit "3")]]))
    == ["2", "1"]
-- ORDER BY may name a VALUES variable that is not projected.
#guard colS "s" (rows dsNums (qGroupValues [.var "s", countItem]
    [[("s", .iri iAlice), ("k", sLit "b")], [("s", .iri iBob), ("k", sLit "a")]]
    { orderBy := some [.asc (.var "k")] })) == ["bob", "alice"]
#guard colS "s" (rows dsNums (qGroupValues [.var "s", countItem]
    [[("s", .iri iAlice), ("k", sLit "a")], [("s", .iri iBob), ("k", sLit "b")]]
    { orderBy := some [.asc (.var "k")] })) == ["alice", "bob"]
-- The ORDER BY key is not projected.
#guard (rows dsNums (qGroupValues [.var "s", countItem]
    [[("s", .iri iAlice), ("k", sLit "b")]] { orderBy := some [.asc (.var "k")] })).all
    (fun mu => (mu.lookup "k").isNone)

/-! ## §11.4 a SELECT expression reads the earlier ones

"the variable is introduced by an earlier SELECT expression in the same
SELECT clause" (W3C sparql12 `grouping/select-variable-reuse`). -/

#guard colS "d" (rows dsNums
    (mkQuery (.select (.vars [.expr (.aggregate .count false (.var "v")) "c",
                              .expr (.arith .add (.var "c") (.numericLit 1)) "d"]))
      (.bgp [tpv "s" pVal (.var "v")]))) == ["4"]
-- A LATER item is not visible: `?c` is unbound when `?d` is computed.
#guard colS "d" (rows dsNums
    (mkQuery (.select (.vars [.expr (.arith .add (.var "c") (.numericLit 1)) "d",
                              .expr (.aggregate .count false (.var "v")) "c"]))
      (.bgp [tpv "s" pVal (.var "v")]))) == [""]
-- An item whose expression errs stays unbound, even when a non-grouped
-- WHERE variable of the same name is bound in the group's rows.
#guard colS "v" (rows dsNums
    (mkQuery (.select (.vars [.var "s", .expr (.var "unbound") "v"]))
      (.bgp [tpv "s" pVal (.var "v")]) (groupBy := some [.var "s"]))) == ["", ""]

/-! ## §18.2.4 ASK -/

#guard evalAsk emptyEnv dsMain (mkQuery .ask pLabels) == true
#guard evalAsk emptyEnv dsMain (mkQuery .ask (.bgp [tpv "s" pKnows (.var "k")])) == false
-- A SELECT query is not an ASK query: the ASK entry point answers
-- false rather than guessing.
#guard evalAsk emptyEnv dsMain (qAll pLabels) == false
-- ASK sees the trailing VALUES block.
#guard evalAsk emptyEnv dsMain
    (mkQuery .ask pLabels (postValues := some [[("s", .iri iZed)]])) == false

/-! ### ASK with a SolutionModifier — grammar rule [12], §18.2.4, §18.2.5

ASK is true exactly when the solution sequence after GROUP BY, HAVING,
the trailing VALUES join, ORDER BY, OFFSET and LIMIT is non-empty. The
fixture is `dsNums`: `:alice :val 1, 2` and `:bob :val 3`, so three
solutions in two groups. Issue 699. -/

/-- `ASK { ?s :val ?v }` with the given clauses after the WHERE clause. -/
def qAskVal (groupBy : Option (List GroupCondition) := none)
    (having : List Expr := []) (md : SolutionModifier := {})
    (vals : Option (List Binding) := none) : Query :=
  mkQuery .ask (.bgp [tpv "s" pVal (.var "v")]) (groupBy := groupBy)
    (having := having) (modifier := md) (postValues := vals)

def askNums (q : Query) : Bool := evalAsk emptyEnv dsNums q

/-- `COUNT(*) > n`. -/
def countGt (n : Nat) : Expr :=
  .compare .gt (.aggregate .count false (.var "*")) (.numericLit n)

-- No modifier: three solutions.
#guard askNums (qAskVal) == true
-- LIMIT 0 keeps no solution, whatever the data holds.
#guard askNums (qAskVal (md := { limit := some 0 })) == false
#guard askNums (qAskVal (md := { limit := some 1 })) == true
-- OFFSET skips solutions: two of three leaves one; three of three leaves none.
#guard askNums (qAskVal (md := { offset := some 2 })) == true
#guard askNums (qAskVal (md := { offset := some 3 })) == false
#guard askNums (qAskVal (md := { offset := some 99 })) == false
-- OFFSET is applied before LIMIT, so `OFFSET 2 LIMIT 0` is empty and
-- `OFFSET 2 LIMIT 1` keeps the last solution.
#guard askNums (qAskVal (md := { offset := some 2, limit := some 0 })) == false
#guard askNums (qAskVal (md := { offset := some 2, limit := some 1 })) == true
-- ORDER BY changes no length: the answers are those of the same query without it.
#guard askNums (qAskVal (md := { orderBy := some [.desc (.var "v")], limit := some 0 })) == false
#guard askNums (qAskVal (md := { orderBy := some [.desc (.var "v")], limit := some 1 })) == true
-- GROUP BY ?s makes two groups (alice, bob).
#guard askNums (qAskVal (groupBy := some [.var "s"])) == true
#guard askNums (qAskVal (groupBy := some [.var "s"]) (md := { offset := some 1 })) == true
#guard askNums (qAskVal (groupBy := some [.var "s"]) (md := { offset := some 2 })) == false
-- HAVING filters groups: alice has two rows, bob one.
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [countGt 1])) == true
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [countGt 2])) == false
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [countGt 100])) == false
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [.boolLit true])) == true
-- HAVING and LIMIT together: the group that passes HAVING survives LIMIT 1,
-- and OFFSET 1 skips it.
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [countGt 1])
    (md := { limit := some 1 })) == true
#guard askNums (qAskVal (groupBy := some [.var "s"]) (having := [countGt 1])
    (md := { offset := some 1 })) == false
-- HAVING with no GROUP BY: the whole sequence is one group of three rows.
#guard askNums (qAskVal (having := [countGt 2])) == true
#guard askNums (qAskVal (having := [countGt 3])) == false
-- ... and that one group is one solution, so OFFSET 1 leaves nothing.
#guard askNums (qAskVal (having := [countGt 2]) (md := { offset := some 1 })) == false
-- An empty WHERE result still forms the one implicit group, whose count is 0.
#guard evalAsk emptyEnv dsNums
    (mkQuery .ask (.bgp [tpv "s" pLabel (.var "v")]) (having := [countGt 0])) == false
#guard evalAsk emptyEnv dsNums
    (mkQuery .ask (.bgp [tpv "s" pLabel (.var "v")])
      (having := [.compare .eq (.aggregate .count false (.var "*")) (.numericLit 0)])) == true
-- The trailing VALUES join comes AFTER grouping: a row for a subject with
-- no group (`:zed`) leaves nothing; a row for `:alice` keeps her group.
#guard askNums (qAskVal (groupBy := some [.var "s"])
    (vals := some [[("s", .iri iZed)]])) == false
#guard askNums (qAskVal (groupBy := some [.var "s"])
    (vals := some [[("s", .iri iAlice)]])) == true
-- `?v` is not in scope after GROUP BY ?s, so a VALUES row that binds it
-- filters no group. Joining the rows BEFORE grouping would find no
-- solution with `?v = 99` and answer false.
#guard askNums (qAskVal (groupBy := some [.var "s"])
    (vals := some [[("v", nLit "99")]])) == true
-- The same VALUES row joined to the ungrouped solutions (no GROUP BY, no HAVING).
#guard askNums (qAskVal (vals := some [[("v", nLit "99")]])) == false
-- A CONSTRUCT is not an ASK: the ASK entry point answers false.
#guard evalAsk emptyEnv dsNums
    (mkQuery (.construct []) (.bgp [tpv "s" pVal (.var "v")])) == false

/-! ## §16.2 CONSTRUCT -/

/-- `CONSTRUCT { ?s :knows ?s } WHERE { ?s :label ?label }`. -/
def qConstructSelf : Query :=
  mkQuery (.construct [{ s := .var "s", p := .iri pKnows, o := .var "s" }]) pLabels

#guard (evalConstruct emptyEnv dsMain qConstructSelf).length == 2
#guard (evalConstruct emptyEnv dsMain qConstructSelf).all
         (fun t => t.p == pKnows) == true

/-- A template BLANK NODE: two solutions must mint two DISTINCT nodes,
and the same label within one solution must mint the same node. -/
def qConstructBnode : Query :=
  mkQuery (.construct [{ s := .bnode "b", p := .iri pLabel, o := .var "label" },
                       { s := .bnode "b", p := .iri pType, o := .iri cPerson }])
    pLabels

def bnodeSubjects : List String :=
  (evalConstruct emptyEnv dsMain qConstructBnode).map (fun t =>
    match t.s with | .bnode b => b | .iri i => i.val)

#guard (evalConstruct emptyEnv dsMain qConstructBnode).length == 4
-- Two solutions → two distinct template nodes, each used twice.
#guard bnodeSubjects == ["tpl_0_b", "tpl_0_b", "tpl_1_b", "tpl_1_b"]
#guard (dedupErAcc (bnodeSubjects.map (fun s => EvalResult.term (.bnode s))) []).length == 2
-- An ill-formed instantiation is SKIPPED, not an error: a literal
-- cannot be a subject.
#guard evalConstruct emptyEnv dsMain
    (mkQuery (.construct [{ s := .var "label", p := .iri pKnows, o := .var "s" }]) pLabels) == []
-- A LIMIT on the WHERE clause limits which bindings drive the
-- template.
#guard (evalConstruct emptyEnv dsMain
    (mkQuery (.construct [{ s := .var "s", p := .iri pKnows, o := .var "s" }]) pLabels
      (modifier := { limit := some 1 }))).length == 1
-- ORDER BY applies to the solution sequence BEFORE LIMIT in a
-- CONSTRUCT too (§18.2.4 builds OrderBy then Slice for every query
-- form): `DESC(?label) LIMIT 1` drives the template with bob's row
-- ("bbb"), whatever order the BGP produced. Pinned after the
-- differential harness found the unordered slice (2026-08-22).
#guard evalConstruct emptyEnv { default := gMain, named := [] }
    (mkQuery (.construct [{ s := .var "s", p := .iri pKnows, o := .var "s" }]) pLabels
      (modifier := { orderBy := some [.desc (.var "label")], limit := some 1 }))
    == [{ s := .iri iBob, p := pKnows, o := .iri iBob }]
-- The result is a GRAPH, so a template that yields the same triple for
-- every solution collapses to one triple.
#guard (evalConstruct emptyEnv dsMain
    (mkQuery (.construct [{ s := .iri iZed, p := .iri pType, o := .iri cPerson }])
      pLabels)).length == 1

/-! ### CONSTRUCT with GROUP BY and HAVING — §18.2.4.1, §16.2

§18.2.4.1 applies to every query form, and §16.2 instantiates the
template over the resulting solution sequence. After grouping the
solutions bind the named GROUP BY variables only. The fixture is
`dsNums`: `:alice :val 1, 2` and `:bob :val 3`. Issue 699. -/

def pValPat : QueryPattern := .bgp [tpv "s" pVal (.var "v")]

/-- `CONSTRUCT { <template> } WHERE { ?s :val ?v }` with clauses. -/
def qConstructVal (template : List TriplePattern)
    (groupBy : Option (List GroupCondition) := none) (having : List Expr := [])
    (md : SolutionModifier := {}) (vals : Option (List Binding) := none) : Query :=
  mkQuery (.construct template) pValPat (groupBy := groupBy) (having := having)
    (modifier := md) (postValues := vals)

/-- `?s :age 1`: uses only the grouping variable. -/
def tmplKey : TriplePattern := { s := .var "s", p := .iri pAge, o := .literal (Literal.string "k") }
/-- `?s :age ?v`: uses a variable that GROUP BY ?s does not keep. -/
def tmplNonKey : TriplePattern := { s := .var "s", p := .iri pAge, o := .var "v" }

def constructNums (q : Query) : Graph := evalConstruct emptyEnv dsNums q

def aliceKey : Triple := tr iAlice pAge (sLit "k")
def bobKey : Triple := tr iBob pAge (sLit "k")

-- Without GROUP BY every solution drives the template: `?v` gives three
-- triples, and the constant object gives one per subject (a graph).
#guard (constructNums (qConstructVal [tmplNonKey])).length == 3
#guard (constructNums (qConstructVal [tmplKey])).length == 2
-- A template variable that is a GROUP BY variable: one triple per group.
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"]))
    == [aliceKey, bobKey]
-- A template variable that is NOT a GROUP BY variable is unbound after
-- grouping, so the triple is not produced (§16.2). Ungrouped, the same
-- template yields three triples.
#guard constructNums (qConstructVal [tmplNonKey] (groupBy := some [.var "s"])) == []
-- A template with one triple of each kind keeps only the first.
#guard constructNums (qConstructVal [tmplKey, tmplNonKey] (groupBy := some [.var "s"]))
    == [aliceKey, bobKey]
-- GROUP BY (expr AS ?k) keeps ?k, and drops the variable it was computed from.
#guard (constructNums (qConstructVal
    [{ s := .var "k", p := .iri pAge, o := .literal (Literal.string "k") }]
    (groupBy := some [.expr (.str (.var "s")) (some "k")]))) == []
#guard (constructNums (qConstructVal
    [{ s := .var "s", p := .iri pAge, o := .var "k" }]
    (groupBy := some [.expr (.str (.var "s")) (some "k")]))) == []
#guard (constructNums (qConstructVal
    [{ s := .iri iZed, p := .iri pAge, o := .var "k" }]
    (groupBy := some [.expr (.str (.var "s")) (some "k")]))).length == 2
-- HAVING filters groups before the template is instantiated: only
-- alice has more than one row.
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (having := [countGt 1])) == [aliceKey]
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (having := [countGt 99])) == []
-- HAVING with no GROUP BY: the one implicit group of three rows. A
-- ground template triple is produced once, or not at all.
#guard constructNums (qConstructVal [{ s := .iri iZed, p := .iri pAge, o := .iri iZed }]
    (having := [countGt 2])) == [tr iZed pAge (.iri iZed)]
#guard constructNums (qConstructVal [{ s := .iri iZed, p := .iri pAge, o := .iri iZed }]
    (having := [countGt 3])) == []
-- ... and a variable is unbound in that group.
#guard constructNums (qConstructVal [tmplKey] (having := [countGt 2])) == []
-- A template blank node is fresh per SOLUTION: after grouping there are
-- two solutions (groups), where the ungrouped sequence has three.
def tmplBnode : TriplePattern :=
  { s := .bnode "b", p := .iri pAge, o := .iri iZed }
#guard (constructNums (qConstructVal [tmplBnode])).length == 3
#guard (constructNums (qConstructVal [tmplBnode] (groupBy := some [.var "s"]))).length == 2
-- ORDER BY, OFFSET and LIMIT act on the grouped solutions.
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (md := { orderBy := some [.desc (.var "s")], limit := some 1 })) == [bobKey]
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (md := { orderBy := some [.asc (.var "s")], limit := some 1 })) == [aliceKey]
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (md := { offset := some 1 })) == [bobKey]
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (md := { offset := some 2 })) == []
#guard constructNums (qConstructVal [tmplKey] (groupBy := some [.var "s"])
    (md := { limit := some 0 })) == []
-- The trailing VALUES rows join after grouping (W3C sparql11
-- `bindings/values-construct-group-by`): a row for a subject with no
-- group adds nothing, and a row's variables are visible to the template.
#guard constructNums (qConstructVal
    [{ s := .var "s", p := .iri pAge, o := .var "rank" }]
    (groupBy := some [.var "s"])
    (vals := some [[("s", .iri iAlice), ("rank", nLit "1")],
                   [("s", .iri iBob), ("rank", nLit "2")],
                   [("s", .iri iZed), ("rank", nLit "9")]]))
    == [tr iAlice pAge (nLit "1"), tr iBob pAge (nLit "2")]
-- `?v` is not a GROUP BY variable, so a VALUES row on it joins every
-- group and the template still cannot read the WHERE pattern's `?v`.
#guard constructNums (qConstructVal [tmplNonKey] (groupBy := some [.var "s"])
    (vals := some [[("v", nLit "99")]])) == [tr iAlice pAge (nLit "99"), tr iBob pAge (nLit "99")]

/-! ## §9 / §18.4 property paths -/

def qPath (path : PropertyPath) : Query :=
  qAll (.propertyPath (.var "s") path (.var "o"))

def pathPairs (path : PropertyPath) : List (String × String) :=
  (rows dsChain (qPath path)).map (fun mu =>
    (shortName ((col "s" [mu]).headD ""), shortName ((col "o" [mu]).headD "")))

-- A one-step predicate path is the triple pattern.
#guard pathPairs (.iri pKnows) == [("alice", "bob"), ("bob", "carol")]
-- `^:knows` is the converse.
#guard pathPairs (.inverse (.iri pKnows)) == [("bob", "alice"), ("carol", "bob")]
-- https://github.com/danbri/factoidal/issues/1023: §18.4 makes `?s ^:label ?o`
-- the same as `?o :label ?s`, so `?s` binds the literal object "aaa".
#guard pathPairs (.inverse (.iri pLabel)) == [("aaa", "alice")]
-- The literal is also a middle node: `^:label/:label` joins on alice.
#guard pathPairs (.sequence (.inverse (.iri pLabel)) (.iri pLabel)) == [("aaa", "aaa")]
-- `:knows/:knows` composes.
#guard pathPairs (.sequence (.iri pKnows) (.iri pKnows)) == [("alice", "carol")]
-- `:knows|:label` is the union.
#guard (pathPairs (.alternative (.iri pKnows) (.iri pLabel))).length == 3
-- `:knows+` is the transitive closure: alice reaches carol.
#guard ((pathPairs (.oneOrMore (.iri pKnows))).contains ("alice", "carol")) == true
#guard (pathPairs (.oneOrMore (.iri pKnows))).length == 3
-- https://github.com/danbri/factoidal/issues/955: a step relation with a pair
-- twice. `(:knows|:val)+` over alice knows bob, bob knows carol, alice val bob
-- has the step list [(alice, bob), (bob, carol), (alice, bob)]. The first
-- round adds (alice, carol) and the deduplication removes one (alice, bob),
-- so a length test against the step list stops before the §18.4 fixpoint.
def gDupStep : Graph :=
  [ tr iAlice pKnows (.iri iBob),
    tr iBob   pKnows (.iri iCarol),
    tr iAlice pVal   (.iri iBob) ]
def dupStepPairs : List (String × String) :=
  (rows { default := gDupStep, named := [] }
      (qPath (.oneOrMore (.alternative (.iri pKnows) (.iri pVal))))).map (fun mu =>
    (shortName ((col "s" [mu]).headD ""), shortName ((col "o" [mu]).headD "")))
#guard dupStepPairs.contains ("alice", "carol") == true
-- §18.4 ALP: the closure is a set, each pair once.
#guard dupStepPairs.length == 3
-- `:knows*` adds the reflexive pairs over the graph's nodes.
#guard ((pathPairs (.zeroOrMore (.iri pKnows))).contains ("alice", "alice")) == true
#guard ((pathPairs (.zeroOrMore (.iri pKnows))).contains ("alice", "carol")) == true
-- `:knows?` is reflexive plus one step, never two.
#guard ((pathPairs (.zeroOrOne (.iri pKnows))).contains ("alice", "carol")) == false
#guard ((pathPairs (.zeroOrOne (.iri pKnows))).contains ("alice", "bob")) == true
-- §18.2.2.5: a CONSTANT that appears nowhere in the data still matches
-- itself under a zero-length path (the F* tree's issue-#66 fix).
#guard colS "o" (rows dsChain (qAll (.propertyPath (.iri iZed)
    (.zeroOrMore (.iri pKnows)) (.var "o")))) == ["zed"]
-- ...but not under `+`, which requires at least one step.
#guard rows dsChain (qAll (.propertyPath (.iri iZed) (.oneOrMore (.iri pKnows))
    (.iri iZed))) == []
-- `!(:knows)` excludes that predicate and keeps the rest.
#guard pathPairs (.negatedSet [.iri pKnows]) == [("alice", "aaa")]
-- A path whose two endpoints are the SAME variable forces them equal.
#guard rows dsChain (qAll (.propertyPath (.var "x") (.iri pKnows) (.var "x"))) == []

/-! ## The remaining constructors and the two entry points -/

-- The empty group pattern yields exactly the empty solution mapping.
#guard rows dsMain (qAll .empty) == [[]]
-- MINUS still behaves as §18.5 says under the new evaluator.
#guard colS "s" (rows dsMain
    (qAll (.minus pPersons (.values ["s"] [[some (.iri iAlice)]])))) == ["bob"]
-- FILTER over the wider set.
#guard colS "label" (rows { default := gMain, named := [] }
    (qAll (.filter (.compare .eq (.var "label") (.lit (Literal.string "bbb"))) pLabels)))
    == ["bbb"]
-- OPTIONAL keeps the unmatched left row.
#guard colS "label" (rows { default := gMain, named := [] }
    (qAll (.leftJoin pPersons pLabels (.boolLit true)))) == ["aaa", "aab", "bbb", ""]
-- §13.2 FROM rebuilds the default graph from a named one.
#guard colS "label" (rows dsNamed
    (mkQuery (.select .all) pLabels (dataset := [.default gOne]))) == ["aaa"]
-- FROM NAMED makes a graph reachable through GRAPH but not by default.
#guard rows dsNamed
    (mkQuery (.select .all) pLabels (dataset := [.named gTwo])) == []
#guard colS "label" (rows dsNamed
    (mkQuery (.select .all) (.graph (.iri gTwo) pLabels) (dataset := [.named gTwo])))
    == ["bbb"]
-- Trailing VALUES joins onto the WHERE result (§10.2).
#guard colS "label" (rows { default := gMain, named := [] }
    (mkQuery (.select .all) pLabels (postValues := some [[("s", .iri iBob)]]))) == ["bbb"]
-- `evalIn` on a dataset with no named graphs agrees with `eval`.
#guard ((QueryPattern.lower emptyEnv pLabels).eval gNoCarol
        == (QueryPattern.lower emptyEnv pLabels).evalIn dsMain gNoCarol) == true

/-! ## §18.6 EXISTS — active graph and nesting

The shapes of the two sparql11 `exists` cases this stage fixed
(`Exists within graph pattern`, `Nested positive exists`), on inline
graphs with the same structure as `exists01.ttl` / `exists02.ttl`:
default graph `:s :p :o, :o1, :o2 . :t :p :o1, :o2`; named graph `gTwo`
holds `:a :p :o1 . :b :p :o1, :o2`. -/

def pEx : WfIri := iriQ "https://example.org/p"
def oEx  : WfIri := iriQ "https://example.org/o"
def oEx1 : WfIri := iriQ "https://example.org/o1"
def oEx2 : WfIri := iriQ "https://example.org/o2"
def sEx : WfIri := iriQ "https://example.org/s"
def tEx : WfIri := iriQ "https://example.org/t"
def aEx : WfIri := iriQ "https://example.org/a"
def bEx : WfIri := iriQ "https://example.org/b"

def dsExists : Dataset :=
  { default := [ tr sEx pEx (.iri oEx), tr sEx pEx (.iri oEx1), tr sEx pEx (.iri oEx2),
                 tr tEx pEx (.iri oEx1), tr tEx pEx (.iri oEx2) ]
    named := [ { name := .iri gTwo,
                 graph := [ tr aEx pEx (.iri oEx1), tr bEx pEx (.iri oEx1), tr bEx pEx (.iri oEx2) ] } ] }

/-- `?s ?p <o1> FILTER EXISTS { ?s ?p <o2> }` — the EXISTS body shares
the outer row's variables, which `substitute(pattern, μ)` replaces. -/
def pExistsO2 : QueryPattern :=
  .filter (.existsPat (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx2 }]))
    (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }])

-- Against the default graph both subjects carry <o2>.
#guard colS "s" (rows dsExists (qAll pExistsO2)) == ["s", "t"]
-- exists03: inside `GRAPH <g2> { … }` the EXISTS sees the NAMED graph,
-- where only <b> carries <o2>.
#guard colS "s" (rows dsExists (qAll (.graph (.iri gTwo) pExistsO2))) == ["b"]
-- The same under `GRAPH ?g`: the active graph is the one being iterated.
#guard colS "s" (rows dsExists (qAll (.graph (.var "g") pExistsO2))) == ["b"]
-- exists04: a nested EXISTS is evaluated too (not an error → false).
#guard colS "s" (rows dsExists (qAll
    (.filter (.existsPat (.filter (.existsPat (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx2 }]))
                           (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }])))
      (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx }])))) == ["s"]
-- exists05: a nested NOT EXISTS inside a positive EXISTS: <s> has <o2>,
-- so the inner NOT EXISTS fails and no row survives.
#guard rows dsExists (qAll
    (.filter (.existsPat (.filter (.notExistsPat (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx2 }]))
                           (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }])))
      (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx }]))) == []
-- NOT EXISTS in the GRAPH case is the complement: <a> has no <o2>.
#guard colS "s" (rows dsExists (qAll (.graph (.iri gTwo)
    (.filter (.notExistsPat (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx2 }]))
      (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }]))))) == ["a"]
-- EXISTS in an OPTIONAL condition goes through `leftJoin`'s active graph.
#guard colS "s" (rows dsExists (qAll (.graph (.iri gTwo)
    (.leftJoin (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }]) .empty
      (.existsPat (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx2 }])))))) == ["a", "b"]
-- Without a dataset in the environment (no `evalSelect`), an EXISTS is
-- the expression-layer error, so FILTER drops every row.
#guard ((QueryPattern.lower emptyEnv pExistsO2).evalIn dsExists dsExists.default) == []

/-! ### Pattern blank nodes are non-distinguished variables — §18.3.1

Regression pin for https://github.com/danbri/factoidal/issues/607. A
blank node written in a query pattern is a NON-DISTINGUISHED VARIABLE
(SPARQL 1.1 §4.1.4, §18.3.1's pattern instance mapping): it matches any
RDF term and is not returned. `Algebra.tryBindSubject`/`tryBindTerm`
match it as a CONSTANT with that label; `Query.evalSelect` is what
repairs that, by running `QueryPattern.rewriteBnodes` first.

Before this pin the rewrite reached the WHERE clause but NOT an EXISTS
body carried inside a `FILTER` expression, so a blank node there still
matched as a constant and the filter dropped every row. Both trees had
that residue (the F* `factoidal query` binary returned no results on
the same query on 2026-08-26). -/

-- Top level: `?s ?p _:b` binds `?s` for every subject with any
-- object, because `_:b` matches any term.
#guard colS "s" (rows dsExists (qAll
    (.bgp [{ s := .var "s", p := .var "p", o := .bnode "b" }])))
  == ["s", "s", "s", "t", "t"]

-- `SELECT *` does not return the rewrite's variable (§18.2.4
-- OutScope): the header carries `?s` and `?p` only, in query order.
#guard hdr dsExists (qAll (.bgp [{ s := .var "s", p := .var "p", o := .bnode "b" }]))
  == ["s", "p"]

-- Inside an EXISTS body the same reading must hold: `<s> <p> _:b`
-- after substitution asks whether the row's subject has ANY object,
-- true for both subjects. Engine behaviour before the repair: `[]`.
#guard colS "s" (rows dsExists (qAll
    (.filter (.existsPat (.bgp [{ s := .var "s", p := .var "p", o := .bnode "e1" }]))
      (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }]))))
  == ["s", "t"]

-- NOT EXISTS is its complement: no subject lacks an object, so no
-- row survives. Before the repair this returned both rows, for the
-- wrong reason (the body matched nothing).
#guard rows dsExists (qAll
    (.filter (.notExistsPat (.bgp [{ s := .var "s", p := .var "p", o := .bnode "e2" }]))
      (.bgp [{ s := .var "s", p := .var "p", o := .iri oEx1 }])))
  == []

/-! ### The hash-indexed grouping agrees with the specification

`groupSolutionsFast` (hash buckets, rows newest first) must return exactly the
groups `groupSolutions` (`addToGroups` per row) returns: same keys, same first
appearance order, same rows in input order. The keys below are evaluated
values, so the cases that decide the bucket choice are exercised directly:
`1`, `1.0` and `1.0E0` denote distinct RDF terms across `xsd:integer`,
`xsd:decimal` and `xsd:double` and must remain separate groups; an unbound variable is an error key;
two literals that differ only in language tag or datatype are different
groups. -/

private def gkNum1  : EvalResult := .num 1
private def gkDec1  : EvalResult := .dec "1.0"
private def gkDbl1  : EvalResult := .dbl "1.0E0"
private def gkNum2  : EvalResult := .num 2
private def gkDec2  : EvalResult := .dec "2.00"
private def gkTrue  : EvalResult := .bool true
private def gkFalse : EvalResult := .bool false
private def gkErr   : EvalResult := .error
private def gkAlice : EvalResult := .term (.iri iAlice)
private def gkBob   : EvalResult := .term (.iri iBob)
private def gkBn    : EvalResult := .term (.bnode "b1")
private def gkLitEn : EvalResult := .term (.literal (Literal.langString "chat" "en"))
private def gkLitFr : EvalResult := .term (.literal (Literal.langString "chat" "fr"))
private def gkLitPl : EvalResult := .term (.literal (Literal.string "chat"))
private def gkLitI  : EvalResult := .term (nLit "1")

private def gkeys : List (List EvalResult) :=
  [ [gkNum1], [gkAlice], [gkDec1], [gkErr], [gkBob], [gkNum2], [gkDbl1], [gkTrue],
    [gkLitEn], [gkDec2], [gkLitFr], [gkAlice, gkNum1], [gkLitPl], [gkAlice, gkDec1],
    [gkBn], [gkFalse], [gkLitI], [gkErr], [gkBob, gkErr], [gkBn], [gkTrue], [gkLitEn],
    [gkNum1], [], [], [gkAlice, gkNum2] ]

/-- Row `i` carries its position, so rows are all distinct. -/
private def gkRows (cycles : Nat) : List (List EvalResult × Binding) :=
  (List.range (cycles * gkeys.length)).map (fun i =>
    (gkeys[i % gkeys.length]!, [("i", nLit (toString i))]))

private def gkShape (gs : List SolutionGroup) : List (List EvalResult × List Binding) :=
  gs.map (fun g => (g.key, g.solutions))

private def gkSpec (rows : List (List EvalResult × Binding)) : List SolutionGroup :=
  rows.foldl (fun gs (r : List EvalResult × Binding) => addToGroups r.1 r.2 gs) []

private def gkFast (rows : List (List EvalResult × Binding)) : List SolutionGroup :=
  (rows.foldl (fun acc (r : List EvalResult × Binding) => acc.add r.1 r.2)
    ({} : GroupAcc)).groups

#guard gkShape (gkFast []) == gkShape (gkSpec [])
#guard gkShape (gkFast (gkRows 1)) == gkShape (gkSpec (gkRows 1))
#guard gkShape (gkFast (gkRows 2)) == gkShape (gkSpec (gkRows 2))
#guard gkShape (gkFast (gkRows 7)) == gkShape (gkSpec (gkRows 7))

-- The groups are the expected ones, so a grouping that put every row in one
-- group, or every row in its own group, fails. Numeric value equality does
-- not erase RDF datatype or lexical spelling in one- or two-component keys.
#guard (gkFast (gkRows 3)).length == (gkSpec (gkRows 3)).length
#guard (gkFast (gkRows 3)).length > 10
#guard (gkFast (gkRows 3)).length < gkeys.length
#guard ((gkFast (gkRows 1)).head?.map (fun g => g.solutions.length)) == some 3
#guard ((gkFast (gkRows 2)).head?.map (fun g => g.solutions.length)) == some 6
#guard (gkFast (gkRows 3)).all (fun g => g.solutions.length > 1)
-- Rows keep their input order inside a group.
#guard ((gkFast (gkRows 1)).head?.map (fun g => g.solutions)) ==
  some [[("i", nLit "0")], [("i", nLit "16")], [("i", nLit "22")]]

-- These identity-distinct terms have distinct datatype/lexical bucket keys.
#guard keyBucket [gkNum1] != keyBucket [gkDec1] && keyBucket [gkDec1] != keyBucket [gkDbl1]
#guard keyBucket [gkAlice] != keyBucket [gkBob]
#guard keyBucket [gkLitEn] != keyBucket [gkLitFr]
#guard keyBucket [gkLitI] != keyBucket [gkLitPl]

/-! ### Aggregate DISTINCT: the indexed duplicate removal agrees with the scan

`dedupEr` is registered with `csimp` to compile as `dedupErFast`
(https://github.com/danbri/factoidal/issues/722), so a guard on `dedupEr` runs
the indexed code. `dedupErAcc` is not rewritten: these guards compare the
indexed code with the scan. The values are the first components of the group
keys above, repeated, so order-equal values of three numeric types, error
values, IRIs, blank nodes and literals that differ only in language tag or
datatype all occur. -/

private def dkVals (cycles : Nat) : List EvalResult :=
  (List.range (cycles * gkeys.length)).filterMap (fun i => (gkeys[i % gkeys.length]!).head?)

#guard dedupErFast [] == dedupErAcc [] []
#guard dedupErFast (dkVals 1) == dedupErAcc (dkVals 1) []
#guard dedupErFast (dkVals 5) == dedupErAcc (dkVals 5) []
#guard dedupEr (dkVals 3) == dedupErAcc (dkVals 3) []
-- RDF term identities remain distinct. Direct low-level dedup preserves
-- errors (no RDF term); aggregate callers remove them before deduplication.
-- There are thirteen distinct bound terms and eight errors in four cycles.
#guard (dedupErFast (dkVals 4)).length == 21
#guard dedupErFast [gkNum1, gkDec1, gkDbl1, gkNum2, gkDec2] == [gkNum1, gkDec1, gkDbl1, gkNum2, gkDec2]
#guard dedupErFast [gkDec1, gkNum1] == [gkDec1, gkNum1]
#guard dedupErFast [gkLitEn, gkLitFr, gkLitPl, gkLitEn, gkLitI] == [gkLitEn, gkLitFr, gkLitPl, gkLitI]
#guard dedupErFast [gkErr, gkErr, gkBn, gkBn, gkAlice] == [gkErr, gkErr, gkBn, gkAlice]

-- COUNT(DISTINCT *) counts distinct rows (the code runs `distinctSolutionsFast`,
-- `evalAggregate_countDistinctStar` restates it with `distinctSolutions`), and
-- COUNT(DISTINCT ?x) counts distinct bound values.
private def cdGroup : SolutionGroup :=
  { key := [], solutions :=
      [[("x", .iri iAlice)], [("x", .iri iBob)], [("x", .iri iAlice)], [], [],
       [("x", .iri iAlice), ("y", .iri iBob)], [("y", .iri iBob), ("x", .iri iAlice)]] }

#guard evalAggregate emptyEnv .count true (.var "*") cdGroup == .num 4
#guard evalAggregate emptyEnv .count true (.var "*") cdGroup ==
  .num (Int.ofNat (distinctSolutions cdGroup.solutions).length)
#guard evalAggregate emptyEnv .count false (.var "*") cdGroup == .num 7
#guard evalAggregate emptyEnv .count true (.var "x") cdGroup == .num 2
#guard evalAggregate emptyEnv .count false (.var "x") cdGroup == .num 5

/-! ### Axiom audit — the whole pipeline is definition-only -/

#print axioms GraphPattern.evalIn
#print axioms QueryPattern.lowerWith
#print axioms evalSelect
#print axioms evalConstruct
#print axioms evalPath


/-! ### ORDER BY order through the native string comparison

`strCompare` compiles to `strCompareFast` (`Expr.lean`, `csimp`). These check
that the §15.1 order still reads the code point order of IRIs, blank-node
labels and lexical forms, in both directions. -/

#guard sparqlOrder (.term (.iri (iriQ "http://e/a"))) (.term (.iri (iriQ "http://e/b"))) == -1
#guard sparqlOrder (.term (.iri (iriQ "http://e/b"))) (.term (.iri (iriQ "http://e/a"))) == 1
#guard sparqlOrder (.term (.iri (iriQ "http://e/a"))) (.term (.iri (iriQ "http://e/a"))) == 0
#guard sparqlOrder (.term (.bnode "b10")) (.term (.bnode "b2")) == -1
#guard sparqlOrder (.term (.literal (Literal.string "b"))) (.term (.literal (Literal.string "ab"))) == 1
#guard sparqlOrder (.term (.literal (Literal.string "Z"))) (.term (.literal (Literal.string "a"))) == -1
#guard erEqual (.term (.literal (Literal.string "x"))) (.term (.literal (Literal.string "x")))
#guard !erEqual (.term (.literal (Literal.string "x"))) (.term (.literal (Literal.string "X")))

/-! ### sameTerm over variable bindings (issue 794)

W3C SPARQL 1.0 `expr-builtin/sameTerm-simple` and `sameTerm-eq`: a
variable bound to a numeric or boolean literal is promoted to its value
for `=`, but `sameTerm` compares RDF terms (SPARQL 1.1 §17.4.1.8). Eight
objects: "1"^^integer twice, "01"^^integer, "1.0"^^decimal, "true" and
"1" booleans, "1.0e0" and "1.0" doubles. Terms equal under sameTerm: the
two "1"^^integer objects in both orders plus each object with itself. -/

def pSt : WfIri := iriQ "https://example.org/things#p"
def lt (lex : String) (dt : WfIri) : Term := .literal (mkTypedLiteral lex dt)

def gSame : Graph :=
  [ tr iAlice pSt (lt "1" xsdInteger),
    tr iBob   pSt (lt "1" xsdInteger),
    tr iCarol pSt (lt "01" xsdInteger),
    tr iDave  pSt (lt "1.0" xsdDecimal),
    tr iZed   pSt (lt "true" xsdBoolean),
    tr epOne  pSt (lt "1" xsdBoolean),
    tr epTwo  pSt (lt "1.0e0" xsdDouble),
    tr gOne   pSt (lt "1.0" xsdDouble) ]

def pSame : QueryPattern :=
  .bgp [tpv "x1" pSt (.var "v1"), tpv "x2" pSt (.var "v2")]

def dsSame : Dataset := { default := gSame, named := [] }

-- 8 self pairs plus the (x1, x2) and (x2, x1) pair of equal terms.
#guard (rows dsSame (qAll (.filter (.sameTerm (.var "v1") (.var "v2")) pSame))).length == 10
-- `=` is value equality: the six numeric objects of value 1 give 36
-- pairs and the two true booleans give 4, so it keeps more rows.
#guard (rows dsSame (qAll (.filter (.compare .eq (.var "v1") (.var "v2")) pSame))).length == 40
-- sameTerm and `=` together: sameTerm already decides, so 10 rows.
#guard (rows dsSame (qAll (.filter
    (.and (.sameTerm (.var "v1") (.var "v2")) (.compare .eq (.var "v1") (.var "v2"))) pSame))).length == 10

end L4Factoidal.SPARQL.QueryTests

-- Numeric ORDER BY preserves source rounding; NaN has one fixed position,
-- rather than tying every finite pair through an unordered intermediary.
#guard L4Factoidal.SPARQL.sparqlOrder (.dbl "1") (.dbl "NaN") == -1
#guard L4Factoidal.SPARQL.sparqlOrder (.dbl "NaN") (.dbl "2") == 1
#guard L4Factoidal.SPARQL.sparqlOrder (.dbl "NaN") (.dbl "NaN") == 0
#guard L4Factoidal.SPARQL.sparqlOrder (.dbl "1") (.dbl "2") == -1
#guard L4Factoidal.SPARQL.findMin [.dbl "NaN", .num 1] == .num 1
#guard L4Factoidal.SPARQL.findMax [.num 1, .dbl "NaN"] == .dbl "NaN"
