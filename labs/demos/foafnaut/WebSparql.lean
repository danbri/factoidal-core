import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StorePlan
import L4Factoidal.Planner.Kinds.Memory
import L4Factoidal.Planner.FromQuery
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Pretty
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-!
# WebSparql: the SPARQL planner, drawn as live debug

Document ops of the Foafnaut engine that show how Factoidal plans and runs a SPARQL query
(owner, 2026-11-08: "Could we have svg viz of sparql query planner as live debug?").
Every number on the page comes from the engine's own functions; this module only walks the
query, calls them, and writes the answer as JSON or as HTML with SVG.

- `sparqlInfo`: the ops and the datasets. Hosts call it first: an engine from before these ops
  answers "unknown document operation".
- `sparqlExplain`: `query`, `dataset` (`foaf`, the built-in sample, or `turtle` with `data`),
  `run` (default true). The answer has the operators in execution order (post-order), each with
  its kind, its text, its children, the planner's estimate, the rows it gave and its time, and
  why the planner chose it; the capability planner's plan for each basic graph pattern; and the
  first rows of the result.
- `sparqlPage`: the page `foafnaut:sparql`, as HTML that this engine lays out. `argument` is the
  part of the address after `foafnaut:sparql/`: `q=QUERY&step=N` with percent-encoding. With a
  step, only the first N operators have run; operator N is marked, and its rows are shown.

What each planner fact is:

- The operator tree is the query pattern as the parser gives it (`QueryPattern`), with the
  solution modifiers of SELECT above it. The rows of an operator are the rows of
  `GraphPattern.evalIn` for its sub-pattern, which is what `evalSelect` runs.
- A join, OPTIONAL or MINUS says the variables of its hash key: `joinKeyVars` of its two inputs,
  as `hashJoin`, `hashLeftJoin` and `hashMinus` choose them. No key variable: nested loop.
- Each basic graph pattern is expanded into the steps of the store planner
  (`StorePlan.evalBgpBackend` over the list backend of the same triples): for each partial
  solution it takes the pattern with the smallest estimate (`chooseBestTpBackend`,
  `estimateTpBackend`). A step's estimate is the sum of the estimates of the patterns chosen at
  that depth; its rows are the rows the full pattern match kept. The walk here is level by level
  and gives the same rows, in the same order, as `evalBgpBackend` (`WebSparqlTests.lean`).
- The capability planner (`Planner.search`, issue https://github.com/danbri/factoidal/issues/801)
  plans each basic graph pattern of at most `capLimit` patterns over the in-memory source kind
  (`Planner.Kinds.Memory.describe`): its plan family, the accesses of the first plan with the
  estimated calls, tuples and cost of `estUse`, and the rows each prefix of the plan gives.

Times come from the host clock through `timed`, whose logical model is time 0: a measurement,
not part of any result that a proof reads. An operator's time includes its inputs.
-/

set_option compiler.extract_closed false

namespace WebSparql
open L4Factoidal
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreBackend

/-! ## Time -/

private unsafe def timedImpl {α : Type} (f : Unit → α) : α × Nat :=
  let timing : IO (α × Nat) := do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure f
    let t1 ← IO.monoNanosNow
    pure (r, t1 - t0)
  match unsafeIO timing with
  | .ok r => r
  | .error _ => (f (), 0)

/-- `f ()` and the nanoseconds it took on the host clock. The logical model has time 0. -/
@[implemented_by timedImpl] def timed {α : Type} (f : Unit → α) : α × Nat := (f (), 0)

/-! ## The built-in dataset -/

/-- A synthetic FOAF sample: the people of `pages/foaf-demo.ttl`, with ages and some mailboxes
added so that FILTER, OPTIONAL and aggregates have something to do. -/
def foafSample : String :=
  "@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n" ++
  "@prefix ex: <https://example.org/friends/> .\n" ++
  "ex:alice a foaf:Person ; foaf:name \"Alice\" ; foaf:age 34 ; foaf:mbox <mailto:alice@example.org> ; foaf:knows ex:bob, ex:carol, ex:dan .\n" ++
  "ex:bob a foaf:Person ; foaf:name \"Bob\" ; foaf:age 27 ; foaf:knows ex:erin .\n" ++
  "ex:carol a foaf:Person ; foaf:name \"Carol\" ; foaf:age 41 ; foaf:mbox <mailto:carol@example.org> ; foaf:knows ex:farah .\n" ++
  "ex:dan a foaf:Person ; foaf:name \"Dan\" ; foaf:age 19 ; foaf:knows ex:grace .\n" ++
  "ex:erin a foaf:Person ; foaf:name \"Erin\" ; foaf:age 52 ; foaf:knows ex:hiro .\n" ++
  "ex:farah a foaf:Person ; foaf:name \"Farah\" ; foaf:age 30 ; foaf:mbox <mailto:farah@example.org> ; foaf:knows ex:alice .\n" ++
  "ex:grace a foaf:Person ; foaf:name \"Grace\" ; foaf:age 23 ; foaf:knows ex:hiro .\n" ++
  "ex:hiro a foaf:Person ; foaf:name \"Hiro\" ; foaf:age 45 .\n" ++
  "ex:rome a foaf:Organization ; foaf:name \"Rome Lab\" ; foaf:member ex:alice, ex:erin .\n"

def foafBase : String := "https://example.org/friends/"

/-! ## Short text for terms, patterns and expressions -/

def prefixes : PrefixTable :=
  [("http://xmlns.com/foaf/0.1/", "foaf:"), ("https://example.org/friends/", "ex:"),
   ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:"), ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:"),
   ("http://www.w3.org/2001/XMLSchema#", "xsd:")]

def numericTypes : List String :=
  ["http://www.w3.org/2001/XMLSchema#integer", "http://www.w3.org/2001/XMLSchema#decimal",
   "http://www.w3.org/2001/XMLSchema#double"]

def termShort (t : Term) : String :=
  match t with
  | .literal wl =>
    if wl.val.langTag.isNone && numericTypes.contains wl.val.datatype.val then wl.val.lexicalForm
    else termWithPrefixes prefixes t
  | .iri i => if i.val == "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" then "a" else termWithPrefixes prefixes t
  | _ => termWithPrefixes prefixes t

def ptShort (pt : PatternTerm) : String :=
  match pt with
  | .iri i => termShort (.iri i)
  | .literal l => termShort (.literal l)
  | _ => patternTermShort prefixes pt

def psShort (ps : PatternSubject) : String :=
  match ps with
  | .iri i => termShort (.iri i)
  | _ => patternSubjectShort prefixes ps

def tpShort (tp : TriplePattern) : String := psShort tp.s ++ " " ++ ptShort tp.p ++ " " ++ ptShort tp.o

def compName : CompOp → String
  | .eq => "=" | .ne => "!=" | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="

def arithName : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

def aggName : AggregateFn → String
  | .count => "COUNT" | .sum => "SUM" | .min => "MIN" | .max => "MAX" | .avg => "AVG"
  | .groupConcat _ => "GROUP_CONCAT" | .sample => "SAMPLE"

/-- An expression as short text; `n` bounds the depth shown. -/
def exprShort : Nat → Expr → String
  | 0, _ => "..."
  | n + 1, e =>
    match e with
    | .var v => "?" ++ v
    | .iri i => termShort (.iri i)
    | .lit l => termShort (.literal l)
    | .boolLit b => toString b
    | .numericLit k => toString k
    | .decimalLit s => s
    | .doubleLit s => s
    | .arith op l r => "(" ++ exprShort n l ++ " " ++ arithName op ++ " " ++ exprShort n r ++ ")"
    | .compare op l r => exprShort n l ++ " " ++ compName op ++ " " ++ exprShort n r
    | .and l r => exprShort n l ++ " && " ++ exprShort n r
    | .or l r => "(" ++ exprShort n l ++ " || " ++ exprShort n r ++ ")"
    | .not a => "!" ++ exprShort n a
    | .bound v => "BOUND(?" ++ v ++ ")"
    | .str a => "STR(" ++ exprShort n a ++ ")"
    | .lang a => "LANG(" ++ exprShort n a ++ ")"
    | .regex a p _ => "REGEX(" ++ exprShort n a ++ ", " ++ exprShort n p ++ ")"
    | .contains a b => "CONTAINS(" ++ exprShort n a ++ ", " ++ exprShort n b ++ ")"
    | .strStarts a b => "STRSTARTS(" ++ exprShort n a ++ ", " ++ exprShort n b ++ ")"
    | .existsPat _ => "EXISTS {...}"
    | .notExistsPat _ => "NOT EXISTS {...}"
    | .aggregate fn d a => aggName fn ++ "(" ++ (if d then "DISTINCT " else "") ++ exprShort n a ++ ")"
    | _ => "expr"

def pathShort : Nat → PropertyPath → String
  | 0, _ => "..."
  | n + 1, p =>
    match p with
    | .iri i => termShort (.iri i)
    | .inverse a => "^" ++ pathShort n a
    | .sequence a b => pathShort n a ++ "/" ++ pathShort n b
    | .alternative a b => "(" ++ pathShort n a ++ "|" ++ pathShort n b ++ ")"
    | .zeroOrMore a => pathShort n a ++ "*"
    | .oneOrMore a => pathShort n a ++ "+"
    | .zeroOrOne a => pathShort n a ++ "?"
    | .negatedSet ps => "!(" ++ "|".intercalate (ps.map (pathShort n)) ++ ")"

def varsText (vs : List VarName) : String :=
  if vs.isEmpty then "none" else " ".intercalate (vs.map ("?" ++ ·))

/-! ## Operators -/

/-- One operator of the plan. `children` are indices of earlier operators. -/
structure Op where
  kind : String
  label : String
  why : String := ""
  children : List Nat := []
  /-- The planner's estimate of the rows out, where a planner makes one. -/
  est : Option Nat := none
  /-- The rows out, when the operator ran. -/
  actual : Option Nat := none
  ns : Nat := 0
  sample : List Binding := []
  deriving Inhabited

/-- Rows kept as a sample of an operator's output. -/
def sampleSize : Nat := 8

structure Ctx where
  env : EvalEnv
  ds : Dataset
  g : Graph
  run : Bool := true

def evalPattern (c : Ctx) (p : QueryPattern) : SolutionSeq :=
  (p.lower c.env).evalIn c.ds c.g

def push (ops : Array Op) (op : Op) : Array Op × Nat := (ops.push op, ops.size)

/-- An operator whose rows are the rows of its own sub-pattern. -/
def patternOp (c : Ctx) (p : QueryPattern) (op : Op) (ops : Array Op) : Array Op × Nat :=
  if c.run then
    let (rows, ns) := timed fun _ => evalPattern c p
    push ops { op with actual := some rows.length, ns := ns, sample := rows.take sampleSize }
  else push ops op

/-- The hash key a join of `l` and `r` uses, as `hashJoin` chooses it. -/
def keyWhy (c : Ctx) (what : String) (l r : QueryPattern) : String :=
  if !c.run then s!"{what}." else
  match joinKeyVars (evalPattern c l) (evalPattern c r) with
  | [] => s!"{what}: no variable is bound in every row of both inputs, so a nested loop (joinKeyVars is empty)."
  | ks => s!"{what}: hash table on {varsText ks}, the variables bound in every row of both inputs (joinKeyVars)."

/-! ### A basic graph pattern, as the store planner runs it -/

/-- One depth of the store planner's run: which pattern it took for how many rows, the sum of
the estimates of the patterns it took, and the rows out. -/
structure Level where
  chosen : List (Nat × Nat)
  est : Nat
  rows : SolutionSeq
  ns : Nat

def bump (xs : List (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
  if xs.any (·.1 == i) then xs.map (fun (j, k) => if j == i then (j, k + 1) else (j, k)) else xs ++ [(i, 1)]

def indexIn (b : Bgp) (tp : TriplePattern) : Nat := (b.findIdx? (· == tp)).getD 0

/-- One depth for every partial solution, as `evalBgpFromMuFuel` does it for one: choose the
pattern with the smallest estimate under the row (`chooseBestTpBackend`), then match it. -/
def levelStep (gb : GraphBackend) (b : Bgp) (frontier : List (Binding × Bgp)) :
    List (Binding × Bgp) × List (Nat × Nat) × Nat :=
  let (out, ch, est) := frontier.foldl (fun (out, ch, est) (mu, rem) =>
    match chooseBestTpBackend gb mu rem with
    | none => ((mu, []) :: out, ch, est)
    | some (tp, rest) =>
      let rows := evalSingleTpBackend tp gb mu
      (rows.foldl (fun acc r => (r, rest) :: acc) out, bump ch (indexIn b tp), est + estimateTpBackend tp gb mu))
    ([], [], 0)
  (out.reverse, ch, est)

/-- The store planner's run of `b`, depth by depth. -/
def traceBgp (gb : GraphBackend) (b : Bgp) : List Level :=
  let (_, levels) := (List.range b.length).foldl (fun (frontier, acc) _ =>
    let ((next, ch, est), ns) := timed fun _ => levelStep gb b frontier
    (next, { chosen := ch, est := est, rows := next.map Prod.fst, ns := ns } :: acc))
    ([(Binding.empty, b)], [])
  levels.reverse

/-- The rows of the store planner's run: the rows of its last depth. -/
def traceRows (gb : GraphBackend) (b : Bgp) : SolutionSeq :=
  match (traceBgp gb b).getLast? with
  | some l => l.rows
  | none => [Binding.empty]

def boundText (tp : TriplePattern) : String :=
  let pos := (if (boundSubjectOfPattern tp.s Binding.empty).isSome then ["s"] else []) ++
    (if (boundPredicateOfPattern tp.p Binding.empty).isSome then ["p"] else []) ++
    (if (boundObjectOfPattern tp.o Binding.empty).isSome then ["o"] else [])
  if pos.isEmpty then "nothing bound" else "bound " ++ " ".intercalate pos

def levelWhy (gb : GraphBackend) (b : Bgp) (d : Nat) (l : Level) (inRows : Nat) : String :=
  if d == 0 then
    let alts := b.map (fun tp => s!"{tpShort tp} estimate {estimateTpBackend tp gb Binding.empty} ({boundText tp})")
    "First pattern: the smallest estimate with nothing bound (chooseBestTpBackend; a tie goes to the earlier pattern). " ++
      "Estimates: " ++ "; ".intercalate alts ++ "."
  else
    let picks := l.chosen.map (fun (i, k) => s!"{(b[i]?.map tpShort).getD "?"} for {k} rows")
    s!"For each of {inRows} partial solutions, the pattern left with the smallest estimate under that row's bindings: " ++
      "; ".intercalate picks ++ ". The estimate is the backend's count of triples that match the bound positions; the full match then keeps the rows."

def levelLabel (b : Bgp) (l : Level) : String :=
  match l.chosen with
  | [(i, _)] => (b[i]?.map tpShort).getD "?"
  | (i, _) :: _ => (b[i]?.map tpShort).getD "?" ++ " (and others, per row)"
  | [] => "no row"

/-- The steps of a BGP, each the input of the next, then the BGP itself. -/
def bgpOps (c : Ctx) (p : QueryPattern) (b : Bgp) (ops : Array Op) : Array Op × Nat :=
  let gb := GraphBackend.list c.g
  let label := s!"BGP, {b.length} pattern" ++ (if b.length == 1 then "" else "s")
  if !c.run || b.isEmpty then patternOp c p { kind := "bgp", label := label } ops else
  let levels := traceBgp gb b
  let (ops, last, _, _) := levels.foldl (fun (ops, prev, d, inRows) l =>
    let op : Op := { kind := if d == 0 then "scan" else "probe", label := levelLabel b l,
                     why := levelWhy gb b d l inRows, children := prev.toList,
                     est := some l.est, actual := some l.rows.length, ns := l.ns, sample := l.rows.take sampleSize }
    let (ops, i) := push ops op
    (ops, some i, d + 1, l.rows.length)) (ops, none, 0, 1)
  patternOp c p
    { kind := "bgp", label := label, children := last.toList,
      why := "In-memory evaluation (GraphPattern.evalIn) runs a BGP in written order with an index per pattern; " ++
        "the steps below it are the store planner's run (StorePlan.evalBgpBackend) over the same triples, which orders patterns by estimate. Both give the same rows." } ops

/-! ### The query pattern -/

def leafOp (c : Ctx) (p : QueryPattern) (kind label why : String) (ops : Array Op) : Array Op × Nat :=
  patternOp c p { kind := kind, label := label, why := why } ops

/-- The operators of a query pattern, children first. `n` bounds the depth walked. -/
def walk (c : Ctx) : Nat → QueryPattern → Array Op → Array Op × Nat
  | 0, p, ops => leafOp c p "pattern" "pattern nested too deep to show" "" ops
  | n + 1, p, ops =>
    match p with
    | .bgp b => bgpOps c p b ops
    | .join l r =>
      let (ops, a) := walk c n l ops
      let (ops, b) := walk c n r ops
      patternOp c p { kind := "join", label := "Join", why := keyWhy c "Join" l r, children := [a, b] } ops
    | .leftJoin l r e =>
      let (ops, a) := walk c n l ops
      let (ops, b) := walk c n r ops
      let cond := match e with | .boolLit true => "" | _ => " FILTER " ++ exprShort 6 e
      patternOp c p
        { kind := "leftjoin", label := "LeftJoin (OPTIONAL)" ++ cond,
          why := keyWhy c "OPTIONAL keeps each left row, extended where the right side matches" l r, children := [a, b] } ops
    | .filter e q =>
      let (ops, a) := walk c n q ops
      patternOp c p
        { kind := "filter", label := "Filter " ++ exprShort 6 e,
          why := "Keeps the rows whose condition has the effective boolean value true (SPARQL 1.1 section 17.2.2).", children := [a] } ops
    | .union l r =>
      let (ops, a) := walk c n l ops
      let (ops, b) := walk c n r ops
      patternOp c p { kind := "union", label := "Union", why := "The rows of the left side, then the rows of the right side.", children := [a, b] } ops
    | .minus l r =>
      let (ops, a) := walk c n l ops
      let (ops, b) := walk c n r ops
      patternOp c p { kind := "minus", label := "Minus", why := keyWhy c "Minus" l r, children := [a, b] } ops
    | .graph g q =>
      let (ops, a) := walk c n q ops
      patternOp c p { kind := "graph", label := "Graph " ++ ptShort g, children := [a] } ops
    | .lateral l r =>
      let (ops, a) := walk c n l ops
      let (ops, b) := walk c n r ops
      patternOp c p { kind := "join", label := "Lateral", why := "The right side runs once for each left row.", children := [a, b] } ops
    | .bind e v q =>
      let (ops, a) := walk c n q ops
      patternOp c p { kind := "extend", label := s!"Extend ?{v} := {exprShort 6 e}", children := [a] } ops
    | .values vs rows => leafOp c p "values" s!"Values {varsText vs}, {rows.length} rows" "Inline data." ops
    | .service i _ _ => leafOp c p "service" ("Service " ++ termShort (.iri i)) "No endpoint is registered on this page, so a SERVICE call fails." ops
    | .serviceVar v _ _ => leafOp c p "service" ("Service ?" ++ v) "No endpoint is registered on this page." ops
    | .subSelect _ => leafOp c p "subquery" "Sub-SELECT" "Its own pattern and modifiers, run as one operator here." ops
    | .propertyPath s path o =>
      leafOp c p "path" (psShort s ++ " " ++ pathShort 8 path ++ " " ++ ptShort o)
        "Property path (SPARQL 1.1 section 9): evaluated by the path evaluator, not by the BGP planner." ops
    | .empty => leafOp c p "empty" "Empty group {}" "One solution with no bindings." ops

/-! ### Solution modifiers -/

def selectItemText : SelectItem → String
  | .var v => "?" ++ v
  | .expr e v => s!"({exprShort 6 e} AS ?{v})"

def groupText : GroupCondition → String
  | .var v => "?" ++ v
  | .expr e (some v) => s!"({exprShort 6 e} AS ?{v})"
  | .expr e none => exprShort 6 e

/-- The modifiers of a SELECT above its pattern. Their rows are not counted one by one, except
the groups, which `groupWhere` gives; the top operator has the rows of the query. -/
def modifierOps (c : Ctx) (q : Query) (root : Nat) (rows : Option SolutionSeq) (ops : Array Op) : Array Op × Nat :=
  let step := fun (st : Array Op × Nat) (op : Op) => push st.1 { op with children := [st.2] }
  let sel := match q.form with | .select s => some s | _ => none
  let groups := q.groupBy.isSome || (sel.map selectHasAggregates).getD false
  let (ops, prev) :=
    if groups then
      let omega := if c.run then some (evalPattern c q.pattern) else none
      let count := omega.map (fun o => (groupWhere c.env q.groupBy o).length)
      let label := match q.groupBy with
        | some gs => "Group by " ++ " ".intercalate (gs.map groupText)
        | none => "Group (one group: an aggregate with no GROUP BY)"
      step (ops, root)
        { kind := "group", label := label, actual := count,
          why := "groupWhere: one group for each distinct key; the aggregates are computed over each group." }
    else (ops, root)
  let (ops, prev) := if q.having.isEmpty then (ops, prev) else
    step (ops, prev) { kind := "modifier", label := "Having " ++ " && ".intercalate (q.having.map (exprShort 6)) }
  let m := q.modifier
  let (ops, prev) := match m.orderBy with
    | some os => step (ops, prev) { kind := "modifier", label := s!"Order by ({os.length} keys)" }
    | none => (ops, prev)
  let proj := match sel with
    | some (.vars items) => "Project " ++ " ".intercalate (items.map selectItemText)
    | some .all => "Project *"
    | none => "Query form (not SELECT)"
  let tail := m.distinct || m.reduced || m.offset.isSome || m.limit.isSome
  let final := fun (op : Op) => match rows with
    | some rs => { op with actual := some rs.length, sample := rs.take sampleSize }
    | none => op
  let projOp : Op := { kind := "modifier", label := proj }
  let (ops, prev) := step (ops, prev) (if tail then projOp else final projOp)
  if !tail then (ops, prev) else
  let words := (if m.distinct then ["Distinct"] else []) ++ (if m.reduced then ["Reduced"] else []) ++
    (match m.offset with | some o => [s!"Offset {o}"] | none => []) ++
    (match m.limit with | some l => [s!"Limit {l}"] | none => [])
  step (ops, prev) (final { kind := "modifier", label := " ".intercalate words })

/-! ## The capability planner, for each basic graph pattern -/

open L4Factoidal.Planner in
/-- The memory source kind over the graph: the predicate form when every predicate is an IRI,
the triple form otherwise (as the planner tests do). -/
def capCatalog (g : Graph) (b : Bgp) : Catalog :=
  match Kinds.Memory.describe g with
  | .error _ => []
  | .ok ds =>
    let ds := if b.all (fun tp => match tp.p with | .iri _ => true | _ => false)
      then Kinds.partitioned ds else ds.filter (·.partition.isNone)
    ds.map (Kinds.graphSource · g)

/-- Basic graph patterns with more patterns are not given to the capability planner: its
search grows with the number of candidate accesses to the power of the pattern count. -/
def capLimit : Nat := 4

structure CapStep where
  source : String
  args : String
  inputs : String
  estCalls : Nat
  estRows : Nat
  estCost : Nat
  rows : Nat

structure CapPlan where
  bgpOp : Nat
  family : Nat
  approx : Bool
  cost : Nat
  steps : List CapStep
  rows : Nat
  note : String := ""

open L4Factoidal.Planner in
def argText : Arg → String
  | .const t => termShort t
  | .var v => if v.startsWith "_:" then v else "?" ++ v

open L4Factoidal.Planner in
def capPlan (c : Ctx) (opIndex : Nat) (b : Bgp) : CapPlan :=
  let none_ := fun (why : String) => ({ bgpOp := opIndex, family := 0, approx := false, cost := 0, steps := [], rows := 0, note := why } : CapPlan)
  if b.length > capLimit then none_ s!"Not planned here: {b.length} patterns, more than {capLimit}."
  else if !b.all tpFlat then none_ "Not planned: a triple term in a pattern (FromQuery.tpFlat)."
  else
  let req : Requirement := { bgp := b.map tpBnodeToVar, projection := (bgpVars b).eraseDups }
  let cat := capCatalog c.g b
  match search cat req b.length with
  | [] => none_ "No rewriting: the planner found no plan over the memory sources (notAnswerable)."
  | fam@(best :: _) =>
    let steps := best.rewriting.steps
    -- estUse gives the uses in reverse order (its accumulator).
    let uses := (estUse cat (statModel 10) steps).reverse
    let rowsAfter := fun (i : Nat) => if c.run then ((chainPlan (steps.take (i + 1))).run cat).length else 0
    let capSteps := (steps.zip uses).zipIdx.map (fun (x : (Access × UseEst) × Nat) =>
      let ((a, u), i) := x
      let cap := (cat[a.src]?.map (fun (s : Source) => s.cap))
      ({ source := (cap.map (·.name)).getD "?",
         args := ", ".intercalate (a.args.map argText),
         inputs := match cap with
           | some k => if k.inputs.isEmpty then "none (scan)" else ", ".intercalate (k.inputs.filterMap (fun j => a.args[j]?.map argText))
           | none => "?",
         estCalls := u.calls, estRows := u.rows, estCost := u.cost, rows := rowsAfter i } : CapStep))
    { bgpOp := opIndex, family := fam.length, approx := best.approx, cost := best.cost, steps := capSteps,
      rows := if c.run then ((best.rewriting.toPlan req).run cat).length else 0 }

/-- The BGPs of a pattern with the index of their operator: the operators are pushed in the
order `walk` pushes them, so the BGP operators are found by kind in that order. -/
def bgpsOf : Nat → QueryPattern → List Bgp
  | 0, _ => []
  | n + 1, p =>
    match p with
    | .bgp b => [b]
    | .join l r | .leftJoin l r _ | .union l r | .minus l r | .lateral l r => bgpsOf n l ++ bgpsOf n r
    | .filter _ q | .graph _ q | .bind _ _ q => bgpsOf n q
    | _ => []

/-! ## The explanation -/

structure Explained where
  query : Query
  pattern : QueryPattern
  ops : Array Op
  caps : List CapPlan
  wholeQuery : Bool
  vars : List VarName
  rows : SolutionSeq
  answer : String
  ns : Nat

def walkDepth : Nat := 64

def datasetOf (request : JSON.Json) : Except String Graph := do
  let name := match request.field? "dataset" with | some (.string s) => s | _ => "foaf"
  if name == "foaf" then
    match Syntax.parseTurtle foafSample (some foafBase) with
    | .ok g => return g
    | .error e => throw s!"the built-in dataset does not parse: {e}"
  else if name == "turtle" then
    let data := match request.field? "data" with | some (.string s) => s | _ => ""
    if data.length > 262144 then throw "the data has more than 262144 characters"
    match Syntax.parseTurtle data none with
    | .ok g => return g
    | .error e => throw s!"the Turtle data does not parse: {e}"
  else throw s!"unknown dataset {name}: use foaf or turtle"

def maxQueryChars : Nat := 8192

def explain (text : String) (g : Graph) (run : Bool := true) : Except String Explained := do
  if text.length > maxQueryChars then throw s!"the query has more than {maxQueryChars} characters"
  let q ← match parseSparql text (some foafBase) with
    | .ok q => pure q
    | .error e => throw s!"parse error: {e}"
  let ds : Dataset := { default := g, named := [] }
  let c : Ctx := { env := { dataset := some ds, base := some foafBase }, ds := ds, g := g, run := run }
  let pattern := q.pattern.rewriteBnodes
  let ((vars, rows, answer), ns) := timed fun _ =>
    if !run then (([] : List VarName), ([] : SolutionSeq), "not run") else
    match q.form with
    | .select _ =>
      match evalSelect c.env ds q with
      | (vs, rs) => (vs, rs, s!"{rs.length} rows")
    | .ask => ([], [], if evalAsk c.env ds q then "true" else "false")
    | .construct _ => ([], [], s!"{(evalConstruct c.env ds q).length} triples")
    | .describe _ => ([], [], s!"{(evalDescribe c.env ds q).length} triples")
  let (ops, root) := walk c walkDepth pattern #[]
  let isSelect := match q.form with | .select _ => true | _ => false
  let (ops, _) := if isSelect then modifierOps c q root (if run then some rows else none) ops else (ops, root)
  let bgpIdx := (List.range ops.size).filter (fun i => (ops[i]?.map (·.kind)).getD "" == "bgp")
  let caps := (bgpIdx.zip (bgpsOf walkDepth pattern)).map (fun (i, b) => capPlan c i b)
  return { query := q, pattern := pattern, ops := ops, caps := caps,
           wholeQuery := (Planner.Requirement.ofQuery? q).isSome, vars := vars, rows := rows, answer := answer, ns := ns }

/-! ## JSON -/

def num (n : Nat) : JSON.Json := .number (toString n)
def optNum : Option Nat → JSON.Json
  | some n => num n
  | none => .null

def rowJSON (vars : List VarName) (mu : Binding) : JSON.Json :=
  .object (vars.map fun v => (v, match mu.lookup v with | some t => .string (termShort t) | none => .null))

def bindingVars (rows : List Binding) : List VarName :=
  (rows.flatMap (fun mu => mu.map Prod.fst)).eraseDups.filter (fun v => !v.startsWith "_:")

def opJSON (i : Nat) (op : Op) : JSON.Json :=
  .object [("id", num i), ("kind", .string op.kind), ("label", .string op.label), ("why", .string op.why),
    ("children", .array (op.children.map num)), ("estimate", optNum op.est), ("actual", optNum op.actual),
    ("ns", num op.ns)]

def capJSON (cp : CapPlan) : JSON.Json :=
  .object [("bgp", num cp.bgpOp), ("family", num cp.family), ("approximate", .bool cp.approx), ("cost", num cp.cost),
    ("rows", num cp.rows), ("note", .string cp.note),
    ("steps", .array (cp.steps.map fun s => .object [("source", .string s.source), ("args", .string s.args),
      ("inputs", .string s.inputs), ("estimatedCalls", num s.estCalls), ("estimatedRows", num s.estRows),
      ("estimatedCost", num s.estCost), ("rows", num s.rows)]))]

def maxRowsJSON : Nat := 50

def explainJSON (e : Explained) : String :=
  let form := match e.query.form with
    | .select _ => "select" | .ask => "ask" | .construct _ => "construct" | .describe _ => "describe"
  (JSON.Json.object [("ok", .bool true), ("form", .string form),
    ("operators", .array (e.ops.toList.zipIdx.map fun (op, i) => opJSON i op)),
    ("root", num (e.ops.size - 1)),
    ("capability", .array (e.caps.map capJSON)),
    ("capabilityWholeQuery", .bool e.wholeQuery),
    ("answer", .string e.answer), ("ns", num e.ns),
    ("vars", .array (e.vars.map .string)),
    ("rows", .array ((e.rows.take maxRowsJSON).map (rowJSON e.vars))), ("rowCount", num e.rows.length)]).toString

/-! ## The address: `q=QUERY&step=N` -/

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

def decodeGo : List Char → List UInt8 → List UInt8
  | '%' :: a :: b :: rest, acc =>
    match hexVal a, hexVal b with
    | some x, some y => decodeGo rest ((x * 16 + y).toUInt8 :: acc)
    | _, _ => decodeGo (a :: b :: rest) (37 :: acc)
  | '+' :: rest, acc => decodeGo rest (32 :: acc)
  | c :: rest, acc => decodeGo rest ((String.singleton c).toUTF8.toList.reverse ++ acc)
  | [], acc => acc.reverse

/-- Percent-decoding, with `+` for a space. -/
def decode (s : String) : String :=
  (String.fromUTF8? (ByteArray.mk (decodeGo s.toList []).toArray)).getD s

def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList[n % 16]!

/-- Percent-encoding of every byte but letters, digits and `-_.`; a space is `+`. -/
def encode (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if (c.isAlphanum && b.toNat < 128) || c == '-' || c == '_' || c == '.' then c.toString
    else if c == ' ' then "+"
    else String.ofList ['%', hexDigit (b.toNat / 16), hexDigit b.toNat])

def param (argument key : String) : Option String :=
  (argument.splitOn "&").findSome? fun part =>
    match part.splitOn "=" with
    | k :: rest => if k == key then some (decode ("=".intercalate rest)) else none
    | [] => none

def pageURL (query : String) (step : Option Nat := none) : String :=
  "foafnaut:sparql/q=" ++ encode query ++ (match step with | some n => s!"&step={n}" | none => "")

/-! ## The page `foafnaut:sparql` -/

structure Example where
  name : String
  query : String

def examples : List Example :=
  [ { name := "BGP join", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nSELECT ?name ?friend WHERE {\n  ?p foaf:name ?name .\n  ?p foaf:knows ?f .\n  ?f foaf:name ?friend .\n  ?p foaf:mbox ?m .\n}" },
    { name := "OPTIONAL", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nSELECT ?name ?mbox WHERE {\n  ?p a foaf:Person ; foaf:name ?name .\n  OPTIONAL { ?p foaf:mbox ?mbox }\n}" },
    { name := "FILTER", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nSELECT ?name ?age WHERE {\n  ?p foaf:name ?name ; foaf:age ?age .\n  FILTER(?age > 30)\n}" },
    { name := "UNION", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nSELECT ?x ?y WHERE {\n  { ?x foaf:knows ?y }\n  UNION\n  { ?y foaf:member ?x }\n}" },
    { name := "Aggregate", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nSELECT ?name (COUNT(?f) AS ?friends) WHERE {\n  ?p foaf:name ?name ; foaf:knows ?f .\n}\nGROUP BY ?name\nORDER BY DESC(?friends)" },
    { name := "Property path", query := "PREFIX foaf: <http://xmlns.com/foaf/0.1/>\nPREFIX ex: <https://example.org/friends/>\nSELECT ?name WHERE {\n  ex:alice foaf:knows+ ?p .\n  ?p foaf:name ?name .\n}" } ]

def escape (value : String) : String :=
  String.join (value.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else if c.toNat < 32 then " " else c.toString)

def ms (ns : Nat) : String :=
  let us := ns / 1000
  if us < 1000 then s!"{us} us" else s!"{us / 1000}.{(us % 1000) / 100} ms"

/-- The fill of an operator kind. -/
def kindColour : String → String
  | "scan" => "#2a6fb0" | "probe" => "#4a90d0" | "bgp" => "#184078"
  | "join" => "#a0186a" | "leftjoin" => "#c8508a" | "minus" => "#7a1040"
  | "filter" => "#c87800" | "union" => "#1a8a40" | "path" => "#008080"
  | "extend" => "#806000" | "values" => "#606060" | "group" => "#5a3a9a"
  | "modifier" => "#7a68b0" | _ => "#506070"

def kindNames : List (String × String) :=
  [("scan", "first pattern of a BGP (store planner)"), ("probe", "next pattern, per partial solution"),
   ("bgp", "basic graph pattern"), ("join", "join"), ("leftjoin", "OPTIONAL"), ("minus", "MINUS"),
   ("filter", "FILTER"), ("union", "UNION"), ("path", "property path"), ("extend", "BIND"),
   ("values", "VALUES"), ("group", "GROUP BY and aggregates"), ("modifier", "projection and other modifiers")]

/-! ### The SVG: operator boxes with numbers, edges as wide as their rows -/

/-- Segments of a seven-segment digit, in a 7 by 12 cell: a b c d e f g. -/
def segments : List (Nat × Nat × Nat × Nat) :=
  [(0,0,7,0), (7,0,7,6), (7,6,7,12), (0,12,7,12), (0,6,0,12), (0,0,0,6), (0,6,7,6)]

def digitMask : Nat → List Bool
  | 0 => [true,true,true,true,true,true,false]
  | 1 => [false,true,true,false,false,false,false]
  | 2 => [true,true,false,true,true,false,true]
  | 3 => [true,true,true,true,false,false,true]
  | 4 => [false,true,true,false,false,true,true]
  | 5 => [true,false,true,true,false,true,true]
  | 6 => [true,false,true,true,true,true,true]
  | 7 => [true,true,true,false,false,false,false]
  | 8 => [true,true,true,true,true,true,true]
  | _ => [true,true,true,true,false,true,true]

def digitsOf (n : Nat) : List Nat := (toString n).toList.map (fun c => c.toNat - 48)

/-- A number drawn as strokes centred on (cx, cy). -/
def numberPath (n : Nat) (cx cy : Int) : String :=
  let ds := digitsOf n
  let w : Int := ds.length * 11 - 4
  let x0 := cx - w / 2
  let y0 := cy - 6
  String.join (ds.zipIdx.map fun (d, i) =>
    String.join ((segments.zip (digitMask d)).map fun ((ax, ay, bx, by_), on) =>
      if on then
        let ox := x0 + i * 11
        s!"M{ox + ax} {y0 + ay}L{ox + bx} {y0 + by_}"
      else ""))

/-- Depth from the root, and the leaf column of each operator, by a walk from the root. -/
def placeGo (ops : Array Op) : Nat → Nat → Nat → Array (Nat × Float) → Nat → Array (Nat × Float) × Nat
  | 0, _, _, pos, col => (pos, col)
  | fuel + 1, i, depth, pos, col =>
    match ops[i]? with
    | none => (pos, col)
    | some op =>
      if op.children.isEmpty then (pos.set! i (depth, col.toFloat), col + 1)
      else
        let (pos, col) := op.children.foldl (fun (pos, col) ch => placeGo ops fuel ch (depth + 1) pos col) (pos, col)
        let xs := op.children.map (fun ch => ((pos[ch]?.getD (0, 0.0) : Nat × Float)).2)
        let x := xs.foldl (· + ·) 0 / xs.length.toFloat
        (pos.set! i (depth, x), col)

def strokeWidth (n : Nat) : Float :=
  let w := 1.0 + 1.6 * (Nat.log2 (n + 1)).toFloat
  if w > 14 then 14 else w

/-- A non-negative length with one decimal. -/
def fmt (x : Float) : String :=
  let t := (if x < 0 then 0 else x * 10).round.toUInt64.toNat
  if t % 10 == 0 then toString (t / 10) else s!"{t / 10}.{t % 10}"

def boxW : Float := 56
def boxH : Float := 30
def colW : Float := 76
def rowH : Float := 74
def margin : Float := 20

/-- `done i`: operator `i` has run. `current`: the operator of this step. -/
def planSVG (ops : Array Op) (done : Nat → Bool) (current : Option Nat) : String :=
  if ops.isEmpty then "" else
  let root := ops.size - 1
  let (pos, cols) := placeGo ops (ops.size + 1) root 0 (Array.replicate ops.size (0, 0.0)) 0
  let depthMax := pos.foldl (fun (m : Nat) (p : Nat × Float) => max m p.1) 0
  let width := margin * 2 + (max 1 cols).toFloat * colW
  let height := margin * 2 + (depthMax + 1).toFloat * rowH
  -- The root is at the top: y grows with depth.
  let posOf := fun (i : Nat) => (pos[i]?.getD (0, 0.0) : Nat × Float)
  let cx := fun (i : Nat) => margin + colW / 2 + (posOf i).2 * colW
  let cy := fun (i : Nat) => margin + boxH / 2 + (posOf i).1.toFloat * rowH
  let edges := String.join (ops.toList.zipIdx.map fun (op, i) =>
    String.join (op.children.map fun ch =>
      let child := ops[ch]!
      let x1 := cx ch
      let y1 := cy ch - boxH / 2
      let x2 := cx i
      let y2 := cy i + boxH / 2
      let ran := done ch
      let est := match child.est with
        | some e => s!"<line x1=\"{fmt (x1 - 5)}\" y1=\"{fmt y1}\" x2=\"{fmt (x2 - 5)}\" y2=\"{fmt y2}\" stroke=\"#d0a020\" stroke-width=\"{fmt (strokeWidth e)}\" stroke-dasharray=\"6 4\"/>"
        | none => ""
      let act := match child.actual, ran with
        | some a, true => s!"<line x1=\"{fmt (x1 + 5)}\" y1=\"{fmt y1}\" x2=\"{fmt (x2 + 5)}\" y2=\"{fmt y2}\" stroke=\"#203040\" stroke-width=\"{fmt (strokeWidth a)}\"/>"
        | _, _ => s!"<line x1=\"{fmt (x1 + 5)}\" y1=\"{fmt y1}\" x2=\"{fmt (x2 + 5)}\" y2=\"{fmt y2}\" stroke=\"#b8c0c8\" stroke-width=\"1\" stroke-dasharray=\"2 3\"/>"
      est ++ act))
  let boxes := String.join (ops.toList.zipIdx.map fun (op, i) =>
    let x := cx i - boxW / 2
    let y := cy i - boxH / 2
    let fill := if done i then kindColour op.kind else "#d4d8dc"
    let ring := if current == some i then " stroke=\"#ff2a2a\" stroke-width=\"4\"" else " stroke=\"#ffffff\" stroke-width=\"1\""
    s!"<rect x=\"{fmt x}\" y=\"{fmt y}\" width=\"{fmt boxW}\" height=\"{fmt boxH}\" rx=\"6\" fill=\"{fill}\"{ring}/>" ++
    s!"<path d=\"{numberPath (i + 1) (cx i).round.toUInt64.toNat (cy i).round.toUInt64.toNat}\" fill=\"none\" stroke=\"{if done i then "#ffffff" else "#506070"}\" stroke-width=\"2\"/>")
  let shownW := if width > 880 then 880 else width
  let shownH := height * shownW / width
  s!"<svg width=\"{fmt shownW}\" height=\"{fmt shownH}\" viewBox=\"0 0 {fmt width} {fmt height}\">" ++
  s!"<rect x=\"0\" y=\"0\" width=\"{fmt width}\" height=\"{fmt height}\" fill=\"#ffffff\"/>" ++ edges ++ boxes ++ "</svg>"

def swatch (colour : String) : String :=
  s!"<svg width=\"14\" height=\"14\" viewBox=\"0 0 14 14\"><rect x=\"1\" y=\"1\" width=\"12\" height=\"12\" rx=\"3\" fill=\"{colour}\"/></svg>"

def legend (ops : Array Op) : String :=
  let used := kindNames.filter (fun (k, _) => ops.any (·.kind == k))
  "<table class=\"legend\"><tr>" ++ String.join (used.map fun (k, name) =>
    s!"<td>{swatch (kindColour k)}</td><td class=\"dim\">{escape name}</td>") ++ "</tr></table>" ++
  "<p class=\"dim\">Edges go from an operator up to the operator that reads its rows. The solid line is as wide as the rows that went up; " ++
  "the dashed yellow line beside it is as wide as the store planner's estimate, where it makes one. Grey boxes have not run yet.</p>"

def cell (s : String) (cls : String := "") : String :=
  if cls.isEmpty then s!"<td>{escape s}</td>" else s!"<td class=\"{cls}\">{escape s}</td>"

def opTable (ops : Array Op) (done : Nat → Bool) (current : Option Nat) : String :=
  "<table><tr><th>#</th><th>Operator</th><th>Estimate</th><th>Rows</th><th>Time</th><th>Why</th></tr>" ++
  String.join (ops.toList.zipIdx.map fun (op, i) =>
    let ran := done i
    let mark := if current == some i then "cur" else if ran then "" else "dim"
    "<tr>" ++ cell (toString (i + 1)) mark ++ cell op.label mark ++
      cell ((op.est.map toString).getD "-") ++
      cell (if ran then (op.actual.map toString).getD "-" else "not run") (if ran then "" else "dim") ++
      cell (if ran && op.ns > 0 then ms op.ns else "-") "dim" ++ cell op.why "why" ++ "</tr>") ++ "</table>"

def capTable (ops : Array Op) (caps : List CapPlan) (whole : Bool) : String :=
  let intro := "<p>The capability planner (Planner.search) plans a basic graph pattern over sources that each answer one access shape. " ++
    "Here the sources are the in-memory kind (Planner.Kinds.Memory): a scan, or a lookup with bound positions, for each predicate. " ++
    "It keeps the minimal rewritings that pass Rewriting.check, exact before approximate, then by estimated cost (estUse, fan-out 10). " ++
    (if whole then "This whole query is in the fragment that Requirement.ofQuery? accepts (a SELECT of basic graph patterns).</p>"
     else "This whole query is not in the fragment that Requirement.ofQuery? accepts (only a SELECT of basic graph patterns is), so each basic graph pattern is planned alone.</p>")
  intro ++ String.join (caps.map fun cp =>
    let name := (ops[cp.bgpOp]?.map (·.label)).getD "BGP"
    s!"<h3>Operator {cp.bgpOp + 1}: {escape name}</h3>" ++
    (if !cp.note.isEmpty then s!"<p class=\"dim\">{escape cp.note}</p>" else
    s!"<p>{cp.family} plans in the family. The first: estimated cost {cp.cost}, " ++
      (if cp.approx then "approximate" else "exact") ++ s!"; it gave {cp.rows} rows.</p>" ++
    "<table><tr><th>Access</th><th>Source (capability)</th><th>Arguments</th><th>Inputs</th><th>Est. calls</th><th>Est. tuples</th><th>Est. cost</th><th>Rows after</th></tr>" ++
    String.join (cp.steps.zipIdx.map fun (s, i) =>
      "<tr>" ++ cell (toString (i + 1)) ++ cell s.source ++ cell s.args ++ cell s.inputs ++ cell (toString s.estCalls) ++
        cell (toString s.estRows) ++ cell (toString s.estCost) ++ cell (toString s.rows) ++ "</tr>") ++ "</table>"))

def rowsTable (vars : List VarName) (rows : List Binding) (total : Nat) : String :=
  let vars := vars.filter (fun v => !v.startsWith "_:")
  if vars.isEmpty then s!"<p>{total} rows, with no variables to show.</p>" else
  s!"<p>{total} rows" ++ (if total > rows.length then s!"; the first {rows.length} are shown" else "") ++ ".</p>" ++
  "<table><tr>" ++ String.join (vars.map fun v => s!"<th>?{escape v}</th>") ++ "</tr>" ++
  String.join (rows.map fun mu => "<tr>" ++ String.join (vars.map fun v =>
    cell ((mu.lookup v).map termShort |>.getD "")) ++ "</tr>") ++ "</table>"

def style : String :=
  "body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:#f4f4ee}" ++
  "h1{margin:0 0 4px 0;font-size:22px;line-height:28px;color:#184078}" ++
  "h2{margin:16px 0 6px 0;font-size:16px;line-height:22px;color:#184078}" ++
  "h3{margin:10px 0 4px 0;font-size:14px;line-height:20px;color:#184078}" ++
  "p{margin:0 0 8px 0}table{border-collapse:collapse}svg{display:block}" ++
  "th{text-align:left;padding:3px 10px 3px 0;border-bottom:1px solid #8090a0;font-size:13px}" ++
  "td{padding:3px 10px 3px 0;border-bottom:1px solid #d0d4d8;font-size:13px;vertical-align:top}" ++
  ".q{margin:0;font-size:13px;line-height:18px;color:#102030}.qbox{background:#ffffff;padding:8px;border:1px solid #c0c8d0}" ++
  ".dim{color:#607080}.bad{color:#b02020}.cur{color:#d01818}.why{font-size:12px;color:#405060}.legend td{border-bottom:0;padding:2px 6px 2px 0}"

def queryBox (text : String) : String :=
  "<div class=\"qbox\">" ++ String.join ((text.splitOn "\n").map fun line =>
    let chars := line.toList.map (fun c => if c == '\t' then ' ' else c)
    let indent := (chars.takeWhile (· == ' ')).length
    let body := String.ofList (chars.drop indent)
    if body.isEmpty then "<p class=\"q\" style=\"height:18px\"></p>"
    else s!"<p class=\"q\" style=\"padding-left:{indent * 7}px\">{escape body}</p>") ++ "</div>"

def exampleLinks : String :=
  "<p>Examples: " ++ " · ".intercalate (examples.map fun ex =>
    s!"<a href=\"{escape (pageURL ex.query)}\">{escape ex.name}</a>") ++ "</p>"

def stepLinks (query : String) (step : Option Nat) (n : Nat) : String :=
  let link := fun (s : Option Nat) (text : String) => s!"<a href=\"{escape (pageURL query s)}\">{text}</a>"
  match step with
  | none => s!"<p>Step through the run: {link (some 1) "start at operator 1"}. Address bar: :sparql-step goes one operator on.</p>"
  | some k =>
    let prev := if k > 1 then link (some (k - 1)) "previous" else "previous"
    let next := if k < n then link (some (k + 1)) "next" else "next"
    s!"<p>Step {k} of {n}: operator {k} has just run (red ring); the operators after it have not. {prev} · {next} · {link none "run all"}</p>"

/-- The address of the next step, for `:sparql-step`. -/
def nextURL (query : String) (step : Option Nat) (n : Nat) : String :=
  match step with
  | none => pageURL query (some 1)
  | some k => if k < n then pageURL query (some (k + 1)) else pageURL query none

def defaultQuery : String := (examples.head?.map (·.query)).getD "SELECT * WHERE { ?s ?p ?o }"

def pageHead (title : String) : String :=
  s!"<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>{escape title}</title><style>{style}</style></head><body>"

def intro : String :=
  "<h1>SPARQL planner, live</h1>" ++
  "<p>Type a query in the address bar: <b>:sparql SELECT ...</b>, or follow an example. " ++
  "This engine parses it, plans it with Factoidal's planners, runs it over a small FOAF sample and draws the plan. " ++
  "Every number below comes from the engine's own functions, run now.</p>"

/-- The page for `argument`, the part of the address after `foafnaut:sparql/`. -/
def page (argument : String) (g : Graph) : String × String × String :=
  let query := (param argument "q").getD (if argument.isEmpty || argument.contains '=' then defaultQuery else decode argument)
  let step := (param argument "step").bind String.toNat?
  match explain query g with
  | .error e =>
    (pageHead "SPARQL planner" ++ intro ++ exampleLinks ++ "<h2>Query</h2>" ++ queryBox query ++
      s!"<p class=\"bad\">{escape e}</p></body></html>", "SPARQL planner", pageURL query none)
  | .ok ex =>
    let n := ex.ops.size
    let step := step.map (fun k => max 1 (min n k))
    let done := fun (i : Nat) => match step with | some k => i < k | none => true
    let current := step.map (· - 1)
    let shown := match current with
      | some i =>
        let op := ex.ops[i]!
        s!"<h2>Rows of operator {i + 1}: {escape op.label}</h2>" ++
          rowsTable (bindingVars op.sample) op.sample ((op.actual).getD op.sample.length)
      | none =>
        s!"<h2>Result: {escape ex.answer}</h2>" ++ rowsTable ex.vars (ex.rows.take 12) ex.rows.length ++
          s!"<p class=\"dim\">Query run in {ms ex.ns} (evalSelect over {g.length} triples).</p>"
    let body := intro ++ exampleLinks ++ "<h2>Query</h2>" ++ queryBox query ++
      stepLinks query step n ++
      s!"<h2>Plan: {n} operators, in the order they run</h2>" ++ planSVG ex.ops done current ++ legend ex.ops ++
      shown ++
      "<h2>Operators</h2>" ++ opTable ex.ops done current ++
      "<h2>Capability planner</h2>" ++ capTable ex.ops ex.caps ex.wholeQuery ++
      "<p class=\"dim\">Data: a synthetic FOAF sample of " ++ toString g.length ++ " triples (people, names, ages, mailboxes, foaf:knows). " ++
      "Times include the operator's inputs. Not shown: per-operator times of the modifiers, and SERVICE (no endpoint is registered).</p>"
    (pageHead "SPARQL planner" ++ body ++ "</body></html>", "SPARQL planner", nextURL query step n)

def info : String :=
  (JSON.Json.object [("engine", .string "Factoidal SPARQL"),
    ("ops", .array ([("sparqlInfo" : String), "sparqlExplain", "sparqlPage"].map .string)),
    ("datasets", .array [.string "foaf", .string "turtle"]),
    ("examples", .array (examples.map fun ex => .object [("name", .string ex.name), ("query", .string ex.query)]))]).toString

def str (j : JSON.Json) (key : String) : String :=
  match j.field? key with | some (.string s) => s | _ => ""

/-- The ops of this module, or `none` for another op. -/
def op (name : String) (request : JSON.Json) : Except String (Option String) := do
  if name == "sparqlInfo" then return some info
  if name == "sparqlExplain" then
    let g ← datasetOf request
    let run := match request.field? "run" with | some (.bool false) => false | _ => true
    let e ← explain (str request "query") g run
    return some (explainJSON e)
  if name == "sparqlPage" then
    let g ← datasetOf request
    let (source, title, next) := page (str request "argument") g
    return some (JSON.Json.object [("source", .string source), ("title", .string title), ("next", .string next)]).toString
  return none

end WebSparql
