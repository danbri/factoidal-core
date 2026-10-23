/-
L4Factoidal.Storage.Sbm11.IdGroup — the recursive evaluator of group graph
patterns on the SBM11 id path
(https://github.com/danbri/factoidal/issues/959, parent
https://github.com/danbri/factoidal/issues/775).

`IdQuery.translate` accepts WHERE clauses of fixed top-level shapes
(`flattenOptional`) and runs them with its own planner (`whereTableM`,
`runPlanM`). Any other WHERE clause that `IdQuery.nestedRefusal?` accepts
gets a plan with `nested := some p`, and `evalGroupM` evaluates `p`: one arm
per constructor of the pattern the parser builds (the SPARQL 1.1 section 18.2
translation, `QueryPattern`), each arm the id form of the reference arm
(`QueryPattern.lowerWith`, `GraphPattern.evalIn`):

| pattern               | on id tables                                         |
|-----------------------|------------------------------------------------------|
| BGP                   | `IdQuery.evalBgpM` over the active graph             |
| property path         | `IdQuery.pathTableM`, candidates from a left side    |
| Join(P1, P2)          | `IdJoin.joinIds`                                     |
| LeftJoin(P1, P2, e)   | `leftJoinCondM`: the pairs of `joinPairs`, `e` on the merged rows, the left rows with no pair that passes |
| Filter(e, P)          | `filterM`: the compiled and residual conjuncts (`applyFilters`), then EXISTS and NOT EXISTS of a basic graph pattern (`semiJoinByM`) |
| Union(P1, P2)         | `IdJoin.unionIds`                                    |
| Minus(P1, P2)         | `IdQuery.semiMatches` with `needShared`              |
| Graph(<iri>, P)       | `P` with that named graph active, or no row          |
| Graph(?g, P)          | per named graph, `P` with it active and `?g` bound; a basic graph pattern alone is one scan with `?g` as the graph column |
| Extend(P, ?v, e)      | `IdQuery.extendM`                                    |
| VALUES                | `IdQuery.resolveValuesVocabM`                        |
| sub-SELECT            | `subSelectM`: a projection of variables on ids, else the reference `selectPost` on the decoded rows, the values encoded |
| {}                    | one row, no column                                   |

Every operator works on columns of `UInt64` ids. Values are decoded only
where the reference reads a term: a residual FILTER conjunct (memoised by the
tuple of ids it reads), a BIND expression (once per distinct tuple), the
substitution check of EXISTS. The joins compare ids.

The specification of this evaluator is `IdGroupTheorems.evalGroupIds`, the
same recursion over rows of ids, and `IdAllowedTheorems.evalGroupIds_allowed`
proves that it decodes to an answer the reference evaluator allows (SPARQL
1.1 fixes no order of solutions), for every pattern of the fragment, at any
depth. `GroupTableTheorems.query_where_allowed_exec` proves that this
evaluator refuses a term the query-local vocabulary cannot hold, or returns
a table that decodes, with the decoder of its final state
(`LocalVocabTheorems`), to such an answer for Join, LeftJoin, FILTER (a
condition with no EXISTS, `FilterTableTheorems`), Union, MINUS, GRAPH with an
IRI, GRAPH ?g over a pattern that is not a basic graph pattern, BIND, VALUES
and the leaves; the other arms (EXISTS in a condition, GRAPH ?g over a basic
graph pattern, sub-SELECT) are tested by `tests/sbm11/gate/ids-nest-*.rq`
and the W3C census.

Refused, with a message the harness reports (`refused: ...` at run time, a
`translate` error before): LATERAL, SERVICE, a GRAPH name that
is not an IRI or a variable, a sub-SELECT with EXISTS outside its WHERE
clause, EXISTS of a pattern that is not a basic graph
pattern or EXISTS inside an expression, a BIND whose value depends on the row
index, a property path under FROM or FROM NAMED, and GRAPH on a store that
gives no list of named graphs.

`for` loops only; structural recursion on the pattern.
-/
import L4Factoidal.Storage.Sbm11.IdQuery

namespace L4Factoidal.Storage.Sbm11.IdGroup

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr QueryPattern EvalEnv Binding PatternTerm PatternSubject PropertyPath)
open L4Factoidal.Qlvr (Table sharedCols)
open L4Factoidal.Storage.Sbm11.IdQuery

/-- The active graph: the default graph of the query's dataset, or the named
    graph of an id. -/
inductive GCtx where
  | dflt
  | named (x : UInt64)

/-- What the evaluator reads: the store, the environment of the expressions,
    the query's dataset, and the ids of its named graphs. -/
structure NCx (m : Type → Type) where
  st : Store m
  env : EvalEnv
  ds : Option DatasetSpec
  named : Array UInt64

/-- The query-local vocabulary (`IdQuery.termIdM`), the plan lines and the
    scan statistics. -/
structure NSt where
  vocab : Array Term := #[]
  localIdx : Std.HashMap Term Nat := {}
  lines : Array String := #[]
  stats : ScanStats := {}

abbrev NM (m : Type → Type) := StateT NSt (ExceptT String m)

/-- One row, no column: the solution of `{}`. -/
def unitTable : Table := { vars := #[], cols := #[], rows := 1 }

section

variable {m : Type → Type} [Monad m]

def liftE {α : Type} (x : ExceptT String m α) : NM m α := StateT.lift x

def note (line : String) : NM m Unit := modify fun s => { s with lines := s.lines.push line }

def addStats (x : ScanStats) : NM m Unit := modify fun s => { s with stats := s.stats.add x }

/-- The store that decodes the query-local ids made so far. -/
def localStore (cx : NCx m) : NM m (Store m) := do
  return cx.st.withLocal (← get).vocab

/-- A triple pattern as a `PatSpec` of the default graph. -/
def patSpecOf (tp : L4Factoidal.SPARQL.TriplePattern) : Except String PatSpec := do
  return { s := ← argOfSubject tp.s, p := ← argOfTerm tp.p, o := ← argOfObject tp.o, g := .dflt }

def patSpecsOf (tps : List L4Factoidal.SPARQL.TriplePattern) : NM m (Array PatSpec) := do
  let mut out : Array PatSpec := #[]
  for tp in tps do
    match patSpecOf tp with
    | .ok p => out := out.push p
    | .error e => throw s!"refused: {e}"
  return out

/-- A pattern over the active graph. -/
def resolveIn (cx : NCx m) (g : GCtx) (p : PatSpec) : ExceptT String m Pat := do
  match g with
  | .dflt => resolvePatIn cx.st cx.ds p
  | .named x =>
    let base ← resolvePat cx.st { p with g := .dflt }
    return { base with g := .const x }

/-- The rows of a basic graph pattern in the active graph, every variable
    kept; `{}` for no triple pattern. -/
def bgpM (cx : NCx m) (g : GCtx) (tps : List L4Factoidal.SPARQL.TriplePattern) : NM m Table := do
  if tps.isEmpty then return unitTable
  let specs ← patSpecsOf tps
  let pats ← liftE (specs.mapM (resolveIn cx g))
  let (t, _, s) ← liftE (evalBgpM cx.st pats (fun _ => true))
  addStats s
  note s!"BGP of {pats.size} triple patterns: {t.rows} rows"
  return t

/-- `?g` and the graph column: `GRAPH ?g { B }` with `B` a basic graph
    pattern is one scan of the named graphs (`Pat.named`, FROM NAMED by
    `resolvePatIn`); a variable of `B` named `?g` must equal the graph, as
    `bindIfCompatible` requires. -/
def bgpGraphVarM (cx : NCx m) (v : String) (tps : List L4Factoidal.SPARQL.TriplePattern) : NM m Table := do
  let specs ← patSpecsOf tps
  let pats ← liftE (specs.mapM fun p => resolvePatIn cx.st cx.ds { p with g := .var v })
  let (t, _, s) ← liftE (evalBgpM cx.st pats (fun _ => true))
  addStats s
  note s!"GRAPH ?{v} BGP of {pats.size} triple patterns as one scan: {t.rows} rows"
  return t

/-- A property path pattern in the active graph (`IdQuery.pathTableM`): the
    endpoints resolved (`termIdM`), the candidates of an endpoint variable
    from the columns of `left`. -/
def pathM (cx : NCx m) (g : GCtx) (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
    (left : Table) : NM m Table := do
  let gid ← match g, cx.ds with
    | .named x, _ => pure (some x)
    | .dflt, none => pure (some 0)
    | .dflt, some _ => throw "refused: a property path with FROM or FROM NAMED"
  let args ← match argOfSubject s, argOfTerm o with
    | .ok a, .ok b => pure #[a, b]
    | .error e, _ | _, .error e => throw s!"refused: {e}"
  let mut slots : Array Slot := #[]
  for a in args do
    match a with
    | .var v => slots := slots.push (.var v)
    | .term t =>
      let st0 ← get
      let (y, voc, ix) ← liftE (termIdM cx.st st0.vocab st0.localIdx t)
      modify fun s => { s with vocab := voc, localIdx := ix }
      slots := slots.push (.const y)
  let ip ← liftE (resolvePathM cx.st path)
  let rp : RPath := { s := slots[0]!, o := slots[1]!, ipath := ip, zeroLen := isZeroLen path, g := gid }
  let (t, how, ps) ← liftE (pathTableM (← localStore cx) rp left)
  addStats ps
  note s!"property path: {how}"
  return t

/-- Whether column `v` of `t` holds an id in every row. -/
def colBound (t : Table) (v : String) : Bool :=
  match t.idx v with
  | none => false
  | some c => Id.run do
    for i in [0:t.rows] do
      if t.at c i == OptJoin.unbound then return false
    return true

/-- The conjuncts of a FILTER condition `c` over `t`, classified: the
    EXISTS-free ones as `applyFilters` runs them (compiled on ids,
    `compileFilter`, when every variable they read is bound in every row and
    they are `backendLocal`; else the reference on the decoded terms,
    `residualKind`), `EXISTS { B }` and `NOT EXISTS { B }` as semi-joins, and
    whether some conjunct is `NOT EXISTS {}` (no row passes). -/
def filterKindsM (cx : NCx m) (t : Table) (c : Expr) : NM m (Array FKind × Array SemiBlock × Bool) := do
  let mut fs : Array FKind := #[]
  let mut semis : Array SemiBlock := #[]
  let mut none_ := false
  for cj in conjuncts c do
    match cj with
    | .existsPat (.bgp b) => semis := semis.push { pats := ← patSpecsOf b, kind := .semi }
    | .notExistsPat (.bgp b) => semis := semis.push { pats := ← patSpecsOf b, kind := .anti }
    | .existsPat .empty => pure ()
    | .notExistsPat .empty => none_ := true
    | _ =>
      let some vs := residualVars cj | throw "refused: an EXISTS or NOT EXISTS inside an expression"
      unless cj.existsFree do throw "refused: an EXISTS or NOT EXISTS inside an expression"
      if cj.backendLocal && (exprVars cj).isSome && vs.all (colBound t) then
        let k ← liftE (compileFilter cx.st cj)
        match k with
        | .idEq _ none =>
          -- the constant has no stored id; a query-local id may name it
          if (← get).vocab.isEmpty then fs := fs.push k else fs := fs.push (residualKind cx.env cj)
        | _ => fs := fs.push k
      else fs := fs.push (residualKind cx.env cj)
  return (fs, semis, none_)

/-- Filter(e, Ω) on an id table: the EXISTS-free conjuncts first
    (`filterKindsM`, `applyFilters`), then `EXISTS { B }` and
    `NOT EXISTS { B }` with `B` in the active graph (`semiJoinByM`).
    `ebvOrFalse` of a conjunction is the conjunction of its conjuncts'
    (`ebvOrFalse_evalIn_and`). -/
def filterM (cx : NCx m) (g : GCtx) (t : Table) (c : Expr) : NM m Table := do
  let (fs, semis, none_) ← filterKindsM cx t c
  if none_ then return t.select fun _ => false
  let lst ← localStore cx
  let (t1, _) ← liftE (applyFilters lst fs (fs.map fun _ => {}) t)
  let mut t2 := t1
  for b in semis do
    let (t', _, s) ← liftE (semiJoinByM lst (resolveIn cx g) t2 b)
    addStats s
    t2 := t'
  note s!"FILTER: {fs.size} conjuncts on ids or decoded terms, {semis.size} EXISTS: {t.rows} rows to {t2.rows}"
  return t2

/-- The name of the column of pair indices `leftJoinCondM` adds (no SPARQL
    variable has it). -/
def pairCol : String := "#pair"

/-- The rows of `LeftJoin` as indices: per left row `i < nl` in order, its
    pairs `k` (`li[k] = i`; `li` is non-decreasing) that passed the
    condition (`alive`), else `(none, i)`, the left row alone. -/
def ljSource (nl : Nat) (li : Array Nat) (alive : Array Bool) : Array (Option Nat × Nat) := Id.run do
  let mut src : Array (Option Nat × Nat) := Array.mkEmpty (nl + li.size)
  let mut k := 0
  for i in [0:nl] do
    let mut any := false
    for _ in [0:li.size] do
      if k < li.size && li[k]! == i then
        if alive[k]! then
          src := src.push (some k, i)
          any := true
        k := k + 1
      else break
    if !any then src := src.push (none, i)
  return src

/-- The columns of the `LeftJoin` table: per column of `merged`, for each
    entry of `src` the merged row of a pair, or the left row (`unbound` in
    a column the left table does not have). -/
def ljColumns (merged l : Table) (src : Array (Option Nat × Nat)) : Array ByteArray := Id.run do
  let mut cols : Array ByteArray := Array.mkEmpty merged.vars.size
  for c in [0:merged.vars.size] do
    let mut out := ByteArray.emptyWithCapacity (8 * src.size)
    for (pk, i) in src do
      let x := match pk with
        | some k => merged.at c k
        | none => if c < l.vars.size then l.at c i else OptJoin.unbound
      out := L4Factoidal.Qlvr.Side.put64 out x
    cols := cols.push out
  return cols

/-- `LeftJoin(Ω1, Ω2, e)` on id tables (SPARQL 1.1 section 18.5): the pairs
    of compatible rows (`IdJoin.joinPairs`; an `unbound` id is compatible
    with any), merged (`IdJoin.pairsTable`); `e` on the merged rows
    (`filterKeep` of the conjuncts as a mask, or `filterM` on the merged
    rows tagged with their pair index when `e` has an EXISTS conjunct; so `e`
    reads the left and the right variables); then per left row in order its
    merged rows that passed, or the left row itself when none did
    (`IdGroupTheorems.idLeftJoinC`). -/
def leftJoinCondM (cx : NCx m) (g : GCtx) (l r : Table) (c : Expr) : NM m Table := do
  let shared := sharedCols l r
  let (li, ri) := IdJoin.joinPairs l r shared
  let merged := IdJoin.pairsTable l r shared li ri
  let trivial := match c with
    | .boolLit true => true
    | _ => false
  let alive : Array Bool ← if trivial then pure (Array.replicate li.size true) else do
    let (fs, semis, none_) ← filterKindsM cx merged c
    if semis.isEmpty && !none_ then
      -- no EXISTS: the conjuncts on the merged rows, as a mask
      -- (`filterKeep`, one entry per pair)
      let lst ← localStore cx
      let (keep, _) ← liftE (filterKeep lst fs (fs.map fun _ => {}) merged)
      note s!"OPTIONAL FILTER: {fs.size} conjuncts on ids or decoded terms over {li.size} pairs"
      pure keep
    else
      -- EXISTS in the condition: the FILTER on the merged rows tagged with
      -- their pair index
      let mut idxCol := ByteArray.emptyWithCapacity (8 * li.size)
      for k in [0:li.size] do
        idxCol := L4Factoidal.Qlvr.Side.put64 idxCol k.toUInt64
      let tagged : Table := { merged with vars := merged.vars.push pairCol, cols := merged.cols.push idxCol }
      let kept ← filterM cx g tagged c
      let mut a := Array.replicate li.size false
      match kept.idx pairCol with
      | some pc =>
        for i in [0:kept.rows] do
          a := a.set! (kept.at pc i).toNat true
      | none => pure ()
      pure a
  let src := ljSource l.rows li alive
  let cols := ljColumns merged l src
  note s!"OPTIONAL: {l.rows} left rows, {r.rows} right rows, {li.size} compatible pairs; {src.size} rows"
  return { vars := merged.vars, cols, rows := src.size }

/-- Bind `?v` to the graph id `x` in each row (`bindIfCompatible`): a row
    that has `?v` keeps it when it is `x` or unbound (then `x`); a table
    without the column gets it. -/
def bindGraph (t : Table) (v : String) (x : UInt64) : Table :=
  match t.idx v with
  | none =>
    let col := Id.run do
      let mut b := ByteArray.emptyWithCapacity (8 * t.rows)
      for _ in [0:t.rows] do
        b := L4Factoidal.Qlvr.Side.put64 b x
      return b
    { vars := t.vars.push v, cols := t.cols.push col, rows := t.rows }
  | some c =>
    let t' := t.select fun i => t.at c i == x || t.at c i == OptJoin.unbound
    let col := Id.run do
      let mut b := ByteArray.emptyWithCapacity (8 * t'.rows)
      for _ in [0:t'.rows] do
        b := L4Factoidal.Qlvr.Side.put64 b x
      return b
    { t' with cols := t'.cols.set! c col }

/-- The id of a named graph of the dataset given by an IRI, if it is one. -/
def namedIdOf (cx : NCx m) (t : Term) : NM m (Option UInt64) := do
  match ← liftE (cx.st.idOf t) with
  | some x => return if cx.named.contains x then some x else none
  | none => return none

/-- Extend(Ω, ?v, e) (`IdQuery.extendM`), the query-local vocabulary
    threaded. -/
def extendNM (cx : NCx m) (t : Table) (e : Expr) (v : String) : NM m Table := do
  let s ← get
  let (t', voc, ix) ← liftE (extendM cx.st cx.env t e v s.vocab s.localIdx)
  set { s with vocab := voc, localIdx := ix }
  note s!"BIND ?{v}: {t'.rows} rows"
  return t'

/-- A VALUES block as an id table (`resolveValuesVocabM`). -/
def valuesNM (cx : NCx m) (vars : List String) (rows : List (List (Option Term))) : NM m Table := do
  let s ← get
  let b : ValuesBlock := { vars := vars.toArray, rows := (rows.map List.toArray).toArray }
  let (ts, voc, ix) ← liftE (resolveValuesVocabM cx.st #[b] s.vocab s.localIdx)
  set { s with vocab := voc, localIdx := ix }
  return ts[0]!

/-- The projection of a sub-SELECT that is a list of variables and nothing
    else (no GROUP BY, HAVING, aggregate, expression, ORDER BY, OFFSET,
    LIMIT, REDUCED or trailing VALUES): its variables and DISTINCT. -/
def plainProjection? (sq : L4Factoidal.SPARQL.Query) : Option (Array String × Bool) :=
  match sq with
  | .mk (.select (.vars items)) _ _ none [] md none _ =>
    if md.orderBy.isNone && md.offset.isNone && md.limit.isNone && !md.reduced then
      items.foldl (fun acc it => match acc, it with
        | some vs, .var v => some (vs.push v)
        | _, _ => none) (some #[]) |>.map fun vs => (vs, md.distinct)
    else none
  | _ => none

/-- A sub-SELECT (SPARQL 1.1 section 18.2.4.1 and 18.2.5) over the id table
    `t` of its WHERE clause. A projection of variables (`plainProjection?`)
    stays on ids: the columns of the projected variables (`IdJoin.keepVars`),
    then `IdJoin.distinctRows` for DISTINCT (equal ids are equal terms). Any
    other sub-SELECT decodes the rows (`decodeRowsM`), runs the reference
    post-processing (`selectPost`: grouping, aggregates, HAVING, expressions,
    ORDER BY, projection, DISTINCT, slice) and encodes the values of the
    projected variables (`termIdM`; a new term gets a query-local id), as
    `IdGroupTheorems.evalGroupIds` does. `nestedRefusal?` admits only a
    sub-SELECT with no EXISTS outside its WHERE clause, so the post-processing
    reads no active graph. -/
def subSelectM (cx : NCx m) (sq : L4Factoidal.SPARQL.Query) (t : Table) : NM m Table := do
  match plainProjection? sq with
  | some (vs, distinct) =>
    let p := IdJoin.keepVars t vs.contains
    let p := if distinct then IdJoin.distinctRows p else p
    note s!"sub-SELECT on ids: {vs.size} variables{if distinct then ", DISTINCT" else ""}: {t.rows} rows to {p.rows}"
    return p
  | none =>
    let rows ← liftE (decodeRowsM (← localStore cx) t)
    let out := L4Factoidal.SPARQL.selectPost cx.env Graph.empty sq rows
    let vars := (L4Factoidal.SPARQL.Query.projectedVars sq).toArray
    let mut cols : Array ByteArray := vars.map fun _ => ByteArray.emptyWithCapacity (8 * out.length)
    for mu in out do
      for k in [0:vars.size] do
        let mut x := OptJoin.unbound
        match mu.lookup vars[k]! with
        | some term =>
          let s ← get
          let (y, voc, ix) ← liftE (termIdM cx.st s.vocab s.localIdx term)
          set { s with vocab := voc, localIdx := ix }
          x := y
        | none => pure ()
        cols := cols.modify k (L4Factoidal.Qlvr.Side.put64 · x)
    note s!"sub-SELECT: {t.rows} rows decoded, reference selectPost: {out.length} rows encoded"
    return { vars, cols, rows := out.length }

/-- The evaluator (module header): the rows of `p` with `g` the active
    graph, every variable of `p` that a row binds a column (`unbound` where a
    row does not bind it). -/
def evalGroupM (cx : NCx m) : QueryPattern → GCtx → NM m Table
  | .bgp tps, g => bgpM cx g tps
  | .empty, _ => pure unitTable
  | .join l (.propertyPath s path o), g => do
    let tl ← evalGroupM cx l g
    let tp ← pathM cx g s path o tl
    return IdJoin.joinIds tl tp
  | .join l r, g => do
    let tl ← evalGroupM cx l g
    let tr ← evalGroupM cx r g
    let t := IdJoin.joinIds tl tr
    note s!"join: {tl.rows} and {tr.rows} rows: {t.rows} rows"
    return t
  | .leftJoin l r c, g => do
    let tl ← evalGroupM cx l g
    let tr ← evalGroupM cx r g
    leftJoinCondM cx g tl tr c
  | .filter c q, g => do
    let t ← evalGroupM cx q g
    filterM cx g t c
  | .union l r, g => do
    let tl ← evalGroupM cx l g
    let tr ← evalGroupM cx r g
    return IdJoin.unionIds #[tl, tr]
  | .minus l r, g => do
    let tl ← evalGroupM cx l g
    let tr ← evalGroupM cx r g
    let hits := semiMatches tl tr true
    let t := tl.select fun i => !hits[i]!
    note s!"MINUS: {tl.rows} rows, right {tr.rows} rows: {t.rows} rows"
    return t
  | .graph (.iri i) q, _ => do
    if cx.st.namedGraphs.isNone then throw "refused: GRAPH on a store with no list of named graphs"
    match ← namedIdOf cx (.iri i) with
    | some x => evalGroupM cx q (.named x)
    | none =>
      note s!"GRAPH <{i.val}>: not a named graph of the dataset"
      return Table.empty #[]
  | .graph (.var v) q, _ => do
    match q with
    | .bgp tps =>
      if !tps.isEmpty then return ← bgpGraphVarM cx v tps
    | _ => pure ()
    if cx.st.namedGraphs.isNone then throw "refused: GRAPH on a store with no list of named graphs"
    let mut parts : Array Table := #[]
    for x in cx.named do
      let t ← evalGroupM cx q (.named x)
      parts := parts.push (bindGraph t v x)
    let u := IdJoin.unionIds parts
    note s!"GRAPH ?{v}: {cx.named.size} named graphs, {u.rows} rows"
    return u
  | .graph _ _, _ => throw "refused: a GRAPH name that is not an IRI or a variable"
  | .bind e v q, g => do
    let t ← evalGroupM cx q g
    extendNM cx t e v
  | .values vars rows, _ => valuesNM cx vars rows
  | .propertyPath s path o, g => pathM cx g s path o unitTable
  | .subSelect (.mk form dcs inner gb hv md pv bs), g => do
    let t ← evalGroupM cx inner g
    subSelectM cx (.mk form dcs inner gb hv md pv bs) t
  | .lateral _ _, _ => throw "refused: LATERAL"
  | .service _ _ _, _ => throw "refused: SERVICE"
  | .serviceVar _ _ _, _ => throw "refused: SERVICE"

/-- The named graphs `GRAPH` reads: the store's (`Store.namedGraphs`), those
    the FROM NAMED IRIs name under a dataset clause. -/
def namedOf (st : Store m) (ds : Option DatasetSpec) : ExceptT String m (Array UInt64) := do
  let all ← match st.namedGraphs with
    | some f => f
    | none => pure #[]
  match ds with
  | none => return all
  | some d =>
    let ns ← idsOfM st d.named
    return ns.filter all.contains

/-- The WHERE solutions of a nested plan as an id table, and the store that
    decodes its query-local ids. -/
def nestedTableM (st : Store m) (plan : Plan) (env : EvalEnv) :
    ExceptT String m (Table × Store m × Array String × ScanStats) := do
  let some p := plan.nested | throw "not a nested plan"
  let cx : NCx m := { st, env, ds := plan.dataset, named := ← namedOf st plan.dataset }
  let (t, s) ← (evalGroupM cx p .dflt).run {}
  return (t, st.withLocal s.vocab, s.lines.push s!"nested WHERE (issue 959): {t.rows} solutions", s.stats)

/-- Run a nested plan: `nestedTableM`, the first rows the answer reads, then
    the reference post-processing (`postAnswerM`). -/
def runNestedM (st : Store m) (plan : Plan) (ps : PostSpec) (env : EvalEnv) :
    ExceptT String m (PostAnswer × RunStats) := do
  let (t, st', lines, s) ← nestedTableM st plan env
  let t := match ps.firstRows with
    | some n => t.slice 0 n
    | none => t
  postAnswerM st' ps env t lines s

end

end L4Factoidal.Storage.Sbm11.IdGroup
