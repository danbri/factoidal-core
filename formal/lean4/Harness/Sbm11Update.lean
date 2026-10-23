/-
Harness/Sbm11Update — `l4sbm11 update`: SPARQL 1.1 Update on an SBM11
generation (stage 5, https://github.com/danbri/factoidal/issues/791; the WHERE
clause: https://github.com/danbri/factoidal/issues/849; blank nodes:
https://github.com/danbri/factoidal/issues/850).

  l4sbm11 update GEN ('SPARQL UPDATE' | --file U.ru) [--base IRI] [--sparql12]

The request is parsed, its operations are compiled in order to log entries,
and the entries of the whole request are appended to the generation's
`deltas.dlog` as ONE batch (SPARQL 1.1 Update section 2.2: a request SHOULD be
atomic; a request that raises an error writes nothing).

Each operation reads the state the operations before it left (section 3: the
operations of a request are performed in order). That state is the generation
plus the batches of the log plus the entries of the earlier operations of this
request. The harness opens the generation only when an operation needs it:

  * INSERT DATA without a blank node, DELETE DATA, CLEAR DEFAULT, DROP DEFAULT
    and LOAD SILENT read nothing and append, as before, without opening the
    generation;
  * INSERT DATA with a blank node needs the labels the dictionary and the log
    hold (fresh labels, below), so it opens the generation but does not replay
    the log;
  * a WHERE clause, a graph that must exist (CLEAR GRAPH, DROP GRAPH, CREATE,
    COPY, MOVE, ADD), the named graphs (CLEAR NAMED, DROP ALL, ...) and the
    triples of a graph (COPY, MOVE, ADD) need the overlaid generation: the log
    is replayed into the overlay (`Session.loadOverlay`), and the entries of
    the earlier operations of the request are applied to it
    (`Session.stepEntry`, `Session.withOverlay`) before the read.

The WHERE clause is evaluated by the evaluator of `l4sbm11 query`:

  * the id path (`IdQuery.translate`, `IdQuery.whereTableM`,
    `IdQuery.decodeRowsM`) when the WHERE clause is in the id fragment and the
    operation has no `USING` clause. `WITH <g>` makes the default-graph
    patterns read `g`: the plan's default-graph patterns are given the graph
    `g`, and a `g` the dictionary does not hold makes them empty, as an empty
    default graph does in the reference semantics;
  * the reference evaluator (`evalWhere`) over the quads that the planner
    guard selects (`selectedDataset`) for every other WHERE clause, with the
    Graph Store view `whereDataset` builds for `WITH` and `USING` (section
    3.1.3).

The templates are instantiated from the solution sequence by the reference
functions (`UpdateStore.modifyDeleteQuads`, `modifyInsertQuads`,
`deleteWhereQuads`, which call `instQuads`): the deletes and the inserts of
one operation come from the same solutions, the entries are the removes and
then the adds.

Fresh blank nodes (sections 3.1.1 and 3.1.3): every blank node label of INSERT
DATA is mapped to a fresh label, one per label for the whole request, and every
blank node label of an INSERT template to a fresh label for each solution. A
fresh label is `sbm11u<n>`; `n` starts at the number of labels with that prefix
that the dictionary and the log hold, and is increased until the label is held
by neither of them nor drawn earlier in the request. The harness looks the next
64 candidates up in the dictionary and the log, and gives `UpdateStore.chooseGo`
the labels it found as `taken`; `UpdateStore.drawMany` is the same choice for
`k` labels at once. `UpdateStoreTheorems.chooseGo_spec` and `drawMany_spec`
state that a chosen label is not taken and that the chosen labels differ. The
labels are in the batch, so replay and compaction give the same blank nodes.
A candidate is looked up in the dictionary only when the dictionary holds a
label with the prefix, and in the log's labels only when the log holds one.

Graph existence. The store keeps every named graph, also one with no triple
(RDF 1.1 Concepts section 4; 2026-10-15,
https://github.com/danbri/factoidal/issues/855): the named graphs of the
overlaid generation are the base named graphs (its graph list GNL1) that the log
did not drop, and the graphs that the log created (CREATE, or an INSERT into a
graph that did not exist): `Session.hasNamedGraph`, `Session.namedGraphIds`,
`Overlay.denoteNamed`. CLEAR keeps a graph and DROP removes it. CLEAR GRAPH,
DROP GRAPH, COPY, MOVE and ADD of a graph that does not exist raise the error of
section 3.2 unless SILENT, CREATE of a graph that exists raises one, and the
graph-wide forms (CLEAR NAMED, CLEAR ALL, DROP NAMED, DROP ALL) act on every
named graph, also a graph with no triple and a graph named by a blank node
(https://github.com/danbri/factoidal/issues/856). An entry that names a graph by
a blank node makes the log version 3 (`appendPlan?`).

This is a HARNESS: it does file I/O. The semantics is
`L4Factoidal.SPARQL.UpdateStore` (pure) and the reference
`L4Factoidal.SPARQL.Update`.
-/
import Harness.Sbm11Query
import Harness.Sbm11Delta
import L4Factoidal.SPARQL.UpdateStore
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.Qlvr.Sort

namespace Harness.Sbm11Update

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.UpdateStore
open L4Factoidal.Storage
open L4Factoidal.Storage.Sbm11
open Harness.Sbm11Gen
open Harness.Sbm11Query

/-- The prefixed labels that the log's batches mention. -/
def logFreshLabels (batches : List DeltaBatch) : Std.HashSet String :=
  batches.foldl (fun acc b => b.ops.foldl (fun acc e =>
    match e with
    | .add t _ | .remove t _ =>
      (tripleBnodes t).foldl (fun a l => if l.startsWith freshPrefix then a.insert l else a) acc
    | _ => acc) acc) {}

/-- The counters of the fresh label supply are looked up in blocks of this
    size. -/
def labelBlock : Nat := 64

/-- The state of the fresh label supply of one request. The counters below
    `examined` have been looked up. `next` is the first counter that can still
    be drawn, and `next ≤ examined`. -/
structure Supply where
  next : Nat
  examined : Nat
  /-- the log holds a label with the prefix, so each candidate is looked up in
      the set of the log's labels -/
  inLog : Bool
  /-- the dictionary holds a label with the prefix, so each candidate is looked
      up in the dictionary -/
  inDict : Bool

/-- The state of one request. -/
structure Run where
  dir : String
  verify : Verify
  /-- the labels with the fresh prefix that the log mentions -/
  logLabels : Std.HashSet String
  /-- the generation opened without the log -/
  base : IO.Ref (Option Session)
  /-- the generation with the log and the earlier operations of the request -/
  overlaid : IO.Ref (Option Session)
  /-- entries of earlier operations, not yet applied to `overlaid` -/
  pending : IO.Ref (Array DeltaEntry)
  /-- the fresh label supply (`none`: not started) -/
  supply : IO.Ref (Option Supply)
  /-- the labels that are taken: held by the dictionary or the log (among the
      examined counters) or drawn in this request -/
  taken : IO.Ref (Std.HashSet String)
  /-- the environment of expressions: NOW is read once for the request -/
  env : EvalEnv
  /-- the notes for stderr: one line per operation that read the store -/
  notes : IO.Ref (Array String)

def Run.baseSession (r : Run) : IO Session := do
  match ← r.base.get with
  | some ss => return ss
  | none =>
    let ss ← openSession r.verify r.dir
    r.base.set (some ss)
    return ss

/-- The session an operation reads: the generation with the log replayed and
    the entries of the earlier operations applied. -/
def Run.sync (r : Run) : IO Session := do
  let ss ← match ← r.overlaid.get with
    | some ss => pure ss
    | none => do
      let ss ← (← r.baseSession).loadOverlay
      if ss.deltaTorn then
        throw (IO.userError "the log has an uncommitted suffix; recover it before updating")
      r.overlaid.set (some ss)
      pure ss
  let pend ← r.pending.swap #[]
  if pend.isEmpty then return ss
  let mut st := ss.ovState
  -- the dictionary ids of every term of the entries, in dictionary order (issue 858)
  let _ ← ss.prefillBaseIds pend.size fun f => do
    for e in pend do f e
  for e in pend do st ← ss.stepEntry st e
  ss.baseIds.set {}
  let ss' ← ss.withOverlay st
  r.overlaid.set (some ss')
  return ss'

/-- The number of dictionary keys that are blank nodes with the fresh prefix:
    the keys of class 1 from `1 ++ prefix` up to `1 ++ prefix ++ 0xFF`, which no
    UTF-8 label reaches. -/
def prefixHeld (ss : Session) : IO Nat := do
  let pre := bytesOfString freshPrefix
  let lo ← ss.lowerBound (ByteArray.mk (classBnode :: pre).toArray)
  let hi ← ss.lowerBound (ByteArray.mk (classBnode :: pre ++ [0xFF]).toArray)
  return hi - lo

/-- Look the labels of the next block of counters up in the log and in the
    dictionary, add the held ones to `taken`, and extend the examined range by
    the block. The dictionary is read only when it holds a label with the
    prefix, and the log's set only when the log holds one. -/
def Run.examineBlock (r : Run) (ss : Session) (sp : Supply) : IO Supply := do
  if sp.inLog || sp.inDict then
    for i in [0:labelBlock] do
      let l := freshLabel (sp.examined + i)
      let mut held := sp.inLog && r.logLabels.contains l
      if !held && sp.inDict then
        held := (← ss.idOf (.bnode l)).isSome
      if held then r.taken.modify (·.insert l)
  return { sp with examined := sp.examined + labelBlock }

/-- A fresh blank node label: see the module header. A round examines one more
    block of counters; 2^26 rounds of 64 counters are 2^32 counters, which
    bounds the search. -/
def Run.draw (r : Run) : IO BNodeId := do
  let ss ← r.baseSession
  let mut sp : Supply ← match ← r.supply.get with
    | some s => pure s
    | none => do
      let dictHeld ← prefixHeld ss
      let held := dictHeld + r.logLabels.size
      pure { next := held, examined := held, inLog := !r.logLabels.isEmpty, inDict := dictHeld != 0 }
  for _ in [0:67108864] do
    if sp.examined ≤ sp.next then
      sp ← r.examineBlock ss sp
    let t ← r.taken.get
    match chooseGo (fun l => t.contains l) (sp.examined - sp.next) sp.next with
    | some m =>
      r.supply.set (some { sp with next := m + 1 })
      let l := freshLabel m
      r.taken.modify (·.insert l)
      return l
    | none => sp := { sp with next := sp.examined }
  throw (IO.userError "no free blank node label")

/-! ## Reading the store -/

/-- Does the named graph exist in the overlaid generation, with or without a
    triple? A graph whose name has no id does not exist. -/
def graphExists (ss : Session) (g : WfIri) : IO Bool := do
  match ← ss.idOf (.iri g) with
  | none => return false
  | some x => ss.hasNamedGraph x.toNat

/-- The triples of the graph with id `gid` (0: the default graph) in the
    overlaid generation: one scan of a permutation, filtered by the graph. -/
def graphTriples (ss : Session) (gid : UInt64) : IO (List Triple) := do
  let pat : IdQuery.Pat := { s := .var "s", p := .var "p", o := .var "o", g := .const gid, named := false }
  let spec := IdQuery.mkSpec pat (IdQuery.permFor pat none) (fun _ => true)
  match ← (IdQuery.scanTableM ss.store spec).run with
  | .error e => throw (IO.userError s!"graph scan failed: {e}")
  | .ok (t, _) =>
    match ← (IdQuery.decodeRowsM ss.store t).run with
    | .error e => throw (IO.userError s!"graph decode failed: {e}")
    | .ok rows =>
      return rows.filterMap fun mu =>
        match mu.lookup "s", mu.lookup "p", mu.lookup "o" with
        | some s, some (.iri p), some o => s.toSubject?.map fun sub => ({ s := sub, p := p, o := o } : Triple)
        | _, _, _ => none

/-- The triples a graph reference names; the graph of an IRI the store has no
    id for is empty. -/
def refTriples (ss : Session) : L4Factoidal.SPARQL.GraphRef → IO (List Triple)
  | .default => graphTriples ss 0
  | .graph i => do
    match ← ss.idOf (.iri i) with
    | none => return []
    | some x => graphTriples ss x
  | _ => return []

/-- The names of the named graphs of the overlaid generation, in id order: IRIs
    and blank nodes, a graph with no triple included (`Session.namedGraphIds`). -/
def namedGraphs (ss : Session) : IO (List DeltaGraphName) := do
  let mut out : Array DeltaGraphName := #[]
  for x in ← ss.namedGraphIds do
    match ← ss.termOf x.toUInt64 with
    | .iri i => out := out.push (.iri i.val)
    | .bnode b => out := out.push (.bnode b)
    | _ => throw (IO.userError s!"the named graph id {x} is not an IRI or a blank node")
  return out.toList

/-! ## The WHERE clause -/

/-- The plan with the default-graph patterns reading the graph `w`
    (`WITH <w>`). -/
def redirectPlan (w : WfIri) (plan : IdQuery.Plan) : IdQuery.Plan :=
  let redir (p : IdQuery.PatSpec) : IdQuery.PatSpec :=
    match p.g with
    | .dflt => { p with g := .term (.iri w) }
    | _ => p
  { plan with pats := plan.pats.map redir,
              optionals := plan.optionals.map fun g => { g with pats := g.pats.map redir },
              unions := plan.unions.map fun bs => bs.map fun b => { b with pats := b.pats.map redir },
              binds := plan.binds.map fun b => { b with pats := b.pats.map redir },
              paths := plan.paths.map fun b => match b.g with
                | .dflt => { b with g := .term (.iri w) }
                | _ => b,
              semis := plan.semis.map fun b => { b with pats := b.pats.map redir } }

/-- The solutions of a WHERE clause on the state the operation reads, and the
    path that evaluated it. -/
def Run.evalWhere (r : Run) (u : Update) (opIx : Nat) (withIri : Option WfIri)
    (usingClauses : List DatasetClause) (p : QueryPattern) :
    IO (Except UpdateError SolutionSeq) := do
  let ss ← r.sync
  let env : EvalEnv := { r.env with base := u.base }
  let q : Query := .mk (.select .all) usingClauses p none [] {} none u.base
  let viaIds : IO (Option SolutionSeq) := do
    if !usingClauses.isEmpty then return none
    match IdQuery.translate q with
    | .error why =>
      r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"{why}\"")
      return none
    | .ok plan =>
      if plan.nested.isSome then
        -- issue 959: a nested WHERE clause; under WITH the reference evaluator
        if withIri.isSome then
          r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"a nested WHERE clause under WITH\"")
          return none
        match ← (IdGroup.nestedTableM (ss.storeNested 1 (some 16) 8192) plan env).run with
        | .error e =>
          if e.startsWith "refused: " then
            r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"{e.drop 9}\"")
            return none
          throw (IO.userError s!"id query failed: {e}")
        | .ok (t, st, _, _) =>
          match ← (IdQuery.decodeRowsM st t).run with
          | .error e => throw (IO.userError s!"id query failed: {e}")
          | .ok rows =>
            r.notes.modify (·.push s!"op {opIx}: where path=ids solutions={rows.length}")
            return some rows
      let plan := match withIri with | some w => redirectPlan w plan | none => plan
      let st0 := ss.storeWith 1 (some 16) 8192
      -- the VALUES blocks as id tables, the rows of the BIND blocks, and the
      -- store that decodes their query-local ids (issues 950 and 953)
      match ← (IdQuery.resolveExtrasM st0 plan env).run with
      | .error e =>
        -- issue 954: a query the id path refuses only after reading the store
        if e.startsWith "refused: " then
          r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"{e.drop 9}\"")
          return none
        throw (IO.userError s!"id query failed: {e}")
      | .ok (vtabs, btabs, st, _, _, rpaths) =>
      match ← (IdQuery.whereTableM st plan env none vtabs btabs rpaths).run with
      | .error e =>
        -- issue 956: an EXISTS or NOT EXISTS the id path refuses after the joins
        if e.startsWith "refused: " then
          r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"{e.drop 9}\"")
          return none
        throw (IO.userError s!"id query failed: {e}")
      | .ok (t, _, _) =>
        match ← (IdQuery.decodeRowsM st t).run with
        | .error e => throw (IO.userError s!"id query failed: {e}")
        | .ok rows =>
          r.notes.modify (·.push s!"op {opIx}: where path=ids solutions={rows.length}")
          return some rows
  match ← viaIds with
  | some rows => return .ok rows
  | none =>
    if !usingClauses.isEmpty then
      r.notes.modify (·.push s!"op {opIx}: where path=reference reason=\"USING / USING NAMED\"")
    let extra := match withIri with | some w => [w] | none => []
    let (ds, what) ← selectedDataset ss q extra
    let view := whereDataset ds withIri usingClauses
    match whereServiceFailure env view p with
    | some f => return .error (.serviceFailed f)
    | none =>
      let rows := L4Factoidal.SPARQL.evalWhere env view p
      r.notes.modify (·.push s!"op {opIx}: reference evaluator over {what}: solutions={rows.length}")
      return .ok rows

/-! ## Compiling an operation to entries -/

/-- The fresh label supply of the INSERT template for each solution: a table
    with one fresh label per (solution, template label). -/
def Run.templateSupply (r : Run) (it : QueryPattern) (n : Nat) : IO (Nat → String → BNodeId) := do
  let labels := (templateLabels it).reverse.eraseDups.toArray
  if labels.isEmpty || n == 0 then return fun _ l => l
  let mut table : Array BNodeId := Array.mkEmpty (n * labels.size)
  for _ in [0:n * labels.size] do
    table := table.push (← r.draw)
  return fun ix l =>
    match labels.findIdx? (· == l) with
    | some j => table[ix * labels.size + j]!
    | none => l

/-- The entries of one operation, or the error of section 3. -/
def Run.compileOp (r : Run) (u : Update) (dataTable : Std.HashMap String String) (opIx : Nat)
    (op : UpdateOp) : IO (Except UpdateError (List DeltaEntry)) := do
  match op with
  | .insertData quads =>
    let f : BNodeId → BNodeId := fun l => (dataTable.get? l).getD l
    return .ok ((insertDataQuads f quads).map addEntry)
  | .deleteData quads =>
    let collected := collectQuads none quads
    if collected.any (fun q => tripleMentionsBnode q.2) then
      throw (IO.userError "DELETE DATA must not contain blank nodes")
    return .ok (collected.map removeEntry)
  | .deleteWhere p =>
    match ← r.evalWhere u opIx none [] p with
    | .error e => return .error e
    | .ok sols => return .ok (changeEntries (deleteWhereQuads sols p) [])
  | .modify w dt it us p =>
    match ← r.evalWhere u opIx w us p with
    | .error e => return .error e
    | .ok sols =>
      let dels := modifyDeleteQuads w dt sols
      let fresh ← match it with
        | some t => r.templateSupply t sols.length
        | none => pure (fun _ l => l)
      let adds := modifyInsertQuads w it fresh sols
      return .ok (changeEntries dels adds)
  | .load silent src _ => return loadEntries silent src
  | .create silent g =>
    let ss ← r.sync
    let h ← graphExists ss g
    return createEntries silent (fun _ => h) g
  | .clear silent target =>
    match target with
    | .default => return clearEntries silent [] (fun _ => false) target
    | .graph i =>
      let ss ← r.sync
      let h ← graphExists ss i
      return clearEntries silent [] (fun _ => h) target
    | _ =>
      let ss ← r.sync
      return clearEntries silent (← namedGraphs ss) (fun _ => false) target
  | .drop silent target =>
    match target with
    | .default => return dropEntries silent [] (fun _ => false) target
    | .graph i =>
      let ss ← r.sync
      let h ← graphExists ss i
      return dropEntries silent [] (fun _ => h) target
    | _ =>
      let ss ← r.sync
      return dropEntries silent (← namedGraphs ss) (fun _ => false) target
  | .add silent src dst => graphToGraph addGraphEntries silent src dst
  | .copy silent src dst => graphToGraph copyGraphEntries silent src dst
  | .move silent src dst => graphToGraph moveGraphEntries silent src dst
where
  /-- ADD, COPY and MOVE: whether the source exists, and its triples when it
      does and the destination is a slot. -/
  graphToGraph (f : Bool → (WfIri → Bool) → List Triple → L4Factoidal.SPARQL.GraphRef →
      L4Factoidal.SPARQL.GraphRef → Except UpdateError (List DeltaEntry)) (silent : Bool)
      (src dst : L4Factoidal.SPARQL.GraphRef) :
      IO (Except UpdateError (List DeltaEntry)) := do
    if src == dst then return f silent (fun _ => false) [] src dst
    let ss ← r.sync
    let exists_ ← match src with
      | .graph i => graphExists ss i
      | _ => pure true
    let triples ← if exists_ then refTriples ss src else pure []
    return f silent (fun _ => exists_) triples src dst

/-! ## The request -/

/-- Does the dictionary admit every term of an added quad? An entry with a term
    it does not admit would make every later open of the generation fail
    (`Session.idOrNew`), so the request is refused before it is written. -/
def entryAdmitted : DeltaEntry → Bool
  | .add t _ =>
    (termKeyBytes? (normalizeTerm t.s.toTerm)).isSome && (termKeyBytes? (normalizeTerm (.iri t.p))).isSome &&
      (termKeyBytes? (normalizeTerm t.o)).isSome
  | _ => true

/-- The labels of the INSERT DATA operations of the request, each with one
    fresh label (request scope). -/
def Run.dataTable (r : Run) (ops : List UpdateOp) : IO (Std.HashMap String String) := do
  let mut tbl : Std.HashMap String String := {}
  for l in insertDataLabels ops do
    if !tbl.contains l then
      tbl := tbl.insert l (← r.draw)
  return tbl

/-- The entries of the whole request, or the error that stops it. -/
def Run.compile (r : Run) (u : Update) : IO (Except UpdateError (Array DeltaEntry)) := do
  let tbl ← r.dataTable u.ops
  let mut acc : Array DeltaEntry := #[]
  let mut ix := 0
  for op in u.ops do
    match ← r.compileOp u tbl ix op with
    | .error e => return .error e
    | .ok es =>
      acc := acc ++ es.toArray
      r.pending.modify (· ++ es.toArray)
    ix := ix + 1
  return .ok acc

/-- Append one batch for `text` to the log of the generation `dir0` names
    (through `CURRENT` when `dir0` is a collection root). The append is
    positioned at the size read (`appendSyncAtSizeRaw`, file synced); a
    concurrent writer makes it start again, with the WHERE clauses evaluated
    again, three times at most. -/
def appendUpdate (dir0 text : String) (sparql : SparqlVersion := .v11) (base : Option String := none)
    (limit : L4Factoidal.Storage.Sbm11.OverlayLimit.Limit := {}) : IO UInt32 := do
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
  let epoch := Harness.CompactedEpoch.nextWriteEpoch baseEpoch
  let path := s!"{dir}/{Harness.Sbm11Delta.logName}"
  match parseSparqlUpdate text base sparql with
  | .error e =>
    IO.eprintln s!"l4sbm11 update: parse error at {e.pos}: {e.msg}"
    return 1
  | .ok update =>
    for _ in [0:3] do
      let exists_ ← System.FilePath.pathExists path
      let bytes ← if exists_ then IO.FS.readBinFile path else pure ByteArray.empty
      let (logVersion, batches) ← if bytes.isEmpty then pure (none, []) else
        match DeltaLogBytes.parseLogCheckedBA bytes, DeltaLogBytes.logHeaderVersionAt? bytes with
        | .ok (bs, false), some v =>
          if validBatchHistory bs then pure (some v, bs)
          else throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
        | .ok (_, true), _ => throw (IO.userError s!"{path}: DLOG has an uncommitted suffix; recover it before appending")
        | .error e, _ => throw (IO.userError s!"{path}: {e}")
        | .ok _, none => throw (IO.userError s!"{path}: DLOG header is malformed or unsupported")
      -- the size limit of the log (https://github.com/danbri/factoidal/issues/851): the entries and bytes
      -- the log holds now, and the refusal text that names the repair
      let logEntries := batches.foldl (fun n b => n + b.ops.length) 0
      let fold := s!"Run 'l4sbm11 compact {dir0} OUTDIR' and 'l4sbm11 activate ROOT NAME' to fold the log into a new generation, then repeat the request."
      if limit.exceeded logEntries bytes.size then
        IO.eprintln s!"l4sbm11 update: refused: the log of {dir0} already holds {logEntries} entries in {bytes.size} bytes, over the limit of {limitText limit}. {fold}"
        return 1
      let verify ← cliDefaultVerify dir
      let clockEnv ← L4Wasm.Ops.emptyEnvNow
      let run : Run := {
        dir, verify, logLabels := logFreshLabels batches,
        base := ← IO.mkRef none, overlaid := ← IO.mkRef none, pending := ← IO.mkRef #[],
        supply := ← IO.mkRef none, taken := ← IO.mkRef {},
        env := { clockEnv with ext := L4Factoidal.Geo.extFns }, notes := ← IO.mkRef #[] }
      let t0 ← IO.monoNanosNow
      match ← run.compile update with
      | .error e =>
        for n in ← run.notes.get do IO.eprintln s!"l4sbm11 update: {n}"
        IO.eprintln s!"l4sbm11 update: refused: {e}"
        return 1
      | .ok entries =>
        let t1 ← IO.monoNanosNow
        let rssCompile ← vmHWM
        for n in ← run.notes.get do IO.eprintln s!"l4sbm11 update: {n}"
        if !entries.all entryAdmitted then
          IO.eprintln "l4sbm11 update: refused: a term of an added quad is not admitted by the SBM11 dictionary"
          return 1
        if limit.exceeded (logEntries + entries.size) bytes.size then
          IO.eprintln s!"l4sbm11 update: refused: this request adds {entries.size} entries, so the log of {dir0} would hold {logEntries + entries.size} entries, over the limit of {limitText limit}. {fold}"
          return 1
        let batch : DeltaBatch := { seq := Harness.Sbm11Delta.nextSeq batches, epoch, ops := entries.toList }
        match DeltaLogBytes.appendPlanBA? logVersion batch with
        | none =>
          IO.eprintln "l4sbm11 update: refused: the batch exceeds the DLOG wire-format limits"
          return 1
        | some plan =>
          if limit.exceeded (logEntries + entries.size) (bytes.size + plan.bytes.size) then
            IO.eprintln s!"l4sbm11 update: refused: this request adds {plan.bytes.size} bytes, so the log of {dir0} would hold {bytes.size + plan.bytes.size} bytes, over the limit of {limitText limit}. {fold}"
            return 1
          let t2 ← IO.monoNanosNow
          let rssEncode ← vmHWM
          let size := UInt64.ofNat bytes.size
          -- a log gets version 2 before the first RDF 1.2 batch and version 3
          -- before the first batch that names a graph by a blank node; a
          -- concurrent append changes the size, and the loop reads again
          let headerOk ← if plan.setVersion then
              Harness.PosixRangeIO.writeAtSizeSyncRaw path size 4
                (Harness.Sbm11Delta.asBytes (writeU32LE plan.version))
            else pure true
          if headerOk then
            if ← Harness.PosixRangeIO.appendSyncAtSizeRaw path size plan.bytes then
              let t3 ← IO.monoNanosNow
              let frameBytes := if bytes.isEmpty then plan.bytes.size - 8 else plan.bytes.size
              IO.eprintln s!"sbm11-update: entries {entries.size}; generation opened {(← run.base.get).isSome}, log replayed {(← run.overlaid.get).isSome}; compile {ms t0 t1} ms; batch encode {ms t1 t2} ms; append {ms t2 t3} ms; peak RSS after compile {rssCompile}, after encode {rssEncode}; peak RSS (VmHWM): {← vmHWM}"
              IO.println s!"l4sbm11 update: committed path={path} seq={batch.seq} epoch={batch.epoch} ops={batch.ops.length} bytes={frameBytes} log-version={plan.version}{match logVersion with | some v => if plan.setVersion then s!" (set from {v})" else "" | none => ""}"
              return 0
    IO.eprintln "l4sbm11 update: concurrent writers prevented a stable append after 3 tries"
    return 1

end Harness.Sbm11Update
