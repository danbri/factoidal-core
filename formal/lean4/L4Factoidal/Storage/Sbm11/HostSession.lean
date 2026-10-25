/-
L4Factoidal.Storage.Sbm11.HostSession — SPARQL over an SBM11 generation whose
bytes a host supplies (stage 1 of https://github.com/danbri/factoidal/issues/1007;
KR1 of the OKR https://github.com/danbri/factoidal/issues/1009).

The query engine is the one `l4sbm11 query` runs: `IdQuery.translate`, then
the id path (`IdQuery.runPlanM`, `runPostM`, `IdGroup.runNestedM`) over an
`IdQuery.Store IO`, or the reference evaluator over the quads the planner
guard selects. This module gives that engine a store whose every byte comes
from one host function:

  Host.readAt file offset length : IO ByteArray   -- exactly `length` bytes
  Host.size file : IO (Option Nat)                -- `none`: no such file

`file` is the name of a file of the generation directory, as the manifest
names it (and `manifest.sbm11`, `deltas.dlog`). The host decides where the
generation is (a directory for Node, an OPFS directory, an HTTP base); it
never decides a format, a name or a digest (iron rule 7). The module has no
`IO.FS`, no thread and no extern, so the wasm build compiles it, and a test
can give it a host over bytes in memory.

What differs from `Harness/Sbm11Query.lean` (the native session):

* one thread: no worker pool, no task views, no locks;
* reads are checked as `Verify.none` is on the native path: every artifact's
  size against the manifest at open, every read against the manifest's
  length. The Merkle check (`Verify.merkle`) is not here yet;
* a generation with a delta log (`deltas.dlog` with bytes) is refused at
  open: the replay is stage 3 of issue 1007.

The same library functions decode every byte (`Dict.pageM`, `Dict.lookupM`,
`DictRange.lowerBoundM`, `PrmRange.openM`, `PrmRange.rangeM` over
`PrmRange.bytesReader`, `GraphList.decodeAt`), and the caches are
`MemoCache.insertBounded` and `insertEvict`, whose coherence
`MemoCache.lookup_eq` proves. `FileGenTheorems.store_written` holds for this
store under the same named assumption as for the native one: `ReadsWritten`,
each positioned read returns the bytes the packer wrote.

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.IdGroup
import L4Factoidal.Storage.Sbm11.QueryEnv
import L4Factoidal.Storage.Sbm11.TermKeyFast
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.DictRange
import L4Factoidal.Storage.Sbm11.MemoCache
import L4Factoidal.Storage.Sbm11.GraphList
import L4Factoidal.Storage.Sbm11.Manifest
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.SelectedDataset
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.Geo.Functions
import L4Factoidal.Dataflow.Store
import L4Factoidal.RDF.Sink
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.HostSession

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Manifest

/-- The positioned reads of one generation, supplied by the host. -/
structure Host where
  /-- Bytes `[off, off + len)` of a file of the generation; exactly `len`
      bytes, else an error. -/
  readAt : String → Nat → Nat → IO ByteArray
  /-- The size of a file of the generation; `none` when it does not exist. -/
  size : String → IO (Option Nat)

/-- The file name of the manifest in a generation directory. -/
def manifestName : String := "manifest.sbm11"

/-- The file name of the delta log in a generation directory. -/
def logName : String := "deltas.dlog"

/-- The permutation names in id order (`Sbm11Gen.permNamesArr`). -/
def permNames : Array String := #["PSO", "POS", "SPO", "OSP"]

/-- A permutation opened by the session: its two files, their lengths (from
    the manifest), the PRM1 block count, and the answers of `rangeM` asked
    so far (at most 256 keys). -/
structure Perm where
  prmFile : String
  prmBytes : Nat
  prbFile : String
  prbBytes : Nat
  count : Nat
  ranges : IO.Ref (Std.HashMap (Array UInt64) (Array BlockMeta))

/-- An open generation. -/
structure Session where
  host : Host
  manifest : Manifest
  gdxFile : String
  gdxBytes : Nat
  gdvFile : String
  gdvBytes : Nat
  dictHdr : Dict.GdxHeader
  perms : IO.Ref (Array (Option Perm))
  /-- decoded dictionary pages, packed (`Harness.Sbm11Query.Session.loadPage`) -/
  pages : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))
  idMemo : IO.Ref (Std.HashMap Term UInt64)
  baseNamedRef : IO.Ref (Option (Array Nat))
  /-- bytes the host returned since the session opened -/
  bytesRead : IO.Ref Nat
  /-- host reads since the session opened -/
  reads : IO.Ref Nat
  /-- the most decoded dictionary pages kept (about 4.5 KB each): the native
      default `SBM11_PAGES` (`Harness.Sbm11Query.defaultPages`). Olympics q19
      and q21 need between 4,096 and 8,192 pages; at 4,096 they ran 2.2 to 2.6
      times as long as native `l4sbm11 query`. -/
  pageLimit : Nat := 8192

/-- A session for one query, with references of its own that hold the
    caches of `ss` (`keep` writes them back). A session in a global handle
    table (`Wasm/Ops/Sbm11.lean`) is reachable from a global, so the Lean
    runtime marks it and everything stored in its references as shared
    between threads (`lean_mark_mt`), and a shared object is never updated in
    place: every insert into the page cache walked the whole cache to mark it
    and copied its bucket array. Olympics q19, callgrind: 25 percent of the
    instructions in `lean_mark_mt`, 22 percent in `lean_del_core_other` and
    `lean_copy_expand_array`, and twice the time of native `l4sbm11 query`.
    On the copies the first insert copies a shared map once; the rest are in
    place. -/
def Session.localize (ss : Session) : IO Session := do
  let perms ← (← ss.perms.get).mapM fun o => do
    match o with
    | some p => return some { p with ranges := ← IO.mkRef (← p.ranges.get) }
    | none => return none
  return { ss with perms := ← IO.mkRef perms, pages := ← IO.mkRef (← ss.pages.get),
                   idMemo := ← IO.mkRef (← ss.idMemo.get),
                   baseNamedRef := ← IO.mkRef (← ss.baseNamedRef.get),
                   bytesRead := ← IO.mkRef (← ss.bytesRead.get), reads := ← IO.mkRef (← ss.reads.get) }

/-- Write the caches and counters of a query's session (`localize`) back to
    `ss`, for the next query. -/
def Session.keep (ss q : Session) : IO Unit := do
  ss.perms.set (← q.perms.get)
  ss.pages.set (← q.pages.get)
  ss.idMemo.set (← q.idMemo.get)
  ss.baseNamedRef.set (← q.baseNamedRef.get)
  ss.bytesRead.set (← q.bytesRead.get)
  ss.reads.set (← q.reads.get)

def ioErr {α : Type} (msg : String) : IO α := throw (IO.userError msg)

def okOr {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => ioErr s!"{what}: {e}"

def artifactNamed (m : Manifest) (role : String) : IO Artifact :=
  match artifactOf? m role with
  | some a => pure a
  | none => ioErr s!"the manifest has no artifact {role}"

/-- A checked read: inside the file's manifest length, exactly `len` bytes. -/
def Session.fetch (ss : Session) (file : String) (total off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  if off + len > total then
    ioErr s!"{file}: read of {len} bytes at {off} past the manifest's length {total}"
  let b ← try ss.host.readAt file off len
    catch e => ioErr s!"{file}: read of {len} bytes at {off}: {e}"
  if b.size != len then ioErr s!"{file}: the host returned {b.size} bytes for a read of {len}"
  ss.bytesRead.modify (· + len)
  ss.reads.modify (· + 1)
  return b

def Session.gdxFetch (ss : Session) (off len : Nat) : IO ByteArray :=
  ss.fetch ss.gdxFile ss.gdxBytes off len

def Session.gdvFetch (ss : Session) (off len : Nat) : IO ByteArray :=
  ss.fetch ss.gdvFile ss.gdvBytes off len

/-- The file name of a collection root's pointer to its active generation
    (`Harness.GenerationPointer.currentName`). -/
def currentName : String := "CURRENT"

/-- A generation name that `CURRENT` may hold
    (`Harness.GenerationPointer.safeGenerationName`). -/
def safeGenerationName (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." && !(name.contains '/') && !(name.contains '\\')

/-- The host of the subdirectory `name`. -/
def Host.under (h : Host) (name : String) : Host :=
  { readAt := fun f off len => h.readAt s!"{name}/{f}" off len
    size := fun f => h.size s!"{name}/{f}" }

/-- The host of the generation that `h` names: the generation `CURRENT`
    names when the source is a collection root with that pointer, else the
    source itself (the rule of `Harness.GenerationPointer.resolveStoreDirectory`).
    The second component is the generation name, or `""`. -/
def resolveHost (h : Host) : IO (Host × String) := do
  match ← h.size currentName with
  | none => return (h, "")
  | some n =>
    let b ← h.readAt currentName 0 n
    let some name := String.fromUTF8? b | ioErr "CURRENT is not valid UTF-8"
    unless safeGenerationName name do ioErr "CURRENT does not name a safe generation directory"
    let g := h.under name
    if (← g.size manifestName).isNone then ioErr s!"CURRENT names a generation with no {manifestName}: {name}"
    return (g, name)

/-- Open a generation: read and decode its manifest, check that every
    artifact has the manifest's size, refuse a delta log, read the GDX1
    header. The host names a generation directory (`resolveHost` first for
    a collection root). -/
def openSession (host : Host) : IO Session := do
  let some msize ← host.size manifestName
    | ioErr s!"{manifestName}: not found; the source is not an SBM11 generation directory"
  let mbytes ← host.readAt manifestName 0 msize
  let some m := decodeManifest mbytes.data.toList
    | ioErr s!"{manifestName}: does not decode as an SBM11 manifest"
  for a in m.artifacts do
    match ← host.size a.file with
    | some n => if n != a.bytes then ioErr s!"{a.file}: {n} bytes, the manifest says {a.bytes}"
    | none => ioErr s!"{a.file}: named by the manifest and not found"
  if let some n ← host.size logName then
    if n > 0 then
      ioErr s!"{logName}: this generation has a delta log ({n} bytes); this session does not replay a log yet (stage 3 of https://github.com/danbri/factoidal/issues/1007)"
  let gdvA ← artifactNamed m "GDV1"
  let gdxA ← artifactNamed m "GDX1"
  let ss0 : Session :=
    { host, manifest := m, gdxFile := gdxA.file, gdxBytes := gdxA.bytes, gdvFile := gdvA.file,
      gdvBytes := gdvA.bytes, dictHdr := { termCount := 0, pageCount := 0 },
      perms := ← IO.mkRef #[none, none, none, none], pages := ← IO.mkRef {}, idMemo := ← IO.mkRef {},
      baseNamedRef := ← IO.mkRef none, bytesRead := ← IO.mkRef msize, reads := ← IO.mkRef 1 }
  let hdr ← okOr "GDX1" (Dict.parseGdxHeader (← ss0.gdxFetch 0 Dict.gdxHeaderBytes))
  return { ss0 with dictHdr := hdr }

def Session.prmReadAt (ss : Session) (file : String) (total : Nat) (off len : Nat) :
    ExceptT String IO ByteArray :=
  ExceptT.lift (ss.fetch file total off len)

def Session.perm (ss : Session) (p : Nat) : IO Perm := do
  match (← ss.perms.get)[p]? with
  | some (some lp) => return lp
  | some none =>
    let nm := permNames[p]!
    let prmA ← artifactNamed ss.manifest s!"PRM1-{nm}"
    let prbA ← artifactNamed ss.manifest s!"PRB1-{nm}"
    let count ← match ← (PrmRange.openM (ss.prmReadAt prmA.file prmA.bytes) prmA.bytes p).run with
      | .ok n => pure n
      | .error e => ioErr s!"{prmA.file}: {e}"
    let lp : Perm := { prmFile := prmA.file, prmBytes := prmA.bytes, prbFile := prbA.file,
                       prbBytes := prbA.bytes, count, ranges := ← IO.mkRef {} }
    ss.perms.modify (·.set! p (some lp))
    return lp
  | none => ioErr s!"no permutation {p}"

def Session.loadPage (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) := do
  let ks ← okOr s!"GDV1 page {pg}" (← (Dict.pageM ss.gdxFetch ss.gdvFetch pg).run)
  let total := ks.foldl (fun a k => a + k.size) 0
  let mut packed := ByteArray.emptyWithCapacity total
  let mut offs : Array Nat := Array.mkEmpty (ks.size + 1)
  for k in ks do
    offs := offs.push packed.size
    packed := packed ++ k
  offs := offs.push packed.size
  return (packed, offs)

def Session.pageKeys (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) := do
  match (← ss.pages.get).get? pg with
  | some ks => return ks
  | none =>
    let ks ← ss.loadPage pg
    ss.pages.modify fun m => MemoCache.insertEvict m ss.pageLimit pg ks
    return ks

def Session.keySlice (ss : Session) (x : UInt64) : IO (ByteArray × Nat × Nat) := do
  let id := x.toNat
  let tag := id / two60
  unless isDictTag tag do ioErr s!"id {id}: not a dictionary id"
  let rank := id % two60
  if rank ≥ ss.dictHdr.termCount then ioErr s!"id {id}: rank not below the term count"
  let (packed, offs) ← ss.pageKeys (rank / Dict.pageTerms)
  let j := rank % Dict.pageTerms
  if j + 1 < offs.size then return (packed, offs[j]!, offs[j + 1]!)
  ioErr s!"id {id}: no key"

def Session.keyOf (ss : Session) (x : UInt64) : IO ByteArray := do
  let (packed, a, e) ← ss.keySlice x
  return packed.extract a e

def Session.termOf (ss : Session) (x : UInt64) : IO Term := do
  let id := x.toNat
  let tag := id / two60
  if tag == tagInt || tag == tagBool then
    match ofInlineCode? id with
    | some t => return t
    | none => ioErr s!"inline id {id} does not decode"
  let (packed, a, e) ← ss.keySlice x
  if classTagSlice packed a e != tag then ioErr s!"id {id}: tag differs from the key's class"
  match decodeKeySlice? packed a e with
  | some t => return t
  | none => ioErr s!"id {id}: key does not decode"

def idMemoLimit : Nat := 65536

def Session.idOf (ss : Session) (t : Term) : IO (Option UInt64) := do
  let t := normalizeTerm t
  match inlineCode? t with
  | some c => return some c.toUInt64
  | none =>
    if let some x := MemoCache.find? (← ss.idMemo.get) t then return some x
    match termKeyBytes? t with
    | none => return none
    | some k =>
      let (r, _) ← okOr "lookup" (← (Dict.lookupM ss.gdxFetch ss.gdvFetch ss.dictHdr k).run)
      match r with
      | some r =>
        let x := (dictCode k.data.toList r).toUInt64
        ss.idMemo.modify fun m => MemoCache.insertBounded idMemoLimit m t x
        return some x
      | none => return none

def Session.lowerBound (ss : Session) (k : ByteArray) : IO Nat := do
  okOr "lower bound" (← (DictRange.lowerBoundM ss.gdxFetch ss.gdvFetch ss.dictHdr k).run)

def Session.rangeFor (ss : Session) (p : Nat) (key : Array UInt64) : IO (Array BlockMeta) := do
  let lp ← ss.perm p
  if let some r := MemoCache.find? (← lp.ranges.get) key then return r
  let read := ss.prmReadAt lp.prmFile lp.prmBytes
  let r ← match ← (PrmRange.rangeM (PrmRange.bytesReader read lp.count) key).run with
    | .ok r => pure r
    | .error e => ioErr s!"{lp.prmFile}: {e}"
  lp.ranges.modify fun m => MemoCache.insertBounded 256 m key r
  return r

def Session.prb (ss : Session) (p off len : Nat) : IO ByteArray := do
  let lp ← ss.perm p
  ss.fetch lp.prbFile lp.prbBytes off len

/-- An IO action in the store's monad. Its IO error is not caught here: it
    leaves `runPlanM` as an IO error, which the caller reports (as
    `Harness.Sbm11Query.liftIO`; a `try` per call cost time on every key). -/
def liftIO {α : Type} (x : IO α) : ExceptT String IO α := ExceptT.lift x

/-- The session as the id engine's store (`IdQuery.Store IO`), single thread. -/
def Session.store (ss : Session) : IdQuery.Store IO :=
  { blockCount := fun p => liftIO do pure (← ss.perm p).count
    blocksForRange := fun p key => liftIO (ss.rangeFor p key)
    prb := fun p off len => liftIO (ss.prb p off len)
    idOf := fun t => liftIO (ss.idOf t)
    keyOf := fun x => liftIO (ss.keyOf x)
    keySlice := fun x => liftIO (ss.keySlice x)
    termOf := fun x => liftIO (ss.termOf x)
    lowerBound := fun k => liftIO (ss.lowerBound k) }

/-! ## Named graphs -/

def Session.graphIdsOfQuads (ss : Session) : IO (Array Nat) := do
  let pat : IdQuery.Pat := { s := .var "s", p := .var "p", o := .var "o", g := .var "g", named := true }
  let spec := IdQuery.mkSpec pat 0 (fun v => v == "g")
  let seen ← IO.mkRef ({} : Std.HashSet Nat)
  match ← (IdQuery.scanFoldM ss.store spec true () fun _ ch => do
      let mut s ← liftIO seen.get
      liftIO (seen.set {})
      for i in [0:ch.table.rows] do
        let x := (ch.table.at 0 i).toNat
        if x != 0 then s := s.insert x
      liftIO (seen.set s)
      pure ((), true)).run with
  | .error e => ioErr s!"graph scan failed: {e}"
  | .ok _ => pure ()
  return L4Factoidal.Qlvr.mergeSortBy (← seen.get).toArray (· ≤ ·)

/-- The named graphs of the generation, sorted: the graph list GNL1, or the
    graph ids of the quads for a generation that has no list; read once. -/
def Session.namedGraphIds (ss : Session) : IO (Array Nat) := do
  match ← ss.baseNamedRef.get with
  | some xs => return xs
  | none =>
    let xs ← match artifactOf? ss.manifest "GNL1" with
      | some a =>
        match GraphList.decodeAt (← ss.fetch a.file a.bytes 0 a.bytes) with
        | some ids => pure ids
        | none => ioErr s!"{a.file}: does not decode as a GNL1 graph list"
      | none => ss.graphIdsOfQuads
    ss.baseNamedRef.set (some xs)
    return xs

def Session.storeWith (ss : Session) (sip : Option Nat := some 16) (aggOnIds : Bool := true) :
    IdQuery.Store IO :=
  { ss.store with sipFactor := sip, aggOnIds := aggOnIds }

def Session.storeNested (ss : Session) (sip : Option Nat := some 16) (aggOnIds : Bool := true) :
    IdQuery.Store IO :=
  { ss.storeWith sip aggOnIds with
    namedGraphs := some (liftIO do return (← ss.namedGraphIds).map (·.toUInt64)) }

/-! ## The reference fallback -/

def scanAll (ss : Session) (perm : Nat) (key : Array UInt64)
    (f : Array ByteArray → Nat → IO Unit) : IO Unit := do
  let spec : IdQuery.ScanSpec := { perm, key, checks := #[], named := false,
                                   outVars := #["c0", "c1", "c2", "g"], outCols := #[0, 1, 2, 3], eqs := #[] }
  match ← (IdQuery.scanFoldM ss.store spec true () fun _ ch => do
      liftIO (f ch.table.cols ch.table.rows)
      pure ((), true)).run with
  | .ok _ => pure ()
  | .error e => ioErr e

def subjectOf (t : Term) : IO Subject :=
  match t with
  | .iri i => pure (.iri i)
  | .bnode b => pure (.bnode b)
  | _ => ioErr "a subject or graph name that is not an IRI or a blank node"

/-- The quads the planner guard selects, as the dataset they denote, with the
    named graphs the guard keeps that hold no selected quad
    (`Harness.Sbm11Query.selectedDataset`; pure model
    `Storage.SelectedDataset.selectedModel`). -/
def selectedDataset (ss : Session) (q : Query) : IO (Dataset × String) := do
  let preds := L4Factoidal.Storage.ShardManifest.queryQuadConstantPredicates? q
  let graphs := L4Factoidal.Storage.ShardManifest.queryGraphNames? q
  let mut allowed : Option (Array UInt64) := none
  match graphs with
  | none => pure ()
  | some gs =>
    let mut a : Array UInt64 := #[]
    for gn in gs do
      match gn with
      | .defaultGraph => a := a.push 0
      | .iri v => if let some x ← ss.idOf (.iri v) then a := a.push x
      | .bnode l => if let some x ← ss.idOf (.bnode l) then a := a.push x
    allowed := some a
  let rowsRef ← IO.mkRef (#[] : Array (UInt64 × UInt64 × UInt64 × UInt64))
  let collect (perm : Nat) (cols : Array ByteArray) (n : Nat) : IO Unit := do
    let mut acc ← rowsRef.get
    rowsRef.set #[]
    for i in [0:n] do
      let a := IdQuery.at64 cols[0]! i
      let b := IdQuery.at64 cols[1]! i
      let c := IdQuery.at64 cols[2]! i
      let g := IdQuery.at64 cols[3]! i
      let ok := match allowed with
        | some xs => xs.contains g
        | none => true
      if ok then
        acc := acc.push (if perm == 0 then (b, a, c, g) else (a, b, c, g))
    rowsRef.set acc
  let what ← match preds with
    | some ps => do
      let mut found := 0
      for p in ps.eraseDups do
        match ← ss.idOf (.iri p) with
        | some pid =>
          found := found + 1
          scanAll ss 0 #[pid] (collect 0)
        | none => pure ()
      pure s!"predicates={ps.eraseDups.length} (in the dictionary: {found})"
    | none => do
      scanAll ss 2 #[] (collect 2)
      pure "predicates=all"
  let rows ← rowsRef.get
  let mut quads : Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow := Array.mkEmpty rows.size
  let mut withQuad : Std.HashSet UInt64 := {}
  for (s, p, o, g) in rows do
    if g != 0 then withQuad := withQuad.insert g
    let st ← subjectOf (← ss.termOf s)
    let pt ← match ← ss.termOf p with
      | .iri i => pure i
      | _ => ioErr "a predicate that is not an IRI"
    let ot ← ss.termOf o
    let gr : Option Subject ← if g == 0 then pure none else pure (some (← subjectOf (← ss.termOf g)))
    quads := quads.push (gr, { s := st, p := pt, o := ot })
  let mut noQuad : Array NamedGraph := #[]
  for x in ← ss.namedGraphIds do
    let gid := x.toUInt64
    if withQuad.contains gid then continue
    let kept := match allowed with
      | some xs => xs.contains gid
      | none => true
    if kept then noQuad := noQuad.push { name := ← subjectOf (← ss.termOf gid), graph := [] }
  let graphsText := match graphs with
    | some gs => s!"graphs={gs.length}"
    | none => "graphs=all"
  let ds0 := L4Factoidal.Storage.QuadDataset.datasetOfQuads quads.toList
  return ({ ds0 with named := ds0.named ++ noQuad.toList },
          s!"{what} {graphsText} quads={quads.size} named-graphs-without-a-selected-quad={noQuad.size}")

private def stripDatasetClauses (query : Query) : Query :=
  .mk query.form [] query.pattern query.groupBy query.having query.modifier
      query.postValues query.base

/-- A graph (CONSTRUCT, DESCRIBE) as N-Triples lines; returns the number of
    triples. -/
def emitGraph (graph : Graph) (emit : ByteArray → IO Unit) : IO Nat := do
  let mut n := 0
  for tr in graph do
    match Sink.nquadsLineOfTerms .rdf12 (match tr.s with | .iri i => .iri i | .bnode b => .bnode b) (.iri tr.p) tr.o none with
    | .ok l =>
      emit (l ++ "\n").toUTF8
      n := n + 1
    | .error e => ioErr e
  return n

def emitPost (ans : IdQuery.PostAnswer) (emit : ByteArray → IO Unit) : IO Unit := do
  match ans with
  | .solutions vars rows => emit (QueryResult.bindings vars rows).toSrjFast.toUTF8
  | .boolean b => emit (QueryResult.boolean b).toSrjFast.toUTF8
  | .graph g => discard <| emitGraph g emit

/-- The reference evaluator over the selected dataset
    (`Harness.Sbm11Query.runReference`). `clockEnv` carries the instant of
    the query (`NOW()`), read once by the caller. -/
def runReference (ss : Session) (clockEnv : EvalEnv) (q : Query) (reason : String)
    (emit : ByteArray → IO Unit) : IO (Nat × String) := do
  let (ds, what) ← selectedDataset ss q
  let (applied, _) := applyDataset q.dataset ds ds.default
  let stripped := stripDatasetClauses q
  let env : EvalEnv := { clockEnv with dataset := some applied, ext := L4Factoidal.Geo.extFns, base := q.base }
  let indexed := L4Factoidal.Storage.QuadDataset.namesAreIris applied
  let line := s!"path=reference reason=\"{reason}\" {what}"
  match stripped.serviceFailure env applied with
  | some f => ioErr f.message
  | none =>
  match q.form with
  | .select _ =>
    let rows := L4Factoidal.Storage.SelectedDataset.referenceSelect env q applied
    emit (QueryResult.bindings q.projectedVars rows).toSrjFast.toUTF8
    return (rows.length, line)
  | .ask =>
    let answer? :=
      if indexed then (L4Factoidal.Dataflow.LawfulDataset.ofDataset applied).runAsk env stripped
      else some (evalAsk env applied stripped)
    let answer := match answer? with
      | some answer => answer
      | none => evalAsk env applied stripped
    emit (QueryResult.boolean answer).toSrjFast.toUTF8
    return ((if answer then 1 else 0), line)
  | .construct _ | .describe _ =>
    let graph := match q.form with
      | .construct _ => evalConstruct env applied stripped
      | _ => evalDescribe env applied stripped
    let n ← emitGraph graph emit
    return (n, line)

/-! ## Running a query -/

structure Outcome where
  rows : Nat
  /-- `path=ids` or `path=reference ...` -/
  path : String

/-- Run one parsed query (`Harness.Sbm11Query.runOne` with one thread). -/
def runOne (ss : Session) (clockEnv : EvalEnv) (q : Query) (emit : ByteArray → IO Unit)
    (forceReference : Bool := false) (sip : Option Nat := some 16) (aggOnIds : Bool := true) :
    IO Outcome := do
  let plan? := if forceReference then .error "reference requested" else IdQuery.translate q
  match plan? with
  | .error reason =>
    let (n, line) ← runReference ss clockEnv q reason emit
    return { rows := n, path := line }
  | .ok plan =>
    let env := IdGroup.queryEnvOf clockEnv q.base
    let refusedOr (e : String) : IO Outcome := do
      if e.startsWith "refused: " then
        let (n, line) ← runReference ss clockEnv q (e.drop 9).toString emit
        return { rows := n, path := line }
      ioErr s!"id query failed: {e}"
    match plan.post with
    | some ps =>
      if plan.nested.isSome then
        match ← (IdGroup.runNestedM (ss.storeNested sip aggOnIds) plan ps env).run with
        | .ok (ans, st) =>
          emitPost ans emit
          return { rows := st.rows, path := "path=ids" }
        | .error e => refusedOr e
      else
      match ← (IdQuery.runPostM (ss.storeWith sip aggOnIds) plan ps env).run with
      | .ok (ans, st) =>
        emitPost ans emit
        return { rows := st.rows, path := "path=ids" }
      | .error e => refusedOr e
    | none =>
    match ← (IdQuery.runPlanM (ss.storeWith sip) plan emit false none env).run with
    | .ok st => return { rows := st.rows, path := "path=ids" }
    | .error e => refusedOr e

end L4Factoidal.Storage.Sbm11.HostSession
