/-
Harness/Sbm11Query — `l4sbm11 query` and `l4sbm11 serve`: SPARQL over an SBM11
generation (stage 4, https://github.com/danbri/factoidal/issues/790).

  l4sbm11 query GEN ('SPARQL' | --file Q.rq) [--base IRI] [--explain]
                [--repeat N] [--reference-render] [--reference]
                [--verify merkle|none] [--threads N] [--sip auto|always|off]
                [--sparql12] [--no-agg-ids]
  l4sbm11 serve GEN [--verify merkle|none] [--sparql12]
  l4sbm11 prm-check GEN
  l4sbm11 frame-check GEN

The query is parsed by the repository's SPARQL parser. A query in the id
fragment (`IdQuery.translate`) runs on ids (`IdQuery.runPlanM`); every other
query runs the reference evaluator over the quads of the generation that the
planner guard selects (`ShardManifest.queryQuadConstantPredicates?` and
`queryGraphNames?`, the guard of `quadEntriesForQuery`): the quads of the
predicates the query names, in the graphs it reads, or every quad when the
guard selects nothing. A line on stderr names the path that ran
(`sbm11-query: path=ids` or `path=reference reason=...`).

  --explain           the plan, blocks and bytes read (stderr)
  --repeat N          open once, run N times, write the answer of the last
                      run only; the median execution time is printed
  --reference-render  print every term through `jsonOfTerm` (the key
                      printer is compared with it in tests/sbm11/run.sh)
  --reference         run the reference fallback even for the id fragment
  --no-agg-ids        decode the rows of a grouped SELECT and run `selectPost`
                      on them, also when its aggregates could run on ids
                      (`IdAgg.aggregateM`, issue 825): to measure and to
                      compare the two paths. Answers are the same.
  --sparql12          read the query with the SPARQL 1.2 grammar: triple-term
                      patterns `<<( s p o )>>`, reified triples, annotations,
                      TRIPLE, SUBJECT, PREDICATE, OBJECT, isTRIPLE (the
                      default is the SPARQL 1.1 grammar). The id path takes a
                      triple-term pattern without variables or blank nodes as
                      a constant; one with a variable or a blank node inside
                      goes to the reference fallback; the triple functions are
                      evaluated by the reference evaluator's own functions on
                      decoded terms (issue 792 item 1)
  --threads N         scan tasks per BGP scan (issue 799): the selected blocks
                      of each scan are cut into N consecutive chunks, each
                      scanned in its own task; N = 1 is the single-thread path.
                      Stage 1b: a single-pattern query that streams, counts
                      or orders with LIMIT renders, counts or keeps its first
                      rows in each chunk (at most 16 blocks per chunk when it
                      streams, N tasks at once), and the parent combines the
                      chunk results in chunk order
  --sip S             sideways information passing (issue 809): the right
                      scan of a merge join takes the sorted distinct left
                      values of the join variable as candidates and decodes
                      the other columns of the matching rows only. `auto`
                      (default): when 16 × left rows < the scan's PRM1
                      estimate; `always`: whenever the join shape allows it
                      (tests); `off`: never. Answers are the same in each.
  --verify V          how reads are checked (`Sbm11Gen.Verify`,
                      https://github.com/danbri/factoidal/issues/796):
                      `merkle` widens each read to its 65,536-byte chunks and
                      checks each by its Merkle proof; `none` reads exactly
                      the needed bytes and hashes nothing (activation checked
                      the files). Default: `none` when a `CURRENT` pointer
                      names GEN (an activated generation), else `merkle`.

Output: SPARQL JSON for SELECT and ASK; N-Triples for CONSTRUCT and DESCRIBE.
`serve` reads one query per line of stdin (or `--file PATH`) and writes one
line of SPARQL JSON per query. At start it reports on stderr the size of the
overlay that the log of the generation made (`serve: overlay size: N log
entries in B batches, M bytes of log, ...`) and where it stands against the
log size limit that `SBM11_MAX_OVERLAY_ENTRIES` and `SBM11_MAX_OVERLAY_BYTES`
set (`Sbm11Compact`: `l4sbm11 update` refuses a request that would pass it;
https://github.com/danbri/factoidal/issues/851).

Opening a generation that has a log replays it (`Session.loadOverlay`): the
distinct terms of the log are looked up in the dictionary in key order, each
page read once (`Session.prefillBaseIds`, `Dict.lookupWalkM`, issue 858), then
the entries are applied in log order. `SBM11_REPLAY_LOOKUP=each` looks every
occurrence of every term up on its own, as the replay did before issue 858
(the oracle of the differential test in tests/sbm11/update_where.sh).

This is a HARNESS: it does file I/O, and it runs scans on several threads. The
query engine is `L4Factoidal.Storage.Sbm11.IdQuery`; the session, the delta
overlay and the query driver are `L4Factoidal.Storage.Sbm11.QuerySession`
(https://github.com/danbri/factoidal/issues/1009 KR1), the same functions the
wasm ops `sbm11Open`, `sbm11Query` and `sbm11Close` call
(`Wasm/Ops/Sbm11.lean`) over a storage medium.
-/
import Harness.Sbm11Gen
import Harness.Sbm11Delta
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.IdGroup
import L4Factoidal.Storage.Sbm11.QueryEnv
import L4Factoidal.Storage.Sbm11.TermKeyFast
import L4Factoidal.Storage.Sbm11.ParallelScan
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.OverlayLimit
import L4Factoidal.Storage.Sbm11.PrmAt
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.DictRange
import L4Factoidal.Storage.Sbm11.DictFinger
import L4Factoidal.Storage.Sbm11.FrameWords
import L4Factoidal.Storage.Sbm11.MemoCache
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.SelectedDataset
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.Geo.Functions
import Wasm.Ops.Clock
import Std.Sync.Mutex
import Std.Data.TreeMap
import Harness.WorkerPool
import L4Factoidal.Dataflow.Store
import L4Factoidal.Storage.Sbm11.QuerySession

namespace Harness.Sbm11Query

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Manifest
open Harness.Sbm11Gen
open L4Factoidal.Storage.ChunkedArtifact (Ref)

/-! ## A generation opened lazily

The session state, the dictionary, the id store, the delta overlay and the
query driver are the library's (`L4Factoidal.Storage.Sbm11.QuerySession`,
https://github.com/danbri/factoidal/issues/1009 KR1): `Session` extends
`QuerySession.Core` and is a `QuerySession.SessionOps` instance, and every
method below that is not about threads, the worker pool or the Merkle-checked
file reads calls the library function of the same name. What this file adds:
the reads of the files (`readsOf`: POSIX `pread`, under `--verify merkle`
through the verified chunk caches), the dictionary pages that scan tasks share
(`taskPages`, `sharedPage`, `prefetch`), the task views, and the divided scans
of `--threads N`. -/

/-- A page of `Session.taskPages` (issue 799, stage 1b): its keys, or a
    promise of them while one task loads it (the other tasks that need the
    page wait for the promise, so a page is loaded once). -/
inductive TaskPage where
  | ready (ks : ByteArray × Array Nat)
  | loading (p : IO.Promise (Except String (ByteArray × Array Nat)))

/-- The files of a permutation: the paths of its PRB1 and PRM1 files and,
    under `Verify.merkle`, their admitted Merkle leaves and verified chunk
    caches. Loaded at the first read of the permutation (`permFiles`). -/
structure PermFiles where
  prbPath : String
  prbRef : Ref
  leaves : List L4Factoidal.Storage.BlockMerkle.Digest
  cache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  prmPath : String
  prmRef : Ref
  prmLeaves : List L4Factoidal.Storage.BlockMerkle.Digest
  prmCache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache

/-- A permutation opened by a query session: the paths of its files and the
    library's state of it (`QuerySession.PermState`: the PRM1 block count and
    the answers of `PrmRange.rangeM` asked so far). Its PRM1 file is never
    read whole (https://github.com/danbri/factoidal/issues/805). -/
structure LoadedPerm where
  prbPath : String
  prmPath : String
  /-- the block count of the PRM1 header -/
  count : Nat
  ranges : IO.Ref (Std.HashMap (Array UInt64) (Array BlockMeta))

/-- The dictionary page cache of one pool worker (stage 1h of
    docs/designissues/2026-10-12-parallel-block-scans.md): made by the
    worker's own thread when the pool starts (`Harness.WorkerPool.start`) and
    given to each job of that worker, so it is never reachable from another
    thread. The Lean runtime then updates it in place and counts references
    to its pages without atomic operations, and the pages a worker copied
    stay with it from one query to the next. -/
abbrev WorkerPages := IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))

/-- An open generation: the library's session state (`QuerySession.Core`:
    the manifest, the dictionary header, the opened permutations, the page
    cache, the id caches, the delta overlay and the counters) over the reads
    of `readsOf`, and the state of the native command: the open generation
    `g` (paths, Merkle leaves, chunk caches, byte counters), the locks and the
    shared pages of scan tasks, and the worker pool. -/
structure Session extends QuerySession.Core where
  g : Gen
  /-- The files of each permutation, loaded at its first read (`permFiles`). -/
  files : IO.Ref (Array (Option PermFiles))
  /-- Under `Verify.merkle`: GDX1, read whole on the first dictionary access
      (102 KB on olympics: 12 bytes per page), its length and SHA-256 checked
      against the manifest. Unused under `none` (each GDX1 entry is one
      `pread`). -/
  gdx : IO.Ref (Option ByteArray)
  /-- Serialises the verified chunk cache (`merkle` reads) between scan
      tasks (issue 799). Shared by every task view of the session. -/
  lock : Std.Mutex Unit
  /-- Serialises the dictionary between task views (issue 799, stage 1b):
      `taskPages`, and under `merkle` the page loads (the GDX1 copy and the
      GDV1 and GDX1 chunk caches are shared). Shared by every task view. -/
  dictLock : Std.Mutex Unit
  /-- The dictionary pages that scan tasks loaded or are loading (issue 799,
      stage 1b), shared by the tasks under `dictLock` and read by the session
      on a miss in `pages`; at most `SBM11_PAGES` entries, emptied when full,
      like `pages`. A tree map: a value that two threads can reach is never
      updated in place by the Lean runtime (`lean_is_exclusive` is false for
      it), so each insert into a shared hash map copied its bucket array; an
      insert into a tree map copies one path. Empty while no task has run. -/
  taskPages : IO.Ref (Std.TreeMap Nat TaskPage)
  /-- A task view (`Session.view`): `pageKeys` goes to `taskPages` under
      `dictLock` on a miss in the view's own `pages`. -/
  inTask : Bool := false
  /-- In a task view (made by the task, `Session.local`): the pages it has
      taken once from `taskPages` without a copy (`Session.sharedPage`). -/
  onceSeen : Option (IO.Ref (Std.HashSet Nat)) := none
  /-- `min SBM11_PAGES SBM11_TASK_PAGES` (default 256), the page limit of a
      task view's own cache, read once at open (issue 799, KR 1.2). -/
  taskPageLimit : Nat := 256
  /-- The session's worker pool (`Harness.WorkerPool`, issue 961): started by
      `l4sbm11 query --threads N` for N above 1 (N - 1 workers; the calling
      thread is the N-th), stopped when the command ends. `none`: divided work
      runs on the Lean task pool (`IO.asTask`). Each worker keeps a
      dictionary page cache of its own for the life of the pool
      (`WorkerPages`, stage 1h). -/
  pool : Option (Harness.WorkerPool.Pool WorkerPages) := none
  /-- `SBM11_PHASES` set: the id path records the time of each phase mark
      (`IdQuery.Store.mark`) and `l4sbm11 query --repeat N` prints the median
      time of each phase over runs 2 to N. -/
  phases : Bool := false
  /-- `IdQuery.Par.renderRows` (`SBM11_RENDER_ROWS`; 0: the calling thread
      renders a finished table) -/
  renderRows : Nat := IdQuery.renderJobRows
  /-- `IdQuery.Par.streamPerThread` (`SBM11_STREAM_JOBS`) -/
  streamPerThread : Nat := IdQuery.streamJobsPerThread
  /-- `IdQuery.Par.sortedRows` (`SBM11_SORTED_RENDER_ROWS`; 0: the calling
      thread renders after the sort; the gate fixtures of
      tests/sbm11/threads.sh and part (z) of tests/sbm11/run.sh set 1, so
      that results of a few rows take the path) -/
  sortedRows : Nat := 64
  /-- A view of a pool worker that renders rows beside the ORDER BY sort
      (stage 1o, `renderStartPar`): a page from `taskPages` is copied into the
      worker's own cache on its first use (`sharedPage`), not on its second.
      The rendering of one query reads most pages once, so with the rule of
      the scans every query read them again from `taskPages` (a ref that every
      thread reads, and pages whose reference counts are atomic): olympics
      q07's 313 rows took 2 to 4 times as long per row on a worker as on the
      calling thread. The worker's cache lives as long as the pool, so the
      copy is made once. -/
  copyFirst : Bool := false
  /-- `IdQuery.Par.joinShare`: the share of the calling thread's range of a
      divided merge join, in tenths of an equal share (`SBM11_JOIN_SHARE`,
      default 14; stage 1p of docs/designissues/2026-10-12-parallel-block-scans.md) -/
  joinShare : Nat := 14

/-- The default of `SBM11_PAGES`, the most dictionary pages a cache holds. A
    page is about 4.5 KB (olympics q19 needs between 4,096 and 8,192 pages). At
    2,048 pages, the former default, q19 and q21 loaded pages again on every
    run, and q19 took 97 ms against 36 ms with no limit (issue 799, KR 1.2). -/
def defaultPages : Nat := 8192

/-- `SBM11_PAGES` (default `defaultPages`), read once per session. -/
def pagesLimitEnv : IO Nat := do
  return ((← IO.getEnv "SBM11_PAGES").bind String.toNat?).getD defaultPages

/-- The page limit of a task view's own cache: `SBM11_TASK_PAGES` (default
    256), never more than `SBM11_PAGES`; read once per session. -/
def taskPagesLimitEnv : IO Nat := do
  return min (← pagesLimitEnv) (((← IO.getEnv "SBM11_TASK_PAGES").bind String.toNat?).getD 256)

/-! ### The reads of the files -/

/-- The files of permutation `p`, loaded at the first read: under `merkle`
    the leaves of the Merkle trees of its PRM1 and PRB1 files, admitted
    against the manifest's roots, and a verified chunk cache for each. -/
def permFiles (g : Gen) (files : IO.Ref (Array (Option PermFiles))) (p : Nat) : IO PermFiles := do
  match (← files.get)[p]? with
  | some (some f) => return f
  | some none =>
    let m := g.manifest
    let nm := (permNamesArr[p]!).toUpper
    let prmA ← artifact m s!"PRM1-{nm}"
    let prbA ← artifact m s!"PRB1-{nm}"
    let prmPath := s!"{g.dir}/{prmA.file}"
    let prbPath := s!"{g.dir}/{prbA.file}"
    let prmLeaves ← loadLeaves g.verify g.fileBytes prmPath prmA.merkle
    let prmCache ← newChunkCache g.verify prmA.merkle
    let leaves ← loadLeaves g.verify g.fileBytes prbPath prbA.merkle
    let cache ← newChunkCache g.verify prbA.merkle
    let f : PermFiles := { prbPath, prbRef := prbA.merkle, leaves, cache, prmPath, prmRef := prmA.merkle,
                           prmLeaves, prmCache }
    files.modify (·.set! p (some f))
    return f
  | none => throw (IO.userError s!"no permutation {p}")

/-- GDX1 whole, under `Verify.merkle` (`Session.gdx`). -/
def gdxWhole (g : Gen) (gdx : IO.Ref (Option ByteArray)) : IO ByteArray := do
  match ← gdx.get with
  | some b => return b
  | none =>
    let a ← artifact g.manifest "GDX1"
    let b ← IO.FS.readBinFile g.gdxPath
    g.fileBytes.modify (· + b.size)
    if b.size != a.bytes || Harness.nativeSha256 b != a.sha256 then
      throw (IO.userError s!"{g.gdxPath}: length or SHA-256 differs from the manifest")
    -- `modify`, not `set`: another thread may read `gdx` with `get` (issue
    -- 981, `Harness.WorkerPool` module comment)
    gdx.modify fun _ => some b
    return b

/-- Bytes `[off, off + len)` of GDX1. `none`: one `pread`; `merkle`: cut
    from the whole file (`gdxWhole`). -/
def sessionGdx (g : Gen) (gdx : IO.Ref (Option ByteArray)) (off len : Nat) : IO ByteArray := do
  if g.verify == .none then
    return (← verifiedRead g g.gdxPath g.gdxRef g.gdxLeaves g.gdxCache off len)
  let b ← gdxWhole g gdx
  if off + len > b.size then throw (IO.userError s!"GDX1: read past the end")
  return b.extract off (off + len)

/-- Bytes `[off, off + len)` of GDV1. `merkle`: through the verified chunk
    cache: each 65,536-byte chunk is admitted once by its Merkle proof
    (`readVerifiedChunkCached?`), then ranges are cut from it. `none`: one
    `pread` of exactly those bytes. -/
def sessionGdv (g : Gen) (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  if g.verify == .none then
    return (← verifiedRead g g.gdvPath g.gdvRef g.gdvLeaves g.gdvCache off len)
  let cb := g.gdvRef.chunkBytes
  let first := off / cb
  let last := (off + len - 1) / cb
  let mut out := ByteArray.emptyWithCapacity len
  for c in [first:last + 1] do
    match ← Harness.PosixRangeIO.readVerifiedChunkCached? g.gdvPath g.gdvRef g.gdvLeaves g.gdvCache c with
    | some (chunk, fp) =>
      g.fetchedBytes.modify (· + fp.fetchedBytes)
      g.fileBytes.modify (· + fp.fetchedBytes)
      let lo := max off (c * cb) - c * cb
      let hi := min (off + len) ((c + 1) * cb) - c * cb
      if hi > chunk.size then throw (IO.userError s!"GDV1: chunk {c} is short")
      out := chunk.copySlice lo out out.size (hi - lo)
    | none => throw (IO.userError s!"GDV1: chunk {c} refused")
  return out

/-- **The reads of the native session** (`QuerySession.Reads`): GDX1 and
    GDV1 ranges (`sessionGdx`, `sessionGdv`), PRM1 and PRB1 ranges of a
    permutation (`verifiedRead`; under `merkle` one read at a time, since the
    chunk caches are shared by the task views, issue 799) and the graph list
    (`Sbm11Gen.readGraphListBytes`). -/
def readsOf (g : Gen) (files : IO.Ref (Array (Option PermFiles))) (gdx : IO.Ref (Option ByteArray))
    (lock : Std.Mutex Unit) : QuerySession.Reads :=
  { gdx := sessionGdx g gdx
    gdv := sessionGdv g
    prm := fun p off len => do
      let f ← permFiles g files p
      match g.verify with
      | .merkle => lock.atomically (verifiedRead g f.prmPath f.prmRef f.prmLeaves f.prmCache off len)
      | .none => verifiedRead g f.prmPath f.prmRef f.prmLeaves f.prmCache off len
    prb := fun p off len => do
      let f ← permFiles g files p
      match g.verify with
      | .merkle => lock.atomically (verifiedRead g f.prbPath f.prbRef f.leaves f.cache off len)
      | .none => verifiedRead g f.prbPath f.prbRef f.leaves f.cache off len
    graphList := readGraphListBytes g }

/-- Open a generation for queries, reads checked as `v` says (no default:
    the caller chooses; the CLI's choice is `Sbm11Gen.cliDefaultVerify`). -/
def openSession (v : Verify) (dir0 : String) : IO Session := do
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let mbytes ← IO.FS.readBinFile s!"{dir}/{manifestName}"
  let some m := decodeManifest mbytes.data.toList
    | throw (IO.userError s!"{dir}/{manifestName}: does not decode as an SBM11 manifest")
  if v == .none then checkLengths dir m
  let fileBytes ← IO.mkRef mbytes.size
  let gdvA ← artifact m "GDV1"
  let gdxA ← artifact m "GDX1"
  let gdvPath := s!"{dir}/{gdvA.file}"
  let gdxPath := s!"{dir}/{gdxA.file}"
  let gdvLeaves ← loadLeaves v fileBytes gdvPath gdvA.merkle
  let gdxLeaves ← loadLeaves v fileBytes gdxPath gdxA.merkle
  let readBytes ← IO.mkRef 0
  let fetchedBytes ← IO.mkRef 0
  let gdvCache ← newChunkCache v gdvA.merkle
  let gdxCache ← newChunkCache v gdxA.merkle
  let g0 : Gen := { dir, manifest := m, verify := v, gdvPath, gdxPath, gdvRef := gdvA.merkle, gdxRef := gdxA.merkle,
                    gdvLeaves, gdxLeaves, gdvCache, gdxCache, dictHdr := default, perms := #[],
                    readBytes, fetchedBytes, fileBytes }
  let hdrBytes ← verifiedRead g0 gdxPath gdxA.merkle gdxLeaves gdxCache 0 Dict.gdxHeaderBytes
  let dictHdr ← ok "GDX1" (Dict.parseGdxHeader hdrBytes)
  let g := { g0 with dictHdr }
  let files ← IO.mkRef #[none, none, none, none]
  let gdx ← IO.mkRef none
  let lock ← Std.Mutex.new ()
  return { manifest := m, reads := readsOf g files gdx lock, dictHdr, termCount := dictHdr.termCount,
           perms := ← IO.mkRef #[none, none, none, none],
           pages := ← IO.mkRef {}, frameBytes := ← IO.mkRef 0, prmBytes := ← IO.mkRef 0,
           lookups := ← IO.mkRef 0,
           ovVocab := ← IO.mkRef #[], ovIds := ← IO.mkRef {}, baseIds := ← IO.mkRef {},
           idMemo := ← IO.mkRef {},
           baseNamedRef := ← IO.mkRef none,
           pageLimit := ← pagesLimitEnv,
           g, files, gdx, lock, dictLock := ← Std.Mutex.new (), taskPages := ← IO.mkRef {},
           taskPageLimit := ← taskPagesLimitEnv }

/-- The permutation `p`, opened on its first use (`QuerySession.Core.perm`:
    the PRM1 header only), with the paths of its files. -/
def Session.perm (ss : Session) (p : Nat) : IO LoadedPerm := do
  let ps ← ss.toCore.perm p
  let f ← permFiles ss.g ss.files p
  return { prbPath := f.prbPath, prmPath := f.prmPath, count := ps.count, ranges := ps.ranges }

/-! ### Dictionary pages shared by scan tasks -/

/-- The class of pages that a full cache drops (`MemoCache.evictClasses`). -/
abbrev evictClasses : Nat := MemoCache.evictClasses

/-- Insert page `pg` in a page map that holds at most `lim` entries
    (`MemoCache.insertEvict`). When the map is full, the entries whose number
    is in the same class modulo `evictClasses` as `pg` are dropped (about one
    sixteenth), and the whole map if that does not make room. The earlier rule
    emptied the whole map when it was full: a scan whose pages are a few more
    than the limit (olympics q19 and q21: between 4,096 and 8,192 pages against
    2,048) then loaded every page again on every run (q19: 97 ms against 36 ms
    with no limit; issue 799, KR 1.2). `MemoCache.coherent_insertEvict`: the
    insert keeps every entry the page of its number. -/
abbrev insertPageBounded {α : Type} (m : Std.HashMap Nat α) (lim pg : Nat) (v : α) : Std.HashMap Nat α :=
  MemoCache.insertEvict m lim pg v

/-- The keys of dictionary page `pg`, packed (`QuerySession.loadPage`). -/
def Session.loadPage (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) :=
  QuerySession.loadPage ss.toCore pg

/-- Put page `pg` in the page cache `c`, emptied first when it holds
    `SBM11_PAGES` pages (default 8,192; 0: no cache). -/
abbrev cachePage (lim : Nat) (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit :=
  QuerySession.cachePage lim c pg ks

/-- Put page `pg` in a task view's own cache (issue 799, stage 1b): emptied
    first when it holds `SBM11_TASK_PAGES` pages (default 256), and never
    more than `SBM11_PAGES`. A task's cache holds copies of pages that
    `taskPages` also holds. Olympics q19 at 4 threads, 7 runs per process
    (2026-10-13): 2,048 pages per task, 74 ms and 156 MB peak RSS; 1,024, 54
    ms and 125 MB; 256, 84 ms and 106 MB (36 MB at 1 thread, 47 MB at 4
    threads with no page cache at all). Those figures were taken with
    `SBM11_PAGES` at the former default of 2,048, where the shared level
    thrashed; with the default of 8,192 (KR 1.2, 2026-10-22, 4 threads, load
    average 2 to 3): 1,024 pages per task, peak RSS 147 MB (q19) and 125 MB
    (q21); 256, 98 to 108 MB and 105 to 108 MB; 0, 97 MB and 102 MB but 3 to 9
    times slower (every page loaded again). A block of 4,096 rows can need more
    pages than a small cache holds, and its prefetched pages then drop others. -/
def cacheTaskPage (lim : Nat) (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit := do
  if lim > 0 then
    c.modify fun m => insertPageBounded m lim pg ks

/-- A copy of a page made by the calling thread. A page in `taskPages` is
    reachable from every task, so taking and releasing a reference to it is an
    atomic operation on one cache line from every thread that renders with it;
    each task and the session keep their own copy (about 2 KB). The copy is
    the same value (`MemoCache.copyPage_eq`). -/
abbrev copyPage (ks : ByteArray × Array Nat) : ByteArray × Array Nat :=
  MemoCache.copyPage ks

/-- Put an entry in `taskPages` (call under `dictLock`), emptied first when
    it holds `SBM11_PAGES` entries. -/
def Session.putTaskPage (ss : Session) (pg : Nat) (e : TaskPage) : IO Unit := do
  let lim := ss.pageLimit
  if lim > 0 then
    ss.taskPages.modify fun m =>
      if m.size < lim then m.insert pg e
      else
        let m' := m.filter fun k _ => k % evictClasses != pg % evictClasses
        (if m'.size < lim then m' else {}).insert pg e

/-- A task view (issue 799, stage 1b) on a miss in its own cache: the page in
    `taskPages`, else this task loads it. Under `none` the load runs outside
    `dictLock` with a promise in `taskPages`, so tasks load different pages
    at the same time and a task that needs a page being loaded waits for it
    (one load per page while `taskPages` holds it; loads under the lock made
    olympics q21 slower at 4 threads than at 1, with the default page limit
    the pages are loaded again on every run). Under `merkle` the load runs
    under the lock (the chunk caches are shared). Then a copy goes to the
    view's own cache. -/
def Session.sharedPage (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) := do
  -- a page that `taskPages` holds ready is read without `dictLock`: the map
  -- is a persistent tree, and `IO.Ref.get` gives the whole map as it was at
  -- one moment (KR 1.2 of batch 3: olympics q19 at 4 threads, 82 percent of
  -- the context switches were waits for `dictLock` in this function)
  if let some (.ready ks) := (← ss.taskPages.get).get? pg then
    -- the first use of a page by this view reads the shared page and keeps
    -- no copy; the second copies it into the view's cache. Most pages of a
    -- scan give one key to a view, and the copy of 4.5 KB per page and view
    -- on every query was the largest cost that 1 thread does not have
    -- (olympics q19 at 4 threads, KR 1.2 of batch 3)
    if let some r := (if ss.copyFirst then none else ss.onceSeen) then
      if ← r.modifyGet (fun st => if st.contains pg then (false, st) else (true, st.insert pg)) then
        return ks
    let ks := copyPage ks
    cacheTaskPage ss.taskPageLimit ss.pages pg ks
    return ks
  let underLock := ss.g.verify != .none
  let step ← ss.dictLock.atomically (do
    match (← ss.taskPages.get).get? pg with
    | some (.ready ks) => pure (Sum.inl ks)
    | some (.loading p) => pure (Sum.inr (p, false))
    | none =>
      if underLock then
        let ks ← ss.loadPage pg
        ss.putTaskPage pg (.ready ks)
        pure (Sum.inl ks)
      else
        let p ← IO.Promise.new
        ss.putTaskPage pg (.loading p)
        pure (Sum.inr (p, true)) : IO ((ByteArray × Array Nat) ⊕ (IO.Promise (Except String (ByteArray × Array Nat)) × Bool)))
  let ks ← match step with
    | .inl ks => pure ks
    | .inr (p, false) =>
      match ← IO.wait p.result? with
      | some (.ok ks) => pure ks
      | some (.error e) => throw (IO.userError e)
      | none => throw (IO.userError s!"GDV1 page {pg}: the task that loaded it stopped")
    | .inr (p, true) =>
      match ← (ss.loadPage pg).toBaseIO with
      | .ok ks =>
        ss.dictLock.atomically (ss.putTaskPage pg (.ready ks) : IO Unit)
        p.resolve (.ok ks)
        pure ks
      | .error e =>
        ss.dictLock.atomically (ss.taskPages.modify (·.erase pg) : IO Unit)
        p.resolve (.error (toString e))
        throw e
  let ks := copyPage ks
  cacheTaskPage ss.taskPageLimit ss.pages pg ks
  return ks

/-- A task view under `none` (issue 799, stage 1b): the dictionary pages of
    the ids in rows `[0, n)` of `t` that the view's cache does not hold, put
    in it with two rounds of `dictLock` for the whole set: one to take the
    pages that `taskPages` holds and to mark the others as loading by this
    task, one to publish the pages this task loaded (outside the lock). A
    page another task is loading is waited for. Rendering then finds every
    page in the view's cache. Per-page rounds (`sharedPage`) made olympics
    q19 slower at 4 threads than at 1 with the default page limit (a fifth of
    the profile in the scheduler: threads that wait for the lock). -/
def Session.prefetch (ss : Session) (t : L4Factoidal.Qlvr.Table) (n : Nat) : IO Unit := do
  if !ss.inTask || ss.g.verify != .none then return
  let localPages ← ss.pages.get
  let mut want : Array Nat := #[]
  let mut seen : Std.HashSet Nat := {}
  -- the page cache first: a pool worker's cache lives across queries
  -- (`Session.withPages`), so most pages are in it, and the rows of a column
  -- often repeat the last page (stage 1h)
  let mut last := ss.termCount
  for c in [0:t.cols.size] do
    for i in [0:min n t.rows] do
      let x := t.at c i
      let tag := (x >>> 60).toNat
      if isDictTag tag then
        let rank := (x &&& 0x0FFFFFFFFFFFFFFF).toNat
        if rank < ss.termCount then
          let pg := rank / Dict.pageTerms
          if pg != last then
            last := pg
            if !localPages.contains pg && !seen.contains pg then
              seen := seen.insert pg
              want := want.push pg
  if want.isEmpty then return
  let (got, waits, mine) ← ss.dictLock.atomically (do
    let tp ← ss.taskPages.get
    let mut got : Array (Nat × (ByteArray × Array Nat)) := #[]
    let mut waits : Array (Nat × IO.Promise (Except String (ByteArray × Array Nat))) := #[]
    let mut mine : Array (Nat × IO.Promise (Except String (ByteArray × Array Nat))) := #[]
    for pg in want do
      match tp.get? pg with
      | some (.ready ks) => got := got.push (pg, ks)
      | some (.loading p) => waits := waits.push (pg, p)
      | none =>
        let p ← IO.Promise.new
        mine := mine.push (pg, p)
    for (pg, p) in mine do ss.putTaskPage pg (.loading p)
    pure (got, waits, mine) : IO _)
  -- load this task's pages outside the lock
  let mut loaded : Array (Nat × (ByteArray × Array Nat)) := Array.mkEmpty mine.size
  let mut failure : Option IO.Error := none
  for (pg, _) in mine do
    if failure.isNone then
      match ← (ss.loadPage pg).toBaseIO with
      | .ok ks => loaded := loaded.push (pg, ks)
      | .error e => failure := some e
  let loadedNow := loaded
  let failed := failure
  ss.dictLock.atomically (do
    for (pg, ks) in loadedNow do ss.putTaskPage pg (.ready ks)
    if failed.isSome then
      for (pg, _) in mine do
        if !(loadedNow.any (·.1 == pg)) then ss.taskPages.modify (·.erase pg)
    pure () : IO Unit)
  let mut k := 0
  for (_, p) in mine do
    match loaded[k]? with
    | some (_, ks) => p.resolve (.ok ks)
    | none => p.resolve (.error (match failure with | some e => toString e | none => "not loaded"))
    k := k + 1
  if let some e := failure then throw e
  for (pg, ks) in got ++ loaded do cacheTaskPage ss.taskPageLimit ss.pages pg (copyPage ks)
  for (pg, p) in waits do
    match ← IO.wait p.result? with
    | some (.ok ks) => cacheTaskPage ss.taskPageLimit ss.pages pg (copyPage ks)
    | some (.error e) => throw (IO.userError e)
    | none => throw (IO.userError s!"GDV1 page {pg}: the task that loaded it stopped")

/-- The keys of a page: the cache `pages`; on a miss in a task view
    `sharedPage`; on a miss in the session, the pages scan tasks loaded
    (empty unless a divided path ran), then the file. -/
def Session.pageKeys (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) := do
  match (← ss.pages.get).get? pg with
  | some ks => return ks
  | none =>
    if ss.inTask then return ← ss.sharedPage pg
    -- with a worker pool (stage 1j) the calling thread renders and runs
    -- jobs while the workers load pages: it loads through `taskPages` as
    -- they do, so that no page is read from the file twice (the range
    -- bytes of `tests/sbm11/threads.sh` equal those of one thread)
    if ss.pool.isSome then return ← { ss with taskPageLimit := ss.pageLimit }.sharedPage pg
    let tp ← ss.taskPages.get
    if !tp.isEmpty then
      if let some (.ready ks) := tp.get? pg then
        let ks := copyPage ks
        cachePage ss.pageLimit ss.pages pg ks
        return ks
    let ks ← ss.loadPage pg
    cachePage ss.pageLimit ss.pages pg ks
    return ks

/-! ### The id store -/

/-- The phase marks of the current run (`Session.phases`): label and
    `IO.monoNanosNow` at the end of the phase. -/
initialize phaseMarks : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

def phaseMark (l : String) : IO Unit := do
  let t ← IO.monoNanosNow
  phaseMarks.modify (·.push (l, t))

/-- The native session as a library session: its pages come from
    `Session.pageKeys` (the task views' shared pages), it prefetches the pages
    of a block in a task view (`Session.prefetch`), and it marks phases when
    `SBM11_PHASES` is set. -/
instance : QuerySession.SessionOps Session where
  core s := s.toCore
  setCore s c := { s with toCore := c }
  pageKeys := Session.pageKeys
  prefetch s := some (Session.prefetch s)
  mark s := if s.phases then some phaseMark else none

def Session.keySlice (ss : Session) (x : UInt64) : IO (ByteArray × Nat × Nat) := QuerySession.keySlice ss x
def Session.keyOf (ss : Session) (x : UInt64) : IO ByteArray := QuerySession.keyOf ss x
def Session.termOf (ss : Session) (x : UInt64) : IO Term := QuerySession.termOf ss x

/-- The id of the dictionary key `k` of rank `r`. -/
abbrev dictIdOfRank (k : ByteArray) (r : Nat) : UInt64 := QuerySession.dictIdOfRank k r

def Session.overlayIdOf (ss : Session) (t : Term) : IO (Option UInt64) := ss.toCore.overlayIdOf t

/-- The most entries `Session.idMemo` holds. -/
abbrev idMemoLimit : Nat := QuerySession.idMemoLimit

/-- The id of a term (`QuerySession.Core.idOf`): its inline code, its
    dictionary id (from `baseIds` during a replay, else from `idMemo`, else one
    `Dict.lookupM`), else the id the delta log gave it. -/
def Session.idOf (ss : Session) (t : Term) : IO (Option UInt64) := ss.toCore.idOf t

def Session.lowerBound (ss : Session) (k : ByteArray) : IO Nat := ss.toCore.lowerBound k

/-- The PRM1 entries of the blocks of permutation `p` that may hold a row
    with the key prefix (`QuerySession.Core.rangeFor`). -/
def Session.rangeFor (ss : Session) (p : Nat) (key : Array UInt64) : IO (Array BlockMeta) :=
  ss.toCore.rangeFor p key

def Session.prb (ss : Session) (p off len : Nat) : IO ByteArray := ss.toCore.prb p off len

/-- A view of the session for one scan task (issue 799): its own byte and
    lookup counters, its reads over a copy of the open generation with those
    counters, and a copy of the permutations opened so far (the parent opens a
    permutation before it starts tasks, so a task never opens one). The chunk
    caches, the locks, the GDX1 copy and `taskPages` (read under `dictLock`)
    are shared; the session's own page cache is not (`pages` here is a
    placeholder that the task replaces with a cache it creates itself,
    `Session.local`). A task reaches the dictionary only through `pageKeys`
    (`keySlice`, `keyOf`, `termOf`): never `idOf` or `lowerBound`, which the
    parent calls before it starts tasks. The parent adds the view's counters
    after the task has finished (`Session.absorb`). -/
def Session.view (ss : Session) : IO Session := do
  let g' : Gen := { ss.g with readBytes := ← IO.mkRef 0, fetchedBytes := ← IO.mkRef 0,
                              fileBytes := ← IO.mkRef 0 }
  let files' ← IO.mkRef (← ss.files.get)
  return { ss with g := g', files := files', reads := readsOf g' files' ss.gdx ss.lock,
                   perms := ← IO.mkRef (← ss.perms.get), frameBytes := ← IO.mkRef 0,
                   prmBytes := ← IO.mkRef 0,
                   lookups := ← IO.mkRef 0, pages := ← IO.mkRef {}, inTask := true }

/-- The view with a page cache made by the calling thread (call it in the
    task). A cache made in the parent is reachable from two threads, so the
    Lean runtime marks it shared and never updates it in place: every insert
    copied the whole hash map (q21 at 4 threads: 335 ms against 158 ms at one
    thread, `lean_copy_expand_array` and `lean_mark_mt` at the top of the
    profile). -/
def Session.local (v : Session) : IO Session := do
  return { v with pages := ← IO.mkRef {}, onceSeen := some (← IO.mkRef {}) }

/-- The pages a pool worker keeps in its own cache (`WorkerPages`), never
    more than `SBM11_PAGES`. Olympics q19 at 4 threads renders with about
    2,100 dictionary pages per query; a worker that does every fourth block
    range needs about a quarter of them and the pages every range shares. -/
def workerPageLimit : Nat := 2048

/-- The view with the page cache of the pool worker that runs the job (call
    it in the job). The cache lives as long as the pool: a page that the
    worker uses twice in one fold is copied into it (`onceSeen`, made here by
    the worker) and kept for later queries. -/
def Session.withPages (v : Session) (wp : WorkerPages) : IO Session := do
  return { v with pages := wp, onceSeen := some (← IO.mkRef {}),
                  taskPageLimit := min v.pageLimit workerPageLimit }

/-- Add the counters of a finished task view to the session. -/
def Session.absorb (ss v : Session) : IO Unit := do
  ss.frameBytes.modify (· + (← v.frameBytes.get))
  ss.prmBytes.modify (· + (← v.prmBytes.get))
  ss.lookups.modify (· + (← v.lookups.get))
  ss.g.readBytes.modify (· + (← v.g.readBytes.get))
  ss.g.fetchedBytes.modify (· + (← v.g.fetchedBytes.get))
  ss.g.fileBytes.modify (· + (← v.g.fileBytes.get))

def liftIO {α : Type} (x : IO α) : ExceptT String IO α := ExceptT.lift x

/-- Start `act` on another thread: a job of worker `i` of the session's worker
    pool when it has one and `i` is below its size (a polling worker starts it
    within microseconds), else a task of
    the Lean pool (`IO.asTask`; a parked pool thread starts it 50 to 120
    microseconds later on the 4-vCPU test VM). -/
def Session.spawnAt {α : Type} (ss : Session) (i : Nat) (act : IO α) :
    IO (Harness.WorkerPool.Handle (Except IO.Error α)) := do
  match ss.pool with
  | some p => if i < p.size then p.spawnOn i act else return .task (← IO.asTask act)
  | none => return .task (← IO.asTask act)

/-- `Session.spawnAt` for a job that uses the page cache of the pool worker
    that runs it (`some`), or `none` when the job runs on the Lean task pool. -/
def Session.spawnLocal {α : Type} (ss : Session) (i : Nat) (act : Option WorkerPages → IO α) :
    IO (Harness.WorkerPool.Handle (Except IO.Error α)) := do
  match ss.pool with
  | some p => if i < p.size then p.spawnWith i (fun wp => act (some wp)) else return .task (← IO.asTask (act none))
  | none => return .task (← IO.asTask (act none))

/-- Wait for a job of `Session.spawnAt`: a pool job's result cell is polled
    for at most the pool's poll time before the thread blocks. -/
def Session.await {α : Type} (ss : Session) (h : Harness.WorkerPool.Handle α) : IO α :=
  h.await (match ss.pool with | some p => p.spinNs | none => 0)

/-- The session's id store on one thread (`QuerySession.store`). -/
def Session.store (ss : Session) : IdQuery.Store IO := QuerySession.store ss

/-! ## Parallel block scans (stage 1, issue 799) -/

/-- A new copy of a word of a PRM1 entry (a dictionary id can be a big
    number object). -/
@[noinline] def freshNat (n : Nat) : Nat := n.succ - 1

/-- A new copy of a PRM1 entry and its two rows. -/
def freshMeta (b : BlockMeta) : BlockMeta :=
  { first := ⟨freshNat b.first.c0, freshNat b.first.c1, freshNat b.first.c2, freshNat b.first.g⟩,
    last := ⟨freshNat b.last.c0, freshNat b.last.c1, freshNat b.last.c2, freshNat b.last.g⟩,
    rows := freshNat b.rows, offset := freshNat b.offset, len0 := freshNat b.len0,
    len1 := freshNat b.len1, len2 := freshNat b.len2, len3 := freshNat b.len3 }

/-- The PRM1 entries of block range `X` copied for the task that scans it,
    and the range's positions in the copy (stage 1h). The task makes the copy:
    the entries of the session's array are reachable from every task, so each
    block's `metas[i]!` and the functions that take the entry took and dropped
    references atomically (DBpedia d10 at 4 threads: in `cutCol`,
    `frameSpan`, `frameStarts`, `keyRange` and `blockChunk`). The scan reads
    an entry only through its position (`IdQuery.scanBlockM`,
    `IdQuery.scanBlockSipM`), so `metas` at `X` and the copy at
    `0, ..., |X| - 1` give the same scan. -/
def rangeMetas (metas : Array BlockMeta) (X : List Nat) : Array BlockMeta × List Nat :=
  (X.foldl (fun a i => a.push (freshMeta metas[i]!)) (Array.mkEmpty X.length), List.range X.length)


/-- The fewest estimated rows per range of a divided BGP scan on the worker
    pool (issue 961): `minRows / 2` (4,096 by default), so that olympics
    q07's first two scans (8,192 and 16,384 estimated rows) are divided. -/
def poolScanRows (minRows : Nat) : Nat := minRows / 2

/-- The job of one block range of a divided scan (`scanTableParM`,
    `startScanTablePar`): its own copies of the spec, the overlay context, the
    PRM1 entries of the range and the empty table, then the loop of
    `IdQuery.scanListM`. A function of its own, called by the job: when the
    job was a `do` block written in the caller's loop, the compiler moved its
    pure steps (`ScanSpec.fresh`, `OvCtx.fresh`, `rangeMetas`, and in
    `sipRangeJob` the copy of the candidates) out of the job into the calling
    thread (stage 1o, read from the generated C). The calling thread then
    made every task's copies before it scanned its own range (olympics q07 at
    4 threads: each task started 9 to 18 microseconds after the one before),
    and the copies, reached by the job, were shared objects whose reference
    counts are atomic, which is what the copies are there to avoid. -/
@[noinline] def scanRangeJob (v : Session) (spec : IdQuery.ScanSpec) (ox : IdQuery.OvCtx)
    (metas : Array BlockMeta) (X : Nat × Nat) : IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats) := do
  -- stage 1b: the task's own copies of the spec, the overlay context and
  -- the empty table (`IdQuery.ScanSpec.fresh`; `ScanSpec.fresh_eq` says
  -- the copy is equal to `spec`, the spec of `ParallelScanTheorems`). The
  -- parent's spec is reachable from every task, and reading it in every
  -- block cost atomic reference counts on shared cache lines; the
  -- parent's empty table had the capacity of the whole scan, and each
  -- task's first append copied it at that capacity.
  let spec := spec.fresh
  let ox := ox.fresh spec.key
  let sortVar := IdQuery.sortVarOf spec
  let (metasX, posX) := rangeMetas metas (L4Factoidal.Storage.Sbm11.ParallelScan.boundsList X)
  let capX := 8 * metasX.foldl (fun a b => a + b.rows) 0
  let init : L4Factoidal.Qlvr.Table :=
    { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity capX,
      rows := 0, sortVar }
  let f := fun (acc : L4Factoidal.Qlvr.Table) (ch : IdQuery.Chunk) =>
    (pure (acc.append ch.table, true) : ExceptT String IO (L4Factoidal.Qlvr.Table × Bool))
  match ← (IdQuery.scanListM v.store spec true init f metasX sortVar ox posX).run with
  | .ok r => pure r
  | .error e => throw (IO.userError e)

/-- The job of one block range of the scan with candidates
    (`scanSipTableParM`): `scanRangeJob` with the task's own copy of the
    candidates and the loop of `IdQuery.scanListSipM`. -/
@[noinline] def sipRangeJob (v : Session) (spec : IdQuery.ScanSpec) (ox : IdQuery.OvCtx) (candBytes : ByteArray)
    (nCands : Nat) (metas : Array BlockMeta) (X : Nat × Nat) : IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats) := do
  let spec := spec.fresh
  let ox := ox.fresh spec.key
  let cands := IdQuery.unpackWords candBytes nCands
  let (metasX, posX) := rangeMetas metas (L4Factoidal.Storage.Sbm11.ParallelScan.boundsList X)
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  let init : L4Factoidal.Qlvr.Table :=
    { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.empty,
      rows := 0, sortVar := IdQuery.sortVarOf spec }
  let f := fun (acc : L4Factoidal.Qlvr.Table) (ch : IdQuery.Chunk) =>
    (pure (acc.append ch.table, true) : ExceptT String IO (L4Factoidal.Qlvr.Table × Bool))
  match ← (IdQuery.scanListSipM v.store spec cands init f metasX sortVar ox posX).run with
  | .ok r => pure r
  | .error e => throw (IO.userError e)

/-- The table of `IdQuery.scanTableM`, computed with the selected blocks cut
    into at most `threads` consecutive chunks. The first chunk is scanned by
    the calling thread, each other one by its own task (`IO.asTask`), with
    the same loop (`IdQuery.scanListM`); the chunk tables are appended in
    chunk order and
    the statistics are summed. A scan with an overlay (stage 5) stays on one
    thread. Answers: `ParallelScanTheorems.parallel_acc_eq` (the list form),
    tests/sbm11/threads.sh (the tables, native). -/
def scanTableParM (ss : Session) (spec : IdQuery.ScanSpec) (threads : Nat) (minRows : Nat := 8192) :
    ExceptT String IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats) := do
  let st := ss.store
  -- the selected blocks' PRM1 entries (issue 805); a chunk is a list of
  -- positions in that array
  let metas ← st.blocksForRange spec.perm spec.key
  let ox := IdQuery.ovCtx (st.ovl spec.perm) spec.key
  -- stage 1b: at most `IdQuery.rangeCount` ranges; fewer than 2: one thread.
  -- Stage 1f: at least `2 * minRows` rows per range (16,384 by default).
  -- Olympics q07's second scan (16,384 estimated rows, 4 blocks, 0.22 ms on
  -- one thread) took 0.37 to 0.47 ms at 4 threads in 2 ranges and 0.24 to
  -- 0.28 ms in one: a range waits for a sleeping worker (50 to 120
  -- microseconds on the test machine) and the parent appends the tables.
  -- issue 961: on the worker pool a range costs microseconds, not a wake-up
  let n := IdQuery.rangeCount threads (if ss.pool.isSome then poolScanRows minRows else 2 * minRows)
    (IdQuery.selRows metas)
  if threads ≤ 1 || ox.on || n < 2 then return ← IdQuery.scanTableM st spec
  let sortVar := IdQuery.sortVarOf spec
  let c := (metas.size + n - 1) / n
  -- the ranges as bounds (`ParallelScan.rangeBounds_map`): a task makes the
  -- list of its positions (`boundsList`), so no list the parent frees was
  -- reachable from a task (stage 1k)
  let chunks := L4Factoidal.Storage.Sbm11.ParallelScan.rangeBounds c metas.size
  let cap := 8 * IdQuery.selRows metas
  let init : L4Factoidal.Qlvr.Table :=
    { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity cap,
      rows := 0, sortVar }
  let f := fun (acc : L4Factoidal.Qlvr.Table) (ch : IdQuery.Chunk) =>
    (pure (acc.append ch.table, true) : ExceptT String IO (L4Factoidal.Qlvr.Table × Bool))
  -- each task: its own view (counters, dictionary state, permutation copies).
  -- Stage 1f: the first range is scanned by the calling thread after the
  -- tasks of the others have started (it would otherwise wait for them).
  let mut tasks : Array (Harness.WorkerPool.Handle (Except IO.Error (L4Factoidal.Qlvr.Table × IdQuery.ScanStats)) × Session) := #[]
  for X in chunks.drop 1 do
    let v ← ss.view
    let t ← ss.spawnAt tasks.size (scanRangeJob v spec ox metas X)
    tasks := tasks.push (t, v)
  let mut out := init
  let mut stats : IdQuery.ScanStats := { blocksTotal := ← st.blockCount spec.perm }
  let mut failure : Option String := none
  -- the first range, onto `init` (the capacity of the whole scan)
  match ← liftIO (IdQuery.scanListM st spec true init f metas sortVar ox (L4Factoidal.Storage.Sbm11.ParallelScan.boundsList (chunks.headD (0, 0)))).run with
  | Except.ok (tab, s) =>
    out := tab
    stats := stats.add s
  | Except.error e => failure := some e
  for (t, v) in tasks do
    match ← liftIO (ss.await t) with
    | .ok (tab, s) =>
      out := out.append tab
      stats := stats.add s
    | .error e => if failure.isNone then failure := some (toString e)
    -- the counters of every task are added, failed or not
    ss.absorb v
  if let some e := failure then throw e
  return (out, stats)

/-! ## The next scan started early (stage 1o) -/

/-- Two scan specs that ask for the same table. -/
def specSame (a b : IdQuery.ScanSpec) : Bool :=
  a.perm == b.perm && a.key == b.key && a.checks == b.checks && a.named == b.named &&
    a.outVars == b.outVars && a.outCols == b.outCols && a.eqs == b.eqs

/-- The scan started early by `IdQuery.Par.scanHint` (stage 1o): its spec and
    the action that waits for its table. One query at a time per process; the
    store's `scanTable` takes it (`Session.storeWith`). -/
initialize prescanSlot : IO.Ref (Option (IdQuery.ScanSpec ×
    ExceptT String IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats))) ← IO.mkRef none

/-- Start the table of `IdQuery.scanTableM` for `spec` on the pool workers
    `ws` (none of it on the calling thread): the selected blocks in at most
    `ws.length` consecutive ranges (`ParallelScan.rangeBounds`), range `k` a
    job of worker `ws[k]` with the loop of `scanTableParM`. The action
    returned waits for the ranges in order, appends their tables and adds
    their statistics and counters: the table and statistics of
    `scanTableParM` (`ParallelScanTheorems.parallel_acc_eq`: any cut of the
    selected blocks into consecutive ranges gives the single scan's table).

    `none`, and nothing started, unless the generation is read with
    `verify none`, the scan has no delta overlay, and the PRM1 entries of its
    key are in the permutation's range cache: a started scan that the query
    does not use (the hint named another scan) then reads no PRM1 entry and
    fills no shared cache, so the counters of the query equal those of one
    thread (tests/sbm11/threads.sh compares them). -/
def startScanTablePar (ss : Session) (spec : IdQuery.ScanSpec) (ws : List Nat) (minRows : Nat) :
    ExceptT String IO (Option (ExceptT String IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats))) := do
  if ss.g.verify != .none || ws.isEmpty then return none
  let lp ← liftIO (ss.perm spec.perm)
  let some metas := MemoCache.find? (← liftIO lp.ranges.get) spec.key | return none
  let st := ss.store
  let ox := IdQuery.ovCtx (st.ovl spec.perm) spec.key
  if ox.on || metas.isEmpty then return none
  let n := max 1 (min ws.length (IdQuery.rangeCount ws.length (poolScanRows minRows) (IdQuery.selRows metas)))
  let c := (metas.size + n - 1) / n
  let chunks := L4Factoidal.Storage.Sbm11.ParallelScan.rangeBounds c metas.size
  let wsA := ws.toArray
  let mut tasks : Array (Harness.WorkerPool.Handle (Except IO.Error (L4Factoidal.Qlvr.Table × IdQuery.ScanStats)) × Session) := #[]
  for X in chunks do
    let v ← liftIO ss.view
    let t ← liftIO (ss.spawnAt (wsA[tasks.size]?.getD 0) (scanRangeJob v spec ox metas X))
    tasks := tasks.push (t, v)
  let handles := tasks
  let total := lp.count
  let cap := 8 * IdQuery.selRows metas
  return some (do
    let mut out : L4Factoidal.Qlvr.Table :=
      { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity cap,
        rows := 0, sortVar := IdQuery.sortVarOf spec }
    let mut stats : IdQuery.ScanStats := { blocksTotal := total }
    let mut failure : Option String := none
    for (t, v) in handles do
      match ← liftIO (ss.await t) with
      | .ok (tab, s) =>
        out := out.append tab
        stats := stats.add s
      | .error e => if failure.isNone then failure := some (toString e)
      liftIO (ss.absorb v)
    if let some e := failure then throw e
    return (out, stats))

/-- `IdQuery.Par.scanHint` on the session's worker pool: the hinted scan
    started on the last pool workers (the first scan's ranges take the first
    ones, `scanTableParM`), at most `size - 1` of them, at least one. A scan
    started for an earlier hint and not taken is dropped (its jobs end on
    their own; their counters are not added). -/
def scanHintPar (ss : Session) (minRows : Nat) (spec : IdQuery.ScanSpec) : IO Unit := do
  let _ ← prescanSlot.swap none
  let some p := ss.pool | return
  let k := max 1 (p.size - 1)
  let ws := (List.range k).map fun i => p.size - 1 - i
  match ← (startScanTablePar ss spec ws minRows).run with
  | .ok (some w) => prescanSlot.set (some (spec, w))
  | _ => pure ()

/-- The store's `scanTable` with the scan started early: the started scan's
    table when it is for `spec`, else `scanTableParM` (a started scan for
    another spec stays for a later scan, and is dropped at the next hint or
    query). -/
def scanTableOrStarted (ss : Session) (spec : IdQuery.ScanSpec) (threads minRows : Nat) :
    ExceptT String IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats) := do
  -- the slot is read and written by the calling thread only
  match ← liftIO prescanSlot.get with
  | some (sp, w) =>
    if specSame sp spec then
      liftIO (prescanSlot.set none)
      w
    else scanTableParM ss spec threads minRows
  | none => scanTableParM ss spec threads minRows

/-- The scan with candidates (`IdQuery.scanSipTableM`) in block ranges, one
    task per range after the first, which the calling thread scans (issue
    799, KR 1.2; stage 1f): the tasks of `scanTableParM` with
    `IdQuery.scanListSipM`, their tables appended in range order and their
    statistics added. A scan with a delta overlay, fewer than two ranges
    (`IdQuery.rangeCount`) or one selected block runs `scanSipTableM` on the
    calling thread. Each task has its own copy of the candidates (a value the
    tasks share costs atomic reference counts, section "Values that two threads
    can reach" of `skills/lean4-performance`). -/
def scanSipTableParM (ss : Session) (spec : IdQuery.ScanSpec) (cands : Array UInt64) (threads : Nat)
    (minRows : Nat := 8192) : ExceptT String IO (L4Factoidal.Qlvr.Table × IdQuery.ScanStats) := do
  let st := ss.store
  let metas ← st.blocksForRange spec.perm spec.key
  let ox := IdQuery.ovCtx (st.ovl spec.perm) spec.key
  let n := IdQuery.rangeCount threads minRows (IdQuery.selRows metas)
  if threads ≤ 1 || ox.on || n < 2 || metas.size < 2 then return ← IdQuery.scanSipTableM st spec cands
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  -- stage 1m: the ranges cut at about equal estimated work, not at equal
  -- block counts. A block that the PRM1 entry or the candidates rule out
  -- (`selects`, `sipRange`, `Sip.mayHold`) costs about 1 microsecond, a block
  -- that is read 30 to 50; with equal block counts the largest of olympics
  -- q07's four ranges held 1.12 to 1.20 times the mean of the join-key values
  -- tested. The weight of a block is its rows when it is read, else 0
  -- (`ParallelScan.weightCuts`). The ranges are bounds of consecutive
  -- positions; any cut points give ranges whose concatenation is the
  -- selected blocks (`ParallelScan.cutBounds_flatten`,
  -- `ParallelSipTheorems.parallel_sip_acc_eq_cut`). A task makes the list of
  -- its positions (`boundsList`), so no list the parent frees was reachable
  -- from a task (stage 1k).
  let jc := spec.key.size
  let ws := metas.map fun b =>
    if !IdQuery.selects b spec.key then 0
    else
      let (vlo, vhi) := IdQuery.sipRange b spec.key jc
      if Sip.mayHold cands vlo vhi (Sip.lbHint cands vlo) then b.rows else 0
  let chunks := L4Factoidal.Storage.Sbm11.ParallelScan.cutBounds metas.size
    (L4Factoidal.Storage.Sbm11.ParallelScan.weightCuts ws n)
  let init : L4Factoidal.Qlvr.Table :=
    { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.empty,
      rows := 0, sortVar := IdQuery.sortVarOf spec }
  let f := fun (acc : L4Factoidal.Qlvr.Table) (ch : IdQuery.Chunk) =>
    (pure (acc.append ch.table, true) : ExceptT String IO (L4Factoidal.Qlvr.Table × Bool))
  -- Stage 1f: the first range is scanned by the calling thread after the
  -- tasks of the others have started. Olympics q07 at 4 threads (41 runs per
  -- process, 3 processes): the two scans with candidates took 1.08 to 1.14
  -- and 0.76 to 0.78 ms with a task per range, 0.81 to 0.85 and 0.62 ms so.
  let candBytes := IdQuery.packWords cands
  let mut tasks : Array (Harness.WorkerPool.Handle (Except IO.Error (L4Factoidal.Qlvr.Table × IdQuery.ScanStats)) × Session) := #[]
  for X in chunks.drop 1 do
    let v ← ss.view
    let t ← ss.spawnAt tasks.size (sipRangeJob v spec ox candBytes cands.size metas X)
    tasks := tasks.push (t, v)
  let mut out := init
  let mut stats : IdQuery.ScanStats := { blocksTotal := ← st.blockCount spec.perm }
  let mut failure : Option String := none
  match ← liftIO (IdQuery.scanListSipM st spec cands init f metas sortVar ox (L4Factoidal.Storage.Sbm11.ParallelScan.boundsList (chunks.headD (0, 0)))).run with
  | Except.ok (tab, s) =>
    out := tab
    stats := stats.add s
  | Except.error e => failure := some e
  for (t, v) in tasks do
    match ← liftIO (ss.await t) with
    | .ok (tab, s) =>
      out := out.append tab
      stats := stats.add s
    | .error e => if failure.isNone then failure := some (toString e)
    ss.absorb v
  if let some e := failure then throw e
  return (out, stats)

/-- `IdQuery.Par.fold` on this session (issue 799, stage 1b; workers from
    KR 1.2 of batch 3). At most `nWorkers` worker tasks, started once per
    fold.
    Each worker has its own view of the session (`Session.view`, then
    `Session.local` in the worker: counters, permutation copies and a page
    cache that it keeps for all its ranges) and takes the next range from a
    shared counter, so the ranges are taken in range order. The parent folds
    the results with `g` in range order. Range `k` starts only after range
    `k - window` is folded (a permit per range), so at most `window` ranges
    are running or wait in memory (`parWindowFactor`). The counters of every worker are
    added (`Session.absorb`), failed or not; after a failure the workers
    finish the ranges they hold and take no new work.

    The first version started one task per range, each with a new view and an
    empty page cache. With the streamed path's ranges of one block
    (`IdQuery.streamRangeBlocks`), every block filled a new cache from
    `taskPages` under `dictLock`: olympics q19 at 4 threads spent 1.5 times
    the CPU time of 1 thread, most of the extra in `copyPage` (`memmove`),
    lock waits and fresh memory. -/
def parFold (ss : Session) (nWorkers window : Nat) (fixed : Bool := false) {α β γ : Type} [Inhabited γ]
    (job : IdQuery.Store IO → γ → ExceptT String IO α) (chunks : List γ) (init : β)
    (g : β → α → ExceptT String IO β) : ExceptT String IO β := do
  let arr := chunks.toArray
  let n := arr.size
  if n == 0 then return init
  let w := max window 1
  let poolOnly := (← liftIO (IO.getEnv "SBM11_POOLONLY")).isSome
  let trace := (← liftIO (IO.getEnv "SBM11_RANGE_TRACE")).isSome
  let nW := match ss.pool with
    | some p => if poolOnly && p.size > 0 then min nWorkers p.size else nWorkers
    | none => nWorkers
  let nwk := min (max nW 1) n
  -- stage 1j: with a pool of fewer threads than workers, the calling thread
  -- is the last worker (its jobs run between the folds of the results, with
  -- the session's own store and page cache), not a task of the Lean pool
  -- with a new page cache for each fold
  let parentTask := (← liftIO (IO.getEnv "SBM11_PARENT_TASK")).isSome
  let parentAt : Option Nat := match ss.pool with
    | some p => if p.size > 0 && nwk > p.size && !parentTask then some p.size else none
    | none => none
  let nSpawn := match parentAt with
    | some j => j
    | none => nwk
  -- a range's result goes to its slot, then its promise is resolved; the
  -- parent takes the result out of the slot, so a folded result is freed (a
  -- resolved promise keeps its value while the promise is reachable)
  let slots ← liftIO (arr.mapM fun _ => (IO.mkRef none : IO (IO.Ref (Option (Except String α)))))
  let results ← liftIO (arr.mapM fun _ => (IO.Promise.new : IO (IO.Promise Unit)))
  let permits ← liftIO (arr.mapM fun _ => (IO.Promise.new : IO (IO.Promise Unit)))
  let permit (k : Nat) : IO Unit := match permits[k]? with
    | some p => p.resolve ()
    | none => pure ()
  let resolveAt (k : Nat) (r : Except String α) : IO Unit := do
    if let some c := slots[k]? then c.set (some r)
    if let some p := results[k]? then p.resolve ()
  for k in [0:min w n] do liftIO (permit k)
  let next ← liftIO (IO.mkRef (0 : Nat))
  let stop ← liftIO (IO.mkRef false)
  let fx := fixed && (← liftIO (IO.getEnv "SBM11_DYNAMIC")).isNone
  let runJob (st : IdQuery.Store IO) (j k : Nat) : IO Unit := do
    if ← stop.get then
      resolveAt k (.error "a range before this one failed")
    else
      let t0 ← IO.monoNanosNow
      match ← ((job st arr[k]!).run).toBaseIO with
      | .ok r => resolveAt k r
      | .error e => resolveAt k (.error (toString e))
      if trace then
        let t1 ← IO.monoNanosNow
        IO.eprintln s!"range-trace: job {k} worker {j} start {t0} us {(t1 - t0) / 1000}"
  let mut workers : Array (Harness.WorkerPool.Handle (Except IO.Error Unit) × Session) := #[]
  for j in [0:nSpawn] do
    let v ← liftIO ss.view
    let t ← liftIO (ss.spawnLocal workers.size (fun wp => do
      -- issue 981: an error of the worker's setup still resolves every range
      -- the worker takes (with the error), so the calling thread, which waits
      -- for each range in order, never waits for a range that no one runs
      let lvE ← (do
        let lim := ((← IO.getEnv "SBM11_WORKER_PAGES").bind String.toNat?).getD workerPageLimit
        match wp with
        | some r => pure { (← v.withPages r) with taskPageLimit := min v.pageLimit lim }
        | none => v.local : IO Session).toBaseIO
      for i in [0:n] do
        let k ← if fx then pure (j + i * nwk) else next.modifyGet fun k => (k, k + 1)
        if k ≥ n then break
        if let some p := permits[k]? then
          let _ ← IO.wait p.result?
        match lvE with
        | .ok lv => runJob lv.store j k
        | .error e => resolveAt k (.error s!"block range {k}: its worker did not start: {e}")))
    workers := workers.push (t, v)
  -- the calling thread's next job (`parentAt`): in fixed order its ranges
  -- `j, j + nwk, ...`; else the next range of the shared counter. It takes a
  -- range only when that range's permit is given (below `k + w`, `k` the
  -- next range to fold), so it never waits for itself.
  let pst := ss.store
  let mut mine : Nat := parentAt.getD 0
  let mut acc := init
  let mut failure : Option String := none
  for k in [0:n] do
    if let some j := parentAt then
      let mut go := true
      while go do
        -- the promise, not the slot: `IO.Ref.get` on a ref that another
        -- thread writes takes the value out and puts it back, so a write
        -- between the two is lost (the runtime's `lean_st_ref_get`); a get
        -- here lost a range's result about once in 4,000 folds ("its worker
        -- stopped", then a hang at exit with the pool still running)
        let ready ← match results[k]? with
          | some p => liftIO (IO.hasFinished p.result?)
          | none => pure true
        if ready then go := false
        else
          let lim := min n (k + w)
          let mk ← if fx then pure (if mine < lim then some mine else none)
            else liftIO (next.modifyGet fun i => if i < lim then (some i, i + 1) else (none, i))
          match mk with
          | some i =>
            liftIO (runJob pst j i)
            if fx then mine := mine + nwk
          | none => go := false
    if let some p := results[k]? then
      let _ ← liftIO (IO.wait p.result?)
    let r : Option (Except String α) ← match slots[k]? with
      | some c => liftIO (c.swap none)
      | none => pure none
    match r with
    | some (.ok a) =>
      if failure.isNone then
        match ← liftIO (g acc a).run with
        | .ok b => acc := b
        | .error e => failure := some e
    | some (.error e) => if failure.isNone then failure := some e
    | none => if failure.isNone then failure := some s!"block range {k}: its worker stopped"
    -- `modify`, not `set`: the workers read `stop` with `get`, and a `set`
    -- between the two exchanges of a `get` is lost (issue 981,
    -- `Harness.WorkerPool` module comment)
    if failure.isSome then liftIO (stop.modify fun _ => true)
    liftIO (permit (k + w))
  for (t, v) in workers do
    match ← liftIO (ss.await t) with
    | .ok () => pure ()
    | .error e => if failure.isNone then failure := some (toString e)
    liftIO (ss.absorb v)
  if let some e := failure then throw e
  return acc

/-- The ranges that may run or wait in memory, per worker, in `parFold`, for a
    bounded fold (`IdQuery.Par.fold`; the streamed path). An unbounded fold
    (small results) gives every range a permit at once, so a worker does
    not wait for the parent between ranges. With one range per worker, a worker that finished its range waited until the
    parent had written the range before it, the slowest of the window: olympics
    at 4 threads (KR 1.2 of batch 3, 21 runs per process), q19 19.0 ms against
    15.2 ms with 2 per worker, q21 37.0 ms against 28.9 ms; peak RSS 112 and 81
    MB against 119 and 88 MB (1 thread: 69 and 53 MB). -/
def parWindowFactor : Nat := 2

/-- `xs.map f` with `f` of the first element computed by the calling thread
    and of element `i ≥ 1` by worker `i - 1` of the pool (issue 961;
    `IdQuery.Par.mapList`). `IO.lazyPure` puts the call of `f` inside the
    job: `pure (f y)` would compute it on the calling thread. -/
def poolMap {α β : Type} (p : Harness.WorkerPool.Pool WorkerPages) (f : α → β) (xs : List α) : IO (List β) := do
  match xs with
  | [] => return []
  | x :: rest =>
    let mut hs := #[]
    for y in rest do
      hs := hs.push (← p.spawnOn hs.size (IO.lazyPure fun _ => f y))
    let a := f x
    let mut out := #[a]
    for h in hs do
      match ← h.await p.spinNs with
      | .ok b => out := out.push b
      | .error e => throw e
    return out.toList

/-- `IdQuery.Par.renderStart` on the session's worker pool (stage 1o of
    docs/designissues/2026-10-12-parallel-block-scans.md, issue 961): range
    `j` of the rows is rendered by pool worker `j` (`IdQuery.renderPartM` on a
    view with the worker's own page cache, pages copied on first use), so a
    worker renders the same rows, with the same pages, in every run of a
    query. Each job gets its rows as a table that the calling thread copied
    for it (`Table.slice`) and its own copy of the variable names: the
    calling thread's table and names stay single-threaded objects, and no
    column's reference count is shared by two threads. A job's store decodes
    the query-local ids of `vocab` (`IdQuery.Store.withLocal`; a VALUES term
    with no id in the generation). The action returned waits for the rows in
    range order and adds the counters of every view. -/
def renderStartPar (ss : Session) (vocab : Array Term) (t : L4Factoidal.Qlvr.Table) (vars : Array String) (reference : Bool)
    (rs : List (Nat × Nat)) : ExceptT String IO (ExceptT String IO (List (Array ByteArray))) := do
  let mut hs : Array (Harness.WorkerPool.Handle (Except IO.Error (Array ByteArray)) × Session) := #[]
  for r in rs do
    -- the job's rows: `renderPartM` slices `t`; the slice is made here, by
    -- the calling thread, so that the job does not reach `t`
    let part := t.slice r.1 r.2
    let v ← liftIO ss.view
    let h ← liftIO (ss.spawnLocal hs.size (fun wp => do
      let lv ← match wp with
        | some r => do
          let w ← v.withPages r
          pure { w with copyFirst := true }
        | none => v.local
      let names := vars.map IdQuery.freshStr
      -- `IdQuery.renderPartM (lv.store.withLocal vocab) reference t names r`, with the slice
      -- made by the calling thread
      match ← (IdQuery.renderRowsListM (lv.store.withLocal vocab) reference part names 0 part.rows).run with
      | .ok r => pure r
      | .error e => throw (IO.userError e)))
    hs := hs.push (h, v)
  let handles := hs
  return (do
    let mut out : Array (Array ByteArray) := Array.mkEmpty handles.size
    let mut failure : Option String := none
    for (h, v) in handles do
      match ← liftIO (ss.await h) with
      | .ok r => out := out.push r
      | .error e => if failure.isNone then failure := some (toString e)
      liftIO (ss.absorb v)
    if let some e := failure then throw e
    return out.toList)

/-- The fewest input rows per range of a divided merge join on the worker
    pool (issue 961): a job starts within microseconds, so ranges can be
    smaller than with tasks of the Lean pool (`IdQuery.joinMinRows`). -/
def poolJoinRows : Nat := 4096

/-- The divided single-pattern paths of `IdQuery.runPlanM` with `threads`
    tasks at once (issue 799, stage 1b). -/
def Session.par (ss : Session) (threads : Nat) (minRows : Nat := 8192) : IdQuery.Par IO :=
  { threads, minRows,
    fold := fun bounded job chunks init g =>
      parFold ss threads (if bounded then parWindowFactor * threads else chunks.length) bounded job chunks init g
    mapList := ss.pool.map fun p => fun f xs => poolMap p f xs
    joinRows := if ss.pool.isSome then poolJoinRows else IdQuery.joinMinRows
    joinShare := ss.joinShare
    renderRows := ss.renderRows
    streamPerThread := ss.streamPerThread
    renderStart := ss.pool.map fun _ => renderStartPar ss
    sortedRows := ss.sortedRows
    scanHint := ss.pool.map fun _ => scanHintPar ss minRows }

/-- `SBM11_MIN_RANGE_ROWS`: the fewest estimated rows per block range
    (`IdQuery.rangeCount`; default 8,192; 0: one range per thread, as the
    gate fixture tests use to divide scans of a few rows). -/
def minRangeRows : IO Nat := do
  return ((← IO.getEnv "SBM11_MIN_RANGE_ROWS").bind String.toNat?).getD 8192

/-- The session's store with `threads` scan tasks per BGP scan (1: the
    single-thread store, `scanTable` unset). -/
def Session.storeWith (ss : Session) (threads : Nat) (sip : Option Nat := some 16) (minRows : Nat := 8192)
    (aggOnIds : Bool := true) : IdQuery.Store IO :=
  let base := { ss.store with sipFactor := sip, aggOnIds := aggOnIds }
  if threads ≤ 1 then base
  else { base with scanTable := some fun spec => scanTableOrStarted ss spec threads minRows,
                   scanSipTable := some fun spec cands => scanSipTableParM ss spec cands threads minRows }


/-! ## The delta overlay (stage 5)

The replay is the library's (`QuerySession.replay`, `Core.stepEntry`,
`Core.prefillBaseIds`, `Core.idOrNew`); the methods below call it. -/

/-- The id of `t`: its base id, its overlay id, or a new overlay id. -/
def Session.idOrNew (ss : Session) (t0 : Term) : IO Nat := ss.toCore.idOrNew t0

/-- A graph name of a DLOG entry as a term: an IRI or a blank node. -/
abbrev graphTerm : L4Factoidal.Storage.DeltaGraphName → IO Term := QuerySession.graphTerm

def Session.graphIdOrNew (ss : Session) (g : Option L4Factoidal.Storage.DeltaGraphName) : IO Nat :=
  ss.toCore.graphIdOrNew g

/-- The id of a quad when every term has an id (a quad with a term that has
    no id is in no generation). -/
def Session.quadIds? (ss : Session) (t : Triple) (g : Option L4Factoidal.Storage.DeltaGraphName) :
    IO (Option Row) := ss.toCore.quadIds? t g

/-- `SBM11_REPLAY_LOOKUP=each`: the replay looks every occurrence of every term
    up in the dictionary on its own, as it did before issue 858. The oracle of
    the differential test (group `replay` of tests/sbm11/update_where.sh); not
    for use otherwise. -/
def replayEach : IO Bool := do
  return (← IO.getEnv "SBM11_REPLAY_LOOKUP") == some "each"

/-- The terms that `stepEntry` maps to ids for the entry `e`. -/
abbrev entryTerms : L4Factoidal.Storage.DeltaEntry → List Term := QuerySession.entryTerms

/-- Look the distinct terms of the entries that `forEach` gives up in the
    dictionary, in dictionary order, and keep their ids in `baseIds`
    (`QuerySession.Core.prefillBaseIds`, issue 858). -/
def Session.prefillBaseIds (ss : Session) (entries : Nat)
    (forEach : (L4Factoidal.Storage.DeltaEntry → IO Unit) → IO Unit) : IO Nat := do
  ss.toCore.prefillBaseIds (← replayEach) entries forEach

/-- One log entry applied to an overlay state (`QuerySession.Core.stepEntry`). -/
def Session.stepEntry (ss : Session) (st : L4Factoidal.Storage.Sbm11.Overlay.State)
    (e : L4Factoidal.Storage.DeltaEntry) : IO L4Factoidal.Storage.Sbm11.Overlay.State :=
  ss.toCore.stepEntry st e

/-- The distinct graph ids other than the default graph (0) of the BASE quads,
    sorted (`QuerySession.baseGraphIdsOfQuads`). -/
def Session.baseGraphIdsOfQuads (ss : Session) : IO (Array Nat) := QuerySession.baseGraphIdsOfQuads ss

/-- The named graphs of the base generation (`QuerySession.baseNamed`). -/
def Session.baseNamed (ss : Session) : IO (Array Nat) := QuerySession.baseNamed ss

/-- Does the named graph with id `x` exist in the overlaid generation? -/
def Session.hasNamedGraph (ss : Session) (x : Nat) : IO Bool := QuerySession.hasNamedGraph ss x

/-- The ids of the named graphs of the overlaid generation, sorted. -/
def Session.namedGraphIds (ss : Session) : IO (Array Nat) := QuerySession.namedGraphIds ss

/-- `storeWith` with the named graphs of the overlaid generation
    (`namedGraphIds`), which the nested evaluator reads for GRAPH
    (https://github.com/danbri/factoidal/issues/959). -/
def Session.storeNested (ss : Session) (threads : Nat) (sip : Option Nat := some 16) (minRows : Nat := 8192)
    (aggOnIds : Bool := true) : IdQuery.Store IO :=
  QuerySession.withNamedGraphs ss (ss.storeWith threads sip minRows aggOnIds)

/-- The session with the overlay state `st` (`QuerySession.withOverlay`). -/
def Session.withOverlay (ss : Session) (st : L4Factoidal.Storage.Sbm11.Overlay.State) : IO Session :=
  QuerySession.withOverlay ss st

/-- Replay the committed batches of the generation's delta log
    (`Sbm11Delta.readBatches`) into the overlay (`QuerySession.replay`). -/
def Session.loadOverlay (ss : Session) : IO Session := do
  let t0 ← IO.monoNanosNow
  let (batches, logBytes, clean) ← Harness.Sbm11Delta.readBatches ss.g.dir
  QuerySession.replay ss batches logBytes.size clean (← replayEach) (some t0)

/-- Open a generation with its delta log replayed (the session every query,
    serve and compaction uses). -/
def openOverlaid (v : Verify) (dir0 : String) : IO Session := do
  (← openSession v dir0).loadOverlay

/-- The limit as text: `5 entries`, `100 bytes`, `5 entries and 100 bytes`. -/
def limitText (l : L4Factoidal.Storage.Sbm11.OverlayLimit.Limit) : String :=
  match l.maxEntries, l.maxBytes with
  | some e, some b => s!"{e} entries and {b} bytes"
  | some e, Option.none => s!"{e} entries"
  | Option.none, some b => s!"{b} bytes"
  | Option.none, Option.none => "none"

/-- A size limit from the environment variable `name`: unset or empty is no
    limit; a decimal number is that limit; anything else is an error. -/
def limitFromEnv (name : String) : IO (Option Nat) := do
  match ← IO.getEnv name with
  | Option.none => return Option.none
  | some "" => return Option.none
  | some v =>
    match v.toNat? with
    | some n => return some n
    | Option.none => throw (IO.userError s!"{name}={v}: not a decimal number")

/-- The log size limit set by `SBM11_MAX_OVERLAY_ENTRIES` and
    `SBM11_MAX_OVERLAY_BYTES` (both off when unset). `l4sbm11 update` takes the
    flags `--max-overlay-entries` and `--max-overlay-bytes` in their place;
    `l4sbm11 serve` reports whether the log it opened is within it. -/
def overlayLimitFromEnv : IO L4Factoidal.Storage.Sbm11.OverlayLimit.Limit := do
  return { maxEntries := ← limitFromEnv "SBM11_MAX_OVERLAY_ENTRIES",
           maxBytes := ← limitFromEnv "SBM11_MAX_OVERLAY_BYTES" }

/-- The size of the overlay of an opened generation, for `serve`: the entries
    and bytes of its log, what the replay made of them, and where that stands
    against the limit. -/
def Session.overlayText (ss : Session) (lim : L4Factoidal.Storage.Sbm11.OverlayLimit.Limit) : String :=
  let state :=
    if !lim.isSet then "no limit set"
    else if lim.exceeded ss.deltaOps ss.ovLogBytes then
      s!"over the limit of {limitText lim}: run l4sbm11 compact and l4sbm11 activate to fold the log"
    else s!"within the limit of {limitText lim}"
  s!"overlay size: {ss.deltaOps} log entries in {ss.deltaBatches} batches, {ss.ovLogBytes} bytes of log, {ss.ovInserts} inserted quads, {ss.ovDeletes} deleted quads, {ss.ovNewTerms} new terms; {state}"

def Session.deltaText (ss : Session) : String :=
  s!"delta batches {ss.deltaBatches}, entries {ss.deltaOps}, overlay inserts {ss.ovInserts}, deletes {ss.ovDeletes}, cleared graphs {ss.ovCleared}, new terms {ss.ovNewTerms}, log bytes {ss.ovLogBytes}, dictionary terms looked up {ss.replayTerms}, replay ms {ms 0 ss.replayNs}" ++
    (if ss.deltaTorn then ", torn final frame left out (an append that did not complete)" else "")

/-! ## The reference fallback (`QuerySession.selectedDataset`, `runReference`) -/

/-- Every row of permutation `perm` with key prefix `key`, all graphs. -/
def scanAll (ss : Session) (perm : Nat) (key : Array UInt64)
    (f : Array ByteArray → Nat → IO Unit) : IO Unit :=
  QuerySession.scanAll ss perm key f

abbrev subjectOf (t : Term) : IO Subject := QuerySession.subjectOf t

/-- The quads the planner guard selects, as the dataset they denote
    (`QuerySession.selectedDataset`; its pure model is
    `Storage.SelectedDataset.selectedModel`, named assumption `SelectedAgrees`). -/
def selectedDataset (ss : Session) (q : Query) (extraGraphs : List WfIri := []) : IO (Dataset × String) :=
  QuerySession.selectedDataset ss q extraGraphs

/-- Write a graph (CONSTRUCT, DESCRIBE) as N-Triples lines; returns the
    number of triples. -/
abbrev emitGraph (graph : Graph) (emit : ByteArray → IO Unit) : IO Nat := QuerySession.emitGraph graph emit

/-- The query's environment for expressions (NOW read once, BASE, the
    GeoSPARQL extension functions), without a dataset: the id path's
    post-processing and residual FILTERs (issue 823) read no EXISTS. The
    reference fallback adds its dataset (`runReference`). The theorem for the
    WHERE clause under this environment:
    `HarnessWhereTheorems.harness_where_allowed`. -/
def queryEnv (q : Query) : IO EvalEnv := do
  let clockEnv ← L4Wasm.Ops.emptyEnvNow
  return IdGroup.queryEnvOf clockEnv q.base

/-- Write the answer of a post-processed id plan (issue 823). -/
abbrev emitPost (ans : IdQuery.PostAnswer) (emit : ByteArray → IO Unit) : IO Unit := QuerySession.emitPost ans emit

/-- The reference evaluator over the selected dataset
    (`QuerySession.runReference`), NOW read once here. -/
def runReference (ss : Session) (q : Query) (reason : String) (emit : ByteArray → IO Unit) :
    IO (Nat × String) := do
  QuerySession.runReference ss (← L4Wasm.Ops.emptyEnvNow) q reason emit

/-! ## Running a query -/

abbrev Outcome := QuerySession.Outcome

def parse (text : String) (base : Option String) (version : SparqlVersion := .v11) : IO Query :=
  match QuerySession.parse? text base version with
  | .error e => throw (IO.userError e)
  | .ok q => pure q

/-- Run one parsed query on an open session: `QuerySession.runOneWith` with
    the stores of `threads` scan tasks per BGP scan (`storeWith`,
    `storeNested`), the divided paths of `Session.par` above one thread, and,
    before an id plan, the pool's workers woken (issue 961: blocked pool
    workers poll again from here, so the first divided phase does not wait for
    a kernel wake-up; only for a plan with two or more triple patterns: DBpedia
    d17, one pattern answered from the PRM1 entries in 0.3 ms, took 0.37 ms at
    4 threads against 0.29 ms with every query waking the workers) and a scan
    started early for the query before dropped (stage 1o). -/
def runOne (ss : Session) (q : Query) (emit : ByteArray → IO Unit) (forceReference referenceRender : Bool)
    (threads : Nat := 1) (sip : Option Nat := some 16) (aggOnIds : Bool := true) : IO Outcome := do
  let minRows ← minRangeRows
  let clockEnv ← L4Wasm.Ops.emptyEnvNow
  QuerySession.runOneWith ss clockEnv q emit forceReference referenceRender
    { store := ss.storeWith threads sip minRows aggOnIds
      nested := ss.storeNested threads sip minRows aggOnIds
      par := if threads ≤ 1 then none else some (ss.par threads minRows)
      onPlan := fun plan => do
        if plan.pats.size ≥ 2 then
          if let some p := ss.pool then p.wake
        let _ ← prescanSlot.swap none }

def verifyText : Verify → String
  | .merkle => "each read widened to its 65,536-byte chunks, each chunk checked by its Merkle proof"
  | .none => "exact byte ranges, no chunk widening, no hash checks; activation checked the files"

def median (xs : Array Nat) : Nat :=
  let s := L4Factoidal.Qlvr.mergeSortBy xs (· ≤ ·)
  if s.isEmpty then 0 else s[(s.size - 1) / 2]!

def msText (ns : Nat) : String :=
  let us := ns / 1000
  s!"{us / 1000}.{toString (1000 + us % 1000) |>.drop 1}"

structure Opts where
  text : Option String := none
  file : Option String := none
  base : Option String := none
  explain : Bool := false
  repeatN : Nat := 1
  referenceRender : Bool := false
  reference : Bool := false
  /-- `--verify`; when absent the CLI uses `cliDefaultVerify` -/
  verify : Option Verify := Option.none
  /-- `--threads N`: scan tasks per BGP scan; 1 is the single-thread path -/
  threads : Nat := 1
  /-- `--sip auto|always|off` (issue 809): the factor of `IdQuery.sipRule`
      (16, 0) or none -/
  sip : Option Nat := some 16
  /-- `--sparql12`: read the query with the SPARQL 1.2 grammar (triple-term
      patterns and the triple functions; issue 792 item 1) -/
  sparql12 : Bool := false
  /-- `--no-agg-ids` clears it (issue 825) -/
  aggOnIds : Bool := true

def parseOpts (xs : List String) : Except String Opts := Id.run do
  let arr := xs.toArray
  let mut o : Opts := {}
  let mut i := 0
  for _ in [0:arr.size] do
    if i ≥ arr.size then break
    let x := arr[i]!
    if x == "--file" then
      o := { o with file := arr[i + 1]? }
      i := i + 2
    else if x == "--base" then
      o := { o with base := arr[i + 1]? }
      i := i + 2
    else if x == "--repeat" then
      o := { o with repeatN := ((arr.getD (i + 1) "1").toNat?.getD 1) }
      i := i + 2
    else if x == "--explain" then
      o := { o with explain := true }
      i := i + 1
    else if x == "--reference-render" then
      o := { o with referenceRender := true }
      i := i + 1
    else if x == "--reference" then
      o := { o with reference := true }
      i := i + 1
    else if x == "--sparql12" then
      o := { o with sparql12 := true }
      i := i + 1
    else if x == "--no-agg-ids" then
      o := { o with aggOnIds := false }
      i := i + 1
    else if x == "--threads" then
      match (arr[i + 1]?).bind String.toNat? with
      | some n => if n ≥ 1 then o := { o with threads := n } else return .error "--threads takes N ≥ 1"
      | Option.none => return .error "--threads takes N ≥ 1"
      i := i + 2
    else if x == "--sip" then
      match arr[i + 1]? with
      | some "auto" => o := { o with sip := some 16 }
      | some "always" => o := { o with sip := some 0 }
      | some "off" => o := { o with sip := Option.none }
      | _ => return .error "--sip takes auto, always or off"
      i := i + 2
    else if x == "--verify" then
      match (arr[i + 1]?).bind Verify.ofString? with
      | some v => o := { o with verify := some v }
      | Option.none => return .error "--verify takes merkle or none"
      i := i + 2
    else if x.startsWith "--" then return .error s!"unknown option {x}"
    else
      o := { o with text := some x }
      i := i + 1
  return .ok o

/-- The `--verify` option, or the CLI default for `dir`; the second part says
    which (for `--explain` and the stderr summary). -/
def chooseVerify (dir : String) : Option Verify → IO (Verify × String)
  | some v => pure (v, "--verify")
  | Option.none => do
    let v ← cliDefaultVerify dir
    pure (v, if v == .none then "default: CURRENT names this generation" else "default: not an activated generation")

def runQuery (dir : String) (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let text ← match o.file, o.text with
    | some f, _ => IO.FS.readFile f
    | none, some t => pure t
    | none, none => throw (IO.userError "no query")
  let q ← parse text o.base (if o.sparql12 then .v12 else .v11)
  let (v, why) ← chooseVerify dir o.verify
  let ss ← openOverlaid v dir
  -- issue 961: the session's worker pool, N - 1 threads that poll between the
  -- divided phases of a query (the calling thread is the N-th). Not when N is
  -- above the hardware threads: a polling worker then takes a core from a
  -- thread with work (olympics q07 at 8 threads on 4 vCPUs, 7 polling
  -- workers: the scans with candidates took 2.5 to 4.6 ms against 0.5 to
  -- 0.9 ms at 4 threads).
  let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
  let ss ← if o.threads > 1 && (hw == 0 || o.threads ≤ hw) then
      pure { ss with pool := some (← Harness.WorkerPool.start (((← IO.getEnv "SBM11_POOL_SIZE").bind String.toNat?).getD (o.threads - 1)) ((← IO.getEnv "SBM11_SPIN_NS").bind String.toNat? |>.getD 1000000) (IO.mkRef {})) }
    else pure ss
  let ss := { ss with phases := (← IO.getEnv "SBM11_PHASES").isSome,
                      renderRows := ((← IO.getEnv "SBM11_RENDER_ROWS").bind String.toNat?).getD IdQuery.renderJobRows,
                      streamPerThread := ((← IO.getEnv "SBM11_STREAM_JOBS").bind String.toNat?).getD IdQuery.streamJobsPerThread,
                      sortedRows := ((← IO.getEnv "SBM11_SORTED_RENDER_ROWS").bind String.toNat?).getD 64,
                      joinShare := ((← IO.getEnv "SBM11_JOIN_SHARE").bind String.toNat?).getD 14 }
  let t1 ← IO.monoNanosNow
  let openBytes ← ss.g.fileBytes.get
  let stdout ← IO.getStdout
  let runs := max o.repeatN 1
  let mut execs : Array Nat := #[]
  let mut phaseTimes : Array (Array (String × Nat)) := #[]
  let mut last : Option Outcome := none
  for k in [0:runs] do
    let final := k + 1 == runs
    -- the opened permutations, the verified chunk caches and the
    -- dictionary page cache persist from run to run, as in an open store
    ss.frameBytes.set 0
    ss.prmBytes.set 0
    ss.g.fetchedBytes.set 0
    phaseMarks.set #[]
    let a ← IO.monoNanosNow
    phaseMark "start"
    -- a failed run stops the worker pool before the error leaves `main`: the
    -- runtime waits for the pool's dedicated threads at exit, so an error
    -- with the pool running made the process hang (stage 1j)
    let r ← match ← (runOne ss q (if final then fun s => stdout.write s else fun _ => pure ()) o.reference
        o.referenceRender o.threads o.sip o.aggOnIds).toBaseIO with
      | .ok r => pure r
      | .error e =>
        if let some p := ss.pool then p.shutdown
        throw e
    let b ← IO.monoNanosNow
    -- stage 1p: the time after the last phase mark of the query (the plan
    -- text, the JSON tail, the end of the divided work)
    if ss.phases then phaseMark "end"
    execs := execs.push (b - a)
    if ss.phases then
      let ms ← phaseMarks.get
      phaseTimes := phaseTimes.push ((List.range (ms.size - 1)).toArray.map fun i =>
        (ms[i + 1]!.1, ms[i + 1]!.2 - ms[i]!.2))
    last := some r
  stdout.write "\n".toUTF8
  stdout.flush
  if let some p := ss.pool then p.shutdown
  let t2 ← IO.monoNanosNow
  let some r := last | return 1
  if o.explain then
    IO.eprintln s!"plan: verify={v.name} ({why}; {verifyText v})"
    IO.eprintln s!"plan: threads={o.threads} (scan tasks per BGP scan; 1 is the single-thread path)"
    IO.eprintln s!"plan: sip={match o.sip with | some 16 => "auto" | some 0 => "always" | some k => s!"factor {k}" | Option.none => "off"} (candidates into a merge join's right scan when factor × left rows < estimate; issue 809)"
    for l in r.plan do IO.eprintln s!"plan: {l}"
    IO.eprintln s!"plan: {ss.deltaText}"
  let fb ← ss.frameBytes.get
  let fetched ← ss.g.fetchedBytes.get
  -- SBM11_PHASES: the median of each phase over runs 2 to N (run 1 fills the
  -- caches); phases are matched by position, as every run of one query
  -- passes the same marks
  if let some w := phaseTimes[1]? then
    for j in [0:w.size] do
      let xs := (phaseTimes.extract 1 phaseTimes.size).filterMap fun r => (r[j]?).map (·.2)
      IO.eprintln s!"phase: {w[j]!.1} median {msText (median xs)} ms"
  if runs > 1 then
    IO.eprintln s!"repeat: {runs} runs in one process; execution ms median {msText (median execs)} min {msText (execs.foldl min (execs.getD 0 0))} max {msText (execs.foldl max 0)}"
  IO.eprintln s!"sbm11-query: {r.path}; rows {r.rows}; verify={v.name}; {ss.deltaText}; constants looked up {← ss.lookups.get}; block bytes read {fb}; PRM1 bytes read {← ss.prmBytes.get}; range bytes fetched {fetched}; file bytes read {← ss.g.fileBytes.get}; open file bytes {openBytes}; open {msText (t1 - t0)} ms; execution {msText (t2 - t1)} ms; total {msText (t2 - t0)} ms; peak RSS (VmHWM): {← vmHWM}"
  return 0

/-- One query per line of stdin; one line of SPARQL JSON per query; each read
    with the SPARQL grammar `version`. -/
def runServe (dir : String) (verify? : Option Verify) (version : SparqlVersion := .v11) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let (v, why) ← chooseVerify dir verify?
  let ss ← openOverlaid v dir
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"serve: verify={v.name} ({why}); {ss.deltaText}; open {msText (t1 - t0)} ms; peak RSS (VmHWM): {← vmHWM}"
  IO.eprintln s!"serve: {ss.overlayText (← overlayLimitFromEnv)}"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut failures := 0
  for _ in [0:1000000] do
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    try
      let text ← if line.startsWith "--file " then IO.FS.readFile (line.drop 7).trimAscii.toString else pure line
      let q ← parse text none version
      let a ← IO.monoNanosNow
      let r ← runOne ss q (fun s => stdout.write s) false false
      let b ← IO.monoNanosNow
      stdout.write "\n".toUTF8
      stdout.flush
      IO.eprintln s!"serve: {r.path}; rows {r.rows}; execution {msText (b - a)} ms; peak RSS (VmHWM): {← vmHWM}"
    catch e =>
      stdout.write "{\"error\":true}\n".toUTF8
      stdout.flush
      IO.eprintln s!"serve: failed: {e}"
      failures := failures + 1
  return (if failures == 0 then 0 else 1)

/-- The keys of the range check of `prm-check`: the empty key; for about 48
    blocks spread over the file (the first two, the last two, and every
    `n / 44`-th), the prefixes of length 1, 2 and 3 of the first and the last
    row, and the first column of the first row plus and minus one. -/
def rangeCheckKeys (ms : Array BlockMeta) : Array (Array UInt64) := Id.run do
  let n := ms.size
  let mut idx : Array Nat := #[0, 1, n - 1, n - 2]
  for i in [0:44] do idx := idx.push (i * n / 44)
  let mut keys : Array (Array UInt64) := #[#[]]
  for i in idx do
    if i < n then
      let b := ms[i]!
      for r in [b.first, b.last] do
        keys := keys.push #[r.c0.toUInt64]
        keys := keys.push #[r.c0.toUInt64, r.c1.toUInt64]
        keys := keys.push #[r.c0.toUInt64, r.c1.toUInt64, r.c2.toUInt64]
      keys := keys.push #[(b.first.c0 + 1).toUInt64]
      if b.first.c0 > 0 then keys := keys.push #[(b.first.c0 - 1).toUInt64]
  return keys

/-- `PrmAt.decodePrmAt` against `Block.decodePrm` on every PRM1 file; then
    the range search of issue 805 (`PrmRange.rangeM`) against decoding the
    whole file and selecting (`IdQuery.metasFor`), for the keys of
    `rangeCheckKeys`: over the file's bytes in memory (the reader of
    `PrmRangeTheorems.rangeM_bytes`), and through a query session's
    positioned reads under `--verify none` and `--verify merkle`. -/
def runPrmCheck (dir0 : String) : IO UInt32 := do
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let mbytes ← IO.FS.readBinFile s!"{dir}/{manifestName}"
  let some m := decodeManifest mbytes.data.toList
    | throw (IO.userError "manifest does not decode")
  let ssNone ← openSession .none dir
  let ssMerkle ← openSession .merkle dir
  let mut bad := 0
  for p in [0:4] do
    let a ← artifact m s!"PRM1-{(permNamesArr[p]!).toUpper}"
    let bytes ← IO.FS.readBinFile s!"{dir}/{a.file}"
    let fast := (PrmAt.decodePrmAt bytes).map fun (q, ms) => (q, ms.toList)
    let spec := decodePrm bytes.data.toList
    let same := fast == spec
    -- the range search against the whole file, selected
    let mut keysChecked := 0
    let mut rangeBad := 0
    let mut selected := 0
    match PrmAt.decodePrmAt bytes with
    | none => rangeBad := rangeBad + 1
    | some (_, ms) =>
      let read : Nat → Nat → ExceptT String Id ByteArray := fun off len => pure (bytes.extract off (off + len))
      for key in rangeCheckKeys ms do
        let want := IdQuery.metasFor ms key
        let pure' := Id.run (do let n ← PrmRange.openM read bytes.size p; PrmRange.rangeM (PrmRange.bytesReader read n) key).run
        let viaNone ← ssNone.rangeFor p key
        let viaMerkle ← ssMerkle.rangeFor p key
        keysChecked := keysChecked + 1
        selected := selected + want.size
        if pure'.toOption != some want || viaNone != want || viaMerkle != want then rangeBad := rangeBad + 1
    IO.println s!"prm-check {permNamesArr[p]!}: entries {(spec.map (·.2.length)).getD 0}; equal {same}; range search: {keysChecked} keys, {selected} entries selected, {rangeBad} different"
    if !same || spec.isNone || rangeBad > 0 then bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- `FrameWords.decodeWords` against `decodeColumnAt` on every frame of
    every block of every permutation. -/
def runFrameCheck (dir : String) : IO UInt32 := do
  let ss ← openSession .merkle dir
  let mut frames := 0
  let mut bad := 0
  for p in [0:4] do
    let lp ← ss.perm p
    -- every frame: the whole PRM1 file (the query path never reads it whole)
    let some (_, metas) := PrmAt.decodePrmAt (← IO.FS.readBinFile lp.prmPath)
      | throw (IO.userError s!"{lp.prmPath}: does not decode as PRM1")
    let size := metas.foldl (fun a m => max a (m.offset + m.size)) 0
    let bytes ← IO.FS.readBinFile lp.prbPath
    if bytes.size < size then throw (IO.userError s!"{lp.prbPath}: shorter than its blocks")
    for m in metas do
      let lens := #[m.len0, m.len1, m.len2, m.len3]
      let mut off := m.offset
      for c in [0:4] do
        let a := FrameWords.decodeWords bytes m.rows off
        let r := FrameWords.decodeWordsRef bytes m.rows off
        frames := frames + 1
        if !FrameWords.same a r || a.isNone then bad := bad + 1
        off := off + lens[c]!
  IO.println s!"frame-check: {frames} frames, {bad} different or refused"
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | "query" :: dir :: rest =>
    match parseOpts rest with
    | .error e => IO.eprintln s!"l4sbm11 query: {e}"; return 2
    | .ok o =>
      try runQuery dir o
      catch e => IO.eprintln s!"l4sbm11 query: {e}"; return 1
  | ["serve", dir] =>
    try runServe dir Option.none
    catch e => IO.eprintln s!"l4sbm11 serve: {e}"; return 1
  | ["serve", dir, "--verify", vs] =>
    match Verify.ofString? vs with
    | Option.none => IO.eprintln "l4sbm11 serve: --verify takes merkle or none"; return 2
    | some v =>
      try runServe dir (some v)
      catch e => IO.eprintln s!"l4sbm11 serve: {e}"; return 1
  | ["prm-check", dir] =>
    try runPrmCheck dir
    catch e => IO.eprintln s!"l4sbm11 prm-check: {e}"; return 1
  | ["frame-check", dir] =>
    try runFrameCheck dir
    catch e => IO.eprintln s!"l4sbm11 frame-check: {e}"; return 1
  | _ =>
    IO.eprintln "usage: l4sbm11 query GEN ('SPARQL' | --file Q.rq) [--base IRI] [--explain] [--repeat N] [--reference-render] [--reference] [--verify merkle|none] [--threads N] [--sip auto|always|off] [--sparql12] [--no-agg-ids] | serve GEN [--verify merkle|none] [--sparql12] | prm-check GEN | frame-check GEN"
    return 2

end Harness.Sbm11Query
