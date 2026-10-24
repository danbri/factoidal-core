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

This is a HARNESS: it does file I/O. The query engine is
`L4Factoidal.Storage.Sbm11.IdQuery`.
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
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.Geo.Functions
import Wasm.Ops.Clock
import Std.Sync.Mutex
import Std.Data.TreeMap
import Harness.WorkerPool

namespace Harness.Sbm11Query

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Manifest
open Harness.Sbm11Gen
open L4Factoidal.Storage.ChunkedArtifact (Ref)

/-! ## A generation opened lazily -/

/-- A page of `Session.taskPages` (issue 799, stage 1b): its keys, or a
    promise of them while one task loads it (the other tasks that need the
    page wait for the promise, so a page is loaded once). -/
inductive TaskPage where
  | ready (ks : ByteArray × Array Nat)
  | loading (p : IO.Promise (Except String (ByteArray × Array Nat)))

/-- A permutation opened by a query session. Its PRM1 file is never read
    whole (https://github.com/danbri/factoidal/issues/805): the open reads
    the 22-byte header (`PrmRange.openM`), and each key range is found by
    `PrmRange.rangeM` over positioned reads (`prmRead`): two binary searches
    that read one 92-byte entry per probe, then one read of the entries of
    the selected blocks. Under `Verify.merkle` every such read goes through
    the PRM1 file's verified chunk cache (`prmLeaves`, `prmCache`). -/
structure LoadedPerm where
  prbPath : String
  prbRef : Ref
  leaves : List L4Factoidal.Storage.BlockMerkle.Digest
  cache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  prmPath : String
  prmRef : Ref
  /-- PRB1 and PRM1 opened once for positioned reads (stage 1n of the
      parallel-scans record): closed when the session is freed. -/
  prbFile : Option Harness.PosixRangeIO.BlockFile := none
  prmFile : Option Harness.PosixRangeIO.BlockFile := none
  prmLeaves : List L4Factoidal.Storage.BlockMerkle.Digest
  prmCache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  /-- the block count of the PRM1 header -/
  count : Nat
  /-- the answers of `rangeM` for the keys asked so far (the generation does
      not change while it is open); at most 256 keys, emptied when full -/
  ranges : IO.Ref (Std.HashMap (Array UInt64) (Array BlockMeta))

/-- The dictionary page cache of one pool worker (stage 1h of
    docs/designissues/2026-10-12-parallel-block-scans.md): made by the
    worker's own thread when the pool starts (`Harness.WorkerPool.start`) and
    given to each job of that worker, so it is never reachable from another
    thread. The Lean runtime then updates it in place and counts references
    to its pages without atomic operations, and the pages a worker copied
    stay with it from one query to the next. -/
abbrev WorkerPages := IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))

/-- An open generation: the manifest, the dictionary's Merkle leaves and
    header; each permutation is opened on its first use (its PRM1 read, length
    and, under `Verify.merkle`, SHA-256 checked against the manifest, decoded;
    under `merkle` its PRB1 leaves admitted against the manifest root). -/
structure Session where
  g : Gen
  perms : IO.Ref (Array (Option LoadedPerm))
  pages : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))
  /-- bytes of PRB1 blocks read (the frames a plan reads) -/
  frameBytes : IO.Ref Nat
  /-- bytes of PRM1 entries and headers asked for (issue 805; under
      `merkle` the verified chunks fetched for them are in `fetchedBytes`) -/
  prmBytes : IO.Ref Nat
  lookups : IO.Ref Nat
  /-- Under `Verify.merkle`: GDX1, read whole on the first dictionary access
      (102 KB on olympics: 12 bytes per page), its length and SHA-256 checked
      against the manifest. Unused under `none` (each GDX1 entry is one
      `pread`). -/
  gdx : IO.Ref (Option ByteArray)
  /-- The overlay vocabulary (stage 5): terms of the delta log that have no
      base id, in the order the replay met them; the id of entry `k` is
      `tagDelta · 2^60 + k`. -/
  ovVocab : IO.Ref (Array Term)
  ovIds : IO.Ref (Std.HashMap Term Nat)
  /-- The dictionary ids of the terms of the log being replayed
      (`prefillBaseIds`, issue 858): a normalised term to its dictionary id, or
      `none` when the dictionary does not hold it. Empty except during a
      replay; `idOf` reads it before it reads the dictionary. -/
  baseIds : IO.Ref (Std.HashMap Term (Option UInt64))
  /-- The dictionary ids that `idOf` has looked up in this session (a
      normalised term to its id; terms the dictionary does not hold are not
      kept, since the delta overlay may give them an id). The base dictionary
      does not change while the session is open, so an entry stays right, as
      a cached dictionary page does. At most `idMemoLimit` entries, emptied
      when full. Olympics q07 looks up 6 constants per run; each lookup is a
      binary search over GDX1 entries and GDV1 pages, about 14 positioned
      reads: 0.43 ms of the 5.4 ms query on one thread, the same at 4
      threads (KR 1.2 of https://github.com/danbri/factoidal/issues/875). -/
  idMemo : IO.Ref (Std.HashMap Term UInt64)
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
  /-- The dictionary's term count (`g.dictHdr.termCount`), read by every
      `keySlice`. A field of its own: reading it through `g.dictHdr` took and
      released a reference to the header object, which every task view
      shares, and on an object that two threads reach that is an atomic
      operation on one cache line from every thread. -/
  termCount : Nat := 0
  /-- The overlay per permutation (`Overlay.forPerm`), fixed at open. -/
  ovl : Array L4Factoidal.Storage.Sbm11.Overlay.PermOverlay := #[{}, {}, {}, {}]
  /-- committed batches and entries replayed at open; overlay inserts,
      deletes, cleared graphs -/
  deltaBatches : Nat := 0
  deltaOps : Nat := 0
  ovInserts : Nat := 0
  ovDeletes : Nat := 0
  ovCleared : Nat := 0
  ovNewTerms : Nat := 0
  /-- the distinct terms of the log looked up in the dictionary by the replay
      (issue 858) -/
  replayTerms : Nat := 0
  replayNs : Nat := 0
  /-- the log ended with a torn final frame (an append that did not
      complete), left out of the replay (issue 843) -/
  deltaTorn : Bool := false
  /-- the replayed overlay state (`ovl` is its cut per permutation); `l4sbm11
      update` (`Harness/Sbm11Update.lean`) applies the entries of a request to
      it, so that each operation reads the state the one before left -/
  ovState : L4Factoidal.Storage.Sbm11.Overlay.State := {}
  /-- the named graphs of the base generation (`baseNamedGraphs`: the graph
      list GNL1, or the graph ids of the base quads), read at the first use -/
  baseNamedRef : IO.Ref (Option (Array Nat))
  /-- the size in bytes of the log file the replay read (0: no log); a
      positioned append of `l4sbm11 update` uses it -/
  ovLogBytes : Nat := 0
  /-- `SBM11_PAGES` (default `defaultPages`) and the per-view limit
      `min SBM11_PAGES SBM11_TASK_PAGES` (default 256), read once at open
      (issue 799, KR 1.2). They were read from the environment on every page
      insert: `getenv` and its string compares were 1.3 percent of olympics
      q19 at 4 threads. -/
  pageLimit : Nat := 8192
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
  -- stage 1n: GDV1 and GDX1 opened once, not at every read
  let gdvFile := some (← Harness.PosixRangeIO.BlockFile.open gdvPath)
  let gdxFile := some (← Harness.PosixRangeIO.BlockFile.open gdxPath)
  let g0 : Gen := { dir, manifest := m, verify := v, gdvPath, gdxPath, gdvRef := gdvA.merkle, gdxRef := gdxA.merkle,
                    gdvLeaves, gdxLeaves, gdvCache, gdxCache, gdvFile, gdxFile, dictHdr := default, perms := #[],
                    readBytes, fetchedBytes, fileBytes }
  let hdrBytes ← verifiedRead g0 g0.gdxSrc gdxA.merkle gdxLeaves gdxCache 0 Dict.gdxHeaderBytes
  let dictHdr ← ok "GDX1" (Dict.parseGdxHeader hdrBytes)
  return { g := { g0 with dictHdr }, termCount := dictHdr.termCount,
           perms := ← IO.mkRef #[none, none, none, none],
           pages := ← IO.mkRef {}, frameBytes := ← IO.mkRef 0, prmBytes := ← IO.mkRef 0,
           lookups := ← IO.mkRef 0,
           gdx := ← IO.mkRef none, ovVocab := ← IO.mkRef #[], ovIds := ← IO.mkRef {}, baseIds := ← IO.mkRef {},
           idMemo := ← IO.mkRef {},
           baseNamedRef := ← IO.mkRef none,
           lock := ← Std.Mutex.new (), dictLock := ← Std.Mutex.new (), taskPages := ← IO.mkRef {},
           pageLimit := ← pagesLimitEnv, taskPageLimit := ← taskPagesLimitEnv }

/-- A positioned read of a PRM1 file (`PrmRange`'s `read`): under `none` one
    `pread` of exactly the bytes, under `merkle` through the file's verified
    chunk cache (one read at a time: the cache is shared, issue 799). -/
def Session.prmReadAt (ss : Session) (path : Harness.PosixRangeIO.ReadSrc) (ref : Ref)
    (leaves : List L4Factoidal.Storage.BlockMerkle.Digest)
    (cache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache) (off len : Nat) : ExceptT String IO ByteArray :=
  ExceptT.lift do
    ss.prmBytes.modify (· + len)
    match ss.g.verify with
    | .merkle => ss.lock.atomically (verifiedRead ss.g path ref leaves cache off len)
    | .none => verifiedRead ss.g path ref leaves cache off len

def Session.perm (ss : Session) (p : Nat) : IO LoadedPerm := do
  match (← ss.perms.get)[p]? with
  | some (some lp) => return lp
  | some none =>
    let m := ss.g.manifest
    let nm := (permNamesArr[p]!).toUpper
    let prmA ← artifact m s!"PRM1-{nm}"
    let prbA ← artifact m s!"PRB1-{nm}"
    let prmPath := s!"{ss.g.dir}/{prmA.file}"
    let prbPath := s!"{ss.g.dir}/{prbA.file}"
    -- PRM1: the header only (issue 805); the leaves of its Merkle tree under
    -- `merkle`, so that each positioned read is checked by its chunks
    let prmLeaves ← loadLeaves ss.g.verify ss.g.fileBytes prmPath prmA.merkle
    let prmCache ← newChunkCache ss.g.verify prmA.merkle
    -- stage 1n: PRB1 and PRM1 opened once, not at every read
    let prmFile := some (← Harness.PosixRangeIO.BlockFile.open prmPath)
    let prbFile := some (← Harness.PosixRangeIO.BlockFile.open prbPath)
    let count ← match ← (PrmRange.openM (ss.prmReadAt { path := prmPath, file := prmFile } prmA.merkle prmLeaves prmCache) prmA.bytes p).run with
      | .ok n => pure n
      | .error e => throw (IO.userError s!"{prmPath}: {e}")
    let leaves ← loadLeaves ss.g.verify ss.g.fileBytes prbPath prbA.merkle
    let cache ← newChunkCache ss.g.verify prbA.merkle
    let lp : LoadedPerm := { prbPath, prbRef := prbA.merkle, leaves, cache, prmPath, prmRef := prmA.merkle,
                             prmLeaves, prmCache, prbFile, prmFile, count, ranges := ← IO.mkRef {} }
    ss.perms.modify (·.set! p (some lp))
    return lp
  | none => throw (IO.userError s!"no permutation {p}")

def Session.gdxBytes (ss : Session) : IO ByteArray := do
  match ← ss.gdx.get with
  | some b => return b
  | none =>
    let a ← artifact ss.g.manifest "GDX1"
    let b ← IO.FS.readBinFile ss.g.gdxPath
    ss.g.fileBytes.modify (· + b.size)
    if b.size != a.bytes || Harness.nativeSha256 b != a.sha256 then
      throw (IO.userError s!"{ss.g.gdxPath}: length or SHA-256 differs from the manifest")
    -- `modify`, not `set`: another thread may read `gdx` with `get` (issue
    -- 981, `Harness.WorkerPool` module comment)
    ss.gdx.modify fun _ => some b
    return b

def Session.gdxFetch (ss : Session) (off len : Nat) : IO ByteArray := do
  if ss.g.verify == .none then
    return (← verifiedRead ss.g ss.g.gdxSrc ss.g.gdxRef ss.g.gdxLeaves ss.g.gdxCache off len)
  let b ← ss.gdxBytes
  if off + len > b.size then throw (IO.userError s!"GDX1: read past the end")
  return b.extract off (off + len)

/-- Bytes `[off, off + len)` of GDV1. `merkle`: through the verified chunk
    cache: each 65,536-byte chunk is admitted once by its Merkle proof
    (`readVerifiedChunkCached?`), then ranges are cut from it. `none`: one
    `pread` of exactly those bytes. -/
def Session.gdvFetch (ss : Session) (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  if ss.g.verify == .none then
    return (← verifiedRead ss.g ss.g.gdvSrc ss.g.gdvRef ss.g.gdvLeaves ss.g.gdvCache off len)
  let cb := ss.g.gdvRef.chunkBytes
  let first := off / cb
  let last := (off + len - 1) / cb
  let mut out := ByteArray.emptyWithCapacity len
  for c in [first:last + 1] do
    match ← Harness.PosixRangeIO.readVerifiedChunkCached? ss.g.gdvSrc ss.g.gdvRef ss.g.gdvLeaves ss.g.gdvCache c with
    | some (chunk, fp) =>
      ss.g.fetchedBytes.modify (· + fp.fetchedBytes)
      ss.g.fileBytes.modify (· + fp.fetchedBytes)
      let lo := max off (c * cb) - c * cb
      let hi := min (off + len) ((c + 1) * cb) - c * cb
      if hi > chunk.size then throw (IO.userError s!"GDV1: chunk {c} is short")
      out := chunk.copySlice lo out out.size (hi - lo)
    | none => throw (IO.userError s!"GDV1: chunk {c} refused")
  return out

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

/-- The keys of dictionary page `pg`, packed: one byte array holding the keys
    one after the other and the start of each key (and the end of the last).
    One object per page: a cache of 64 separate key arrays per page left the
    heap fragmented (q19: peak RSS 98 MB against 31 MB with a cache of 64
    pages, and slower, each new huge page being cleared on first touch). The
    cache holds at most `SBM11_PAGES` pages (default 8,192) and is emptied
    when full. -/
def Session.loadPage (ss : Session) (pg : Nat) : IO (ByteArray × Array Nat) := do
  let ks ← ok s!"GDV1 page {pg}" (← (Dict.pageM ss.gdxFetch ss.gdvFetch pg).run)
  let total := ks.foldl (fun a k => a + k.size) 0
  let mut packed := ByteArray.emptyWithCapacity total
  let mut offs : Array Nat := Array.mkEmpty (ks.size + 1)
  for k in ks do
    offs := offs.push packed.size
    packed := packed ++ k
  offs := offs.push packed.size
  return (packed, offs)

/-- Put page `pg` in the page cache `c`, emptied first when it holds
    `SBM11_PAGES` pages (default 8,192; 0: no cache). -/
def cachePage (lim : Nat) (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit := do
  if lim > 0 then
    c.modify fun m => insertPageBounded m lim pg ks

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
    if let some r := ss.onceSeen then
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

def Session.keySlice (ss : Session) (x : UInt64) : IO (ByteArray × Nat × Nat) := do
  let id := x.toNat
  let tag := id / two60
  unless isDictTag tag do
    throw (IO.userError s!"id {id}: not a dictionary id")
  let rank := id % two60
  if rank ≥ ss.termCount then throw (IO.userError s!"id {id}: rank not below the term count")
  let (packed, offs) ← ss.pageKeys (rank / Dict.pageTerms)
  let j := rank % Dict.pageTerms
  if j + 1 < offs.size then return (packed, offs[j]!, offs[j + 1]!)
  throw (IO.userError s!"id {id}: no key")

def Session.keyOf (ss : Session) (x : UInt64) : IO ByteArray := do
  let (packed, a, e) ← ss.keySlice x
  return packed.extract a e

def Session.termOf (ss : Session) (x : UInt64) : IO Term := do
  let id := x.toNat
  let tag := id / two60
  if tag == tagInt || tag == tagBool then
    match ofInlineCode? id with
    | some t => return t
    | none => throw (IO.userError s!"inline id {id} does not decode")
  if tag == L4Factoidal.Storage.Sbm11.Overlay.tagDelta then
    match (← ss.ovVocab.get)[id % two60]? with
    | some t => return t
    | none => throw (IO.userError s!"id {id}: not in the overlay vocabulary")
  -- the key is read in place from the page (`keySlice`): no copy of its bytes
  -- and no list (`decodeKeySlice?_eq`, `classTagSlice_eq`; issue 825)
  let (packed, a, e) ← ss.keySlice x
  if classTagSlice packed a e != tag then throw (IO.userError s!"id {id}: tag differs from the key's class")
  match decodeKeySlice? packed a e with
  | some t => return t
  | none => throw (IO.userError s!"id {id}: key does not decode")

/-- The id of the dictionary key `k` of rank `r`. -/
def dictIdOfRank (k : ByteArray) (r : Nat) : UInt64 := (dictCode k.data.toList r).toUInt64

/-- The id of a term that the delta log added (stage 5), when it has one. -/
def Session.overlayIdOf (ss : Session) (t : Term) : IO (Option UInt64) := do
  return ((← ss.ovIds.get).get? t).map fun n =>
    (L4Factoidal.Storage.Sbm11.Overlay.tagDelta * two60 + n).toUInt64

/-- The most entries `Session.idMemo` holds. -/
def idMemoLimit : Nat := 65536

/-- The id of a term: its inline code, its dictionary id (from `baseIds` when
    a replay has put it there, else from `idMemo`, else one `Dict.lookupM`),
    else the id the delta log gave it. -/
def Session.idOf (ss : Session) (t : Term) : IO (Option UInt64) := do
  ss.lookups.modify (· + 1)
  let t := normalizeTerm t
  match inlineCode? t with
  | some c => return some c.toUInt64
  | none =>
    let memo ← ss.baseIds.get
    match (if memo.isEmpty then none else memo.get? t) with
    | some (some x) => return some x
    | some none => ss.overlayIdOf t
    | none =>
      if let some x := MemoCache.find? (← ss.idMemo.get) t then return some x
      match termKeyBytes? t with
      | none => return none
      | some k =>
        let (r, _) ← ok "lookup" (← (Dict.lookupM ss.gdxFetch ss.gdvFetch ss.g.dictHdr k).run)
        match r with
        | some r =>
          let x := dictIdOfRank k r
          ss.idMemo.modify fun m => MemoCache.insertBounded idMemoLimit m t x
          return some x
        | none =>
          -- a term the delta log added (stage 5)
          ss.overlayIdOf t

def Session.lowerBound (ss : Session) (k : ByteArray) : IO Nat := do
  ok "lower bound" (← (DictRange.lowerBoundM ss.gdxFetch ss.gdvFetch ss.g.dictHdr k).run)

/-- The PRM1 entries of the blocks of permutation `p` that may hold a row
    with the key prefix (`Store.blocksForRange`): `PrmRange.rangeM` over
    `PrmRange.bytesReader` of the permutation's positioned reads, the code of
    `PrmRangeTheorems.rangeM_bytes`; an answer is kept for the next query
    with the same key. -/
def Session.rangeFor (ss : Session) (p : Nat) (key : Array UInt64) : IO (Array BlockMeta) := do
  let lp ← ss.perm p
  if let some r := MemoCache.find? (← lp.ranges.get) key then return r
  let read := ss.prmReadAt { path := lp.prmPath, file := lp.prmFile } lp.prmRef lp.prmLeaves lp.prmCache
  let r ← match ← (PrmRange.rangeM (PrmRange.bytesReader read lp.count) key).run with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{lp.prmPath}: {e}")
  lp.ranges.modify fun m => MemoCache.insertBounded 256 m key r
  return r

def Session.prb (ss : Session) (p off len : Nat) : IO ByteArray := do
  let lp ← ss.perm p
  ss.frameBytes.modify (· + len)
  match ss.g.verify with
  | .merkle =>
    -- the chunk cache is one shared table: one read at a time (issue 799)
    ss.lock.atomically (verifiedRead ss.g { path := lp.prbPath, file := lp.prbFile } lp.prbRef lp.leaves lp.cache off len)
  | .none => verifiedRead ss.g { path := lp.prbPath, file := lp.prbFile } lp.prbRef lp.leaves lp.cache off len

/-- A view of the session for one scan task (issue 799): its own byte and
    lookup counters, and a copy of the permutations opened so far (the parent
    opens a permutation before it starts tasks, so a task never opens one).
    The chunk caches, the locks, the GDX1 copy and `taskPages` (read under
    `dictLock`) are shared; the session's own page cache is not (`pages` here
    is a placeholder that the task replaces with a cache it creates itself,
    `Session.local`). A task reaches the dictionary only through `pageKeys`
    (`keySlice`, `keyOf`, `termOf`): never `idOf` or `lowerBound`, which the
    parent calls before it starts tasks. The parent adds the view's counters
    after the task has finished (`Session.absorb`). -/
def Session.view (ss : Session) : IO Session := do
  let g' : Gen := { ss.g with readBytes := ← IO.mkRef 0, fetchedBytes := ← IO.mkRef 0,
                              fileBytes := ← IO.mkRef 0 }
  return { ss with g := g', perms := ← IO.mkRef (← ss.perms.get), frameBytes := ← IO.mkRef 0,
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

/-- The phase marks of the current run (`Session.phases`): label and
    `IO.monoNanosNow` at the end of the phase. -/
initialize phaseMarks : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

def phaseMark (l : String) : IO Unit := do
  let t ← IO.monoNanosNow
  phaseMarks.modify (·.push (l, t))

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

def Session.store (ss : Session) : IdQuery.Store IO :=
  { blockCount := fun p => liftIO do pure (← ss.perm p).count
    blocksForRange := fun p key => liftIO (ss.rangeFor p key)
    prb := fun p off len => liftIO (ss.prb p off len)
    idOf := fun t => liftIO (ss.idOf t)
    keyOf := fun x => liftIO (ss.keyOf x)
    keySlice := fun x => liftIO (ss.keySlice x)
    termOf := fun x => liftIO (ss.termOf x)
    lowerBound := fun k => liftIO (ss.lowerBound k)
    ovl := fun p => ss.ovl.getD p {}
    prefetch := some fun t n => liftIO (ss.prefetch t n)
    mark := if ss.phases then some phaseMark else none }

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
    let t ← ss.spawnAt tasks.size (do
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
      match ← (IdQuery.scanListM v.store spec true init f metasX sortVar ox posX).run with
      | .ok r => pure r
      | .error e => throw (IO.userError e))
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
  let mut tasks : Array (Harness.WorkerPool.Handle (Except IO.Error (L4Factoidal.Qlvr.Table × IdQuery.ScanStats)) × Session) := #[]
  for X in chunks.drop 1 do
    let v ← ss.view
    let t ← ss.spawnAt tasks.size (do
      let spec := spec.fresh
      let ox := ox.fresh spec.key
      let cands := cands.map fun x => UInt64.ofNat x.toNat
      let (metasX, posX) := rangeMetas metas (L4Factoidal.Storage.Sbm11.ParallelScan.boundsList X)
      let init : L4Factoidal.Qlvr.Table :=
        { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.empty,
          rows := 0, sortVar := IdQuery.sortVarOf spec }
      match ← (IdQuery.scanListSipM v.store spec cands init f metasX sortVar ox posX).run with
      | .ok r => pure r
      | .error e => throw (IO.userError e))
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
    renderRows := ss.renderRows
    streamPerThread := ss.streamPerThread }

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
  else { base with scanTable := some fun spec => scanTableParM ss spec threads minRows,
                   scanSipTable := some fun spec cands => scanSipTableParM ss spec cands threads minRows }

/-! ## The delta overlay (stage 5) -/

/-- The id of `t`: its base id, its overlay id, or a new overlay id. -/
def Session.idOrNew (ss : Session) (t0 : Term) : IO Nat := do
  match ← ss.idOf t0 with
  | some x => pure x.toNat
  | none =>
    let t := normalizeTerm t0
    -- a term in `baseIds` was resolved because it has a dictionary key; any other is checked now
    let admitted := (← ss.baseIds.get).contains t || (termKeyBytes? t).isSome
    if !admitted then
      throw (IO.userError s!"delta log: a term the SBM11 dictionary does not admit: {repr t}")
    -- one step that reads the size and pushes: a `get` before the `modify` leaves a second
    -- reference to the array, and every push then copies it (quadratic replay)
    let n ← ss.ovVocab.modifyGet fun vocab => (vocab.size, vocab.push t)
    ss.ovIds.modify (·.insert t n)
    pure (L4Factoidal.Storage.Sbm11.Overlay.tagDelta * two60 + n)

/-- A graph name of a DLOG entry as a term: an IRI or a blank node. -/
def graphTerm : L4Factoidal.Storage.DeltaGraphName → IO Term
  | .iri g =>
    if h : isIri g = true then pure (.iri ⟨g, h⟩)
    else throw (IO.userError s!"delta log: graph name is not an IRI: {g}")
  | .bnode b => pure (.bnode b)

def Session.graphIdOrNew (ss : Session) : Option L4Factoidal.Storage.DeltaGraphName → IO Nat
  | none => pure 0
  | some g => do ss.idOrNew (← graphTerm g)

/-- The id of a quad when every term has an id (a quad with a term that has
    no id is in no generation). -/
def Session.quadIds? (ss : Session) (t : Triple) (g : Option L4Factoidal.Storage.DeltaGraphName) :
    IO (Option Row) := do
  let some s ← ss.idOf t.s.toTerm | return none
  let some p ← ss.idOf (.iri t.p) | return none
  let some o ← ss.idOf t.o | return none
  let gid ← match g with
    | none => pure (some 0)
    | some gi => do pure ((← ss.idOf (← graphTerm gi)).map (·.toNat))
  let some gid := gid | return none
  return some ⟨s.toNat, p.toNat, o.toNat, gid⟩

/-- `SBM11_REPLAY_LOOKUP=each`: the replay looks every occurrence of every term
    up in the dictionary on its own, as it did before issue 858. The oracle of
    the differential test (group `replay` of tests/sbm11/update_where.sh); not
    for use otherwise. -/
def replayEach : IO Bool := do
  return (← IO.getEnv "SBM11_REPLAY_LOOKUP") == some "each"

/-- A graph name as a term (`graphTerm` without the error for a string that is
    not an IRI). -/
def graphTerm? : L4Factoidal.Storage.DeltaGraphName → Option Term
  | .iri g => if h : isIri g = true then some (.iri ⟨g, h⟩) else none
  | .bnode b => some (.bnode b)

/-- The terms that `stepEntry` maps to ids for the entry `e`. A graph name that
    is not an IRI or a blank node is left out: `stepEntry` refuses it. -/
def entryTerms : L4Factoidal.Storage.DeltaEntry → List Term
  | .add t g | .remove t g =>
    t.s.toTerm :: .iri t.p :: t.o :: (match g with | some gi => (graphTerm? gi).toList | none => [])
  | .clear (some g) | .drop g | .create g => (graphTerm? g).toList
  | .clear none => []

/-- Look the distinct terms of the entries that `forEach` gives up in the
    dictionary, in dictionary order, and keep their ids in `baseIds` (stage 5,
    https://github.com/danbri/factoidal/issues/858). `idOf` then answers
    those terms from `baseIds`, so the replay of a log reads each page of the
    dictionary that it needs once, in file order, in place of the page reads of
    one binary search for each occurrence of each term. The terms are
    normalised, those with an inline code are left out (they are never in the
    dictionary), the keys are sorted by `Dict.cmpBytesAt` (the order of the
    dictionary), and `Dict.lookupWalkM` walks them with a finger.
    `DictFingerTheorems.walkM_encodeDict`: the answer for each term is the
    answer of `Dict.lookupM`, in whatever order the keys come (the sort makes
    the finger useful; it does not make the answers right). The ids the delta
    log gave to terms that the dictionary does not hold (`ovIds`) are not in
    `baseIds`: `idOf` reads them from `ovIds` as before, so `idOrNew` gives the
    same ids in the same order. The caller empties `baseIds` after the replay.
    `entries` is the number of entries the caller will apply (it sizes the hash
    sets). Gives the number of terms looked up. -/
def Session.prefillBaseIds (ss : Session) (entries : Nat)
    (forEach : (L4Factoidal.Storage.DeltaEntry → IO Unit) → IO Unit) : IO Nat := do
  if ← replayEach then return 0
  -- the hash sets and maps are sized for one new term in each entry, so that they do not grow
  -- (each growth hashes every term again)
  let seen ← IO.mkRef (Std.HashSet.emptyWithCapacity entries : Std.HashSet Term)
  let terms ← IO.mkRef (#[] : Array Term)
  forEach fun e => do
    for t0 in entryTerms e do
      let t := normalizeTerm t0
      if (inlineCode? t).isNone then
        let isNew ← seen.modifyGet fun st => if st.contains t then (false, st) else (true, st.insert t)
        if isNew then terms.modify (·.push t)
  seen.set ∅
  let ts ← terms.get
  terms.set #[]
  -- (key, position in `ts`): a term has no `Inhabited` instance for the sort
  let mut items : Array (ByteArray × Nat) := Array.mkEmpty ts.size
  for h : i in [0:ts.size] do
    if let some k := termKeyBytes? ts[i] then items := items.push (k, i)
  let sorted := L4Factoidal.Qlvr.mergeSortBy items fun a b => Dict.cmpBytesAt a.1 b.1 != .gt
  let mut memo : Std.HashMap Term (Option UInt64) := Std.HashMap.emptyWithCapacity sorted.size
  let mut w : Dict.Walk := none
  for (k, i) in sorted do
    let (r, w') ← ok "lookup" (← (Dict.lookupWalkM ss.gdxFetch ss.gdvFetch ss.g.dictHdr w k).run)
    w := w'
    if h : i < ts.size then
      memo := memo.insert ts[i] (r.map (dictIdOfRank k))
  ss.baseIds.set memo
  -- the terms the dictionary does not hold get overlay ids (`idOrNew`): size `ovIds` for them
  let absent := memo.fold (fun n _ r => if r.isNone then n + 1 else n) 0
  ss.ovIds.modify fun m => if m.isEmpty then Std.HashMap.emptyWithCapacity absent else m
  return sorted.size

/-- One log entry applied to an overlay state: the terms of the entry mapped to
    ids (a term that has no id gets an overlay id, `idOrNew`), then
    `Overlay.step`. A removed quad with a term that has no id is in no
    generation and changes nothing; so does CLEAR or DROP of a graph whose name
    has no id (it holds no quad and has no slot). CREATE gives its graph name an
    id, a new overlay id when the dictionary does not hold it, and a slot. -/
def Session.stepEntry (ss : Session) (st : L4Factoidal.Storage.Sbm11.Overlay.State)
    (e : L4Factoidal.Storage.DeltaEntry) : IO L4Factoidal.Storage.Sbm11.Overlay.State := do
  match e with
  | .add t g =>
    let s ← ss.idOrNew t.s.toTerm
    let p ← ss.idOrNew (.iri t.p)
    let o ← ss.idOrNew t.o
    let gid ← ss.graphIdOrNew g
    return L4Factoidal.Storage.Sbm11.Overlay.step st (.add ⟨s, p, o, gid⟩)
  | .remove t g =>
    if let some r ← ss.quadIds? t g then
      return L4Factoidal.Storage.Sbm11.Overlay.step st (.remove r)
    return st
  | .clear none => return L4Factoidal.Storage.Sbm11.Overlay.step st (.clear 0)
  | .clear (some g) =>
    if let some x ← ss.idOf (← graphTerm g) then
      return L4Factoidal.Storage.Sbm11.Overlay.step st (.clear x.toNat)
    return st
  | .drop g =>
    if let some x ← ss.idOf (← graphTerm g) then
      return L4Factoidal.Storage.Sbm11.Overlay.step st (.drop x.toNat)
    return st
  | .create g =>
    let x ← ss.idOrNew (← graphTerm g)
    return L4Factoidal.Storage.Sbm11.Overlay.step st (.create x)

/-- The distinct graph ids other than the default graph (0) of the BASE quads,
    sorted: one scan of the graph column of the PSO permutation with the overlay
    left out. The named graphs of a generation that has no graph list. A session
    opens its permutations when it first reads them (`Session.perm`), so it does
    not use `Sbm11Gen.graphIdsOfQuads`, which reads the permutations of `openGen`.
    Until 2026-10-15 this read the overlaid generation; the log decides only
    `created` and `dropped`. -/
def Session.baseGraphIdsOfQuads (ss : Session) : IO (Array Nat) := do
  let base : Session := { ss with ovl := #[{}, {}, {}, {}] }
  let pat : IdQuery.Pat := { s := .var "s", p := .var "p", o := .var "o", g := .var "g", named := true }
  let spec := IdQuery.mkSpec pat 0 (fun v => v == "g")
  let seen ← IO.mkRef ({} : Std.HashSet Nat)
  match ← (IdQuery.scanFoldM base.store spec true () fun _ ch => do
      let mut s ← liftIO seen.get
      liftIO (seen.set {})
      for i in [0:ch.table.rows] do
        let x := (ch.table.at 0 i).toNat
        if x != 0 then s := s.insert x
      liftIO (seen.set s)
      pure ((), true)).run with
  | .error e => throw (IO.userError s!"graph scan failed: {e}")
  | .ok _ => pure ()
  return L4Factoidal.Qlvr.mergeSortBy (← seen.get).toArray (· ≤ ·)

/-- The named graphs of the base generation: the graph list GNL1, or the graph
    ids of the base quads for a generation that has no list
    (`baseGraphIdsOfQuads`), sorted; read once. -/
def Session.baseNamed (ss : Session) : IO (Array Nat) := do
  match ← ss.baseNamedRef.get with
  | some xs => return xs
  | none =>
    let xs ← match ← readGraphList ss.g with
      | some ids => pure ids
      | none => ss.baseGraphIdsOfQuads
    ss.baseNamedRef.set (some xs)
    return xs

/-- Does the named graph with id `x` exist in the overlaid generation?
    `Overlay.denoteNamed` over the base named graphs: created by the log, or a
    base named graph the log did not drop. -/
def Session.hasNamedGraph (ss : Session) (x : Nat) : IO Bool := do
  if x == 0 then return false
  let st := ss.ovState
  if st.created.contains x then return true
  if st.dropped.contains x then return false
  return L4Factoidal.Storage.Sbm11.GraphList.contains (← ss.baseNamed) x

/-- The ids of the named graphs of the overlaid generation, sorted: the base
    named graphs the log did not drop, and the graphs the log created
    (`Overlay.denoteNamed`; `created` and `dropped` are disjoint, so a base
    graph that is not dropped is in). A graph with no triple is in. -/
def Session.namedGraphIds (ss : Session) : IO (Array Nat) := do
  let base ← ss.baseNamed
  let st := ss.ovState
  let mut out : Array Nat := Array.mkEmpty (base.size + st.created.size)
  for x in base do
    if !st.dropped.contains x then out := out.push x
  for x in st.created do
    if !L4Factoidal.Storage.Sbm11.GraphList.contains base x then out := out.push x
  return L4Factoidal.Qlvr.mergeSortBy out (· ≤ ·)

/-- `storeWith` with the named graphs of the overlaid generation
    (`namedGraphIds`), which the nested evaluator reads for GRAPH
    (https://github.com/danbri/factoidal/issues/959). -/
def Session.storeNested (ss : Session) (threads : Nat) (sip : Option Nat := some 16) (minRows : Nat := 8192)
    (aggOnIds : Bool := true) : IdQuery.Store IO :=
  { ss.storeWith threads sip minRows aggOnIds with
    namedGraphs := some (liftIO do return (← ss.namedGraphIds).map (·.toUInt64)) }

/-- The session with the overlay state `st`: `ovl` cut from it per
    permutation, and the counters of `deltaText` read from it. -/
def Session.withOverlay (ss : Session) (st : L4Factoidal.Storage.Sbm11.Overlay.State) : IO Session := do
  let ovl := #[0, 1, 2, 3].map (L4Factoidal.Storage.Sbm11.Overlay.forPerm st)
  return { ss with ovl, ovState := st, ovInserts := st.ins.size, ovDeletes := st.del.size,
                    ovCleared := st.cleared.length, ovNewTerms := (← ss.ovVocab.get).size }

/-- Replay the committed batches of the generation's delta log
    (`Sbm11Delta.readBatches`) into the overlay: each entry's terms mapped to
    ids (`idOrNew` for an addition), then `Overlay.step`. -/
def Session.loadOverlay (ss : Session) : IO Session := do
  let t0 ← IO.monoNanosNow
  let (batches, logBytes, clean) ← Harness.Sbm11Delta.readBatches ss.g.dir
  let ss := { ss with deltaTorn := !clean, ovLogBytes := logBytes.size }
  if batches.isEmpty then return ss
  -- the dictionary ids of every term of the log, in dictionary order (issue 858)
  let entries := batches.foldl (fun n b => n + b.ops.length) 0
  let resolved ← ss.prefillBaseIds entries fun f => do
    for b in batches do
      for e in b.ops do f e
  -- the sets of the state are sized for the entries, so that they do not grow
  let mut st : L4Factoidal.Storage.Sbm11.Overlay.State :=
    { ins := Std.HashSet.emptyWithCapacity entries, del := Std.HashSet.emptyWithCapacity entries }
  let mut ops := 0
  for b in batches do
    for e in b.ops do
      ops := ops + 1
      st ← ss.stepEntry st e
  ss.baseIds.set {}
  let ss ← ss.withOverlay st
  let t1 ← IO.monoNanosNow
  return { ss with deltaBatches := batches.length, deltaOps := ops, replayTerms := resolved, replayNs := t1 - t0 }

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

/-! ## The reference fallback -/

/-- Every row of permutation `perm` with key prefix `key`, all graphs: `f`
    gets the four columns of each block's rows. -/
def scanAll (ss : Session) (perm : Nat) (key : Array UInt64)
    (f : Array ByteArray → Nat → IO Unit) : IO Unit := do
  let spec : IdQuery.ScanSpec := { perm, key, checks := #[], named := false,
                                   outVars := #["c0", "c1", "c2", "g"], outCols := #[0, 1, 2, 3], eqs := #[] }
  match ← (IdQuery.scanFoldM ss.store spec true () fun _ ch => do
      liftIO (f ch.table.cols ch.table.rows)
      pure ((), true)).run with
  | .ok _ => pure ()
  | .error e => throw (IO.userError e)

def subjectOf (t : Term) : IO Subject :=
  match t with
  | .iri i => pure (.iri i)
  | .bnode b => pure (.bnode b)
  | _ => throw (IO.userError "a subject or graph name that is not an IRI or a blank node")

/-- The quads the planner guard selects, as the dataset they denote, with every
    named graph of the overlaid generation that the guard keeps: a named graph
    with no selected quad (a graph with no triple, or a graph whose triples have
    none of the selected predicates) is in the dataset with no triple. SPARQL 1.1
    Query section 13: the named graphs of the dataset are its graph names, so
    `GRAPH ?g { }` gives one solution for each, and FROM NAMED selects one with no
    triple (2026-10-15, https://github.com/danbri/factoidal/issues/855). A graph
    that the predicate selection empties contributes no solution to a pattern of
    the planner fragment with or without it (`evalPatternBackend_restrict`). -/
def selectedDataset (ss : Session) (q : Query) (extraGraphs : List WfIri := []) : IO (Dataset × String) := do
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
    -- graphs the caller reads that the query text does not name (`WITH <g>` of
    -- an update makes `g` the graph the default-graph patterns read)
    for v in extraGraphs do
      if let some x ← ss.idOf (.iri v) then a := a.push x
    allowed := some a
  let rowsRef ← IO.mkRef (#[] : Array (UInt64 × UInt64 × UInt64 × UInt64))
  -- (s, p, o, g) of each kept row
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
      | _ => throw (IO.userError "a predicate that is not an IRI")
    let ot ← ss.termOf o
    let gr : Option Subject ← if g == 0 then pure none else pure (some (← subjectOf (← ss.termOf g)))
    quads := quads.push (gr, { s := st, p := pt, o := ot })
  -- the named graphs that hold no selected quad
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

/-- Write a graph (CONSTRUCT, DESCRIBE) as N-Triples lines; returns the
    number of triples. -/
def emitGraph (graph : Graph) (emit : ByteArray → IO Unit) : IO Nat := do
  let mut n := 0
  for tr in graph do
    match nquadLine (match tr.s with | .iri i => .iri i | .bnode b => .bnode b) (.iri tr.p) tr.o none with
    | .ok l =>
      emit (l ++ "\n").toUTF8
      n := n + 1
    | .error e => throw (IO.userError e)
  return n

/-- The query's environment for expressions (NOW read once, BASE, the
    GeoSPARQL extension functions), without a dataset: the id path's
    post-processing and residual FILTERs (issue 823) read no EXISTS. The
    reference fallback adds its dataset (`runReference`). The theorem for the
    WHERE clause under this environment:
    `HarnessWhereTheorems.harness_where_allowed`. -/
def queryEnv (q : Query) : IO EvalEnv := do
  let clockEnv ← L4Wasm.Ops.emptyEnvNow
  return IdGroup.queryEnvOf clockEnv q.base

/-- Write the answer of a post-processed id plan (issue 823) as
    `runReference` writes the reference evaluator's answer of the same form. -/
def emitPost (ans : IdQuery.PostAnswer) (emit : ByteArray → IO Unit) : IO Unit := do
  match ans with
  | .solutions vars rows => emit (QueryResult.bindings vars rows).toSrjFast.toUTF8
  | .boolean b => emit (QueryResult.boolean b).toSrjFast.toUTF8
  | .graph g => discard <| emitGraph g emit

/-- The reference evaluator over the selected dataset (the evaluation of
    `Harness/QuadQuery.lean`'s `finish`). -/
def runReference (ss : Session) (q : Query) (reason : String) (emit : ByteArray → IO Unit) :
    IO (Nat × String) := do
  let (ds, what) ← selectedDataset ss q
  let clockEnv ← L4Wasm.Ops.emptyEnvNow
  let (applied, _) := applyDataset q.dataset ds ds.default
  let stripped := stripDatasetClauses q
  let env : EvalEnv := { clockEnv with dataset := some applied, ext := L4Factoidal.Geo.extFns, base := q.base }
  let indexed := L4Factoidal.Storage.QuadDataset.namesAreIris applied
  let line := s!"path=reference reason=\"{reason}\" {what}"
  match stripped.serviceFailure env applied with
  | some f => throw (IO.userError f.message)
  | none =>
  match q.form with
  | .select _ =>
    let rows? :=
      if indexed then StoreDataset.runSelectQueryBackendDataset env stripped (StoreDataset.indexedDatasetBackend applied)
      else some (evalSelect env applied stripped).2
    -- The backend runner answers `none` for a query it hands to the reference
    -- evaluator (`text:query`, StoreDataset.runSelectQueryBackendDataset).
    let rows := match rows? with
      | some rows => rows
      | none => (evalSelect env applied stripped).2
    emit (QueryResult.bindings q.projectedVars rows).toSrjFast.toUTF8
    return (rows.length, line)
  | .ask =>
    let answer? :=
      if indexed then StoreDataset.runAskQueryBackendDataset env stripped (StoreDataset.indexedDatasetBackend applied)
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
  plan : Array String := #[]

def parse (text : String) (base : Option String) (version : SparqlVersion := .v11) : IO Query :=
  match parseSparql text base version with
  | .error e => throw (IO.userError s!"SPARQL parse error at {e.pos}: {e.msg}")
  | .ok q => pure q

/-- Run one parsed query on an open session. -/
def runOne (ss : Session) (q : Query) (emit : ByteArray → IO Unit) (forceReference referenceRender : Bool)
    (threads : Nat := 1) (sip : Option Nat := some 16) (aggOnIds : Bool := true) : IO Outcome := do
  let plan? := if forceReference then .error "--reference" else IdQuery.translate q
  match plan? with
  | .error reason =>
    let (n, line) ← runReference ss q reason emit
    return { rows := n, path := line }
  | .ok plan =>
    -- issue 961: blocked pool workers poll again from here, so the first
    -- divided phase does not wait for a kernel wake-up. Only for a plan with
    -- two or more triple patterns (joins, then the steps after them): DBpedia
    -- d17, one pattern answered from the PRM1 entries in 0.3 ms, took 0.37 ms
    -- at 4 threads against 0.29 ms with every query waking the workers.
    if plan.pats.size ≥ 2 then
      if let some p := ss.pool then p.wake
    let minRows ← minRangeRows
    let par := if threads ≤ 1 then none else some (ss.par threads minRows)
    let env ← queryEnv q
    match plan.post with
    | some ps =>
      if plan.nested.isSome then
        -- issue 959: a nested WHERE clause, the recursive evaluator on ids
        match ← (IdGroup.runNestedM (ss.storeNested threads sip minRows aggOnIds) plan ps env).run with
        | .ok (ans, st) =>
          emitPost ans emit
          return { rows := st.rows, path := "path=ids", plan := st.plan }
        | .error e => refusedOr e
      else
      -- issue 823: the WHERE clause on ids, the reference post-processing on
      -- the decoded solutions
      match ← (IdQuery.runPostM (ss.storeWith threads sip minRows aggOnIds) plan ps env).run with
      | .ok (ans, st) =>
        emitPost ans emit
        return { rows := st.rows, path := "path=ids", plan := st.plan }
      | .error e => refusedOr e
    | none =>
    -- `runPlanM` refuses (issue 954) before it emits anything
    match ← (IdQuery.runPlanM (ss.storeWith threads sip minRows) plan emit referenceRender par env).run with
    | .ok st => return { rows := st.rows, path := "path=ids", plan := st.plan }
    | .error e => refusedOr e
where
  /-- An id-path error that starts with `refused: ` (issue 954: a shape the
      id path recognises only after reading the store) runs the reference
      evaluator; any other error fails the query. -/
  refusedOr (e : String) : IO Outcome := do
    if e.startsWith "refused: " then
      let (n, line) ← runReference ss q (e.drop 9).toString emit
      return { rows := n, path := line }
    throw (IO.userError s!"id query failed: {e}")

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
                      streamPerThread := ((← IO.getEnv "SBM11_STREAM_JOBS").bind String.toNat?).getD IdQuery.streamJobsPerThread }
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
