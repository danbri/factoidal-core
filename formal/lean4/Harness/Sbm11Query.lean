/-
Harness/Sbm11Query — `l4sbm11 query` and `l4sbm11 serve`: SPARQL over an SBM11
generation (stage 4, https://github.com/danbri/factoidal/issues/790).

  l4sbm11 query GEN ('SPARQL' | --file Q.rq) [--base IRI] [--explain]
                [--repeat N] [--reference-render] [--reference]
                [--verify merkle|none] [--threads N] [--sip auto|always|off]
                [--sparql12]
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
line of SPARQL JSON per query.

This is a HARNESS: it does file I/O. The query engine is
`L4Factoidal.Storage.Sbm11.IdQuery`.
-/
import Harness.Sbm11Gen
import Harness.Sbm11Delta
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.ParallelScan
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.PrmAt
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.DictRange
import L4Factoidal.Storage.Sbm11.FrameWords
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.Geo.Functions
import Wasm.Ops.Clock
import Std.Sync.Mutex
import Std.Data.TreeMap

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
  prmLeaves : List L4Factoidal.Storage.BlockMerkle.Digest
  prmCache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  /-- the block count of the PRM1 header -/
  count : Nat
  /-- the answers of `rangeM` for the keys asked so far (the generation does
      not change while it is open); at most 256 keys, emptied when full -/
  ranges : IO.Ref (Std.HashMap (Array UInt64) (Array BlockMeta))

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
  replayNs : Nat := 0
  /-- the log ended with a torn final frame (an append that did not
      complete), left out of the replay (issue 843) -/
  deltaTorn : Bool := false
  /-- the replayed overlay state (`ovl` is its cut per permutation); `l4sbm11
      update` (`Harness/Sbm11Update.lean`) applies the entries of a request to
      it, so that each operation reads the state the one before left -/
  ovState : L4Factoidal.Storage.Sbm11.Overlay.State := {}
  /-- the size in bytes of the log file the replay read (0: no log); a
      positioned append of `l4sbm11 update` uses it -/
  ovLogBytes : Nat := 0

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
  return { g := { g0 with dictHdr }, termCount := dictHdr.termCount,
           perms := ← IO.mkRef #[none, none, none, none],
           pages := ← IO.mkRef {}, frameBytes := ← IO.mkRef 0, prmBytes := ← IO.mkRef 0,
           lookups := ← IO.mkRef 0,
           gdx := ← IO.mkRef none, ovVocab := ← IO.mkRef #[], ovIds := ← IO.mkRef {},
           lock := ← Std.Mutex.new (), dictLock := ← Std.Mutex.new (), taskPages := ← IO.mkRef {} }

/-- A positioned read of a PRM1 file (`PrmRange`'s `read`): under `none` one
    `pread` of exactly the bytes, under `merkle` through the file's verified
    chunk cache (one read at a time: the cache is shared, issue 799). -/
def Session.prmReadAt (ss : Session) (path : String) (ref : Ref)
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
    let count ← match ← (PrmRange.openM (ss.prmReadAt prmPath prmA.merkle prmLeaves prmCache) prmA.bytes p).run with
      | .ok n => pure n
      | .error e => throw (IO.userError s!"{prmPath}: {e}")
    let leaves ← loadLeaves ss.g.verify ss.g.fileBytes prbPath prbA.merkle
    let cache ← newChunkCache ss.g.verify prbA.merkle
    let lp : LoadedPerm := { prbPath, prbRef := prbA.merkle, leaves, cache, prmPath, prmRef := prmA.merkle,
                             prmLeaves, prmCache, count, ranges := ← IO.mkRef {} }
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
    ss.gdx.set (some b)
    return b

def Session.gdxFetch (ss : Session) (off len : Nat) : IO ByteArray := do
  if ss.g.verify == .none then
    return (← verifiedRead ss.g ss.g.gdxPath ss.g.gdxRef ss.g.gdxLeaves ss.g.gdxCache off len)
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
    return (← verifiedRead ss.g ss.g.gdvPath ss.g.gdvRef ss.g.gdvLeaves ss.g.gdvCache off len)
  let cb := ss.g.gdvRef.chunkBytes
  let first := off / cb
  let last := (off + len - 1) / cb
  let mut out := ByteArray.emptyWithCapacity len
  for c in [first:last + 1] do
    match ← Harness.PosixRangeIO.readVerifiedChunkCached? ss.g.gdvPath ss.g.gdvRef ss.g.gdvLeaves ss.g.gdvCache c with
    | some (chunk, fp) =>
      ss.g.fetchedBytes.modify (· + fp.fetchedBytes)
      ss.g.fileBytes.modify (· + fp.fetchedBytes)
      let lo := max off (c * cb) - c * cb
      let hi := min (off + len) ((c + 1) * cb) - c * cb
      if hi > chunk.size then throw (IO.userError s!"GDV1: chunk {c} is short")
      out := chunk.copySlice lo out out.size (hi - lo)
    | none => throw (IO.userError s!"GDV1: chunk {c} refused")
  return out

/-- The keys of dictionary page `pg`, packed: one byte array holding the keys
    one after the other and the start of each key (and the end of the last).
    One object per page: a cache of 64 separate key arrays per page left the
    heap fragmented (q19: peak RSS 98 MB against 31 MB with a cache of 64
    pages, and slower, each new huge page being cleared on first touch). The
    cache holds at most `SBM11_PAGES` pages (default 2,048) and is emptied
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
    `SBM11_PAGES` pages (default 2,048; 0: no cache). -/
def cachePage (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit := do
  let lim := ((← IO.getEnv "SBM11_PAGES").bind String.toNat?).getD 2048
  if lim > 0 then
    c.modify fun m => (if m.size ≥ lim then {} else m).insert pg ks

/-- Put page `pg` in a task view's own cache (issue 799, stage 1b): emptied
    first when it holds `SBM11_TASK_PAGES` pages (default 1,024), and never
    more than `SBM11_PAGES`. A task's cache holds copies of pages that
    `taskPages` also holds. Olympics q19 at 4 threads, 7 runs per process
    (2026-10-13): 2,048 pages per task, 74 ms and 156 MB peak RSS; 1,024, 54
    ms and 125 MB; 256, 84 ms and 106 MB (36 MB at 1 thread, 47 MB at 4
    threads with no page cache at all). A block of 4,096 rows can need more
    pages than a small cache holds, and its prefetched pages then empty it. -/
def cacheTaskPage (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit := do
  let all := ((← IO.getEnv "SBM11_PAGES").bind String.toNat?).getD 2048
  let lim := min all (((← IO.getEnv "SBM11_TASK_PAGES").bind String.toNat?).getD 1024)
  if lim > 0 then
    c.modify fun m => (if m.size ≥ lim then {} else m).insert pg ks

/-- A copy of a page made by the calling thread. A page in `taskPages` is
    reachable from every task, so taking and releasing a reference to it is an
    atomic operation on one cache line from every thread that renders with it;
    each task and the session keep their own copy (about 2 KB). -/
def copyPage (ks : ByteArray × Array Nat) : ByteArray × Array Nat :=
  (ks.1.extract 0 ks.1.size, ks.2.extract 0 ks.2.size)

/-- Put an entry in `taskPages` (call under `dictLock`), emptied first when
    it holds `SBM11_PAGES` entries. -/
def Session.putTaskPage (ss : Session) (pg : Nat) (e : TaskPage) : IO Unit := do
  let lim := ((← IO.getEnv "SBM11_PAGES").bind String.toNat?).getD 2048
  if lim > 0 then
    ss.taskPages.modify fun m => (if m.size ≥ lim then {} else m).insert pg e

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
  cacheTaskPage ss.pages pg ks
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
  for c in [0:t.cols.size] do
    for i in [0:min n t.rows] do
      let x := t.at c i
      let tag := (x >>> 60).toNat
      if isDictTag tag then
        let rank := (x &&& 0x0FFFFFFFFFFFFFFF).toNat
        if rank < ss.termCount then
          let pg := rank / Dict.pageTerms
          if !seen.contains pg && !localPages.contains pg then
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
  for (pg, ks) in got ++ loaded do cacheTaskPage ss.pages pg (copyPage ks)
  for (pg, p) in waits do
    match ← IO.wait p.result? with
    | some (.ok ks) => cacheTaskPage ss.pages pg (copyPage ks)
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
    let tp ← ss.taskPages.get
    if !tp.isEmpty then
      if let some (.ready ks) := tp.get? pg then
        let ks := copyPage ks
        cachePage ss.pages pg ks
        return ks
    let ks ← ss.loadPage pg
    cachePage ss.pages pg ks
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
  let kb ← ss.keyOf x
  let k := kb.data.toList
  if classTag k != tag then throw (IO.userError s!"id {id}: tag differs from the key's class")
  match decodeKey? k with
  | some t => return t
  | none => throw (IO.userError s!"id {id}: key does not decode")

def Session.idOf (ss : Session) (t : Term) : IO (Option UInt64) := do
  ss.lookups.modify (· + 1)
  let t := normalizeTerm t
  match inlineCode? t with
  | some c => return some c.toUInt64
  | none =>
    match termKeyBytes? t with
    | none => return none
    | some k =>
      let (r, _) ← ok "lookup" (← (Dict.lookupM ss.gdxFetch ss.gdvFetch ss.g.dictHdr k).run)
      match r with
      | some r => return some (dictCode k.data.toList r).toUInt64
      | none =>
        -- a term the delta log added (stage 5)
        return ((← ss.ovIds.get).get? t).map fun n =>
          (L4Factoidal.Storage.Sbm11.Overlay.tagDelta * two60 + n).toUInt64

def Session.lowerBound (ss : Session) (k : ByteArray) : IO Nat := do
  ok "lower bound" (← (DictRange.lowerBoundM ss.gdxFetch ss.gdvFetch ss.g.dictHdr k).run)

/-- The PRM1 entries of the blocks of permutation `p` that may hold a row
    with the key prefix (`Store.blocksForRange`): `PrmRange.rangeM` over
    `PrmRange.bytesReader` of the permutation's positioned reads, the code of
    `PrmRangeTheorems.rangeM_bytes`; an answer is kept for the next query
    with the same key. -/
def Session.rangeFor (ss : Session) (p : Nat) (key : Array UInt64) : IO (Array BlockMeta) := do
  let lp ← ss.perm p
  if let some r := (← lp.ranges.get).get? key then return r
  let read := ss.prmReadAt lp.prmPath lp.prmRef lp.prmLeaves lp.prmCache
  let r ← match ← (PrmRange.rangeM (PrmRange.bytesReader read lp.count) key).run with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{lp.prmPath}: {e}")
  lp.ranges.modify fun m => (if m.size ≥ 256 then {} else m).insert key r
  return r

def Session.prb (ss : Session) (p off len : Nat) : IO ByteArray := do
  let lp ← ss.perm p
  ss.frameBytes.modify (· + len)
  match ss.g.verify with
  | .merkle =>
    -- the chunk cache is one shared table: one read at a time (issue 799)
    ss.lock.atomically (verifiedRead ss.g lp.prbPath lp.prbRef lp.leaves lp.cache off len)
  | .none => verifiedRead ss.g lp.prbPath lp.prbRef lp.leaves lp.cache off len

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
  return { v with pages := ← IO.mkRef {} }

/-- Add the counters of a finished task view to the session. -/
def Session.absorb (ss v : Session) : IO Unit := do
  ss.frameBytes.modify (· + (← v.frameBytes.get))
  ss.prmBytes.modify (· + (← v.prmBytes.get))
  ss.lookups.modify (· + (← v.lookups.get))
  ss.g.readBytes.modify (· + (← v.g.readBytes.get))
  ss.g.fetchedBytes.modify (· + (← v.g.fetchedBytes.get))
  ss.g.fileBytes.modify (· + (← v.g.fileBytes.get))

def liftIO {α : Type} (x : IO α) : ExceptT String IO α := ExceptT.lift x

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
    prefetch := some fun t n => liftIO (ss.prefetch t n) }

/-! ## Parallel block scans (stage 1, issue 799) -/

/-- The table of `IdQuery.scanTableM`, computed with the selected blocks cut
    into at most `threads` consecutive chunks. Each chunk is scanned by its
    own dedicated task (`IO.asTask`) with the same loop
    (`IdQuery.scanListM`), the chunk tables are appended in chunk order and
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
  -- stage 1b: at most `IdQuery.rangeCount` ranges; fewer than 2: one thread
  let n := IdQuery.rangeCount threads minRows (IdQuery.selRows metas)
  if threads ≤ 1 || ox.on || n < 2 then return ← IdQuery.scanTableM st spec
  let sortVar := IdQuery.sortVarOf spec
  let sel := List.range metas.size
  let c := (sel.length + n - 1) / n
  let chunks := L4Factoidal.Storage.Sbm11.ParallelScan.chunksOf c sel
  let cap := 8 * IdQuery.selRows metas
  let init : L4Factoidal.Qlvr.Table :=
    { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity cap,
      rows := 0, sortVar }
  let f := fun (acc : L4Factoidal.Qlvr.Table) (ch : IdQuery.Chunk) =>
    (pure (acc.append ch.table, true) : ExceptT String IO (L4Factoidal.Qlvr.Table × Bool))
  -- each task: its own view (counters, dictionary state, permutation copies)
  let mut tasks : Array (Task (Except IO.Error (L4Factoidal.Qlvr.Table × IdQuery.ScanStats)) × Session) := #[]
  for X in chunks do
    let v ← ss.view
    let t ← IO.asTask (prio := .dedicated) (do
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
      let capX := 8 * X.foldl (fun a i => a + metas[i]!.rows) 0
      let init : L4Factoidal.Qlvr.Table :=
        { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity capX,
          rows := 0, sortVar }
      match ← (IdQuery.scanListM v.store spec true init f metas sortVar ox X).run with
      | .ok r => pure r
      | .error e => throw (IO.userError e))
    tasks := tasks.push (t, v)
  let mut out := init
  let mut stats : IdQuery.ScanStats := { blocksTotal := ← st.blockCount spec.perm }
  let mut failure : Option String := none
  for (t, v) in tasks do
    match ← IO.wait t with
    | .ok (tab, s) =>
      out := out.append tab
      stats := stats.add s
    | .error e => if failure.isNone then failure := some (toString e)
    -- the counters of every task are added, failed or not
    ss.absorb v
  if let some e := failure then throw e
  return (out, stats)

/-- `IdQuery.Par.fold` on this session (issue 799, stage 1b): one dedicated
    task per chunk of blocks, each on its own view (`Session.view`), at most
    `window` tasks at once; the results are folded with `g` in chunk order as
    they finish, and the next task starts when one is folded, so at most
    `window` results wait in memory. The counters of every task are added
    (`Session.absorb`), failed or not; after a failure no task starts. -/
def parFold (ss : Session) (window : Nat) {α β : Type}
    (job : IdQuery.Store IO → List Nat → ExceptT String IO α) (chunks : List (List Nat)) (init : β)
    (g : β → α → ExceptT String IO β) : ExceptT String IO β := do
  let arr := chunks.toArray
  let spawn (X : List Nat) : IO (Task (Except IO.Error α) × Session) := do
    let v ← ss.view
    let t ← IO.asTask (do
      let w ← v.local
      match ← (job w.store X).run with
      | .ok r => pure r
      | .error e => throw (IO.userError e))
    pure (t, v)
  let mut queue : Array (Task (Except IO.Error α) × Session) := #[]
  let mut next := 0
  for _ in [0:max window 1] do
    if next < arr.size then
      queue := queue.push (← liftIO (spawn arr[next]!))
      next := next + 1
  let mut acc := init
  let mut failure : Option String := none
  for _ in [0:arr.size] do
    let some (t, v) := queue[0]? | break
    queue := queue.extract 1 queue.size
    let r ← liftIO (IO.wait t)
    liftIO (ss.absorb v)
    match r with
    | .ok a =>
      if failure.isNone then
        match ← liftIO (g acc a).run with
        | .ok b => acc := b
        | .error e => failure := some e
    | .error e => if failure.isNone then failure := some (toString e)
    if failure.isNone && next < arr.size then
      queue := queue.push (← liftIO (spawn arr[next]!))
      next := next + 1
  if let some e := failure then throw e
  return acc

/-- The divided single-pattern paths of `IdQuery.runPlanM` with `threads`
    tasks at once (issue 799, stage 1b). -/
def Session.par (ss : Session) (threads : Nat) (minRows : Nat := 8192) : IdQuery.Par IO :=
  { threads, minRows, fold := fun job chunks init g => parFold ss threads job chunks init g }

/-- `SBM11_MIN_RANGE_ROWS`: the fewest estimated rows per block range
    (`IdQuery.rangeCount`; default 8,192; 0: one range per thread, as the
    gate fixture tests use to divide scans of a few rows). -/
def minRangeRows : IO Nat := do
  return ((← IO.getEnv "SBM11_MIN_RANGE_ROWS").bind String.toNat?).getD 8192

/-- The session's store with `threads` scan tasks per BGP scan (1: the
    single-thread store, `scanTable` unset). -/
def Session.storeWith (ss : Session) (threads : Nat) (sip : Option Nat := some 16) (minRows : Nat := 8192) :
    IdQuery.Store IO :=
  let base := { ss.store with sipFactor := sip }
  if threads ≤ 1 then base
  else { base with scanTable := some fun spec => scanTableParM ss spec threads minRows }

/-! ## The delta overlay (stage 5) -/

/-- The id of `t`: its base id, its overlay id, or a new overlay id. -/
def Session.idOrNew (ss : Session) (t0 : Term) : IO Nat := do
  match ← ss.idOf t0 with
  | some x => pure x.toNat
  | none =>
    let t := normalizeTerm t0
    if (termKeyBytes? t).isNone then
      throw (IO.userError s!"delta log: a term the SBM11 dictionary does not admit: {repr t}")
    -- one step that reads the size and pushes: a `get` before the `modify` leaves a second
    -- reference to the array, and every push then copies it (quadratic replay)
    let n ← ss.ovVocab.modifyGet fun vocab => (vocab.size, vocab.push t)
    ss.ovIds.modify (·.insert t n)
    pure (L4Factoidal.Storage.Sbm11.Overlay.tagDelta * two60 + n)

/-- A graph name of a DLOG entry as a term. -/
def graphTerm (g : Iri) : IO Term :=
  if h : isIri g = true then pure (.iri ⟨g, h⟩)
  else throw (IO.userError s!"delta log: graph name is not an IRI: {g}")

def Session.graphIdOrNew (ss : Session) : Option Iri → IO Nat
  | none => pure 0
  | some g => do ss.idOrNew (← graphTerm g)

/-- The id of a quad when every term has an id (a quad with a term that has
    no id is in no generation). -/
def Session.quadIds? (ss : Session) (t : Triple) (g : Option Iri) : IO (Option Row) := do
  let some s ← ss.idOf t.s.toTerm | return none
  let some p ← ss.idOf (.iri t.p) | return none
  let some o ← ss.idOf t.o | return none
  let gid ← match g with
    | none => pure (some 0)
    | some gi => do pure ((← ss.idOf (← graphTerm gi)).map (·.toNat))
  let some gid := gid | return none
  return some ⟨s.toNat, p.toNat, o.toNat, gid⟩

/-- One log entry applied to an overlay state: the terms of the entry mapped to
    ids (a term that has no id gets an overlay id, `idOrNew`), then
    `Overlay.step`. A removed quad with a term that has no id is in no
    generation and changes nothing. -/
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
  | .clear (some g) | .drop g =>
    if let some x ← ss.idOf (← graphTerm g) then
      return L4Factoidal.Storage.Sbm11.Overlay.step st (.clear x.toNat)
    return st
  | .create _ => return st

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
  let mut st : L4Factoidal.Storage.Sbm11.Overlay.State := {}
  let mut ops := 0
  for b in batches do
    for e in b.ops do
      ops := ops + 1
      st ← ss.stepEntry st e
  let ss ← ss.withOverlay st
  let t1 ← IO.monoNanosNow
  return { ss with deltaBatches := batches.length, deltaOps := ops, replayNs := t1 - t0 }

/-- Open a generation with its delta log replayed (the session every query,
    serve and compaction uses). -/
def openOverlaid (v : Verify) (dir0 : String) : IO Session := do
  (← openSession v dir0).loadOverlay

def Session.deltaText (ss : Session) : String :=
  s!"delta batches {ss.deltaBatches}, entries {ss.deltaOps}, overlay inserts {ss.ovInserts}, deletes {ss.ovDeletes}, cleared graphs {ss.ovCleared}, new terms {ss.ovNewTerms}, replay ms {ms 0 ss.replayNs}" ++
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

/-- The quads the planner guard selects, as the dataset they denote. -/
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
  for (s, p, o, g) in rows do
    let st ← subjectOf (← ss.termOf s)
    let pt ← match ← ss.termOf p with
      | .iri i => pure i
      | _ => throw (IO.userError "a predicate that is not an IRI")
    let ot ← ss.termOf o
    let gr : Option Subject ← if g == 0 then pure none else pure (some (← subjectOf (← ss.termOf g)))
    quads := quads.push (gr, { s := st, p := pt, o := ot })
  let graphsText := match graphs with
    | some gs => s!"graphs={gs.length}"
    | none => "graphs=all"
  return (L4Factoidal.Storage.QuadDataset.datasetOfQuads quads.toList,
          s!"{what} {graphsText} quads={quads.size}")

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
    reference fallback adds its dataset (`runReference`). -/
def queryEnv (q : Query) : IO EvalEnv := do
  let clockEnv ← L4Wasm.Ops.emptyEnvNow
  return { clockEnv with ext := L4Factoidal.Geo.extFns, base := q.base }

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
    (threads : Nat := 1) (sip : Option Nat := some 16) : IO Outcome := do
  let plan? := if forceReference then .error "--reference" else IdQuery.translate q
  match plan? with
  | .error reason =>
    let (n, line) ← runReference ss q reason emit
    return { rows := n, path := line }
  | .ok plan =>
    let minRows ← minRangeRows
    let par := if threads ≤ 1 then none else some (ss.par threads minRows)
    let env ← queryEnv q
    match plan.post with
    | some ps =>
      -- issue 823: the WHERE clause on ids, the reference post-processing on
      -- the decoded solutions
      match ← (IdQuery.runPostM (ss.storeWith threads sip minRows) plan ps env).run with
      | .ok (ans, st) =>
        emitPost ans emit
        return { rows := st.rows, path := "path=ids", plan := st.plan }
      | .error e => throw (IO.userError s!"id query failed: {e}")
    | none =>
    match ← (IdQuery.runPlanM (ss.storeWith threads sip minRows) plan emit referenceRender par env).run with
    | .ok st => return { rows := st.rows, path := "path=ids", plan := st.plan }
    | .error e => throw (IO.userError s!"id query failed: {e}")

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
  let t1 ← IO.monoNanosNow
  let openBytes ← ss.g.fileBytes.get
  let stdout ← IO.getStdout
  let runs := max o.repeatN 1
  let mut execs : Array Nat := #[]
  let mut last : Option Outcome := none
  for k in [0:runs] do
    let final := k + 1 == runs
    -- the opened permutations, the verified chunk caches and the
    -- dictionary page cache persist from run to run, as in an open store
    ss.frameBytes.set 0
    ss.prmBytes.set 0
    ss.g.fetchedBytes.set 0
    let a ← IO.monoNanosNow
    let r ← runOne ss q (if final then fun s => stdout.write s else fun _ => pure ()) o.reference o.referenceRender
      o.threads o.sip
    let b ← IO.monoNanosNow
    execs := execs.push (b - a)
    last := some r
  stdout.write "\n".toUTF8
  stdout.flush
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
    IO.eprintln "usage: l4sbm11 query GEN ('SPARQL' | --file Q.rq) [--base IRI] [--explain] [--repeat N] [--reference-render] [--reference] [--verify merkle|none] [--threads N] [--sip auto|always|off] [--sparql12] | serve GEN [--verify merkle|none] [--sparql12] | prm-check GEN | frame-check GEN"
    return 2

end Harness.Sbm11Query
