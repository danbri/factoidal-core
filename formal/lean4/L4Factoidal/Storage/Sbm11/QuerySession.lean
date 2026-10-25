/-
L4Factoidal.Storage.Sbm11.QuerySession — SPARQL over an SBM11 generation
through host byte reads: the query command logic of `l4sbm11 query` as library
functions (https://github.com/danbri/factoidal/issues/1009 KR1, on the medium
interface of https://github.com/danbri/factoidal/issues/1010 KR1).

Until 2026-10-25 this code was `Harness/Sbm11Query.lean`, which read the files
with `IO.FS` and POSIX `pread`; the wasm module could not build it
(`Wasm/build-wasm.sh` skips every `Harness_*` unit). Now:

* `Reads` is the five byte reads a session makes: GDX1 and GDV1 ranges, PRM1
  and PRB1 ranges of a permutation, and the GNL1 graph list. The session never
  reads a file in any other way.
* `Core` is the session state: the manifest, the dictionary header, the
  opened permutations, the caches, the delta overlay and the counters.
* `SessionOps σ` is what a session type adds to its `Core`: where a
  dictionary page comes from (`pageKeys`), a prefetch hint and a phase clock.
  `Core` itself is an instance (one thread, one page cache). The native
  harness's session (`Harness/Sbm11Query.lean`, `--threads N`, the worker pool
  of issue 961, Merkle-checked reads) is another instance, and calls these
  same functions; only its page source and its divided scans are its own.
* `openMedium` opens a generation over a `Medium.Medium IO`
  (`Storage/Medium.lean`): it resolves `CURRENT`, decodes the manifest,
  checks the length of every file, reads the GDX1 header and replays the delta
  log. Reads are exact byte ranges inside the manifest's length of each file
  (the `--verify none` reads of the native session); no Merkle proof is checked
  over a medium in this landing.

The query: `runOneWith` translates the query to the id fragment
(`IdQuery.translate`) and runs it on ids (`IdQuery.runPlanM`, `runPostM`,
`IdGroup.runNestedM`), or runs the reference evaluator over the quads the
planner guard selects (`selectedDataset`, `runReference`). The id path's
theorem over the files' bytes is `FileGenTheorems.harness_where_allowed_file`
(stage `sbm11WhereStage`); over a medium it holds under the named assumption
`MediumReadsWritten` (stage `sbm11Medium`, `Dataflow/Instances.lean`). The
caches are not covered by a theorem (as for the native session).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Medium
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.IdGroup
import L4Factoidal.Storage.Sbm11.QueryEnv
import L4Factoidal.Storage.Sbm11.TermKeyFast
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.PrmAt
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.DictRange
import L4Factoidal.Storage.Sbm11.DictFinger
import L4Factoidal.Storage.Sbm11.MemoCache
import L4Factoidal.Storage.Sbm11.GraphList
import L4Factoidal.Storage.Sbm11.Manifest
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.SelectedDataset
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.DeltaLogBytes
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.RDF.Sink
import L4Factoidal.Geo.Functions
import L4Factoidal.Qlvr.Sort
import L4Factoidal.Dataflow.Store
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.QuerySession

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Manifest

/-! ## Helpers -/

/-- An `Except` as an `IO` value; the error text is prefixed by `what`. -/
def okIO {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def liftIO {α : Type} (x : IO α) : ExceptT String IO α := ExceptT.lift x

/-- The name of the manifest file of a generation. -/
def manifestFile : String := "manifest.sbm11"

/-- The name of the delta log of a generation (`Harness/Sbm11Delta.lean`). -/
def deltaLogFile : String := "deltas.dlog"

/-- The name of the compacted-epoch marker (`Harness/CompactedEpoch.lean`). -/
def compactedEpochFile : String := "compacted.epoch"

/-- The artifact of a role, or an error that names it. -/
def artifactIO (m : Manifest) (role : String) : IO Artifact :=
  match artifactOf? m role with
  | some a => pure a
  | none => throw (IO.userError s!"manifest has no artifact {role}")

/-- The upper-case permutation name of a permutation code: PSO, POS, SPO, OSP. -/
def permRoleName (p : Nat) : String := ((permNames[p]?).getD "").toUpper

/-- The N-Quads line of a quad of terms, without its line break: the line of
the serialiser layer (`Sink.nquadsLineOfTerms`), RDF 1.2 syntax. -/
def nquadLine (s p o : Term) (gname : Option Term) : Except String String :=
  Sink.nquadsLineOfTerms .rdf12 s p o gname

/-- The committed batches of a delta log that its base does not hold, and
`true` when no torn final frame follows them (`Harness/Sbm11Delta.lean`'s
`readBatches` over the bytes): the log decoded by
`DeltaLogBytes.parseLogCheckedBA`, its history checked by
`validBatchHistory`, and the batches after the compacted epoch `baseEpoch`
kept (`replayBatchesSinceEpoch?`). -/
def batchesOfLog (bytes : ByteArray) (baseEpoch : Option Nat) : Except String (List DeltaBatch × Bool) :=
  match DeltaLogBytes.parseLogCheckedBA bytes with
  | .error e => .error e
  | .ok (batches, torn) =>
    if !validBatchHistory batches then
      .error "DLOG batch sequence or epoch order is invalid"
    else
      match replayBatchesSinceEpoch? baseEpoch batches with
      | some replay => .ok (replay, !torn)
      | none => .error "DLOG epochs do not form a compacted-prefix/replay-suffix history"

/-- The epoch of a compacted-epoch marker (`Harness/CompactedEpoch.lean`'s
`read?` over the bytes). -/
def epochOfMarker (bytes : ByteArray) : Except String Nat :=
  match parseEpoch bytes.toList with
  | some marker => .ok marker.epoch
  | none => .error "compacted.epoch is malformed or unsupported"

/-! ## The session state -/

/-- The five byte reads of a session. Each answers exactly the bytes asked
for, or throws. -/
structure Reads where
  /-- bytes `[off, off + len)` of GDX1 -/
  gdx : Nat → Nat → IO ByteArray
  /-- bytes `[off, off + len)` of GDV1 -/
  gdv : Nat → Nat → IO ByteArray
  /-- bytes `[off, off + len)` of the PRM1 file of a permutation -/
  prm : Nat → Nat → Nat → IO ByteArray
  /-- bytes `[off, off + len)` of the PRB1 file of a permutation -/
  prb : Nat → Nat → Nat → IO ByteArray
  /-- the whole GNL1 graph list; `none` when the generation has none -/
  graphList : IO (Option ByteArray)

/-- A permutation opened by a session. Its PRM1 file is never read whole
(https://github.com/danbri/factoidal/issues/805): the open reads the 22-byte
header (`PrmRange.openM`), and each key range is found by `PrmRange.rangeM`
over positioned reads. -/
structure PermState where
  /-- the block count of the PRM1 header -/
  count : Nat
  /-- the answers of `rangeM` for the keys asked so far (the generation does
      not change while it is open); at most 256 keys, emptied when full -/
  ranges : IO.Ref (Std.HashMap (Array UInt64) (Array BlockMeta))

/-- **An open generation.** -/
structure Core where
  manifest : Manifest
  reads : Reads
  dictHdr : Dict.GdxHeader
  /-- The dictionary's term count (`dictHdr.termCount`), a field of its own
      (the native session reads it from every thread; see
      `Harness/Sbm11Query.lean`). -/
  termCount : Nat := 0
  perms : IO.Ref (Array (Option PermState))
  /-- The dictionary page cache of the session: the keys of a page, packed in
      one byte array with the start of each key. -/
  pages : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))
  /-- bytes of PRB1 blocks read (the frames a plan reads) -/
  frameBytes : IO.Ref Nat
  /-- bytes of PRM1 entries and headers asked for -/
  prmBytes : IO.Ref Nat
  lookups : IO.Ref Nat
  /-- The overlay vocabulary (stage 5): terms of the delta log that have no
      base id, in the order the replay met them; the id of entry `k` is
      `tagDelta · 2^60 + k`. -/
  ovVocab : IO.Ref (Array Term)
  ovIds : IO.Ref (Std.HashMap Term Nat)
  /-- The dictionary ids of the terms of the log being replayed
      (`prefillBaseIds`, issue 858). Empty except during a replay. -/
  baseIds : IO.Ref (Std.HashMap Term (Option UInt64))
  /-- The dictionary ids `idOf` has looked up (at most `idMemoLimit`). -/
  idMemo : IO.Ref (Std.HashMap Term UInt64)
  /-- the named graphs of the base generation, read at the first use -/
  baseNamedRef : IO.Ref (Option (Array Nat))
  /-- The overlay per permutation (`Overlay.forPerm`), fixed at open. -/
  ovl : Array Overlay.PermOverlay := #[{}, {}, {}, {}]
  deltaBatches : Nat := 0
  deltaOps : Nat := 0
  ovInserts : Nat := 0
  ovDeletes : Nat := 0
  ovCleared : Nat := 0
  ovNewTerms : Nat := 0
  replayTerms : Nat := 0
  replayNs : Nat := 0
  /-- the log ended with a torn final frame, left out of the replay (issue 843) -/
  deltaTorn : Bool := false
  /-- the replayed overlay state (`ovl` is its cut per permutation) -/
  ovState : Overlay.State := {}
  /-- the size in bytes of the log the replay read (0: no log) -/
  ovLogBytes : Nat := 0
  /-- the most pages `pages` holds (`SBM11_PAGES` in the native session) -/
  pageLimit : Nat := 8192

/-- **What a session type adds to its state.** `pageKeys` answers the keys
of a dictionary page (from a cache, another thread's cache, or the file);
`prefetch` is the hint of `IdQuery.Store.prefetch`; `mark` the phase clock of
`IdQuery.Store.mark`. -/
class SessionOps (σ : Type) where
  core : σ → Core
  setCore : σ → Core → σ
  pageKeys : σ → Nat → IO (ByteArray × Array Nat)
  prefetch : σ → Option (Qlvr.Table → Nat → IO Unit)
  mark : σ → Option (String → IO Unit)

/-! ## Dictionary pages -/

/-- The keys of dictionary page `pg`, packed: one byte array holding the keys
one after the other and the start of each key (and the end of the last). -/
def loadPage (c : Core) (pg : Nat) : IO (ByteArray × Array Nat) := do
  let ks ← okIO s!"GDV1 page {pg}" (← (Dict.pageM c.reads.gdx c.reads.gdv pg).run)
  let total := ks.foldl (fun a k => a + k.size) 0
  let mut packed := ByteArray.emptyWithCapacity total
  let mut offs : Array Nat := Array.mkEmpty (ks.size + 1)
  for k in ks do
    offs := offs.push packed.size
    packed := packed ++ k
  offs := offs.push packed.size
  return (packed, offs)

/-- Put page `pg` in a page map that holds at most `lim` entries
(`MemoCache.insertEvict`; 0: no cache). -/
def cachePage (lim : Nat) (c : IO.Ref (Std.HashMap Nat (ByteArray × Array Nat))) (pg : Nat)
    (ks : ByteArray × Array Nat) : IO Unit := do
  if lim > 0 then
    c.modify fun m => MemoCache.insertEvict m lim pg ks

/-- The keys of a page in a one-thread session: the cache, else the file. -/
def Core.pageKeys (c : Core) (pg : Nat) : IO (ByteArray × Array Nat) := do
  match (← c.pages.get).get? pg with
  | some ks => return ks
  | none =>
    let ks ← loadPage c pg
    cachePage c.pageLimit c.pages pg ks
    return ks

instance : SessionOps Core where
  core c := c
  setCore _ c := c
  pageKeys := Core.pageKeys
  prefetch _ := none
  mark _ := none

section
variable {σ : Type} [SessionOps σ]

/-- The key of a dictionary id as a range `[a, e)` of its packed page. -/
def keySlice (s : σ) (x : UInt64) : IO (ByteArray × Nat × Nat) := do
  let c := SessionOps.core s
  let id := x.toNat
  let tag := id / two60
  unless isDictTag tag do
    throw (IO.userError s!"id {id}: not a dictionary id")
  let rank := id % two60
  if rank ≥ c.termCount then throw (IO.userError s!"id {id}: rank not below the term count")
  let (packed, offs) ← SessionOps.pageKeys s (rank / Dict.pageTerms)
  let j := rank % Dict.pageTerms
  if j + 1 < offs.size then return (packed, offs[j]!, offs[j + 1]!)
  throw (IO.userError s!"id {id}: no key")

def keyOf (s : σ) (x : UInt64) : IO ByteArray := do
  let (packed, a, e) ← keySlice s x
  return packed.extract a e

/-- The term of an id: an inline id decodes by itself, an overlay id is an
entry of the overlay vocabulary, a dictionary id is decoded from its key in
place (`decodeKeySlice?`, `TermKeyFast.decodeKeySlice?_eq`). -/
def termOf (s : σ) (x : UInt64) : IO Term := do
  let id := x.toNat
  let tag := id / two60
  if tag == tagInt || tag == tagBool then
    match ofInlineCode? id with
    | some t => return t
    | none => throw (IO.userError s!"inline id {id} does not decode")
  if tag == Overlay.tagDelta then
    match (← (SessionOps.core s).ovVocab.get)[id % two60]? with
    | some t => return t
    | none => throw (IO.userError s!"id {id}: not in the overlay vocabulary")
  let (packed, a, e) ← keySlice s x
  if classTagSlice packed a e != tag then throw (IO.userError s!"id {id}: tag differs from the key's class")
  match decodeKeySlice? packed a e with
  | some t => return t
  | none => throw (IO.userError s!"id {id}: key does not decode")

end

/-! ## Term ids, permutations, blocks -/

/-- The id of the dictionary key `k` of rank `r`. -/
def dictIdOfRank (k : ByteArray) (r : Nat) : UInt64 := (dictCode k.data.toList r).toUInt64

/-- The id of a term that the delta log added (stage 5), when it has one. -/
def Core.overlayIdOf (c : Core) (t : Term) : IO (Option UInt64) := do
  return ((← c.ovIds.get).get? t).map fun n => (Overlay.tagDelta * two60 + n).toUInt64

/-- The most entries `Core.idMemo` holds. -/
def idMemoLimit : Nat := 65536

/-- The id of a term: its inline code, its dictionary id (from `baseIds`
when a replay has put it there, else from `idMemo`, else one `Dict.lookupM`),
else the id the delta log gave it. -/
def Core.idOf (c : Core) (t : Term) : IO (Option UInt64) := do
  c.lookups.modify (· + 1)
  let t := normalizeTerm t
  match inlineCode? t with
  | some code => return some code.toUInt64
  | none =>
    let memo ← c.baseIds.get
    match (if memo.isEmpty then none else memo.get? t) with
    | some (some x) => return some x
    | some none => c.overlayIdOf t
    | none =>
      if let some x := MemoCache.find? (← c.idMemo.get) t then return some x
      match termKeyBytes? t with
      | none => return none
      | some k =>
        let (r, _) ← okIO "lookup" (← (Dict.lookupM c.reads.gdx c.reads.gdv c.dictHdr k).run)
        match r with
        | some r =>
          let x := dictIdOfRank k r
          c.idMemo.modify fun m => MemoCache.insertBounded idMemoLimit m t x
          return some x
        | none => c.overlayIdOf t

def Core.lowerBound (c : Core) (k : ByteArray) : IO Nat := do
  okIO "lower bound" (← (DictRange.lowerBoundM c.reads.gdx c.reads.gdv c.dictHdr k).run)

/-- A positioned read of a PRM1 file (`PrmRange`'s `read`), counted. -/
def Core.prmRead (c : Core) (p : Nat) (off len : Nat) : ExceptT String IO ByteArray :=
  ExceptT.lift do
    c.prmBytes.modify (· + len)
    c.reads.prm p off len

/-- The permutation `p`, opened on its first use: the PRM1 header only. -/
def Core.perm (c : Core) (p : Nat) : IO PermState := do
  match (← c.perms.get)[p]? with
  | some (some ps) => return ps
  | some none =>
    let prmA ← artifactIO c.manifest s!"PRM1-{permRoleName p}"
    let count ← match ← (PrmRange.openM (c.prmRead p) prmA.bytes p).run with
      | .ok n => pure n
      | .error e => throw (IO.userError s!"{prmA.file}: {e}")
    let ps : PermState := { count, ranges := ← IO.mkRef {} }
    c.perms.modify (·.set! p (some ps))
    return ps
  | none => throw (IO.userError s!"no permutation {p}")

/-- The PRM1 entries of the blocks of permutation `p` that may hold a row
with the key prefix (`Store.blocksForRange`): `PrmRange.rangeM` over
`PrmRange.bytesReader` of the permutation's positioned reads, the code of
`PrmRangeTheorems.rangeM_bytes`; an answer is kept for the next query with
the same key. -/
def Core.rangeFor (c : Core) (p : Nat) (key : Array UInt64) : IO (Array BlockMeta) := do
  let ps ← c.perm p
  if let some r := MemoCache.find? (← ps.ranges.get) key then return r
  let r ← match ← (PrmRange.rangeM (PrmRange.bytesReader (c.prmRead p) ps.count) key).run with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"PRM1-{permRoleName p}: {e}")
  ps.ranges.modify fun m => MemoCache.insertBounded 256 m key r
  return r

/-- Bytes `[off, off + len)` of the PRB1 file of permutation `p`, counted. -/
def Core.prb (c : Core) (p off len : Nat) : IO ByteArray := do
  c.frameBytes.modify (· + len)
  c.reads.prb p off len

section
variable {σ : Type} [SessionOps σ]

/-- **The id store of a session** (`IdQuery.Store IO`), one thread: the
function `FileGen.store` models over the files' bytes
(`FileGenTheorems.lean`). -/
def store (s : σ) : IdQuery.Store IO :=
  let c := SessionOps.core s
  { blockCount := fun p => liftIO do pure (← c.perm p).count
    blocksForRange := fun p key => liftIO (c.rangeFor p key)
    prb := fun p off len => liftIO (c.prb p off len)
    idOf := fun t => liftIO (c.idOf t)
    keyOf := fun x => liftIO (keyOf s x)
    keySlice := fun x => liftIO (keySlice s x)
    termOf := fun x => liftIO (termOf s x)
    lowerBound := fun k => liftIO (c.lowerBound k)
    ovl := fun p => c.ovl.getD p {}
    prefetch := (SessionOps.prefetch s).map fun f => fun t n => liftIO (f t n)
    mark := SessionOps.mark s }

end

/-! ## The delta overlay (stage 5) -/

/-- The id of `t`: its base id, its overlay id, or a new overlay id. -/
def Core.idOrNew (c : Core) (t0 : Term) : IO Nat := do
  match ← c.idOf t0 with
  | some x => pure x.toNat
  | none =>
    let t := normalizeTerm t0
    let admitted := (← c.baseIds.get).contains t || (termKeyBytes? t).isSome
    if !admitted then
      throw (IO.userError s!"delta log: a term the SBM11 dictionary does not admit: {repr t}")
    -- one step that reads the size and pushes: a `get` before the `modify`
    -- leaves a second reference to the array, and every push then copies it
    let n ← c.ovVocab.modifyGet fun vocab => (vocab.size, vocab.push t)
    c.ovIds.modify (·.insert t n)
    pure (Overlay.tagDelta * two60 + n)

/-- A graph name of a DLOG entry as a term: an IRI or a blank node. -/
def graphTerm : DeltaGraphName → IO Term
  | .iri g =>
    if h : isIri g = true then pure (.iri ⟨g, h⟩)
    else throw (IO.userError s!"delta log: graph name is not an IRI: {g}")
  | .bnode b => pure (.bnode b)

def Core.graphIdOrNew (c : Core) : Option DeltaGraphName → IO Nat
  | none => pure 0
  | some g => do c.idOrNew (← graphTerm g)

/-- The id of a quad when every term has an id (a quad with a term that has
no id is in no generation). -/
def Core.quadIds? (c : Core) (t : Triple) (g : Option DeltaGraphName) : IO (Option Row) := do
  let some s ← c.idOf t.s.toTerm | return none
  let some p ← c.idOf (.iri t.p) | return none
  let some o ← c.idOf t.o | return none
  let gid ← match g with
    | none => pure (some 0)
    | some gi => do pure ((← c.idOf (← graphTerm gi)).map (·.toNat))
  let some gid := gid | return none
  return some ⟨s.toNat, p.toNat, o.toNat, gid⟩

/-- A graph name as a term (`graphTerm` without the error). -/
def graphTerm? : DeltaGraphName → Option Term
  | .iri g => if h : isIri g = true then some (.iri ⟨g, h⟩) else none
  | .bnode b => some (.bnode b)

/-- The terms that `stepEntry` maps to ids for the entry `e`. -/
def entryTerms : DeltaEntry → List Term
  | .add t g | .remove t g =>
    t.s.toTerm :: .iri t.p :: t.o :: (match g with | some gi => (graphTerm? gi).toList | none => [])
  | .clear (some g) | .drop g | .create g => (graphTerm? g).toList
  | .clear none => []

/-- Look the distinct terms of the entries that `forEach` gives up in the
dictionary, in dictionary order, and keep their ids in `baseIds` (stage 5,
https://github.com/danbri/factoidal/issues/858; `DictFingerTheorems.walkM_encodeDict`:
the answer for each term is the answer of `Dict.lookupM`). `each`: look every
occurrence up on its own instead (the oracle of tests/sbm11/update_where.sh,
`SBM11_REPLAY_LOOKUP=each`). Gives the number of terms looked up. -/
def Core.prefillBaseIds (c : Core) (each : Bool) (entries : Nat)
    (forEach : (DeltaEntry → IO Unit) → IO Unit) : IO Nat := do
  if each then return 0
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
  let mut items : Array (ByteArray × Nat) := Array.mkEmpty ts.size
  for h : i in [0:ts.size] do
    if let some k := termKeyBytes? ts[i] then items := items.push (k, i)
  let sorted := Qlvr.mergeSortBy items fun a b => Dict.cmpBytesAt a.1 b.1 != .gt
  let mut memo : Std.HashMap Term (Option UInt64) := Std.HashMap.emptyWithCapacity sorted.size
  let mut w : Dict.Walk := none
  for (k, i) in sorted do
    let (r, w') ← okIO "lookup" (← (Dict.lookupWalkM c.reads.gdx c.reads.gdv c.dictHdr w k).run)
    w := w'
    if h : i < ts.size then
      memo := memo.insert ts[i] (r.map (dictIdOfRank k))
  c.baseIds.set memo
  let absent := memo.fold (fun n _ r => if r.isNone then n + 1 else n) 0
  c.ovIds.modify fun m => if m.isEmpty then Std.HashMap.emptyWithCapacity absent else m
  return sorted.size

/-- One log entry applied to an overlay state: the terms of the entry mapped
to ids (a term that has no id gets an overlay id, `idOrNew`), then
`Overlay.step`. -/
def Core.stepEntry (c : Core) (st : Overlay.State) (e : DeltaEntry) : IO Overlay.State := do
  match e with
  | .add t g =>
    let s ← c.idOrNew t.s.toTerm
    let p ← c.idOrNew (.iri t.p)
    let o ← c.idOrNew t.o
    let gid ← c.graphIdOrNew g
    return Overlay.step st (.add ⟨s, p, o, gid⟩)
  | .remove t g =>
    if let some r ← c.quadIds? t g then
      return Overlay.step st (.remove r)
    return st
  | .clear none => return Overlay.step st (.clear 0)
  | .clear (some g) =>
    if let some x ← c.idOf (← graphTerm g) then
      return Overlay.step st (.clear x.toNat)
    return st
  | .drop g =>
    if let some x ← c.idOf (← graphTerm g) then
      return Overlay.step st (.drop x.toNat)
    return st
  | .create g =>
    let x ← c.idOrNew (← graphTerm g)
    return Overlay.step st (.create x)

section
variable {σ : Type} [SessionOps σ]

/-- The session with the overlay state `st`: `ovl` cut from it per
permutation, and the overlay counters read from it. -/
def withOverlay (s : σ) (st : Overlay.State) : IO σ := do
  let c := SessionOps.core s
  let ovl := #[0, 1, 2, 3].map (Overlay.forPerm st)
  return SessionOps.setCore s
    { c with ovl, ovState := st, ovInserts := st.ins.size, ovDeletes := st.del.size,
             ovCleared := st.cleared.length, ovNewTerms := (← c.ovVocab.get).size }

/-- Replay the committed batches of a delta log into the overlay: each
entry's terms mapped to ids (`idOrNew` for an addition), then `Overlay.step`.
`logBytes` is the size of the log; `clean` is `false` when a torn final frame
was left out; `start`: the clock at which the replay time is counted from (the
caller's read of the log), else now. -/
def replay (s : σ) (batches : List DeltaBatch) (logBytes : Nat) (clean : Bool) (each : Bool := false)
    (start : Option Nat := none) : IO σ := do
  let t0 ← match start with
    | some t => pure t
    | none => IO.monoNanosNow
  let c := SessionOps.core s
  let s := SessionOps.setCore s { c with deltaTorn := !clean, ovLogBytes := logBytes }
  if batches.isEmpty then return s
  let c := SessionOps.core s
  let entries := batches.foldl (fun n b => n + b.ops.length) 0
  let resolved ← c.prefillBaseIds each entries fun f => do
    for b in batches do
      for e in b.ops do f e
  let mut st : Overlay.State :=
    { ins := Std.HashSet.emptyWithCapacity entries, del := Std.HashSet.emptyWithCapacity entries }
  let mut ops := 0
  for b in batches do
    for e in b.ops do
      ops := ops + 1
      st ← c.stepEntry st e
  c.baseIds.set {}
  let s ← withOverlay s st
  let t1 ← IO.monoNanosNow
  let c := SessionOps.core s
  return SessionOps.setCore s
    { c with deltaBatches := batches.length, deltaOps := ops, replayTerms := resolved, replayNs := t1 - t0 }

/-- The distinct graph ids other than the default graph (0) of the BASE
quads, sorted: one scan of the graph column of the PSO permutation with the
overlay left out. The named graphs of a generation that has no graph list. -/
def baseGraphIdsOfQuads (s : σ) : IO (Array Nat) := do
  let base := SessionOps.setCore s { SessionOps.core s with ovl := #[{}, {}, {}, {}] }
  let pat : IdQuery.Pat := { s := .var "s", p := .var "p", o := .var "o", g := .var "g", named := true }
  let spec := IdQuery.mkSpec pat 0 (fun v => v == "g")
  let seen ← IO.mkRef ({} : Std.HashSet Nat)
  match ← (IdQuery.scanFoldM (store base) spec true () fun _ ch => do
      let mut st ← liftIO seen.get
      liftIO (seen.set {})
      for i in [0:ch.table.rows] do
        let x := (ch.table.at 0 i).toNat
        if x != 0 then st := st.insert x
      liftIO (seen.set st)
      pure ((), true)).run with
  | .error e => throw (IO.userError s!"graph scan failed: {e}")
  | .ok _ => pure ()
  return Qlvr.mergeSortBy (← seen.get).toArray (· ≤ ·)

/-- The named graphs of the base generation: the graph list GNL1, or the
graph ids of the base quads for a generation that has no list, sorted; read
once. -/
def baseNamed (s : σ) : IO (Array Nat) := do
  let c := SessionOps.core s
  match ← c.baseNamedRef.get with
  | some xs => return xs
  | none =>
    let xs ← match ← c.reads.graphList with
      | some bytes =>
        match GraphList.decodeAt bytes with
        | some ids => pure ids
        | none => throw (IO.userError "graphs.gnl1: does not decode as a GNL1 graph list")
      | none => baseGraphIdsOfQuads s
    c.baseNamedRef.set (some xs)
    return xs

/-- Does the named graph with id `x` exist in the overlaid generation?
`Overlay.denoteNamed` over the base named graphs. -/
def hasNamedGraph (s : σ) (x : Nat) : IO Bool := do
  if x == 0 then return false
  let st := (SessionOps.core s).ovState
  if st.created.contains x then return true
  if st.dropped.contains x then return false
  return GraphList.contains (← baseNamed s) x

/-- The ids of the named graphs of the overlaid generation, sorted: the base
named graphs the log did not drop, and the graphs the log created. -/
def namedGraphIds (s : σ) : IO (Array Nat) := do
  let base ← baseNamed s
  let st := (SessionOps.core s).ovState
  let mut out : Array Nat := Array.mkEmpty (base.size + st.created.size)
  for x in base do
    if !st.dropped.contains x then out := out.push x
  for x in st.created do
    if !GraphList.contains base x then out := out.push x
  return Qlvr.mergeSortBy out (· ≤ ·)

/-- A store with the named graphs of the overlaid generation
(`namedGraphIds`), which the nested evaluator reads for GRAPH
(https://github.com/danbri/factoidal/issues/959). -/
def withNamedGraphs (s : σ) (st : IdQuery.Store IO) : IdQuery.Store IO :=
  { st with namedGraphs := some (liftIO do return (← namedGraphIds s).map (·.toUInt64)) }

/-! ## The reference fallback -/

/-- Every row of permutation `perm` with key prefix `key`, all graphs: `f`
gets the four columns of each block's rows. -/
def scanAll (s : σ) (perm : Nat) (key : Array UInt64) (f : Array ByteArray → Nat → IO Unit) : IO Unit := do
  let spec : IdQuery.ScanSpec := { perm, key, checks := #[], named := false,
                                   outVars := #["c0", "c1", "c2", "g"], outCols := #[0, 1, 2, 3], eqs := #[] }
  match ← (IdQuery.scanFoldM (store s) spec true () fun _ ch => do
      liftIO (f ch.table.cols ch.table.rows)
      pure ((), true)).run with
  | .ok _ => pure ()
  | .error e => throw (IO.userError e)

end

def subjectOf (t : Term) : IO Subject :=
  match t with
  | .iri i => pure (.iri i)
  | .bnode b => pure (.bnode b)
  | _ => throw (IO.userError "a subject or graph name that is not an IRI or a blank node")

section
variable {σ : Type} [SessionOps σ]

/-- The quads the planner guard selects, as the dataset they denote, with
every named graph of the overlaid generation that the guard keeps (SPARQL 1.1
Query section 13: a named graph with no selected quad is in the dataset with
no triple; https://github.com/danbri/factoidal/issues/855). The pure model of
this read is `Storage.SelectedDataset.selectedModel`, up to the order of the
triples and of the named graphs; that this IO read returns it is the named
assumption `SelectedAgrees` (stage `sbm11SelectedRead`). -/
def selectedDataset (s : σ) (q : Query) (extraGraphs : List WfIri := []) : IO (Dataset × String) := do
  let c := SessionOps.core s
  let preds := ShardManifest.queryQuadConstantPredicates? q
  let graphs := ShardManifest.queryGraphNames? q
  let mut allowed : Option (Array UInt64) := none
  match graphs with
  | none => pure ()
  | some gs =>
    let mut a : Array UInt64 := #[]
    for gn in gs do
      match gn with
      | .defaultGraph => a := a.push 0
      | .iri v => if let some x ← c.idOf (.iri v) then a := a.push x
      | .bnode l => if let some x ← c.idOf (.bnode l) then a := a.push x
    -- graphs the caller reads that the query text does not name (`WITH <g>`
    -- of an update makes `g` the graph the default-graph patterns read)
    for v in extraGraphs do
      if let some x ← c.idOf (.iri v) then a := a.push x
    allowed := some a
  let rowsRef ← IO.mkRef (#[] : Array (UInt64 × UInt64 × UInt64 × UInt64))
  let collect (perm : Nat) (cols : Array ByteArray) (n : Nat) : IO Unit := do
    let mut acc ← rowsRef.get
    rowsRef.set #[]
    for i in [0:n] do
      let a := IdQuery.at64 cols[0]! i
      let b := IdQuery.at64 cols[1]! i
      let cc := IdQuery.at64 cols[2]! i
      let g := IdQuery.at64 cols[3]! i
      let ok := match allowed with
        | some xs => xs.contains g
        | none => true
      if ok then
        acc := acc.push (if perm == 0 then (b, a, cc, g) else (a, b, cc, g))
    rowsRef.set acc
  let what ← match preds with
    | some ps => do
      let mut found := 0
      for p in ps.eraseDups do
        match ← c.idOf (.iri p) with
        | some pid =>
          found := found + 1
          scanAll s 0 #[pid] (collect 0)
        | none => pure ()
      pure s!"predicates={ps.eraseDups.length} (in the dictionary: {found})"
    | none => do
      scanAll s 2 #[] (collect 2)
      pure "predicates=all"
  let rows ← rowsRef.get
  let mut quads : Array IndexedBlockWireV4.QuadRow := Array.mkEmpty rows.size
  let mut withQuad : Std.HashSet UInt64 := {}
  for (sx, p, o, g) in rows do
    if g != 0 then withQuad := withQuad.insert g
    let st ← subjectOf (← termOf s sx)
    let pt ← match ← termOf s p with
      | .iri i => pure i
      | _ => throw (IO.userError "a predicate that is not an IRI")
    let ot ← termOf s o
    let gr : Option Subject ← if g == 0 then pure none else pure (some (← subjectOf (← termOf s g)))
    quads := quads.push (gr, { s := st, p := pt, o := ot })
  let mut noQuad : Array NamedGraph := #[]
  for x in ← namedGraphIds s do
    let gid := x.toUInt64
    if withQuad.contains gid then continue
    let kept := match allowed with
      | some xs => xs.contains gid
      | none => true
    if kept then noQuad := noQuad.push { name := ← subjectOf (← termOf s gid), graph := [] }
  let graphsText := match graphs with
    | some gs => s!"graphs={gs.length}"
    | none => "graphs=all"
  let ds0 := QuadDataset.datasetOfQuads quads.toList
  return ({ ds0 with named := ds0.named ++ noQuad.toList },
          s!"{what} {graphsText} quads={quads.size} named-graphs-without-a-selected-quad={noQuad.size}")

end

/-- The query without its FROM and FROM NAMED clauses (the dataset is applied
before evaluation). -/
def stripDatasetClauses (query : Query) : Query :=
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

/-- Write the answer of a post-processed id plan (issue 823) as
`runReference` writes the reference evaluator's answer of the same form. -/
def emitPost (ans : IdQuery.PostAnswer) (emit : ByteArray → IO Unit) : IO Unit := do
  match ans with
  | .solutions vars rows => emit (QueryResult.bindings vars rows).toSrjFast.toUTF8
  | .boolean b => emit (QueryResult.boolean b).toSrjFast.toUTF8
  | .graph g => discard <| emitGraph g emit

section
variable {σ : Type} [SessionOps σ]

/-- The reference evaluator over the selected dataset. `clockEnv`: the
environment with NOW read once for this query (purity doctrine: the clock is
an argument). -/
def runReference (s : σ) (clockEnv : EvalEnv) (q : Query) (reason : String) (emit : ByteArray → IO Unit) :
    IO (Nat × String) := do
  let (ds, what) ← selectedDataset s q
  let (applied, _) := applyDataset q.dataset ds ds.default
  let stripped := stripDatasetClauses q
  let env : EvalEnv := { clockEnv with dataset := some applied, ext := L4Factoidal.Geo.extFns, base := q.base }
  let indexed := QuadDataset.namesAreIris applied
  let line := s!"path=reference reason=\"{reason}\" {what}"
  match stripped.serviceFailure env applied with
  | some f => throw (IO.userError f.message)
  | none =>
  match q.form with
  | .select _ =>
    -- `SelectedDataset.referenceSelect`: the backend evaluator when every
    -- graph name is an IRI, else the reference evaluator. Its theorem over
    -- the model of `selectedDataset`: `SelectedDataset.referenceSelect_selectedModel`.
    let rows := SelectedDataset.referenceSelect env q applied
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

end

/-! ## Running a query -/

structure Outcome where
  rows : Nat
  /-- `path=ids` or `path=reference ...` -/
  path : String
  plan : Array String := #[]

/-- The query text read by the repository's SPARQL parser. -/
def parse? (text : String) (base : Option String) (version : SparqlVersion := .v11) : Except String Query :=
  match parseSparql text base version with
  | .error e => .error s!"SPARQL parse error at {e.pos}: {e.msg}"
  | .ok q => .ok q

/-- How a query runs on ids: the store of the flat plans, the store of the
nested evaluator, the divided paths (`none`: one thread), and a step before
an id plan starts (the native worker pool wakes its workers there). -/
structure IdRun where
  store : IdQuery.Store IO
  nested : IdQuery.Store IO
  par : Option (IdQuery.Par IO) := none
  onPlan : IdQuery.Plan → IO Unit := fun _ => pure ()

section
variable {σ : Type} [SessionOps σ]

/-- **Run one parsed query on an open session.** The id path when
`IdQuery.translate` takes the query (and `forceReference` is off), else the
reference fallback; an id-path error that starts with `refused: ` (issue 954)
also runs the reference fallback. The answer goes to `emit`: SPARQL JSON for
SELECT and ASK, N-Triples lines for CONSTRUCT and DESCRIBE. -/
def runOneWith (s : σ) (clockEnv : EvalEnv) (q : Query) (emit : ByteArray → IO Unit)
    (forceReference referenceRender : Bool) (r : IdRun) : IO Outcome := do
  let refusedOr (e : String) : IO Outcome := do
    if e.startsWith "refused: " then
      let (n, line) ← runReference s clockEnv q (e.drop 9).toString emit
      return { rows := n, path := line }
    throw (IO.userError s!"id query failed: {e}")
  let plan? := if forceReference then .error "--reference" else IdQuery.translate q
  match plan? with
  | .error reason =>
    let (n, line) ← runReference s clockEnv q reason emit
    return { rows := n, path := line }
  | .ok plan =>
    r.onPlan plan
    let env := IdGroup.queryEnvOf clockEnv q.base
    match plan.post with
    | some ps =>
      if plan.nested.isSome then
        -- issue 959: a nested WHERE clause, the recursive evaluator on ids
        match ← (IdGroup.runNestedM r.nested plan ps env).run with
        | .ok (ans, st) =>
          emitPost ans emit
          return { rows := st.rows, path := "path=ids", plan := st.plan }
        | .error e => refusedOr e
      else
      -- issue 823: the WHERE clause on ids, the reference post-processing on
      -- the decoded solutions
      match ← (IdQuery.runPostM r.store plan ps env).run with
      | .ok (ans, st) =>
        emitPost ans emit
        return { rows := st.rows, path := "path=ids", plan := st.plan }
      | .error e => refusedOr e
    | none =>
    -- `runPlanM` refuses (issue 954) before it emits anything
    match ← (IdQuery.runPlanM r.store plan emit referenceRender r.par env).run with
    | .ok st => return { rows := st.rows, path := "path=ids", plan := st.plan }
    | .error e => refusedOr e

/-- `runOneWith` on one thread: the session's own store, with the named
graphs for the nested evaluator, and with the SIP factor and the aggregate
switch of the native command's defaults. -/
def runOne (s : σ) (clockEnv : EvalEnv) (q : Query) (emit : ByteArray → IO Unit)
    (forceReference referenceRender : Bool := false) (sip : Option Nat := some 16) (aggOnIds : Bool := true) :
    IO Outcome :=
  let st := { store s with sipFactor := sip, aggOnIds := aggOnIds }
  runOneWith s clockEnv q emit forceReference referenceRender { store := st, nested := withNamedGraphs s st }

end

/-! ## Opening a generation over a medium -/

open L4Factoidal.Storage.Medium (Medium objectName readWhole? resolveGeneration)

/-- The bytes of a medium object, the range checked against the length the
manifest records (`totalBytes`), every byte counted in `counter`. -/
def mediumRange (md : Medium IO) (counter : IO.Ref Nat) (name : String) (totalBytes : Nat)
    (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  if off + len > totalBytes then
    throw (IO.userError s!"{name}: read of {len} bytes at {off} past the manifest's length {totalBytes}")
  let b ← okIO name (← md.readAt name off len)
  if b.size != len then throw (IO.userError s!"{name}: short read of {len} bytes at {off}")
  counter.modify (· + len)
  return b

/-- The reads of a generation in directory `dir` of a medium. -/
def mediumReads (md : Medium IO) (counter : IO.Ref Nat) (dir : String) (m : Manifest) : IO Reads := do
  let gdvA ← artifactIO m "GDV1"
  let gdxA ← artifactIO m "GDX1"
  let mut prmA : Array Artifact := #[]
  let mut prbA : Array Artifact := #[]
  for p in [0:4] do
    prmA := prmA.push (← artifactIO m s!"PRM1-{permRoleName p}")
    prbA := prbA.push (← artifactIO m s!"PRB1-{permRoleName p}")
  let prmA' := prmA
  let prbA' := prbA
  let range (a : Artifact) := mediumRange md counter (objectName dir a.file) a.bytes
  let permRange (as : Array Artifact) (p off len : Nat) : IO ByteArray :=
    match as[p]? with
    | some a => range a off len
    | none => throw (IO.userError s!"no permutation {p}")
  return { gdx := range gdxA, gdv := range gdvA, prm := permRange prmA', prb := permRange prbA'
           graphList := match artifactOf? m "GNL1" with
             | none => pure none
             | some a => do return some (← range a 0 a.bytes) }

/-- **Open an SBM11 generation over a medium**: the collection root's
`CURRENT` pointer resolved (`Medium.resolveGeneration`), the manifest decoded,
the length of every file checked against the manifest (`size`), the GDX1
header read, and the delta log replayed (`replay`) when the generation has one.
`counter` counts every byte read from the medium after the open. -/
def openMedium (md : Medium IO) (counter : IO.Ref Nat) (each : Bool := false) : IO (Core × String) := do
  let dir ← okIO "CURRENT" (← resolveGeneration md)
  let mname := objectName dir manifestFile
  let some mbytes ← okIO mname (← readWhole? md mname)
    | throw (IO.userError s!"{mname}: no such object")
  let some m := decodeManifest mbytes.data.toList
    | throw (IO.userError s!"{mname}: does not decode as an SBM11 manifest")
  for a in m.artifacts do
    let name := objectName dir a.file
    match ← okIO name (← md.size name) with
    | some n =>
      if n != a.bytes then throw (IO.userError s!"{name}: {n} bytes, the manifest says {a.bytes}")
    | none => throw (IO.userError s!"{name}: no such object")
  let reads ← mediumReads md counter dir m
  let hdrBytes ← reads.gdx 0 Dict.gdxHeaderBytes
  let dictHdr ← okIO "GDX1" (Dict.parseGdxHeader hdrBytes)
  let c : Core := { manifest := m, reads, dictHdr, termCount := dictHdr.termCount,
                    perms := ← IO.mkRef #[none, none, none, none],
                    pages := ← IO.mkRef {}, frameBytes := ← IO.mkRef 0, prmBytes := ← IO.mkRef 0,
                    lookups := ← IO.mkRef 0, ovVocab := ← IO.mkRef #[], ovIds := ← IO.mkRef {},
                    baseIds := ← IO.mkRef {}, idMemo := ← IO.mkRef {}, baseNamedRef := ← IO.mkRef none }
  let logName := objectName dir deltaLogFile
  match ← okIO logName (← readWhole? md logName) with
  | none => return (c, dir)
  | some log =>
    let epochName := objectName dir compactedEpochFile
    let baseEpoch ← match ← okIO epochName (← readWhole? md epochName) with
      | none => pure none
      | some b => pure (some (← okIO epochName (epochOfMarker b)))
    let (batches, clean) ← okIO logName (batchesOfLog log baseEpoch)
    return (← replay c batches log.size clean each, dir)

end L4Factoidal.Storage.Sbm11.QuerySession
