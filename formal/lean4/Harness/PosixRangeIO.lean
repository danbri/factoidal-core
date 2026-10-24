/- Native POSIX range reader for executable block-engine probes.

   This deliberately lives under Harness, not L4Factoidal: `pread` is an
   operating-system realization of the pure IBK2 ByteRange contract, not part
   of the verified block semantics and not available to the WASM target. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.GenerationVerify
import Harness.NativeHasher

namespace Harness.PosixRangeIO

open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.BlockMerkle

/- Every chunk admission below hashes with `Harness.nativeHasher` (HACL*
    `Hacl_Hash_SHA2_hash_256`) rather than the pure Lean specification
    hash. `lake exe l4native-crypto-smoke` checks agreement on FIPS vectors,
    padding and block boundaries, and a 1 MiB buffer. Agreement for all
    admitted inputs within the native binding's length bound remains a host
    trust condition, not a Lean theorem. The specification instance stays
    `pureHasher`; nothing proved about `ChunkedArtifact` or `BlockMerkle`
    mentions the extern. -/

/-- Read at an absolute file offset without changing any shared file cursor.
    The C implementation returns an empty array on open/read/short-read
    failure; `readRange?` below turns that into an explicit refusal by checking
    the exact requested extent. -/
@[extern "l4_block_pread"]
opaque preadRaw (path : @& String) (offset length : UInt64) : IO ByteArray

/-- Multi-writer counterpart: append only if the file still has the exact
    byte length Lean validated.  The native edge holds an exclusive advisory
    lock for the size check, write-all loop and file `fsync`. -/
@[extern "l4_delta_log_append_sync_at_size"]
opaque appendSyncAtSizeRaw (path : @& String) (expectedSize : UInt64)
  (bytes : @& ByteArray) : IO Bool

/-- In-place counterpart: overwrite `bytes` at `offset` (inside the file) only
    if the file still has exactly `expectedSize` bytes, under the same
    exclusive advisory lock, then `fsync`. The DLOG writer sets the header
    version to 2 with it before the first batch that holds an RDF 1.2 term. -/
@[extern "l4_delta_log_write_at_size"]
opaque writeAtSizeSyncRaw (path : @& String) (expectedSize offset : UInt64)
  (bytes : @& ByteArray) : IO Bool

/-- Atomically replace a small, Lean-validated control file after syncing its
    complete new contents and the parent directory entry. Readers observe
    either whole version, and a successful result survives normal crash
    recovery rather than merely concurrent access. -/
@[extern "l4_atomic_replace_file_sync"]
opaque atomicReplaceFileSyncRaw (path : @& String) (bytes : @& ByteArray) : IO Bool

def rangeArgs? (range : ByteRange) : Option (UInt64 × UInt64) :=
  if range.offset >= 2 ^ 63 || range.offset + range.length > 2 ^ 63 then none
  else some (UInt64.ofNat range.offset, UInt64.ofNat range.length)

#guard (rangeArgs? { offset := 0, length := 4 }).map
  (fun args => (args.1.toNat, args.2.toNat)) == some (0, 4)
#guard (rangeArgs? { offset := 2 ^ 64, length := 1 }).isNone
#guard (rangeArgs? { offset := 0, length := 2 ^ 64 }).isNone
#guard (rangeArgs? { offset := 2 ^ 63 - 1, length := 2 }).isNone
#guard (rangeArgs? { offset := 2 ^ 63, length := 0 }).isNone
#guard (rangeArgs? { offset := 2 ^ 63 - 1, length := 1 }).map
  (fun args => (args.1.toNat, args.2.toNat)) == some (2 ^ 63 - 1, 1)

/-- An open file for positioned reads (`l4_block_file_open`): the
    descriptor and the length are read once, and the descriptor is closed when
    the object is freed. Reads give the bytes `preadRaw` gives for the same
    file, as long as the file does not change after the open (the files of
    an SBM11 generation do not). Issue 961, stage 1n of
    docs/designissues/2026-10-12-parallel-block-scans.md: q07 read a block
    with `open`, `fstat`, `pread` and `close`. -/
opaque BlockFilePointed : NonemptyType
def BlockFile : Type := BlockFilePointed.type
instance : Nonempty BlockFile := BlockFilePointed.property

/-- Open `path` for reading. A file that does not open gives an object whose
    reads are empty, as `preadRaw` of that path is. -/
@[extern "l4_block_file_open"]
opaque BlockFile.open (path : @& String) : IO BlockFile

/-- `preadRaw` through an open file: the bytes, or an empty array when the
    range is past the file's length at the open or the read fails. -/
@[extern "l4_block_file_pread"]
opaque BlockFile.pread (f : @& BlockFile) (offset length : UInt64) : IO ByteArray

/-- Where a positioned read goes: the path, and the file opened once for
    it when the caller keeps one (`BlockFile`). -/
structure ReadSrc where
  path : String
  file : Option BlockFile := none

instance : Coe String ReadSrc := ⟨fun path => { path }⟩

def ReadSrc.ofPath (path : String) : IO ReadSrc :=
  return { path, file := some (← BlockFile.open path) }

/-- `preadRaw` of the source: through its open file when it has one. -/
def ReadSrc.pread (src : ReadSrc) (offset length : UInt64) : IO ByteArray :=
  match src.file with
  | some f => f.pread offset length
  | none => preadRaw src.path offset length

def readRange? (path : ReadSrc) (range : ByteRange) : IO (Option ByteArray) := do
  match rangeArgs? range with
  | none => pure none
  | some (offset, length) =>
      let bytes ← path.pread offset length
      if bytes.size == range.length then pure (some bytes) else pure none

/-- Decode untrusted raw 32-byte leaf hashes from a packer's `.merkle`
    sidecar. Their authority comes only from a successful proof to an SBM1
    root, never from the sidecar file itself. `extract` avoids copying the
    whole sidecar into a linked list for each individual leaf. -/
def leaves? (expected : Nat) (bytes : ByteArray) : Option (List Digest) :=
  L4Factoidal.Storage.GenerationVerify.leaves? expected bytes

private def singleChunkIndex? (ref : Ref) (range : ByteRange) : Option Nat := do
  if range.length == 0 || range.offset + range.length > ref.totalBytes then none else do
  let first := range.offset / ref.chunkBytes
  let last := (range.offset + range.length - 1) / ref.chunkBytes
  if first == last then some first else none

private def chunkIndices? (ref : Ref) (range : ByteRange) : Option (Nat × List Nat) := do
  if range.length == 0 || range.offset + range.length > ref.totalBytes then none else do
  let first := range.offset / ref.chunkBytes
  let last := (range.offset + range.length - 1) / ref.chunkBytes
  some (first, (List.range (last - first + 1)).map fun delta => first + delta)

/-- Honest positioned-read accounting for one verified range. `requestedBytes`
    is the logical range length; `fetchedBytes` is the sum of complete fixed
    chunks the native host must obtain before it can return that range. -/
structure VerifiedReadFootprint where
  requestedBytes : Nat
  fetchedBytes : Nat
  chunks : Nat
  deriving Repr, DecidableEq

def verifiedReadFootprint? (ref : Ref) (range : ByteRange) : Option VerifiedReadFootprint := do
  let (_, indices) ← chunkIndices? ref range
  let lengths ← indices.mapM (expectedBytes? ref)
  some { requestedBytes := range.length
         fetchedBytes := lengths.foldl (fun total length => total + length) 0
         chunks := lengths.length }

/-- The chunks of one file that a reader has admitted, and the proof table of the
    file's Merkle tree.

    `chunks` is indexed by the already validated fixed-chunk ordinal.  The
    earlier association-list representation was deliberately simple, but a
    full scan of a large artifact performs one lookup per row and made cache
    hits grow linearly with the number of admitted chunks.  This bounded
    sparse array keeps the same trust boundary -- only the chunk readers
    insert bytes -- while making an admitted-chunk lookup constant time.

    `tree` is the file's levels (`BlockMerkle.Tree`), computed from the leaves
    of the first call that needs a proof and kept with the chunks.  Before
    2026-10-14 every admitted chunk computed the whole tree again
    (`proofWith?`: `n - 1` hashes for one proof of a file of `n` chunks), so a
    pass over a file cost `n * (n - 1)` hashes
    (https://github.com/danbri/factoidal/issues/854).  The proof read from the
    table is the proof `proofWith?` computes (`Tree.proof?_ofLeavesWith`), and
    the chunk is still verified against the root of the manifest, so a wrong
    table can only refuse a chunk.  The leaves are read when the table is
    built, once for the cache; a call that finds its chunk, or the table,
    does not look at them. -/
structure VerifiedChunkCache where
  chunks : Array (Option ByteArray)
  tree : Option Tree := none

def newVerifiedChunkCache (ref : Ref) : IO (IO.Ref VerifiedChunkCache) :=
  IO.mkRef { chunks := Array.replicate ref.chunkCount none }

/-- Read the chunk `index` and admit it under `proof?`, a proof for that index,
    or refuse it. -/
private def readVerifiedChunkProof? (path : ReadSrc) (ref : Ref) (proof? : Option (List Step))
    (index : Nat) : IO (Option ByteArray) := do
  match offset? ref index, expectedBytes? ref index, proof? with
  | some offset, some length, some proof =>
      match ← readRange? path { offset, length } with
      | some chunk => if verifyChunkWith nativeHasher ref index chunk proof then pure (some chunk) else pure none
      | none => pure none
  | _, _, _ => pure none

/-- The proof table of a file, from the leaves of its `.merkle` sidecar, hashed
    with the native hasher.  The cost is `n - 1` node hashes for `n` leaves, once
    for the file; a proof read from it is `log2 n` reads. -/
def treeOfLeaves (leaves : List Digest) : Tree := Tree.ofLeavesWith nativeHasher leaves

/-- The proof table of the file `ref`, or `none` when `leaves` are not
    `ref.chunkCount` many: no proof of a tree of another size can admit a chunk of
    this file. -/
def treeOf? (ref : Ref) (leaves : List Digest) : Option Tree :=
  let t := treeOfLeaves leaves
  if t.leafCount != ref.chunkCount then none else some t

/-- The table exists exactly when the count of leaves is the file's count of chunks,
    which is the test that the readers made on the list of leaves before the table
    (`Tree.leafCount_ofLeavesWith`). -/
theorem treeOf?_eq_some (ref : Ref) (leaves : List Digest) (h : leaves.length = ref.chunkCount) :
    treeOf? ref leaves = some (treeOfLeaves leaves) := by
  simp [treeOf?, treeOfLeaves, Tree.leafCount_ofLeavesWith, h]

theorem treeOf?_eq_none (ref : Ref) (leaves : List Digest) (h : leaves.length ≠ ref.chunkCount) :
    treeOf? ref leaves = none := by
  simp [treeOf?, treeOfLeaves, Tree.leafCount_ofLeavesWith, h]

/-- One chunk by the proof that the file's table `tree` gives.  Until
    https://github.com/danbri/factoidal/issues/859 was repaired (2026-10-14) a
    reader without a cache computed the proof from the leaves for each chunk
    (`proofWith?`: `n - 1` hashes for a file of `n` chunks), so a read of most of
    a file cost the square of its chunk count.  The chunk is still checked against
    the root of the manifest (`verifyChunkWith`), so a wrong table can only refuse a
    chunk. -/
def readVerifiedChunkTree? (path : ReadSrc) (ref : Ref) (tree : Tree)
    (index : Nat) : IO (Option ByteArray) :=
  readVerifiedChunkProof? path ref (tree.proof? index) index

/-- The proof that admits a chunk is the proof `proofWith?` computes from the
    leaves, for every file, list of leaves and index: the right side is the reader
    that called `proofWith?` for each chunk. -/
theorem readVerifiedChunkTree?_eq (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (index : Nat) :
    readVerifiedChunkTree? path ref (treeOfLeaves leaves) index =
      readVerifiedChunkProof? path ref (proofWith? nativeHasher leaves index) index := by
  simp only [readVerifiedChunkTree?, treeOfLeaves, Tree.proof?_ofLeavesWith]

/-- The proof table of the file, built from `leaves` when the cache has none.
    `none` when `leaves` are not `ref.chunkCount` many (`treeOf?`). -/
private def cachedTree? (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) : IO (Option Tree) := do
  match (← cache.get).tree with
  | some t => pure (some t)
  | none =>
      match treeOf? ref leaves with
      | none => pure none
      | some t =>
          cache.modify fun c => { c with tree := some t }
          pure (some t)

/-- Admit one fixed chunk through the same positioned-read and Merkle-proof
    path as `readVerifiedRangeCached?`.  A cache hit reports zero newly
    fetched/requested bytes; callers that form a larger logical range account
    for that range separately.  This primitive is useful for streaming
    validators which must not first concatenate every touched chunk. -/
def readVerifiedChunkCached? (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) (index : Nat) :
    IO (Option (ByteArray × VerifiedReadFootprint)) := do
  match (← cache.get).chunks[index]? with
  | some (some chunk) =>
      pure (some (chunk, { requestedBytes := 0, fetchedBytes := 0, chunks := 0 }))
  | _ =>
      match ← cachedTree? ref leaves cache with
      | none => pure none
      | some tree =>
          match ← readVerifiedChunkProof? path ref (tree.proof? index) index with
          | none => pure none
          | some chunk =>
              cache.modify fun c =>
                match c with
                | { chunks, tree } => { chunks := chunks.set! index (some chunk), tree }
              pure (some (chunk, { requestedBytes := chunk.size, fetchedBytes := chunk.size, chunks := 1 }))

/-- The chunks `indices`, in order, each admitted by the proof of `tree`; `none`
    when one is refused.  A loop: `acc` holds the chunks read, newest first.  The
    list of chunks of a range is as long as the range is in chunks, so a call for
    each chunk would take one stack frame for each. -/
private def readVerifiedChunksTree (path : ReadSrc) (ref : Ref) (tree : Tree) :
    List Nat → List ByteArray → IO (Option (List ByteArray))
  | [], acc => pure (some acc.reverse)
  | index :: rest, acc => do
      match ← readVerifiedChunkTree? path ref tree index with
      | some chunk => readVerifiedChunksTree path ref tree rest (chunk :: acc)
      | none => pure none

private def concatChunks (chunks : List ByteArray) : ByteArray :=
  /- `fastAppend` is Lean's growing-capacity append intended for repeated
     assembly. This keeps verified cross-chunk reads packed throughout rather
     than materializing every chunk as a linked byte list. -/
  chunks.foldl ByteArray.fastAppend ByteArray.empty

/-- Compatibility helper for one fixed SBM1 chunk. The generic verified-range
    reader below now handles cross-chunk requests; this narrower form remains
    useful to callers that intentionally require a single inclusion proof. -/
def readVerifiedSingleChunkRange? (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (range : ByteRange) : IO (Option ByteArray) := do
  if leaves.length != ref.chunkCount then return none
  match singleChunkIndex? ref range with
  | none => pure none
  | some index =>
      match offset? ref index, expectedBytes? ref index, (treeOfLeaves leaves).proof? index with
      | some offset, some length, some proof =>
          match ← readRange? path { offset, length } with
          | some chunk =>
              if !verifyChunkWith nativeHasher ref index chunk proof then pure none
              else
                let localOffset := range.offset - offset
                pure (some (chunk.extract localOffset (localOffset + range.length)))
          | none => pure none
      | _, _, _ => pure none

/-- Read an exact contiguous range by verifying every fixed chunk it touches
    to the same SBM1 root, then returning only the requested interior bytes.
    `tree` is the proof table of the file (`treeOf?`, `treeOfLeaves`): a caller
    that reads several ranges of one file builds it once and gives it to each
    call (`Harness.ShardMerkleScan`).  The leaf count of the table is checked
    against `ref` (one read). -/
def readVerifiedRangeTree? (path : ReadSrc) (ref : Ref) (tree : Tree)
    (range : ByteRange) : IO (Option ByteArray) := do
  if tree.leafCount != ref.chunkCount then return none
  match chunkIndices? ref range with
  | none => pure none
  | some (first, indices) =>
      match ← readVerifiedChunksTree path ref tree indices [] with
      | none => pure none
      | some chunks =>
          /- Most row reads touch one chunk.  Do not copy a full fixed chunk
             merely to take the requested few bytes from it; concatenate only
             when an exact range actually crosses a chunk boundary. -/
          let all := match chunks with
            | [chunk] => chunk
            | _ => concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            pure (some (all.extract localOffset (localOffset + range.length)))
          else pure none

/-- `readVerifiedRangeTree?` with the proof table built from `leaves` for this
    call: `n - 1` node hashes for a file of `n` chunks, once, where the reader
    before https://github.com/danbri/factoidal/issues/859 computed `n - 1` for each
    chunk of the range. -/
def readVerifiedRange? (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (range : ByteRange) : IO (Option ByteArray) := do
  if leaves.length != ref.chunkCount then return none
  readVerifiedRangeTree? path ref (treeOfLeaves leaves) range

private def readCachedChunks (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) : List Nat → IO (Option (List ByteArray × Nat × Nat))
  | [] => pure (some ([], 0, 0))
  | index :: rest => do
      match ← readVerifiedChunkCached? path ref leaves cache index with
      | some (chunk, footprint) =>
          match ← readCachedChunks path ref leaves cache rest with
          | some (chunks, freshChunks, freshBytes) =>
              pure (some (chunk :: chunks, freshChunks + footprint.chunks, freshBytes + footprint.fetchedBytes))
          | none => pure none
      | none => pure none

/-- Cached variant of `readVerifiedRange?`. Cache misses still perform the
    full positioned read and proof check; the returned footprint counts only
    those newly obtained chunks, not chunks already admitted by this cache. -/
def readVerifiedRangeCached? (path : ReadSrc) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) (range : ByteRange) :
    IO (Option (ByteArray × VerifiedReadFootprint)) := do
  -- The leaves are not counted here: `readVerifiedChunkCached?` counts them once,
  -- when it builds the proof table (a count on every read was a walk down the
  -- list of leaves for each read).
  match chunkIndices? ref range with
  | none => pure none
  | some (first, indices) =>
      match ← readCachedChunks path ref leaves cache indices with
      | none => pure none
      | some (chunks, freshChunks, freshBytes) =>
          /- A cached fixed-row read ordinarily has exactly one chunk.  This
             branch avoids allocating and copying that whole chunk on every
             row while retaining the existing general cross-chunk behaviour. -/
          let all := match chunks with
            | [chunk] => chunk
            | _ => concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            let bytes := all.extract localOffset (localOffset + range.length)
            pure (some (bytes, { requestedBytes := range.length, fetchedBytes := freshBytes, chunks := freshChunks }))
          else pure none

end Harness.PosixRangeIO
