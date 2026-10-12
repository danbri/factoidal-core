/-
Harness/Sbm11Gen — host I/O for SBM11 generations (stage 3,
https://github.com/danbri/factoidal/issues/789): file hashing and Merkle
leaves, opening a generation through its manifest, verified positioned reads
of blocks, the scan and count of a key prefix, id-to-term through the
dictionary, and the activation checks.

This is a HARNESS: it does file I/O. The formats, their decoders and their
theorems are `L4Factoidal.Storage.Sbm11.{Column, Block, Manifest, Dict,
TermId}`.
-/
import L4Factoidal.Storage.Sbm11.Block
import L4Factoidal.Storage.Sbm11.Manifest
import L4Factoidal.Storage.Sbm11.Dict
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.BlockMerkle
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Crypto.SHA2
import Harness.PosixRangeIO
import Harness.NativeHasher
import Harness.GenerationPointer
import Std.Data.HashMap

namespace Harness.Sbm11Gen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.Manifest
open L4Factoidal.Storage.BlockMerkle
open L4Factoidal.Storage.ChunkedArtifact (Ref)

/-! ## Small I/O helpers -/

def vmHWM : IO String := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    match (s.splitOn "\n").find? (·.startsWith "VmHWM:") with
    | some l => pure ((l.drop 6).trimAscii.toString)
    | none => pure "n/a"
  catch _ => pure "n/a"

def ms (t0 t1 : Nat) : String :=
  let u := (t1 - t0) / 1000
  s!"{u / 1000}.{toString (1000 + u % 1000) |>.drop 1}"

def pread (path : String) (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  let b ← Harness.PosixRangeIO.preadRaw path off.toUInt64 len.toUInt64
  if b.size != len then throw (IO.userError s!"{path}: short read of {len} bytes at {off}")
  pure b

def fileSize (p : String) : IO Nat := do
  pure (← System.FilePath.metadata p).byteSize.toNat

def ok {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def listBytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def hex (b : ByteArray) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList (b.data.toList.flatMap fun x => [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

/-! ## Permutations and rows -/

/-- A row of a permutation as four machine words (the sort and merge type). -/
structure QRow where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  deriving Inhabited, BEq, Repr

def QRow.lt (x y : QRow) : Bool :=
  if x.a != y.a then x.a < y.a
  else if x.b != y.b then x.b < y.b
  else if x.c != y.c then x.c < y.c
  else x.d < y.d

def QRow.le (x y : QRow) : Bool := !(y.lt x)

def QRow.toRow (r : QRow) : Row := ⟨r.a.toNat, r.b.toNat, r.c.toNat, r.d.toNat⟩

def permNamesArr : Array String := #["pso", "pos", "spo", "osp"]

def permOfName? (s : String) : Option Nat := permNamesArr.idxOf? s.toLower

/-- The row of quad `(s, p, o, g)` in permutation `perm`. -/
def toPerm (perm : Nat) (s p o g : UInt64) : QRow :=
  match perm with
  | 0 => ⟨p, s, o, g⟩
  | 1 => ⟨p, o, s, g⟩
  | 2 => ⟨s, p, o, g⟩
  | _ => ⟨o, s, p, g⟩

/-- The quad `(s, p, o, g)` of a row of permutation `perm`. -/
def ofPerm (perm : Nat) (c0 c1 c2 g : Nat) : Nat × Nat × Nat × Nat :=
  match perm with
  | 0 => (c1, c0, c2, g)
  | 1 => (c2, c0, c1, g)
  | 2 => (c0, c1, c2, g)
  | _ => (c1, c2, c0, g)

/-- splitmix64 finaliser. -/
def mix64 (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- The digest of one quad; a permutation's digest is the sum (mod 2^64)
    and the xor of its quads' digests, independent of row order. -/
def quadDigest (s p o g : Nat) : UInt64 :=
  mix64 (s.toUInt64 ^^^ mix64 (p.toUInt64 ^^^ mix64 (o.toUInt64 ^^^ mix64 g.toUInt64)))

structure Digest2 where
  sum : UInt64 := 0
  xor : UInt64 := 0
  rows : Nat := 0
  deriving BEq, Repr, Inhabited

def Digest2.add (d : Digest2) (h : UInt64) : Digest2 := { sum := d.sum + h, xor := d.xor ^^^ h, rows := d.rows + 1 }

/-! ## File hashing: SHA-256 and Merkle leaves -/

def chunkBytes : Nat := 65536

/-- Stream a file: its SHA-256 (HACL* block fold), its 65,536-byte Merkle
    leaves and the chunk reference. -/
def hashFile (path : String) : IO (ByteArray × Array ByteArray × Ref) := do
  let size ← fileSize path
  let mut st := L4Factoidal.Crypto.Sha256Stream.init
  let mut leaves : Array ByteArray := #[]
  let mut off := 0
  for _ in [0:size / (16 * chunkBytes) + 2] do
    if off ≥ size then break
    let len := min (16 * chunkBytes) (size - off)
    let b ← pread path off len
    st := st.updateWith Harness.nativeBlockFold256 b
    let mut i := 0
    for _ in [0:17] do
      if i ≥ b.size then break
      leaves := leaves.push (leafWith Harness.nativeHasher (b.extract i (min b.size (i + chunkBytes))))
      i := i + chunkBytes
    off := off + len
  let sha := st.finishWith Harness.nativeBlockFold256
  let root := rootWith Harness.nativeHasher leaves.toList
  pure (sha, leaves, { totalBytes := size, chunkBytes, chunkCount := leaves.size, root })

def writeLeaves (path : String) (leaves : Array ByteArray) : IO Unit := do
  let mut out := ByteArray.emptyWithCapacity (32 * leaves.size)
  for l in leaves do out := out ++ l
  IO.FS.writeBinFile (path ++ ".merkle") out

/-! ## Verification of reads (https://github.com/danbri/factoidal/issues/796) -/

/-- How a reader checks the bytes it reads from a generation. The library has
    no default: every caller of `openGen` and `Sbm11Query.openSession` names
    one.

    * `merkle`: each read is widened to the 65,536-byte chunks it touches, and
      each chunk is checked by its Merkle proof against the root in the
      manifest (the leaves come from the `.merkle` sidecar, admitted only when
      they rebuild that root); PRM1 files and GDX1 are read whole and checked
      by SHA-256. A changed byte in a chunk the reader touches is refused.
    * `none`: each read is one `pread` of exactly the bytes it needs (block
      frames, GDX1 entries, GDV1 pages); no file is hashed and no sidecar is
      read. The open still decodes the manifest and checks that every file
      has the manifest's length. The reader relies on activation
      (`l4sbm11 activate`, which checks every file's length, SHA-256, Merkle
      root and sidecar) having admitted the files, and on nobody changing
      them after that: a changed byte is NOT detected (pinned by
      `tests/sbm11/run.sh` part (g)).

    The format does not change: the packer writes the Merkle roots and
    sidecars in both cases. -/
inductive Verify where
  | merkle
  | none
  deriving BEq, Repr

def Verify.name : Verify → String
  | .merkle => "merkle"
  | .none => "none"

def Verify.ofString? : String → Option Verify
  | "merkle" => some .merkle
  | "none" => some .none
  | _ => Option.none

/-! ## An open generation -/

structure PermSrc where
  perm : Nat
  prbPath : String
  prbRef : Ref
  leaves : List L4Factoidal.Storage.BlockMerkle.Digest
  cache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  metas : Array BlockMeta
  rows : Nat

structure Gen where
  dir : String
  manifest : Manifest
  verify : Verify
  gdvPath : String
  gdxPath : String
  gdvRef : Ref
  gdxRef : Ref
  gdvLeaves : List L4Factoidal.Storage.BlockMerkle.Digest
  gdxLeaves : List L4Factoidal.Storage.BlockMerkle.Digest
  gdvCache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  gdxCache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache
  dictHdr : Dict.GdxHeader
  perms : Array PermSrc
  /-- Bytes the callers asked for, and the bytes fetched for them: under
      `merkle` the whole 65,536-byte chunks not yet in the chunk cache, under
      `none` the asked bytes themselves. -/
  readBytes : IO.Ref Nat
  fetchedBytes : IO.Ref Nat
  /-- Every byte this open read from the generation's files: the manifest,
      the `.merkle` sidecars, whole-file reads (PRM1, GDX1) and the fetched
      ranges. -/
  fileBytes : IO.Ref Nat

def manifestName : String := "manifest.sbm11"

def artifact (m : Manifest) (role : String) : IO Artifact :=
  match artifactOf? m role with
  | some a => pure a
  | none => throw (IO.userError s!"manifest has no artifact {role}")

/-- The untrusted leaves of a file, admitted only when they rebuild the
    committed root. Under `Verify.none` no sidecar is read and there are no
    leaves. -/
def loadLeaves (v : Verify) (io : IO.Ref Nat) (path : String) (ref : Ref) :
    IO (List L4Factoidal.Storage.BlockMerkle.Digest) := do
  if v == .none then return []
  let bytes ← IO.FS.readBinFile (path ++ ".merkle")
  io.modify (· + bytes.size)
  match L4Factoidal.Storage.GenerationVerify.leaves? ref.chunkCount bytes with
  | none => throw (IO.userError s!"{path}.merkle: not {ref.chunkCount} leaves")
  | some ls =>
    if rootWith Harness.nativeHasher ls != ref.root then
      throw (IO.userError s!"{path}.merkle: leaves do not rebuild the manifest root")
    pure ls

/-- An empty chunk cache under `Verify.none` (never filled), one slot per
    chunk under `merkle`. -/
def newChunkCache (v : Verify) (ref : Ref) : IO (IO.Ref Harness.PosixRangeIO.VerifiedChunkCache) :=
  if v == .merkle then Harness.PosixRangeIO.newVerifiedChunkCache ref else IO.mkRef #[]

/-- Bytes `[off, off + len)` of a file of the generation. `merkle`: through
    the verified chunk cache (`readVerifiedRangeCached?`); `none`: one `pread`
    of exactly those bytes, inside the manifest's length of the file. -/
def verifiedRead (g : Gen) (path : String) (ref : Ref) (leaves : List L4Factoidal.Storage.BlockMerkle.Digest)
    (cache : IO.Ref Harness.PosixRangeIO.VerifiedChunkCache) (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  match g.verify with
  | .none =>
    if off + len > ref.totalBytes then
      throw (IO.userError s!"{path}: read of {len} bytes at {off} past the manifest's length {ref.totalBytes}")
    let b ← pread path off len
    g.readBytes.modify (· + len)
    g.fetchedBytes.modify (· + len)
    g.fileBytes.modify (· + len)
    pure b
  | .merkle =>
    match ← Harness.PosixRangeIO.readVerifiedRangeCached? path ref leaves cache { offset := off, length := len } with
    | some (b, fp) =>
      g.readBytes.modify (· + len)
      g.fetchedBytes.modify (· + fp.fetchedBytes)
      g.fileBytes.modify (· + fp.fetchedBytes)
      pure b
    | Option.none => throw (IO.userError s!"{path}: verified read of {len} bytes at {off} refused")

/-- Under `Verify.none`: every file of the manifest has the manifest's
    length (one `stat` per file; no file is read). -/
def checkLengths (dir : String) (m : Manifest) : IO Unit := do
  for a in m.artifacts do
    let n ← fileSize s!"{dir}/{a.file}"
    if n != a.bytes then
      throw (IO.userError s!"{dir}/{a.file}: {n} bytes, the manifest says {a.bytes}")

/-- A whole PRM1 file, its length checked against the manifest, and under
    `merkle` its SHA-256 too. -/
def readPrm (v : Verify) (io : IO.Ref Nat) (prmPath : String) (prmA : Artifact) : IO ByteArray := do
  let prmBytes ← IO.FS.readBinFile prmPath
  io.modify (· + prmBytes.size)
  if prmBytes.size != prmA.bytes then
    throw (IO.userError s!"{prmPath}: length differs from the manifest")
  if v == .merkle && Harness.nativeSha256 prmBytes != prmA.sha256 then
    throw (IO.userError s!"{prmPath}: length or SHA-256 differs from the manifest")
  pure prmBytes

/-- The CLI's default when `--verify` is not given: `none` for a generation
    that a `CURRENT` pointer names (GEN is a collection root with `CURRENT`,
    or the parent of GEN has a `CURRENT` that names GEN), because activation
    checked every file's length, SHA-256 and Merkle root before it wrote
    `CURRENT`; `merkle` for any other directory. -/
def cliDefaultVerify (dir0 : String) : IO Verify := do
  let p : System.FilePath := dir0
  if ← (p / Harness.GenerationPointer.currentName).pathExists then return .none
  try
    let real ← IO.FS.realPath p
    match real.parent, real.fileName with
    | some parent, some nm =>
      let b ← IO.FS.readBinFile (parent / Harness.GenerationPointer.currentName)
      return (if String.fromUTF8? b == some nm then .none else .merkle)
    | _, _ => return .merkle
  catch _ => return .merkle

/-- Open a generation directory (or a collection root with `CURRENT`):
    decode the manifest; under `merkle` admit the Merkle leaves of every file
    and check every PRM1 file's SHA-256, under `none` check every file's
    length; read and decode every PRM1 file. -/
def openGen (v : Verify) (dir0 : String) : IO Gen := do
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
  let mut perms : Array PermSrc := #[]
  for p in [0:4] do
    let nm := (permNamesArr[p]!).toUpper
    let prmA ← artifact m s!"PRM1-{nm}"
    let prbA ← artifact m s!"PRB1-{nm}"
    let prmPath := s!"{dir}/{prmA.file}"
    let prbPath := s!"{dir}/{prbA.file}"
    let prmBytes ← readPrm v fileBytes prmPath prmA
    let some (perm, ms) := decodePrm prmBytes.data.toList
      | throw (IO.userError s!"{prmPath}: does not decode as PRM1")
    if perm != p then throw (IO.userError s!"{prmPath}: permutation code {perm}, expected {p}")
    let leaves ← loadLeaves v fileBytes prbPath prbA.merkle
    let cache ← newChunkCache v prbA.merkle
    perms := perms.push { perm := p, prbPath, prbRef := prbA.merkle, leaves, cache, metas := ms.toArray,
                          rows := rowSum ms }
  pure { g0 with dictHdr, perms }

/-- The columns of block `i` of a permutation, by verified positioned reads. -/
def readBlock (g : Gen) (ps : PermSrc) (i : Nat) : IO Cols := do
  let m := ps.metas[i]!
  let b ← verifiedRead g ps.prbPath ps.prbRef ps.leaves ps.cache m.offset m.size
  ok s!"{permNamesArr[ps.perm]!} block {i}" (decodeBlockAt b m 0)

/-! ## Key prefixes -/

/-- A key prefix: the first `k` positions of a permutation row are bound. -/
structure Prefix where
  vals : Array Nat
  deriving Repr

def Prefix.lo (p : Prefix) : Row := ⟨p.vals[0]?.getD 0, p.vals[1]?.getD 0, p.vals[2]?.getD 0, p.vals[3]?.getD 0⟩

def maxId : Nat := 18446744073709551615

def Prefix.hi (p : Prefix) : Row :=
  ⟨p.vals[0]?.getD maxId, p.vals[1]?.getD maxId, p.vals[2]?.getD maxId, p.vals[3]?.getD maxId⟩

def Prefix.matches (p : Prefix) (r : Row) : Bool :=
  (p.vals.size < 1 || r.c0 == p.vals[0]!) && (p.vals.size < 2 || r.c1 == p.vals[1]!) &&
    (p.vals.size < 3 || r.c2 == p.vals[2]!) && (p.vals.size < 4 || r.g == p.vals[3]!)

/-- The first block whose last row is not below `lo` (binary search). -/
def firstBlockGo (metas : Array BlockMeta) (lo : Row) : Nat → Nat → Nat → Nat
  | 0, l, _ => l
  | f + 1, l, h =>
    if l < h then
      let mid := (l + h) / 2
      if (metas[mid]!).last.lt lo then firstBlockGo metas lo f (mid + 1) h else firstBlockGo metas lo f l mid
    else l

def blocksFor (ps : PermSrc) (p : Prefix) : Array Nat := Id.run do
  let lo := p.lo
  let hi := p.hi
  let start := firstBlockGo ps.metas lo (Nat.log2 ps.metas.size + 2) 0 ps.metas.size
  let mut out := #[]
  let mut i := start
  for _ in [0:ps.metas.size] do
    if i ≥ ps.metas.size then break
    if hi.lt (ps.metas[i]!).first then break
    out := out.push i
    i := i + 1
  return out

structure ScanStats where
  blocks : Nat := 0
  rows : Nat := 0
  wholeBlocks : Nat := 0
  deriving Repr

/-- Rows of permutation `perm` whose key starts with `p`, in key order;
    `f` sees each row. Reads only the blocks whose `[first, last]` meets
    the prefix. -/
def permSrc (g : Gen) (perm : Nat) : IO PermSrc :=
  match g.perms[perm]? with
  | some ps => pure ps
  | none => throw (IO.userError s!"no permutation {perm}")

def scan (g : Gen) (perm : Nat) (p : Prefix) (f : Row → IO Unit) : IO ScanStats := do
  let ps ← permSrc g perm
  let mut st : ScanStats := {}
  for i in blocksFor ps p do
    let c ← readBlock g ps i
    st := { st with blocks := st.blocks + 1 }
    for j in [0:c.size] do
      let r := c.row j
      if p.matches r then
        f r
        st := { st with rows := st.rows + 1 }
  pure st

/-- The number of rows with prefix `p`: from PRM1 row counts for a block
    whose first and last row both carry the prefix (then every row between
    them does, the rows being sorted), by reading the block otherwise. -/
def count (g : Gen) (perm : Nat) (p : Prefix) : IO (Nat × ScanStats) := do
  let ps ← permSrc g perm
  let mut n := 0
  let mut st : ScanStats := {}
  for i in blocksFor ps p do
    let m := ps.metas[i]!
    if p.matches m.first && p.matches m.last then
      n := n + m.rows
      st := { st with wholeBlocks := st.wholeBlocks + 1 }
    else
      let c ← readBlock g ps i
      st := { st with blocks := st.blocks + 1 }
      for j in [0:c.size] do
        if p.matches (c.row j) then n := n + 1
  pure (n, { st with rows := n })

/-! ## Terms -/

def gdvFetch (g : Gen) (off len : Nat) : IO ByteArray :=
  verifiedRead g g.gdvPath g.gdvRef g.gdvLeaves g.gdvCache off len

def gdxFetch (g : Gen) (off len : Nat) : IO ByteArray :=
  verifiedRead g g.gdxPath g.gdxRef g.gdxLeaves g.gdxCache off len

/-- A page cache for id-to-term: page index to its keys. -/
abbrev PageCache := IO.Ref (Std.HashMap Nat (Array ByteArray))

def termOfId (g : Gen) (cache : PageCache) (id : Nat) : IO Term := do
  let tag := id / two60
  if tag == tagInt || tag == tagBool then
    match ofInlineCode? id with
    | some t => pure t
    | none => throw (IO.userError s!"inline id {id} does not decode")
  else if tag == tagBnode || tag == tagIri || tag == tagLit then
    let rank := id % two60
    if rank ≥ g.dictHdr.termCount then throw (IO.userError s!"id {id}: rank not below the term count")
    let pg := rank / Dict.pageTerms
    let c ← cache.get
    let keys ← match c.get? pg with
      | some ks => pure ks
      | none => do
        let ks ← ok s!"GDV1 page {pg}" (← (Dict.pageM (gdxFetch g) (gdvFetch g) pg).run)
        let c := if c.size ≥ 4096 then {} else c
        cache.set (c.insert pg ks)
        pure ks
    match keys[rank % Dict.pageTerms]? with
    | none => throw (IO.userError s!"id {id}: no key")
    | some kb =>
      let k := kb.data.toList
      if classTag k != tag then throw (IO.userError s!"id {id}: tag differs from the key's class")
      match decodeKey? k with
      | some t => pure t
      | none => throw (IO.userError s!"id {id}: key does not decode")
  else throw (IO.userError s!"id {id}: unknown tag {tag}")

/-- An id for a term: inline, or a dictionary lookup; `none` when the term is
    not in the dictionary. -/
def idOfTerm (g : Gen) (t : Term) : IO (Option Nat) := do
  let t := normalizeTerm t
  match inlineCode? t with
  | some c => pure (some c)
  | none =>
    match termKeyBytes? t with
    | none => pure none
    | some k =>
      let (r, _) ← ok "lookup" (← (Dict.lookupM (gdxFetch g) (gdvFetch g) g.dictHdr k).run)
      pure (r.map fun r => dictCode k.data.toList r)

def nquadLine (s p o : Term) (gname : Option Term) : Except String String := do
  let ss ← L4Factoidal.Syntax.Term.toNTriples .rdf12 s
  let ps ← L4Factoidal.Syntax.Term.toNTriples .rdf12 p
  let os ← L4Factoidal.Syntax.Term.toNTriples .rdf12 o
  match gname with
  | none => pure s!"{ss} {ps} {os} ."
  | some gt => pure s!"{ss} {ps} {os} {← L4Factoidal.Syntax.Term.toNTriples .rdf12 gt} ."

end Harness.Sbm11Gen
