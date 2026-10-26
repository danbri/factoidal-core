/- l4merkle-range-read -- make a chunked file with its Merkle sidecar, and read a
   range of it through the verified range readers of `Harness.PosixRangeIO`.

   Usage:
     l4merkle-range-read make DIR CHUNKS [TAIL]
         DIR/file.bin: CHUNKS chunks of 65,536 bytes, the last one of TAIL bytes
         (1 to 65,536; default 65,536). Every chunk is different: its first 8
         bytes are its number (little endian), the rest is a pseudo-random block
         (splitmix64) the same for every chunk. DIR/file.bin.merkle: the 32-byte
         leaf of each chunk. DIR/root: the Merkle root, 64 hex digits. Prints the
         size of the file.
     l4merkle-range-read read DIR [--reader leaves|tree|cached] [--offset O] [--length L] [--check]
         Read the bytes [O, O + L) of DIR/file.bin (default: the whole file) with
         the reader, against the root in DIR/root. `leaves`: `readVerifiedRange?`
         (no cache; it builds the proof table from the leaves). `tree`:
         `readVerifiedRangeTree?` with a table built here. `cached`:
         `readVerifiedRangeCached?` with a new cache. Prints
         `l4merkle-range-read reader=R offset=O length=L verified-bytes=N
         chunks=F-L`; exit 1 when the reader refuses the range. With `--check` it
         also reads the same bytes without any check, and prints `match=true` when
         the SHA-256 of the two agree (exit 1 when they do not). The check costs
         two more passes over the range, so a timed run does not use it.

   This is the input of the row `merkle-range-read-time` of
   tests/stack/lean_scaling.py and of tests/merkle-range/run.sh
   (https://github.com/danbri/factoidal/issues/859). The shard packer cuts its
   blocks at 2 MiB, so a shard directory that it writes has no artifact above about
   64 chunks. Before the issue was repaired, the cost of `readVerifiedRange?` for a
   read of a whole file was the larger one of two terms from about 450 chunks
   (30 MB). `make` writes a file of 2,048 chunks (128 MB) in 1 s. -/
import Harness.PosixRangeIO
import Harness.NativeHasher
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.BlockMerkle

namespace Harness.MerkleRangeRead

open Harness.PosixRangeIO
open L4Factoidal.Storage.BlockMerkle
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.IndexedBlockWireV2 (ByteRange)

def chunkBytes : Nat := 65536

private def mix64 (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- 65,536 pseudo-random bytes. A function of `Unit`, so that no other
    executable evaluates it at start. -/
private def baseBlock (_ : Unit) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity chunkBytes
  let mut s : UInt64 := 12345
  for _ in [0:chunkBytes / 8] do
    s := mix64 s
    let mut v := s
    for _ in [0:8] do
      b := b.push v.toUInt8
      v := v >>> 8
  return b

/-- Chunk `i` of `len` bytes: the base block with `i` in its first 8 bytes. -/
private def chunkOf (base : ByteArray) (i len : Nat) : ByteArray :=
  let c := Id.run do
    let mut c := base
    let mut v := i
    for k in [0:8] do
      c := c.set! k (v % 256).toUInt8
      v := v / 256
    return c
  if len == chunkBytes then c else c.extract 0 len

def hex (b : ByteArray) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList (b.data.toList.flatMap fun x => [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes of a string of hex digits (an even number of them). -/
private def unhex? (s : String) : Option ByteArray :=
  let ds := s.toList.mapM hexDigit?
  match ds with
  | none => none
  | some ds =>
    if ds.length % 2 != 0 then none
    else
      let rec go : List Nat → ByteArray → ByteArray
        | hi :: lo :: rest, acc => go rest (acc.push (hi * 16 + lo).toUInt8)
        | _, acc => acc
      some (go ds ByteArray.empty)

private def make (dir : String) (chunks tail : Nat) : IO UInt32 := do
  if chunks == 0 || tail == 0 || tail > chunkBytes then
    IO.eprintln "l4merkle-range-read make: CHUNKS is at least 1, TAIL is 1 to 65536"
    return 2
  IO.FS.createDirAll dir
  let path := s!"{dir}/file.bin"
  let base := baseBlock ()
  let leaves ← IO.FS.withFile path .write fun h => do
    let mut leaves : Array ByteArray := #[]
    for i in [0:chunks] do
      let len := if i + 1 == chunks then tail else chunkBytes
      let c := chunkOf base i len
      h.write c
      leaves := leaves.push (leafWith nativeHasher c)
    h.flush
    pure leaves
  IO.FS.writeBinFile (path ++ ".merkle") (leaves.foldl (· ++ ·) ByteArray.empty)
  IO.FS.writeFile s!"{dir}/root" (hex (rootWith nativeHasher leaves.toList) ++ "\n")
  IO.println s!"l4merkle-range-read make chunks={chunks} bytes={(chunks - 1) * chunkBytes + tail}"
  return 0

private structure Opts where
  reader : String := "leaves"
  offset : Option Nat := none
  length : Option Nat := none
  check : Bool := false

private def parseOpts : List String → Opts → Option Opts
  | [], o => some o
  | "--reader" :: v :: rest, o => parseOpts rest { o with reader := v }
  | "--offset" :: v :: rest, o => v.toNat?.bind fun n => parseOpts rest { o with offset := some n }
  | "--length" :: v :: rest, o => v.toNat?.bind fun n => parseOpts rest { o with length := some n }
  | "--check" :: rest, o => parseOpts rest { o with check := true }
  | _, _ => none

private def readMode (dir : String) (o : Opts) : IO UInt32 := do
  let path := s!"{dir}/file.bin"
  let size := (← System.FilePath.metadata path).byteSize.toNat
  let rootText := (← IO.FS.readFile s!"{dir}/root").trimAscii.toString
  let some root := unhex? rootText
    | IO.eprintln "l4merkle-range-read: DIR/root is not hex"; return 1
  let ref : Ref := { totalBytes := size, chunkBytes, chunkCount := (size + chunkBytes - 1) / chunkBytes, root }
  let some leaves := leaves? ref.chunkCount (← IO.FS.readBinFile (path ++ ".merkle"))
    | IO.eprintln "l4merkle-range-read: DIR/file.bin.merkle does not hold one leaf for each chunk"; return 1
  let range : ByteRange := { offset := o.offset.getD 0, length := o.length.getD (size - o.offset.getD 0) }
  let got? ← match o.reader with
    | "leaves" => readVerifiedRange? path ref leaves range
    | "tree" => readVerifiedRangeTree? path ref (treeOfLeaves leaves) range
    | "cached" =>
        let cache ← newVerifiedChunkCache ref
        pure ((← readVerifiedRangeCached? path ref leaves cache range).map (·.1))
    | other => do IO.eprintln s!"l4merkle-range-read: unknown reader {other} (leaves, tree, cached)"; pure none
  let some got := got?
    | IO.eprintln s!"l4merkle-range-read: reader {o.reader} refused the range [{range.offset}, {range.offset + range.length})"
      return 1
  let first := range.offset / chunkBytes
  let last := (range.offset + range.length - 1) / chunkBytes
  let base := s!"l4merkle-range-read reader={o.reader} offset={range.offset} length={range.length} verified-bytes={got.size} chunks={first}-{last}"
  if !o.check then
    IO.println base
    return 0
  -- the same bytes without any check
  let raw ← preadRaw path range.offset.toUInt64 range.length.toUInt64
  let same := nativeSha256 raw == nativeSha256 got
  IO.println s!"{base} sha256={hex (nativeSha256 got)} match={same}"
  return (if same then 0 else 1)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["make", dir, chunks] =>
        match chunks.toNat? with
        | some c => make dir c chunkBytes
        | none => IO.eprintln "usage: l4merkle-range-read make DIR CHUNKS [TAIL]"; pure 2
    | ["make", dir, chunks, tail] =>
        match chunks.toNat?, tail.toNat? with
        | some c, some t => make dir c t
        | _, _ => IO.eprintln "usage: l4merkle-range-read make DIR CHUNKS [TAIL]"; pure 2
    | "read" :: dir :: rest =>
        match parseOpts rest {} with
        | some o => readMode dir o
        | none =>
            IO.eprintln "usage: l4merkle-range-read read DIR [--reader leaves|tree|cached] [--offset O] [--length L] [--check]"
            pure 2
    | _ =>
        IO.eprintln "usage: l4merkle-range-read make DIR CHUNKS [TAIL] | read DIR [--reader leaves|tree|cached] [--offset O] [--length L] [--check]"
        pure 2
  catch e =>
    IO.eprintln s!"l4merkle-range-read: {e}"
    pure 1

end Harness.MerkleRangeRead

def main (args : List String) : IO UInt32 := Harness.MerkleRangeRead.main args
