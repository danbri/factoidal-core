/-
Harness/QlvrZstdCheck — `l4qlvr-zstd-check`: run `L4Factoidal.Codec.Zstd`
against libzstd's answers (https://github.com/danbri/factoidal/issues/778).

This is a HARNESS, not part of the verified library: it reads files, times
the decoder and prints scores. Three modes:

  l4qlvr-zstd-check vectors DIR
      DIR/expected.tsv lists `name size sha256`; decode DIR/<name>.zst and
      compare the size and the sha256 of the output.
      (Vectors: formal/lean4/Harness/TestData/zstd, written by
      tools/qlvr/zstd_vectors.py.)
  l4qlvr-zstd-check blocks INDEXDIR TSV
      TSV lines `file offset length size sha256` (written by
      `tools/qlvr/probe_index.py --zstd-tsv`): decode bytes
      [offset, offset+length) of INDEXDIR/file, one zstd frame each, and
      compare with libzstd's output. Prints the score, the counts of zstd
      blocks and literal sections by type, the decode time and throughput
      (output bytes per second, decode only, sha256 excluded) and the peak
      resident set size (VmHWM from /proc/self/status).
  l4qlvr-zstd-check frame FILE SHA256
      decode one file (any number of frames) and compare the sha256; used by
      tests/stack under a reduced stack.

Scores print as "N pass, M fail (out of T)". The exit code is 0 only when
every case passes.
-/
import L4Factoidal.Codec.Zstd
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.SHA2Native

open L4Factoidal.Codec.Zstd
open L4Factoidal.Crypto

namespace QlvrZstdCheck

def shaHex (b : ByteArray) : String := bytesToHex (sha256Hacl b)

/-- Peak resident set size from /proc/self/status (Linux), or "n/a". -/
def vmHWM : IO String := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    match (s.splitOn "\n").find? (·.startsWith "VmHWM:") with
    | some l => pure ((l.drop 6).trimAscii.toString)
    | none => pure "n/a"
  catch _ => pure "n/a"

def addStats (a b : Stats) : Stats :=
  { frames := a.frames + b.frames, rawBlocks := a.rawBlocks + b.rawBlocks,
    rleBlocks := a.rleBlocks + b.rleBlocks,
    compressedBlocks := a.compressedBlocks + b.compressedBlocks,
    rawLits := a.rawLits + b.rawLits, rleLits := a.rleLits + b.rleLits,
    hufLits := a.hufLits + b.hufLits, treelessLits := a.treelessLits + b.treelessLits,
    sequences := a.sequences + b.sequences }

def statsLine (s : Stats) : String :=
  s!"frames {s.frames}; zstd blocks {s.rawBlocks + s.rleBlocks + s.compressedBlocks} " ++
  s!"(raw {s.rawBlocks}, RLE {s.rleBlocks}, compressed {s.compressedBlocks}); " ++
  s!"literal sections raw {s.rawLits}, RLE {s.rleLits}, Huffman {s.hufLits}, " ++
  s!"treeless {s.treelessLits}; sequences {s.sequences}"

def fields (line : String) : List String :=
  (line.splitOn "\t").filter (· ≠ "")

def runVectors (dir : String) : IO UInt32 := do
  let tsv ← IO.FS.readFile (dir ++ "/expected.tsv")
  let mut pass := 0
  let mut fail := 0
  let mut stats : Stats := {}
  for line in tsv.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match fields line with
    | [name, size, sha] =>
      let blob ← IO.FS.readBinFile s!"{dir}/{name}.zst"
      match decompressStats blob with
      | .ok (out, st) =>
        stats := addStats stats st
        if toString out.size == size && shaHex out == sha then
          pass := pass + 1
          IO.println s!"ok   {name}: {out.size} bytes"
        else
          fail := fail + 1
          IO.println s!"FAIL {name}: {out.size} bytes, sha256 {shaHex out}, want {size} bytes {sha}"
      | .error e =>
        fail := fail + 1
        IO.println s!"FAIL {name}: {e}"
    | _ => IO.println s!"skip malformed line: {line}"
  IO.println (statsLine stats)
  IO.println s!"zstd vectors: {pass} pass, {fail} fail (out of {pass + fail})"
  pure (if fail == 0 && pass > 0 then 0 else 1)

def runBlocks (dir tsvPath : String) : IO UInt32 := do
  let tsv ← IO.FS.readFile tsvPath
  let mut pass := 0
  let mut fail := 0
  let mut stats : Stats := {}
  let mut curName := ""
  let mut cur := ByteArray.empty
  let mut nanos : Nat := 0
  let mut outBytes : Nat := 0
  let mut inBytes : Nat := 0
  for line in tsv.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match fields line with
    | [file, off, len, size, sha] =>
      if file != curName then
        cur ← IO.FS.readBinFile s!"{dir}/{file}"
        curName := file
      let o := off.toNat!
      let n := len.toNat!
      let frame := cur.extract o (o + n)
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure fun _ => decompressStats frame
      -- an effect that depends on the result, so the decode runs before t1
      let ok := match r with | .ok (out, _) => out.size | .error _ => 0
      if ok == 1 then IO.print ""
      let t1 ← IO.monoNanosNow
      nanos := nanos + (t1 - t0)
      inBytes := inBytes + n
      match r with
      | .ok (out, st) =>
        stats := addStats stats st
        outBytes := outBytes + ok
        if toString out.size == size && shaHex out == sha then pass := pass + 1
        else
          fail := fail + 1
          IO.println s!"FAIL {file}@{off}: {out.size} bytes, want {size}"
      | .error e =>
        fail := fail + 1
        IO.println s!"FAIL {file}@{off}: {e}"
    | _ => IO.println s!"skip malformed line: {line}"
  IO.println (statsLine stats)
  let ms := nanos / 1000000
  let mbps := if nanos == 0 then 0 else outBytes * 1000 / nanos
  IO.println s!"decode: {inBytes} compressed bytes to {outBytes} bytes in {ms} ms ({mbps} MB/s of output)"
  IO.println s!"peak RSS (VmHWM): {← vmHWM}"
  IO.println s!"qlever zstd frames: {pass} pass, {fail} fail (out of {pass + fail})"
  pure (if fail == 0 && pass > 0 then 0 else 1)

def runFrame (file sha : String) : IO UInt32 := do
  let blob ← IO.FS.readBinFile file
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => decompressStats blob
  let sz := match r with | .ok (out, _) => out.size | .error _ => 0
  if sz == 1 then IO.print ""
  let t1 ← IO.monoNanosNow
  match r with
  | .ok (out, st) =>
    let got := shaHex out
    IO.println (statsLine st)
    IO.println s!"{out.size} bytes in {(t1 - t0) / 1000000} ms; peak RSS (VmHWM): {← vmHWM}"
    if got == sha then
      IO.println "ok"; pure 0
    else
      IO.println s!"FAIL: sha256 {got}, want {sha}"; pure 1
  | .error e =>
    IO.println s!"FAIL: {e}"; pure 1

end QlvrZstdCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | ["vectors", dir] => QlvrZstdCheck.runVectors dir
  | ["blocks", dir, tsv] => QlvrZstdCheck.runBlocks dir tsv
  | ["frame", file, sha] => QlvrZstdCheck.runFrame file sha
  | _ =>
    IO.eprintln "usage: l4qlvr-zstd-check vectors DIR | blocks INDEXDIR TSV | frame FILE SHA256"
    pure 2
