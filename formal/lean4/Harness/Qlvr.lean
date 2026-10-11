/-
Harness/Qlvr — `l4qlvr`: read a QLever index directory from Lean
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

This is a HARNESS, not part of the verified library: it does file I/O,
measures time and peak RSS, and prints. The decoding is
`L4Factoidal.Qlvr.*`. Permutation files are read with positioned reads
(`pread`, `ffi/block_pread.c`): the trailing metadata first, then only the
column frames of the blocks a command needs. The three vocabulary files are
read whole (16 MB for the instance); a word is decoded only when it is used.

  l4qlvr stats INDEXDIR            counts per permutation, vocabulary size
  l4qlvr scan INDEXDIR PRED-IRI    the PSO scan of one predicate, as N-Triples
  l4qlvr dump INDEXDIR             every triple of SPO as N-Triples, one block
                                   at a time
  l4qlvr words INDEXDIR            every vocabulary word as an N-Triples term,
                                   one per line, in index order

Timings and peak RSS (VmHWM) go to stderr; data goes to stdout.
-/
import L4Factoidal.Qlvr.Scan

open L4Factoidal.Qlvr

namespace QlvrTool

/-- Positioned read; the C side returns an empty array on any failure. -/
@[extern "l4_block_pread"]
opaque preadRaw (path : @& String) (offset length : UInt64) : IO ByteArray

def pread (path : String) (off len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  let b ← preadRaw path off.toUInt64 len.toUInt64
  if b.size != len then throw (IO.userError s!"{path}: short read of {len} bytes at {off}")
  pure b

def vmHWM : IO String := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    match (s.splitOn "\n").find? (·.startsWith "VmHWM:") with
    | some l => pure ((l.drop 6).trimAscii.toString)
    | none => pure "n/a"
  catch _ => pure "n/a"

def ok {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def fileSize (p : String) : IO Nat := do
  pure (← System.FilePath.metadata p).byteSize.toNat

/-- The base name: the one `<base>.meta-data.json` in the directory. -/
def findBase (dir : String) : IO String := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    let n := e.fileName
    if n.endsWith ".meta-data.json" then some (n.dropEnd ".meta-data.json".length).toString else none
  match names.toList with
  | [b] => pure b
  | [] => throw (IO.userError s!"{dir}: no <base>.meta-data.json")
  | _ => throw (IO.userError s!"{dir}: more than one <base>.meta-data.json")

/-- Refuse an index whose format version or vocabulary type this reader
    was not written for (format record, section 5). -/
def checkMetaData (dir base : String) : IO Unit := do
  let s ← IO.FS.readFile s!"{dir}/{base}.meta-data.json"
  let has (t : String) := (s.splitOn t).length > 1
  unless has "\"index-format-version\":{\"date\":\"2026-09-26\",\"pull-request-number\":3470}" do
    throw (IO.userError "meta-data.json: index-format-version is not 2026-09-26 / 3470")
  unless has "\"vocabulary-type\":\"on-disk-compressed\"" do
    throw (IO.userError "meta-data.json: vocabulary-type is not on-disk-compressed")

def loadVocab (dir base : String) : IO Vocab := do
  let p := s!"{dir}/{base}.vocabulary"
  let cb ← IO.FS.readBinFile (p ++ ".codebooks")
  let off ← IO.FS.readBinFile (p ++ ".words.external.offsets")
  let ext ← IO.FS.readBinFile (p ++ ".words.external")
  ok "vocabulary" (Vocab.load cb off ext)

/-- Read a permutation's trailing metadata with two positioned reads. -/
def loadPermMeta (path : String) : IO PermMeta := do
  let sz ← fileSize path
  if sz < 8 then throw (IO.userError s!"{path}: shorter than its trailer")
  let start ← ok path (metaStart (← pread path (sz - 8) 8) sz)
  ok path (parsePermMeta (← pread path start (sz - 8 - start)) sz)

def ms (t0 t1 : Nat) : Nat := (t1 - t0) / 1000000

def perms : List String :=
  ["index.pso", "index.pos", "index.spo", "index.sop", "index.osp", "index.ops",
   "internal.index.pso", "internal.index.pos"]

def runStats (dir : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  IO.println s!"vocabulary words: {v.size}; decoder pairs: {v.decoders.size}"
  for p in perms do
    let path := s!"{dir}/{base}.{p}"
    unless (← System.FilePath.pathExists path) do continue
    let pm ← loadPermMeta path
    let rows := pm.blocks.foldl (fun a b => a + b.rows) 0
    let ncols := pm.blocks.foldl (fun (a : List Nat) b => if a.contains b.cols.size then a else a ++ [b.cols.size]) []
    let rels ← ok (path ++ ".meta") (parseRelations (← IO.FS.readBinFile (path ++ ".meta")))
    IO.println s!"{p}: blocks {pm.blocks.size}; triples {pm.totalElements}; rows in blocks {rows}; distinct col0 {pm.distinctCol0}; columns per block {ncols}; large relations in .meta {rels.size}"
    if rows != pm.totalElements then
      throw (IO.userError s!"{p}: block rows {rows} != totalElements {pm.totalElements}")
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"stats: {ms t0 t1} ms; peak RSS (VmHWM): {← vmHWM}"
  pure 0

/-- The stored form of an IRI argument (`<...>` added when missing). -/
def storedIri (s : String) : String :=
  if s.startsWith "<" then s else "<" ++ s ++ ">"

def runScan (dir iri : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  let target := storedIri iri
  let t1 ← IO.monoNanosNow
  let (lo, hi) ← ok "vocabulary" (v.firstByteRange target.toUTF8)
  let found ← ok "vocabulary" (v.findWord target)
  let t2 ← IO.monoNanosNow
  match found with
  | none =>
    IO.eprintln s!"scan: {target} is not in the vocabulary (searched words {lo}..{hi})"
    pure 1
  | some idx =>
    let pred := Id.ofVocabIndex idx
    let path := s!"{dir}/{base}.index.pso"
    let pm ← loadPermMeta path
    let selected := (pm.blocks.filter (·.covers pred)).size
    let pairs ← ok "scan" (← (scanCol0M (pread path) pm pred).run)
    let out ← ok "render" (renderPairs v pairs target.toUTF8 (pairs.size + 1) 0 ByteArray.empty)
    let t3 ← IO.monoNanosNow
    (← IO.getStdout).write out
    IO.eprintln s!"scan {target}: VocabIndex {idx}; vocabulary lookup {ms t1 t2} ms over {idx - lo + 1} decoded words (first-byte range {lo}..{hi} of {v.size}); PSO blocks read {selected} of {pm.blocks.size}; rows {pairs.size}; scan and render {ms t2 t3} ms; total {ms t0 t3} ms; peak RSS (VmHWM): {← vmHWM}"
    pure 0

def runDump (dir : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  let path := s!"{dir}/{base}.index.spo"
  let pm ← loadPermMeta path
  let stdout ← IO.getStdout
  let mut lines := 0
  for b in pm.blocks do
    let cols ← ok s!"block {b.index}" (← (fetchColumns (pread path) b 3).run)
    let (out, n) ← ok s!"block {b.index}" (renderBlock v cols (0, 1, 2) none b.rows)
    stdout.write out
    lines := lines + n
  stdout.flush
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"dump: {lines} triples from {pm.blocks.size} SPO blocks in {ms t0 t1} ms; peak RSS (VmHWM): {← vmHWM}"
  if lines != pm.totalElements then
    IO.eprintln s!"dump: FAIL: {lines} lines, metadata says {pm.totalElements}"
    return 1
  pure 0

def runWords (dir : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  let stdout ← IO.getStdout
  let chunk := 65536
  let mut i := 0
  for _ in [0:(v.size + chunk - 1) / chunk] do
    let stop := min v.size (i + chunk)
    stdout.write (← ok "words" (renderWords v stop (stop - i + 1) i ByteArray.empty))
    i := stop
  stdout.flush
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"words: {v.size} in {ms t0 t1} ms; peak RSS (VmHWM): {← vmHWM}"
  pure 0

end QlvrTool

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["stats", dir] => QlvrTool.runStats dir
    | ["scan", dir, iri] => QlvrTool.runScan dir iri
    | ["dump", dir] => QlvrTool.runDump dir
    | ["words", dir] => QlvrTool.runWords dir
    | _ =>
      IO.eprintln "usage: l4qlvr stats INDEXDIR | scan INDEXDIR PRED-IRI | dump INDEXDIR | words INDEXDIR"
      pure 2
  catch e =>
    IO.eprintln s!"l4qlvr: {e}"
    pure 1
