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
  l4qlvr side-index INDEXDIR       write the side index INDEXDIR.qlvr-side/
                                   (words in byte order with their VocabIndex),
                                   by an external merge sort
  l4qlvr side-check INDEXDIR [W..] side index against the linear scan: the
                                   stored forms W, 1,000 sampled words and 100
                                   words that are not in the vocabulary
  l4qlvr query INDEXDIR 'SPARQL'   answer a SELECT query (L4Factoidal.Qlvr.Query)
  l4qlvr query INDEXDIR --file F   as SPARQL JSON on stdout; --explain prints the
                                   plan to stderr; --constants prints the stored
                                   forms the query looks up, one per line, and
                                   does not run it. Exit 3: the query is outside
                                   the fragment (refused); exit 1: an error.
                                   --repeat N: load once, run N times in this
                                   process, print the last answer and the median
                                   execution time; --libzstd: decode column
                                   frames with libzstd (ffi/qlvr_zstd.c, dlopen)
                                   in place of the Lean decoder, for
                                   measurement; --reference-render: write the
                                   answer through idTerm and SPARQL.rowJson (the
                                   reference) in place of the byte renderer
  l4qlvr serve INDEXDIR [--libzstd]
                                   load once; answer one query per line of stdin
                                   (a query, or --file PATH); one line of SPARQL
                                   JSON per query on stdout, timings on stderr
  l4qlvr zstd-diff INDEXDIR        every column frame through the Lean decoder
                                   and libzstd: byte comparison and times
  l4qlvr kernel-dump INDEXDIR OUT  the input of the q07 kernel
                                   (Harness/QlvrKernel.lean)
  l4qlvr kernel FILE [ITERS]       the Lean implementations of the kernel; the
                                   C reference is tools/qlvr/bench/kernel.c
                                   (tests/qlvr/kernel.sh runs both)

Performance record: docs/designissues/2026-10-11-qlvr-performance.md.

Timings and peak RSS (VmHWM) go to stderr; data goes to stdout.
-/
import L4Factoidal.Qlvr.Scan
import L4Factoidal.Qlvr.Query
import Harness.QlvrKernel

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

/-! ## Side index -/

def sideDir (dir : String) : String :=
  (dir.dropEndWhile (· == '/')).toString ++ ".qlvr-side"

/-- A sequential reader of one run file, by positioned reads of 1 MiB. -/
structure RunReader where
  path : String
  size : Nat
  base : Nat
  buf : ByteArray
  pos : Nat
  deriving Inhabited

def RunReader.ensure (r : RunReader) (need : Nat) : IO RunReader := do
  if r.pos + need ≤ r.buf.size then return r
  let base := r.base + r.pos
  let len := min (r.size - base) (max need (1 <<< 20))
  if len < need then throw (IO.userError s!"{r.path}: truncated record at {base}")
  return { r with base, buf := ← pread r.path base len, pos := 0 }

def RunReader.next (r : RunReader) : IO (Option (ByteArray × Nat) × RunReader) := do
  if r.base + r.pos ≥ r.size then return (none, r)
  let r ← r.ensure 4
  let len := Side.get32 r.buf r.pos
  let r ← r.ensure (12 + len)
  let w := r.buf.extract (r.pos + 4) (r.pos + 4 + len)
  let idx := (L4Factoidal.Codec.Zstd.word64 r.buf (r.pos + 4 + len)).toNat
  return (some (w, idx), { r with pos := r.pos + 12 + len })

def offsetsHash (v : Vocab) : UInt64 := L4Factoidal.Codec.Zstd.xxh64 v.offsets 0 v.offsets.size

def runSideIndex (dir : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  let sd := sideDir dir
  IO.FS.createDirAll sd
  let chunk := 65536
  let nRuns := (v.size + chunk - 1) / chunk
  let mut runs : Array String := #[]
  for r in [0:nRuns] do
    let lo := r * chunk
    let hi := min v.size (lo + chunk)
    let mut ws : Array (ByteArray × Nat) := Array.mkEmpty (hi - lo)
    for i in [lo:hi] do
      ws := ws.push (← ok "vocabulary" (v.wordBytes i), i)
    let path := s!"{sd}/run-{r}.tmp"
    IO.FS.writeBinFile path (Side.encodeRun (Side.sortChunk ws))
    runs := runs.push path
  let t1 ← IO.monoNanosNow
  -- merge
  let mut readers : Array RunReader := #[]
  let mut heads : Array (Option (ByteArray × Nat)) := #[]
  for path in runs do
    let (h, r) ← RunReader.next { path, size := ← fileSize path, base := 0, buf := .empty, pos := 0 }
    readers := readers.push r
    heads := heads.push h
  let sortedTmp := s!"{sd}/words.sorted.tmp"
  let entriesTmp := s!"{sd}/words.entries.tmp"
  let hS ← IO.FS.Handle.mk sortedTmp .write
  let hE ← IO.FS.Handle.mk entriesTmp .write
  let mut bufS := ByteArray.emptyWithCapacity (1 <<< 20)
  let mut bufE := ByteArray.emptyWithCapacity (1 <<< 20)
  let mut written := 0
  let mut count := 0
  let mut prev : ByteArray := .empty
  for _ in [0:v.size] do
    let mut best : Option (Nat × ByteArray × Nat) := none
    for k in [0:heads.size] do
      match heads[k]! with
      | some (w, idx) =>
        match best with
        | some (_, bw, _) => if cmpBytes w bw == .lt then best := some (k, w, idx)
        | none => best := some (k, w, idx)
      | none => pure ()
    match best with
    | none => break
    | some (k, w, idx) =>
      if count > 0 && cmpBytes prev w != .lt then
        throw (IO.userError s!"side-index: words not strictly increasing at entry {count} (VocabIndex {idx})")
      bufE := Side.encodeEntry bufE written w.size idx
      bufS := bufS ++ w
      written := written + w.size
      count := count + 1
      prev := w
      let (h, r) ← readers[k]!.next
      readers := readers.set! k r
      heads := heads.set! k h
      if bufS.size ≥ (1 <<< 20) then
        hS.write bufS
        bufS := ByteArray.emptyWithCapacity (1 <<< 20)
      if bufE.size ≥ (1 <<< 20) then
        hE.write bufE
        bufE := ByteArray.emptyWithCapacity (1 <<< 20)
  hS.write bufS
  hE.write bufE
  hS.flush
  hE.flush
  if count != v.size || heads.any (·.isSome) then
    throw (IO.userError s!"side-index: merged {count} words, vocabulary has {v.size}")
  let hdr : Side.Header := { count, externalSize := v.external.size, offsetsHash := offsetsHash v,
                             sortedSize := written }
  IO.FS.rename sortedTmp s!"{sd}/words.sorted"
  IO.FS.rename entriesTmp s!"{sd}/words.entries"
  IO.FS.writeBinFile s!"{sd}/side.header" hdr.encode
  for path in runs do IO.FS.removeFile path
  let t2 ← IO.monoNanosNow
  IO.eprintln s!"side-index: {count} words in {sd}; {nRuns} sorted runs of up to {chunk} words in {ms t0 t1} ms (vocabulary load included); merge {ms t1 t2} ms; total {ms t0 t2} ms; words.sorted {written} bytes, words.entries {count * Side.entryBytes} bytes; peak RSS (VmHWM): {← vmHWM}"
  pure 0

/-- An open side index: the entry count and its directory. -/
structure SideIdx where
  dir : String
  count : Nat

def openSide (dir : String) (v : Vocab) : IO (Option SideIdx) := do
  let sd := sideDir dir
  let hp := s!"{sd}/side.header"
  unless (← System.FilePath.pathExists hp) do return none
  let h ← ok hp (Side.Header.parse (← IO.FS.readBinFile hp))
  if h.count != v.size || h.externalSize != v.external.size || h.offsetsHash != offsetsHash v then
    throw (IO.userError s!"{sd}: side index does not match this vocabulary (rebuild with l4qlvr side-index)")
  return some { dir := sd, count := h.count }

def SideIdx.lookup (s : SideIdx) (stored : String) : IO (Option Nat × Nat) := do
  let r ← (Side.sideLookupM (pread s!"{s.dir}/words.entries") (pread s!"{s.dir}/words.sorted")
            s.count stored.toUTF8).run
  ok "side index" r

def runSideCheck (dir : String) (given : List String) : IO UInt32 := do
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  let some side ← openSide dir v | do
    IO.eprintln s!"side-check: no side index at {sideDir dir} (run l4qlvr side-index)"
    return 2
  let mut pass := 0
  let mut fail := 0
  -- (a) the given stored forms: findWord (first-byte binary search, then a linear scan)
  let ta ← IO.monoNanosNow
  for w in given do
    let lin ← ok "vocabulary" (v.findWord w)
    let (sid, _) ← side.lookup w
    if lin == sid then pass := pass + 1
    else
      fail := fail + 1
      IO.println s!"DIFFERENT {w}: linear {lin}, side {sid}"
  let tb ← IO.monoNanosNow
  -- (b) 1,000 sampled words and 100 absent words: one linear pass over the
  -- whole vocabulary gives each target's first index
  let samples := (List.range 1000).map fun k => (k * v.size) / 1000 + (k % 7)
  let mut targets : Array String := #[]
  for i in samples do
    if i < v.size then targets := targets.push (← ok "vocabulary" (vocabWord v i))
  let nSampled := targets.size
  for k in [0:100] do
    targets := targets.push (targets[k * 10 % nSampled]! ++ "#qlvr-absent")
  let mut want : Std.HashMap String (Option Nat) := {}
  for t in targets do want := want.insert t none
  for i in [0:v.size] do
    let w ← ok "vocabulary" (vocabWord v i)
    if want.get? w == some none then want := want.insert w (some i)
  let tc ← IO.monoNanosNow
  let mut probes := 0
  for t in targets do
    let (sid, p) ← side.lookup t
    probes := probes + p
    let lin := (want.get? t).getD none
    if lin == sid then pass := pass + 1
    else
      fail := fail + 1
      IO.println s!"DIFFERENT {t}: linear {lin}, side {sid}"
  let td ← IO.monoNanosNow
  IO.println s!"side-check: {pass} pass, {fail} fail (out of {pass + fail}): {given.length} given stored forms, {nSampled} sampled words, 100 absent words"
  IO.eprintln s!"side-check: given forms by findWord {ms ta tb} ms; one linear pass for the samples {ms tb tc} ms; side index for the samples {ms tc td} ms, {probes} probes ({targets.size} lookups); peak RSS (VmHWM): {← vmHWM}"
  return (if fail == 0 then 0 else 1)

/-! ## Query -/

/-- libzstd, loaded at run time by `ffi/qlvr_zstd.c` (dlopen). Only for
    measurement; the pure Lean decoder is the reference and the default. -/
@[extern "l4_zstd_available"]
opaque zstdAvailable : IO Bool

/-- Decompress one column frame with libzstd into exactly `size` bytes; an
    empty array on any failure. -/
@[extern "l4_zstd_decompress"]
opaque zstdDecompressRaw (frame : @& ByteArray) (size : UInt64) : IO ByteArray

/-- The column decoder: the pure Lean one (the reference) or libzstd. -/
inductive Codec where
  | lean
  | libzstd
  deriving BEq

def Codec.name : Codec → String
  | .lean => "lean"
  | .libzstd => "libzstd"

/-- The pure Lean decoder as an IO step of its own, so that the time taken
    around the call is the decode time. -/
@[noinline] def decodeLeanIO (frame : ByteArray) (rows : Nat) : IO (Except String ByteArray) :=
  pure (decodeColumn frame rows)

def decodeWith (codec : Codec) (frame : ByteArray) (rows : Nat) : IO (Except String ByteArray) := do
  match codec with
  | .lean => decodeLeanIO frame rows
  | .libzstd =>
    let out ← zstdDecompressRaw frame (8 * rows).toUInt64
    if out.size != 8 * rows then return .error s!"libzstd: {out.size} bytes, want {8 * rows}"
    return .ok out

/-- Per-run counters of the column reads. -/
structure IoCounters where
  preadNs : Nat := 0
  decodeNs : Nat := 0
  frames : Nat := 0
  frameBytes : Nat := 0
  outBytes : Nat := 0

/-- What `l4qlvr query` and `l4qlvr serve` load once: the vocabulary, the
    six permutation trailers, the side index. -/
structure Session where
  dir : String
  vocab : Vocab
  srcs : Array (PermSrc IO)
  side : Option SideIdx
  codec : Codec
  counters : IO.Ref IoCounters

def openSession (dir : String) (codec : Codec) : IO Session := do
  let base ← findBase dir
  checkMetaData dir base
  let v ← loadVocab dir base
  if codec == .libzstd && !(← zstdAvailable) then
    throw (IO.userError "--libzstd: libzstd.so.1 could not be loaded")
  let counters ← IO.mkRef ({} : IoCounters)
  let mut srcs : Array (PermSrc IO) := #[]
  for pi in permInfos do
    let path := s!"{dir}/{base}.index.{pi.name}"
    let pm ← loadPermMeta path
    let column (cr : ColumnRef) (rows : Nat) : IO (Except String ByteArray) := do
      let a ← IO.monoNanosNow
      let frame ← pread path cr.offset cr.size
      let b ← IO.monoNanosNow
      let r ← decodeWith codec frame rows
      let c ← IO.monoNanosNow
      counters.modify fun k =>
        { preadNs := k.preadNs + (b - a), decodeNs := k.decodeNs + (c - b), frames := k.frames + 1,
          frameBytes := k.frameBytes + cr.size, outBytes := k.outBytes + 8 * rows }
      pure r
    srcs := srcs.push { permMeta := pm, column }
  let side ← openSide dir v
  return { dir, vocab := v, srcs, side, codec, counters }

/-- Run one query on an open session; `emit` gets the SPARQL JSON in pieces.
    Returns the statistics, the number of constant lookups and their time. -/
def Session.run (ss : Session) (plan : Query.Plan) (emit : ByteArray → IO Unit) (reference : Bool := false) :
    IO (Except String (Query.RunStats × Nat × Nat)) := do
  let lookups ← IO.mkRef (0 : Nat)
  let lookupNs ← IO.mkRef (0 : Nat)
  let lookup (s : String) : ExceptT String IO (Option Nat) := do
    let a ← IO.monoNanosNow
    let r ← match ss.side with
      | some sd => do pure (← sd.lookup s).1
      | none => match ss.vocab.findWord s with
        | .ok r => pure r
        | .error e => throw e
    let b ← IO.monoNanosNow
    lookups.modify (· + 1)
    lookupNs.modify (· + (b - a))
    pure r
  match ← (Query.runPlanM ss.srcs ss.vocab plan lookup emit reference).run with
  | .error e => return .error e
  | .ok st => return .ok (st, ← lookups.get, ← lookupNs.get)

def parsePlan (text : String) : IO (Except String Query.Plan) := do
  match L4Factoidal.SPARQL.parseSparql text with
  | .error e => throw (IO.userError s!"SPARQL parse error: {e}")
  | .ok q => return Query.translate q

def median (xs : Array Nat) : Nat :=
  let s := mergeSortBy xs (· ≤ ·)
  if s.isEmpty then 0 else s[(s.size - 1) / 2]!

/-- `--repeat N` and the remaining arguments. -/
def queryOpts (xs : List String) : Nat × List String := Id.run do
  let mut n := 1
  let mut acc : Array String := #[]
  let mut skip := false
  let arr := xs.toArray
  for i in [0:arr.size] do
    if skip then
      skip := false
      continue
    let x := arr[i]!
    if x == "--repeat" then
      n := (arr.getD (i + 1) "1").toNat?.getD 1
      skip := true
    else if x == "--explain" || x == "--constants" || x == "--libzstd" || x == "--reference-render" then pure ()
    else acc := acc.push x
  return (n, acc.toList)

def runQuery (dir : String) (text : String) (explain : Bool) (constants : Bool := false)
    (codec : Codec := .lean) (repeatN : Nat := 1) (reference : Bool := false) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let plan ← match ← parsePlan text with
    | .ok p => pure p
    | .error e =>
      IO.eprintln s!"l4qlvr: refused: {e}"
      return 3
  if constants then
    for w in plan.words do IO.println w
    return 0
  let ss ← openSession dir codec
  let t1 ← IO.monoNanosNow
  let stdout ← IO.getStdout
  let runs := max repeatN 1
  let mut execs : Array Nat := #[]
  let mut last : Option (Query.RunStats × Nat × Nat) := none
  let mut io : IoCounters := {}
  for k in [0:runs] do
    let final := k + 1 == runs
    ss.counters.set {}
    let a ← IO.monoNanosNow
    let r ← ss.run plan (if final then fun s => stdout.write s else fun _ => pure ()) reference
    let b ← IO.monoNanosNow
    match r with
    | .error e =>
      stdout.flush
      IO.eprintln s!"l4qlvr: query failed: {e}"
      return 1
    | .ok x =>
      last := some x
      execs := execs.push (b - a)
      io ← ss.counters.get
  stdout.write "\n".toUTF8
  stdout.flush
  let t2 ← IO.monoNanosNow
  let some (st, nLookups, lookupNs) := last | return 1
  if explain then
    for l in st.plan do IO.eprintln s!"plan: {l}"
  let ioLine := s!"codec {codec.name}: {io.frames} frames, {io.frameBytes} bytes read, {io.outBytes} bytes decoded; pread {io.preadNs / 1000} us; decode {io.decodeNs / 1000} us"
  if runs > 1 then
    let us := execs.map (· / 1000)
    IO.eprintln s!"repeat: {execs.size} runs in one process; execution us min {us.foldl min (us.getD 0 0)} median {median us} max {us.foldl max 0}; last run {ioLine}"
  IO.eprintln s!"query: {st.rows} rows; {nLookups} constants looked up by {if ss.side.isSome then "side index" else "linear scan (no side index)"} in {lookupNs / 1000000} ms; setup {ms t0 t1} ms; execution {ms t1 t2} ms; total {ms t0 t2} ms; {ioLine}; peak RSS (VmHWM): {← vmHWM}"
  return 0

/-- `l4qlvr serve INDEXDIR`: load once, then answer one query per line of
    standard input (a query on one line, or `--file PATH`). Each answer is
    one line of SPARQL JSON on stdout; one timing line per query on stderr. -/
def runServe (dir : String) (codec : Codec) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let ss ← openSession dir codec
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"serve: session loaded in {ms t0 t1} ms (vocabulary, 6 permutation trailers, side index); codec {codec.name}; peak RSS (VmHWM): {← vmHWM}"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut failures := 0
  for _ in [0:1000000] do
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    let text ← if line.startsWith "--file " then IO.FS.readFile (line.drop 7).trimAscii.toString else pure line
    let a ← IO.monoNanosNow
    match ← parsePlan text with
    | .error e =>
      IO.eprintln s!"l4qlvr: refused: {e}"
      stdout.write "{\"refused\":true}\n".toUTF8
      stdout.flush
      failures := failures + 1
    | .ok plan =>
      ss.counters.set {}
      let b ← IO.monoNanosNow
      let r ← ss.run plan fun s => stdout.write s
      let c ← IO.monoNanosNow
      stdout.write "\n".toUTF8
      stdout.flush
      let io ← ss.counters.get
      match r with
      | .error e =>
        IO.eprintln s!"l4qlvr: query failed: {e}"
        failures := failures + 1
      | .ok (st, n, lns) =>
        IO.eprintln s!"serve: {st.rows} rows; parse {(b - a) / 1000} us; execution {(c - b) / 1000} us; {n} lookups {lns / 1000} us; {io.frames} frames; pread {io.preadNs / 1000} us; decode {io.decodeNs / 1000} us; peak RSS (VmHWM): {← vmHWM}"
  return (if failures == 0 then 0 else 1)

/-! ## zstd: the Lean decoder against libzstd on every column frame -/

/-- Decode every column frame of the eight permutation files with the Lean
    decoder and with libzstd; compare the outputs byte for byte and time
    each decoder. -/
def runZstdDiff (dir : String) : IO UInt32 := do
  let base ← findBase dir
  checkMetaData dir base
  unless ← zstdAvailable do
    IO.eprintln "zstd-diff: libzstd.so.1 could not be loaded"
    return 2
  let mut pass := 0
  let mut fail := 0
  let mut leanNs := 0
  let mut libNs := 0
  let mut outBytes := 0
  let mut inBytes := 0
  for p in perms do
    let path := s!"{dir}/{base}.{p}"
    unless (← System.FilePath.pathExists path) do continue
    let pm ← loadPermMeta path
    for b in pm.blocks do
      for cr in b.cols do
        let frame ← pread path cr.offset cr.size
        let t0 ← IO.monoNanosNow
        let l ← decodeLeanIO frame b.rows
        let t1 ← IO.monoNanosNow
        let z ← zstdDecompressRaw frame (8 * b.rows).toUInt64
        let t2 ← IO.monoNanosNow
        leanNs := leanNs + (t1 - t0)
        libNs := libNs + (t2 - t1)
        inBytes := inBytes + cr.size
        outBytes := outBytes + 8 * b.rows
        match l with
        | .ok lb =>
          if lb.size == 8 * b.rows && lb == z then pass := pass + 1
          else
            fail := fail + 1
            IO.println s!"DIFFERENT {p} block {b.index} frame at {cr.offset}"
        | .error e =>
          fail := fail + 1
          IO.println s!"LEAN ERROR {p} block {b.index} frame at {cr.offset}: {e}"
  let mbps (ns : Nat) : Nat := if ns == 0 then 0 else outBytes * 1000 / ns
  IO.println s!"zstd-diff: {pass} pass, {fail} fail (out of {pass + fail}) column frames; {inBytes} bytes in, {outBytes} bytes out"
  IO.println s!"zstd-diff: Lean {leanNs / 1000000} ms ({mbps leanNs} MB/s of output); libzstd {libNs / 1000000} ms ({mbps libNs} MB/s)"
  IO.eprintln s!"zstd-diff: peak RSS (VmHWM): {← vmHWM}"
  return (if fail == 0 then 0 else 1)


/-! ## The q07 kernel: Lean against C on the same input -/

/-- Decoded columns 0, 1, 2 of every block of `src` that the key prefix
    selects, concatenated. -/
def gatherBlocks (src : PermSrc IO) (key : Array UInt64) : IO (ByteArray × ByteArray × ByteArray × Nat) := do
  let mut c0 := ByteArray.empty
  let mut c1 := ByteArray.empty
  let mut c2 := ByteArray.empty
  let mut n := 0
  for b in src.permMeta.blocks do
    if b.selects key then
      c0 := c0 ++ (← ok "kernel-dump" (← (fetchColumn src b 0).run))
      c1 := c1 ++ (← ok "kernel-dump" (← (fetchColumn src b 1).run))
      c2 := c2 ++ (← ok "kernel-dump" (← (fetchColumn src b 2).run))
      n := n + b.rows
  return (c0, c1, c2, n)

/-- `l4qlvr kernel-dump INDEXDIR OUT`: the input of the q07 kernel. -/
def runKernelDump (dir out : String) : IO UInt32 := do
  let ss ← openSession dir .lean
  let some sd := ss.side | throw (IO.userError "kernel-dump: needs the side index (l4qlvr side-index)")
  let look (w : String) : IO UInt64 := do
    match (← sd.lookup w).1 with
    | some i => pure (Id.ofVocabIndex i).bits
    | none => throw (IO.userError s!"kernel-dump: {w} is not in the vocabulary")
  let medal ← look "<http://wallscope.co.uk/ontology/olympics/medal>"
  let gold ← look "<http://wallscope.co.uk/resource/olympics/medal/Gold>"
  let athlete ← look "<http://wallscope.co.uk/ontology/olympics/athlete>"
  -- permInfos: 0 = pso, 1 = pos
  let (a0, a1, a2, nA) ← gatherBlocks ss.srcs[1]! #[medal, gold]
  let (b0, b1, b2, nB) ← gatherBlocks ss.srcs[0]! #[athlete]
  let x : QlvrKernel.Input := { kA0 := medal, kA1 := gold, kB0 := athlete, nA, nB, a0, a1, a2, b0, b1, b2 }
  IO.FS.writeBinFile out x.encode
  IO.eprintln s!"kernel-dump: A (POS, wso:medal Gold) {nA} rows; B (PSO, wso:athlete) {nB} rows; {out}"
  return 0

/-- `l4qlvr kernel FILE [ITERS]`: `QlvrKernel.runKernel`. -/
def runKernel (file : String) (iters : Nat) : IO UInt32 :=
  do QlvrKernel.runKernel (← IO.FS.readBinFile file) iters

end QlvrTool

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["stats", dir] => QlvrTool.runStats dir
    | ["scan", dir, iri] => QlvrTool.runScan dir iri
    | ["dump", dir] => QlvrTool.runDump dir
    | ["words", dir] => QlvrTool.runWords dir
    | ["side-index", dir] => QlvrTool.runSideIndex dir
    | "side-check" :: dir :: words => QlvrTool.runSideCheck dir words
    | "query" :: dir :: rest =>
      let explain := rest.contains "--explain"
      let constants := rest.contains "--constants"
      let codec := if rest.contains "--libzstd" then QlvrTool.Codec.libzstd else .lean
      let reference := rest.contains "--reference-render"
      let (repeatN, rest) := QlvrTool.queryOpts rest
      match rest with
      | ["--file", f] => do QlvrTool.runQuery dir (← IO.FS.readFile f) explain constants codec repeatN reference
      | [text] => QlvrTool.runQuery dir text explain constants codec repeatN reference
      | _ =>
        IO.eprintln "usage: l4qlvr query INDEXDIR 'SPARQL' | --file Q.rq [--explain] [--repeat N] [--libzstd]"
        pure 2
    | ["serve", dir] => QlvrTool.runServe dir .lean
    | ["serve", dir, "--libzstd"] => QlvrTool.runServe dir .libzstd
    | ["zstd-diff", dir] => QlvrTool.runZstdDiff dir
    | ["kernel-dump", dir, out] => QlvrTool.runKernelDump dir out
    | ["kernel", file] => QlvrTool.runKernel file 50
    | ["kernel", file, n] => QlvrTool.runKernel file (n.toNat?.getD 50)
    | _ =>
      IO.eprintln "usage: l4qlvr stats|dump|words|side-index|zstd-diff INDEXDIR | scan INDEXDIR PRED-IRI | side-check INDEXDIR [STORED..] | query INDEXDIR ('SPARQL' | --file Q.rq) [--explain] [--repeat N] [--libzstd] | serve INDEXDIR [--libzstd]"
      pure 2
  catch e =>
    IO.eprintln s!"l4qlvr: {e}"
    pure 1
