/-
Harness/Sbm11DictPack — `l4sbm11-dict-pack`: phases 1 and 2 of the SBM11
packer (https://github.com/danbri/factoidal/issues/788; design record
`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.8).

This is a HARNESS: it does file I/O, measures time and peak RSS (VmHWM),
and prints. The formats and the decoders are
`L4Factoidal.Storage.Sbm11.{TermKey, TermId, Dict}`.

  l4sbm11-dict-pack SOURCE OUTDIR [--run-terms N] [--workers K] [--format F] [--base IRI]
      Phase 1: SOURCE is a document in any of the six RDF syntaxes (the format
      from `--format F`, else the file extension, as for `l4sbm11-pack`; there is
      no default syntax). It is read through the source layer
      (`L4Factoidal/RDF/Source.lean`, `Sbm11Pack.streamRange`) in 64 KiB chunks
      as RDF 1.2: a triple term is a class-7 key
      (https://github.com/danbri/factoidal/issues/792 item 1). For N-Triples and
      N-Quads, SOURCE is cut into K byte ranges at line starts (default 4), each
      read in its own task; lines are independent in those two syntaxes, and a
      blank node keeps its label, so the cut changes no term. Any other syntax is
      one range (`Sbm11Pack.planRanges`). Each task collects the
      distinct non-inline terms (language tags folded to lower case) in a
      hash set; when it holds N / K terms (N default 262,144) it sorts their
      keys in byte order and writes a run file `OUTDIR/run-W-J.tmp`. The reader's
      accumulator only conses the terms of one chunk onto a list; the hash
      set lives outside the fold, so no insert finds it shared (a shared
      set is copied whole on its first insert of every chunk: measured
      2026-10-12, phase 1 took 96 s on olympics that way).
      Phase 2: k-way merge of the runs (positioned reads of 16 MiB / k per
      run, at least 64 KiB),
      drop duplicates, write `OUTDIR/dict.gdv1` page by page and
      `OUTDIR/dict.gdx1`; remove the runs.
      Memory is bounded by N terms plus 16 MiB of run buffers (64 KiB per
      run once there are more than 256 runs).

  l4sbm11-dict-pack --check SOURCE OUTDIR [--exact] [--format F] [--base IRI]
      Read the dictionary into memory and check (1) every key in rank order:
      strictly increasing, `decodeKey?` gives a term whose key is the same
      bytes, lookup of the key gives its rank, the key of the rank is the
      key; (2) every term of SOURCE: an inline id decodes to the same term,
      any other term has a rank whose key decodes to the same term. With
      `--exact`, also compare both files byte for byte with
      `Dict.encodeDict?` of the key list (small dictionaries only: the
      spec encoder works over lists).

  l4sbm11-dict-pack --lookup-bench OUTDIR [N] [ABSENT]
      String to id by positioned reads (`pread`) of GDX1 and GDV1: N keys
      sampled evenly by rank (default 1,000) and ABSENT keys that are not
      in the dictionary (default 100). Prints per-lookup time and probes.

  l4sbm11-dict-pack --nest-check N
      A triple term nested N deep in the object position, with an
      upper-case language tag in the innermost literal, through
      `normalizeTerm`, `termKeyBytes?` (class 7), `decodeKey?` and
      `termKeyBytes?` again: the second key must be the bytes of the first,
      the decoded term N deep, its innermost tag in lower case
      (https://github.com/danbri/factoidal/issues/792 item 1). The
      `tests/stack/run.sh` case `sbm11-triple-term` runs it at N = 300,000
      under the default stack and under `LEAN_STACK_SIZE_KB=512`.

Exit 1 on any error or failed check. Timings and VmHWM go to stderr.
-/
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.Dict
import Harness.Sbm11PackLib
import L4Factoidal.Qlvr.Sort
import L4Factoidal.Qlvr.CmpBytesFast
import Harness.PosixRangeIO
import Harness.RunHeap
import Std.Data.HashMap

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Dict
open L4Factoidal.Qlvr (cmpBytes mergeSortBy)

namespace Sbm11DictPack

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

def put32 (b : ByteArray) (x : Nat) : ByteArray :=
  let x := x.toUInt32
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

def get32 (d : ByteArray) (p : Nat) : Nat := word32At d p

/-! ## Phase 1: terms of the source -/

/-- The fold accumulator: the non-inline terms of the current chunk
    (normalised, newest first, duplicates kept) and counts. -/
structure P1 where
  pending : List Term := []
  inlineOcc : Nat := 0
  quads : Nat := 0

def addTerm (acc : P1) (t : Term) : P1 :=
  let t := normalizeTerm t
  if (inlineCode? t).isSome then { acc with inlineOcc := acc.inlineOcc + 1 }
  else { acc with pending := t :: acc.pending }

def consume (acc : P1) (tr : Triple) (g : Option Subject) : P1 :=
  let acc := addTerm (addTerm (addTerm acc tr.s.toTerm) (.iri tr.p)) tr.o
  let acc := match g with
    | some s => addTerm acc s.toTerm
    | none => acc
  { acc with quads := acc.quads + 1 }

/-- Sorted run bytes: `u32 length, key` per record. -/
def encodeRun (ks : Array ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (ks.size * 64)
  for k in ks do
    out := put32 out k.size ++ k
  return out

/-- Keys of a set of terms, sorted; `.error` names a term with no key. -/
def runKeys (terms : Std.HashMap Term Unit) : Except String (Array ByteArray) := do
  let mut ks : Array ByteArray := Array.mkEmpty terms.size
  for (t, _) in terms do
    match termKeyBytes? t with
    | some k => ks := ks.push k
    | none => throw s!"term not admitted by the SBM11 dictionary: {repr t}"
  return mergeSortBy ks (fun a b => cmpBytes a b != .gt)

/-- What one phase-1 worker leaves: its run files and its counts. -/
structure WorkerOut where
  runs : Array String := #[]
  quads : Nat := 0
  inlineOcc : Nat := 0

/-- Phase 1 over one byte range: collect terms in a hash set, spill a
    sorted run whenever it holds `runTerms` terms. The source is read by the
    source layer (`Sbm11Pack.streamRange`) in the syntax `cfg` names. -/
def phase1Worker (cfg : Sbm11Pack.ReadCfg) (source outDir : String) (w start stop runTerms : Nat) :
    IO WorkerOut := do
  let runsRef ← IO.mkRef (#[] : Array String)
  let setRef ← IO.mkRef (({} : Std.HashMap Term Unit))
  let spill (acc : P1) (force : Bool) : IO P1 := do
    -- move the chunk's terms into the set; `swap` leaves the ref empty, so
    -- the set is uniquely referenced while it is updated
    let mut set ← setRef.swap {}
    for t in acc.pending do
      set := set.insert t ()
    let acc := { acc with pending := [] }
    if set.size == 0 || (!force && set.size < runTerms) then
      setRef.set set
      return acc
    let ks ← ok "phase 1" (runKeys set)
    let rs ← runsRef.get
    let path := s!"{outDir}/run-{w}-{rs.size}.tmp"
    IO.FS.writeBinFile path (encodeRun ks)
    runsRef.set (rs.push path)
    return acc
  let final ← Sbm11Pack.streamRange cfg source start stop consume ({} : P1) fun acc => spill acc false
  let final ← spill final true
  return { runs := ← runsRef.get, quads := final.quads, inlineOcc := final.inlineOcc }

/-! ## Phase 2: merge and write -/

structure RunReader where
  path : String
  size : Nat
  base : Nat
  buf : ByteArray
  pos : Nat
  /-- Bytes per positioned read: 16 MiB shared by all runs, at least 64 KiB,
      so the merge's buffers do not grow with the number of runs. -/
  chunk : Nat := 1 <<< 20
  deriving Inhabited

def RunReader.ensure (r : RunReader) (need : Nat) : IO RunReader := do
  if r.pos + need ≤ r.buf.size then return r
  let base := r.base + r.pos
  let len := min (r.size - base) (max need r.chunk)
  if len < need then throw (IO.userError s!"{r.path}: truncated record at {base}")
  return { r with base, buf := ← pread r.path base len, pos := 0 }

def RunReader.next (r : RunReader) : IO (Option ByteArray × RunReader) := do
  if r.base + r.pos ≥ r.size then return (none, r)
  let r ← r.ensure 4
  let len := get32 r.buf r.pos
  let r ← r.ensure (4 + len)
  let w := r.buf.extract (r.pos + 4) (r.pos + 4 + len)
  return (some w, { r with pos := r.pos + 4 + len })

/-- The page writer: GDV1 directly, the GDX1 entries to a temporary file
    that is copied behind the GDX1 header at the end. -/
structure Writer where
  gdv : IO.FS.Handle
  ent : IO.FS.Handle
  page : Array (List UInt8) := #[]
  gdvOff : Nat := gdvHeader.length
  pages : Nat := 0
  terms : Nat := 0
  bufGdv : ByteArray := ByteArray.emptyWithCapacity (1 <<< 20)
  bufEnt : ByteArray := ByteArray.emptyWithCapacity (1 <<< 16)

def Writer.flushBufs (w : Writer) (force : Bool) : IO Writer := do
  let mut w := w
  if force || w.bufGdv.size ≥ (1 <<< 20) then
    w.gdv.write w.bufGdv
    w := { w with bufGdv := ByteArray.emptyWithCapacity (1 <<< 20) }
  if force || w.bufEnt.size ≥ (1 <<< 16) then
    w.ent.write w.bufEnt
    w := { w with bufEnt := ByteArray.emptyWithCapacity (1 <<< 16) }
  return w

/-- Encode the open page with `Dict.encodePage` (the encoder of the round
    trip theorem) and its directory entry with `Dict.entryBytes`. -/
def Writer.closePage (w : Writer) : IO Writer := do
  if w.page.isEmpty then return w
  let bytes := encodePage w.page.toList
  let e : DirEntry := ⟨w.gdvOff, bytes.length⟩
  let w := { w with
    bufGdv := w.bufGdv ++ listBytes bytes
    bufEnt := w.bufEnt ++ listBytes (entryBytes e)
    gdvOff := w.gdvOff + bytes.length
    pages := w.pages + 1
    page := #[] }
  w.flushBufs false

def Writer.add (w : Writer) (k : ByteArray) : IO Writer := do
  let w := { w with page := w.page.push k.data.toList, terms := w.terms + 1 }
  if w.page.size ≥ pageTerms then w.closePage else return w

def copyInto (dst : IO.FS.Handle) (src : String) : IO Unit := do
  IO.FS.withFile src .read fun h => do
    repeat
      let b ← h.read 1048576
      if b.isEmpty then break
      dst.write b

def runPack (source outDir : String) (runTerms workers : Nat) (opts : Sbm11Pack.SourceOpts := {}) :
    IO UInt32 := do
  let t0 ← IO.monoNanosNow
  IO.FS.createDirAll outDir
  -- phase 1: one task for each byte range (`workers` ranges cut at line starts
  -- for N-Triples and N-Quads, else one); each keeps a set of at most
  -- runTerms / ranges terms
  let size ← fileSize source
  let cfg ← Sbm11Pack.readCfg source size opts
  let ranges ← Sbm11Pack.planRanges cfg.fmt source size workers
  let perWorker := max 1 (runTerms / ranges.size)
  let mut tasks := #[]
  for i in [0:ranges.size] do
    let (lo, hi) := ranges[i]!
    let t ← IO.asTask (phase1Worker cfg source outDir i lo hi perWorker) .dedicated
    tasks := tasks.push t
  let mut runs : Array String := #[]
  let mut final : P1 := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok o =>
      runs := runs ++ o.runs
      final := { final with quads := final.quads + o.quads, inlineOcc := final.inlineOcc + o.inlineOcc }
    | .error e => throw e
  let t1 ← IO.monoNanosNow
  -- phase 2
  let mut readers : Array RunReader := #[]
  let mut heads : Array (Option ByteArray) := #[]
  let mut runBytes := 0
  for path in runs do
    let sz ← fileSize path
    runBytes := runBytes + sz
    let chunk := max 65536 ((16 <<< 20) / max 1 runs.size)
    let (hd, r) ← RunReader.next { path, size := sz, base := 0, buf := .empty, pos := 0, chunk }
    readers := readers.push r
    heads := heads.push hd
  let gdvPath := s!"{outDir}/dict.gdv1"
  let gdxPath := s!"{outDir}/dict.gdx1"
  let entTmp := s!"{outDir}/gdx-entries.tmp"
  let hV ← IO.FS.Handle.mk gdvPath .write
  let hE ← IO.FS.Handle.mk entTmp .write
  hV.write (listBytes gdvHeader)
  let mut w : Writer := { gdv := hV, ent := hE }
  let mut prev : Option ByteArray := none
  let mut records := 0
  -- the next record comes from a loser tree over the runs (issue 804)
  let mut tree := Harness.RunHeap.build cmpBytes heads
  for _ in [0:runBytes + 1] do
    let k := Harness.RunHeap.winner tree
    match heads[k]?.bind id with
    | none => break
    | some x =>
      records := records + 1
      let c := match prev with
        | some p => cmpBytes p x
        | none => .lt
      if c != .eq then
        if c != .lt then
          throw (IO.userError s!"phase 2: keys out of order after {w.terms} terms")
        w ← w.add x
        prev := some x
      let (hd, r) ← readers[k]!.next
      readers := readers.set! k r
      heads := heads.set! k hd
      tree := Harness.RunHeap.replay cmpBytes heads tree k
  w ← w.closePage
  w ← w.flushBufs true
  hV.flush; hE.flush
  let hdr := gdxMagic ++ L4Factoidal.Storage.writeU64LE (UInt64.ofNat w.terms) ++
    L4Factoidal.Storage.writeU64LE (UInt64.ofNat w.pages)
  IO.FS.withFile gdxPath .write fun hX => do
    hX.write (listBytes hdr)
    copyInto hX entTmp
    hX.flush
  IO.FS.removeFile entTmp
  for path in runs do IO.FS.removeFile path
  let t2 ← IO.monoNanosNow
  let gdvSize ← fileSize gdvPath
  let gdxSize ← fileSize gdxPath
  IO.println s!"sbm11-dict: source={source} workers={ranges.size} quads={final.quads} terms={w.terms} pages={w.pages} inline-occurrences={final.inlineOcc} runs={runs.size} run-records={records} run-bytes={runBytes} gdv1-bytes={gdvSize} gdx1-bytes={gdxSize} dictionary-bytes={gdvSize + gdxSize}"
  IO.println s!"sbm11-dict: phase1-ms={ms t0 t1} phase2-ms={ms t1 t2} total-ms={ms t0 t2} peak-rss={← vmHWM}"
  pure 0

/-! ## Check -/

structure MemDict where
  gdv : ByteArray
  gdx : ByteArray
  hdr : GdxHeader

def MemDict.load (dir : String) : IO MemDict := do
  let gdv ← IO.FS.readBinFile s!"{dir}/dict.gdv1"
  let gdx ← IO.FS.readBinFile s!"{dir}/dict.gdx1"
  if bytesToList (gdv.extract 0 6) != gdvHeader then throw (IO.userError "GDV1: bad header")
  let hdr ← ok "GDX1" (parseGdxHeader gdx)
  pure { gdv, gdx, hdr }

def MemDict.fetchV (d : MemDict) (o n : Nat) : ByteArray := d.gdv.extract o (o + n)
def MemDict.fetchX (d : MemDict) (o n : Nat) : ByteArray := d.gdx.extract o (o + n)

def MemDict.lookup (d : MemDict) (k : ByteArray) : Except String (Option Nat) :=
  ((lookupM (m := Id) d.fetchX d.fetchV d.hdr k).run).map (·.1)

def MemDict.keyOf (d : MemDict) (r : Nat) : Except String ByteArray :=
  (keyOfRankM (m := Id) d.fetchX d.fetchV d.hdr r).run

def MemDict.page (d : MemDict) (i : Nat) : Except String (Array ByteArray) :=
  (pageM (m := Id) d.fetchX d.fetchV i).run

def runCheck (source dir : String) (exact : Bool) (opts : Sbm11Pack.SourceOpts := {}) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let d ← MemDict.load dir
  let mut fails := 0
  let mut rank := 0
  let mut prev : Option Key := none
  let mut allKeys : Array Key := #[]
  for p in [0:d.hdr.pageCount] do
    let ks ← ok s!"page {p}" (d.page p)
    if p + 1 < d.hdr.pageCount && ks.size != pageTerms then
      throw (IO.userError s!"page {p} holds {ks.size} keys")
    for kb in ks do
      let k := bytesToList kb
      if exact then allKeys := allKeys.push k
      if let some pk := prev then
        if cmpKey pk k != .lt then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: not strictly after the previous key"
      match decodeKey? k with
      | none =>
        fails := fails + 1
        if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: key does not decode"
      | some t =>
        if termKey? t != some k then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: key of the decoded term differs"
        if (inlineCode? t).isSome then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: an inline term is in the dictionary"
      match d.lookup kb with
      | .ok (some r) =>
        if r != rank then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: lookup gives {r}"
      | _ =>
        fails := fails + 1
        if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: lookup does not find the key"
      match d.keyOf rank with
      | .ok k' =>
        if k' != kb then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: key of rank differs"
      | .error e =>
        fails := fails + 1
        if fails ≤ 5 then IO.eprintln s!"FAIL rank {rank}: {e}"
      prev := some k
      rank := rank + 1
  if rank != d.hdr.termCount then
    fails := fails + 1
    IO.eprintln s!"FAIL: {rank} keys in the pages, GDX1 says {d.hdr.termCount}"
  let t1 ← IO.monoNanosNow
  IO.println s!"sbm11-check: dictionary keys={rank} pages={d.hdr.pageCount} ms={ms t0 t1}"
  -- every term of the source
  let seenRef ← IO.mkRef (({} : Std.HashMap Term Unit))
  let statsRef ← IO.mkRef ((0, 0, 0) : Nat × Nat × Nat) -- distinct dict, distinct inline, fails
  let check (t0 : Term) : IO Unit := do
    let t := normalizeTerm t0
    -- take the set out of the ref so that the insert updates it in place
    let seen ← seenRef.swap {}
    if seen.contains t then
      seenRef.set seen
      return
    seenRef.set (seen.insert t ())
    let (nd, ni, nf) ← statsRef.get
    match inlineCode? t with
    | some n =>
      let good := ofInlineCode? n == some t && n / two60 ≥ tagInt
      statsRef.set (nd, ni + 1, if good then nf else nf + 1)
      if !good && nf < 5 then IO.eprintln s!"FAIL inline term {repr t}"
    | none =>
      let good := match termKey? t with
        | none => false
        | some k =>
          match d.lookup (listBytes k) with
          | .ok (some r) =>
            match d.keyOf r with
            | .ok k' => decodeKey? (bytesToList k') == some t
            | .error _ => false
          | _ => false
      statsRef.set (nd + 1, ni, if good then nf else nf + 1)
      if !good && nf < 5 then IO.eprintln s!"FAIL dictionary term {repr t}"
  let checkAcc (acc : P1) : IO P1 := do
    for t in acc.pending do check t
    pure { acc with pending := [] }
  -- this fold keeps every term of a chunk, inline ones included
  let consumeAll (acc : P1) (tr : Triple) (g : Option Subject) : P1 :=
    let add := fun (a : P1) (t : Term) => { a with pending := t :: a.pending }
    let acc := add (add (add acc tr.s.toTerm) (.iri tr.p)) tr.o
    match g with
    | some s => add acc s.toTerm
    | none => acc
  let size ← fileSize source
  let cfg ← Sbm11Pack.readCfg source size opts
  let _ ← Sbm11Pack.streamRange cfg source 0 size consumeAll ({} : P1) checkAcc
  let (nd, ni, nf) ← statsRef.get
  fails := fails + nf
  if nd != rank then
    fails := fails + 1
    IO.eprintln s!"FAIL: the source has {nd} distinct dictionary terms, the dictionary {rank}"
  let t2 ← IO.monoNanosNow
  IO.println s!"sbm11-check: source distinct-dictionary-terms={nd} distinct-inline-terms={ni} ms={ms t1 t2}"
  if exact then
    match encodeDict? allKeys.toList with
    | none =>
      fails := fails + 1
      IO.eprintln "FAIL: encodeDict? refuses the key list"
    | some (v, x) =>
      let sameV := listBytes v == d.gdv
      let sameX := listBytes x == d.gdx
      let dec := decodeDict (bytesToList d.gdv) (bytesToList d.gdx) == some allKeys.toList
      IO.println s!"sbm11-check: exact gdv1-equal={sameV} gdx1-equal={sameX} decodeDict-equal={dec}"
      if !(sameV && sameX && dec) then fails := fails + 1
  IO.println s!"sbm11-check: failures={fails} peak-rss={← vmHWM}"
  pure (if fails == 0 then 0 else 1)

/-! ## Lookup by positioned reads -/

def runLookupBench (dir : String) (n absent : Nat) : IO UInt32 := do
  let gdvPath := s!"{dir}/dict.gdv1"
  let gdxPath := s!"{dir}/dict.gdx1"
  let hdr ← ok "GDX1" (parseGdxHeader (← pread gdxPath 0 gdxHeaderBytes))
  if hdr.termCount == 0 then throw (IO.userError "empty dictionary")
  -- sample keys by rank, through the same positioned reads
  let mut samples : Array (Nat × ByteArray) := #[]
  for i in [0:n] do
    let r := i * hdr.termCount / n
    let k ← ok s!"rank {r}" (← (keyOfRankM (pread gdxPath) (pread gdvPath) hdr r).run)
    samples := samples.push (r, k)
  let mut fails := 0
  let mut times : Array Nat := #[]
  let mut probes := 0
  for (r, k) in samples do
    let t0 ← IO.monoNanosNow
    let (res, pr) ← ok "lookup" (← (lookupM (pread gdxPath) (pread gdvPath) hdr k).run)
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    probes := probes + pr
    if res != some r then fails := fails + 1
  let mut absTimes : Array Nat := #[]
  for i in [0:absent] do
    let (_, k) := samples[i % samples.size]!
    let k := k ++ ⟨#[0xFF, 0xFE, i.toUInt8]⟩
    let t0 ← IO.monoNanosNow
    let (res, _) ← ok "lookup" (← (lookupM (pread gdxPath) (pread gdvPath) hdr k).run)
    let t1 ← IO.monoNanosNow
    absTimes := absTimes.push (t1 - t0)
    if res.isSome then fails := fails + 1
  let sorted := mergeSortBy times (· ≤ ·)
  let sortedA := mergeSortBy absTimes (· ≤ ·)
  let us (x : Nat) : String := s!"{x / 1000}.{toString (1000 + x % 1000) |>.drop 1}"
  let mean := times.foldl (· + ·) 0 / max 1 times.size
  let meanA := absTimes.foldl (· + ·) 0 / max 1 absTimes.size
  IO.println s!"sbm11-lookup: terms={hdr.termCount} pages={hdr.pageCount} present={times.size} mean-us={us mean} median-us={us sorted[sorted.size / 2]!} max-us={us sorted[sorted.size - 1]!} mean-probes={probes / max 1 times.size}"
  IO.println s!"sbm11-lookup: absent={absTimes.size} mean-us={us meanA} median-us={us (sortedA[sortedA.size / 2]?.getD 0)} max-us={us (sortedA[sortedA.size - 1]?.getD 0)} failures={fails} peak-rss={← vmHWM}"
  pure (if fails == 0 then 0 else 1)

/-! ## Nested triple terms through the key codec -/

/-- `t` inside `n` triple terms `<<( s p ... )>>` (the object position is the
    one RDF 1.2 nests), by a loop. -/
def nestGo (s : Subject) (p : WfIri) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => nestGo s p n (.tripleTerm s p t)

/-- The nesting depth of a term and its innermost object, by a loop. -/
def innermostGo : Nat → Term → Nat × Term
  | d, .tripleTerm _ _ o => innermostGo (d + 1) o
  | d, t => (d, t)

def runNestCheck (n : Nat) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let s : Subject := .iri ⟨"a:s", rfl⟩
  let p : WfIri := ⟨"a:p", rfl⟩
  let t := nestGo s p n (.literal (Literal.langString "deep" "EN-GB"))
  let tn := normalizeTerm t
  let t1 ← IO.monoNanosNow
  let some k := termKeyBytes? tn
    | IO.eprintln "FAIL: the normalised term has no key"; return 1
  let t2 ← IO.monoNanosNow
  let some back := decodeKey? k.data.toList
    | IO.eprintln "FAIL: the key does not decode"; return 1
  let t3 ← IO.monoNanosNow
  let some k2 := termKeyBytes? back
    | IO.eprintln "FAIL: the decoded term has no key"; return 1
  let (depth, leaf) := innermostGo 0 back
  let leafOk := leaf == .literal (Literal.langString "deep" "en-gb")
  let mut fails := 0
  if k2 != k then
    fails := fails + 1; IO.eprintln "FAIL: the key of the decoded term differs"
  if depth != n then
    fails := fails + 1; IO.eprintln s!"FAIL: decoded depth {depth}, built {n}"
  if !leafOk then
    fails := fails + 1; IO.eprintln "FAIL: the innermost literal is not \"deep\"@en-gb"
  if (termKeyBytes? t).isSome then
    fails := fails + 1; IO.eprintln "FAIL: the term with an upper-case tag has a key before normalisation"
  let t4 ← IO.monoNanosNow
  IO.println s!"sbm11-nest-check: depth={n} key-bytes={k.size} normalise-ms={ms t0 t1} encode-ms={ms t1 t2} decode-ms={ms t2 t3} check-ms={ms t3 t4} failures={fails} peak-rss={← vmHWM}"
  pure (if fails == 0 then 0 else 1)

def usage : String :=
  "usage: l4sbm11-dict-pack SOURCE OUTDIR [--run-terms N] [--workers K] [--format F] [--base IRI]\n" ++
  "       l4sbm11-dict-pack --check SOURCE OUTDIR [--exact] [--format F] [--base IRI]\n" ++
  "       l4sbm11-dict-pack --lookup-bench OUTDIR [N] [ABSENT]\n" ++
  "       l4sbm11-dict-pack --nest-check N\n" ++
  "  F is ntriples, nquads, turtle, trig, rdfxml or jsonld; without --format the file extension decides\n" ++
  "  (.nt .nq .ttl .trig .rdf .jsonld). There is no default syntax."

/-- The options of a pack or a check. -/
structure Opts where
  runTerms : Nat := 262144
  workers : Nat := 4
  exact : Bool := false
  source : Sbm11Pack.SourceOpts := {}

def parseOpts : List String → Opts → Option Opts
  | [], o => some o
  | "--run-terms" :: v :: rest, o => v.toNat?.bind fun n => parseOpts rest { o with runTerms := max 1 n }
  | "--workers" :: v :: rest, o => v.toNat?.bind fun n => parseOpts rest { o with workers := max 1 n }
  | "--exact" :: rest, o => parseOpts rest { o with exact := true }
  | "--format" :: v :: rest, o => parseOpts rest { o with source := { o.source with format := some v } }
  | "--base" :: v :: rest, o => parseOpts rest { o with source := { o.source with base := some v } }
  | _, _ => none

end Sbm11DictPack

open Sbm11DictPack in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "--check" :: src :: dir :: rest =>
        match parseOpts rest {} with
        | some o => runCheck src dir o.exact o.source
        | none => IO.eprintln usage; pure 2
    | ["--lookup-bench", dir] => runLookupBench dir 1000 100
    | ["--lookup-bench", dir, n] => runLookupBench dir n.toNat! 100
    | ["--lookup-bench", dir, n, a] => runLookupBench dir n.toNat! a.toNat!
    | ["--nest-check", n] => runNestCheck n.toNat!
    | src :: dir :: rest =>
        match parseOpts rest {} with
        | some o => runPack src dir o.runTerms o.workers o.source
        | none => IO.eprintln usage; pure 2
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11-dict-pack: {e}"
    pure 1
