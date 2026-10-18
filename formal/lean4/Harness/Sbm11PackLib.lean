/-
Harness/Sbm11PackLib — the code of `l4sbm11-pack` (packer phases 1 to 3 of SBM11),
shared with compaction (`Harness/Sbm11Compact.lean`, stage 5)
(https://github.com/danbri/factoidal/issues/789; design record
`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.8).

  l4sbm11-pack SOURCE OUTDIR [--format F] [--base IRI] [--workers K]
               [--run-terms N] [--block-rows B] [--sort-rows M] [--phase2-only]
               [--via-dataset]

## The entry: a producer of RDF quads

The packer takes RDF quads from producers (`QuadSource`,
`L4Factoidal/RDF/QuadSource.lean`) and does not know where they come from (owner,
2026-10-15, https://github.com/danbri/factoidal/issues/866: "isn't packing (into
shardborough?) done against abstract rdf graph or dataset API not a text file
format???"). The entry is `packQuads`. It takes one way to open a producer for each
phase-1 worker, runs phase 1 on them, and runs phases 2 and 3 (`packBatches`) on the
batches. The producers in the tree:

  * `fileRangeSource`: bytes `[start, stop)` of a file, read through the source layer
    (`L4Factoidal/RDF/Source.lean`) in the syntax the command line names. The syntax is
    named in the code that makes the producers (`chooseFormat`, `readCfg`, `planRanges`,
    `fileRangeSource`, `openDatasetSource`) and nowhere in `packQuads` or in the phases it
    runs. `runPack` makes one producer for each byte range.
  * `QuadSource.ofDataset`, `QuadSource.ofArray`: an RDF `Dataset` or an array of quads
    in memory. `--via-dataset` reads the whole document into a `Dataset` (the batch
    meaning of the source layer, `Source.parseDocument`) and packs that `Dataset`.
  * `GraphStore.quadSource` (`L4Factoidal/HDT/QuadSource.lean`): the triples of an HDT
    file, read with the HDT reader. SOURCE ending in `.hdt`, or `--format hdt`.

The pack records the length and the SHA-256 of the source in the manifest. A file or an
HDT file gives its own. A pack with no document (`packQuads` with `noDocument`) records
length 0 and the SHA-256 of the empty byte string.

## The file producer

SOURCE is a document in any of the six RDF syntaxes (N-Triples, N-Quads,
Turtle, TriG, RDF/XML, JSON-LD). The format is `--format F` (a label of
`RDF.formatOfLabel`), else the file extension (`RDF.formatOfExtension`). A
source whose format neither gives is refused, with a message that asks for
`--format`. The pack takes RDF quads from the source layer
(`L4Factoidal/RDF/Source.lean`) and does not know the syntax they came from
(owner, 2026-10-14, https://github.com/danbri/factoidal/issues/837); the
generation of the same dataset written in two syntaxes is byte-identical
except for the source length and digest in the manifest
(`tests/sbm11/syntax_independence.sh`). The source is read as RDF 1.2.

Phase 1. For N-Triples and N-Quads, SOURCE is cut into K byte ranges at line
  starts (default 4; a line start is a statement boundary), and each range is
  read by its own task. For every other syntax one task reads the whole
  source: Turtle and TriG after one read for the generated blank-node prefix
  (`Source.Prepass`), RDF/XML and JSON-LD by parsing the joined chunks at the
  end (https://github.com/danbri/factoidal/issues/838,
  https://github.com/danbri/factoidal/issues/839). A task reads 64 KiB chunks
  through the source layer. A task gives each distinct non-inline term of its
  batch a batch-local number (a hash map of at most N / K terms, N default
  262,144) and keeps the batch's quads as four slots each: 0 for the default
  graph, `1 + local number`, or an inline id (`TermId.inlineCode?`). When the
  map is full (or the batch holds 1,048,576 quads) it sorts the batch's keys
  and writes a term run (`run-W-J.tmp`, the stage 2 run format) and a quad
  run (`quads-W-J.tmp`, 32 bytes per quad, the local numbers replaced by the
  rank of the key in the term run). A separate task computes the SHA-256 of
  SOURCE.
Phase 2. The k-way merge of the term runs writes GDV1 and GDX1 exactly as
  `l4sbm11-dict-pack` does, and per term run a remap file (`remap-W-J.tmp`):
  the global id of the run's keys, in run order.
Phase 3. Each quad run is rewritten to global ids through its remap (at most
  N / K ids in memory) and each quad goes to four row buffers, one per
  permutation (PSO, POS, SPO, OSP). A full buffer (M rows, default 524,288)
  is sorted and written as a row run (`perm-P-J.tmp`). Then four tasks, one
  per permutation, merge the row runs, drop duplicate rows and write the
  blocks (PRB1) and their metadata (PRM1). A block ends at B rows (default
  4,096), or at a change of `c0` when it already holds B / 16 rows.
Then every file is hashed (SHA-256 and 65,536-byte Merkle leaves, written to
  `<file>.merkle`) and `manifest.sbm11` is written.

Memory is bounded by the K phase-1 maps and quad buffers, the merge buffers
and the four row buffers; for N-Triples, N-Quads, Turtle and TriG it does not
grow with the source. For RDF/XML and JSON-LD the reader holds the document
(see Phase 1). Every frame the packer writes is decoded again and compared
with its column.

Prints phase times and VmHWM. Exit 1 on any error.
-/
import Harness.Sbm11Gen
import Harness.RunHeap
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.RDF.QuadSource
import L4Factoidal.HDT.QuadSource
import L4Factoidal.Storage.Sbm11.GraphList
import L4Factoidal.Qlvr.Sort
import L4Factoidal.Qlvr.CmpBytesFast
import Std.Data.HashMap

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Dict (pageTerms gdvHeader gdxMagic encodePage entryBytes DirEntry)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.Manifest
open L4Factoidal.Qlvr (cmpBytes mergeSortBy)
open Harness.Sbm11Gen

namespace Sbm11Pack

def put32 (b : ByteArray) (x : Nat) : ByteArray :=
  let x := x.toUInt32
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

def pushW (b : ByteArray) (x : UInt64) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
    |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8 |>.push (x >>> 48).toUInt8 |>.push (x >>> 56).toUInt8

def wordAt (b : ByteArray) (i : Nat) : UInt64 :=
  (b.get! i).toUInt64 ||| ((b.get! (i + 1)).toUInt64 <<< 8) ||| ((b.get! (i + 2)).toUInt64 <<< 16) |||
    ((b.get! (i + 3)).toUInt64 <<< 24) ||| ((b.get! (i + 4)).toUInt64 <<< 32) |||
    ((b.get! (i + 5)).toUInt64 <<< 40) ||| ((b.get! (i + 6)).toUInt64 <<< 48) |||
    ((b.get! (i + 7)).toUInt64 <<< 56)

def get32 (d : ByteArray) (p : Nat) : Nat := Dict.word32At d p

/-! ## Phase 1 -/

structure P1 where
  pending : List (Triple × Option Subject) := []

def consume (acc : P1) (tr : Triple) (g : Option Subject) : P1 :=
  { acc with pending := (tr, g) :: acc.pending }

/-- How phase 1 reads the source: the syntax, the RDF version, the base IRI
    that relative IRIs resolve against, and the prefix of the generated
    blank-node labels (Turtle and TriG; `Source.Prepass`). -/
structure ReadCfg where
  fmt : RdfFormat
  version : Source.RdfVersion := .rdf12
  base : Option String := none
  bnodePrefix : String := ""

/-- What the command line gives about the source: `--format F` and
    `--base IRI`. -/
structure SourceOpts where
  format : Option String := none
  base : Option String := none
  /-- `--via-dataset`: read the whole document into a `Dataset` and pack that
      `Dataset` (the batch meaning of the source layer), not the chunks of the
      reader. The memory is that of the document and of its `Dataset`. -/
  viaDataset : Bool := false

/-- The syntax of a source: `--format F` when given, else the extension of
    its name. There is no default: a source that neither names gets an error
    that asks for `--format`. -/
def chooseFormat (source : String) (flag : Option String) : Except String RdfFormat :=
  match flag with
  | some label =>
      match formatOfLabel label with
      | some fmt => .ok fmt
      | none => .error s!"unknown format '{label}'; give --format with one of ntriples, nquads, turtle, trig, rdfxml, jsonld"
  | none =>
      match formatOfPath source with
      | some fmt => .ok fmt
      | none =>
          .error s!"cannot tell the RDF syntax of {source} from its name; give --format with one of ntriples, nquads, turtle, trig, rdfxml, jsonld"

/-- What SOURCE is: a document in one of the RDF syntaxes, or an HDT file (a store
    that its own reader opens; there is no text in between). `--format hdt` or the
    extension `.hdt` makes it an HDT file. -/
inductive SourceKind where
  | document (fmt : RdfFormat)
  | hdt

def chooseKind (source : String) (flag : Option String) : Except String SourceKind :=
  match flag with
  | some "hdt" => .ok .hdt
  | some _ => (chooseFormat source flag).map .document
  | none => if source.endsWith ".hdt" then .ok .hdt else (chooseFormat source flag).map .document

/-- How a read failure is told to the user. `start` is the byte where the
    range began, so a parse position names a place in the document. -/
def failureText (source : String) (start pos : Nat) : Source.Failure → String
  | .utf8 m => s!"{source}: UTF-8 error near byte {pos}: {m}"
  | .parse e => s!"{source}: parse error at {start + e.pos}: {e.msg}"

/-- The generated blank-node prefix of the whole source, by one sequential
    read (Turtle and TriG; `Source.Prepass`, `Source.prepass_chunks`). Other
    syntaxes need none. -/
def bnodePrefixOf (source : String) (fmt : RdfFormat) (size : Nat) : IO String := do
  if !Source.needsPrepass fmt then return ""
  let mut scan : Source.Prepass := {}
  let mut pos := 0
  for _ in [0:size / 1048576 + 2] do
    if pos ≥ size then break
    let len := min 1048576 (size - pos)
    match scan.feed (← pread source pos len) with
    | .error m => throw (IO.userError s!"{source}: UTF-8 error near byte {pos}: {m}")
    | .ok next => scan := next
    pos := pos + len
  match scan.finish with
  | .error m => throw (IO.userError s!"{source}: UTF-8 error: {m}")
  | .ok pfx => pure pfx

/-- The read configuration of a source: its syntax, and the pre-pass for
    syntaxes that need one. -/
def readCfg (source : String) (size : Nat) (opts : SourceOpts) : IO ReadCfg := do
  let fmt ← match chooseFormat source opts.format with
    | .ok f => pure f
    | .error m => throw (IO.userError m)
  pure { fmt, base := opts.base, bnodePrefix := ← bnodePrefixOf source fmt size }

/-- The reader of one byte range of a source, in the syntax `cfg` names, with the
    accumulator `init`. -/
def openRangeReader {α : Type} (cfg : ReadCfg) (source : String) (init : α) :
    IO (Source.ByteReader α) :=
  match Source.ByteReader.init Source.withJsonLd cfg.fmt cfg.version cfg.base cfg.bnodePrefix init with
  | .ok r => pure r
  | .error m => throw (IO.userError s!"{source}: {m}")

/-- Read the next 64 KiB of bytes `[start, stop)` of the source, from `pos`, and
    give them to the reader. Returns the reader and the position after the chunk.
    `decl` gets the named graphs the chunk declares (a TriG graph block). -/
def feedChunk {α : Type} (source : String) (start stop : Nat) (step : Source.Step α)
    (rd : Source.ByteReader α) (pos : Nat) (decl : Source.Decl α := Source.noDecl) :
    IO (Source.ByteReader α × Nat) := do
  let len := min 65536 (stop - pos)
  let bytes ← pread source pos len
  let pos := pos + len
  match rd.feedD step decl bytes with
  | .error f => throw (IO.userError (failureText source start pos f))
  | .ok next => pure (next, pos)

/-- The end of the range: the unfinished statement is read, and the accumulator is
    returned. A whole reader (RDF/XML, JSON-LD) declares the named graphs of its
    dataset here. -/
def finishRange {α : Type} (source : String) (start pos : Nat) (step : Source.Step α)
    (rd : Source.ByteReader α) (decl : Source.Decl α := Source.noDecl) : IO α :=
  match rd.endBytes with
  | .error f => throw (IO.userError (failureText source start pos f))
  | .ok reader =>
    match reader.finishD step decl with
    | .error e => throw (IO.userError (failureText source start pos (.parse e)))
    | .ok acc => pure acc

/-- Stream bytes `[start, stop)` of the source through the source layer in
    64 KiB positioned reads. The consumer is `step` from the accumulator `init`;
    `onFeed` sees the accumulator after every chunk and gives back the
    accumulator to continue with. `canon` and the dictionary packer
    (`Sbm11DictPack`) each pass their own. The packer's phase 1 takes quads from
    `fileRangeSource` instead. -/
def streamRange {α : Type} (cfg : ReadCfg) (source : String) (start stop : Nat)
    (step : Source.Step α) (init : α) (onFeed : α → IO α) : IO α := do
  let mut rd ← openRangeReader cfg source init
  let mut pos := start
  for _ in [0:(stop - start) / 65536 + 2] do
    if pos ≥ stop then break
    let (next, pos') ← feedChunk source start stop step rd pos
    pos := pos'
    let acc ← onFeed next.acc
    rd := next.setAcc acc
  let acc ← finishRange source start pos step rd
  onFeed acc

/-- The quad consumer of `fileRangeSource`: the reader's accumulator is the batch. -/
def pushQuad : Source.Step QuadSource.Batch := fun batch t g => batch.pushQuad (t, g)

/-- The declaration consumer of `fileRangeSource`: a named graph that the document
    declares goes into the batch, empty or not (a TriG graph block, a named graph of
    a JSON-LD document). -/
def pushGraph : Source.Decl QuadSource.Batch := fun batch g => batch.pushGraph g

/-- Where a `fileRangeSource` is: the reader, with the quads of the chunks read
    since the last batch in its accumulator, and the position of the next chunk. -/
structure RangePos where
  reader : Source.ByteReader QuadSource.Batch
  pos : Nat

/-- The quads of bytes `[start, stop)` of a file, read through the source layer in
    64 KiB chunks in the syntax `cfg` names: this is the file producer of the packer.
    Each call of `next` reads chunks
    until they complete a statement, and gives the quads of the statements the chunks
    completed, and the named graphs they declared. The end of the range gives the
    quads of the last statement. A parse error is an exception of `next`
    (`failureText`: the position is in the file). -/
def fileRangeSource (cfg : ReadCfg) (source : String) (start stop : Nat) : IO QuadSource := do
  let reader ← openRangeReader cfg source ({} : QuadSource.Batch)
  QuadSource.ofStep (some (⟨reader, start⟩ : RangePos)) fun st => do
    match st with
    | none => pure none
    | some ⟨reader, pos⟩ => do
      let mut rd := reader
      let mut pos := pos
      for _ in [0:(stop - start) / 65536 + 2] do
        if pos ≥ stop then break
        let (next, pos') ← feedChunk source start stop pushQuad rd pos pushGraph
        pos := pos'
        -- take the quads out of the reader and leave an empty batch in it
        let (next, batch) := next.withAcc fun acc => ({}, acc)
        rd := next
        if !batch.isEmpty then return some (batch, some ⟨rd, pos⟩)
      let last ← finishRange source start pos pushQuad rd pushGraph
      pure (if last.isEmpty then none else some (last, none))

def lineStartFrom (source : String) (size b : Nat) : IO Nat := do
  if b == 0 then return 0
  let mut p := b - 1
  for _ in [0:size + 1] do
    if p ≥ size then return size
    let len := min 65536 (size - p)
    let w ← pread source p len
    for i in [0:w.size] do
      if w.get! i == 10 then return p + i + 1
    p := p + len
  return size

/-- The byte ranges phase 1 reads. N-Triples and N-Quads are cut at line
    starts into `workers` ranges, a line start being a statement boundary
    (`Source.splitsAtLines`). Every other syntax is one range, the whole
    source: a statement of Turtle, TriG, RDF/XML or JSON-LD has no boundary
    that is found without reading from the start. -/
def planRanges (fmt : RdfFormat) (source : String) (size workers : Nat) : IO (Array (Nat × Nat)) := do
  if !Source.splitsAtLines fmt then return #[(0, size)]
  let mut bounds : Array Nat := #[]
  for i in [0:workers + 1] do
    bounds := bounds.push (← lineStartFrom source size (size * i / workers))
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:workers] do
    out := out.push (bounds[i]!, bounds[i + 1]!)
  pure out

structure Batch where
  termRun : String
  quadRun : String
  terms : Nat
  quads : Nat
  /-- the run of the named graphs the batch's producers declared (8 bytes each, the
      run-local number of the name), and their number; `""` and 0 when they declared
      none -/
  graphRun : String := ""
  graphs : Nat := 0
  deriving Inhabited

structure WorkerOut where
  batches : Array Batch := #[]
  quads : Nat := 0
  inlineOcc : Nat := 0

def maxBatchQuads : Nat := 1048576

def localLimit : Nat := two60

/-- Phase 1 of one worker as an object that takes batches: `consume` gives a batch
    to the worker, `finish` spills what is left and returns what the worker made.
    `phase1Worker` pulls the batches of a producer into it. A caller that scans a
    store with a callback pushes the batches itself. -/
structure Phase1Sink where
  consume : QuadSource.Batch → IO Unit
  finish : IO WorkerOut

/-- Open the phase-1 worker `w`: give each distinct non-inline term a batch-local
    number, and spill a term run and a quad run whenever the map is full. The worker
    knows RDF terms, triples and graph names only. A declared named graph (a batch's
    `graphs`) is a term of the dictionary, also when no quad has it, and its
    number goes to the graph run of the batch, which phase 3a adds to the graph
    list. -/
def openPhase1 (outDir : String) (w runTerms : Nat) : IO Phase1Sink := do
  let idsRef ← IO.mkRef (({} : Std.HashMap Term Nat))
  let quadsRef ← IO.mkRef ((Array.mkEmpty 65536 : Array Nat))
  let graphsRef ← IO.mkRef (#[] : Array Nat)
  let outRef ← IO.mkRef ({} : WorkerOut)
  let slotOf (t0 : Term) : IO Nat := do
    let t := normalizeTerm t0
    match inlineCode? t with
    | some c =>
      outRef.modify fun o => { o with inlineOcc := o.inlineOcc + 1 }
      pure c
    | none =>
      let ids ← idsRef.swap {}
      match ids.get? t with
      | some n =>
        idsRef.set ids
        pure (n + 1)
      | none =>
        let n := ids.size
        idsRef.set (ids.insert t n)
        pure (n + 1)
  let spill : IO Unit := do
    let ids ← idsRef.swap {}
    let quads ← quadsRef.swap #[]
    let declared ← graphsRef.swap #[]
    if quads.isEmpty && ids.isEmpty && declared.isEmpty then return
    let mut pairs : Array (ByteArray × Nat) := Array.mkEmpty ids.size
    for (t, n) in ids do
      match termKeyBytes? t with
      | some k => pairs := pairs.push (k, n)
      | none => throw (IO.userError s!"term not admitted by the SBM11 dictionary: {repr t}")
    let sorted := mergeSortBy pairs (fun a b => cmpBytes a.1 b.1 != .gt)
    let mut rankOf : Array Nat := Array.replicate sorted.size 0
    let mut run := ByteArray.emptyWithCapacity (sorted.size * 64)
    for i in [0:sorted.size] do
      let (k, n) := sorted[i]!
      rankOf := rankOf.set! n i
      run := put32 run k.size ++ k
    let o ← outRef.get
    let j := o.batches.size
    let termRun := s!"{outDir}/run-{w}-{j}.tmp"
    let quadRun := s!"{outDir}/quads-{w}-{j}.tmp"
    IO.FS.writeBinFile termRun run
    let mut qb := ByteArray.emptyWithCapacity (quads.size * 8)
    for v in quads do
      let v' := if v ≥ 1 && v < localLimit then rankOf[v - 1]! + 1 else v
      qb := pushW qb v'.toUInt64
    IO.FS.writeBinFile quadRun qb
    -- the declared named graphs: run-local numbers, as in the quad run
    let graphRun := if declared.isEmpty then "" else s!"{outDir}/graphs-{w}-{j}.tmp"
    if !declared.isEmpty then
      let mut gb := ByteArray.emptyWithCapacity (declared.size * 8)
      for v in declared do
        let v' := if v ≥ 1 && v < localLimit then rankOf[v - 1]! + 1 else v
        gb := pushW gb v'.toUInt64
      IO.FS.writeBinFile graphRun gb
    outRef.set { o with batches := o.batches.push { termRun, quadRun, terms := sorted.size, quads := quads.size / 4,
                                                     graphRun, graphs := declared.size },
                        quads := o.quads + quads.size / 4 }
  let full : IO Bool := do
    let nIds := (← idsRef.get).size
    let nQ := (← quadsRef.get).size / 4
    pure (nIds ≥ runTerms || nQ ≥ maxBatchQuads)
  /- A batch of a streaming syntax holds a few hundred quads. The whole
     document syntaxes (RDF/XML, JSON-LD) and a `Dataset` give all their quads
     in a few batches, so the batch limits are also tested inside the loop. -/
  let onBatch (batch : QuadSource.Batch) : IO Unit := do
    for gn in batch.graphs do
      let gs ← slotOf gn.toTerm
      graphsRef.modify (·.push gs)
    let mut k := 0
    for (tr, g) in batch.quads do
      let s ← slotOf tr.s.toTerm
      let p ← slotOf (.iri tr.p)
      let o ← slotOf tr.o
      let gs ← match g with
        | some gn => slotOf gn.toTerm
        | none => pure 0
      quadsRef.modify fun q => q.push s |>.push p |>.push o |>.push gs
      k := k + 1
      if k % 4096 == 0 then
        if (← full) then spill
    if (← full) then spill
  pure { consume := onBatch, finish := do spill; outRef.get }

/-- Phase 1 of one worker: take the batches of a producer. -/
def phase1Worker (src : QuadSource) (outDir : String) (w runTerms : Nat) : IO WorkerOut := do
  let sink ← openPhase1 outDir w runTerms
  src.foldBatches () fun _ batch => sink.consume batch
  sink.finish

/-- What phase 1 of all the workers leaves: the batches (term runs and quad
    runs, in the order of the workers), the quads read, and the occurrences of
    inline terms. -/
structure Phase1Out where
  batches : Array Batch := #[]
  quads : Nat := 0
  inlineOcc : Nat := 0

/-- Phase 1: one task for each way of opening a producer. The task opens its
    producer itself, so that the producer and its state belong to the thread that
    uses them (a state shared between threads is not updated in place). Each task
    keeps a map of at most `runTerms / sources.size` terms. -/
def phase1 (sources : Array (IO QuadSource)) (outDir : String) (runTerms : Nat) : IO Phase1Out := do
  let perWorker := max 1 (runTerms / sources.size)
  let mut tasks := #[]
  for i in [0:sources.size] do
    let openSource := sources[i]!
    let t ← IO.asTask (do phase1Worker (← openSource) outDir i perWorker) .dedicated
    tasks := tasks.push t
  let mut out : Phase1Out := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok o =>
      out := { batches := out.batches ++ o.batches, quads := out.quads + o.quads,
               inlineOcc := out.inlineOcc + o.inlineOcc }
    | .error e => throw e
  pure out

/-- The SHA-256 of the source, by the HACL* block fold in 1 MiB reads. -/
def sourceSha (source : String) (size : Nat) : IO ByteArray := do
  let mut st := L4Factoidal.Crypto.Sha256Stream.init
  let mut off := 0
  for _ in [0:size / 1048576 + 2] do
    if off ≥ size then break
    let len := min 1048576 (size - off)
    st := st.updateWith Harness.nativeBlockFold256 (← pread source off len)
    off := off + len
  pure (st.finishWith Harness.nativeBlockFold256)

/-! ## Phase 2: merge, dictionary and remap files -/

structure RunReader where
  path : String
  size : Nat
  base : Nat
  buf : ByteArray
  pos : Nat
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

/-- The next 32-byte row of a row run. -/
def RunReader.nextRow (r : RunReader) : IO (Option QRow × RunReader) := do
  if r.base + r.pos ≥ r.size then return (none, r)
  let r ← r.ensure 32
  let b := r.buf
  let i := r.pos
  return (some ⟨wordAt b i, wordAt b (i + 8), wordAt b (i + 16), wordAt b (i + 24)⟩, { r with pos := i + 32 })

/-- The next 8-byte word of a word run (the graph id runs of phase 3a). -/
def RunReader.nextWord (r : RunReader) : IO (Option UInt64 × RunReader) := do
  if r.base + r.pos ≥ r.size then return (none, r)
  let r ← r.ensure 8
  return (some (wordAt r.buf r.pos), { r with pos := r.pos + 8 })

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

def tagOfKey (k : ByteArray) : Nat := classTagOfByte (k.get! 0)


/-- Merge the term runs into GDV1/GDX1; per run, the remap file. The next
    record comes from a loser tree over the runs (`Harness/RunHeap.lean`):
    about log2 k comparisons per record for k runs (issue 804; the linear scan
    of every head it replaces made phase 2 quadratic in the terms). Returns the
    term count, the page count and the number of run records. -/
def phase2 (outDir : String) (batches : Array Batch) : IO (Nat × Nat × Nat) := do
  let mut readers : Array RunReader := #[]
  let mut heads : Array (Option ByteArray) := #[]
  let mut runBytes := 0
  for b in batches do
    let sz ← fileSize b.termRun
    runBytes := runBytes + sz
    let chunk := max 65536 ((16 <<< 20) / max 1 batches.size)
    let (hd, r) ← RunReader.next { path := b.termRun, size := sz, base := 0, buf := .empty, pos := 0, chunk }
    readers := readers.push r
    heads := heads.push hd
  let mut remaps : Array ByteArray := batches.map fun b => ByteArray.emptyWithCapacity (8 * b.terms)
  let gdvPath := s!"{outDir}/dict.gdv1"
  let gdxPath := s!"{outDir}/dict.gdx1"
  let entTmp := s!"{outDir}/gdx-entries.tmp"
  let hV ← IO.FS.Handle.mk gdvPath .write
  let hE ← IO.FS.Handle.mk entTmp .write
  hV.write (listBytes gdvHeader)
  let mut w : Writer := { gdv := hV, ent := hE }
  let mut prev : Option ByteArray := none
  let mut prevId : UInt64 := 0
  let mut records := 0
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
      let dup := c == .eq
      if !dup then
        if c != .lt then
          throw (IO.userError s!"phase 2: keys out of order after {w.terms} terms")
        let rank := w.terms
        w ← w.add x
        prev := some x
        prevId := (tagOfKey x * two60 + rank).toUInt64
      remaps := remaps.modify k (fun rb => pushW rb prevId)
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
  for i in [0:batches.size] do
    let b := batches[i]!
    if remaps[i]!.size != 8 * b.terms then
      throw (IO.userError s!"phase 2: remap of {b.termRun} has {remaps[i]!.size / 8} ids, run has {b.terms}")
    IO.FS.writeBinFile (b.termRun ++ ".remap") remaps[i]!
    IO.FS.removeFile b.termRun
  pure (w.terms, w.pages, records)

/-! ## Phase 3: permutation runs -/

/-- The three-way comparison of `QRow.lt`, for the merge tree of phase 3b. -/
@[inline] def QRow.cmp (x y : QRow) : Ordering :=
  if x.lt y then .lt else if y.lt x then .gt else .eq

def sortRows (rows : Array QRow) : Array QRow := mergeSortBy rows QRow.le

def writeRowRun (path : String) (rows : Array QRow) : IO Unit := do
  let mut b := ByteArray.emptyWithCapacity (32 * rows.size)
  for r in rows do
    b := pushW (pushW (pushW (pushW b r.a) r.b) r.c) r.d
  IO.FS.writeBinFile path b

/-- Sort the four buffers in parallel and write each as a row run. -/
def spillPerms (outDir : String) (bufs : Array (Array QRow)) (runs : Array (Array String)) :
    IO (Array (Array String)) := do
  let mut tasks := #[]
  for p in [0:4] do
    let path := s!"{outDir}/perm-{p}-{runs[p]!.size}.tmp"
    let rows := bufs[p]!
    let t ← IO.asTask (do writeRowRun path (sortRows rows); pure path) .dedicated
    tasks := tasks.push t
  let mut runs := runs
  for p in [0:4] do
    match ← IO.wait tasks[p]! with
    | .ok path => runs := runs.set! p (runs[p]!.push path)
    | .error e => throw e
  pure runs

/-- Sort the graph ids of a buffer, drop the repeats, and write them as a word run
    (8 bytes each). -/
def spillGraphIds (outDir : String) (ids : Array UInt64) (runs : Array String) : IO (Array String) := do
  if ids.isEmpty then return runs
  let sorted := mergeSortBy ids (· ≤ ·)
  let mut b := ByteArray.emptyWithCapacity (8 * sorted.size)
  let mut last : Option UInt64 := none
  for x in sorted do
    if last != some x then
      b := pushW b x
      last := some x
  let path := s!"{outDir}/graphids-{runs.size}.tmp"
  IO.FS.writeBinFile path b
  pure (runs.push path)

/-- What phase 3a leaves: the row runs of each permutation, and the runs of the
    named graph ids (each sorted, without repeats). -/
structure Phase3a where
  runs : Array (Array String)
  graphRuns : Array String

def phase3a (outDir : String) (batches : Array Batch) (sortRowsMax : Nat) : IO Phase3a := do
  let mut bufs : Array (Array QRow) := #[#[], #[], #[], #[]]
  let mut runs : Array (Array String) := #[#[], #[], #[], #[]]
  -- the graph ids of the quads (not 0, the default graph); a run of quads of one graph
  -- adds its id once
  let mut gids : Array UInt64 := #[]
  let mut lastG : UInt64 := 0
  let mut graphRuns : Array String := #[]
  for b in batches do
    let remapBytes ← IO.FS.readBinFile (b.termRun ++ ".remap")
    let mut remap : Array UInt64 := Array.mkEmpty b.terms
    for i in [0:b.terms] do
      remap := remap.push (wordAt remapBytes (8 * i))
    let qsize ← fileSize b.quadRun
    let mut off := 0
    for _ in [0:qsize / 1048576 + 2] do
      if off ≥ qsize then break
      let len := min 1048576 (qsize - off)
      let chunk ← pread b.quadRun off len
      off := off + len
      let mut i := 0
      for _ in [0:len / 32] do
        let mapv (v : UInt64) : IO UInt64 := do
          if v ≥ 1 && v.toNat < localLimit then
            match remap[v.toNat - 1]? with
            | some x => pure x
            | none => throw (IO.userError s!"{b.quadRun}: local number {v} not in the remap")
          else pure v
        let s ← mapv (wordAt chunk i)
        let p ← mapv (wordAt chunk (i + 8))
        let o ← mapv (wordAt chunk (i + 16))
        let g ← mapv (wordAt chunk (i + 24))
        bufs := bufs.modify 0 (·.push (toPerm 0 s p o g))
        bufs := bufs.modify 1 (·.push (toPerm 1 s p o g))
        bufs := bufs.modify 2 (·.push (toPerm 2 s p o g))
        bufs := bufs.modify 3 (·.push (toPerm 3 s p o g))
        if g != 0 && g != lastG then
          gids := gids.push g
          lastG := g
        i := i + 32
      if bufs[0]!.size ≥ sortRowsMax then
        runs ← spillPerms outDir bufs runs
        bufs := #[#[], #[], #[], #[]]
      if gids.size ≥ sortRowsMax then
        graphRuns ← spillGraphIds outDir gids graphRuns
        gids := #[]
        lastG := 0
    -- the named graphs the batch's producers declared, empty or not
    if b.graphs > 0 then
      let gb ← IO.FS.readBinFile b.graphRun
      for k in [0:b.graphs] do
        let v := wordAt gb (8 * k)
        let g ← if v ≥ 1 && v.toNat < localLimit then
            match remap[v.toNat - 1]? with
            | some x => pure x
            | none => throw (IO.userError s!"{b.graphRun}: local number {v} not in the remap")
          else pure v
        if g != 0 && g != lastG then
          gids := gids.push g
          lastG := g
      IO.FS.removeFile b.graphRun
      if gids.size ≥ sortRowsMax then
        graphRuns ← spillGraphIds outDir gids graphRuns
        gids := #[]
        lastG := 0
    IO.FS.removeFile b.quadRun
    IO.FS.removeFile (b.termRun ++ ".remap")
  if !bufs[0]!.isEmpty then
    runs ← spillPerms outDir bufs runs
  graphRuns ← spillGraphIds outDir gids graphRuns
  pure { runs, graphRuns }

/-! ## The graph list (GNL1) -/

/-- Merge the graph id runs (each sorted, without repeats) into the list of the
    named graphs, and write `graphs.gnl1` when the list is not empty
    (`Storage/Sbm11/GraphList.lean`): the magic, the count and the ids. The merge
    holds one buffer for each run, so the memory does not grow with the number of
    graphs. The file is read back and decoded by `GraphList.decodeAt` (the decoder
    the readers run, `GraphListTheorems.decodeAt_eq`), which checks the order and the
    tags, and its count is compared. Returns the number of named graphs (0: no file). -/
def writeGraphList (outDir : String) (graphRuns : Array String) : IO Nat := do
  let mut readers : Array RunReader := #[]
  let mut heads : Array (Option UInt64) := #[]
  let mut total := 0
  for path in graphRuns do
    let sz ← fileSize path
    total := total + sz / 8
    let (hd, r) ← RunReader.nextWord { path, size := sz, base := 0, buf := .empty, pos := 0,
                                        chunk := max 65536 ((8 <<< 20) / max 1 graphRuns.size) }
    readers := readers.push r
    heads := heads.push hd
  let wordsPath := s!"{outDir}/graphids-merged.tmp"
  let h ← IO.FS.Handle.mk wordsPath .write
  let mut buf := ByteArray.emptyWithCapacity (1 <<< 20)
  let mut count := 0
  let mut prev : Option UInt64 := none
  let cmp : UInt64 → UInt64 → Ordering := fun a b => compare a b
  let mut tree := Harness.RunHeap.build cmp heads
  for _ in [0:total + 1] do
    let k := Harness.RunHeap.winner tree
    match heads[k]?.bind id with
    | none => break
    | some x =>
      if prev != some x then
        buf := pushW buf x
        count := count + 1
        prev := some x
        if buf.size ≥ (1 <<< 20) then
          h.write buf
          buf := ByteArray.emptyWithCapacity (1 <<< 20)
      let (hd, r) ← readers[k]!.nextWord
      readers := readers.set! k r
      heads := heads.set! k hd
      tree := Harness.RunHeap.replay cmp heads tree k
  h.write buf
  h.flush
  for path in graphRuns do IO.FS.removeFile path
  if count == 0 then
    IO.FS.removeFile wordsPath
    return 0
  let listPath := s!"{outDir}/{GraphList.fileName}"
  IO.FS.withFile listPath .write fun hl => do
    hl.write (listBytes (GraphList.magic ++ put64 count))
    copyInto hl wordsPath
    hl.flush
  IO.FS.removeFile wordsPath
  match GraphList.decodeAt (← IO.FS.readBinFile listPath) with
  | some ids =>
    if ids.size != count then
      throw (IO.userError s!"{listPath}: {ids.size} graph ids decoded, {count} written")
  | none =>
    throw (IO.userError s!"{listPath}: the graph list does not decode (an id that is not of a blank node or an IRI, or ids out of order)")
  pure count

/-! ## Phase 3b: blocks -/

structure PermOut where
  blocks : Nat
  rows : Nat
  dups : Nat
  prbBytes : Nat
  prmBytes : Nat
  digest : Digest2
  codecs : Array Nat
  frameBytes : Array Nat
  deriving Inhabited

structure BlockWriter where
  perm : Nat
  h : IO.FS.Handle
  buf : ByteArray := ByteArray.emptyWithCapacity (1 <<< 20)
  offset : Nat := prbHeaderBytes
  metas : Array BlockMeta := #[]
  cur : Array QRow := #[]
  digest : Digest2 := {}
  codecs : Array Nat := #[0, 0, 0, 0]
  frameBytes : Array Nat := #[0, 0, 0, 0]

def encodeChecked (col : Array Nat) (what : String) : IO ByteArray := do
  let f := encodeColumnFast col
  match decodeColumnAt f col.size 0 with
  | some (c, j) =>
    if j == f.size && c == col then pure f
    else throw (IO.userError s!"{what}: the frame does not decode to its column")
  | none => throw (IO.userError s!"{what}: the frame does not decode")

def BlockWriter.close (w : BlockWriter) : IO BlockWriter := do
  if w.cur.isEmpty then return w
  let n := w.cur.size
  let mut c0 : Array Nat := Array.mkEmpty n
  let mut c1 : Array Nat := Array.mkEmpty n
  let mut c2 : Array Nat := Array.mkEmpty n
  let mut g : Array Nat := Array.mkEmpty n
  let mut d := w.digest
  for r in w.cur do
    let (a, b, c, e) := (r.a.toNat, r.b.toNat, r.c.toNat, r.d.toNat)
    c0 := c0.push a; c1 := c1.push b; c2 := c2.push c; g := g.push e
    let (s, p, o, gg) := ofPerm w.perm a b c e
    d := d.add (quadDigest s p o gg)
  let what := s!"{permNamesArr[w.perm]!} block at {w.offset}"
  let f0 ← encodeChecked c0 what
  let f1 ← encodeChecked c1 what
  let f2 ← encodeChecked c2 what
  let f3 ← encodeChecked g what
  let m : BlockMeta := { first := w.cur[0]!.toRow, last := w.cur[n - 1]!.toRow, rows := n, offset := w.offset,
                         len0 := f0.size, len1 := f1.size, len2 := f2.size, len3 := f3.size }
  let mut codecs := w.codecs
  let mut fb := w.frameBytes
  for (k, f) in [(0, f0), (1, f1), (2, f2), (3, f3)] do
    let t := (f.get! 0).toNat
    codecs := codecs.modify (min t 3) (· + 1)
    fb := fb.modify k (· + f.size)
  let buf := w.buf ++ f0 ++ f1 ++ f2 ++ f3
  let w := { w with buf, offset := w.offset + m.size, metas := w.metas.push m, cur := #[], digest := d,
                    codecs, frameBytes := fb }
  if w.buf.size ≥ (1 <<< 20) then
    w.h.write w.buf
    return { w with buf := ByteArray.emptyWithCapacity (1 <<< 20) }
  return w

def phase3b (outDir : String) (perm : Nat) (runs : Array String) (blockRows : Nat) : IO PermOut := do
  let name := permNamesArr[perm]!
  let prbPath := s!"{outDir}/{name}.prb1"
  let prmPath := s!"{outDir}/{name}.prm1"
  let h ← IO.FS.Handle.mk prbPath .write
  h.write (listBytes (prbHeader perm))
  let mut w : BlockWriter := { perm, h }
  let mut readers : Array RunReader := #[]
  let mut heads : Array (Option QRow) := #[]
  let mut total := 0
  for path in runs do
    let sz ← fileSize path
    total := total + sz / 32
    let (hd, r) ← RunReader.nextRow { path, size := sz, base := 0, buf := .empty, pos := 0,
                                       chunk := max 65536 ((8 <<< 20) / max 1 runs.size) }
    readers := readers.push r
    heads := heads.push hd
  let mut prev : Option QRow := none
  let mut dups := 0
  let mut rows := 0
  let cutAt := max 1 (blockRows / 16)
  let mut tree := Harness.RunHeap.build QRow.cmp heads
  for _ in [0:total + 1] do
    let k := Harness.RunHeap.winner tree
    match heads[k]?.bind id with
    | none => break
    | some x =>
      let dup := match prev with
        | some p => p == x
        | none => false
      if dup then dups := dups + 1
      else
        if let some p := prev then
          if !p.lt x then throw (IO.userError s!"{name}: rows out of order")
        if w.cur.size ≥ blockRows || (w.cur.size ≥ cutAt && (w.cur[w.cur.size - 1]!).a != x.a) then
          w ← w.close
        w := { w with cur := w.cur.push x }
        rows := rows + 1
        prev := some x
      let (hd, r) ← readers[k]!.nextRow
      readers := readers.set! k r
      heads := heads.set! k hd
      tree := Harness.RunHeap.replay QRow.cmp heads tree k
  w ← w.close
  w.h.write w.buf
  w.h.flush
  for path in runs do IO.FS.removeFile path
  match encodePrm? perm w.metas.toList with
  | none => throw (IO.userError s!"{name}: PRM1 encoder refuses the block list")
  | some bytes => IO.FS.writeBinFile prmPath (listBytes bytes)
  pure { blocks := w.metas.size, rows, dups, prbBytes := ← fileSize prbPath, prmBytes := ← fileSize prmPath,
         digest := w.digest, codecs := w.codecs, frameBytes := w.frameBytes }

/-! ## The pack -/

/-- What phases 2 and 3 report. -/
structure PackReport where
  terms : Nat
  pages : Nat
  records : Nat
  outs : Array PermOut
  /-- the named graphs that GNL1 lists (0: the generation has no named graph and
      no GNL1 file) -/
  graphs : Nat
  genBytes : Nat
  manifestBytes : Nat
  merkleBytes : Nat
  phase2Ns : Nat
  phase3aNs : Nat
  phase3bNs : Nat
  hashNs : Nat

/-- Phases 2 and 3 over phase-1 batches (term runs and quad runs in the
    formats `phase1Worker` writes), then every file hashed and the manifest
    written. The packer (`runPack`) and compaction (`Sbm11Compact`) both end
    here, so a compacted generation is built by the same code as a packed
    one. -/
def packBatches (outDir : String) (batches : Array Batch) (blockRows sortRowsMax : Nat)
    (sourceBytes : Nat) (sourceSha : IO ByteArray) : IO PackReport := do
  let t1 ← IO.monoNanosNow
  let (terms, pages, records) ← phase2 outDir batches
  let t2 ← IO.monoNanosNow
  let p3 ← phase3a outDir batches sortRowsMax
  let runs := p3.runs
  let t3 ← IO.monoNanosNow
  let mut ptasks := #[]
  for p in [0:4] do
    ptasks := ptasks.push (← IO.asTask (phase3b outDir p runs[p]! blockRows) .dedicated)
  let graphCount ← writeGraphList outDir p3.graphRuns
  let mut outs : Array PermOut := #[]
  for t in ptasks do
    match ← IO.wait t with
    | .ok o => outs := outs.push o
    | .error e => throw e
  let t4 ← IO.monoNanosNow
  -- the four permutations must hold the same quads
  for p in [1:4] do
    if outs[p]!.rows != outs[0]!.rows || !(outs[p]!.digest == outs[0]!.digest) then
      throw (IO.userError s!"{permNamesArr[p]!}: {outs[p]!.rows} rows or digest differ from pso ({outs[0]!.rows})")
  -- hash every file and write the manifest
  let mut artifacts : Array Artifact := #[]
  -- a generation that has a named graph lists them (GNL1); one that has none has no list
  for role in (if graphCount > 0 then rolesWithGraphs else roles) do
    let file := fileOfRole role
    let path := s!"{outDir}/{file}"
    let (sha, leaves, ref) ← hashFile path
    writeLeaves path leaves
    artifacts := artifacts.push { role, file, bytes := ref.totalBytes, sha256 := sha, merkle := ref }
  let srcSha ← sourceSha
  let m : Manifest := { layout := sbm11Layout, sourceBytes, sourceSha256 := srcSha, quads := outs[0]!.rows,
                        terms, artifacts := artifacts.toList }
  match encodeManifest? m with
  | none => throw (IO.userError "the SBM11 manifest encoder refuses the manifest")
  | some bytes => IO.FS.writeBinFile s!"{outDir}/{manifestName}" (listBytes bytes)
  let t5 ← IO.monoNanosNow
  let mut genBytes := 0
  for a in artifacts do genBytes := genBytes + a.bytes
  let manifestBytes ← fileSize s!"{outDir}/{manifestName}"
  let mut merkleBytes := 0
  for a in artifacts do merkleBytes := merkleBytes + (← fileSize s!"{outDir}/{a.file}.merkle")
  pure { terms, pages, records, outs, graphs := graphCount, genBytes, manifestBytes, merkleBytes,
         phase2Ns := t2 - t1, phase3aNs := t3 - t2, phase3bNs := t4 - t3, hashNs := t5 - t4 }

/-- Where the quads of a pack came from, as the manifest records it: a length in
    bytes and a SHA-256. `sha256` runs when the pack needs it (after phase 3), so
    that a caller can start it as a task that runs during phase 1. -/
structure SourceId where
  bytes : Nat
  sha256 : IO ByteArray

/-- A pack with no document: length 0 and the SHA-256 of the empty byte string. -/
def SourceId.noDocument : SourceId := ⟨0, pure (Harness.nativeSha256 ByteArray.empty)⟩

/-- What `packQuads` reports: phase 1, the end time of phase 1, and phases 2 and
    3. -/
structure PackQuadsOut where
  workers : Nat
  phase1 : Phase1Out
  phase1End : Nat
  report : PackReport

/-- THE ENTRY OF THE PACKER. Pack the quads of the producers into the generation
    directory `outDir`: phase 1 on the producers, one worker for each way of
    opening one (`phase1`), then phases 2 and 3 on the batches (`packBatches`).
    The packer knows RDF terms, triples and graph names. It does not know whether
    the quads come from a file, a `Dataset`, an array or another store. The output
    is a function of the set of quads and of `sourceId`: it does not depend on the
    number of producers, on how the quads are divided among them, on the size of
    their batches, or on their order (`tests/sbm11/quad_source.sh`). -/
def packQuads (sources : Array (IO QuadSource)) (outDir : String) (runTerms blockRows sortRowsMax : Nat)
    (sourceId : SourceId) : IO PackQuadsOut := do
  let p1 ← phase1 sources outDir runTerms
  let t1 ← IO.monoNanosNow
  let report ← packBatches outDir p1.batches blockRows sortRowsMax sourceId.bytes sourceId.sha256
  pure { workers := sources.size, phase1 := p1, phase1End := t1, report }

def printPermLines (tool : String) (outs : Array PermOut) : IO Unit := do
  for p in [0:4] do
    let o := outs[p]!
    IO.println s!"{tool}: {permNamesArr[p]!} blocks={o.blocks} rows={o.rows} prb1-bytes={o.prbBytes} prm1-bytes={o.prmBytes} frames-const={o.codecs[0]!} frames-raw={o.codecs[1]!} frames-delta={o.codecs[2]!} col-bytes={o.frameBytes[0]!},{o.frameBytes[1]!},{o.frameBytes[2]!},{o.frameBytes[3]!} digest={o.digest.sum}/{o.digest.xor}"

/-- CPU time of the calling thread in nanoseconds (Linux
    `/proc/thread-self/schedstat`, first field); `none` where it cannot be
    read. Phase 2 runs on one thread, so its CPU time is not inflated by
    other processes the way wall time is under load. -/
def threadCpuNs : IO (Option Nat) := do
  try
    let s ← IO.FS.readFile "/proc/thread-self/schedstat"
    pure ((s.splitOn " ").head?.bind String.toNat?)
  catch _ => pure none

/-- The producers of a source, and what the log line says about them. -/
structure Producers where
  /-- The value of `format=` in the log. -/
  label : String
  /-- A word appended to the first log line when the source is not a file read in
      chunks. -/
  note : String := ""
  /-- One way of opening a producer for each worker. -/
  sources : Array (IO QuadSource)

/-- The whole document as a `Dataset` (the batch meaning of the source layer,
    `Source.parseDocument`), then the producer of that `Dataset`. -/
def openDatasetSource (source : String) (fmt : RdfFormat) (base : Option String) : IO QuadSource := do
  let bytes ← IO.FS.readBinFile source
  let some text := String.fromUTF8? bytes
    | throw (IO.userError s!"{source}: UTF-8 error")
  match Source.parseDocument Source.withJsonLd fmt .rdf12 base text with
  | .error e => throw (IO.userError s!"{source}: parse error at {e.pos}: {e.msg}")
  | .ok ds => QuadSource.ofDataset ds 4096

/-- What SOURCE is and how it is read. An HDT file is opened here (the whole file
    is read into memory, as the HDT reader does), and its producer is the triples
    of the store. A document is cut into byte ranges when its syntax allows
    (`planRanges`) and each range is a `fileRangeSource`; with `--via-dataset` the
    document is one `Dataset`. -/
def producersOf (source : String) (size workers : Nat) (opts : SourceOpts) : IO Producers := do
  let kind ← match chooseKind source opts.format with
    | .ok k => pure k
    | .error m => throw (IO.userError m)
  match kind with
  | .hdt =>
      let some gs ← L4Factoidal.HDT.openGraphStore none (System.FilePath.mk source) none
        | throw (IO.userError s!"{source}: not a readable HDT file")
      pure { label := "hdt", sources := #[gs.quadSource 4096] }
  | .document fmt =>
      if opts.viaDataset then
        pure { label := formatLabel fmt, note := " producer=dataset",
               sources := #[openDatasetSource source fmt opts.base] }
      else
        let cfg ← readCfg source size opts
        let ranges ← planRanges cfg.fmt source size workers
        pure { label := formatLabel cfg.fmt,
               sources := ranges.map fun (lo, hi) => fileRangeSource cfg source lo hi }

/-- `--phase2-only`: phase 1, then phase 2; the quad runs are removed, and
    GDV1, GDX1 and the remap files (`run-W-J.tmp.remap`) are kept, so that
    phase 2 can be timed and its output compared byte for byte
    (`tests/sbm11/phase2_scaling.sh`,
    https://github.com/danbri/factoidal/issues/804). -/
def runPhase2Only (source outDir : String) (workers runTerms : Nat) (opts : SourceOpts := {}) :
    IO UInt32 := do
  let t0 ← IO.monoNanosNow
  IO.FS.createDirAll outDir
  let size ← fileSize source
  let ps ← producersOf source size workers opts
  let p1 ← phase1 ps.sources outDir runTerms
  let batches := p1.batches
  let t1 ← IO.monoNanosNow
  let c1 ← threadCpuNs
  let (terms, pages, records) ← phase2 outDir batches
  let c2 ← threadCpuNs
  let t2 ← IO.monoNanosNow
  for b in batches do
    IO.FS.removeFile b.quadRun
    if b.graphs > 0 then IO.FS.removeFile b.graphRun
  let cpu := match c1, c2 with
    | some a, some b => s!" phase2-cpu-ms={ms a b}"
    | _, _ => ""
  IO.println s!"sbm11-pack: phase2-only source={source} format={ps.label} source-bytes={size} workers={ps.sources.size} terms={terms} pages={pages} batches={batches.size} run-records={records} phase1-ms={ms t0 t1} phase2-ms={ms t1 t2}{cpu} peak-rss={← vmHWM}"
  pure 0

/-- `l4sbm11-pack SOURCE OUTDIR`: the producers of SOURCE (`producersOf`), then the
    entry `packQuads`. The source recorded in the manifest is SOURCE: its length and
    its SHA-256, which a task computes while phase 1 runs. -/
def runPack (source outDir : String) (workers runTerms blockRows sortRowsMax : Nat)
    (opts : SourceOpts := {}) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  IO.FS.createDirAll outDir
  let size ← fileSize source
  let ps ← producersOf source size workers opts
  let shaTask ← IO.asTask (sourceSha source size) .dedicated
  let out ← packQuads ps.sources outDir runTerms blockRows sortRowsMax
    { bytes := size, sha256 := do
        match ← IO.wait shaTask with
        | .ok s => pure s
        | .error e => throw e }
  let t5 ← IO.monoNanosNow
  let r := out.report
  let outs := r.outs
  IO.println s!"sbm11-pack: source={source} format={ps.label} source-bytes={size} workers={out.workers} quads-parsed={out.phase1.quads} quads={outs[0]!.rows} duplicate-rows={outs[0]!.dups} terms={r.terms} pages={r.pages} named-graphs={r.graphs} batches={out.phase1.batches.size} run-records={r.records} inline-occurrences={out.phase1.inlineOcc} block-rows={blockRows}{ps.note}"
  printPermLines "sbm11-pack" outs
  IO.println s!"sbm11-pack: generation-bytes={r.genBytes} manifest-bytes={r.manifestBytes} merkle-bytes={r.merkleBytes} total-on-disk={r.genBytes + r.manifestBytes + r.merkleBytes}"
  IO.println s!"sbm11-pack: phase1-ms={ms t0 out.phase1End} phase2-ms={ms 0 r.phase2Ns} phase3a-ms={ms 0 r.phase3aNs} phase3b-ms={ms 0 r.phase3bNs} hash-manifest-ms={ms 0 r.hashNs} total-ms={ms t0 t5} peak-rss={← vmHWM}"
  pure 0

def usage : String :=
  "usage: l4sbm11-pack SOURCE OUTDIR [--format F] [--base IRI] [--workers K] [--run-terms N] [--block-rows B] [--sort-rows M] [--phase2-only] [--via-dataset]\n" ++
  "  F is ntriples, nquads, turtle, trig, rdfxml, jsonld or hdt; without --format the file extension decides (.nt .nq .ttl .trig .rdf .jsonld .hdt).\n" ++
  "  --via-dataset reads the whole document into an RDF dataset and packs the dataset (the memory is that of the document and the dataset)."

/-- The numbers and the source options of the command line. -/
structure Opts where
  workers : Nat := 4
  runTerms : Nat := 262144
  blockRows : Nat := 4096
  sortRows : Nat := 524288
  phase2Only : Bool := false
  source : SourceOpts := {}

def parseOpts : List String → Opts → Option Opts
  | [], o => some o
  | "--workers" :: v :: rest, o => parseOpts rest { o with workers := max 1 v.toNat! }
  | "--run-terms" :: v :: rest, o => parseOpts rest { o with runTerms := max 1 v.toNat! }
  | "--block-rows" :: v :: rest, o => parseOpts rest { o with blockRows := max 1 v.toNat! }
  | "--sort-rows" :: v :: rest, o => parseOpts rest { o with sortRows := max 1 v.toNat! }
  | "--format" :: v :: rest, o => parseOpts rest { o with source := { o.source with format := some v } }
  | "--base" :: v :: rest, o => parseOpts rest { o with source := { o.source with base := some v } }
  | "--phase2-only" :: rest, o => parseOpts rest { o with phase2Only := true }
  | "--via-dataset" :: rest, o => parseOpts rest { o with source := { o.source with viaDataset := true } }
  | _, _ => none

end Sbm11Pack
