/-
Harness/Sbm11Compact — `l4sbm11 update` and `l4sbm11 compact` (SBM11 stage 5,
https://github.com/danbri/factoidal/issues/791; design record
`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.7).

  l4sbm11 update GEN ('SPARQL UPDATE' | --file U.ru) [--base IRI] [--sparql12]
                  [--max-overlay-entries N] [--max-overlay-bytes N]
  l4sbm11 compact GEN OUTDIR [--block-rows B] [--sort-rows M] [--verify merkle|none] [--via-quads]

`update` appends one DLOG batch to the generation's `deltas.dlog`
(`Sbm11Update.appendUpdate`). Every later open replays the log into the
overlay (`Sbm11Query.openOverlaid`), and every scan merges it
(`IdQuery.scanFoldM`, `Overlay.mergeRows`).

The log has no size limit unless one is set (https://github.com/danbri/factoidal/issues/851).
`--max-overlay-entries N` and `--max-overlay-bytes N` (or the environment variables
`SBM11_MAX_OVERLAY_ENTRIES` and `SBM11_MAX_OVERLAY_BYTES`, which the flags override) make
`update` refuse a request that would take the log past N entries or N bytes of file
(`OverlayLimit.exceeded`: a log that holds exactly N is within the limit). The refusal exits 1,
writes nothing, and names `l4sbm11 compact` and `l4sbm11 activate`: the caller folds the log
into a new generation and repeats the request. A log that is already over the limit refuses
every request. `l4sbm11 serve` reports the size of the overlay it opened and whether it is
within the limit that the environment sets. Nothing compacts the log by itself
(https://github.com/danbri/factoidal/issues/803 item 4; the expected failure
`xfail-auto-compaction` in tests/sbm11/update_where.sh asks for `--auto-compact`).

`compact` writes a new generation that holds the base with the overlay
applied, through the packer's phases 2 and 3 (`Sbm11PackLib.packBatches`), in
place of the packer's phase 1 (parse):

  A. One SPO scan of the overlaid generation (overlay merged) marks the ids
     the remaining quads use: dictionary ranks and overlay vocabulary entries.
  B. One term run: the used dictionary keys (read page by page, already in key
     order) merged with the sorted keys of the used overlay terms; each gets a
     run-local number.
  C. A second SPO scan writes one quad run: per quad four words, a run-local
     number for a dictionary or overlay term, the id itself for an inline
     term, 0 for the default graph (the phase-1 format).
  D. `packBatches`: phase 2 (dictionary, remap), phase 3 (four permutations,
     blocks, PRM1), hashes and the manifest, by the packer's own code.

`--via-quads` is the reference route (https://github.com/danbri/factoidal/issues/866
item 3). It replaces steps A to C by the packer's phase 1: one SPO scan of the
overlaid generation decodes each row to RDF terms (`Session.termOf`) and gives the
quads to a phase-1 worker (`Sbm11Pack.openPhase1`) as any producer of quads does; step
D is the same. Its output is byte-identical to the default route's (run.sh parts (h), (i)
and (m) compare them). It takes about twice as long on the olympics generation, because it
decodes and hashes every term and the default route moves key bytes and ids; the default
route is the tuned implementation and this one is the specification-shaped route that
a test compares it with (design record
`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 11.4).

So the output's dictionary holds exactly the terms of its quads, in key
order, as a pack of the same quads does: `tests/sbm11/run.sh` part (i)
compares every artifact of a compacted generation with a fresh pack of the
updated source, byte for byte. Then `compacted.epoch` (the greatest epoch
folded) and `compacted.source.sha256` (SHA-256 of the source manifest and
log) are written, as `l4block-shard-compact` does. OUTDIR is a new
generation; activate it with `l4sbm11 activate`.

Memory: the two scans are block by block; B holds one byte per dictionary
term (used flags) and one number per used term (the local numbers), and the
sorted overlay keys. The quad run is written in 8 MiB pieces.

This is a HARNESS: it does file I/O.
-/
import Harness.Sbm11Query
import Harness.Sbm11PackLib
import Harness.Sbm11Delta
import Harness.Sbm11Update
import L4Factoidal.Storage.Sbm11.Overlay

namespace Harness.Sbm11Compact

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open Harness.Sbm11Gen
open Harness.Sbm11Query
open L4Factoidal.Qlvr (cmpBytes mergeSortBy)

/-- The id kinds a quad column holds. -/
inductive IdKind where
  | dict (rank : Nat)
  | delta (idx : Nat)
  | other
  deriving Inhabited

@[inline] def kindOf (x : UInt64) : IdKind :=
  let tag := (x >>> 60).toNat
  let pay := (x &&& 0x0FFFFFFFFFFFFFFF).toNat
  if isDictTag tag then .dict pay
  else if tag == Overlay.tagDelta then .delta pay
  else .other

/-- Phases 2 and 3 of a compaction over the phase-1 batches `batches`, and the two files
    that record what it folded: `compacted.epoch` (the greatest epoch folded) and
    `compacted.source.sha256` (the SHA-256 of the source manifest and the log, which is
    also the source digest in the new manifest). Both routes of `compact` end here. -/
def packCompacted (srcDir outDir : String) (batches : Array Sbm11Pack.Batch)
    (blockRows sortRowsMax : Nat) : IO (Sbm11Pack.PackReport × Nat) := do
  let manifestBytes ← IO.FS.readBinFile s!"{srcDir}/{manifestName}"
  let (allBatches, dlogBytes, _) ← Harness.Sbm11Delta.readBatches srcDir
  let identityInput := manifestBytes ++ dlogBytes
  let identity := Harness.nativeSha256 identityInput
  let r ← Sbm11Pack.packBatches outDir batches blockRows sortRowsMax identityInput.size (pure identity)
  let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk srcDir)
  let epoch := Harness.CompactedEpoch.foldedThrough baseEpoch allBatches
  if !(← Harness.CompactedEpoch.write (System.FilePath.mk outDir) epoch) then
    throw (IO.userError "could not write compacted.epoch")
  if !(← Harness.PosixRangeIO.atomicReplaceFileSyncRaw s!"{outDir}/compacted.source.sha256" identity) then
    throw (IO.userError "could not write compacted.source.sha256")
  pure (r, epoch)

def runCompact (src outDir : String) (blockRows sortRowsMax : Nat) (v : Verify) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let ss ← openOverlaid v src
  let tOpen ← IO.monoNanosNow
  let srcDir := ss.g.dir
  IO.FS.createDirAll outDir
  let termCount := ss.g.dictHdr.termCount
  let vocab ← ss.ovVocab.get
  -- A. used ids
  let usedRef ← IO.mkRef (ByteArray.mk (Array.replicate termCount 0))
  let usedVRef ← IO.mkRef (ByteArray.mk (Array.replicate vocab.size 0))
  let rowsRef ← IO.mkRef 0
  scanAll ss 2 #[] fun cols n => do
    let mut u ← usedRef.swap .empty
    let mut uv ← usedVRef.swap .empty
    for i in [0:n] do
      for c in [0:4] do
        match kindOf (IdQuery.at64 cols[c]! i) with
        | .dict r => u := u.set! r 1
        | .delta k => uv := uv.set! k 1
        | .other => pure ()
    usedRef.set u
    usedVRef.set uv
    rowsRef.modify (· + n)
  let used ← usedRef.get
  let usedV ← usedVRef.get
  let t1 ← IO.monoNanosNow
  -- B. one term run: used dictionary keys merged with the used overlay keys
  let mut vkeys : Array (ByteArray × Nat) := #[]
  for k in [0:vocab.size] do
    if usedV.get! k == 1 then
      match vocab[k]?.bind termKeyBytes? with
      | some key => vkeys := vkeys.push (key, k)
      | none => throw (IO.userError s!"overlay term {k} has no dictionary key")
  vkeys := mergeSortBy vkeys fun a b => cmpBytes a.1 b.1 != .gt
  let termRun := s!"{outDir}/run-compact-0.tmp"
  let hRun ← IO.FS.Handle.mk termRun .write
  let mut buf := ByteArray.emptyWithCapacity (1 <<< 20)
  let mut localOf : Array Nat := Array.replicate termCount 0
  let mut localOfV : Array Nat := Array.replicate vocab.size 0
  let mut next := 1
  let mut vi := 0
  let pages := (termCount + Dict.pageTerms - 1) / Dict.pageTerms
  for pg in [0:pages] do
    let (packed, offs) ← ss.pageKeys pg
    for j in [0:offs.size - 1] do
      let rank := pg * Dict.pageTerms + j
      if rank < termCount && used.get! rank == 1 then
        let key := packed.extract offs[j]! offs[j + 1]!
        -- overlay keys below this key first
        for _ in [0:vkeys.size] do
          if vi < vkeys.size then
            let (vk, k) := vkeys[vi]!
            match cmpBytes vk key with
            | .lt =>
              buf := Sbm11Pack.put32 buf vk.size ++ vk
              localOfV := localOfV.set! k next
              next := next + 1
              vi := vi + 1
            | .eq => throw (IO.userError "an overlay term has a dictionary key")
            | .gt => break
          else break
        buf := Sbm11Pack.put32 buf key.size ++ key
        localOf := localOf.set! rank next
        next := next + 1
        if buf.size ≥ (1 <<< 20) then
          hRun.write buf
          buf := ByteArray.emptyWithCapacity (1 <<< 20)
  for _ in [0:vkeys.size] do
    if vi < vkeys.size then
      let (vk, k) := vkeys[vi]!
      buf := Sbm11Pack.put32 buf vk.size ++ vk
      localOfV := localOfV.set! k next
      next := next + 1
      vi := vi + 1
  hRun.write buf
  hRun.flush
  let terms := next - 1
  let t2 ← IO.monoNanosNow
  -- C. one quad run over run-local numbers
  let quadRun := s!"{outDir}/quads-compact-0.tmp"
  let hQ ← IO.FS.Handle.mk quadRun .write
  let qbuf ← IO.mkRef (ByteArray.emptyWithCapacity (8 <<< 20))
  let badRef ← IO.mkRef 0
  scanAll ss 2 #[] fun cols n => do
    let mut b ← qbuf.swap .empty
    let mut bad := 0
    for i in [0:n] do
      for c in [0:4] do
        let x := IdQuery.at64 cols[c]! i
        let y : Nat := match kindOf x with
          | .dict r => localOf[r]!
          | .delta k => localOfV[k]!
          | .other => x.toNat
        if y == 0 && x != 0 then bad := bad + 1
        b := Sbm11Pack.pushW b y.toUInt64
    if b.size ≥ (8 <<< 20) then
      hQ.write b
      b := ByteArray.emptyWithCapacity (8 <<< 20)
    qbuf.set b
    badRef.modify (· + bad)
  hQ.write (← qbuf.get)
  hQ.flush
  if (← badRef.get) != 0 then throw (IO.userError s!"{← badRef.get} ids without a run-local number")
  let quads ← rowsRef.get
  let t3 ← IO.monoNanosNow
  -- D. the packer's phases 2 and 3
  let batch : Sbm11Pack.Batch := { termRun, quadRun, terms, quads }
  let (r, epoch) ← packCompacted srcDir outDir #[batch] blockRows sortRowsMax
  let t4 ← IO.monoNanosNow
  IO.println s!"sbm11-compact: source={srcDir} output={outDir} base-quads={ss.g.manifest.quads} {ss.deltaText} quads={r.outs[0]!.rows} terms={r.terms} new-terms-kept={vkeys.size} dictionary-terms-dropped={termCount - (terms - vkeys.size)} epoch={epoch} verify={v.name}"
  Sbm11Pack.printPermLines "sbm11-compact" r.outs
  IO.println s!"sbm11-compact: generation-bytes={r.genBytes} manifest-bytes={r.manifestBytes} merkle-bytes={r.merkleBytes} total-on-disk={r.genBytes + r.manifestBytes + r.merkleBytes}"
  IO.println s!"sbm11-compact: open-and-replay-ms={ms t0 tOpen} scan-used-ms={ms tOpen t1} term-run-ms={ms t1 t2} quad-run-ms={ms t2 t3} phase2-ms={ms 0 r.phase2Ns} phase3a-ms={ms 0 r.phase3aNs} phase3b-ms={ms 0 r.phase3bNs} hash-manifest-ms={ms 0 r.hashNs} total-ms={ms t0 t4} peak-rss={← vmHWM}"
  pure 0

/-- The reference route (`--via-quads`): the quads of the overlaid generation go to the
    packer's phase 1 as the quads of any producer do. One SPO scan (the overlay merged)
    decodes each row to RDF terms and pushes the rows of a block as one batch to a
    phase-1 worker; phases 2 and 3 and the files that record the epoch are
    `packCompacted`, the code of the default route. The worker keeps a map of 262,144
    terms, the default of a single-worker pack. -/
def runCompactViaQuads (src outDir : String) (blockRows sortRowsMax : Nat) (v : Verify) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let ss ← openOverlaid v src
  let tOpen ← IO.monoNanosNow
  let srcDir := ss.g.dir
  IO.FS.createDirAll outDir
  let sink ← Sbm11Pack.openPhase1 outDir 0 262144
  let rowsRef ← IO.mkRef 0
  scanAll ss 2 #[] fun cols n => do
    let mut batch : L4Factoidal.RDF.QuadSource.Batch := Array.mkEmpty n
    for i in [0:n] do
      let st ← ss.termOf (IdQuery.at64 cols[0]! i)
      let pt ← ss.termOf (IdQuery.at64 cols[1]! i)
      let ot ← ss.termOf (IdQuery.at64 cols[2]! i)
      let gid := IdQuery.at64 cols[3]! i
      let gname ← if gid == 0 then pure none else some <$> (subjectOf (← ss.termOf gid))
      let p ← match pt with
        | .iri i => pure i
        | _ => throw (IO.userError "a predicate that is not an IRI")
      batch := batch.push ({ s := ← subjectOf st, p := p, o := ot }, gname)
    sink.consume batch
    rowsRef.modify (· + n)
  let w ← sink.finish
  let t1 ← IO.monoNanosNow
  let (r, epoch) ← packCompacted srcDir outDir w.batches blockRows sortRowsMax
  let t4 ← IO.monoNanosNow
  IO.println s!"sbm11-compact: via-quads source={srcDir} output={outDir} base-quads={ss.g.manifest.quads} {ss.deltaText} quads-read={← rowsRef.get} quads={r.outs[0]!.rows} terms={r.terms} epoch={epoch} verify={v.name}"
  Sbm11Pack.printPermLines "sbm11-compact" r.outs
  IO.println s!"sbm11-compact: generation-bytes={r.genBytes} manifest-bytes={r.manifestBytes} merkle-bytes={r.merkleBytes} total-on-disk={r.genBytes + r.manifestBytes + r.merkleBytes}"
  IO.println s!"sbm11-compact: open-and-replay-ms={ms t0 tOpen} phase1-ms={ms tOpen t1} phase2-ms={ms 0 r.phase2Ns} phase3a-ms={ms 0 r.phase3aNs} phase3b-ms={ms 0 r.phase3bNs} hash-manifest-ms={ms 0 r.hashNs} total-ms={ms t0 t4} peak-rss={← vmHWM}"
  pure 0

def parseCompactOpts : List String → Nat × Nat × Option Verify → Option (Nat × Nat × Option Verify)
  | [], o => some o
  | "--block-rows" :: x :: rest, (_, m, v) => parseCompactOpts rest (max 1 x.toNat!, m, v)
  | "--sort-rows" :: x :: rest, (b, _, v) => parseCompactOpts rest (b, max 1 x.toNat!, v)
  | "--verify" :: x :: rest, (b, m, _) => (Verify.ofString? x).bind fun v => parseCompactOpts rest (b, m, some v)
  | _, _ => none

/-- Take the flag `name N` out of `parts`: the remaining arguments and the number
    (`ok none`: the flag is absent; `error`: the flag has no decimal number). -/
def takeNatFlag (name : String) (parts : List String) : Except String (List String × Option Nat) :=
  match parts.idxOf name with
  | i =>
    if i < parts.length then
      match parts[i + 1]? with
      | some v =>
        match v.toNat? with
        | some n => .ok (parts.take i ++ parts.drop (i + 2), some n)
        | none => .error s!"{name} takes a decimal number, not {v}"
      | none => .error s!"{name} takes a decimal number"
    else .ok (parts, none)

def updateUsage : String :=
  "usage: l4sbm11 update GEN ('SPARQL UPDATE' | --file U.ru) [--base IRI] [--sparql12] [--max-overlay-entries N] [--max-overlay-bytes N]"

def main (args : List String) : IO UInt32 := do
  match args with
  | "update" :: dir :: parts0 =>
    -- `--sparql12`: the SPARQL 1.2 grammar (triple terms, directional literals);
    -- `--base IRI`: the BASE of the request (relative IRIs in the text);
    -- `--max-overlay-entries N`, `--max-overlay-bytes N`: refuse a request that would take the log
    -- past N entries or N bytes (the environment variables SBM11_MAX_OVERLAY_ENTRIES and
    -- SBM11_MAX_OVERLAY_BYTES set the same limits when the flags are absent; no limit by default)
    let v12 := parts0.contains "--sparql12"
    let parts1 := parts0.filter (· != "--sparql12")
    match takeNatFlag "--max-overlay-entries" parts1 with
    | .error e => IO.eprintln s!"l4sbm11 update: {e}"; return 2
    | .ok (parts2, maxEntries) =>
    match takeNatFlag "--max-overlay-bytes" parts2 with
    | .error e => IO.eprintln s!"l4sbm11 update: {e}"; return 2
    | .ok (parts3, maxBytes) =>
    let (parts, base) := match parts3.idxOf "--base" with
      | i => if i + 1 < parts3.length then
          (parts3.take i ++ parts3.drop (i + 2), some parts3[i + 1]!)
        else (parts3, none)
    let version : L4Factoidal.SPARQL.SparqlVersion := if v12 then .v12 else .v11
    let limit ← try
        let envLimit ← overlayLimitFromEnv
        pure (some { maxEntries := maxEntries.orElse fun _ => envLimit.maxEntries,
                     maxBytes := maxBytes.orElse fun _ => envLimit.maxBytes
                   : L4Factoidal.Storage.Sbm11.OverlayLimit.Limit })
      catch e => IO.eprintln s!"l4sbm11 update: {e}"; pure none
    let some limit := limit | return 2
    match parts with
    | ["--file", path] =>
      try Harness.Sbm11Update.appendUpdate dir (← IO.FS.readFile path) version base limit
      catch e => IO.eprintln s!"l4sbm11 update: {e}"; return 1
    | [] =>
      IO.eprintln updateUsage
      return 2
    | _ =>
      try Harness.Sbm11Update.appendUpdate dir (String.intercalate " " parts) version base limit
      catch e => IO.eprintln s!"l4sbm11 update: {e}"; return 1
  | "compact" :: src :: out :: opts0 =>
    let viaQuads := opts0.contains "--via-quads"
    let opts := opts0.filter (· != "--via-quads")
    match parseCompactOpts opts (4096, 524288, none) with
    | none =>
      IO.eprintln "usage: l4sbm11 compact GEN OUTDIR [--block-rows B] [--sort-rows M] [--verify merkle|none] [--via-quads]"
      return 2
    | some (b, m, v?) =>
      try
        let v ← match v? with
          | some v => pure v
          | none => cliDefaultVerify src
        if viaQuads then runCompactViaQuads src out b m v else runCompact src out b m v
      catch e => IO.eprintln s!"l4sbm11 compact: {e}"; return 1
  | _ =>
    IO.eprintln s!"{updateUsage} | compact GEN OUTDIR [--block-rows B] [--sort-rows M] [--verify merkle|none] [--via-quads]"
    return 2

end Harness.Sbm11Compact
