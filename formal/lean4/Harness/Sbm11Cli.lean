/-
Harness/Sbm11Cli — `l4sbm11`: read an SBM11 generation (stage 3,
https://github.com/danbri/factoidal/issues/789).

  l4sbm11 stats GEN
      The manifest, the files, per permutation the blocks, rows and frame
      codecs.
  l4sbm11 scan GEN PERM [KEY...] [--limit N] [--ids]
      The rows of permutation PERM (pso, pos, spo, osp) whose key starts with
      KEY... (each an IRI `<...>` or a decimal id), in key order, as N-Quads
      (or as ids with `--ids`). Reads only the blocks whose first and last
      key meet the prefix, by verified positioned reads.
  l4sbm11 count GEN PERM [KEY...]
      The number of such rows: from the PRM1 row counts for every block whose
      first and last row carry the prefix; other blocks are read.
  l4sbm11 dump GEN [PERM]
      Every quad as N-Quads, in the order of PERM (default spo).
  l4sbm11 dump-ids GEN PERM
      Every row as `s p o g` ids (the quad order, whatever the permutation).
  --verify merkle|none   (query, serve, scan, count, dump, dump-ids)
      How reads are checked (https://github.com/danbri/factoidal/issues/796,
      `Sbm11Gen.Verify`). `merkle`: each read is widened to the 65,536-byte
      chunks it touches and each chunk is checked by its Merkle proof; PRM1
      and GDX1 are checked by SHA-256 at open. `none`: each read is one
      `pread` of exactly the needed bytes, no file is hashed; the open checks
      only that the manifest decodes and every file has its length, and a
      changed byte is not detected. Default: `none` when a `CURRENT` pointer
      names GEN (activation checked every file), `merkle` otherwise.
      `stats`, `verify`, `activate`, `prm-check` and `frame-check` always use
      `merkle` (or hash every file).
  l4sbm11 canon SOURCE
      The quads of an N-Triples or N-Quads source as N-Quads, with the term
      normalisation of the packer (language tags in lower case), so that
      `sort -u` of this and of `dump` compare the quad sets.
  l4sbm11 verify GEN
      The activation checks, without activating.
  l4sbm11 activate ROOT NAME
      The activation checks on ROOT/NAME, then `ROOT/CURRENT` := NAME.
  l4sbm11 query GEN ('SPARQL' | --file Q.rq) [--base IRI] [--explain] [--repeat N]
                [--reference-render] [--reference] [--verify merkle|none]
  l4sbm11 serve GEN [--verify merkle|none]
  l4sbm11 prm-check GEN
  l4sbm11 frame-check GEN
      SPARQL over the generation (stage 4): `Harness/Sbm11Query.lean`.
  l4sbm11 reseal GEN
      Test support: rewrite the manifest digests and the `.merkle` sidecars
      from the files as they are (`tests/sbm11/stage3_check.sh` uses it to
      reach the block checks with a changed PRM1 or PRB1).

Activation checks: the manifest decodes and is admitted; every file has the
manifest's length, SHA-256 and Merkle root, and its `.merkle` sidecar holds
the same leaves; the dictionary keys are strictly increasing and their count
is the manifest's; every PRM1 file decodes (blocks sorted, not overlapping,
contiguous in PRB1) and its PRB1 file ends where its last block ends; every
block decodes, its rows are strictly increasing between its PRM1 first and
last row, and every frame is the frame the packer's encoder writes for its
column; every id has a known tag, a dictionary id is below the term count, a
predicate is an IRI, a subject is an IRI or a blank node, a graph is the
default graph or an IRI or a blank node; the four permutations have the
manifest's row count and the same quad digest (sum and xor of a 64-bit hash
of each quad); and the exact check that they hold the same quads: the rows of
POS, SPO and OSP re-keyed to PSO rows, bucketed on disk by groups of PSO
blocks, each bucket sorted and compared with its group (`Sbm11PermCheck`;
the check is proved to give equal quad multisets, `PermSet.perms_same`).

Exit 1 on any error or failed check. Timings, bytes and VmHWM go to stderr.
-/
import Harness.Sbm11Gen
import Harness.Sbm11Query
import Harness.Sbm11Compact
import Harness.Sbm11PermCheck
import L4Factoidal.Syntax.NQuadsFold
import L4Factoidal.Syntax.Utf8Stream

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.Manifest
open Harness.Sbm11Gen

namespace Sbm11Cli

def permArg (s : String) : IO Nat :=
  match permOfName? s with
  | some p => pure p
  | none => throw (IO.userError s!"unknown permutation {s} (pso, pos, spo, osp)")

def keyArg (g : Gen) (s : String) : IO (Option Nat) := do
  if s.startsWith "<" && s.endsWith ">" then
    let iri := ((s.drop 1).dropEnd 1).toString
    if h : isIri iri = true then idOfTerm g (.iri ⟨iri, h⟩)
    else throw (IO.userError s!"not an IRI: {s}")
  else
    match s.toNat? with
    | some n => pure (some n)
    | none => throw (IO.userError s!"a key is an IRI <...> or a decimal id: {s}")

def quadText (g : Gen) (cache : PageCache) (s p o gid : Nat) : IO String := do
  let st ← termOfId g cache s
  let pt ← termOfId g cache p
  let ot ← termOfId g cache o
  let gt ← if gid == 0 then pure none else some <$> termOfId g cache gid
  ok "N-Quads" (nquadLine st pt ot gt)

def report (g : Gen) (t0 : Nat) (extra : String) : IO Unit := do
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"sbm11: {extra} verify={g.verify.name} read-bytes={← g.readBytes.get} fetched-bytes={← g.fetchedBytes.get} file-bytes={← g.fileBytes.get} ms={ms t0 t1} peak-rss={← vmHWM}"

/-- `--verify V` out of an argument list (the last one wins), and the other
    arguments in order. -/
def splitVerify : List String → List String → Option Verify → Except String (List String × Option Verify)
  | [], acc, v => .ok (acc.reverse, v)
  | "--verify" :: x :: rest, acc, _ =>
    match Verify.ofString? x with
    | some v => splitVerify rest acc (some v)
    | Option.none => .error "--verify takes merkle or none"
  | ["--verify"], _, _ => .error "--verify takes merkle or none"
  | x :: rest, acc, v => splitVerify rest (x :: acc) v

/-- The `--verify` option, or the CLI default (`cliDefaultVerify`). -/
def verifyFor (dir : String) : Option Verify → IO Verify
  | some v => pure v
  | Option.none => cliDefaultVerify dir

/-! ## stats -/

def runStats (dir : String) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let g ← openGen .merkle dir
  let m := g.manifest
  IO.println s!"generation: {g.dir}"
  IO.println s!"layout: {m.layout}"
  IO.println s!"source-bytes: {m.sourceBytes} source-sha256: {hex m.sourceSha256}"
  IO.println s!"quads: {m.quads} terms: {m.terms} dictionary-pages: {g.dictHdr.pageCount}"
  let mut total := 0
  for a in m.artifacts do
    IO.println s!"artifact {a.role}: {a.file} bytes={a.bytes} chunks={a.merkle.chunkCount} sha256={hex a.sha256}"
    total := total + a.bytes
  IO.println s!"generation-bytes: {total}"
  for ps in g.perms do
    let mut codecs : Array Nat := #[0, 0, 0, 0]
    let mut minRows := 0
    let mut maxRows := 0
    for i in [0:ps.metas.size] do
      let b := ps.metas[i]!
      let bytes ← verifiedRead g ps.prbPath ps.prbRef ps.leaves ps.cache b.offset b.size
      for off in [0, b.len0, b.len0 + b.len1, b.len0 + b.len1 + b.len2] do
        let t := (bytes.get! off).toNat
        codecs := codecs.modify (min t 3) (· + 1)
      minRows := if i == 0 then b.rows else min minRows b.rows
      maxRows := max maxRows b.rows
    IO.println s!"permutation {permNamesArr[ps.perm]!}: blocks={ps.metas.size} rows={ps.rows} prb1-bytes={ps.prbRef.totalBytes} block-rows-min={minRows} block-rows-max={maxRows} frames-const={codecs[0]!} frames-raw={codecs[1]!} frames-delta={codecs[2]!} frames-other={codecs[3]!}"
  report g t0 "stats"
  pure 0

/-! ## scan and count -/

def parseScanArgs : List String → List String → Option Nat → Bool → (List String × Option Nat × Bool)
  | [], keys, lim, ids => (keys.reverse, lim, ids)
  | "--limit" :: n :: rest, keys, _, ids => parseScanArgs rest keys n.toNat? ids
  | "--ids" :: rest, keys, lim, _ => parseScanArgs rest keys lim true
  | k :: rest, keys, lim, ids => parseScanArgs rest (k :: keys) lim ids

def prefixOf (g : Gen) (keys : List String) : IO (Option Prefix) := do
  let mut vals : Array Nat := #[]
  for k in keys do
    match ← keyArg g k with
    | some v => vals := vals.push v
    | none => return none
  pure (some ⟨vals⟩)

def runScan (dir permS : String) (rest : List String) (verify? : Option Verify) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let g ← openGen (← verifyFor dir verify?) dir
  let perm ← permArg permS
  let (keys, lim, ids) := parseScanArgs rest [] none false
  let tOpen ← IO.monoNanosNow
  let some p ← prefixOf g keys
    | IO.eprintln "sbm11: a key is not in the dictionary: 0 rows"; report g t0 "scan rows=0"; return 0
  let cache ← IO.mkRef ({} : Std.HashMap Nat (Array ByteArray))
  let outRef ← IO.mkRef (0 : Nat)
  let readBefore ← g.readBytes.get
  let fetchedBefore ← g.fetchedBytes.get
  let st ← scan g perm p fun r => do
    let n ← outRef.get
    if lim.all (n < ·) then
      let (s, pp, o, gg) := ofPerm perm r.c0 r.c1 r.c2 r.g
      if ids then IO.println s!"{s} {pp} {o} {gg}"
      else IO.println (← quadText g cache s pp o gg)
      outRef.set (n + 1)
  let tScan ← IO.monoNanosNow
  IO.eprintln s!"sbm11: scan perm={permS} prefix={p.vals} blocks-read={st.blocks} rows={st.rows} block-read-bytes={(← g.readBytes.get) - readBefore} block-fetched-bytes={(← g.fetchedBytes.get) - fetchedBefore} open-ms={ms t0 tOpen} scan-ms={ms tOpen tScan}"
  report g t0 "scan"
  pure 0

def runCount (dir permS : String) (keys : List String) (verify? : Option Verify) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let g ← openGen (← verifyFor dir verify?) dir
  let perm ← permArg permS
  let tOpen ← IO.monoNanosNow
  let some p ← prefixOf g keys
    | IO.println "0"; report g t0 "count"; return 0
  let readBefore ← g.readBytes.get
  let (n, st) ← count g perm p
  let tCount ← IO.monoNanosNow
  IO.println s!"{n}"
  IO.eprintln s!"sbm11: count perm={permS} prefix={p.vals} rows={n} whole-blocks-from-prm1={st.wholeBlocks} blocks-read={st.blocks} block-read-bytes={(← g.readBytes.get) - readBefore} open-ms={ms t0 tOpen} count-ms={ms tOpen tCount}"
  report g t0 "count"
  pure 0

/-! ## dump -/

def runDump (dir permS : String) (idsOnly : Bool) (verify? : Option Verify) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let g ← openGen (← verifyFor dir verify?) dir
  let perm ← permArg permS
  let src ← permSrc g perm
  let ps := src.metas
  let cache ← IO.mkRef ({} : Std.HashMap Nat (Array ByteArray))
  let out ← IO.getStdout
  let mut n := 0
  for i in [0:ps.size] do
    let c ← readBlock g src i
    let mut text := ""
    for j in [0:c.size] do
      let r := c.row j
      let (s, p, o, gg) := ofPerm perm r.c0 r.c1 r.c2 r.g
      if idsOnly then text := text ++ s!"{s} {p} {o} {gg}\n"
      else text := text ++ (← quadText g cache s p o gg) ++ "\n"
      n := n + 1
    out.putStr text
  out.flush
  report g t0 s!"dump perm={permS} rows={n}"
  pure 0

/-! ## canon -/

structure CAcc where
  pending : List (Triple × Option Subject) := []

def runCanon (source : String) : IO UInt32 := do
  let consume (acc : CAcc) (tr : Triple) (g : Option Subject) : CAcc := { pending := (tr, g) :: acc.pending }
  let out ← IO.getStdout
  let flushAcc (acc : CAcc) : IO CAcc := do
    let mut text := ""
    for (tr, g) in acc.pending.reverse do
      let gt := g.map fun s => normalizeTerm s.toTerm
      text := text ++ (← ok "N-Quads" (nquadLine (normalizeTerm tr.s.toTerm) (.iri tr.p) (normalizeTerm tr.o) gt)) ++ "\n"
    out.putStr text
    pure {}
  let mut utf8 := L4Factoidal.Syntax.Utf8Stream.init
  let mut st := L4Factoidal.Syntax.NQuadsStreaming.initialStateC ({} : CAcc)
  let h ← IO.FS.Handle.mk source .read
  repeat
    let bytes ← h.read 65536
    if bytes.isEmpty then break
    match utf8.feed bytes with
    | .error e => throw (IO.userError s!"UTF-8: {e}")
    | .ok (text, u) =>
      utf8 := u
      st := L4Factoidal.Syntax.NQuadsStreaming.feedChunkC .rdf11 consume st text.toList
      if let some e := st.err then throw (IO.userError s!"parse error at {e.pos}: {e.msg}")
      let acc ← flushAcc st.acc
      st := { st with acc := acc }
  match L4Factoidal.Syntax.NQuadsStreaming.finishC .rdf11 consume st with
  | .error e => throw (IO.userError s!"parse error at {e.pos}: {e.msg}")
  | .ok acc => let _ ← flushAcc acc
  out.flush
  pure 0

/-! ## Activation checks -/

def idOk (termCount : Nat) (id : Nat) : Bool :=
  let tag := id / two60
  if isDictTag tag then id % two60 < termCount
  else tag == tagInt || tag == tagBool

def checkPosition (termCount : Nat) (s p o g : Nat) : Option String :=
  if !(idOk termCount s && idOk termCount p && idOk termCount o) then some "id with an unknown tag or a rank past the dictionary"
  else if p / two60 != tagIri then some "predicate is not an IRI"
  else if s / two60 != tagIri && s / two60 != tagBnode then some "subject is not an IRI or a blank node"
  else if g != 0 && !(idOk termCount g && (g / two60 == tagIri || g / two60 == tagBnode)) then
    some "graph is not the default graph, an IRI or a blank node"
  else none

/-- The activation checks of a generation directory, with `tmp` the
    directory for the bucket files of the exact permutation check. Returns
    the number of failures; prints what it checked. -/
def verifyGenIn (dir tmp : String) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut fails := 0
  -- the manifest and every file
  let mbytes ← IO.FS.readBinFile s!"{dir}/{manifestName}"
  let some m := decodeManifest mbytes.data.toList
    | IO.eprintln "FAIL: the manifest does not decode or is not admitted"; return 1
  for a in m.artifacts do
    let path := s!"{dir}/{a.file}"
    let size ← fileSize path
    if size != a.bytes then
      fails := fails + 1
      IO.eprintln s!"FAIL {a.file}: {size} bytes, the manifest says {a.bytes}"
      continue
    let (sha, leaves, ref) ← hashFile path
    if sha != a.sha256 then
      fails := fails + 1; IO.eprintln s!"FAIL {a.file}: SHA-256 differs from the manifest"
    if !(ref == a.merkle) then
      fails := fails + 1; IO.eprintln s!"FAIL {a.file}: Merkle root differs from the manifest"
    let side ← IO.FS.readBinFile (path ++ ".merkle")
    let mut want := ByteArray.empty
    for l in leaves do want := want ++ l
    if side != want then
      fails := fails + 1; IO.eprintln s!"FAIL {a.file}.merkle: leaves differ from the file"
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"sbm11-verify: manifest and {m.artifacts.length} files: failures={fails} ms={ms t0 t1}"
  if fails > 0 then return fails
  let g ← openGen .merkle dir
  -- the dictionary
  if g.dictHdr.termCount != m.terms then
    fails := fails + 1; IO.eprintln s!"FAIL: GDX1 term count {g.dictHdr.termCount}, the manifest says {m.terms}"
  let mut prev : Option ByteArray := none
  let mut keys := 0
  for pg in [0:g.dictHdr.pageCount] do
    let ks ← ok s!"GDV1 page {pg}" (← (Dict.pageM (gdxFetch g) (gdvFetch g) pg).run)
    if pg + 1 < g.dictHdr.pageCount && ks.size != Dict.pageTerms then
      fails := fails + 1; IO.eprintln s!"FAIL: GDV1 page {pg} holds {ks.size} keys"
    for k in ks do
      if let some p := prev then
        if Dict.cmpBytesAt p k != .lt then
          if fails < 5 then IO.eprintln s!"FAIL: dictionary key {keys} not after the previous one"
          fails := fails + 1
      prev := some k
      keys := keys + 1
  if keys != m.terms then
    fails := fails + 1; IO.eprintln s!"FAIL: {keys} dictionary keys, the manifest says {m.terms}"
  let t2 ← IO.monoNanosNow
  IO.eprintln s!"sbm11-verify: dictionary keys={keys}: failures={fails} ms={ms t1 t2}"
  -- the permutations: digests, and the buckets of the exact check (lemma
  -- L3b, `Sbm11PermCheck`, `PermSet.perms_same`)
  let groupRows ← Harness.Sbm11PermCheck.groupRowsOf
  let plan := Harness.Sbm11PermCheck.planGroups (((g.perms[0]?).map (·.metas)).getD #[]) groupRows
  let nb := plan.rows.size
  let flush := Harness.Sbm11PermCheck.flushBytes nb
  Harness.Sbm11PermCheck.createBuckets tmp nb
  let mut bufs : Array ByteArray := Array.replicate (3 * nb) ByteArray.empty
  let mut counts : Array Nat := Array.replicate (3 * nb) 0
  let mut digests : Array Digest2 := #[]
  for ps in g.perms do
    let name := permNamesArr[ps.perm]!
    let hdr ← verifiedRead g ps.prbPath ps.prbRef ps.leaves ps.cache 0 prbHeaderBytes
    if hdr.data.toList != prbHeader ps.perm then
      fails := fails + 1; IO.eprintln s!"FAIL {name}.prb1: header"
    let endOff := match ps.metas.back? with
      | some b => b.offset + b.size
      | none => prbHeaderBytes
    if endOff != ps.prbRef.totalBytes then
      fails := fails + 1; IO.eprintln s!"FAIL {name}.prb1: {ps.prbRef.totalBytes} bytes, the last block ends at {endOff}"
    let mut d : Digest2 := {}
    for i in [0:ps.metas.size] do
      let b := ps.metas[i]!
      let bytes ← verifiedRead g ps.prbPath ps.prbRef ps.leaves ps.cache b.offset b.size
      match decodeBlockAt bytes b 0 with
      | .error e =>
        fails := fails + 1; IO.eprintln s!"FAIL {name} block {i}: {e}"
      | .ok c =>
        -- the frames are the packer encoder's frames for these columns
        let canon := encodeColumnFast c.c0 ++ encodeColumnFast c.c1 ++ encodeColumnFast c.c2 ++ encodeColumnFast c.g
        if canon != bytes then
          fails := fails + 1; IO.eprintln s!"FAIL {name} block {i}: frames are not the encoder's frames"
        for j in [0:c.size] do
          let (s, p, o, gg) := ofPerm ps.perm c.c0[j]! c.c1[j]! c.c2[j]! c.g[j]!
          if let some e := checkPosition m.terms s p o gg then
            if fails < 5 then IO.eprintln s!"FAIL {name} block {i} row {j}: {e}"
            fails := fails + 1
          d := d.add (quadDigest s p o gg)
          if ps.perm != 0 then
            let q := PermSet.rekey ps.perm (c.row j)
            (bufs, counts) ← Harness.Sbm11PermCheck.addRow tmp nb flush bufs counts ps.perm
              (PermSet.bucketOf plan.bounds q) q
    if d.rows != m.quads then
      fails := fails + 1; IO.eprintln s!"FAIL {name}: {d.rows} rows, the manifest says {m.quads}"
    digests := digests.push d
    IO.eprintln s!"sbm11-verify: {name} blocks={ps.metas.size} rows={d.rows} digest={d.sum}/{d.xor}"
  let digestOn := (← IO.getEnv "SBM11_VERIFY_DIGEST") != some "0"
  if digestOn then
    for i in [1:digests.size] do
      if !(digests[i]! == digests[0]!) then
        fails := fails + 1; IO.eprintln s!"FAIL: {permNamesArr[i]!} holds other quads than pso (digest)"
  let t3 ← IO.monoNanosNow
  IO.eprintln s!"sbm11-verify: permutations: failures={fails} ms={ms t2 t3}"
  -- the exact check: each bucket sorted and compared with its PSO group
  Harness.Sbm11PermCheck.flushAll tmp nb bufs
  bufs := #[]
  let mut exactFails := 0
  if fails == 0 then
    for p in [1:4] do
      for j in [0:nb] do
        if exactFails == 0 then
          if let some e ← Harness.Sbm11PermCheck.compareBucket g plan tmp counts p j then
            exactFails := exactFails + 1
            IO.eprintln s!"FAIL: {e}"
  fails := fails + exactFails
  let t4 ← IO.monoNanosNow
  IO.eprintln s!"sbm11-verify: exact permutation check: buckets={nb} group-rows={groupRows} digest={if digestOn then "on" else "off"} failures={exactFails} ms={ms t3 t4}"
  let t3 := t4
  IO.eprintln s!"sbm11-verify: failures={fails} total-ms={ms t0 t3} read-bytes={← g.readBytes.get} peak-rss={← vmHWM}"
  pure fails

/-- The activation checks of a generation directory; the bucket files of the
    exact permutation check go to a directory next to it, removed at the end. -/
def verifyGen (dir : String) : IO Nat := do
  let tmp := s!"{dir}.verify-{← IO.Process.getPID}"
  try verifyGenIn dir tmp
  finally
    if ← System.FilePath.pathExists tmp then IO.FS.removeDirAll tmp

def runVerify (dir : String) : IO UInt32 := do
  let f ← verifyGen dir
  IO.println s!"sbm11-verify: {if f == 0 then "admitted" else "refused"} failures={f}"
  pure (if f == 0 then 0 else 1)

def runActivate (root name : String) : IO UInt32 := do
  if !Harness.GenerationPointer.safeGenerationName name then
    throw (IO.userError s!"not a safe generation name: {name}")
  let f ← verifyGen s!"{root}/{name}"
  if f != 0 then
    IO.println s!"sbm11-activate: refused failures={f}"
    return 1
  if !(← Harness.GenerationPointer.activateGeneration root name) then
    throw (IO.userError "CURRENT was not written")
  IO.println s!"sbm11-activate: admitted pointer={root}/CURRENT generation={name}"
  pure 0

/-- Test support: recompute every file's length, SHA-256, Merkle root and
    `.merkle` sidecar and rewrite the manifest, so that a test can change a
    file and still reach the checks after the digest checks. -/
def runReseal (dir : String) : IO UInt32 := do
  let mbytes ← IO.FS.readBinFile s!"{dir}/{manifestName}"
  let some m := decodeManifest mbytes.data.toList
    | throw (IO.userError "the manifest does not decode")
  let mut arts : Array Artifact := #[]
  for a in m.artifacts do
    let path := s!"{dir}/{a.file}"
    let (sha, leaves, ref) ← hashFile path
    writeLeaves path leaves
    arts := arts.push { a with bytes := ref.totalBytes, sha256 := sha, merkle := ref }
  match encodeManifest? { m with artifacts := arts.toList } with
  | none => throw (IO.userError "the manifest encoder refuses the resealed manifest")
  | some b => IO.FS.writeBinFile s!"{dir}/{manifestName}" (listBytes b)
  IO.println s!"sbm11-reseal: {dir}"
  pure 0

def usage : String :=
  "usage: l4sbm11 stats GEN | scan GEN PERM [KEY...] [--limit N] [--ids] | count GEN PERM [KEY...]\n" ++
  "       | dump GEN [PERM] | dump-ids GEN PERM | canon SOURCE | verify GEN | activate ROOT NAME\n" ++
  "       | query GEN (SPARQL | --file Q.rq) [--base IRI] [--explain] [--repeat N] [--reference-render] [--reference]\n" ++
  "         [--sparql12]\n" ++
  "       | serve GEN [--sparql12] | prm-check GEN | frame-check GEN\n" ++
  "       | update GEN ('SPARQL UPDATE' | --file U.ru) | compact GEN OUTDIR [--block-rows B] [--sort-rows M]\n" ++
  "  --verify merkle|none (query, serve, scan, count, dump, dump-ids): merkle checks every 65,536-byte chunk\n" ++
  "    read by its Merkle proof; none reads exact byte ranges and hashes nothing (a changed byte is not\n" ++
  "    detected). Default: none when a CURRENT pointer names GEN (activated: every file was checked at\n" ++
  "    activation), merkle otherwise. --explain prints the choice (plan: verify=...)."

end Sbm11Cli

open Sbm11Cli in
def main (args0 : List String) : IO UInt32 := do
  try
    let (args, verify?) ← match splitVerify args0 [] Option.none with
      | .ok r => pure r
      | .error e => IO.eprintln s!"l4sbm11: {e}"; return 2
    let verifyUsed := match args with
      | c :: _ => ["query", "serve", "scan", "count", "dump", "dump-ids", "compact"].contains c
      | [] => false
    if verify?.isSome && !verifyUsed then
      IO.eprintln "l4sbm11: --verify applies to query, serve, scan, count, dump and dump-ids"
      return 2
    match args with
    | ["stats", dir] => runStats dir
    | "scan" :: dir :: perm :: rest => runScan dir perm rest verify?
    | "count" :: dir :: perm :: keys => runCount dir perm keys verify?
    | ["dump", dir] => runDump dir "spo" false verify?
    | ["dump", dir, perm] => runDump dir perm false verify?
    | ["dump-ids", dir, perm] => runDump dir perm true verify?
    | ["canon", src] => runCanon src
    | ["verify", dir] => runVerify dir
    | ["activate", root, name] => runActivate root name
    | ["reseal", dir] => runReseal dir
    | ["serve", dir] => Harness.Sbm11Query.runServe dir verify?
    | ["serve", dir, "--sparql12"] => Harness.Sbm11Query.runServe dir verify? .v12
    | "query" :: _ | ["prm-check", _] | ["frame-check", _] => Harness.Sbm11Query.main args0
    | "update" :: _ | "compact" :: _ => Harness.Sbm11Compact.main args0
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11: {e}"
    pure 1
