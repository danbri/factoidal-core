/-
L4Factoidal.Storage.Sbm11.HostVerifyTests — the Merkle check of the host
session (`HostVerify`) over a generation that `PackBytes.packFiles` packs, with
one changed bit in each kind of file
(https://github.com/danbri/factoidal/issues/1009).

`checkAll` makes the checks of `HostSession.openSession` and
`HostSession.Session.chunk` under `Verify.merkle`, over every chunk of every
file: the manifest decodes, the sidecar of each file is admitted against the
manifest's root (`admit`), and each chunk passes `checkChunk`. The packed
generation passes. A generation with one changed bit in the dictionary
(GDV1, GDX1), the graph list (GNL1), a PRM1 or a PRB1 file, a `.merkle`
sidecar or a Merkle reference of the manifest is refused, and the error
names that file.

`openChecks` adds the checks of the open that are not about chunks: the trust
anchor of the manifest (`checkAnchor`, https://github.com/danbri/factoidal/issues/1105)
before the manifest is decoded, and the term count against the GDX1 header
(`checkTerms`) after. A manifest with a changed quad count is not refused by
the Merkle check (no read binds that field); with the anchor of the old
manifest it is refused, and the error names `manifest.sbm11` and both
digests. The untampered generation opens with its anchor; a wrong anchor is
refused.

The hash is `pureHasher` (pure Lean SHA-256). No `sorry`, no `axiom`, no
`partial`.
-/
import L4Factoidal.Storage.Sbm11.HostVerify
import L4Factoidal.Storage.Sbm11.PackBytes
import L4Factoidal.Storage.Sbm11.Dict

namespace L4Factoidal.Storage.Sbm11.HostVerifyTests

open L4Factoidal.RDF
open L4Factoidal.Storage.BlockMerkle (pureHasher)
open L4Factoidal.Storage.Sbm11.HostVerify
open L4Factoidal.Storage.Sbm11.Manifest (decodeManifest Artifact Manifest manifestBytes)
open L4Factoidal.Storage.Sbm11.PackBytes (Packed packFiles)

private abbrev Files := Array (String × ByteArray)

private def fileOf? (fs : Files) (name : String) : Option ByteArray :=
  (fs.find? (·.1 == name)).map (·.2)

/-- Every chunk of the admitted file `ad`, checked. -/
private def checkChunks (fs : Files) (ad : Admitted) : Except String Unit := do
  let a := ad.art
  let some b := fileOf? fs a.file | throw s!"{a.file}: not found"
  if b.size != a.bytes then throw s!"{a.file}: {b.size} bytes, the manifest says {a.bytes}"
  let cb := a.merkle.chunkBytes
  (Array.range a.merkle.chunkCount).foldl (fun acc c => do
      acc
      checkChunk pureHasher ad c (b.extract (c * cb) (min b.size ((c + 1) * cb))))
    (pure ())

/-- The checks of the session under `merkle`, over every chunk of every file;
    the number of files checked. -/
private def checkAll (fs : Files) : Except String Nat := do
  let some mb := fileOf? fs "manifest.sbm11" | throw "manifest.sbm11: not found"
  let some m := decodeManifest mb.data.toList | throw "manifest.sbm11: does not decode"
  m.artifacts.toArray.foldl (fun acc a => do
      let n ← acc
      let some side := fileOf? fs (sidecarName a.file) | throw s!"{sidecarName a.file}: not found"
      let ad ← admit pureHasher a side
      checkChunks fs ad
      pure (n + 1))
    (pure 0)

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def q1 : PackBytes.Quad := (⟨.iri (exI "http://e/s"), exI "http://e/p", .literal (Literal.string "hello")⟩, none)
private def q2 : PackBytes.Quad := (⟨.iri (exI "http://e/s"), exI "http://e/p", .literal (Literal.string "world")⟩,
  some (.iri (exI "http://e/g")))

/-- A generation with a named graph: eleven files, eleven sidecars, the
    manifest. -/
private def gen : Files :=
  match packFiles pureHasher #[q1, q2] #[] 0 (pureHasher.digest ByteArray.empty) with
  | .ok p => p.files
  | .error _ => #[]

/-- `fs` with bit 0 of byte `i` of `name` changed (`i` from the end when
    `fromEnd`). -/
private def flip (fs : Files) (name : String) (i : Nat) (fromEnd : Bool := false) : Files :=
  fs.map fun (n, b) =>
    if n != name || b.size == 0 then (n, b)
    else
      let j := if fromEnd then b.size - 1 - (i % b.size) else i % b.size
      (n, b.set! j (b.get! j ^^^ 1))

/-- `fs` with the first occurrence of the bytes of `old` in `name` replaced
    by `new` (the same length). -/
private def replaceText (fs : Files) (name old new : String) : Files :=
  fs.map fun (n, b) =>
    if n != name then (n, b)
    else
      let o := old.toUTF8
      let w := new.toUTF8
      match (List.range (b.size + 1 - o.size)).find? (fun i => b.extract i (i + o.size) == o) with
      | none => (n, b)
      | some i => (n, (List.range w.size).foldl (fun acc k => acc.set! (i + k) (w.get! k)) b)

private def refusedNaming (fs : Files) (file : String) : Bool :=
  match checkAll fs with
  | .ok _ => false
  | .error e => (e.splitOn file).length > 1

-- the packed generation: 23 files, and every one of its 11 data files passes
#guard gen.size == 23
#guard (checkAll gen).toOption == some 11
-- the replacement of the repro of the review: "hello" to "HELLO" in GDV1
#guard (replaceText gen "dict.gdv1" "hello" "HELLO") != gen
#guard refusedNaming (replaceText gen "dict.gdv1" "hello" "HELLO") "dict.gdv1"
-- one changed bit in each kind of data file
#guard refusedNaming (flip gen "dict.gdv1" 0) "dict.gdv1"
#guard refusedNaming (flip gen "dict.gdx1" 3 true) "dict.gdx1"
#guard refusedNaming (flip gen "graphs.gnl1" 0 true) "graphs.gnl1"
#guard refusedNaming (flip gen "pso.prm1" 30) "pso.prm1"
#guard refusedNaming (flip gen "spo.prb1" 3 true) "spo.prb1"
#guard refusedNaming (flip gen "osp.prb1" 0) "osp.prb1"
-- one changed bit in a sidecar
#guard refusedNaming (flip gen "pos.prb1.merkle" 5) "pos.prb1"
-- one changed bit in the last Merkle root of the manifest (that of
-- osp.prb1, which a query over ?s ?p ?o does not read)
#guard refusedNaming (flip gen "manifest.sbm11" 3 true) "osp.prb1"
-- One changed bit in each of the last 40 bytes of the manifest (the chunk
-- size, chunk count and root of osp.prb1). Since a reader admits any chunk
-- size that agrees with the length and the count (owner decision 2026-10-27,
-- D9 B), a changed chunk size that still describes the same chunks is
-- admitted; then every chunk of every file was checked against the same
-- roots (checkAll), so the bytes read are the packed bytes. Every other
-- change is refused.
private def dataOf (fs : Files) : Option (List (String × Nat × Nat × ByteArray)) := do
  let mb ← fileOf? fs "manifest.sbm11"
  let m ← decodeManifest mb.data.toList
  some (m.artifacts.map fun a => (a.file, a.bytes, a.merkle.totalBytes, a.merkle.root))
#guard (List.range 40).all fun i =>
  let f := flip gen "manifest.sbm11" i true
  !(checkAll f).toBool || (dataOf f).isSome && dataOf f == dataOf gen
-- and most of those changes (every one in the root) are refused
#guard ((List.range 32).filter fun i => (checkAll (flip gen "manifest.sbm11" i true)).toBool).isEmpty

/-! ## The trust anchor and the term count (issue 1105) -/

/-- The checks of `HostSession.openSession` with the trust anchor `anchor`:
    the anchor, the Merkle check of every chunk (`checkAll`), the term count
    of the manifest against the GDX1 header; the SHA-256 of the manifest. -/
private def openChecks (anchor : Option ByteArray) (fs : Files) : Except String ByteArray := do
  let some mb := fileOf? fs "manifest.sbm11" | throw "manifest.sbm11: not found"
  let d ← checkAnchor pureHasher "manifest.sbm11" anchor mb
  let _ ← checkAll fs
  let some m := decodeManifest mb.data.toList | throw "manifest.sbm11: does not decode"
  let some gdx := fileOf? fs "dict.gdx1" | throw "dict.gdx1: not found"
  let hdr ← Dict.parseGdxHeader (gdx.extract 0 Dict.gdxHeaderBytes)
  checkTerms "dict.gdx1" m.terms hdr.termCount
  pure d

private def manifestOf (fs : Files) : Option Manifest :=
  (fileOf? fs "manifest.sbm11").bind fun b => decodeManifest b.data.toList

/-- `fs` with its manifest replaced by the encoding of `f` of it. -/
private def withManifest (fs : Files) (f : Manifest → Manifest) : Files :=
  match manifestOf fs with
  | none => fs
  | some m => fs.map fun (n, b) =>
    if n == "manifest.sbm11" then (n, ByteArray.mk (manifestBytes (f m)).toArray) else (n, b)

/-- The anchor of the packed generation: the SHA-256 of its manifest. -/
private def anchor0 : ByteArray := pureHasher.digest ((fileOf? gen "manifest.sbm11").getD ByteArray.empty)

private def refusedWith (r : Except String ByteArray) (parts : List String) : Bool :=
  match r with
  | .ok _ => false
  | .error e => parts.all fun p => (e.splitOn p).length > 1

/-- the generation with one more quad in its manifest -/
private def moreQuads : Files := withManifest gen fun m => { m with quads := m.quads + 1 }

-- the untampered generation opens with its anchor, and without one; the
-- digest is the anchor
#guard (openChecks (some anchor0) gen).toOption == some anchor0
#guard (openChecks none gen).toOption == some anchor0
-- a changed quad count: one changed manifest byte, which the Merkle check
-- does not refuse; with the anchor of the old manifest it is refused, and the
-- error names the manifest and both digests
#guard moreQuads != gen
#guard (manifestOf moreQuads).map (·.quads) == (manifestOf gen).map (·.quads + 1)
#guard (openChecks none moreQuads).toBool
#guard refusedWith (openChecks (some anchor0) moreQuads)
  ["manifest.sbm11", hexOf anchor0, hexOf (pureHasher.digest ((fileOf? moreQuads "manifest.sbm11").getD ByteArray.empty))]
-- the same for a changed SHA-256 of a file and of the source
#guard refusedWith (openChecks (some anchor0) (withManifest gen fun m =>
  { m with artifacts := m.artifacts.map fun a =>
      if a.file == "spo.prb1" then { a with sha256 := a.sha256.set! 0 (a.sha256.get! 0 ^^^ 1) } else a }))
  ["manifest.sbm11"]
#guard refusedWith (openChecks (some anchor0) (withManifest gen fun m =>
  { m with sourceBytes := m.sourceBytes + 1 })) ["manifest.sbm11"]
-- a wrong anchor (one changed bit) refuses the untampered generation
#guard refusedWith (openChecks (some (anchor0.set! 31 (anchor0.get! 31 ^^^ 1))) gen)
  ["manifest.sbm11", hexOf anchor0]
-- a changed term count is refused with no anchor: the GDX1 header disagrees
#guard refusedWith (openChecks none (withManifest gen fun m => { m with terms := m.terms + 1 }))
  ["dict.gdx1", "terms"]

end L4Factoidal.Storage.Sbm11.HostVerifyTests
