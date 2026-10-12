/-
L4Factoidal.Storage.Sbm11.Manifest — the SBM11 manifest, `manifest.sbm11`
(`docs/designissues/2026-10-11-shardborough-vs-qlever.md` section 6.6;
https://github.com/danbri/factoidal/issues/789).

A generation of wire version 11 is ten files: the dictionary (`dict.gdv1`,
`dict.gdx1`, stage 2) and one PRM1 and one PRB1 file per permutation (PSO,
POS, SPO, OSP). The manifest names each file by its role and commits its
length, its SHA-256 and its Merkle chunk root (`ChunkedArtifact.Ref`,
65,536-byte chunks, the commitment the SBM10 manifest uses). A positioned
read of a block is admitted chunk by chunk against that root
(`Harness.PosixRangeIO.readVerifiedRangeCached?`); the leaf hashes are in a
`<file>.merkle` sidecar, which is not trusted: a leaf is used only through a
proof to the committed root.

## Bytes

    "SBM0"  version u8 = 11            (the SBM magic; an SBM0 to SBM10
                                        reader refuses version 11)
    layout   string                    `sbm11Layout`
    sourceBytes u64  sourceSha256 32 bytes
    quads u64  terms u64               distinct quads, dictionary terms
    count u32
    artifact*: role string  file string  bytes u64  sha256 32 bytes
               chunkBytes u32  chunkCount u32  merkleRoot 32 bytes

A string is a u32 byte count and UTF-8 (`ShardManifest.encodeString`).

## Admission

`manifestAdmitted`: the layout is `sbm11Layout`; both digests are 32 bytes;
the roles are exactly `roles`, in that order; every file name is a single
safe path component; every field inside its width; every Merkle reference
is valid for the artifact's length. `decodeManifest` checks the same
predicate on what it read. The round trip
`ManifestTheorems.decodeManifest_encodeManifest?` has
`encodeManifest? m = some bytes` as its only hypothesis.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.Sbm11.Column

namespace L4Factoidal.Storage.Sbm11.Manifest

open L4Factoidal (two32 two64)
open L4Factoidal.Storage.ShardManifest (encodeString decodeString takeExact byteArrayOfList fitsU32
  encodeChunkedRef decodeChunkedRef)
open L4Factoidal.Storage.Sbm11.Column (put64 get64 put32 get32)

def sbm11Layout : String := "sbm11-gdv1-gdx1-prm1-prb1-pso-pos-spo-osp-merkle-v1"

def permNames : List String := ["pso", "pos", "spo", "osp"]

/-- The roles of a stage 3 generation, in manifest order. -/
def roles : List String :=
  ["GDV1", "GDX1", "PRM1-PSO", "PRB1-PSO", "PRM1-POS", "PRB1-POS", "PRM1-SPO", "PRB1-SPO",
   "PRM1-OSP", "PRB1-OSP"]

/-- The file name the packer gives each role. -/
def fileOfRole (role : String) : String :=
  match role with
  | "GDV1" => "dict.gdv1"
  | "GDX1" => "dict.gdx1"
  | "PRM1-PSO" => "pso.prm1"
  | "PRB1-PSO" => "pso.prb1"
  | "PRM1-POS" => "pos.prm1"
  | "PRB1-POS" => "pos.prb1"
  | "PRM1-SPO" => "spo.prm1"
  | "PRB1-SPO" => "spo.prb1"
  | "PRM1-OSP" => "osp.prm1"
  | "PRB1-OSP" => "osp.prb1"
  | _ => ""

structure Artifact where
  role : String
  file : String
  bytes : Nat
  sha256 : ByteArray
  merkle : ChunkedArtifact.Ref
  deriving DecidableEq

structure Manifest where
  layout : String
  sourceBytes : Nat
  sourceSha256 : ByteArray
  quads : Nat
  terms : Nat
  artifacts : List Artifact
  deriving DecidableEq

def safeFileName (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." && !(name.contains '/') && !(name.contains '\\')

def artifactAdmitted (a : Artifact) : Bool :=
  fitsU32 a.role.toUTF8.size && fitsU32 a.file.toUTF8.size && safeFileName a.file &&
    decide (a.bytes < two64) && a.sha256.size == 32 && ChunkedArtifact.valid a.merkle &&
    a.merkle.totalBytes == a.bytes && fitsU32 a.merkle.chunkBytes && fitsU32 a.merkle.chunkCount

def manifestAdmitted (m : Manifest) : Bool :=
  m.layout == sbm11Layout && fitsU32 m.layout.toUTF8.size && decide (m.sourceBytes < two64) &&
    m.sourceSha256.size == 32 && decide (m.quads < two64) && decide (m.terms < two64) &&
    m.artifacts.map (·.role) == roles && m.artifacts.all artifactAdmitted

def artifactBytes (a : Artifact) : List UInt8 :=
  encodeString a.role ++ encodeString a.file ++ put64 a.bytes ++ a.sha256.toList ++
    encodeChunkedRef a.merkle

/-- `"SBM0"` and the wire version 11. -/
def manifestMagic : List UInt8 := [83, 66, 77, 48, 11]

def manifestBytes (m : Manifest) : List UInt8 :=
  manifestMagic ++ encodeString m.layout ++ put64 m.sourceBytes ++ m.sourceSha256.toList ++
    put64 m.quads ++ put64 m.terms ++ put32 m.artifacts.length ++ (m.artifacts.map artifactBytes).flatten

def encodeManifest? (m : Manifest) : Option (List UInt8) :=
  if manifestAdmitted m then some (manifestBytes m) else none

def getArtifact (bs : List UInt8) : Option (Artifact × List UInt8) := do
  let (role, r1) ← decodeString bs
  let (file, r2) ← decodeString r1
  let (bytes, r3) ← get64 r2
  let (sha, r4) ← takeExact 32 r3
  let (merkle, r5) ← decodeChunkedRef bytes r4
  some ({ role, file, bytes, sha256 := byteArrayOfList sha, merkle }, r5)

def getArtifactsGo : Nat → List UInt8 → List Artifact → Option (List Artifact × List UInt8)
  | 0, bs, acc => some (acc.reverse, bs)
  | n + 1, bs, acc =>
    match getArtifact bs with
    | none => none
    | some (a, rest) => getArtifactsGo n rest (a :: acc)

/-- The fields after the layout string, before admission. -/
structure Fields where
  sourceBytes : Nat
  sha : List UInt8
  quads : Nat
  terms : Nat
  artifacts : List Artifact

def decodeFields (r1 : List UInt8) : Option Fields :=
  match get64 r1 with
  | none => none
  | some (sourceBytes, r2) =>
    match takeExact 32 r2 with
    | none => none
    | some (sha, r3) =>
      match get64 r3 with
      | none => none
      | some (quads, r4) =>
        match get64 r4 with
        | none => none
        | some (terms, r5) =>
          match get32 r5 with
          | none => none
          | some (count, r6) =>
            match getArtifactsGo count r6 [] with
            | some (artifacts, []) => some { sourceBytes, sha, quads, terms, artifacts }
            | _ => none

def admitManifest (m : Manifest) : Option Manifest := if manifestAdmitted m then some m else none

/-- Everything after the magic and the version byte. -/
def decodeManifestTail (rest : List UInt8) : Option Manifest :=
  match decodeString rest with
  | none => none
  | some (layout, r1) =>
    match decodeFields r1 with
    | none => none
    | some f =>
      admitManifest { layout, sourceBytes := f.sourceBytes, sourceSha256 := byteArrayOfList f.sha,
                      quads := f.quads, terms := f.terms, artifacts := f.artifacts }

def decodeManifest (bs : List UInt8) : Option Manifest :=
  match bs with
  | m0 :: m1 :: m2 :: m3 :: v :: rest =>
    if [m0, m1, m2, m3, v] = manifestMagic then decodeManifestTail rest else none
  | _ => none

def artifactOf? (m : Manifest) (role : String) : Option Artifact :=
  m.artifacts.find? (·.role == role)

end L4Factoidal.Storage.Sbm11.Manifest
