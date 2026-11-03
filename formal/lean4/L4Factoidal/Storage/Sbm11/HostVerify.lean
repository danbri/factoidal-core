/-
L4Factoidal.Storage.Sbm11.HostVerify — the Merkle check of the host session
(`HostSession`): the decisions that admit the bytes a host returns for an
SBM11 generation, as pure functions.

The SBM11 manifest commits, for each file, a Merkle root over its
65,536-byte chunks (`Manifest.Artifact.merkle`, a `ChunkedArtifact.Ref`).
The leaves are in the `<file>.merkle` sidecar, which is not trusted:

* `admit h a sidecar`: the manifest's chunk size is positive, at most
  `sbm11MaxChunkBytes`, and agrees with the file's length and chunk count
  (`ChunkedArtifact.expectedCount`); every SBM11 packer writes
  `sbm11ChunkBytes`, but a reader does not require it (owner decision
  2026-10-27, D9 B). The sidecar has exactly
  `a.merkle.chunkCount` leaves of 32 bytes, and they rebuild the root that
  the manifest commits (`BlockMerkle.rootWith h`). Then the proof table of the file
  (`BlockMerkle.Tree`) is kept; a wrong table can only refuse a chunk, since
  each chunk is still checked against the root.
* `checkChunk h ad index bytes`: chunk `index` of the file has the length
  that the manifest gives it, and its proof from the table takes it to the
  committed root (`ChunkedArtifact.verifyChunkWith`, the check of the native
  `Harness.PosixRangeIO.readVerifiedChunkCached?`).
* `chunkSpan`, `sliceLo`, `sliceHi`: the chunks of a byte range, and the part
  of each chunk that the range covers.
* `checkAnchor h name anchor bytes`: the trust anchor of the manifest
  (https://github.com/danbri/factoidal/issues/1105): the SHA-256 of the
  manifest bytes, refused when the caller gave an anchor and it is not that
  digest. `sha256OfHex?` reads the anchor (64 hex digits).
* `checkTerms`: the term count of the manifest against the GDX1 header.

`Verify` is the choice of `l4sbm11 query --verify` (`Harness.Sbm11Gen.Verify`):
`merkle` (every read widened to its chunks, each chunk checked) or `none`
(only the lengths of the manifest are checked).

The hash is a parameter (`BlockMerkle.Hasher`): the `#guard`s use
`pureHasher` (pure Lean SHA-256), the wasm ops HACL* SHA-256
(`Wasm.Ops.sbm11PackHasher`), as `PackBytes` does. The `#guard`s for a changed
byte in each kind of file of a packed generation are in `HostVerifyTests`.

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.Sbm11.Manifest

namespace L4Factoidal.Storage.Sbm11.HostVerify

open L4Factoidal.Storage.BlockMerkle
open L4Factoidal.Storage.ChunkedArtifact (verifyChunkWith expectedBytes?)
open L4Factoidal.Storage.Sbm11.Manifest (Artifact)

/-- How the reads of a host session are checked (`Harness.Sbm11Gen.Verify`). -/
inductive Verify where
  /-- every read widened to its 65,536-byte chunks; each chunk is checked by
      its Merkle proof against the root of the manifest -/
  | merkle
  /-- the length of each file and of each read against the manifest only -/
  | none
  deriving BEq, DecidableEq, Repr

def Verify.name : Verify → String
  | .merkle => "merkle"
  | .none => "none"

def Verify.ofString? : String → Option Verify
  | "merkle" => some .merkle
  | "none" => some .none
  | _ => Option.none

/-- The name of the sidecar of `file`. -/
def sidecarName (file : String) : String := file ++ ".merkle"

/-- The leaves of a sidecar: exactly `n` digests of 32 bytes
    (`GenerationVerify.leaves?`). -/
def sidecarLeaves? (n : Nat) (b : ByteArray) : Option (List Digest) :=
  if b.size != n * 32 then none
  else some ((List.range n).map fun i => b.extract (i * 32) (i * 32 + 32))

/-- The chunk size of every SBM11 file (`PackBytes.chunkBytes`,
    `Harness.Sbm11Gen.chunkBytes`). -/
def sbm11ChunkBytes : Nat := 65536

/-- The largest chunk size a host session admits: 16 MiB, the session's
    budget of checked chunks per file (`chunkLimit` of `HostSession`,
    chunks of `sbm11ChunkBytes`), so one chunk never exceeds it. -/
def sbm11MaxChunkBytes : Nat := 16 * 1024 * 1024

/-- A file whose sidecar the manifest admitted: its manifest entry and the
    proof table of its Merkle tree. -/
structure Admitted where
  art : Artifact
  tree : Tree

/-- Admit the sidecar of the file `a`: the manifest's chunk size is
    positive and at most `maxWidth` (default `sbm11MaxChunkBytes`), its chunk
    count is the one that the length and the chunk size give, the count of the
    leaves is that chunk count, and the leaves rebuild the manifest's root. -/
def admit (h : Hasher) (a : Artifact) (sidecar : ByteArray) (maxWidth : Nat := sbm11MaxChunkBytes) :
    Except String Admitted :=
  let r := a.merkle
  if r.chunkBytes == 0 || r.chunkBytes > maxWidth then
    .error s!"{a.file}: the manifest gives chunks of {r.chunkBytes} bytes; a chunk must have 1 to {maxWidth} bytes"
  else if r.chunkCount != ChunkedArtifact.expectedCount r.totalBytes r.chunkBytes then
    .error s!"{a.file}: the manifest gives {r.chunkCount} chunks, but {r.totalBytes} bytes in chunks of {r.chunkBytes} bytes make {ChunkedArtifact.expectedCount r.totalBytes r.chunkBytes}"
  else
  match sidecarLeaves? a.merkle.chunkCount sidecar with
  | none =>
    .error s!"{sidecarName a.file}: {sidecar.size} bytes, not the {a.merkle.chunkCount} leaves of 32 bytes that the manifest's chunk count of {a.file} needs"
  | some ls =>
    if rootWith h ls != a.merkle.root then
      .error s!"{sidecarName a.file}: the leaves do not rebuild the Merkle root that the manifest commits for {a.file}"
    else .ok { art := a, tree := Tree.ofLeavesWith h ls }

/-- Check chunk `index` of an admitted file: its length is the manifest's,
    and its proof takes it to the manifest's root. -/
def checkChunk (h : Hasher) (ad : Admitted) (index : Nat) (bytes : ByteArray) : Except String Unit :=
  let r := ad.art.merkle
  let at_ := s!"{ad.art.file}: chunk {index} (bytes {index * r.chunkBytes} to {index * r.chunkBytes + bytes.size})"
  match expectedBytes? r index, ad.tree.proof? index with
  | some n, some proof =>
    if bytes.size != n then .error s!"{at_}: {bytes.size} bytes, the manifest gives {n}"
    else if verifyChunkWith h r index bytes proof then .ok ()
    else .error s!"{at_} does not match the Merkle root that the manifest commits; the file was changed"
  | _, _ => .error s!"{ad.art.file}: no chunk {index} (the manifest gives {r.chunkCount})"

/-- The first and the last chunk of the bytes `[off, off + len)`, `len > 0`,
    for chunks of `cb` bytes. -/
def chunkSpan (cb off len : Nat) : Nat × Nat := (off / cb, (off + len - 1) / cb)

/-- The first byte, inside chunk `c`, of the bytes `[off, off + len)`. -/
def sliceLo (cb off c : Nat) : Nat := max off (c * cb) - c * cb

/-- The end, inside chunk `c`, of the bytes `[off, off + len)`. -/
def sliceHi (cb off len c : Nat) : Nat := min (off + len) ((c + 1) * cb) - c * cb

/-! ## The trust anchor of the manifest (https://github.com/danbri/factoidal/issues/1105)

The manifest has no digest of its own. The Merkle check above binds the
names, the lengths and the Merkle references of the manifest to the bytes a
query reads, but not its other fields (the SHA-256 of each file, the length
and the SHA-256 of the source, the quad count). A caller that knows the
SHA-256 of the manifest bytes (from a signed release, a CID document, or a
value that the application pins) gives it as the trust anchor; the open
then refuses a manifest whose SHA-256 is not the anchor, so every field of
the manifest is bound. -/

/-- The value of one hex digit, either case. -/
def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The bytes of an even number of hex digits, appended to `acc`. -/
def hexBytes? (acc : ByteArray) : List Char → Option ByteArray
  | [] => some acc
  | [_] => none
  | a :: b :: rest =>
    match hexValue? a, hexValue? b with
    | some x, some y => hexBytes? (acc.push (x * 16 + y).toUInt8) rest
    | _, _ => none

/-- A SHA-256 digest written as 64 hex digits, either case. -/
def sha256OfHex? (s : String) : Option ByteArray :=
  if s.length != 64 then none else hexBytes? ByteArray.empty s.toList

/-- A digest as lowercase hex. -/
def hexOf (b : ByteArray) : String := L4Factoidal.Crypto.bytesToHex b

/-- The trust-anchor check of the manifest bytes `mbytes` (named `name`):
    the SHA-256 of the bytes (hash `h`), when there is no anchor or it is the
    anchor; else an error that names the manifest and both digests. -/
def checkAnchor (h : Hasher) (name : String) (anchor : Option ByteArray) (mbytes : ByteArray) :
    Except String ByteArray :=
  let d := h.digest mbytes
  match anchor with
  | none => .ok d
  | some a =>
    if a == d then .ok d
    else .error s!"{name}: SHA-256 {hexOf d}, the trust anchor manifestSha256 is {hexOf a}; the manifest was changed, or the anchor is for another generation"

/-- The term count of the manifest against the term count of the GDX1
    header (`Harness.Sbm11Cli.verifyGen` makes the same check). The header is
    read at open; under `merkle` its chunk is checked against the root. -/
def checkTerms (gdxFile : String) (manifestTerms gdxTerms : Nat) : Except String Unit :=
  if manifestTerms == gdxTerms then .ok ()
  else .error s!"{gdxFile}: the GDX1 header gives {gdxTerms} terms, the manifest says {manifestTerms}"

/-! ## Tests (the generation-level ones are in `HostVerifyTests`) -/

private def c0 : ByteArray := ByteArray.mk #[1, 2]
private def c1 : ByteArray := ByteArray.mk #[3, 4]
private def c2 : ByteArray := ByteArray.mk #[5]
private def leaves3 : List Digest := [c0, c1, c2].map (leafWith pureHasher)
private def side3 : ByteArray := leaves3.foldl (· ++ ·) ByteArray.empty
private def art3 : Artifact :=
  { role := "PRB1-SPO", file := "spo.prb1", bytes := 5, sha256 := ByteArray.mk (Array.replicate 32 0),
    merkle := { totalBytes := 5, chunkBytes := 2, chunkCount := 3, root := rootWith pureHasher leaves3 } }

private def chunkOk (index : Nat) (b : ByteArray) : Bool :=
  match admit pureHasher art3 side3 with
  | .ok ad => (checkChunk pureHasher ad index b).toBool
  | .error _ => false

-- the sidecar is admitted (a chunk size other than 65,536 is admitted too);
-- each chunk passes at its own index only
#guard (admit pureHasher art3 side3).toBool
-- a chunk size of 0, or one above the maximum, is refused
#guard !(admit pureHasher { art3 with merkle := { art3.merkle with chunkBytes := 0 } } side3).toBool
#guard !(admit pureHasher art3 side3 1).toBool
-- a chunk count that the length and the chunk size do not give is refused
#guard !(admit pureHasher { art3 with merkle := { art3.merkle with chunkCount := 4 } } side3).toBool
#guard chunkOk 0 c0 && chunkOk 1 c1 && chunkOk 2 c2
#guard !chunkOk 1 c0 && !chunkOk 0 c1 && !chunkOk 3 c2
-- one changed bit in a chunk is refused
#guard !chunkOk 1 (ByteArray.mk #[3, 5])
#guard !chunkOk 2 (ByteArray.mk #[4])
-- a chunk of the wrong length is refused
#guard !chunkOk 2 (ByteArray.mk #[5, 0])
-- a sidecar with a changed leaf, a missing leaf or an extra byte is refused
#guard !(admit pureHasher art3 (side3.set! 40 (side3.get! 40 ^^^ 1)) 2).toBool
#guard !(admit pureHasher art3 (side3.extract 0 64) 2).toBool
#guard !(admit pureHasher art3 (side3.push 0) 2).toBool
-- a manifest whose root has one changed bit refuses the true sidecar
#guard !(admit pureHasher
  { art3 with merkle := { art3.merkle with root := art3.merkle.root.set! 31 (art3.merkle.root.get! 31 ^^^ 1) } }
  side3 2).toBool
-- the chunks of a range and the part of each
#guard chunkSpan 2 1 3 == (0, 1)
#guard chunkSpan 65536 65535 2 == (0, 1)
#guard chunkSpan 65536 0 65536 == (0, 0)
#guard sliceLo 2 1 0 == 1 && sliceHi 2 1 3 0 == 2 && sliceLo 2 1 1 == 0 && sliceHi 2 1 3 1 == 2
-- the anchor: 64 hex digits of either case; any other text is no digest
private def abcHex : String := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (sha256OfHex? abcHex).map hexOf == some abcHex
#guard (sha256OfHex? abcHex.toUpper).map hexOf == some abcHex
#guard (sha256OfHex? (abcHex.drop 2).toString).isNone
#guard (sha256OfHex? ((abcHex.drop 1).toString ++ "g")).isNone
#guard (sha256OfHex? (abcHex ++ "00")).isNone
-- the SHA-256 of "abc" (FIPS 180-4) passes as the anchor of the bytes "abc";
-- no anchor gives the digest; another anchor is refused with both digests
#guard (checkAnchor pureHasher "m" none "abc".toUTF8).toOption.map hexOf == some abcHex
#guard (checkAnchor pureHasher "m" (sha256OfHex? abcHex) "abc".toUTF8).toBool
#guard match checkAnchor pureHasher "m" (sha256OfHex? abcHex) "abd".toUTF8 with
  | .error e => (e.splitOn abcHex).length > 1 && e.startsWith "m: SHA-256 "
  | .ok _ => false
#guard (checkTerms "dict.gdx1" 5 5).toBool && !(checkTerms "dict.gdx1" 5 4).toBool

end L4Factoidal.Storage.Sbm11.HostVerify
