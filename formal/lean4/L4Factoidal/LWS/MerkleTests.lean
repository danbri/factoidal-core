/-
L4Factoidal.LWS.MerkleTests — build-time checks of the LWS Merkle hashes
(https://github.com/danbri/factoidal/issues/919), with the specification
hasher `pureHasher` (pure Lean FIPS 180-4 SHA-256). Positive and negative.
-/
import L4Factoidal.LWS.Merkle
import L4Factoidal.LWS.Snapshot

namespace L4Factoidal.LWS.MerkleTests

open L4Factoidal.LWS
open L4Factoidal.LWS.Merkle
open L4Factoidal.Storage.BlockMerkle (pureHasher Hasher)

private def hex (b : ByteArray) : String := L4Factoidal.Crypto.bytesToHex b

/-! ## The hash: FIPS 180-4 vectors -/

#guard hex (pureHasher.digest "abc".toUTF8) ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hex (pureHasher.digest ByteArray.empty) ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
-- RFC 9530 `Repr-Digest` of an empty representation: the base64 of the
-- SHA-256 of no bytes.
#guard Base64.encode (pureHasher.digest ByteArray.empty) ==
  "47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU="
#guard hex (pureHasher.digest "abd".toUTF8) !=
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

/-! ## Members -/

#guard mcontains "/" "/a/" && mcontains "/a/" "/a/b" && mcontains "/a/" "/a/c/"
#guard !mcontains "/a/" "/a/b/c" && !mcontains "/a/" "/a/" && !mcontains "/a" "/a/b"
#guard mparent "/a/b" == some "/a/" && mparent "/a/" == some "/" && mparent "/" == none
-- A path with no leading slash has the storage root as its parent but is
-- not longer than it; `validTarget` refuses such a path.
#guard parent? "a" == some "/" && mparent "a" == none
#guard countBytes 258 == ⟨#[0, 0, 0, 0, 0, 0, 1, 2]⟩

/-! ## A storage written through the Merkle store -/

private abbrev MS := MerkleStore MemStore memStoreLaws

private def dataE (p body : String) (kind : ResourceKind := .dataResource) : Entry :=
  { path := p, kind, contentType := "text/plain", body := body.toUTF8, mtime := 0 }

private def contE (p : String) : Entry :=
  { path := p, kind := .container, contentType := "text/turtle", body := ByteArray.empty, mtime := 0 }

private def root0 : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := ByteArray.empty, mtime := 0 }] }

private def put (s : MkState MemStore) (e : Entry) : MkState MemStore := MS.put s e
private def del (s : MkState MemStore) (p : String) : MkState MemStore := MS.remove s p

private def s0 : MkState MemStore := MkState.ofMem (some pureHasher) root0

private def s1 : MkState MemStore :=
  [contE "/a/", contE "/a/x/", dataE "/a/x/deep" "one", dataE "/a/b" "bee", contE "/c/",
   dataE "/c/d" "dee"].foldl put s0

private def dig (s : MkState MemStore) (p : String) : Option ByteArray := s.data.dig[p]?

-- A data resource's digest is the SHA-256 of its bytes.
#guard dig s1 "/a/b" == some (pureHasher.digest "bee".toUTF8)
#guard hex ((dig s1 "/a/b").getD ByteArray.empty) ==
  hex (L4Factoidal.Crypto.sha256 "bee".toUTF8)
-- Every stored path has a digest; no other path has one.
#guard ["/", "/a/", "/a/x/", "/a/x/deep", "/a/b", "/c/", "/c/d"].all (fun p => (dig s1 p).isSome)
#guard (dig s1 "/nothing").isNone
-- A container's digest is the digest of its members' list.
#guard dig s1 "/c/" == some (containerDigest pureHasher [("/c/d", pureHasher.digest "dee".toUTF8)])
#guard dig s1 "/a/" == some (containerDigest pureHasher
  [("/a/b", pureHasher.digest "bee".toUTF8), ("/a/x/", (dig s1 "/a/x/").getD ByteArray.empty)])

/-- Every stored path has the digest the recomputation from the store gives
(`MkOk.dig_eq_recompute`, checked here on one state). -/
private def agrees (s : MkState MemStore) : Bool :=
  (memPaths s.base ++ ["/missing", "/a/missing/"]).all fun p =>
    dig s p == recompute pureHasher MemStore s.base p

#guard agrees s1

/-- The data built in one pass from the entries (a snapshot opened) is the
data the writes maintained. -/
private def rebuiltAgrees (s : MkState MemStore) : Bool :=
  let r := rebuild pureHasher s.base.entries
  (memPaths s.base).all fun p => r.dig[p]? == dig s p

#guard rebuiltAgrees s1

/-! ## A change deep in the tree -/

private def s2 : MkState MemStore := put s1 (dataE "/a/x/deep" "two")

-- The changed resource and every container above it get a new digest.
#guard ["/a/x/deep", "/a/x/", "/a/", "/"].all fun p => dig s1 p != dig s2 p
-- The sibling subtree keeps its digests.
#guard ["/c/", "/c/d", "/a/b"].all fun p => dig s1 p == dig s2 p
#guard agrees s2 && rebuiltAgrees s2
-- Writing the same bytes again changes nothing.
#guard ["/a/x/deep", "/a/x/", "/a/", "/"].all fun p => dig s2 p == dig (put s2 (dataE "/a/x/deep" "two")) p
-- Writing a container entry again (a new modification time) changes no digest.
#guard (memPaths s2.base).all fun p => dig s2 p == dig (put s2 { contE "/a/" with mtime := 9 }) p

/-! ## Create, delete and move -/

private def s3 : MkState MemStore := put s2 (dataE "/c/e" "new")
#guard dig s3 "/c/" != dig s2 "/c/" && dig s3 "/" != dig s2 "/" && dig s3 "/a/" == dig s2 "/a/"
#guard agrees s3 && rebuiltAgrees s3

private def s4 : MkState MemStore := del s3 "/c/e"
-- Deleting the new member gives back the digests before it was created.
#guard (memPaths s2.base).all fun p => dig s4 p == dig s2 p
#guard (dig s4 "/c/e").isNone && agrees s4

-- A move as `Move.move` does it: remove at the old path, write at the new.
private def s5 : MkState MemStore := put (del s2 "/a/b") (dataE "/c/b" "bee")
#guard dig s5 "/a/" != dig s2 "/a/" && dig s5 "/c/" != dig s2 "/c/" && dig s5 "/" != dig s2 "/"
#guard dig s5 "/c/b" == dig s2 "/a/b" && agrees s5 && rebuiltAgrees s5

/-! ## What is not a member -/

-- An auxiliary resource has a digest but is not a member: changing it does
-- not change its container's digest.
private def s6 : MkState MemStore := put s2 (dataE "/a/b.meta" "m1" .metadataResource)
private def s7 : MkState MemStore := put s6 (dataE "/a/b.meta" "m2" .metadataResource)
#guard dig s6 "/a/" == dig s2 "/a/" && dig s7 "/a/" == dig s6 "/a/"
#guard dig s6 "/a/b.meta" != dig s7 "/a/b.meta" && agrees s7

/-! ## Off -/

private def off : MkState MemStore :=
  [contE "/a/", dataE "/a/b" "bee"].foldl put (MkState.ofMem none root0)
#guard off.hasher.isNone && off.data.dig.isEmpty && off.data.kids.isEmpty
#guard (memLookup off.base "/a/b").isSome

end L4Factoidal.LWS.MerkleTests
