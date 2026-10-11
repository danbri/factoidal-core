import Harness.NativeHasher
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.VC.Multibase

open L4Factoidal.Crypto
open L4Factoidal.VC.Multibase

namespace NativeCryptoSmoke

private def check (name : String) (valid : Bool) : IO Unit := do
  unless valid do
    throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def repeatByte (count : Nat) (byte : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count byte)

private def sampleBytes (count : Nat) : ByteArray := Id.run do
  let mut state : UInt32 := 0x9e3779b9
  let mut bytes : Array UInt8 := #[]
  for _ in [0:count] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 17)
    state := state ^^^ (state <<< 5)
    bytes := bytes.push state.toUInt8
  return ByteArray.mk bytes

private def streamDigest (fold : BlockFold256) (chunkSize : Nat)
    (bytes : ByteArray) : ByteArray :=
  let chunks := (List.range ((bytes.size + chunkSize - 1) / chunkSize)).map
    (fun index => bytes.extract (index * chunkSize) ((index + 1) * chunkSize))
  let state := chunks.foldl (fun state chunk => state.updateWith fold chunk) Sha256Stream.init
  state.finishWith fold

private def hashCases : List (String × ByteArray) :=
  [("empty", ByteArray.empty),
   ("FIPS abc", "abc".toUTF8),
   ("FIPS 56-byte", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8),
   ("112-byte", ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
     "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toUTF8),
   ("UTF-8", "Ünïcödé".toUTF8),
   ("1-byte", repeatByte 1 0x61),
   ("55-byte", repeatByte 55 0x61),
   ("56-byte", repeatByte 56 0x61),
   ("63-byte", repeatByte 63 0x61),
   ("64-byte", repeatByte 64 0x61),
   ("65-byte", repeatByte 65 0x61),
   ("FIPS million a", repeatByte 1000000 0x61),
   ("deterministic 1 MiB", sampleBytes 1048576)]

private def runHashCases : IO Nat := do
  let mut passed := 0
  for (name, bytes) in hashCases do
    let expected ← IO.lazyPure fun _ => sha256 bytes
    let actual ← IO.lazyPure fun _ => Harness.nativeSha256 bytes
    check s!"whole SHA-256 {name}: {bytes.size} bytes"
      (actual.size == 32 && actual == expected)
    passed := passed + 1
    let chunkSizes := if bytes.size > 200 then [64, 65536] else [1, 7, 64, 65536]
    for chunkSize in chunkSizes do
      let streamed ← IO.lazyPure fun _ =>
        streamDigest Harness.nativeBlockFold256 chunkSize bytes
      check s!"native SHA-256 stream {name}: chunk={chunkSize}" (streamed == expected)
      passed := passed + 1
  return passed

private def stateBytes (words : Array UInt32) : ByteArray :=
  words.foldl appendWord32BE ByteArray.empty

private def runBlockCases : IO Nat := do
  let bytes := sampleBytes 320
  let states := [H256_0, Array.replicate 8 0, Array.replicate 8 0xFFFFFFFF,
    (List.range 8).map (fun index => bytesToWordBE32 bytes (index * 4)) |>.toArray]
  let mut passed := 0
  for words in states do
    for (offset, blocks) in [(0, 0), (0, 1), (1, 2), (63, 4), (64, 4), (320, 0)] do
      let expected ← IO.lazyPure fun _ =>
        stateBytes (processBlocks256At words bytes offset blocks)
      let actual ← IO.lazyPure fun _ =>
        sha256BlocksHacl (stateBytes words) bytes offset.toUSize blocks.toUSize
      check s!"raw block fold offset={offset} blocks={blocks}" (actual == expected)
      passed := passed + 1
  for badState in [ByteArray.empty, repeatByte 31 0, repeatByte 33 0] do
    check s!"block fold refuses state bytes={badState.size}"
      ((sha256BlocksHacl badState bytes 0 1).size == 0)
    passed := passed + 1
  for (offset, blocks) in [(321, 0), (300, 1), (0, UInt32.size / 64)] do
    check s!"block fold refuses offset={offset} blocks={blocks}"
      ((sha256BlocksHacl (stateBytes H256_0) bytes offset.toUSize blocks.toUSize).size == 0)
    passed := passed + 1
  return passed

private structure EdVector where
  secret : String
  publicKeyHex : String
  message : String
  signature : String

private def edVectors : List EdVector :=
  [{ secret := "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
     publicKeyHex := "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
     message := "",
     signature := "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b" },
   { secret := "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
     publicKeyHex := "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
     message := "72",
     signature := "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00" },
   { secret := "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
     publicKeyHex := "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
     message := "af82",
     signature := "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a" }]

private def hexBytes (encoded : String) : IO ByteArray :=
  match byteArrayOfHex? encoded with
  | some bytes => pure bytes
  | none => throw (IO.userError "invalid RFC 8032 fixture hex")

private def runEdCases : IO Nat := do
  let mut passed := 0
  for vector in edVectors do
    let secret ← hexBytes vector.secret
    let publicKey ← hexBytes vector.publicKeyHex
    let message ← hexBytes vector.message
    let signature ← hexBytes vector.signature
    unless secret.size == 32 && publicKey.size == 32 && signature.size == 64 do
      throw (IO.userError "invalid RFC 8032 fixture byte lengths")
    check "RFC 8032 public key" (Ed25519.secretToPublic secret == publicKey)
    check "RFC 8032 deterministic signature" (Ed25519.sign secret message == signature)
    check "RFC 8032 signature verification" (Ed25519.verify publicKey message signature)
    let corrupted := signature.set! 0 (signature[0]! ^^^ 1)
    check "RFC 8032 corrupted signature refused" (!Ed25519.verify publicKey message corrupted)
    passed := passed + 4
  check "Ed25519 short secret refused"
    ((Ed25519.secretToPublic (repeatByte 31 0)).size == 0)
  check "Ed25519 short signing secret refused"
    ((Ed25519.sign (repeatByte 31 0) ByteArray.empty).size == 0)
  check "Ed25519 short public key refused"
    (!Ed25519.verify (repeatByte 31 0) ByteArray.empty (repeatByte 64 0))
  check "Ed25519 short signature refused"
    (!Ed25519.verify (repeatByte 32 0) ByteArray.empty (repeatByte 63 0))
  return passed + 4

end NativeCryptoSmoke

def main : IO Unit := do
  let hashes ← NativeCryptoSmoke.runHashCases
  let blocks ← NativeCryptoSmoke.runBlockCases
  let signatures ← NativeCryptoSmoke.runEdCases
  IO.println s!"native crypto: {hashes + blocks + signatures} pass, 0 fail; whole/stream={hashes}, raw-block={blocks}, Ed25519={signatures}"
