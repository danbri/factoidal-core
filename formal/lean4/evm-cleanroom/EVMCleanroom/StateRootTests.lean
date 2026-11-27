import EVMCleanroom.StateRoot

/-! Executable checks (`#guard`, tests not proofs) of the trie builder
against published constants: the empty trie and empty-code hashes, the
empty logs hash, and the four-key example trie of the Ethereum wiki's
Patricia tree page. -/

namespace EVMCleanroom.StateRootTests
open StateRoot

private def a : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

private def hex (b : Array UInt8) : String :=
  String.join (b.toList.map fun x =>
    let d := "0123456789abcdef".toList
    String.ofList [d.getD (x.toNat / 16) '0', d.getD (x.toNat % 16) '0'])

private def ascii (s : String) : Array UInt8 := s.toUTF8.data

#guard (trieRoot a []).map hex =
  some "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
#guard hex (MPT.hashBytes a #[]) =
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard hex (logsHash a []) =
  "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
-- Wiki example: do/verb, dog/puppy, doge/coin, horse/stallion.
#guard (trieRoot a [(ascii "do", ascii "verb"), (ascii "dog", ascii "puppy"),
    (ascii "doge", ascii "coin"), (ascii "horse", ascii "stallion")]).map hex =
  some "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"
-- Order of insertion does not matter for the same set.
#guard trieRoot a [(ascii "horse", ascii "stallion"), (ascii "doge", ascii "coin"),
    (ascii "do", ascii "verb"), (ascii "dog", ascii "puppy")] =
  trieRoot a [(ascii "do", ascii "verb"), (ascii "dog", ascii "puppy"),
    (ascii "doge", ascii "coin"), (ascii "horse", ascii "stallion")]
#guard rlpScalar 0 = #[0x80]
#guard rlpScalar 0x7f = #[0x7f]
#guard rlpScalar 0x80 = #[0x81, 0x80]
#guard rlpScalar 1024 = #[0x82, 0x04, 0x00]
#guard rlpList [] = #[0xc0]
#guard (rlpBytes ((List.replicate 56 (0 : UInt8)).toArray)).extract 0 2 = #[0xb8, 56]
#guard hexPrefix [1, 2, 3, 4, 5] false = #[0x11, 0x23, 0x45]
#guard hexPrefix [0, 1, 2, 3, 4, 5] false = #[0x00, 0x01, 0x23, 0x45]
#guard hexPrefix [0, 15, 1, 12, 11, 8] true = #[0x20, 0x0f, 0x1c, 0xb8]
#guard hexPrefix [15, 1, 12, 11, 8] true = #[0x3f, 0x1c, 0xb8]

end EVMCleanroom.StateRootTests
