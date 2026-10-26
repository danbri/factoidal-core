/-
L4Factoidal.Codec.XzTests — build-time checks for the xz reader and writer.

The vectors were made by other implementations (Python `lzma`, which is
liblzma) so that the reader is checked against a writer it was not written
with: the five check types, the LZMA2 property variants, an incompressible
input (an uncompressed chunk), an empty stream, concatenated streams with
padding. The writer is checked against the empty stream those tools write,
and by reading its output back. Each rule has a negative twin: a changed
byte, a truncation, a reserved feature.
-/
import L4Factoidal.Codec.Xz

namespace L4Factoidal.Codec

private def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - 48 else c.toNat - 87

/-- Bytes from a string of hexadecimal digits. -/
private def hex (s : String) : ByteArray :=
  let cs := s.toList
  ByteArray.mk ((List.range (cs.length / 2)).map (fun i =>
    (hexVal (cs[2 * i]!) * 16 + hexVal (cs[2 * i + 1]!)).toUInt8)).toArray

private def txt : ByteArray :=
  "the quick brown fox jumps over the lazy dog. the quick brown fox jumps over the lazy dog again and again and again".toUTF8

private def rnd : ByteArray := hex "82b70eee7f1a5039bef07ec2347f066ed08f5dc7512447e3404300026b6e545594a065685d64c498"

private def vDefault : ByteArray := hex (
  "fd377a585a000004e6d6b4460200210116000000742fe5a3e00071003d5d003a1a08ce76c7e5e9d6" ++
  "0734c3d10ebfce55e1aabde0e48f9801dd8de507549e65255f273a6a7eb4d3490389cdc9a2eb7104" ++
  "78b56aa5d089a156e245000000000000e8a9af934775f1f0000159722643f4f51fb6f37d01000000" ++
  "0004595a")

private def vNone : ByteArray := hex (
  "fd377a585a000000ff12d9410200210116000000742fe5a3e00071003d5d003a1a08ce76c7e5e9d6" ++
  "0734c3d10ebfce55e1aabde0e48f9801dd8de507549e65255f273a6a7eb4d3490389cdc9a2eb7104" ++
  "78b56aa5d089a156e245000000000000000151722ec92d3d06729e7a010000000000595a")

private def vCrc32 : ByteArray := hex (
  "fd377a585a0000016922de360200210116000000742fe5a3e00071003d5d003a1a08ce76c7e5e9d6" ++
  "0734c3d10ebfce55e1aabde0e48f9801dd8de507549e65255f273a6a7eb4d3490389cdc9a2eb7104" ++
  "78b56aa5d089a156e245000000000000a47f6255000155722a0c41599042990d010000000001595a")

private def vSha256 : ByteArray := hex (
  "fd377a585a00000ae1fb0ca10200210116000000742fe5a3e00071003d5d003a1a08ce76c7e5e9d6" ++
  "0734c3d10ebfce55e1aabde0e48f9801dd8de507549e65255f273a6a7eb4d3490389cdc9a2eb7104" ++
  "78b56aa5d089a156e24500000000000064ecf7ad26244b972ebaae6ef35068a6cb33231b02c697da" ++
  "5e86e95f41fed3bd000171728ceda9a8189b4b9a01000000000a595a")

private def vLc0Lp4 : ByteArray := hex (
  "fd377a585a000004e6d6b4460200210116000000742fe5a3e00071004024003a1ad9d4741edb8736" ++
  "dab2197a019479f6435a84f0f2b12d5b1db1c0a798b550c8e77229e347faa4043c4ff4c234e2e7f8" ++
  "da4ec687344723112b387d2eb3ec0000e8a9af934775f1f000015c7263b783881fb6f37d01000000" ++
  "0004595a")

private def vLc4Pb4 : ByteArray := hex (
  "fd377a585a000004e6d6b4460200210116000000742fe5a3e00071003fb8003a1a08a20308ffad60" ++
  "498117c05dd4f37c067debc76971cec3a00d7c0de7f967f0a6f500cd1a46f91a19823af216bc0b8d" ++
  "5c46d78d42755e3d7dd0fdcce0000000e8a9af934775f1f000015b72a421c2c71fb6f37d01000000" ++
  "0004595a")

private def vStored : ByteArray := hex (
  "fd377a585a000004e6d6b4460200210116000000742fe5a301002782b70eee7f1a5039bef07ec234" ++
  "7f066ed08f5dc7512447e3404300026b6e545594a065685d64c498009ae46eb96cc6654000014028" ++
  "d4524ae51fb6f37d010000000004595a")

private def vEmpty : ByteArray := hex (
  "fd377a585a000004e6d6b446000000001cdf44211fb6f37d010000000004595a")


private def okIs (r : Except XzError ByteArray) (d : ByteArray) : Bool :=
  match r with | .ok x => x == d | .error _ => false
private def isCorrupt (r : Except XzError ByteArray) : Bool :=
  match r with | .error (.corrupt _) => true | _ => false
private def isUnsupported (r : Except XzError ByteArray) : Bool :=
  match r with | .error (.unsupported _) => true | _ => false

/-! ## Reading what liblzma wrote -/

-- the default stream (CRC64), and each other check type
#guard okIs (unxz vDefault) txt
#guard okIs (unxz vNone) txt
#guard okIs (unxz vCrc32) txt
#guard okIs (unxz vSha256) txt
-- the LZMA2 property variants: lc 0 lp 4 pb 0, and lc 4 lp 0 pb 4
#guard okIs (unxz vLc0Lp4) txt
#guard okIs (unxz vLc4Pb4) txt
-- incompressible input is an uncompressed chunk
#guard okIs (unxz vStored) rnd
-- an empty stream has no block
#guard okIs (unxz vEmpty) ByteArray.empty
-- two streams with stream padding between and after them
#guard okIs (unxz (vDefault ++ ByteArray.mk #[0, 0, 0, 0] ++ vNone ++ ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0])) (txt ++ txt)
-- padding that is not a multiple of four bytes
#guard isCorrupt (unxz (vDefault ++ ByteArray.mk #[0, 0, 0]))

/-! ## Damaged files are corrupt -/

private def flip (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)

-- a byte of the compressed data, of the check, of the index, of the footer
#guard isCorrupt (unxz (flip vDefault 40))
#guard isCorrupt (unxz (flip vDefault (vDefault.size - 40)))
#guard isCorrupt (unxz (flip vDefault (vDefault.size - 20)))
#guard isCorrupt (unxz (flip vDefault (vDefault.size - 1)))
-- a flag of the stream header, of the block header, the magic
#guard isCorrupt (unxz (flip vDefault 7))
#guard isCorrupt (unxz (flip vDefault 13))
#guard isCorrupt (unxz (flip vDefault 0))
-- each check type catches a changed byte of the data it protects
#guard isCorrupt (unxz (flip vCrc32 40))
#guard isCorrupt (unxz (flip vSha256 40))
-- truncation, nothing, and text
#guard isCorrupt (unxz (vDefault.extract 0 (vDefault.size - 5)))
#guard isCorrupt (unxz (vDefault.extract 0 20))
#guard isCorrupt (unxz ByteArray.empty)
#guard isCorrupt (unxz "this is not an xz file at all".toUTF8)

/-! ## Reserved features are unsupported, not corrupt -/

private def fixCrc (b : ByteArray) (from' to : Nat) : ByteArray :=
  let c := crc32 (b.extract from' to)
  (b.set! to c.toUInt8).set! (to + 1) (c >>> (8 : UInt32)).toUInt8
    |>.set! (to + 2) (c >>> (16 : UInt32)).toUInt8 |>.set! (to + 3) (c >>> (24 : UInt32)).toUInt8

-- a check type this reader does not have (type 2 is reserved), with the
-- stream header's and the footer's CRC32 corrected to match
#guard isUnsupported (unxz (fixCrc (fixCrc ((vNone.set! 7 2).set! (vNone.size - 3) 2) 6 8) (vNone.size - 8) (vNone.size - 12)))
-- another filter than LZMA2 (0x03 is the delta filter)
#guard isUnsupported (unxz (fixCrc (vDefault.set! 14 0x03) 12 20))

/-! ## Writing -/

-- the empty stream is the one liblzma writes
#guard xz ByteArray.empty == vEmpty
-- what is written is read back, whatever the size: no data, one byte, a
-- text, exactly one chunk, one byte more than a chunk
#guard okIs (unxz (xz ByteArray.empty)) ByteArray.empty
#guard okIs (unxz (xz (ByteArray.mk #[7]))) (ByteArray.mk #[7])
#guard okIs (unxz (xz txt)) txt
private def big (n : Nat) : ByteArray := ByteArray.mk ((List.range n).map (fun i => (i * 7 % 251).toUInt8)).toArray
#guard okIs (unxz (xz (big 65536))) (big 65536)
#guard okIs (unxz (xz (big 65537))) (big 65537)
#guard okIs (unxz (xz (big 140000))) (big 140000)
-- the stream is padded to a multiple of four bytes
#guard (xz txt).size % 4 == 0
#guard (xz (ByteArray.mk #[1])).size % 4 == 0
-- a written stream damaged is corrupt
#guard isCorrupt (unxz (flip (xz txt) 20))
#guard isCorrupt (unxz (flip (xz txt) ((xz txt).size - 30)))

end L4Factoidal.Codec
