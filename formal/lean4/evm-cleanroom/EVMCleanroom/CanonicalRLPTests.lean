import EVMCleanroom.CanonicalRLP

/-! Local boundary regressions for #1043. These guards are tests, not proofs of
the RLP grammar. The native suite separately exercises published RLP fixtures
and independent encoding/decoding oracles. -/
namespace EVMCleanroom.CanonicalRLP.Tests

private def accepted (raw : Array UInt8) : Bool :=
  match decode raw with
  | .ok _ => true
  | .error _ => false

private def resourceRefused (raw : Array UInt8) : Bool :=
  match decode raw with
  | .error .resourceLimit => true
  | _ => false

private def integer (raw : Array UInt8) (maxBytes : Nat) : Except Error Nat := do
  let item ← decode raw
  scalar item maxBytes

private def immediateBytes (raw : Array UInt8) : Except Error (Array (Array UInt8)) := do
  let item ← decode raw
  let entries ← children item
  return entries.map (·.encoded)

private def sameResult [BEq α] (actual expected : Except Error α) : Bool :=
  match actual, expected with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-- Test-only single-child list encoding, bounded here to at most 65 layers and
one-byte length-of-length. It is not used by the decoder or witness checker. -/
private def wrapLists : Nat → Array UInt8 → Array UInt8
  | 0, bytes => bytes
  | n + 1, bytes =>
    let wrapped := if bytes.size < 56 then #[UInt8.ofNat (192 + bytes.size)] ++ bytes
      else #[248, UInt8.ofNat bytes.size] ++ bytes
    wrapLists n wrapped

#guard accepted #[0]
#guard accepted #[127]
#guard accepted #[128]
#guard accepted #[192]
#guard !accepted #[]
#guard !accepted #[128, 128]
#guard !accepted #[129, 0]
#guard !accepted #[184, 1, 128]
#guard !accepted #[185, 0, 56]
#guard !accepted #[194, 129, 0]
#guard !accepted #[193, 130]
#guard !accepted #[255, 255, 255, 255, 255, 255, 255, 255, 255]
#guard sameResult (integer #[128] 32) (.ok 0)
#guard sameResult (integer #[1] 32) (.ok 1)
#guard sameResult (integer #[0] 32) (.error (.malformed "nonminimal integer"))
#guard sameResult (integer #[130, 0, 1] 32) (.error (.malformed "nonminimal integer"))
#guard sameResult (integer #[130, 1, 0] 1) (.error (.malformed "integer width"))
#guard sameResult (integer #[192] 32) (.error (.malformed "expected integer bytes"))
#guard sameResult (immediateBytes #[195, 193, 128, 1]) (.ok #[#[193, 128], #[1]])
#guard accepted (wrapLists 64 #[0])
#guard resourceRefused (wrapLists 65 #[0])
#guard resourceRefused (Array.replicate 4097 0)

end EVMCleanroom.CanonicalRLP.Tests
