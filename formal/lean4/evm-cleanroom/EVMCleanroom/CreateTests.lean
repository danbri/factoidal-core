import EVMCleanroom.CallOpcode
import EVMCleanroom.CanonicalRLP

/-! Executable regression guards for CREATE and CREATE2: address derivation,
the CREATE preimage read back by the repository's canonical RLP decoder, and
runs through the actual world-aware dispatcher. These are tests, not proofs. -/

namespace EVMCleanroom.CreateTests

open World CallOpcode

private def accept : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

-- Published CREATE vectors (sender 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0, nonces 0 to 3).
#guard Create.createAddress accept 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 0 == 0xcd234a471b72ba2f1ccf0a70fcaba648a5eecd8d
#guard Create.createAddress accept 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 1 == 0x343c43a37d37dff08ae8c4a11544c718abb4fcf8
#guard Create.createAddress accept 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 2 == 0xf778b86fa74e846c4f0a1fbd1335fe81c00a0c91
#guard Create.createAddress accept 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 3 == 0xfffd933a0bc612844eaf0c6fe3e5b8e9b6c1d19c
-- EIP-1014 examples 1, 2 and 4.
#guard Create.create2Address accept 0 0 (ByteView.ofArray #[0x00]) == 0x4D1A2e2bB4F88F0250f26Ffff098B0b30B26BF38
#guard Create.create2Address accept 0xdeadbeef00000000000000000000000000000000 0 (ByteView.ofArray #[0x00]) ==
  0xB928f69Bb1D91Cd65274e3c79d8986362984fDA3
#guard Create.create2Address accept 0 0 (ByteView.ofArray #[0xde, 0xad, 0xbe, 0xef]) ==
  0x70f2b2914A2a4b783FaEFb75f459A580616Fcb5e
#guard Create.create2Address accept 0 0 (ByteView.ofArray #[]) == 0xE33C0C7F7df4809055C3ebA6c09CFe4BaF1BD9e0

/-- The canonical decoder reads the CREATE preimage back as a two-item list:
    20 sender bytes and the minimal nonce. -/
private def decodesTo (sender nonce : Nat) : Bool :=
  match CanonicalRLP.decode (Create.rlpSenderNonce sender nonce).toArray with
  | .ok item =>
    match CanonicalRLP.children item with
    | .ok items =>
      items.size == 2 &&
      (match items[0]? with
        | some first => !first.isList && first.payload.toList == Create.fixedBytes 20 sender
        | none => false) &&
      (match items[1]? with
        | some second => (match CanonicalRLP.scalar second 8 with | .ok n => n == nonce | .error _ => false)
        | none => false)
    | .error _ => false
  | .error _ => false

#guard [0, 1, 0x7f, 0x80, 0xff, 0x100, 0xffff, 0x10000, 2 ^ 32, 2 ^ 56 - 1, 2 ^ 56, 2 ^ 64 - 2, 2 ^ 64 - 1].all
  (decodesTo 0xc1)
#guard decodesTo 0 0 && decodesTo (2 ^ 160 - 1) 5 && decodesTo 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 300

private def padRight (bytes : List UInt8) (n : Nat) : List UInt8 :=
  bytes ++ List.replicate (n - bytes.length) 0

/-- Write `code` into memory from offset 0 with PUSH32/MSTORE. -/
private def store (code : List UInt8) : List UInt8 :=
  (List.range ((code.length + 31) / 32)).flatMap fun i =>
    [0x7f] ++ padRight ((code.drop (32 * i)).take 32) 32 ++ [0x60, UInt8.ofNat (32 * i), 0x52]

private def returning (runtime : List UInt8) : List UInt8 :=
  store runtime ++ [0x60, UInt8.ofNat runtime.length, 0x5f, 0xf3]

private def deploy (init : List UInt8) (value : UInt8 := 0) : List UInt8 :=
  store init ++ [0x60, UInt8.ofNat init.length, 0x5f, 0x60, value, 0xf0]

private def deploy2 (init : List UInt8) (salt : UInt8) : List UInt8 :=
  store init ++ [0x60, salt, 0x60, UInt8.ofNat init.length, 0x5f, 0x5f, 0xf5]

private def runtime : List UInt8 := [0x60, 1, 0x60, 0, 0x55, 0x00]
private def revertInit : List UInt8 := store [0xde, 0xad] ++ [0x60, 2, 0x5f, 0xfd]
private def efInit : List UInt8 := [0x60, 0xef, 0x5f, 0x53, 0x60, 1, 0x5f, 0xf3]

private def creator : Nat := 0xc1
/-- `generateAddress(0xc1, 1)` as computed by the differential oracle. -/
private def first : Nat := 0xe0b7449f26b95a39b953d1221d1bd325e6d9cf21

#guard Create.createAddress accept creator 1 == first

private def world (code : List UInt8) (target : Account := {}) (keccak : Bool := true)
    (witnessed : Option WitnessCoverage := none) : TxWorld :=
  { beginTransaction (fun a =>
      if a == creator then { balance := 1000, nonce := 1, code := code.toArray }
      else if a == first then target else {}) with
    keccakAcceptance := if keccak then some accept else none
    witnessed }

private def run (w : TxWorld) (gas : Nat := 400000) (readOnly : Bool := false)
    (profile : Profile := .cancunPlus) (depth : Nat := 0) : CallOpcode.Outcome :=
  let s := frameInput w creator gas readOnly profile 0xc2 0xc2
  settle w s (executeAtDepth 2000 w creator depth s)

private def bytes (view : ByteView) : List UInt8 := (List.range view.size).map view.readByte

-- Success: the address is pushed, the code deposited, both nonces set, the
-- account marked created and warm, the last-child buffer empty.
#guard match run (world (deploy (returning runtime) 7)) with
  | .stopped out s =>
    s.stack.items.map (·.val) == [first] && (out.accounts first).code.toList == runtime &&
    (out.accounts first).nonce == 1 && (out.accounts first).balance == 7 &&
    (out.accounts creator).nonce == 2 && (out.accounts creator).balance == 993 &&
    out.created first && !out.created creator && out.warmAddresses first && s.returnData.size == 0
  | _ => false

-- Empty initcode: exactly three PUSH0-class pushes (2 + 2 + 3) and 32000 gas.
#guard match run (world [0x5f, 0x5f, 0x60, 0, 0xf0]) with
  | .stopped out s => s.gas == 400000 - 7 - 32000 && s.stack.items.map (·.val) == [first] &&
      (out.accounts first).nonce == 1 && (out.accounts first).code.size == 0
  | _ => false

-- Revert: zero pushed, data returned, checkpoint keeps only nonce and warmth.
#guard match run (world (deploy revertInit 7)) with
  | .stopped out s =>
    s.stack.items.map (·.val) == [0] && bytes s.returnData == [0xde, 0xad] &&
    (out.accounts first).nonce == 0 && (out.accounts first).balance == 0 &&
    (out.accounts creator).nonce == 2 && (out.accounts creator).balance == 1000 &&
    !out.created first && out.warmAddresses first
  | _ => false

-- Exceptional initcode and a 0xEF deposit: no data, no child gas.
#guard [[0xfe], efInit].all fun init =>
  match run (world (deploy init)) with
  | .stopped out s =>
    s.stack.items.map (·.val) == [0] && s.returnData.size == 0 && s.gas < 400000 / 64 &&
    (out.accounts first).code.size == 0 && (out.accounts creator).nonce == 2 && !out.created first
  | _ => false

-- Collisions (code, nonce, storage statement): nonce bumped, child gas consumed.
#guard [({ code := #[0] } : Account), { nonce := 1 }, { hasStorage := true }].all fun target =>
  match run (world (deploy (returning runtime)) target) with
  | .stopped out s =>
    s.stack.items.map (·.val) == [0] && s.gas < 400000 / 64 && (out.accounts creator).nonce == 2 &&
    (out.accounts first).nonce == target.nonce && (out.accounts first).code == target.code &&
    out.warmAddresses first && !out.created first
  | _ => false

-- A balance alone is no collision: it is kept and the endowment added.
#guard match run (world (deploy (returning runtime) 7) { balance := 9 }) with
  | .stopped out s => s.stack.items.map (·.val) == [first] && (out.accounts first).balance == 16
  | _ => false

-- Soft failures: endowment above the balance, and entry depth 1024.
#guard match run (world (store runtime ++ [0x60, 6, 0x5f, 0x61, 0x03, 0xe9, 0xf0])) with
  | .stopped out s => s.stack.items.map (·.val) == [0] && (out.accounts creator).nonce == 1 &&
      !out.warmAddresses first && s.gas > 300000
  | _ => false
#guard match run (world (deploy (returning runtime))) (depth := 1024) with
  | .stopped out s => s.stack.items.map (·.val) == [0] && (out.accounts creator).nonce == 1 &&
      !out.warmAddresses first
  | _ => false
#guard match run (world (deploy (returning runtime))) (depth := 1023) with
  | .stopped _ s => s.stack.items.map (·.val) == [first]
  | _ => false

-- Static frame, EIP-3860 size limit (49153 = 0xc001) and underflow are exceptional.
#guard match run (world (deploy [0x00])) (readOnly := true) with
  | .exceptional _ _ .writeProtection => true
  | _ => false
#guard match run (world [0x61, 0xc0, 0x01, 0x5f, 0x5f, 0xf0]) (gas := 2000000) with
  | .exceptional _ _ .outOfGas => true
  | _ => false
#guard match run (world [0x61, 0xc0, 0x00, 0x5f, 0x5f, 0xf0]) (gas := 2000000) with
  | .stopped _ s => s.stack.items.map (·.val) == [first]
  | _ => false
#guard match run (world [0x5f, 0x5f, 0xf0]) with
  | .exceptional _ _ .stackUnderflow => true
  | _ => false

-- CREATE2: the address of the formula, and a second use of the salt collides.
#guard match run (world (deploy2 (returning runtime) 9 ++ deploy2 (returning runtime) 9)) with
  | .stopped out s =>
    let target := Create.create2Address accept creator 9 (ByteView.ofArray (returning runtime).toArray)
    s.stack.items.map (·.val) == [0, target] && (out.accounts target).code.toList == runtime &&
    (out.accounts creator).nonce == 3 && out.created target
  | _ => false

-- Refusals: pre-Shanghai profile, no Keccak opt-in, uncovered new address.
#guard match run (world [0x60, 0, 0x60, 0, 0x60, 0, 0xf0]) (profile := .preShanghai) with
  | .indeterminate .unsupportedFork => true
  | _ => false
#guard match run (world (deploy [0x00]) (keccak := false)) with
  | .indeterminate .unsupportedFork => true
  | _ => false
#guard match run (world (deploy [0x00]) (witnessed := some ⟨fun a => a == creator, fun _ _ => false⟩)) with
  | .indeterminate (.incompleteState address none) => address == first
  | _ => false
-- A covered new account may use its own (empty) storage without slot witnesses.
#guard match run (world (deploy [0x60, 5, 0x60, 1, 0x55, 0x00])
    (witnessed := some ⟨fun a => a == creator || a == first, fun _ _ => false⟩)) with
  | .stopped out s => s.stack.items.map (·.val) == [first] && (out.accounts first).storage 1 == 5
  | _ => false

end EVMCleanroom.CreateTests
