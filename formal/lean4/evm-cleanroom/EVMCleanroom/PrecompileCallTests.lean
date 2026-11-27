import EVMCleanroom.CallTransaction
import EVMCleanroom.SecpRecovery

/-!
# Native precompiles through the actual CALL family and transaction frame

Executable guards for the routing added with `Precompiles.run`: the same
decoded caller is run through the public `callStep` adapter and the opcode
dispatcher, for CALL and STATICCALL, and a transaction is sent directly to a
precompile address. The target account deliberately holds INVALID code and a
balance: a precompile address must run the native function, not that code.

These are regression tests of the routing, gas hand-back and failure bit. The
functions themselves are tested in their modules and by the vector runner.
-/

namespace EVMCleanroom.PrecompileCallTests

open World CallOpcode

private def testWorld : TxWorld :=
  { beginTransaction (fun address =>
      if address == 0xc1 then { code := #[0xf1, 0x00], balance := 100 }
      else if address == 0xc2 then { code := #[0xfa, 0x00], balance := 100 }
      else if 1 ≤ address ∧ address ≤ 0x11 then { code := #[0xfe], balance := 1 }
      else {}) with keccakAcceptance := some Keccak.dangerouslyAcceptUnverified }

private def inputMemory : Memory :=
  (Memory.empty.expand 2).copyFrom (ByteView.ofArray #[0x61, 0x62, 0x63]) 0 0 3

/-- CALL(requested, target, value, in 0..size, out 32..64). -/
private def caller (target requested size : Nat) (value : Nat := 0) (profile : Profile := .shanghaiPlus) :
    State :=
  { frameInput testWorld 0xc1 100000 false profile with
    memory := inputMemory
    stack := ⟨[word requested, word target, word value, word 0, word size, word 32, word 32], by simp⟩ }

private def observe (world : TxWorld) (state : State) (target : Nat) :
    Nat × Nat × List Nat × List Nat × Nat × Nat :=
  (state.gas, state.returnData.size, state.stack.items.map (·.val),
    (List.range 4).map (fun i => (state.memory.readByte (32 + i)).toNat),
    (world.accounts 0xc1).balance, (world.accounts target).balance)

private def single (target requested size : Nat) (value : Nat := 0) (profile : Profile := .shanghaiPlus) :=
  match callStep 20 testWorld 0xc1 (caller target requested size value profile) with
  | .committed world state => some (observe world state target)
  | _ => none

private def dispatched (target requested size : Nat) (value : Nat := 0)
    (profile : Profile := .shanghaiPlus) :=
  match execute 20 testWorld 0xc1 (caller target requested size value profile) with
  | .stopped world state => some (observe world state target)
  | _ => none

-- SHA-256("abc") = ba7816bf…; 72 gas for one word. 100000 − 100 (warm access) − 72.
#guard single 2 72 3 == some (99828, 32, [1], [0xba, 0x78, 0x16, 0xbf], 100, 1)
#guard dispatched 2 72 3 == single 2 72 3
-- Unused forwarded gas returns to the caller.
#guard single 2 1000 3 == single 2 72 3
-- One gas short: failure bit, forwarded gas lost, output window untouched, no return data.
#guard single 2 71 3 == some (99829, 0, [0], [0, 0, 0, 0], 100, 1)
#guard dispatched 2 71 3 == single 2 71 3
-- RIPEMD-160("abc") = 8eb208f7… left-padded to 32 bytes; 720 gas.
#guard single 3 720 3 == some (99180, 32, [1], [0, 0, 0, 0], 100, 1)
#guard dispatched 3 719 3 == some (99181, 0, [0], [0, 0, 0, 0], 100, 1)
-- A value transfer to a precompile is kept on success and undone on failure.
#guard (single 2 0 3 1).map (fun r => (r.2.2.1, r.2.2.2.2)) == some ([1], 99, 2)
#guard (single 2 0 3 1) == dispatched 2 0 3 1
-- BLAKE2f with malformed (3-byte) input fails at any gas.
#guard single 9 50000 3 == some (49900, 0, [0], [0, 0, 0, 0], 100, 1)
-- MODEXP with a 3-byte input: declared lengths 0x616263…, unaffordable.
#guard (single 5 50000 3).map (·.2.2.1) == some [0]
-- ECRECOVER with garbage succeeds with empty output for 3000 gas.
#guard single 1 3000 3 == some (96900, 0, [1], [0, 0, 0, 0], 100, 1)
#guard single 1 2999 3 == some (96901, 0, [0], [0, 0, 0, 0], 100, 1)

-- Fork gating: 0x0a and above remain refused under the pre-Cancun profile, and
-- addresses that are reserved but not implemented remain refused everywhere.
#guard (match callStep 20 testWorld 0xc1 (caller 0x0a 50000 3) with
  | .indeterminate .unsupportedFork => true | _ => false)
#guard (match execute 20 testWorld 0xc1 (caller 0x0b 50000 3) with
  | .indeterminate .unsupportedFork => true | _ => false)
#guard unimplementedPrecompile .shanghaiPlus 0x0a && unimplementedPrecompile .shanghaiPlus 0x11
#guard !unimplementedPrecompile .shanghaiPlus 2 && !unimplementedPrecompile .shanghaiPlus 4
#guard !unimplementedPrecompile .shanghaiPlus 0x12 && !unimplementedPrecompile .cancunPlus 0x0b
-- Osaka prices MODEXP by EIP-7883: the empty call costs 500, not 200.
#guard (single 5 500 0 0 .osaka).map (·.2.2.1) == some [1]
#guard (single 5 499 0 0 .osaka).map (·.2.2.1) == some [0]
#guard (single 5 200 0).map (·.2.2.1) == some [1]
#guard (single 5 199 0).map (·.2.2.1) == some [0]

-- Without the Keccak opt-in ECRECOVER is refused (indeterminate), like the KECCAK256 opcode.
#guard (match callStep 20 { testWorld with keccakAcceptance := none } 0xc1
    { caller 1 3000 3 with keccakAcceptance := none } with
  | .indeterminate .unsupportedFork => true | _ => false)

-- STATICCALL reaches the same native function.
private def staticCaller (target requested size : Nat) : State :=
  { frameInput testWorld 0xc2 100000 with
    memory := inputMemory
    stack := ⟨[word requested, word target, word 0, word size, word 32, word 32], by simp⟩ }

#guard (match execute 20 testWorld 0xc2 (staticCaller 2 72 3) with
  | .stopped _ state =>
    state.stack.items.map (·.val) == [1] && state.returnData.size == 32 &&
      (state.memory.readByte 32).toNat == 0xba && state.gas == 99828
  | _ => false)

-- A local input-size refusal stays indeterminate.
private def oversized : State :=
  { frameInput testWorld 0xc1 1000000000 with
    stack := ⟨[word 100000000, word 2, word 0, word 0,
      word (Precompiles.maxInputBytes + 1), word 0, word 0], by decide⟩ }

#guard (match callStep 20 testWorld 0xc1 oversized with
  | .indeterminate .resourceLimit => true | _ => false)

-- The shared Jacobian secp256k1 module and the affine transaction-admission module recover
-- the same public key (low-s signatures, both parities; the affine code rejects high s).
private def sameKey (z parity r s : Nat) : Bool :=
  match SecpRecovery.recoverPoint SecpRecovery.dangerouslyAcceptUnverified z parity r s,
      Precompiles.Secp256k1.recover z parity r s with
  | .ok (.affine x y), some (x', y') => x == x' && y == y'
  | _, _ => false

#guard sameKey 0x18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c 0
  0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f
  (Precompiles.Secp256k1.n - 0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549)
-- A signature made here: key d = 7, nonce k = 11, hash z = 12345 (r = ([k]G).x, s = (z + r d)/k).
private def madeR : Nat := ((Precompiles.Secp256k1.mulBase 11).map (·.1)).getD 0 % Precompiles.Secp256k1.n
private def madeS : Nat :=
  (12345 + madeR * 7) % Precompiles.Secp256k1.n * Precompiles.Secp256k1.scalarInv 11 % Precompiles.Secp256k1.n
private def madeLowS : Nat := min madeS (Precompiles.Secp256k1.n - madeS)
#guard (sameKey 12345 0 madeR madeLowS || sameKey 12345 1 madeR madeLowS)
#guard [0, 1].any fun parity =>
  Precompiles.Secp256k1.recover 12345 parity madeR madeS == Precompiles.Secp256k1.mulBase 7

end EVMCleanroom.PrecompileCallTests

namespace EVMCleanroom.CallTransaction

private def shaRequest (gas : Nat) (bytes : Array UInt8) : Request :=
  { fork := .shanghai, fuel := 0
    tx := {
      kind := 2, signedChainId := some 1, sender := 0x1000, to := 2
      nonce := 0, value := 3, gasLimit := gas, gasPriceCap := 2, priorityFeeCap := 1
      data := bytes, accessList := [] }
    block := {
      chainId := 1, coinbase := 0xc4, number := 19000000, timestamp := 1706000000
      gasLimit := 30000000, gasUsedBefore := 0, baseFee := 1, prevRandao := 0, blobBaseFee := 0 }
    witnesses := [
      { address := 0x1000, present := true, balance := 1000000, nonce := 0, code := #[], storage := [] },
      { address := 2, present := true, balance := 7, nonce := 0, code := #[0xfe], storage := [] },
      { address := 0xc4, present := false, balance := 0, nonce := 0, code := #[], storage := [] }] }

-- Intrinsic 21000 + 3 nonzero data bytes (48) + 72 for SHA-256 of one word.
#guard match run (shaRequest 21120 #[0x61, 0x62, 0x63]) with
  | .executed out =>
    out.receiptStatus && out.charge.used == 21120 && out.output.size == 32 &&
    (out.output.readByte 0).toNat == 0xba && (out.output.readByte 31).toNat == 0xad &&
    (out.world.accounts 2).balance == 10
  | _ => false
#guard match run (shaRequest 21119 #[0x61, 0x62, 0x63]) with
  | .executed out =>
    !out.receiptStatus && out.charge.used == 21119 && out.output.size == 0 &&
    (out.world.accounts 2).balance == 7 &&
    (match out.frame with | .exceptional .outOfGas => true | _ => false)
  | _ => false

end EVMCleanroom.CallTransaction
