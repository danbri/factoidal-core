import EVMCleanroom.Precompiles.Secp256k1
import EVMCleanroom.Keccak

/-!
# ECRECOVER (precompile 0x01)

Input is read as four 32-byte big-endian words `hash, v, r, s` (zero-padded on
the right; bytes beyond 128 are ignored). The call always costs 3000 gas. It
returns the 20-byte address left-padded to 32 bytes, or empty output when `v`
is not 27 or 28, `r` or `s` is outside `[1, n-1]`, `r` is not the abscissa of
a curve point, or the recovered key is the point at infinity. Unlike
transaction signatures (EIP-2), a high `s` is accepted here, as in the Yellow
Paper and EELS.

Key recovery is `Secp256k1.recover` from the shared curve module. The address
is the Keccak-256 of the 64-byte public key, so the precompile needs the
repository's explicit Keccak opt-in, like the KECCAK256 opcode.

Proved: gas accounting, output length, that only the first 128 input bytes
matter. Tested, not proved: the recovered address (published vectors, and
agreement with the affine `SecpRecovery` in `PrecompileCallTests.lean`).
-/

namespace EVMCleanroom.Precompiles.Ecrecover

open Secp256k1 (recover n)

def gasCost : Nat := 3000

private def view (b : ByteArray) : ByteView := { size := b.size, raw := fun i => byteAt b i }

/-- Keccak-256 of the 64-byte public key, with the first 12 bytes cleared. -/
def addressBytes (x y : Nat) : ByteArray :=
  let digest := Keccak.digest (view (natToBE 32 x ++ natToBE 32 y))
  natToBE 32 (digest.toArray.foldl (fun acc byte => acc * 256 + byte.toNat) 0 % 2 ^ 160)

def body (data : ByteArray) : Body :=
  let v := beNat data 32 32
  if v ≠ 27 ∧ v ≠ 28 then .output ByteArray.empty
  else
    match recover (beNat data 0 32) (v - 27) (beNat data 64 32) (beNat data 96 32) with
    | none => .output ByteArray.empty
    | some (x, y) => .output (addressBytes x y)

/-- Precompile 0x01. The acceptance token is the Keccak opt-in of the caller. -/
def run (_ : Keccak.Acceptance) (gas : Nat) (input : ByteArray) : Result :=
  charge gas gasCost fun _ => body (readPadded input 0 128)

/-- Kind: gas admission.
    Says: with less than 3000 gas the call fails, whatever the input.
    Does not say: anything about the signature. -/
theorem run_underfunded (a : Keccak.Acceptance) (gas : Nat) (input : ByteArray) (h : gas < 3000) :
    run a gas input = .failure :=
  charge_underfunded _ _ _ h

/-- Kind: output contract.
    Says: the body always produces output (never an invalid or refused result), and that
    output is empty or exactly 32 bytes.
    Does not say: which case applies. -/
theorem body_output (data : ByteArray) :
    ∃ out, body data = .output out ∧ (out.size = 0 ∨ out.size = 32) := by
  unfold body
  simp only
  split
  · exact ⟨_, rfl, Or.inl rfl⟩
  · split
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr (natToBE_size _ _)⟩

/-- Kind: output contract and accounting.
    Says: with at least 3000 gas the call always succeeds, costs exactly 3000, and returns
    either no bytes or exactly 32 bytes. There is no failing input.
    Does not say: that 32 bytes are returned exactly for valid signatures (tested). -/
theorem run_funded (a : Keccak.Acceptance) (gas : Nat) (input : ByteArray) (h : 3000 ≤ gas) :
    ∃ out, run a gas input = .success out (gas - 3000) ∧ (out.size = 0 ∨ out.size = 32) := by
  have ⟨out, hBody, hSize⟩ := body_output (readPadded input 0 128)
  exact ⟨out, charge_funded gas gasCost _ out h hBody, hSize⟩

/-- Kind: input-length handling.
    Says: the result depends only on the first 128 bytes, zero-padded.
    Does not say: anything about what those bytes mean. -/
theorem run_reads_prefix (a : Keccak.Acceptance) (gas : Nat) (x y : ByteArray)
    (h : readPadded x 0 128 = readPadded y 0 128) : run a gas x = run a gas y := by
  simp [run, h]

private def accept : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

private def call (gas : Nat) (input : String) : String :=
  match run accept gas (hex input) with
  | .success out left => toHex out ++ ":" ++ toString left
  | .failure => "failure"
  | .refusal => "refusal"

private def sh : String := "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c"
private def sv : String := "000000000000000000000000000000000000000000000000000000000000001c"
private def sr : String := "73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f"
private def ss : String := "eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549"
private def w (v : Nat) : String := toHex (natToBE 32 v)
private def expected : String := "000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"

#guard call 3000 (sh ++ sv ++ sr ++ ss) == expected ++ ":0"
#guard call 2999 (sh ++ sv ++ sr ++ ss) == "failure"
-- Bytes beyond 128 are ignored; a short input is zero-padded (and then has v = 0).
#guard call 3000 (sh ++ sv ++ sr ++ ss ++ "ffff") == expected ++ ":0"
#guard call 3001 sh == ":1"
#guard call 3000 "" == ":0"
-- v must be exactly 27 or 28 as a 256-bit number.
#guard call 3000 (sh ++ "010000000000000000000000000000000000000000000000000000000000001c" ++ sr ++ ss) == ":0"
#guard call 3000 (sh ++ w 29 ++ sr ++ ss) == ":0"
-- r = 0, s = 0, r = n and s = n are rejected.
#guard call 3000 (sh ++ sv ++ w 0 ++ ss) == ":0"
#guard call 3000 (sh ++ sv ++ sr ++ w 0) == ":0"
#guard call 3000 (sh ++ sv ++ w n ++ ss) == ":0"
#guard call 3000 (sh ++ sv ++ sr ++ w n) == ":0"
-- High s is accepted by the precompile: (r, n - s) with the other parity recovers the same key.
#guard call 3000 (sh ++ w 27 ++ sr ++ w (n - beNat (hex ss) 0 32)) == expected ++ ":0"
#guard n / 2 < n - beNat (hex ss) 0 32 || n / 2 < beNat (hex ss) 0 32

#print axioms run_underfunded
#print axioms body_output
#print axioms run_funded
#print axioms run_reads_prefix

end EVMCleanroom.Precompiles.Ecrecover
