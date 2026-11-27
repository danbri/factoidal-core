import EVMCleanroom.Precompiles.Basic
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.SHA2Theorems

/-!
# SHA-256 (precompile 0x02)

The hash itself is the repository's pure `L4Factoidal.Crypto.SHA2` (FIPS
180-4), shared by source with the consensus package; it imports nothing
beyond `Init`. This module adds only the precompile contract.

Gas (Yellow Paper appendix E, EELS `sha256`): 60 + 12 per 32-byte word.
-/

namespace EVMCleanroom.Precompiles.Sha256

def digest (m : ByteArray) : ByteArray := L4Factoidal.Crypto.sha256 m

def gasCost (size : Nat) : Nat := 60 + 12 * words32 size

/-- Precompile 0x02. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  charge gas (gasCost input.size) fun _ => .output (digest input)

/-- Kind: output contract.
    Says: every successful call returns exactly 32 bytes and the exact unspent gas.
    Does not say: the bytes are the SHA-256 of the input (FIPS vectors, not proved). -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) :
    out.size = 32 ∧ left + gasCost input.size = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  have hEq : digest input = out := Body.output.inj hBody
  exact ⟨hEq ▸ L4Factoidal.Crypto.sha256_size input, hGas⟩

/-- Kind: gas admission.
    Says: the call fails exactly when the forwarded gas is below 60 + 12 per word;
    otherwise it succeeds. There is no invalid input.
    Does not say: anything about the digest. -/
theorem run_total (gas : Nat) (input : ByteArray) :
    (gas < gasCost input.size → run gas input = .failure) ∧
    (gasCost input.size ≤ gas → ∃ out, run gas input = .success out (gas - gasCost input.size)) := by
  constructor
  · intro h; exact charge_underfunded _ _ _ h
  · intro h; exact ⟨_, charge_funded _ _ _ _ h rfl⟩

#guard toHex (digest ByteArray.empty) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard toHex (digest "abc".toUTF8) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard gasCost 0 == 60 && gasCost 1 == 72 && gasCost 32 == 72 && gasCost 33 == 84
#guard (match run 60 ByteArray.empty with | .success out 0 => out.size == 32 | _ => false)
#guard (match run 59 ByteArray.empty with | .failure => true | _ => false)

#print axioms run_success
#print axioms run_total

end EVMCleanroom.Precompiles.Sha256
