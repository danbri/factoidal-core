import EVMCleanroom.Core
import EVMCleanroom.Precompiles.Sha256
import EVMCleanroom.Precompiles.Ripemd160
import EVMCleanroom.Precompiles.Blake2f
import EVMCleanroom.Precompiles.ModExp
import EVMCleanroom.Precompiles.Ecrecover
import EVMCleanroom.Precompiles.BN254
import EVMCleanroom.Precompiles.BN254Fast
import EVMCleanroom.Precompiles.BLS12381
import EVMCleanroom.Precompiles.BLS12381Msm
import EVMCleanroom.Precompiles.KZG
import EVMCleanroom.Precompiles.P256

/-!
# Precompiled contracts: fork gating and the single entry used by CALL

`run` is the one function the CALL family (`CallOpcode.precompileStep`) and the
transaction frame (`CallTransaction.runFrame`) use for every precompile other
than identity (0x04), which keeps its own module and theorems.

Fork gating follows the opcode profiles of `Core`, which are coarser than
forks:

* `preShanghai`, `shanghaiPlus`: 0x01–0x09 with Berlin pricing (EIP-2565
  for 0x05, EIP-1108 for 0x06–0x08). `shanghaiPlus` cannot tell Shanghai from
  later forks, so 0x0a–0x11 stay refused there, as before;
* `cancunPlus`: adds 0x0a (EIP-4844);
* `osaka`: adds 0x0b–0x11 (EIP-2537) and 0x100 (P256VERIFY, EIP-7951), and prices
  0x05 by EIP-7883 with the EIP-7823 length bound.
  There is no separate Prague profile, so the EIP-2537 set is reachable only here.

An address that is reserved in a profile but not implemented here is refused
by the caller as before (`unsupportedFork`, an indeterminate result). It is
never executed as an empty account.

Input is materialised once, after a size check against `maxInputBytes`, a
local bound shared with the identity precompile.
-/

namespace EVMCleanroom.Precompiles

/-- Local input bound. Not an Ethereum rule. -/
def maxInputBytes : Nat := 1_048_576

/-- Precompile addresses with an implementation in this module. -/
def implemented (address : Nat) : Bool :=
  address == 1 || address == 2 || address == 3 || (5 ≤ address && address ≤ 0x11) || address == 0x100

/-- Highest precompile address a profile executes. -/
def lastAddress : Profile → Nat
  | .preShanghai => 0x09
  | .shanghaiPlus => 0x09
  | .cancunPlus => 0x0a
  | .osaka => 0x11

/-- Does this profile execute `address` through `run`? -/
def active (profile : Profile) (address : Nat) : Bool :=
  implemented address &&
    (decide (address ≤ lastAddress profile) || (address == 0x100 && profile == .osaka))

def modexpRule : Profile → ModExp.Rule
  | .osaka => .eip7883
  | _ => .eip2565

def materializeLoop (view : ByteView) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n+1, i, acc => materializeLoop view n (i + 1) (acc.push (view.readByte i))

/-- The bytes of a view; called only after the size check. -/
def materialize (view : ByteView) : ByteArray :=
  materializeLoop view view.size 0 ByteArray.empty

theorem materializeLoop_size (view : ByteView) (n i : Nat) (acc : ByteArray) :
    (materializeLoop view n i acc).size = acc.size + n := by
  induction n generalizing i acc with
  | zero => simp [materializeLoop]
  | succ n ih => simp [materializeLoop, ih, ByteArray.size_push]; omega

/-- Kind: length.
    Says: materialising a view yields exactly `size` bytes.
    Does not say: which bytes. -/
theorem materialize_size (view : ByteView) : (materialize view).size = view.size := by
  simp [materialize, materializeLoop_size]

def viewOf (bytes : ByteArray) : ByteView :=
  { size := bytes.size, raw := fun i => byteAt bytes i }

/-- The implementation behind an address; `none` when it is not available
    (not implemented, or ECRECOVER without the Keccak opt-in). -/
def dispatch (profile : Profile) (keccak : Option Keccak.Acceptance) (address gas : Nat)
    (input : ByteArray) : Option Result :=
  match address with
  | 1 => keccak.map fun acceptance => Ecrecover.run acceptance gas input
  | 2 => some (Sha256.run gas input)
  | 3 => some (Ripemd160.run gas input)
  | 5 => some (ModExp.run (modexpRule profile) gas input)
  | 6 => some (BN254.Fast.runAdd gas input)
  | 7 => some (BN254.Fast.runMul gas input)
  | 8 => some (BN254.runPairing gas input)
  | 9 => some (Blake2f.run gas input)
  | 0x0a => some (KZG.run gas input)
  | 0x0b => some (BLS12381.Fast.runG1Add gas input)
  | 0x0c => some (BLS12381.Fast.runG1Msm gas input)
  | 0x0d => some (BLS12381.Fast.runG2Add gas input)
  | 0x0e => some (BLS12381.Fast.runG2Msm gas input)
  | 0x0f => some (BLS12381.runPairing gas input)
  | 0x10 => some (BLS12381.runMapG1 gas input)
  | 0x11 => some (BLS12381.runMapG2 gas input)
  | 0x100 => some (P256.run gas input)
  | _ => none

/-- Run a precompile on a call's input view with the forwarded gas.
    `.error .outOfGas` stands for every exceptional halt of the precompile
    frame (too little gas or invalid input): the caller loses the forwarded
    gas either way. `.error .resourceLimit` and `.error .unsupportedFork`
    are refusals of this implementation, not Ethereum results. -/
def run (profile : Profile) (keccak : Option Keccak.Acceptance) (address gas : Nat)
    (input : ByteView) : Except Error (ByteView × Nat) :=
  if !active profile address then .error .unsupportedFork
  else if input.size > maxInputBytes then .error .resourceLimit
  else
    match dispatch profile keccak address gas (materialize input) with
    | none => .error .unsupportedFork
    | some (.success output left) => .ok (viewOf output, left)
    | some .failure => .error .outOfGas
    | some .refusal => .error .resourceLimit

/-- Kind: fork gating.
    Says: an address the profile does not execute is refused, never answered.
    Does not say: which addresses a real fork has (see the table above). -/
theorem run_inactive (profile : Profile) (keccak : Option Keccak.Acceptance) (address gas : Nat)
    (input : ByteView) (h : active profile address = false) :
    run profile keccak address gas input = .error .unsupportedFork := by
  simp [run, h]

/-- Kind: local bound.
    Says: input above the local size bound is refused before any byte is read.
    Does not say: Ethereum has this limit. -/
theorem run_oversize (profile : Profile) (keccak : Option Keccak.Acceptance) (address gas : Nat)
    (input : ByteView) (hActive : active profile address = true) (h : maxInputBytes < input.size) :
    run profile keccak address gas input = .error .resourceLimit := by
  simp [run, hActive, h]

/-- Kind: fork gating.
    Says: no profile executes address zero or an address above 0x11 through this entry,
    except 0x100 under `osaka`; the pre-Cancun profiles execute nothing above 0x09 and
    `cancunPlus` nothing above 0x0a.
    Does not say: the lower addresses are all implemented (`implemented` lists them). -/
theorem active_range (profile : Profile) (address : Nat) (h : active profile address = true) :
    1 ≤ address ∧ (address ≤ 0x11 ∨ (address = 0x100 ∧ profile = .osaka)) ∧
      ((profile = .preShanghai ∨ profile = .shanghaiPlus) → address ≤ 0x09) ∧
      (profile = .cancunPlus → address ≤ 0x0a) := by
  simp only [active, implemented, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  cases profile <;> simp [lastAddress] at h ⊢ <;> omega

/-- Kind: accounting.
    Says: a successful precompile never returns more gas than was forwarded.
    Does not say: the charge equals the specification's price (per-module theorems and vectors). -/
theorem run_gas_le (profile : Profile) (keccak : Option Keccak.Acceptance) (address gas : Nat)
    (input output : ByteView) (left : Nat)
    (h : run profile keccak address gas input = .ok (output, left)) : left ≤ gas := by
  unfold run at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i out left' hDispatch
        cases h
        unfold dispatch at hDispatch
        split at hDispatch
        · cases keccak with
          | none => cases hDispatch
          | some acceptance =>
            have := charge_success _ _ _ _ _ (Option.some.inj hDispatch)
            omega
        · have := Sha256.run_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := Ripemd160.run_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := ModExp.run_success _ _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BN254.Fast.runAdd_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BN254.Fast.runMul_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BN254.runPairing_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := Blake2f.run_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := KZG.run_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BLS12381.Fast.runG1Add_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BLS12381.Fast.runG1Msm_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BLS12381.Fast.runG2Add_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BLS12381.Fast.runG2Msm_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := BLS12381.runPairing_success _ _ _ _ (Option.some.inj hDispatch); omega
        · have := (BLS12381.runMap_success _ _ _ _).1 (Option.some.inj hDispatch); omega
        · have := (BLS12381.runMap_success _ _ _ _).2 (Option.some.inj hDispatch); omega
        · have := P256.run_success _ _ _ _ (Option.some.inj hDispatch); omega
        · cases hDispatch
      · cases h
      · cases h

#guard active .shanghaiPlus 1 && active .shanghaiPlus 9 && !active .shanghaiPlus 4
#guard !active .shanghaiPlus 0x0a && !active .preShanghai 0x0a && active .osaka 0x100
#guard !active .cancunPlus 0x100 && !active .shanghaiPlus 0x100 && !active .osaka 0x101
#guard !active .shanghaiPlus 0 && !active .osaka 0x12
#guard (match run .shanghaiPlus none 2 60 {} with | .ok (out, 0) => out.size == 32 | _ => false)
#guard (match run .shanghaiPlus none 2 59 {} with | .error .outOfGas => true | _ => false)
#guard (match run .shanghaiPlus none 1 3000 {} with | .error .unsupportedFork => true | _ => false)
#guard (match run .shanghaiPlus (some Keccak.dangerouslyAcceptUnverified) 1 3000 {} with
  | .ok (out, 0) => out.size == 0 | _ => false)
#guard (match run .shanghaiPlus none 5 200 {} with | .ok (out, 0) => out.size == 0 | _ => false)
#guard (match run .osaka none 5 499 {} with | .error .outOfGas => true | _ => false)
#guard (match run .shanghaiPlus none 9 0 {} with | .error .outOfGas => true | _ => false)
#guard (match run .shanghaiPlus none 2 (1 <<< 40) { size := maxInputBytes + 1 } with
  | .error .resourceLimit => true | _ => false)
#guard (match run .shanghaiPlus none 0x0a 100000 {} with | .error .unsupportedFork => true | _ => false)
#guard (match run .cancunPlus none 0x0a 100000 {} with | .error .outOfGas => true | _ => false)
#guard (match run .cancunPlus none 0x0b 100000 {} with | .error .unsupportedFork => true | _ => false)
#guard (match run .osaka none 0x0b 100000 {} with | .error .outOfGas => true | _ => false)
#guard active .cancunPlus 0x0a && !active .cancunPlus 0x0b && active .osaka 0x11

#print axioms materialize_size
#print axioms run_inactive
#print axioms run_oversize
#print axioms active_range
#print axioms run_gas_le
#print axioms materializeLoop_size

end EVMCleanroom.Precompiles
