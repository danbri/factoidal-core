import EVMCleanroom.Core

/-!
# EVM identity precompile (address 0x04): independently implemented Lean semantics

The identity operation returns precisely the input bytes. Its post-Istanbul
and earlier EVM pricing is 15 base gas plus 3 per 32-byte input word.
The caller supplies the precompile's forwarded gas, not the parent gas.
An explicit implementation byte cap is checked before returning data.

This is an executable precompile *entry point*, not yet integrated with
CALL, CALLCODE, DELEGATECALL or STATICCALL. The identity operation is
available across the Ethereum forks this seed models. A resource refusal
is an indeterminate implementation limit, not an EVM out-of-gas result.

Normative comparison target: Ethereum Yellow Paper Appendix E and
execution-specs precompiles identity. No other Ethereum implementation is
imported as executable code.
-/

namespace EVMCleanroom.IdentityPrecompile

/-- Number of 32-byte words charged for a precompile byte sequence. -/
def wordsForBytes (size : Nat) : Nat := (size + 31) / 32

/-- Identity precompile execution gas, excluding its parent's CALL overhead. -/
def gasCost (size : Nat) : Nat := 15 + 3 * wordsForBytes size

/-- The input limit is an explicitly local resource policy.
    A successful result retains the exact input array and unspent gas. -/
def execute (maxBytes gas : Nat) (input : Array UInt8) :
    Except Error (Array UInt8 × Nat) :=
  if input.size > maxBytes then .error .resourceLimit
  else if gas < gasCost input.size then .error .outOfGas
  else .ok (input, gas - gasCost input.size)

/-- Execute identity on an immutable, bounded view without materialising
    its bytes. This is the adapter used by the real CALL-family dispatcher.
    Its two refusals and gas charge deliberately match `execute`. -/
def executeView (maxBytes gas : Nat) (input : ByteView) :
    Except Error (ByteView × Nat) :=
  if input.size > maxBytes then .error .resourceLimit
  else if gas < gasCost input.size then .error .outOfGas
  else .ok (input, gas - gasCost input.size)

/-- Correspondence with the already tested byte-array entry point.
    No cryptographic assumption or externally computed result is involved. -/
theorem executeView_ofArray (maxBytes gas : Nat) (bytes : Array UInt8) :
    (executeView maxBytes gas (ByteView.ofArray bytes)).map
      (fun result => (bytes, result.2)) = execute maxBytes gas bytes := by
  by_cases hSize : bytes.size > maxBytes
  · simp [executeView, execute, ByteView.ofArray, hSize, Except.map]
  · by_cases hGas : gas < gasCost bytes.size
    · simp [executeView, execute, ByteView.ofArray, hSize, hGas, Except.map]
    · simp [executeView, execute, ByteView.ofArray, hSize, hGas, Except.map]

theorem executeView_oversize (maxBytes gas : Nat) (view : ByteView)
    (h : maxBytes < view.size) :
    executeView maxBytes gas view = .error .resourceLimit := by
  simp [executeView, h]

theorem executeView_exact (maxBytes gas : Nat) (view : ByteView)
    (hSize : view.size ≤ maxBytes) (hGas : gasCost view.size ≤ gas) :
    executeView maxBytes gas view = .ok (view, gas - gasCost view.size) := by
  have hNotOver : ¬ view.size > maxBytes := by omega
  have hNotUnder : ¬ gas < gasCost view.size := by omega
  simp [executeView, hNotOver, hNotUnder]

/-- Kind: admission boundary.
    Says: oversize input is refused before gas charging or output construction.
    Does not say: Ethereum itself has this input-size limit. -/
theorem execute_oversize (maxBytes gas : Nat) (input : Array UInt8)
    (h : maxBytes < input.size) :
    execute maxBytes gas input = .error .resourceLimit := by
  simp [execute, h]

/-- Kind: gas admission.
    Says: in-range input with insufficient forwarded gas fails with out-of-gas.
    Does not say: a parent CALL has allocated its budget correctly. -/
theorem execute_underfunded (maxBytes gas : Nat) (input : Array UInt8)
    (hSize : input.size ≤ maxBytes) (hGas : gas < gasCost input.size) :
    execute maxBytes gas input = .error .outOfGas := by
  have hNotOver : ¬ input.size > maxBytes := by omega
  simp [execute, hNotOver, hGas]

/-- Kind: implementation correspondence.
    Says: admitted input and gas return identical bytes and exact unused gas.
    Does not say: this entry is yet wired into CALL-family dispatch. -/
theorem execute_exact (maxBytes gas : Nat) (input : Array UInt8)
    (hSize : input.size ≤ maxBytes) (hGas : gasCost input.size ≤ gas) :
    execute maxBytes gas input = .ok (input, gas - gasCost input.size) := by
  have hNotOver : ¬ input.size > maxBytes := by omega
  have hNotUnder : ¬ gas < gasCost input.size := by omega
  simp [execute, hNotOver, hNotUnder]

/-- Kind: executed result invariant.
    Says: no successful direct identity-precompile call changes any input byte.
    Does not say: another executable path uses this function. -/
theorem execute_preserves_input (maxBytes gas : Nat) (input output : Array UInt8)
    (remaining : Nat)
    (h : execute maxBytes gas input = .ok (output, remaining)) :
    output = input := by
  by_cases hSize : input.size > maxBytes
  · simp [execute, hSize] at h
  by_cases hGas : gas < gasCost input.size
  · simp [execute, hSize, hGas] at h
  have hok := execute_exact maxBytes gas input (by omega) (by omega)
  rw [hok] at h
  cases h
  rfl

/-- Kind: accounting.
    Says: a successful precompile result conserves the supplied child gas.
    Does not say: the parent caller's access and memory charges are included. -/
theorem execute_gas_accounting (maxBytes gas : Nat) (input output : Array UInt8)
    (remaining : Nat)
    (h : execute maxBytes gas input = .ok (output, remaining)) :
    remaining + gasCost input.size = gas := by
  by_cases hSize : input.size > maxBytes
  · simp [execute, hSize] at h
  by_cases hGas : gas < gasCost input.size
  · simp [execute, hSize, hGas] at h
  have hok := execute_exact maxBytes gas input (by omega) (by omega)
  rw [hok] at h
  cases h
  omega

private def succeeds (maxBytes gas : Nat) (input : Array UInt8) (remaining : Nat) : Bool :=
  match execute maxBytes gas input with
  | .ok (output, left) => output == input && left == remaining
  | _ => false

private def isOutOfGas (maxBytes gas : Nat) (input : Array UInt8) : Bool :=
  match execute maxBytes gas input with
  | .error .outOfGas => true
  | _ => false

private def isResourceLimit (maxBytes gas : Nat) (input : Array UInt8) : Bool :=
  match execute maxBytes gas input with
  | .error .resourceLimit => true
  | _ => false

#guard wordsForBytes 0 == 0
#guard wordsForBytes 1 == 1
#guard wordsForBytes 31 == 1
#guard wordsForBytes 32 == 1
#guard wordsForBytes 33 == 2
#guard wordsForBytes 64 == 2
#guard wordsForBytes 65 == 3
#guard gasCost 0 == 15
#guard gasCost 32 == 18
#guard gasCost 33 == 21
#guard succeeds 0 15 #[] 0
#guard succeeds 1 18 #[0x00] 0
#guard succeeds 2 20 #[0xab, 0xcd] 2
#guard isOutOfGas 0 14 #[]
#guard isOutOfGas 1 17 #[0xff]
#guard isResourceLimit 0 100 #[0x00]
#guard isResourceLimit 1 0 #[0x00, 0x01]

#guard (match executeView 0 15 (ByteView.ofArray #[]) with
  | .ok (_, 0) => true
  | _ => false)
#guard (match executeView 1 17 (ByteView.ofArray #[0xff]) with
  | .error .outOfGas => true
  | _ => false)
#guard (match executeView 0 100 (ByteView.ofArray #[0xff]) with
  | .error .resourceLimit => true
  | _ => false)

#print axioms executeView_ofArray
#print axioms executeView_oversize
#print axioms executeView_exact
#print axioms execute_oversize
#print axioms execute_underfunded
#print axioms execute_exact
#print axioms execute_preserves_input
#print axioms execute_gas_accounting

end EVMCleanroom.IdentityPrecompile
