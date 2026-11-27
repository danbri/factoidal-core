/-!
# Precompiled contracts: shared byte helpers and the result contract

Every precompile in this directory is a pure function from forwarded gas and
the complete input bytes to a `Result`. The three outcomes are kept apart:

* `success output gasLeft`: the call succeeds, `output` becomes return data;
* `failure`: an exceptional halt in the precompile frame (too little gas or
  input the specification rejects). The caller loses the forwarded gas;
* `refusal`: a local resource bound of this implementation was reached. This
  is never reported as an Ethereum result.

The modules under `Precompiles/` import only each other (the field, curve and
pairing modules nothing else at all), so another package can reuse them by
source without importing the EVM.

Normative sources: Ethereum Yellow Paper appendix E, the EIPs named in each
module, and the execution-specs (EELS) precompile modules as the comparison
target. No other implementation is imported, copied or translated.
-/

namespace EVMCleanroom.Precompiles

inductive Result where
  | success (output : ByteArray) (gasLeft : Nat)
  | failure
  | refusal

/-- What the body of a precompile decided after its gas was charged. -/
inductive Body where
  | output (bytes : ByteArray)
  | invalid
  | refuse

/-- Charge first, then run the body. The body is not evaluated when the
    forwarded gas does not cover the price. -/
@[inline] def charge (gas cost : Nat) (body : Unit → Body) : Result :=
  if gas < cost then .failure
  else match body () with
    | .output bytes => .success bytes (gas - cost)
    | .invalid => .failure
    | .refuse => .refusal

/-- Kind: gas admission.
    Says: a call whose forwarded gas is below the price fails without running the body.
    Does not say: the price itself matches the specification. -/
theorem charge_underfunded (gas cost : Nat) (body : Unit → Body) (h : gas < cost) :
    charge gas cost body = .failure := by
  simp [charge, h]

/-- Kind: accounting.
    Says: a successful call returns the body's bytes and exactly the unspent gas.
    Does not say: anything about the bytes. -/
theorem charge_success (gas cost : Nat) (body : Unit → Body) (out : ByteArray) (left : Nat)
    (h : charge gas cost body = .success out left) :
    body () = .output out ∧ left + cost = gas := by
  unfold charge at h
  split at h
  · cases h
  · rename_i hGas
    split at h
    · rename_i bytes hBody
      cases h
      exact ⟨hBody, by omega⟩
    · cases h
    · cases h

/-- Kind: accounting.
    Says: a funded call whose body produced bytes succeeds with those bytes.
    Does not say: anything about the bytes. -/
theorem charge_funded (gas cost : Nat) (body : Unit → Body) (out : ByteArray)
    (hGas : cost ≤ gas) (hBody : body () = .output out) :
    charge gas cost body = .success out (gas - cost) := by
  have : ¬ gas < cost := by omega
  simp [charge, this, hBody]

/-- Number of 32-byte words covering `size` bytes. -/
def words32 (size : Nat) : Nat := (size + 31) / 32

/-- A byte of the input, zero beyond its end (the EELS `buffer_read` rule). -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

def readLoop (b : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n+1, off, acc => readLoop b n (off+1) (acc.push (byteAt b off))

/-- `len` bytes starting at `off`, right-padded with zeros. -/
def readPadded (b : ByteArray) (off len : Nat) : ByteArray :=
  readLoop b len off ByteArray.empty

theorem readLoop_size (b : ByteArray) (n off : Nat) (acc : ByteArray) :
    (readLoop b n off acc).size = acc.size + n := by
  induction n generalizing off acc with
  | zero => simp [readLoop]
  | succ n ih => simp [readLoop, ih, ByteArray.size_push]; omega

/-- Kind: length.
    Says: a padded read has exactly the requested length, whatever the input.
    Does not say: which bytes it holds. -/
theorem readPadded_size (b : ByteArray) (off len : Nat) : (readPadded b off len).size = len := by
  simp [readPadded, readLoop_size]

def beLoop (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n+1, off, acc => beLoop b n (off+1) (acc * 256 + (byteAt b off).toNat)

/-- Big-endian integer of `len` bytes at `off`, zero-padded on the right. -/
def beNat (b : ByteArray) (off len : Nat) : Nat := beLoop b len off 0

def leLoop (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n+1, off, acc => leLoop b n off (acc * 256 + (byteAt b (off + n)).toNat)

/-- Little-endian integer of `len` bytes at `off`. -/
def leNat (b : ByteArray) (off len : Nat) : Nat := leLoop b len off 0

def beOutLoop (n : Nat) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | k+1, acc => beOutLoop n k (acc.push (UInt8.ofNat (n >>> (8 * k))))

/-- `len` big-endian bytes of `n` (the low `8*len` bits). -/
def natToBE (len n : Nat) : ByteArray := beOutLoop n len ByteArray.empty

theorem beOutLoop_size (n k : Nat) (acc : ByteArray) :
    (beOutLoop n k acc).size = acc.size + k := by
  induction k generalizing acc with
  | zero => simp [beOutLoop]
  | succ k ih => simp [beOutLoop, ih, ByteArray.size_push]; omega

/-- Kind: length.
    Says: fixed-width big-endian output has exactly the requested width.
    Does not say: the value fits. -/
theorem natToBE_size (len n : Nat) : (natToBE len n).size = len := by
  simp [natToBE, beOutLoop_size]

def leOutLoop : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | k+1, n, acc => leOutLoop k (n / 256) (acc.push (UInt8.ofNat n))

/-- `len` little-endian bytes of `n`. Used only for short fixed widths. -/
def natToLE (len n : Nat) : ByteArray := leOutLoop len n ByteArray.empty

theorem leOutLoop_size (k n : Nat) (acc : ByteArray) :
    (leOutLoop k n acc).size = acc.size + k := by
  induction k generalizing n acc with
  | zero => simp [leOutLoop]
  | succ k ih => simp [leOutLoop, ih, ByteArray.size_push]; omega

theorem natToLE_size (len n : Nat) : (natToLE len n).size = len := by
  simp [natToLE, leOutLoop_size]

def allZeroLoop (b : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, off => byteAt b off == 0 && allZeroLoop b n (off+1)

/-- Are the `len` bytes at `off` all zero (bytes beyond the end count as zero)? -/
def allZero (b : ByteArray) (off len : Nat) : Bool := allZeroLoop b len off

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hexLoop : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | a :: b :: rest, acc =>
    match hexDigit a, hexDigit b with
    | some x, some y => hexLoop rest (acc.push (UInt8.ofNat (16 * x + y)))
    | _, _ => none

/-- Strict hexadecimal decoding, for tests and the command line. -/
def ofHex? (s : String) : Option ByteArray := hexLoop s.toList ByteArray.empty

/-- Test helper: undecodable text gives the empty array. -/
def hex (s : String) : ByteArray := (ofHex? s).getD ByteArray.empty

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

def toHex (b : ByteArray) : String :=
  String.ofList (b.toList.flatMap fun byte => [hexChar (byte.toNat / 16), hexChar (byte.toNat % 16)])

#guard toHex (readPadded (hex "0102") 1 3) == "020000"
#guard beNat (hex "0102") 0 2 == 258
#guard beNat (hex "0102") 1 2 == 512
#guard leNat (hex "0102") 0 2 == 513
#guard toHex (natToBE 4 258) == "00000102"
#guard toHex (natToBE 1 258) == "02"
#guard toHex (natToLE 4 258) == "02010000"
#guard allZero (hex "000001") 0 2 && !allZero (hex "000001") 0 3 && allZero (hex "") 5 9
#guard (ofHex? "0g").isNone && (ofHex? "0").isNone

#print axioms charge_underfunded
#print axioms charge_success
#print axioms charge_funded
#print axioms readPadded_size
#print axioms natToBE_size
#print axioms natToLE_size
#print axioms readLoop_size
#print axioms beOutLoop_size
#print axioms leOutLoop_size

end EVMCleanroom.Precompiles
