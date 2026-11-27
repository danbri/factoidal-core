/-!
# Byte windows and big-endian words for the ABI codec

Decoders read untrusted bytes through `rd`, a total read that is zero outside
the array, and every decoder checks its range before it reads. Encodings are
specified as `List UInt8`. `Window d p l` says the bytes of `d` from `p` are
exactly `l`: it is the only link the round-trip proofs need between the
specification lists and the array a decoder is given.

Reference: Solidity "Contract ABI Specification" (formal specification of the
encoding), used as specification only.
-/

namespace EthereumWallet.Abi

/-- Total byte read: zero outside the array. -/
@[inline] def rd (d : ByteArray) (i : Nat) : UInt8 :=
  if h : i < d.size then d[i] else 0

/-- `2^256`, the word modulus. -/
def two256 : Nat := 2 ^ 256
/-- `2^255`. -/
def two255 : Nat := 2 ^ 255

theorem two256_eq : two256 = 2 * two255 := by decide

/-- The bytes of `d` from `p` are exactly `l`, and they lie inside `d`. -/
def Window (d : ByteArray) (p : Nat) (l : List UInt8) : Prop :=
  p + l.length ≤ d.size ∧ ∀ (i : Nat) (h : i < l.length), rd d (p + i) = l[i]

theorem Window.left {d : ByteArray} {p : Nat} {a b : List UInt8}
    (h : Window d p (a ++ b)) : Window d p a := by
  obtain ⟨hs, hr⟩ := h
  rw [List.length_append] at hs
  refine ⟨by omega, fun i hi => ?_⟩
  have := hr i (by rw [List.length_append]; omega)
  rw [List.getElem_append_left hi] at this
  exact this

theorem Window.right {d : ByteArray} {p : Nat} {a b : List UInt8}
    (h : Window d p (a ++ b)) : Window d (p + a.length) b := by
  obtain ⟨hs, hr⟩ := h
  rw [List.length_append] at hs
  refine ⟨by omega, fun i hi => ?_⟩
  have := hr (a.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [Nat.add_assoc]
  exact this

theorem Window.size {d : ByteArray} {p : Nat} {l : List UInt8} (h : Window d p l) :
    p + l.length ≤ d.size := h.1

/-- Bytes of a list as an array. -/
def toBytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- Bytes of an array as a list. -/
def ofBytes (d : ByteArray) : List UInt8 := d.data.toList

theorem toBytes_size (l : List UInt8) : (toBytes l).size = l.length := by
  simp [toBytes, ByteArray.size]

theorem rd_toBytes (l : List UInt8) (i : Nat) (h : i < l.length) : rd (toBytes l) i = l[i] := by
  have hs : i < (toBytes l).size := by rw [toBytes_size]; exact h
  simp only [rd, hs, dite_true]
  rfl

/-- Kind: bridge. Says: an array built from a list is a window on that list at 0.
    Does not say: anything about arrays built another way. -/
theorem window_toBytes (l : List UInt8) : Window (toBytes l) 0 l :=
  ⟨by rw [toBytes_size]; omega, fun i h => by rw [Nat.zero_add]; exact rd_toBytes l i h⟩

/-- Decidable form of `Window`, used by the strict decoder's canonical check. -/
def windowLoop (d : ByteArray) : Nat → List UInt8 → Bool
  | _, [] => true
  | p, b :: l => rd d p == b && windowLoop d (p + 1) l

def windowB (d : ByteArray) (p : Nat) (l : List UInt8) : Bool :=
  decide (p + l.length ≤ d.size) && windowLoop d p l

theorem windowLoop_spec (d : ByteArray) (l : List UInt8) (p : Nat) (h : windowLoop d p l = true) :
    ∀ (i : Nat) (hi : i < l.length), rd d (p + i) = l[i] := by
  induction l generalizing p with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons b l ih =>
    simp only [windowLoop, Bool.and_eq_true, beq_iff_eq] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have := ih (p + 1) h.2 j (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem windowLoop_complete (d : ByteArray) (l : List UInt8) (p : Nat)
    (h : ∀ (i : Nat) (hi : i < l.length), rd d (p + i) = l[i]) : windowLoop d p l = true := by
  induction l generalizing p with
  | nil => rfl
  | cons b l ih =>
    simp only [windowLoop, Bool.and_eq_true, beq_iff_eq]
    have h0 := h 0 (by simp)
    refine ⟨by simpa using h0, ih (p + 1) fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- Kind: decision procedure. Says: `windowB` is true exactly when `Window` holds.
    Does not say: anything about cost. -/
theorem windowB_iff (d : ByteArray) (p : Nat) (l : List UInt8) :
    windowB d p l = true ↔ Window d p l := by
  simp only [windowB, Bool.and_eq_true, decide_eq_true_eq, Window]
  exact ⟨fun h => ⟨h.1, windowLoop_spec d l p h.2⟩, fun h => ⟨h.1, windowLoop_complete d l p h.2⟩⟩

/-! ## Big-endian numbers -/

def beAcc : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, n, acc => beAcc k (n / 256) (UInt8.ofNat (n % 256) :: acc)

/-- The low `k` bytes of `n`, most significant first. -/
def beBytes (k n : Nat) : List UInt8 := beAcc k n []

theorem beAcc_eq (k n : Nat) (acc : List UInt8) : beAcc k n acc = beAcc k n [] ++ acc := by
  induction k generalizing n acc with
  | zero => simp [beAcc]
  | succ k ih =>
    simp only [beAcc]
    rw [ih, ih (acc := [_])]
    simp

theorem beBytes_succ (k n : Nat) :
    beBytes (k + 1) n = beBytes k (n / 256) ++ [UInt8.ofNat (n % 256)] := by
  simp only [beBytes, beAcc]
  rw [beAcc_eq]

theorem beBytes_length (k n : Nat) : (beBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [beBytes_succ]; simp [ih]

/-- The number written in the `k` bytes of `d` from `p`, most significant first.
    The recursion depth is `k`, and every caller passes at most 32. -/
def beNat (d : ByteArray) (p : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => beNat d p k * 256 + (rd d (p + k)).toNat

theorem beNat_of_window (d : ByteArray) (p k n : Nat) (h : Window d p (beBytes k n)) :
    beNat d p k = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [beNat, Nat.mod_one]
  | succ k ih =>
    rw [beBytes_succ] at h
    have h1 := ih _ h.left
    have hb : rd d (p + k) = UInt8.ofNat (n % 256) := by
      have := h.right.2 0 (by simp)
      simpa [beBytes_length] using this
    have hn : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp only [UInt8.toNat_ofNat']
      omega
    simp only [beNat, h1, hb, hn]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    generalize n / 256 % 256 ^ k = x
    omega

/-- A 32-byte ABI word. -/
def word (n : Nat) : List UInt8 := beBytes 32 n

theorem word_length (n : Nat) : (word n).length = 32 := beBytes_length 32 n

inductive Err where
  /-- A read would pass the end of the data. -/
  | outOfBounds
  /-- A length or count needs more data than is left. -/
  | lengthOutOfBounds
  /-- An offset is not where the canonical encoding puts the tail. -/
  | badOffset
  /-- Bits set outside the value's width, or nonzero padding. -/
  | dirtyPadding
  /-- Bytes left over after the value. -/
  | trailingBytes
  /-- The bytes are not the canonical encoding of the decoded value. -/
  | nonCanonical
  /-- The type is not one this codec accepts (zero-size element, bad width, too deep). -/
  | badType
  /-- No known function or event matches. -/
  | unknownSelector
  /-- Wrong number of topics, or a topic that does not match. -/
  | badTopics
  deriving Repr, DecidableEq, Inhabited

/-- Read a word, refusing a read past the end. -/
def readWord (d : ByteArray) (p : Nat) : Except Err Nat :=
  if p + 32 ≤ d.size then .ok (beNat d p 32) else .error .outOfBounds

/-- Kind: refusal at the bound. Says: a word read that would pass the end is refused.
    Does not say: what a successful read returns. -/
theorem readWord_out_of_bounds (d : ByteArray) (p : Nat) (h : d.size < p + 32) :
    readWord d p = .error .outOfBounds := by
  simp only [readWord]
  rw [if_neg (by omega)]

theorem readWord_of_window (d : ByteArray) (p n : Nat) (hn : n < two256)
    (h : Window d p (word n)) : readWord d p = .ok n := by
  have hs := h.size
  rw [word_length] at hs
  simp only [readWord]
  rw [if_pos hs, beNat_of_window d p 32 n h]
  have : (256 : Nat) ^ 32 = two256 := by decide
  rw [this, Nat.mod_eq_of_lt hn]

/-- `n` bytes of `d` from `p`. Callers check `p + n ≤ d.size` first. -/
def takeLoop (d : ByteArray) (p : Nat) : Nat → List UInt8 → List UInt8
  | 0, acc => acc
  | k + 1, acc => takeLoop d p k (rd d (p + k) :: acc)

def takeBytes (d : ByteArray) (p n : Nat) : List UInt8 := takeLoop d p n []

theorem takeLoop_eq (d : ByteArray) (p k : Nat) (acc : List UInt8) :
    takeLoop d p k acc = (List.range k).map (fun i => rd d (p + i)) ++ acc := by
  induction k generalizing acc with
  | zero => simp [takeLoop]
  | succ k ih =>
    simp only [takeLoop]
    rw [ih, List.range_succ]
    simp

theorem takeBytes_of_window (d : ByteArray) (p : Nat) (l : List UInt8) (h : Window d p l) :
    takeBytes d p l.length = l := by
  simp only [takeBytes]
  rw [takeLoop_eq, List.append_nil]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact h.2 i h2

/-- True when the `n` bytes of `d` from `p` are all zero. -/
def allZero (d : ByteArray) (p : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => rd d (p + k) == 0 && allZero d p k

theorem allZero_of_window (d : ByteArray) (p k : Nat) (h : Window d p (List.replicate k 0)) :
    allZero d p k = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [allZero, Bool.and_eq_true, beq_iff_eq]
    have h0 : ∀ (i : Nat), i < k + 1 → rd d (p + i) = 0 := by
      intro i hi
      have := h.2 i (by simpa using hi)
      simpa using this
    refine ⟨h0 k (by omega), ih ⟨?_, ?_⟩⟩
    · have := h.1
      simp only [List.length_replicate] at this ⊢
      omega
    · intro i hi
      have hi' : i < k := by simpa using hi
      rw [h0 i (by omega)]
      simp

/-- Zero bytes that pad `n` bytes up to a multiple of 32. -/
def padLen (n : Nat) : Nat := (32 - n % 32) % 32

end EthereumWallet.Abi
