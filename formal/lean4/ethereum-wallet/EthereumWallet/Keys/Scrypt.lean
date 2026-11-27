import L4Factoidal.Crypto.Hmac
import EthereumWallet.Keys.Salsa

/-
scrypt (RFC 7914 sections 5 and 6) over the repository's pure PBKDF2-HMAC-SHA-256.

Memory: scryptROMix keeps `V`, `128 * r * N` bytes, in one `ByteArray`, and the
`p` blocks are mixed one after another, so the peak is about
`128 * r * N + 128 * r * p` bytes plus a few blocks. `ScryptParams.check` runs
before anything is allocated and refuses parameters whose figure is above
`scryptMaxBytes`.

Theorems (stated here, proved at the end of the file):
* `scrypt_refuses_over_limit`, `scrypt_refuses_large_n`: above the limit the
  answer is `.error .memoryLimit`.
* `scrypt_ok_bound`: an answer `.ok` means the parameters were within every bound.
* `scrypt_ok_size`: an answer `.ok dk` has `dk.size = dkLen` (by a run-time check).
* `scrypt_refuses_bad_n`, `scrypt_refuses_zero_r`, `scrypt_refuses_zero_p`,
  `scrypt_refuses_dkLen`.
Tested only (RFC 7914 vectors, `KeystoreTests`): that the bytes are scrypt's.

Constant time: the index into `V` depends on the password by design (that is
scrypt); word operations are fixed-width `UInt32`; no `Nat` holds secret data
(only sizes, counts and the index `j`, which is secret-dependent and is used as
an array offset). Password, the `p` blocks and `V` live in ordinary Lean heap
objects until the runtime frees them; nothing is zeroised.
-/

namespace EthereumWallet.Keys

open L4Factoidal.Crypto (pbkdf2Sha256)

/-- The largest `128 * r * N + 128 * r * p` accepted, in bytes: 1 GiB + 1 MiB
    (it admits RFC 7914's largest vector, N = 2^20 with r = 8). Below 2^31. -/
def scryptMaxBytes : Nat := 1074790400

/-- The largest derived-key length accepted, in bytes. -/
def scryptMaxDkLen : Nat := 1024

/-- scrypt's cost parameters and output length (RFC 7914 section 2). -/
structure ScryptParams where
  n : Nat
  r : Nat
  p : Nat
  dkLen : Nat
  deriving Repr, BEq

inductive ScryptError where
  /-- `128 * r * N + 128 * r * p` is above `scryptMaxBytes`. -/
  | memoryLimit
  /-- `N` is below 2 or not a power of two. -/
  | invalidN
  | zeroR
  | zeroP
  /-- `dkLen` is zero or above `scryptMaxDkLen`. -/
  | invalidDkLen
  /-- A derived key of the wrong length came back (not expected to happen). -/
  | internal
  deriving Repr, BEq, DecidableEq

/-- The bytes scrypt needs for `V` and the `p` blocks. -/
def ScryptParams.memoryBytes (ps : ScryptParams) : Nat :=
  128 * ps.r * ps.n + 128 * ps.r * ps.p

/-- Parameter check, run before any allocation. The memory limit comes first. -/
def ScryptParams.check (ps : ScryptParams) : Except ScryptError Unit :=
  if scryptMaxBytes < ps.memoryBytes then .error .memoryLimit
  else if ps.r = 0 then .error .zeroR
  else if ps.p = 0 then .error .zeroP
  else if ps.n < 2 ∨ ps.n &&& (ps.n - 1) ≠ 0 then .error .invalidN
  else if ps.dkLen = 0 ∨ scryptMaxDkLen < ps.dkLen then .error .invalidDkLen
  else .ok ()

/-- scryptROMix step 2: `V_i = X; X = BlockMix(X)`, `count` times. `v` is
    appended to in place. Structural on `count`, a tail call. -/
def romixFill (r : Nat) : Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | 0, v, x => (v, x)
  | count + 1, v, x =>
    let v := v ++ x
    romixFill r count v (blockMix r x ByteArray.empty 0 false)

/-- scryptROMix step 3: `j = Integerify(X) mod N; X = BlockMix(X XOR V_j)`,
    `count` times. `N` is a power of two below 2^32, so the low 32 bits of the
    last 64-byte block decide `j`. Structural on `count`, a tail call. -/
def romixMix (r n : Nat) (v : ByteArray) : Nat → ByteArray → ByteArray
  | 0, x => x
  | count + 1, x =>
    let j := (le32 x (64 * (2 * r - 1))).toNat % n
    romixMix r n v count (blockMix r x v (j * (128 * r)) true)

/-- scryptROMix (RFC 7914 section 5) on one `128 * r` byte block. -/
def romix (r n : Nat) (b : ByteArray) : ByteArray :=
  let filled := romixFill r n (ByteArray.emptyWithCapacity (128 * r * n)) b
  romixMix r n filled.1 n filled.2

/-- RFC 7914 section 6 step 2: ROMix on each of the `p` blocks in turn. -/
def scryptBlocks (r n : Nat) (b : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | count + 1, i, acc =>
    scryptBlocks r n b count (i + 1)
      (acc ++ romix r n (b.extract (i * (128 * r)) ((i + 1) * (128 * r))))

/-- scrypt without the parameter check: only for parameters that passed it. -/
def scryptCore (password salt : ByteArray) (ps : ScryptParams) : ByteArray :=
  let b := pbkdf2Sha256 password salt 1 (ps.p * (128 * ps.r))
  let b' := scryptBlocks ps.r ps.n b ps.p 0 (ByteArray.emptyWithCapacity (ps.p * (128 * ps.r)))
  pbkdf2Sha256 password b' 1 ps.dkLen

/-- scrypt (RFC 7914 section 6). Refuses bad or over-limit parameters before
    allocating anything. -/
def scrypt (password salt : ByteArray) (ps : ScryptParams) : Except ScryptError ByteArray :=
  match ps.check with
  | .error e => .error e
  | .ok () =>
    let dk := scryptCore password salt ps
    if dk.size = ps.dkLen then .ok dk else .error .internal

/-! ## Theorems -/

/-- Kind: resource refusal.
    Says: when `V` and the blocks would need more than `scryptMaxBytes`, the
    check answers `.error .memoryLimit`.
    Does not say: how much memory the Lean runtime uses below the limit. -/
theorem check_over_limit (ps : ScryptParams) (h : scryptMaxBytes < ps.memoryBytes) :
    ps.check = .error .memoryLimit := by
  simp [ScryptParams.check, h]

/-- Kind: resource refusal.
    Says: `scrypt` answers `.error .memoryLimit`, without reaching `scryptCore`,
    when `128 * r * N + 128 * r * p` is above `scryptMaxBytes`.
    Does not say: that the limit suits a given machine. -/
theorem scrypt_refuses_over_limit (password salt : ByteArray) (ps : ScryptParams)
    (h : scryptMaxBytes < 128 * ps.r * ps.n + 128 * ps.r * ps.p) :
    scrypt password salt ps = .error .memoryLimit := by
  have hc := check_over_limit ps (by simpa [ScryptParams.memoryBytes] using h)
  simp [scrypt, hc]

/-- Kind: resource refusal.
    Says: `V` alone above the limit (`128 * r * N`) is refused the same way.
    Does not say: anything about parameters at or below the limit. -/
theorem scrypt_refuses_large_n (password salt : ByteArray) (ps : ScryptParams)
    (h : scryptMaxBytes < 128 * ps.r * ps.n) :
    scrypt password salt ps = .error .memoryLimit :=
  scrypt_refuses_over_limit password salt ps (by omega)

/-- Kind: resource bound.
    Says: a passed check means memory within the limit, `r` and `p` positive,
    `N` at least 2 with `N &&& (N - 1) = 0`, and `0 < dkLen ≤ scryptMaxDkLen`.
    Does not say: that `N &&& (N - 1) = 0` is spelled out as "a power of two". -/
theorem check_ok_bound (ps : ScryptParams) (h : ps.check = .ok ()) :
    128 * ps.r * ps.n + 128 * ps.r * ps.p ≤ scryptMaxBytes ∧ 0 < ps.r ∧ 0 < ps.p ∧
      2 ≤ ps.n ∧ ps.n &&& (ps.n - 1) = 0 ∧ 0 < ps.dkLen ∧ ps.dkLen ≤ scryptMaxDkLen := by
  unfold ScryptParams.check at h
  by_cases h1 : scryptMaxBytes < ps.memoryBytes
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : ps.r = 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : ps.p = 0
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3] at h
        by_cases h4 : ps.n < 2 ∨ ps.n &&& (ps.n - 1) ≠ 0
        · rw [if_pos h4] at h; cases h
        · by_cases h5 : ps.dkLen = 0 ∨ scryptMaxDkLen < ps.dkLen
          · rw [if_neg h4, if_pos h5] at h; cases h
          · exact ⟨Nat.le_of_not_lt h1, Nat.pos_of_ne_zero h2, Nat.pos_of_ne_zero h3,
              Nat.le_of_not_lt (fun x => h4 (Or.inl x)),
              Decidable.byContradiction (fun hn => h4 (Or.inr hn)),
              Nat.pos_of_ne_zero (fun x => h5 (Or.inl x)),
              Nat.le_of_not_lt (fun x => h5 (Or.inr x))⟩

/-- Kind: resource bound.
    Says: if `scrypt` answers `.ok`, the parameters were within every bound of
    `check_ok_bound`; in particular `V` and the blocks fit in `scryptMaxBytes`.
    Does not say: that the answer is the scrypt function of RFC 7914 (tested). -/
theorem scrypt_ok_bound (password salt : ByteArray) (ps : ScryptParams) (dk : ByteArray)
    (h : scrypt password salt ps = .ok dk) :
    128 * ps.r * ps.n + 128 * ps.r * ps.p ≤ scryptMaxBytes ∧ 0 < ps.r ∧ 0 < ps.p ∧
      2 ≤ ps.n ∧ ps.n &&& (ps.n - 1) = 0 ∧ 0 < ps.dkLen ∧ ps.dkLen ≤ scryptMaxDkLen := by
  cases hc : ps.check with
  | error e => simp [scrypt, hc] at h
  | ok u => cases u; exact check_ok_bound ps hc

/-- Kind: size.
    Says: an `.ok dk` answer has exactly `dkLen` bytes (`scrypt` checks it).
    Does not say: that the `.error .internal` branch is unreachable. -/
theorem scrypt_ok_size (password salt : ByteArray) (ps : ScryptParams) (dk : ByteArray)
    (h : scrypt password salt ps = .ok dk) : dk.size = ps.dkLen := by
  cases hc : ps.check with
  | error e => simp [scrypt, hc] at h
  | ok u =>
    cases u
    simp only [scrypt, hc] at h
    by_cases hs : (scryptCore password salt ps).size = ps.dkLen
    · rw [if_pos hs] at h; cases h; exact hs
    · rw [if_neg hs] at h; cases h

/-- Kind: refusal.
    Says: a failed check is `scrypt`'s answer, whatever the password and salt.
    Does not say: which check failed. -/
theorem scrypt_check_error (password salt : ByteArray) (ps : ScryptParams) (e : ScryptError)
    (h : ps.check = .error e) : scrypt password salt ps = .error e := by
  simp [scrypt, h]

/-- Kind: refusal.
    Says: within the memory limit, `r = 0` is refused with `.zeroR`.
    Does not say: anything else. -/
theorem scrypt_refuses_zero_r (password salt : ByteArray) (ps : ScryptParams)
    (hm : ps.memoryBytes ≤ scryptMaxBytes) (h : ps.r = 0) :
    scrypt password salt ps = .error .zeroR := by
  apply scrypt_check_error
  simp [ScryptParams.check, Nat.not_lt_of_ge hm, h]

/-- Kind: refusal.
    Says: within the memory limit and with `r > 0`, `p = 0` is refused with `.zeroP`.
    Does not say: anything else. -/
theorem scrypt_refuses_zero_p (password salt : ByteArray) (ps : ScryptParams)
    (hm : ps.memoryBytes ≤ scryptMaxBytes) (hr : ps.r ≠ 0) (h : ps.p = 0) :
    scrypt password salt ps = .error .zeroP := by
  apply scrypt_check_error
  simp [ScryptParams.check, Nat.not_lt_of_ge hm, hr, h]

/-- Kind: refusal.
    Says: within the memory limit and with `r, p > 0`, an `N` below 2 or with
    `N &&& (N - 1) ≠ 0` is refused with `.invalidN`.
    Does not say: anything else. -/
theorem scrypt_refuses_bad_n (password salt : ByteArray) (ps : ScryptParams)
    (hm : ps.memoryBytes ≤ scryptMaxBytes) (hr : ps.r ≠ 0) (hp : ps.p ≠ 0)
    (h : ps.n < 2 ∨ ps.n &&& (ps.n - 1) ≠ 0) :
    scrypt password salt ps = .error .invalidN := by
  apply scrypt_check_error
  simp [ScryptParams.check, Nat.not_lt_of_ge hm, hr, hp, h]

/-- Kind: refusal.
    Says: with the other parameters accepted, `dkLen = 0` or
    `dkLen > scryptMaxDkLen` is refused with `.invalidDkLen`.
    Does not say: anything else. -/
theorem scrypt_refuses_dkLen (password salt : ByteArray) (ps : ScryptParams)
    (hm : ps.memoryBytes ≤ scryptMaxBytes) (hr : ps.r ≠ 0) (hp : ps.p ≠ 0)
    (hn : ¬(ps.n < 2 ∨ ps.n &&& (ps.n - 1) ≠ 0))
    (h : ps.dkLen = 0 ∨ scryptMaxDkLen < ps.dkLen) :
    scrypt password salt ps = .error .invalidDkLen := by
  apply scrypt_check_error
  simp only [ScryptParams.check, Nat.not_lt_of_ge hm, hr, hp, if_false, if_neg hn, if_pos h]

end EthereumWallet.Keys
