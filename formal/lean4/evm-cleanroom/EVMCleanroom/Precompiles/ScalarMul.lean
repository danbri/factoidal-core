import EVMCleanroom.Precompiles.Curve

/-!
# Windowed scalar multiplication: signed-digit recoding and table-driven loops

Generic parts shared by the curve precompiles.

* `wnaf h k`: the digits of `k` in the width-`w` non-adjacent form (Solinas,
  "Efficient arithmetic on Koblitz curves", 2000, section on width-`w` NAF),
  least significant first, where `h = 2^(w−1)` is half the window. Every digit
  is zero or odd with absolute value at most `h` (below `h` when `h` is even),
  so a table of the odd multiples `P, 3P, …, (h−1)P` serves all digits.
  The scalar is recoded 60 bits at a time on machine-sized numbers, with a
  carry between the pieces; inside a piece the digits are exactly those of the
  width-`w` NAF, at a boundary a window may be cut short.
* `windowMul`, `strausMul`: one and two scalars over a doubling, an addition
  and a negation given as functions (Straus 1964 for the shared doubling
  chain); `curveMul`, `curveMul2` instantiate them for `Curve` over a
  `FieldOps` dictionary.

Proved here: the digits reconstruct the scalar (`wnaf_eval`), each digit is
zero or odd and bounded by the window (`wnaf_digits`, `wnaf_digits_even`),
and the recoding step shrinks its argument (`wnafStep_lt`), which is what
makes the explicit count of the last piece sufficient.

Not proved: that the loops compute the group multiple (no group law is proved
in this package). `curveMul` and `curveMul2` are tested against `Curve.mul` and
`Curve.mul2` by the guards at the end, and by the differential run of
`evm-fieldperf`.

Nothing here is constant-time: the digits, the table indices and the number
of additions depend on the scalar. Public scalars only.
-/

namespace EVMCleanroom.Precompiles.ScalarMul

/-! ### Recoding -/

/-- The integer with the given signed binary digits, least significant first. -/
def evalDigits : List Int → Int
  | [] => 0
  | d :: ds => d + 2 * evalDigits ds

/-- The value of a digit array, least significant first. -/
def evalArr (a : Array Int) : Int := evalDigits a.toList

/-- One recoding step: a digit `d` and the rest `k'` with `k = d + 2·k'`.
    An even `k` gives the digit zero. An odd `k` gives its residue modulo `2h`
    taken in `(−h, h]`, and the rest is then a multiple of `h`. -/
@[inline] def wnafStep (h k : Nat) : Int × Nat :=
  if k % 2 = 0 then (0, k / 2)
  else if k % (2 * h) ≤ h then (((k % (2 * h) : Nat) : Int), h * (k / (2 * h)))
  else (((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int), h * (k / (2 * h) + 1))

/-- Exactly `count` steps: the digits are appended to `acc`, the rest is returned. -/
def wnafFixed (h : Nat) : Nat → Nat → Array Int → Array Int × Nat
  | 0, v, acc => (acc, v)
  | f+1, v, acc => wnafFixed h f (wnafStep h v).2 (acc.push (wnafStep h v).1)

/-- Steps until the value is zero. The count `fuel` is enough when `v ≤ fuel`. -/
def wnafTail (h : Nat) : Nat → Nat → Array Int → Array Int
  | 0, _, acc => acc
  | f+1, v, acc => if v = 0 then acc else wnafTail h f (wnafStep h v).2 (acc.push (wnafStep h v).1)

/-- Recode `K + c` after the digits in `acc`: 60 digits per round from the low 60 bits of `K`
    (plus the carry `c` of the round before), then the last piece until it is zero. -/
def wnafGo (h : Nat) : Nat → Nat → Nat → Array Int → Array Int
  | 0, K, c, acc => wnafTail h (K + c) (K + c) acc
  | f+1, K, c, acc =>
    if K < 1152921504606846976 then wnafTail h (K + c) (K + c) acc
    else
      wnafGo h f (K / 1152921504606846976)
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).2
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).1

/-- Signed digits of `k`, least significant first; `h` is half the window (`2^(w−1)`). -/
def wnaf (h k : Nat) : Array Int := wnafGo h (Nat.log2 k / 60 + 1) k 0 #[]

/-- A digit is zero, or odd and within the window. -/
def DigitOk (h : Nat) (d : Int) : Prop := d = 0 ∨ (d % 2 = 1 ∧ -(h : Int) ≤ d ∧ d ≤ (h : Int))

/-! ### Theorems on the recoding -/

/-- Kind: recoding identity (one step).
    Says: the digit and the rest of one step reconstruct the argument, `k = d + 2·k'`.
    Does not say: anything about the size of the digit (see `wnafStep_digit`). -/
theorem wnafStep_eq (h k : Nat) : (k : Int) = (wnafStep h k).1 + 2 * ((wnafStep h k).2 : Int) := by
  unfold wnafStep
  by_cases he : k % 2 = 0
  · rw [if_pos he]
    show (k : Int) = 0 + 2 * ((k / 2 : Nat) : Int)
    omega
  · rw [if_neg he]
    have hdm := Nat.div_add_mod k (2 * h)
    rw [Nat.mul_assoc] at hdm
    by_cases hm : k % (2 * h) ≤ h
    · rw [if_pos hm]
      show (k : Int) = ((k % (2 * h) : Nat) : Int) + 2 * ((h * (k / (2 * h)) : Nat) : Int)
      generalize k % (2 * h) = m at hdm ⊢
      generalize h * (k / (2 * h)) = t at hdm ⊢
      omega
    · rw [if_neg hm]
      show (k : Int) = ((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int)
        + 2 * ((h * (k / (2 * h) + 1) : Nat) : Int)
      rw [Nat.mul_add, Nat.mul_one]
      generalize k % (2 * h) = m at hdm ⊢
      generalize h * (k / (2 * h)) = t at hdm ⊢
      omega

/-- Kind: loop bound (decrease).
    Says: for a positive argument the rest of one step is strictly smaller, for every `h`.
    Does not say: how many steps a given scalar takes (at most its value, by this theorem;
    in practice about its bit length). -/
theorem wnafStep_lt (h k : Nat) (hk : 0 < k) : (wnafStep h k).2 < k := by
  unfold wnafStep
  by_cases he : k % 2 = 0
  · rw [if_pos he]
    show k / 2 < k
    omega
  · rw [if_neg he]
    have hdm := Nat.div_add_mod k (2 * h)
    rw [Nat.mul_assoc] at hdm
    by_cases hm : k % (2 * h) ≤ h
    · rw [if_pos hm]
      show h * (k / (2 * h)) < k
      generalize k % (2 * h) = m at hdm
      generalize h * (k / (2 * h)) = t at hdm ⊢
      omega
    · rw [if_neg hm]
      show h * (k / (2 * h) + 1) < k
      rw [Nat.mul_add, Nat.mul_one]
      generalize k % (2 * h) = m at hdm hm
      generalize h * (k / (2 * h)) = t at hdm ⊢
      omega

/-- Kind: digit bound (one step).
    Says: for a positive half-window `h` the digit of a step is zero, or odd with `−h ≤ d ≤ h`.
    Does not say: that non-zero digits are `w` apart (true inside a 60-bit piece, not used). -/
theorem wnafStep_digit (h k : Nat) (hh : 0 < h) : DigitOk h (wnafStep h k).1 := by
  unfold DigitOk wnafStep
  by_cases he : k % 2 = 0
  · rw [if_pos he]
    exact Or.inl rfl
  · rw [if_neg he]
    have hdm := Nat.div_add_mod k (2 * h)
    rw [Nat.mul_assoc] at hdm
    have hlt : k % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
    by_cases hm : k % (2 * h) ≤ h
    · rw [if_pos hm]
      show ((k % (2 * h) : Nat) : Int) = 0 ∨ (((k % (2 * h) : Nat) : Int) % 2 = 1
        ∧ -(h : Int) ≤ ((k % (2 * h) : Nat) : Int) ∧ ((k % (2 * h) : Nat) : Int) ≤ (h : Int))
      generalize k % (2 * h) = m at hdm hm hlt ⊢
      generalize h * (k / (2 * h)) = t at hdm
      omega
    · rw [if_neg hm]
      show ((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int) = 0
        ∨ ((((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int)) % 2 = 1
          ∧ -(h : Int) ≤ ((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int)
          ∧ ((k % (2 * h) : Nat) : Int) - ((2 * h : Nat) : Int) ≤ (h : Int))
      generalize k % (2 * h) = m at hdm hm hlt ⊢
      generalize h * (k / (2 * h)) = t at hdm
      omega

/-- Kind: arithmetic lemma.
    Says: `2^(a+b) = 2^a · 2^b` in the integers.
    Does not say: anything about digits. -/
private theorem two_pow_add (a b : Nat) : (2 : Int) ^ (a + b) = 2 ^ a * 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [← Nat.add_assoc, Int.pow_succ, Int.pow_succ, ih, Int.mul_assoc]

/-- Kind: arithmetic lemma.
    Says: the value of two digit lists joined is the first plus the second shifted by the length of the first.
    Does not say: anything about how the digits were made. -/
private theorem evalDigits_append (l1 l2 : List Int) :
    evalDigits (l1 ++ l2) = evalDigits l1 + 2 ^ l1.length * evalDigits l2 := by
  induction l1 with
  | nil => simp [evalDigits]
  | cons a as ih =>
    show a + 2 * evalDigits (as ++ l2) = a + 2 * evalDigits as + 2 ^ (as.length + 1) * evalDigits l2
    rw [ih, Int.pow_succ, Int.mul_add]
    have e : 2 * (2 ^ as.length * evalDigits l2) = 2 ^ as.length * 2 * evalDigits l2 := by
      rw [← Int.mul_assoc, Int.mul_comm 2 (2 ^ as.length)]
    omega

/-- Kind: arithmetic lemma.
    Says: appending a digit adds it with the weight of its position.
    Does not say: anything about how the digits were made. -/
private theorem evalArr_push (a : Array Int) (d : Int) :
    evalArr (a.push d) = evalArr a + 2 ^ a.size * d := by
  have h := evalDigits_append a.toList [d]
  have e : evalDigits [d] = d := by
    show d + 2 * 0 = d
    omega
  rw [e] at h
  first
    | simpa [evalArr] using h
    | simp [evalArr, evalDigits_append, evalDigits]

/-- Kind: arithmetic lemma.
    Says: no digits have the value zero.
    Does not say: anything else. -/
private theorem evalArr_empty : evalArr #[] = 0 := rfl

/-- Kind: arithmetic lemma.
    Says: one recoding step keeps the weighted sum, under the weight `P` of the next digit.
    Does not say: anything about the digit. -/
private theorem step_arith (A P d v' v : Int) (hs : v = d + 2 * v') :
    A + P * d + P * 2 * v' = A + P * v := by
  subst hs
  rw [Int.mul_add]
  have e : P * (2 * v') = P * 2 * v' := (Int.mul_assoc P 2 v').symm
  omega

/-- Kind: arithmetic lemma.
    Says: one 60-digit round keeps the weighted sum.
    Does not say: anything about the digits. -/
private theorem chunk_arith (E A P Q X Y q r Z : Int) (hQ : Q = P * 2 ^ 60)
    (h1 : E + Q * r = A + P * Y) (hX : X = Y + 2 ^ 60 * q) (hZ : Z = q + r) :
    E + Q * Z = A + P * X := by
  subst hQ hX hZ
  rw [Int.mul_add, Int.mul_add]
  have e : P * (2 ^ 60 * q) = P * 2 ^ 60 * q := (Int.mul_assoc P (2 ^ 60) q).symm
  omega

/-- Kind: recoding identity (fixed count).
    Says: `f` steps append exactly `f` digits, and the digits with the rest reconstruct the value.
    Does not say: that the rest is zero. -/
private theorem wnafFixed_spec (h : Nat) : ∀ (f v : Nat) (acc : Array Int),
    (wnafFixed h f v acc).1.size = acc.size + f ∧
      evalArr (wnafFixed h f v acc).1 + 2 ^ (acc.size + f) * ((wnafFixed h f v acc).2 : Int)
        = evalArr acc + 2 ^ acc.size * (v : Int)
  | 0, v, acc => ⟨rfl, rfl⟩
  | f+1, v, acc => by
    have ih := wnafFixed_spec h f (wnafStep h v).2 (acc.push (wnafStep h v).1)
    rw [Array.size_push, evalArr_push] at ih
    have hexp : acc.size + 1 + f = acc.size + (f + 1) := by omega
    rw [hexp, Int.pow_succ] at ih
    have hs := step_arith (evalArr acc) (2 ^ acc.size) (wnafStep h v).1 ((wnafStep h v).2 : Int) (v : Int)
      (wnafStep_eq h v)
    exact ⟨ih.1, ih.2.trans hs⟩

/-- Kind: recoding identity (last piece).
    Says: with a count at least the value, the appended digits reconstruct the value with no rest.
    Does not say: how many digits are appended. -/
private theorem wnafTail_eval (h : Nat) : ∀ (f v : Nat) (acc : Array Int), v ≤ f →
    evalArr (wnafTail h f v acc) = evalArr acc + 2 ^ acc.size * (v : Int)
  | 0, v, acc, hv => by
    have h0 : v = 0 := by omega
    subst h0
    show evalArr acc = evalArr acc + 2 ^ acc.size * ((0 : Nat) : Int)
    first | simp | omega
  | f+1, v, acc, hv => by
    show evalArr (if v = 0 then acc else wnafTail h f (wnafStep h v).2 (acc.push (wnafStep h v).1))
      = evalArr acc + 2 ^ acc.size * (v : Int)
    by_cases h0 : v = 0
    · rw [if_pos h0]
      subst h0
      first | simp | omega
    · rw [if_neg h0]
      have hlt := wnafStep_lt h v (by omega)
      rw [wnafTail_eval h f (wnafStep h v).2 (acc.push (wnafStep h v).1) (by omega),
        evalArr_push, Array.size_push, Int.pow_succ]
      exact step_arith (evalArr acc) (2 ^ acc.size) (wnafStep h v).1 ((wnafStep h v).2 : Int) (v : Int)
        (wnafStep_eq h v)

/-- Kind: recoding identity (all rounds).
    Says: for every count of rounds, the appended digits reconstruct `K + c` at the weight of the position reached.
    Does not say: how many digits are appended. -/
private theorem wnafGo_eval (h : Nat) : ∀ (f K c : Nat) (acc : Array Int),
    evalArr (wnafGo h f K c acc) = evalArr acc + 2 ^ acc.size * ((K + c : Nat) : Int)
  | 0, K, c, acc => wnafTail_eval h (K + c) (K + c) acc (Nat.le_refl _)
  | f+1, K, c, acc => by
    show evalArr (if K < 1152921504606846976 then wnafTail h (K + c) (K + c) acc
      else wnafGo h f (K / 1152921504606846976)
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).2
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).1)
      = evalArr acc + 2 ^ acc.size * ((K + c : Nat) : Int)
    by_cases hK : K < 1152921504606846976
    · rw [if_pos hK]
      exact wnafTail_eval h (K + c) (K + c) acc (Nat.le_refl _)
    · rw [if_neg hK]
      have hf := wnafFixed_spec h 60 (K % 1152921504606846976 + c) acc
      rw [wnafGo_eval h f (K / 1152921504606846976) _ _, hf.1]
      exact chunk_arith _ _ _ _ _ _ ((K / 1152921504606846976 : Nat) : Int) _ _
        (two_pow_add acc.size 60) hf.2 (by omega) (by omega)

/-- Kind: recoding identity.
    Says: the digits of `wnaf h k`, weighted by powers of two from the least significant,
    sum to `k`, for every half-window `h` and every `k`.
    Does not say: anything about a multiplication loop that consumes the digits. -/
theorem wnaf_eval (h k : Nat) : evalArr (wnaf h k) = (k : Int) := by
  unfold wnaf
  rw [wnafGo_eval, evalArr_empty]
  simp

/-- Kind: digit bound (bookkeeping).
    Says: appending a good digit to good digits leaves all digits good.
    Does not say: anything about values. -/
private theorem push_ok (h : Nat) (acc : Array Int) (x : Int) (hacc : ∀ d ∈ acc, DigitOk h d)
    (hx : DigitOk h x) : ∀ d ∈ acc.push x, DigitOk h d := by
  intro d hd
  first
    | rw [Array.mem_push] at hd
    | simp at hd
  cases hd with
  | inl hd => exact hacc d hd
  | inr hd => rw [hd]; exact hx

/-- Kind: digit bound (fixed count).
    Says: the digits appended by `wnafFixed` are zero or odd and within the window.
    Does not say: anything about values. -/
private theorem wnafFixed_digits (h : Nat) (hh : 0 < h) : ∀ (f v : Nat) (acc : Array Int),
    (∀ d ∈ acc, DigitOk h d) → ∀ d ∈ (wnafFixed h f v acc).1, DigitOk h d
  | 0, _, _, hacc => hacc
  | f+1, v, acc, hacc =>
    wnafFixed_digits h hh f (wnafStep h v).2 (acc.push (wnafStep h v).1)
      (push_ok h acc _ hacc (wnafStep_digit h v hh))

/-- Kind: digit bound (last piece).
    Says: the digits appended by `wnafTail` are zero or odd and within the window.
    Does not say: anything about values. -/
private theorem wnafTail_digits (h : Nat) (hh : 0 < h) : ∀ (f v : Nat) (acc : Array Int),
    (∀ d ∈ acc, DigitOk h d) → ∀ d ∈ wnafTail h f v acc, DigitOk h d
  | 0, _, _, hacc => hacc
  | f+1, v, acc, hacc => by
    show ∀ d ∈ (if v = 0 then acc else wnafTail h f (wnafStep h v).2 (acc.push (wnafStep h v).1)),
      DigitOk h d
    by_cases h0 : v = 0
    · rw [if_pos h0]; exact hacc
    · rw [if_neg h0]
      exact wnafTail_digits h hh f (wnafStep h v).2 (acc.push (wnafStep h v).1)
        (push_ok h acc _ hacc (wnafStep_digit h v hh))

/-- Kind: digit bound (all rounds).
    Says: the digits appended by `wnafGo` are zero or odd and within the window.
    Does not say: anything about values. -/
private theorem wnafGo_digits (h : Nat) (hh : 0 < h) : ∀ (f K c : Nat) (acc : Array Int),
    (∀ d ∈ acc, DigitOk h d) → ∀ d ∈ wnafGo h f K c acc, DigitOk h d
  | 0, K, c, acc, hacc => wnafTail_digits h hh (K + c) (K + c) acc hacc
  | f+1, K, c, acc, hacc => by
    show ∀ d ∈ (if K < 1152921504606846976 then wnafTail h (K + c) (K + c) acc
      else wnafGo h f (K / 1152921504606846976)
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).2
        (wnafFixed h 60 (K % 1152921504606846976 + c) acc).1), DigitOk h d
    by_cases hK : K < 1152921504606846976
    · rw [if_pos hK]; exact wnafTail_digits h hh (K + c) (K + c) acc hacc
    · rw [if_neg hK]
      exact wnafGo_digits h hh f _ _ _ (wnafFixed_digits h hh 60 _ acc hacc)

/-- Kind: digit bound.
    Says: for a positive half-window `h`, every digit of `wnaf h k` is zero, or odd with
    absolute value at most `h`.
    Does not say: how many digits there are, or how many are non-zero. -/
theorem wnaf_digits (h k : Nat) (hh : 0 < h) : ∀ d ∈ wnaf h k, DigitOk h d :=
  wnafGo_digits h hh _ _ _ _ (by intro d hd; simp at hd)

/-- Kind: digit bound.
    Says: for a positive even half-window `h`, every non-zero digit of `wnaf h k` is odd and
    strictly inside `(−h, h)`, so `|d| / 2` is an index below `h / 2` into a table of the
    odd multiples `P, 3P, …, (h−1)P`.
    Does not say: that the loops below only ever index inside the table for other `h`
    (they read with a default, so an index outside is not a trap). -/
theorem wnaf_digits_even (h k : Nat) (hh : 0 < h) (heven : h % 2 = 0) :
    ∀ d ∈ wnaf h k, d = 0 ∨ (d % 2 = 1 ∧ -(h : Int) < d ∧ d < (h : Int)) := by
  intro d hd
  have hok := wnaf_digits h k hh d hd
  unfold DigitOk at hok
  omega

/-! ### Table-driven loops over any doubling and addition -/

section Generic

variable {P : Type}

@[specialize] def oddMultiplesLoop (add : P → P → P) (twice : P) : Nat → P → Array P → Array P
  | 0, _, acc => acc
  | c+1, cur, acc => oddMultiplesLoop add twice c (add cur twice) (acc.push cur)

/-- `[1]p, [3]p, …, [2·count − 1]p`. -/
@[specialize] def oddMultiples (dbl : P → P) (add : P → P → P) (p : P) (count : Nat) : Array P :=
  oddMultiplesLoop add (dbl p) count p #[]

/-- `acc + [d]p` for a digit `d` and the table of odd multiples of `p`. -/
@[specialize] def addDigit (add : P → P → P) (neg : P → P) (zero : P) (table : Array P) (acc : P)
    (d : Int) : P :=
  if d = 0 then acc
  else if 0 < d then add acc (table.getD (d.toNat / 2) zero)
  else add acc (neg (table.getD ((-d).toNat / 2) zero))

/-- Digits from index `i − 1` down to 0: double, then add the digit's multiple. -/
@[specialize] def windowLoop (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P)
    (table : Array P) (ds : Array Int) : Nat → P → P
  | 0, acc => acc
  | i+1, acc => windowLoop dbl add neg zero table ds i (addDigit add neg zero table (dbl acc) (ds.getD i 0))

@[specialize] def windowRun (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P) (table : Array P)
    (ds : Array Int) : P :=
  windowLoop dbl add neg zero table ds ds.size zero

/-- `[k]p` with half-window `h`: a table of `(h+1)/2` odd multiples, one doubling per digit
    and one addition per non-zero digit. -/
@[specialize] def windowMul (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P) (h k : Nat) (p : P) : P :=
  windowRun dbl add neg zero (oddMultiples dbl add p ((h + 1) / 2)) (wnaf h k)

@[specialize] def strausLoop (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P)
    (t1 t2 : Array P) (d1 d2 : Array Int) : Nat → P → P
  | 0, acc => acc
  | i+1, acc =>
    strausLoop dbl add neg zero t1 t2 d1 d2 i
      (addDigit add neg zero t2 (addDigit add neg zero t1 (dbl acc) (d1.getD i 0)) (d2.getD i 0))

@[specialize] def strausRun (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P) (t1 t2 : Array P)
    (d1 d2 : Array Int) : P :=
  strausLoop dbl add neg zero t1 t2 d1 d2 (max d1.size d2.size) zero

/-- `[k1]p1 + [k2]p2` with one shared doubling chain (Straus) and half-window `h` for both. -/
@[specialize] def strausMul (dbl : P → P) (add : P → P → P) (neg : P → P) (zero : P) (h k1 : Nat) (p1 : P)
    (k2 : Nat) (p2 : P) : P :=
  strausRun dbl add neg zero (oddMultiples dbl add p1 ((h + 1) / 2)) (oddMultiples dbl add p2 ((h + 1) / 2))
    (wnaf h k1) (wnaf h k2)

end Generic

/-! ### The `a = 0` curves of `Curve.lean` -/

variable {F : Type}

@[inline] def negPoint (O : FieldOps F) (p : JPoint F) : JPoint F := ⟨p.x, O.neg p.y, p.z⟩

/-- `[k]p` on a curve `y² = x³ + b`, half-window `h` (`h = 8` is width 4, `h = 16` width 5). -/
@[specialize] def curveMul (O : FieldOps F) (h k : Nat) (p : JPoint F) : JPoint F :=
  windowMul (Curve.double O) (Curve.add O) (negPoint O) (Curve.infinity O) h k p

/-- `[k1]p1 + [k2]p2` on a curve `y² = x³ + b`, half-window `h`. -/
@[specialize] def curveMul2 (O : FieldOps F) (h k1 : Nat) (p1 : JPoint F) (k2 : Nat) (p2 : JPoint F) :
    JPoint F :=
  strausMul (Curve.double O) (Curve.add O) (negPoint O) (Curve.infinity O) h k1 p1 k2 p2

/-- Kind: loop bound.
    Says: the single-scalar loop runs once per digit and the two-scalar loop once per digit
    of the longer recoding (by definition: both recurse on that count).
    Does not say: a bound on the number of digits in terms of the bit length (tested: at most
    one more than the bit length for a power-of-two `h`). -/
theorem curveMul_eq (O : FieldOps F) (h k : Nat) (p : JPoint F) :
    curveMul O h k p = windowLoop (Curve.double O) (Curve.add O) (negPoint O) (Curve.infinity O)
      (oddMultiples (Curve.double O) (Curve.add O) p ((h + 1) / 2)) (wnaf h k) (wnaf h k).size
      (Curve.infinity O) := rfl

/-! ### Guards (tests): recoding, and the loops against `Curve.mul` and `Curve.mul2` -/

private def tp : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
private def tn : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
private def tO : FieldOps Nat := Fp.ops tp
private def tg : JPoint Nat := Curve.ofAffine tO
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
private def tq : JPoint Nat := Curve.mul tO 0x1234567890abcdef1234567890abcdef tg

private def scalars : List Nat :=
  [0, 1, 2, 3, 7, 8, 15, 16, 17, 255, 256, 2 ^ 60 - 1, 2 ^ 60, 2 ^ 60 + 1, 2 ^ 120 - 1, 2 ^ 120, 2 ^ 128 - 1,
   2 ^ 128, 2 ^ 180 + 2 ^ 60 - 1, 2 ^ 255, 2 ^ 256 - 1, tn - 1, tn, tn + 1,
   0xdeadbeefcafebabe0123456789abcdeffedcba9876543210aaaaaaaa55555555,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000001]

private def digitOk (h : Nat) (d : Int) : Bool := d == 0 || (d % 2 == 1 && -(h : Int) ≤ d && d ≤ (h : Int))

#guard scalars.all fun k => [1, 2, 4, 8, 16, 128].all fun h =>
  evalArr (wnaf h k) == (k : Int) && (wnaf h k).all (digitOk h) && (wnaf h k).size ≤ Nat.log2 k + 2
-- The last digit is never zero, so the loops do no leading doublings of the point at infinity.
#guard scalars.all fun k => k == 0 || (wnaf 16 k).back? != some 0
#guard wnaf 16 0 == #[] && wnaf 16 1 == #[1] && wnaf 16 15 == #[15] && wnaf 16 17 == #[-15, 0, 0, 0, 0, 1]
#guard wnaf 2 7 == #[-1, 0, 0, 1]
#guard scalars.all fun k => [1, 8, 16].all fun h => Curve.same tO (curveMul tO h k tg) (Curve.mul tO k tg)
#guard [(0, 0), (1, 0), (0, 1), (1, 1), (tn - 1, 1), (1, tn - 1), (tn - 0x1234567890abcdef1234567890abcdef, 1),
    (0x1234567890abcdef1234567890abcdef, tn - 1), (2 ^ 255 + 12345, 2 ^ 254 + 54321), (2 ^ 128 - 1, 2 ^ 60)].all
  fun (k1, k2) => [1, 8, 16].all fun h =>
    Curve.same tO (curveMul2 tO h k1 tg k2 tq) (Curve.mul2 tO k1 tg k2 tq)

#print axioms wnafStep_eq
#print axioms wnafStep_lt
#print axioms wnafStep_digit
#print axioms two_pow_add
#print axioms evalDigits_append
#print axioms evalArr_push
#print axioms evalArr_empty
#print axioms step_arith
#print axioms chunk_arith
#print axioms wnafFixed_spec
#print axioms wnafTail_eval
#print axioms wnafGo_eval
#print axioms wnaf_eval
#print axioms push_ok
#print axioms wnafFixed_digits
#print axioms wnafTail_digits
#print axioms wnafGo_digits
#print axioms wnaf_digits
#print axioms wnaf_digits_even
#print axioms curveMul_eq

end EVMCleanroom.Precompiles.ScalarMul
