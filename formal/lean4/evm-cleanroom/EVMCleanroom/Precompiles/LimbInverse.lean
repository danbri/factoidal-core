import EVMCleanroom.Precompiles.Montgomery

/-!
# Field inversion on limbs

`Mont256.inv` and `Mont384.inv` go through the extended Euclid of `Fp.inv` on
`Nat` (36 µs and 56 µs measured on Linux CI). Here the inverse of a value in
Montgomery form is computed on machine words with Kaliski's method (Kaliski,
"The Montgomery inverse and its applications", 1995): the *almost inverse*
loop keeps `u, v, r, s` with `u·s + v·r = N` and halves `u` or `v` in every
step; when `v` reaches zero after `k` steps, `N − r = a⁻¹·2^k (mod N)`. The
power of two is then removed by one Montgomery multiplication by `2^(2m − k)`
(`m` the limb width in bits, after modular doublings until `k > m`), and one
more multiplication by `R²` restores the Montgomery form.

The loop state is passed as separate `UInt64` arguments of a tail-recursive
function, so a step allocates nothing.

`invFast` returns the candidate only if `a · candidate = 1` holds in the field
(one multiplication); otherwise it returns the Euclid result. So for a
non-zero `a` it returns either a value that passed that check or the value of
`inv`.

Requirement: the modulus is below `2^(m−1)` (values below `2N` must fit the
limbs). This holds for the alt_bn128 base field (254 bits in 256) and the
BLS12-381 base field (381 bits in 384), not for the secp256k1 group order.

Proved: zero maps to zero; a non-zero result is the checked candidate or the
value of `inv`. Not proved: that the candidate always passes (tested: the
guards of the curve modules and `evm-blsops` compare `invCandidate` with
`Fp.inv` on edge values and a pseudo-random walk, and require that it is
never rejected).

Variable-time: the number of steps depends on the value.
-/

set_option linter.unusedVariables false

namespace EVMCleanroom.Precompiles

open Limb

/-- Kaliski's almost-inverse loop on 4 limbs per value, all in machine words (no allocation
    per step). `k` counts the steps; the result is `(k, r)` at the first `v = 0`. -/
def Mont256.almostLoop (fuel k : Nat) (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 s0 s1 s2 s3 : UInt64) : Nat × U256 :=
  match fuel with
  | 0 => (k, ⟨r0, r1, r2, r3⟩)
  | fuel+1 =>
    if (v0 ||| v1 ||| v2 ||| v3) == 0 then (k, ⟨r0, r1, r2, r3⟩)
    else if u0 &&& 1 == 0 then
      Mont256.almostLoop fuel (k + 1) ((u0 >>> 1) ||| (u1 <<< 63)) ((u1 >>> 1) ||| (u2 <<< 63)) ((u2 >>> 1) ||| (u3 <<< 63)) (u3 >>> 1)
        v0 v1 v2 v3 r0 r1 r2 r3
        (s0 <<< 1) ((s1 <<< 1) ||| (s0 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63)) ((s3 <<< 1) ||| (s2 >>> 63))
    else if v0 &&& 1 == 0 then
      Mont256.almostLoop fuel (k + 1) u0 u1 u2 u3
        ((v0 >>> 1) ||| (v1 <<< 63)) ((v1 >>> 1) ||| (v2 <<< 63)) ((v2 >>> 1) ||| (v3 <<< 63)) (v3 >>> 1)
        (r0 <<< 1) ((r1 <<< 1) ||| (r0 >>> 63)) ((r2 <<< 1) ||| (r1 >>> 63)) ((r3 <<< 1) ||| (r2 >>> 63))
        s0 s1 s2 s3
    else
      let w := sbb v0 u0 0; let d0 := w.2; let c := w.1
      let w := sbb v1 u1 c; let d1 := w.2; let c := w.1
      let w := sbb v2 u2 c; let d2 := w.2; let c := w.1
      let w := sbb v3 u3 c; let d3 := w.2; let c := w.1
      if c != 0 then
        let w := sbb u0 v0 0; let e0 := w.2; let c := w.1
        let w := sbb u1 v1 c; let e1 := w.2; let c := w.1
        let w := sbb u2 v2 c; let e2 := w.2; let c := w.1
        let w := sbb u3 v3 c; let e3 := w.2; let c := w.1
        let w := adc r0 s0 0; let t0 := w.2; let c := w.1
        let w := adc r1 s1 c; let t1 := w.2; let c := w.1
        let w := adc r2 s2 c; let t2 := w.2; let c := w.1
        let w := adc r3 s3 c; let t3 := w.2; let c := w.1
        Mont256.almostLoop fuel (k + 1) ((e0 >>> 1) ||| (e1 <<< 63)) ((e1 >>> 1) ||| (e2 <<< 63)) ((e2 >>> 1) ||| (e3 <<< 63)) (e3 >>> 1)
          v0 v1 v2 v3 t0 t1 t2 t3
          (s0 <<< 1) ((s1 <<< 1) ||| (s0 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63)) ((s3 <<< 1) ||| (s2 >>> 63))
      else
        let w := adc s0 r0 0; let t0 := w.2; let c := w.1
        let w := adc s1 r1 c; let t1 := w.2; let c := w.1
        let w := adc s2 r2 c; let t2 := w.2; let c := w.1
        let w := adc s3 r3 c; let t3 := w.2; let c := w.1
        Mont256.almostLoop fuel (k + 1) u0 u1 u2 u3
          ((d0 >>> 1) ||| (d1 <<< 63)) ((d1 >>> 1) ||| (d2 <<< 63)) ((d2 >>> 1) ||| (d3 <<< 63)) (d3 >>> 1)
          (r0 <<< 1) ((r1 <<< 1) ||| (r0 >>> 63)) ((r2 <<< 1) ||| (r1 >>> 63)) ((r3 <<< 1) ||| (r2 >>> 63))
          t0 t1 t2 t3

/-- `fuel` modular doublings, counting them in `k`. -/
def Mont256.doubleUp (N : U256) : Nat → Nat → U256 → Nat × U256
  | 0, k, x => (k, x)
  | fuel+1, k, x => Mont256.doubleUp N fuel (k + 1) (U256.addMod N x x)

/-- One Montgomery multiplication as a plain function. -/
def Mont256.mulPlain (M : Mont256) (a b : U256) : U256 := Mont256.mul M a b

/-- The inverse of a non-zero stored value by Kaliski's method, not verified. The modulus must
    be below `2^255` (the loop holds values below twice the modulus in 4 limbs). -/
def Mont256.invCandidate (M : Mont256) (a : U256) : U256 :=
  let found := Mont256.almostLoop 514 0 M.n.l0 M.n.l1 M.n.l2 M.n.l3
    a.l0 a.l1 a.l2 a.l3 0 0 0 0 1 0 0 0
  let x := U256.negMod M.n (U256.condSub M.n 0 found.2)
  let up := Mont256.doubleUp M.n (257 - found.1) found.1 x
  Mont256.mulPlain M (Mont256.mulPlain M up.2 (U256.ofNat (2 ^ (512 - up.1)))) M.r2

/-- Inverse of a stored value; zero maps to zero. The candidate of Kaliski's method is
    used only after the check `a · candidate = 1`; otherwise the `Nat` Euclid of `Mont256.inv`
    answers. Variable-time. -/
def Mont256.invFast (M : Mont256) (a : U256) : U256 :=
  if a.isZero then a
  else
    let candidate := Mont256.invCandidate M a
    if U256.beq (Mont256.mulPlain M a candidate) M.one then candidate else Mont256.inv M a

/-- Kaliski's almost-inverse loop on 6 limbs per value, all in machine words (no allocation
    per step). `k` counts the steps; the result is `(k, r)` at the first `v = 0`. -/
def Mont384.almostLoop (fuel k : Nat) (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 r0 r1 r2 r3 r4 r5 s0 s1 s2 s3 s4 s5 : UInt64) : Nat × U384 :=
  match fuel with
  | 0 => (k, ⟨r0, r1, r2, r3, r4, r5⟩)
  | fuel+1 =>
    if (v0 ||| v1 ||| v2 ||| v3 ||| v4 ||| v5) == 0 then (k, ⟨r0, r1, r2, r3, r4, r5⟩)
    else if u0 &&& 1 == 0 then
      Mont384.almostLoop fuel (k + 1) ((u0 >>> 1) ||| (u1 <<< 63)) ((u1 >>> 1) ||| (u2 <<< 63)) ((u2 >>> 1) ||| (u3 <<< 63)) ((u3 >>> 1) ||| (u4 <<< 63)) ((u4 >>> 1) ||| (u5 <<< 63)) (u5 >>> 1)
        v0 v1 v2 v3 v4 v5 r0 r1 r2 r3 r4 r5
        (s0 <<< 1) ((s1 <<< 1) ||| (s0 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63)) ((s3 <<< 1) ||| (s2 >>> 63)) ((s4 <<< 1) ||| (s3 >>> 63)) ((s5 <<< 1) ||| (s4 >>> 63))
    else if v0 &&& 1 == 0 then
      Mont384.almostLoop fuel (k + 1) u0 u1 u2 u3 u4 u5
        ((v0 >>> 1) ||| (v1 <<< 63)) ((v1 >>> 1) ||| (v2 <<< 63)) ((v2 >>> 1) ||| (v3 <<< 63)) ((v3 >>> 1) ||| (v4 <<< 63)) ((v4 >>> 1) ||| (v5 <<< 63)) (v5 >>> 1)
        (r0 <<< 1) ((r1 <<< 1) ||| (r0 >>> 63)) ((r2 <<< 1) ||| (r1 >>> 63)) ((r3 <<< 1) ||| (r2 >>> 63)) ((r4 <<< 1) ||| (r3 >>> 63)) ((r5 <<< 1) ||| (r4 >>> 63))
        s0 s1 s2 s3 s4 s5
    else
      let w := sbb v0 u0 0; let d0 := w.2; let c := w.1
      let w := sbb v1 u1 c; let d1 := w.2; let c := w.1
      let w := sbb v2 u2 c; let d2 := w.2; let c := w.1
      let w := sbb v3 u3 c; let d3 := w.2; let c := w.1
      let w := sbb v4 u4 c; let d4 := w.2; let c := w.1
      let w := sbb v5 u5 c; let d5 := w.2; let c := w.1
      if c != 0 then
        let w := sbb u0 v0 0; let e0 := w.2; let c := w.1
        let w := sbb u1 v1 c; let e1 := w.2; let c := w.1
        let w := sbb u2 v2 c; let e2 := w.2; let c := w.1
        let w := sbb u3 v3 c; let e3 := w.2; let c := w.1
        let w := sbb u4 v4 c; let e4 := w.2; let c := w.1
        let w := sbb u5 v5 c; let e5 := w.2; let c := w.1
        let w := adc r0 s0 0; let t0 := w.2; let c := w.1
        let w := adc r1 s1 c; let t1 := w.2; let c := w.1
        let w := adc r2 s2 c; let t2 := w.2; let c := w.1
        let w := adc r3 s3 c; let t3 := w.2; let c := w.1
        let w := adc r4 s4 c; let t4 := w.2; let c := w.1
        let w := adc r5 s5 c; let t5 := w.2; let c := w.1
        Mont384.almostLoop fuel (k + 1) ((e0 >>> 1) ||| (e1 <<< 63)) ((e1 >>> 1) ||| (e2 <<< 63)) ((e2 >>> 1) ||| (e3 <<< 63)) ((e3 >>> 1) ||| (e4 <<< 63)) ((e4 >>> 1) ||| (e5 <<< 63)) (e5 >>> 1)
          v0 v1 v2 v3 v4 v5 t0 t1 t2 t3 t4 t5
          (s0 <<< 1) ((s1 <<< 1) ||| (s0 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63)) ((s3 <<< 1) ||| (s2 >>> 63)) ((s4 <<< 1) ||| (s3 >>> 63)) ((s5 <<< 1) ||| (s4 >>> 63))
      else
        let w := adc s0 r0 0; let t0 := w.2; let c := w.1
        let w := adc s1 r1 c; let t1 := w.2; let c := w.1
        let w := adc s2 r2 c; let t2 := w.2; let c := w.1
        let w := adc s3 r3 c; let t3 := w.2; let c := w.1
        let w := adc s4 r4 c; let t4 := w.2; let c := w.1
        let w := adc s5 r5 c; let t5 := w.2; let c := w.1
        Mont384.almostLoop fuel (k + 1) u0 u1 u2 u3 u4 u5
          ((d0 >>> 1) ||| (d1 <<< 63)) ((d1 >>> 1) ||| (d2 <<< 63)) ((d2 >>> 1) ||| (d3 <<< 63)) ((d3 >>> 1) ||| (d4 <<< 63)) ((d4 >>> 1) ||| (d5 <<< 63)) (d5 >>> 1)
          (r0 <<< 1) ((r1 <<< 1) ||| (r0 >>> 63)) ((r2 <<< 1) ||| (r1 >>> 63)) ((r3 <<< 1) ||| (r2 >>> 63)) ((r4 <<< 1) ||| (r3 >>> 63)) ((r5 <<< 1) ||| (r4 >>> 63))
          t0 t1 t2 t3 t4 t5

/-- `fuel` modular doublings, counting them in `k`. -/
def Mont384.doubleUp (N : U384) : Nat → Nat → U384 → Nat × U384
  | 0, k, x => (k, x)
  | fuel+1, k, x => Mont384.doubleUp N fuel (k + 1) (U384.addMod N x x)

/-- One Montgomery multiplication as a plain function. -/
def Mont384.mulPlain (M : Mont384) (a b : U384) : U384 := Mont384.mul M a b

/-- The inverse of a non-zero stored value by Kaliski's method, not verified. The modulus must
    be below `2^383` (the loop holds values below twice the modulus in 6 limbs). -/
def Mont384.invCandidate (M : Mont384) (a : U384) : U384 :=
  let found := Mont384.almostLoop 770 0 M.n.l0 M.n.l1 M.n.l2 M.n.l3 M.n.l4 M.n.l5
    a.l0 a.l1 a.l2 a.l3 a.l4 a.l5 0 0 0 0 0 0 1 0 0 0 0 0
  let x := U384.negMod M.n (U384.condSub M.n 0 found.2)
  let up := Mont384.doubleUp M.n (385 - found.1) found.1 x
  Mont384.mulPlain M (Mont384.mulPlain M up.2 (U384.ofNat (2 ^ (768 - up.1)))) M.r2

/-- Inverse of a stored value; zero maps to zero. The candidate of Kaliski's method is
    used only after the check `a · candidate = 1`; otherwise the `Nat` Euclid of `Mont384.inv`
    answers. Variable-time. -/
def Mont384.invFast (M : Mont384) (a : U384) : U384 :=
  if a.isZero then a
  else
    let candidate := Mont384.invCandidate M a
    if U384.beq (Mont384.mulPlain M a candidate) M.one then candidate else Mont384.inv M a

/-- Kind: totality on zero and provenance of the result.
    Says: the inverse of zero is zero; for any other value the result is either a candidate
    that passed the check `a · candidate = 1` (as computed by `mul`) or the value of `inv`.
    Does not say: `inv` or `mul` are correct, or that the candidate always passes. -/
theorem Mont256.invFast_spec (M : Mont256) (a : U256) :
    (a.isZero = true → Mont256.invFast M a = a) ∧
    (a.isZero = false →
      (U256.beq (Mont256.mulPlain M a (Mont256.invFast M a)) M.one = true ∨ Mont256.invFast M a = Mont256.inv M a)) := by
  constructor
  · intro h; simp [Mont256.invFast, h]
  · intro h
    by_cases hc : U256.beq (Mont256.mulPlain M a (Mont256.invCandidate M a)) M.one = true
    · left
      have hEq : Mont256.invFast M a = Mont256.invCandidate M a := by simp [Mont256.invFast, h, hc]
      rw [hEq]; exact hc
    · right
      simp [Mont256.invFast, h, hc]

theorem Mont384.invFast_spec (M : Mont384) (a : U384) :
    (a.isZero = true → Mont384.invFast M a = a) ∧
    (a.isZero = false →
      (U384.beq (Mont384.mulPlain M a (Mont384.invFast M a)) M.one = true ∨ Mont384.invFast M a = Mont384.inv M a)) := by
  constructor
  · intro h; simp [Mont384.invFast, h]
  · intro h
    by_cases hc : U384.beq (Mont384.mulPlain M a (Mont384.invCandidate M a)) M.one = true
    · left
      have hEq : Mont384.invFast M a = Mont384.invCandidate M a := by simp [Mont384.invFast, h, hc]
      rw [hEq]; exact hc
    · right
      simp [Mont384.invFast, h, hc]

#print axioms Mont256.invFast_spec
#print axioms Mont384.invFast_spec

end EVMCleanroom.Precompiles
