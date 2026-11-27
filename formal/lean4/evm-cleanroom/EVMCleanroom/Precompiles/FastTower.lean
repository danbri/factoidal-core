import EVMCleanroom.Precompiles.Tower

/-!
# The pairing tower over any base-field representation

`Fq6 K = K[v]/(v³ − ξ)` and `Fq12 K = Fq6[w]/(w² − v)`, written once over a dictionary
`QuadOps K` of the quadratic extension `K = Fp[u]/(u² + 1)`. Two kinds of `K` are provided:
the generic `Fq2 F` over any `FieldOps F` dictionary (here, `Fq2.quadOps`), and the flat
limb forms `Quad256` and `Quad384` of `QuadLimb.lean` (one object per element, lazy
reduction), which the pairing precompiles use for alt_bn128 and BLS12-381. Every function
on a hot path is marked `@[specialize]`, so a call with a constant dictionary is compiled
to direct calls of that field's operations.

The definition and differential oracle stays `Tower.lean` (six `Fp2` coefficients of
`1, w, …, w⁵` over `Nat`, with `w⁶ = ξ`). The correspondence is `v = w²`: the element
`(a₀ + a₁v + a₂v²) + (b₀ + b₁v + b₂v²)·w` here is the flat `(a₀, b₀, a₁, b₁, a₂, b₂)` there
(`Fq12.toFlat`, `Fq12.ofFlat`).

Operation counts, in base-field multiplications (`M`):

* `Fq2.mul` 3 M (Karatsuba), `Fq2.sqr` 2 M (`(a₀+a₁)(a₀−a₁)`, `2a₀a₁`);
* multiplication by `ξ` by additions only (`ξ = 9 + u` or `ξ = 1 + u`);
* `Fq6.mul` 6 `Fq2` products (Karatsuba) = 18 M; `Fq12.mul` 3 `Fq6` products = 54 M
  (the flat schoolbook form has 36 `Fq2` products, so the tower is kept);
* `Fq12.sqr` 2 `Fq6` products = 36 M (complex squaring);
* `Fq12.cyclotomicSqr` 9 `Fq2` squarings = 18 M, valid only in the cyclotomic subgroup
  (elements `g` with `g^(p⁴ − p² + 1) = 1`, where every value is after the easy part of the
  final exponentiation): Granger and Scott, "Faster squaring in the cyclotomic subgroup of
  sixth degree extensions", PKC 2010. With `s = w³` (`s² = ξ`), `Fq4 = Fq2[s]` and
  `g = A + B·w + C·w²` (`A, B, C` in `Fq4`), `g² = (3A² − 2Ā) + (3s·C² + 2B̄)·w + (3B² − 2C̄)·w²`;
* a line of the Miller loop has three non-zero `Fq2` coefficients out of six:
  `Fq12.mulLineD` (`l₀ + l₁w + l₂w³`, D-type twist) and `Fq12.mulLineM` (`l₀ + l₁w² + l₂w³`,
  M-type twist) take 13 `Fq2` products = 39 M;
* `Fq12.inv` goes down the tower (`Fq12` → `Fq6` → `Fq2` → `F`) with one base-field inversion.

Nothing here is proved: no field law is available for an arbitrary dictionary, and none is
proved for the limb fields beyond their refinement of the `Nat` operations. Every operation
is compared with `Tower.lean` by build-time guards in the curve modules (`BN254Pairing`,
`BLS12381Pairing`) and by the run-time differential check `evm-pairingperf`.

Nothing is constant-time: the precompiles handle public data only.
-/

namespace EVMCleanroom.Precompiles

/-- An element `c0 + c1·u` of `F[u]/(u² + 1)`. -/
structure Fq2 (F : Type) where
  c0 : F
  c1 : F

namespace Fq2

variable {F : Type}

@[inline] def zero (O : FieldOps F) : Fq2 F := ⟨O.zero, O.zero⟩
@[inline] def one (O : FieldOps F) : Fq2 F := ⟨O.one, O.zero⟩

@[specialize] def add (O : FieldOps F) (a b : Fq2 F) : Fq2 F := ⟨O.add a.c0 b.c0, O.add a.c1 b.c1⟩
@[specialize] def sub (O : FieldOps F) (a b : Fq2 F) : Fq2 F := ⟨O.sub a.c0 b.c0, O.sub a.c1 b.c1⟩
@[specialize] def neg (O : FieldOps F) (a : Fq2 F) : Fq2 F := ⟨O.neg a.c0, O.neg a.c1⟩
@[specialize] def conj (O : FieldOps F) (a : Fq2 F) : Fq2 F := ⟨a.c0, O.neg a.c1⟩
@[specialize] def double (O : FieldOps F) (a : Fq2 F) : Fq2 F := ⟨O.add a.c0 a.c0, O.add a.c1 a.c1⟩

/-- Karatsuba: `(a₀b₀ − a₁b₁) + ((a₀+a₁)(b₀+b₁) − a₀b₀ − a₁b₁)·u`, three base multiplications. -/
@[specialize] def mul (O : FieldOps F) (a b : Fq2 F) : Fq2 F :=
  let v0 := O.mul a.c0 b.c0
  let v1 := O.mul a.c1 b.c1
  let s := O.mul (O.add a.c0 a.c1) (O.add b.c0 b.c1)
  ⟨O.sub v0 v1, O.sub (O.sub s v0) v1⟩

/-- `(a₀+a₁)(a₀−a₁) + 2a₀a₁·u`, two base multiplications. -/
@[specialize] def sqr (O : FieldOps F) (a : Fq2 F) : Fq2 F :=
  let m := O.mul a.c0 a.c1
  ⟨O.mul (O.add a.c0 a.c1) (O.sub a.c0 a.c1), O.add m m⟩

/-- Multiply both coordinates by a base-field element. -/
@[specialize] def scale (O : FieldOps F) (k : F) (a : Fq2 F) : Fq2 F := ⟨O.mul k a.c0, O.mul k a.c1⟩

/-- Multiply by `ξ = 9 + u` (`nine`) or by `ξ = 1 + u`, by additions only. -/
@[specialize] def mulXi (O : FieldOps F) (nine : Bool) (a : Fq2 F) : Fq2 F :=
  if nine then
    let x2 := O.add a.c0 a.c0
    let x4 := O.add x2 x2
    let x8 := O.add x4 x4
    let y2 := O.add a.c1 a.c1
    let y4 := O.add y2 y2
    let y8 := O.add y4 y4
    ⟨O.sub (O.add x8 a.c0) a.c1, O.add (O.add y8 a.c1) a.c0⟩
  else ⟨O.sub a.c0 a.c1, O.add a.c0 a.c1⟩

/-- Inverse through the norm `a₀² + a₁²`: one base-field inversion. Zero maps to zero. -/
@[specialize] def inv (O : FieldOps F) (a : Fq2 F) : Fq2 F :=
  let n := O.inv (O.add (O.sqr a.c0) (O.sqr a.c1))
  ⟨O.mul a.c0 n, O.neg (O.mul a.c1 n)⟩

@[specialize] def isZero (O : FieldOps F) (a : Fq2 F) : Bool := O.isZero a.c0 && O.isZero a.c1
@[specialize] def eq (O : FieldOps F) (a b : Fq2 F) : Bool := O.eq a.c0 b.c0 && O.eq a.c1 b.c1

/-- Change of representation, coordinate by coordinate (decoding, guards). -/
def map {G : Type} (f : F → G) (a : Fq2 F) : Fq2 G := ⟨f a.c0, f a.c1⟩

/-- To the `Nat` representation of `Field.lean`. -/
def toNat (toNat : F → Nat) (a : Fq2 F) : Fp2 := ⟨toNat a.c0, toNat a.c1⟩
/-- From the `Nat` representation of `Field.lean`. -/
def ofNat (ofNat : Nat → F) (a : Fp2) : Fq2 F := ⟨ofNat a.c0, ofNat a.c1⟩

end Fq2

/-- The operations of a quadratic extension `K = Fp[u]/(u² + 1)` that the tower is written
    over. `mulXi` multiplies by the non-residue `ξ` of the curve, `mulReal a b` multiplies
    `a` by the real part of `b` (line coefficients times a coordinate of a `G1` point),
    `inv` maps zero to zero. -/
class QuadOps (K : Type) where
  zero : K
  one : K
  add : K → K → K
  sub : K → K → K
  neg : K → K
  double : K → K
  mul : K → K → K
  sqr : K → K
  conj : K → K
  mulXi : K → K
  mulReal : K → K → K
  inv : K → K
  isZero : K → Bool
  eq : K → K → Bool

/-- The generic quadratic extension over a `FieldOps` dictionary as a `QuadOps` dictionary;
    `nine` selects `ξ = 9 + u`, otherwise `ξ = 1 + u`. -/
def Fq2.quadOps {F : Type} (O : FieldOps F) (nine : Bool) : QuadOps (Fq2 F) where
  zero := Fq2.zero O
  one := Fq2.one O
  add := Fq2.add O
  sub := Fq2.sub O
  neg := Fq2.neg O
  double := Fq2.double O
  mul := Fq2.mul O
  sqr := Fq2.sqr O
  conj := Fq2.conj O
  mulXi := Fq2.mulXi O nine
  mulReal := fun a b => Fq2.scale O b.c0 a
  inv := Fq2.inv O
  isZero := Fq2.isZero O
  eq := Fq2.eq O

/-- The Frobenius constants `frobᵢ = ξ^(i·(p−1)/6)` for `i = 1 … 5`. -/
structure TowerParams (K : Type) where
  frob1 : K
  frob2 : K
  frob3 : K
  frob4 : K
  frob5 : K

/-- An element `c0 + c1·v + c2·v²` of `K[v]/(v³ − ξ)`. -/
structure Fq6 (K : Type) where
  c0 : K
  c1 : K
  c2 : K

namespace Fq6

variable {K : Type}

@[inline] def zero (Q : QuadOps K) : Fq6 K := ⟨Q.zero, Q.zero, Q.zero⟩
@[inline] def one (Q : QuadOps K) : Fq6 K := ⟨Q.one, Q.zero, Q.zero⟩

@[specialize] def add (Q : QuadOps K) (a b : Fq6 K) : Fq6 K :=
  ⟨Q.add a.c0 b.c0, Q.add a.c1 b.c1, Q.add a.c2 b.c2⟩
@[specialize] def sub (Q : QuadOps K) (a b : Fq6 K) : Fq6 K :=
  ⟨Q.sub a.c0 b.c0, Q.sub a.c1 b.c1, Q.sub a.c2 b.c2⟩
@[specialize] def neg (Q : QuadOps K) (a : Fq6 K) : Fq6 K :=
  ⟨Q.neg a.c0, Q.neg a.c1, Q.neg a.c2⟩

/-- Karatsuba over `K`: six products. -/
@[specialize] def mul (Q : QuadOps K) (a b : Fq6 K) : Fq6 K :=
  let v0 := Q.mul a.c0 b.c0
  let v1 := Q.mul a.c1 b.c1
  let v2 := Q.mul a.c2 b.c2
  let m12 := Q.mul (Q.add a.c1 a.c2) (Q.add b.c1 b.c2)
  let m01 := Q.mul (Q.add a.c0 a.c1) (Q.add b.c0 b.c1)
  let m02 := Q.mul (Q.add a.c0 a.c2) (Q.add b.c0 b.c2)
  ⟨Q.add v0 (Q.mulXi (Q.sub (Q.sub m12 v1) v2)),
   Q.add (Q.sub (Q.sub m01 v0) v1) (Q.mulXi v2),
   Q.add (Q.sub (Q.sub m02 v0) v2) v1⟩

/-- Multiply by `v`: `(c0, c1, c2) ↦ (ξ·c2, c0, c1)`. -/
@[specialize] def mulByV (Q : QuadOps K) (a : Fq6 K) : Fq6 K := ⟨Q.mulXi a.c2, a.c0, a.c1⟩

/-- Multiply by an element of `K`: three products. -/
@[specialize] def scale (Q : QuadOps K) (a : Fq6 K) (k : K) : Fq6 K :=
  ⟨Q.mul a.c0 k, Q.mul a.c1 k, Q.mul a.c2 k⟩

/-- Multiply by the sparse `b0 + b1·v`: five products. -/
@[specialize] def mul01 (Q : QuadOps K) (a : Fq6 K) (b0 b1 : K) : Fq6 K :=
  let v0 := Q.mul a.c0 b0
  let v1 := Q.mul a.c1 b1
  let m := Q.mul (Q.add a.c0 a.c1) (Q.add b0 b1)
  ⟨Q.add v0 (Q.mulXi (Q.mul a.c2 b1)), Q.sub (Q.sub m v0) v1, Q.add (Q.mul a.c2 b0) v1⟩

/-- Multiply by the sparse `b1·v`: three products. -/
@[specialize] def mul1 (Q : QuadOps K) (a : Fq6 K) (b1 : K) : Fq6 K :=
  ⟨Q.mulXi (Q.mul a.c2 b1), Q.mul a.c0 b1, Q.mul a.c1 b1⟩

/-- Inverse by the cubic-extension formula over `K`, with one inversion in `K`. Zero maps to zero. -/
@[specialize] def inv (Q : QuadOps K) (a : Fq6 K) : Fq6 K :=
  let t0 := Q.sub (Q.sqr a.c0) (Q.mulXi (Q.mul a.c1 a.c2))
  let t1 := Q.sub (Q.mulXi (Q.sqr a.c2)) (Q.mul a.c0 a.c1)
  let t2 := Q.sub (Q.sqr a.c1) (Q.mul a.c0 a.c2)
  let norm := Q.add (Q.mul a.c0 t0) (Q.mulXi (Q.add (Q.mul a.c2 t1) (Q.mul a.c1 t2)))
  let ni := Q.inv norm
  ⟨Q.mul t0 ni, Q.mul t1 ni, Q.mul t2 ni⟩

@[specialize] def isZero (Q : QuadOps K) (a : Fq6 K) : Bool :=
  Q.isZero a.c0 && Q.isZero a.c1 && Q.isZero a.c2

end Fq6

/-- An element `c0 + c1·w` of `Fq6[w]/(w² − v)`. -/
structure Fq12 (K : Type) where
  c0 : Fq6 K
  c1 : Fq6 K

namespace Fq12

variable {K : Type}

@[inline] def one (Q : QuadOps K) : Fq12 K := ⟨Fq6.one Q, Fq6.zero Q⟩

/-- Karatsuba over `Fq6`: three products. -/
@[specialize] def mul (Q : QuadOps K) (a b : Fq12 K) : Fq12 K :=
  let t0 := Fq6.mul Q a.c0 b.c0
  let t1 := Fq6.mul Q a.c1 b.c1
  let m := Fq6.mul Q (Fq6.add Q a.c0 a.c1) (Fq6.add Q b.c0 b.c1)
  ⟨Fq6.add Q t0 (Fq6.mulByV Q t1), Fq6.sub Q (Fq6.sub Q m t0) t1⟩

/-- Complex squaring: `(a + b·w)² = ((a + b)(a + v·b) − ab − v·ab) + 2ab·w`, two `Fq6` products. -/
@[specialize] def sqr (Q : QuadOps K) (a : Fq12 K) : Fq12 K :=
  let ab := Fq6.mul Q a.c0 a.c1
  let m := Fq6.mul Q (Fq6.add Q a.c0 a.c1) (Fq6.add Q a.c0 (Fq6.mulByV Q a.c1))
  ⟨Fq6.sub Q (Fq6.sub Q m ab) (Fq6.mulByV Q ab), Fq6.add Q ab ab⟩

/-- The `p⁶`-power Frobenius, `w ↦ −w`. In the cyclotomic subgroup it is the inverse. -/
@[specialize] def conj (Q : QuadOps K) (a : Fq12 K) : Fq12 K := ⟨a.c0, Fq6.neg Q a.c1⟩

/-- The `p`-power Frobenius: conjugate each coefficient and multiply the coefficient
    of `wⁱ` by `ξ^(i(p−1)/6)`. -/
@[specialize] def frobenius (Q : QuadOps K) (T : TowerParams K) (a : Fq12 K) : Fq12 K :=
  ⟨⟨Q.conj a.c0.c0, Q.mul (Q.conj a.c0.c1) T.frob2, Q.mul (Q.conj a.c0.c2) T.frob4⟩,
   ⟨Q.mul (Q.conj a.c1.c0) T.frob1, Q.mul (Q.conj a.c1.c1) T.frob3, Q.mul (Q.conj a.c1.c2) T.frob5⟩⟩

/-- Inverse: `(a + b·w)⁻¹ = (a − b·w)·(a² − v·b²)⁻¹`, one `Fq6` inversion, so one base-field
    inversion in all. Zero maps to zero. -/
@[specialize] def inv (Q : QuadOps K) (a : Fq12 K) : Fq12 K :=
  let t := Fq6.sub Q (Fq6.mul Q a.c0 a.c0) (Fq6.mulByV Q (Fq6.mul Q a.c1 a.c1))
  let ti := Fq6.inv Q t
  ⟨Fq6.mul Q a.c0 ti, Fq6.neg Q (Fq6.mul Q a.c1 ti)⟩

/-- `(a + b·s)²` in `K[s]/(s² − ξ)` as the pair `(a² + ξ·b², 2ab)`: three squarings in `K`. -/
@[specialize] def fq4Sqr (Q : QuadOps K) (a b : K) : K × K :=
  let a2 := Q.sqr a
  let b2 := Q.sqr b
  (Q.add a2 (Q.mulXi b2), Q.sub (Q.sub (Q.sqr (Q.add a b)) a2) b2)

/-- `3t − 2c` as `2(t − c) + t`. -/
@[specialize] def tripleMinus (Q : QuadOps K) (t c : K) : K := Q.add (Q.double (Q.sub t c)) t

/-- `3t + 2c` as `2(t + c) + t`. -/
@[specialize] def triplePlus (Q : QuadOps K) (t c : K) : K := Q.add (Q.double (Q.add t c)) t

/-- Squaring in the cyclotomic subgroup (Granger and Scott 2010; see the module comment).
    The result is the square only for `g` with `g^(p⁴ − p² + 1) = 1`. -/
@[specialize] def cyclotomicSqr (Q : QuadOps K) (g : Fq12 K) : Fq12 K :=
  let a := fq4Sqr Q g.c0.c0 g.c1.c1
  let b := fq4Sqr Q g.c1.c0 g.c0.c2
  let d := fq4Sqr Q g.c0.c1 g.c1.c2
  ⟨⟨tripleMinus Q a.1 g.c0.c0, tripleMinus Q b.1 g.c0.c1, tripleMinus Q d.1 g.c0.c2⟩,
   ⟨triplePlus Q (Q.mulXi d.2) g.c1.c0, triplePlus Q a.2 g.c1.c1, triplePlus Q b.2 g.c1.c2⟩⟩

/-- `f · (l0 + l1·w + l2·w³)`: the line of a D-type twist, 13 products in `K`. -/
@[specialize] def mulLineD (Q : QuadOps K) (f : Fq12 K) (l0 l1 l2 : K) : Fq12 K :=
  let t0 := Fq6.scale Q f.c0 l0
  let t1 := Fq6.mul01 Q f.c1 l1 l2
  let m := Fq6.mul01 Q (Fq6.add Q f.c0 f.c1) (Q.add l0 l1) l2
  ⟨Fq6.add Q t0 (Fq6.mulByV Q t1), Fq6.sub Q (Fq6.sub Q m t0) t1⟩

/-- `f · (l0 + l1·w² + l2·w³)`: the line of an M-type twist, 13 products in `K`. -/
@[specialize] def mulLineM (Q : QuadOps K) (f : Fq12 K) (l0 l1 l2 : K) : Fq12 K :=
  let t0 := Fq6.mul01 Q f.c0 l0 l1
  let t1 := Fq6.mul1 Q f.c1 l2
  let m := Fq6.mul01 Q (Fq6.add Q f.c0 f.c1) l0 (Q.add l1 l2)
  ⟨Fq6.add Q t0 (Fq6.mulByV Q t1), Fq6.sub Q (Fq6.sub Q m t0) t1⟩

@[specialize] def isOne (Q : QuadOps K) (a : Fq12 K) : Bool :=
  Q.eq a.c0.c0 Q.one && Q.isZero a.c0.c1 && Q.isZero a.c0.c2 && Fq6.isZero Q a.c1

/-- Square-and-multiply with full squarings, for guards (any element). -/
def powLoop (Q : QuadOps K) (base : Fq12 K) (e : Nat) : Nat → Fq12 K → Fq12 K
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr Q acc
    powLoop Q base e k (if e.testBit k then mul Q square base else square)

def pow (Q : QuadOps K) (base : Fq12 K) (e : Nat) : Fq12 K :=
  if e = 0 then one Q else powLoop Q base e (Nat.log2 e + 1) (one Q)

/-- The flat form of `Tower.lean`: coefficients of `1, w, …, w⁵`. -/
def toFlat (toFp2 : K → Fp2) (g : Fq12 K) : Fp12 :=
  ⟨toFp2 g.c0.c0, toFp2 g.c1.c0, toFp2 g.c0.c1, toFp2 g.c1.c1, toFp2 g.c0.c2, toFp2 g.c1.c2⟩

def ofFlat (ofFp2 : Fp2 → K) (a : Fp12) : Fq12 K :=
  ⟨⟨ofFp2 a.c0, ofFp2 a.c2, ofFp2 a.c4⟩, ⟨ofFp2 a.c1, ofFp2 a.c3, ofFp2 a.c5⟩⟩

/-- Kind: identity handling.
    Says: the zeroth power is one without entering the loop.
    Does not say: any other power is the field power (guards, not proved). -/
theorem pow_zero (Q : QuadOps K) (base : Fq12 K) : pow Q base 0 = one Q := by
  simp [pow]

/-- Kind: shape of the conjugation.
    Says: conjugation leaves the `Fq6` coefficient of `1` unchanged and negates the
    coefficient of `w`.
    Does not say: that conjugating twice is the identity (that needs the field laws). -/
theorem conj_parts (Q : QuadOps K) (a : Fq12 K) :
    (conj Q a).c0 = a.c0 ∧ (conj Q a).c1 = Fq6.neg Q a.c1 := by
  simp [conj]

#print axioms pow_zero
#print axioms conj_parts

end Fq12

end EVMCleanroom.Precompiles
