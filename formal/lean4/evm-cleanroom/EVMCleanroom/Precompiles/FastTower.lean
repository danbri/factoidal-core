import EVMCleanroom.Precompiles.Tower

/-!
# The pairing tower over any base-field representation

`Fq2 F = F[u]/(u² + 1)`, `Fq6 F = Fq2[v]/(v³ − ξ)` and `Fq12 F = Fq6[w]/(w² − v)`,
written once over a `FieldOps F` dictionary. The pairing precompiles use it over the
Montgomery limb fields (`Mont256` for alt_bn128, `Mont384` for BLS12-381). Every function
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

/-- What the tower needs to know about `ξ`: which of the two supported values it is, and
    the Frobenius constants `frobᵢ = ξ^(i·(p−1)/6)` for `i = 1 … 5`. -/
structure TowerParams (F : Type) where
  /-- `ξ = 9 + u` (alt_bn128); otherwise `ξ = 1 + u` (BLS12-381). -/
  xiNine : Bool
  frob1 : Fq2 F
  frob2 : Fq2 F
  frob3 : Fq2 F
  frob4 : Fq2 F
  frob5 : Fq2 F

/-- An element `c0 + c1·v + c2·v²` of `Fq2[v]/(v³ − ξ)`. -/
structure Fq6 (F : Type) where
  c0 : Fq2 F
  c1 : Fq2 F
  c2 : Fq2 F

namespace Fq6

variable {F : Type}

@[inline] def zero (O : FieldOps F) : Fq6 F := ⟨Fq2.zero O, Fq2.zero O, Fq2.zero O⟩
@[inline] def one (O : FieldOps F) : Fq6 F := ⟨Fq2.one O, Fq2.zero O, Fq2.zero O⟩

@[specialize] def add (O : FieldOps F) (a b : Fq6 F) : Fq6 F :=
  ⟨Fq2.add O a.c0 b.c0, Fq2.add O a.c1 b.c1, Fq2.add O a.c2 b.c2⟩
@[specialize] def sub (O : FieldOps F) (a b : Fq6 F) : Fq6 F :=
  ⟨Fq2.sub O a.c0 b.c0, Fq2.sub O a.c1 b.c1, Fq2.sub O a.c2 b.c2⟩
@[specialize] def neg (O : FieldOps F) (a : Fq6 F) : Fq6 F :=
  ⟨Fq2.neg O a.c0, Fq2.neg O a.c1, Fq2.neg O a.c2⟩

/-- Karatsuba over `Fq2`: six products. -/
@[specialize] def mul (O : FieldOps F) (T : TowerParams F) (a b : Fq6 F) : Fq6 F :=
  let v0 := Fq2.mul O a.c0 b.c0
  let v1 := Fq2.mul O a.c1 b.c1
  let v2 := Fq2.mul O a.c2 b.c2
  let m12 := Fq2.mul O (Fq2.add O a.c1 a.c2) (Fq2.add O b.c1 b.c2)
  let m01 := Fq2.mul O (Fq2.add O a.c0 a.c1) (Fq2.add O b.c0 b.c1)
  let m02 := Fq2.mul O (Fq2.add O a.c0 a.c2) (Fq2.add O b.c0 b.c2)
  ⟨Fq2.add O v0 (Fq2.mulXi O T.xiNine (Fq2.sub O (Fq2.sub O m12 v1) v2)),
   Fq2.add O (Fq2.sub O (Fq2.sub O m01 v0) v1) (Fq2.mulXi O T.xiNine v2),
   Fq2.add O (Fq2.sub O (Fq2.sub O m02 v0) v2) v1⟩

/-- Multiply by `v`: `(c0, c1, c2) ↦ (ξ·c2, c0, c1)`. -/
@[specialize] def mulByV (O : FieldOps F) (T : TowerParams F) (a : Fq6 F) : Fq6 F :=
  ⟨Fq2.mulXi O T.xiNine a.c2, a.c0, a.c1⟩

/-- Multiply by an element of `Fq2`: three products. -/
@[specialize] def scale (O : FieldOps F) (a : Fq6 F) (k : Fq2 F) : Fq6 F :=
  ⟨Fq2.mul O a.c0 k, Fq2.mul O a.c1 k, Fq2.mul O a.c2 k⟩

/-- Multiply by the sparse `b0 + b1·v`: five products. -/
@[specialize] def mul01 (O : FieldOps F) (T : TowerParams F) (a : Fq6 F) (b0 b1 : Fq2 F) : Fq6 F :=
  let v0 := Fq2.mul O a.c0 b0
  let v1 := Fq2.mul O a.c1 b1
  let m := Fq2.mul O (Fq2.add O a.c0 a.c1) (Fq2.add O b0 b1)
  ⟨Fq2.add O v0 (Fq2.mulXi O T.xiNine (Fq2.mul O a.c2 b1)),
   Fq2.sub O (Fq2.sub O m v0) v1,
   Fq2.add O (Fq2.mul O a.c2 b0) v1⟩

/-- Multiply by the sparse `b1·v`: three products. -/
@[specialize] def mul1 (O : FieldOps F) (T : TowerParams F) (a : Fq6 F) (b1 : Fq2 F) : Fq6 F :=
  ⟨Fq2.mulXi O T.xiNine (Fq2.mul O a.c2 b1), Fq2.mul O a.c0 b1, Fq2.mul O a.c1 b1⟩

/-- Inverse by the cubic-extension formula over `Fq2`, with one `Fq2` inversion. Zero maps to zero. -/
@[specialize] def inv (O : FieldOps F) (T : TowerParams F) (a : Fq6 F) : Fq6 F :=
  let t0 := Fq2.sub O (Fq2.sqr O a.c0) (Fq2.mulXi O T.xiNine (Fq2.mul O a.c1 a.c2))
  let t1 := Fq2.sub O (Fq2.mulXi O T.xiNine (Fq2.sqr O a.c2)) (Fq2.mul O a.c0 a.c1)
  let t2 := Fq2.sub O (Fq2.sqr O a.c1) (Fq2.mul O a.c0 a.c2)
  let norm := Fq2.add O (Fq2.mul O a.c0 t0)
    (Fq2.mulXi O T.xiNine (Fq2.add O (Fq2.mul O a.c2 t1) (Fq2.mul O a.c1 t2)))
  let ni := Fq2.inv O norm
  ⟨Fq2.mul O t0 ni, Fq2.mul O t1 ni, Fq2.mul O t2 ni⟩

@[specialize] def isZero (O : FieldOps F) (a : Fq6 F) : Bool :=
  Fq2.isZero O a.c0 && Fq2.isZero O a.c1 && Fq2.isZero O a.c2

end Fq6

/-- An element `c0 + c1·w` of `Fq6[w]/(w² − v)`. -/
structure Fq12 (F : Type) where
  c0 : Fq6 F
  c1 : Fq6 F

namespace Fq12

variable {F : Type}

@[inline] def one (O : FieldOps F) : Fq12 F := ⟨Fq6.one O, Fq6.zero O⟩

/-- Karatsuba over `Fq6`: three products. -/
@[specialize] def mul (O : FieldOps F) (T : TowerParams F) (a b : Fq12 F) : Fq12 F :=
  let t0 := Fq6.mul O T a.c0 b.c0
  let t1 := Fq6.mul O T a.c1 b.c1
  let m := Fq6.mul O T (Fq6.add O a.c0 a.c1) (Fq6.add O b.c0 b.c1)
  ⟨Fq6.add O t0 (Fq6.mulByV O T t1), Fq6.sub O (Fq6.sub O m t0) t1⟩

/-- Complex squaring: `(a + b·w)² = ((a + b)(a + v·b) − ab − v·ab) + 2ab·w`, two `Fq6` products. -/
@[specialize] def sqr (O : FieldOps F) (T : TowerParams F) (a : Fq12 F) : Fq12 F :=
  let ab := Fq6.mul O T a.c0 a.c1
  let m := Fq6.mul O T (Fq6.add O a.c0 a.c1) (Fq6.add O a.c0 (Fq6.mulByV O T a.c1))
  ⟨Fq6.sub O (Fq6.sub O m ab) (Fq6.mulByV O T ab), Fq6.add O ab ab⟩

/-- The `p⁶`-power Frobenius, `w ↦ −w`. In the cyclotomic subgroup it is the inverse. -/
@[specialize] def conj (O : FieldOps F) (a : Fq12 F) : Fq12 F := ⟨a.c0, Fq6.neg O a.c1⟩

/-- The `p`-power Frobenius: conjugate each `Fq2` coefficient and multiply the coefficient
    of `wⁱ` by `ξ^(i(p−1)/6)`. -/
@[specialize] def frobenius (O : FieldOps F) (T : TowerParams F) (a : Fq12 F) : Fq12 F :=
  ⟨⟨Fq2.conj O a.c0.c0, Fq2.mul O (Fq2.conj O a.c0.c1) T.frob2, Fq2.mul O (Fq2.conj O a.c0.c2) T.frob4⟩,
   ⟨Fq2.mul O (Fq2.conj O a.c1.c0) T.frob1, Fq2.mul O (Fq2.conj O a.c1.c1) T.frob3,
    Fq2.mul O (Fq2.conj O a.c1.c2) T.frob5⟩⟩

/-- Inverse: `(a + b·w)⁻¹ = (a − b·w)·(a² − v·b²)⁻¹`, one `Fq6` inversion, so one base-field
    inversion in all. Zero maps to zero. -/
@[specialize] def inv (O : FieldOps F) (T : TowerParams F) (a : Fq12 F) : Fq12 F :=
  let t := Fq6.sub O (Fq6.mul O T a.c0 a.c0) (Fq6.mulByV O T (Fq6.mul O T a.c1 a.c1))
  let ti := Fq6.inv O T t
  ⟨Fq6.mul O T a.c0 ti, Fq6.neg O (Fq6.mul O T a.c1 ti)⟩

/-- `(a + b·s)²` in `Fq2[s]/(s² − ξ)` as the pair `(a² + ξ·b², 2ab)`: three `Fq2` squarings. -/
@[specialize] def fq4Sqr (O : FieldOps F) (nine : Bool) (a b : Fq2 F) : Fq2 F × Fq2 F :=
  let a2 := Fq2.sqr O a
  let b2 := Fq2.sqr O b
  (Fq2.add O a2 (Fq2.mulXi O nine b2), Fq2.sub O (Fq2.sub O (Fq2.sqr O (Fq2.add O a b)) a2) b2)

/-- `3t − 2c` as `2(t − c) + t`. -/
@[specialize] def tripleMinus (O : FieldOps F) (t c : Fq2 F) : Fq2 F :=
  Fq2.add O (Fq2.double O (Fq2.sub O t c)) t

/-- `3t + 2c` as `2(t + c) + t`. -/
@[specialize] def triplePlus (O : FieldOps F) (t c : Fq2 F) : Fq2 F :=
  Fq2.add O (Fq2.double O (Fq2.add O t c)) t

/-- Squaring in the cyclotomic subgroup (Granger and Scott 2010; see the module comment).
    The result is the square only for `g` with `g^(p⁴ − p² + 1) = 1`. -/
@[specialize] def cyclotomicSqr (O : FieldOps F) (T : TowerParams F) (g : Fq12 F) : Fq12 F :=
  let a := fq4Sqr O T.xiNine g.c0.c0 g.c1.c1
  let b := fq4Sqr O T.xiNine g.c1.c0 g.c0.c2
  let d := fq4Sqr O T.xiNine g.c0.c1 g.c1.c2
  ⟨⟨tripleMinus O a.1 g.c0.c0, tripleMinus O b.1 g.c0.c1, tripleMinus O d.1 g.c0.c2⟩,
   ⟨triplePlus O (Fq2.mulXi O T.xiNine d.2) g.c1.c0, triplePlus O a.2 g.c1.c1, triplePlus O b.2 g.c1.c2⟩⟩

/-- `f · (l0 + l1·w + l2·w³)`: the line of a D-type twist, 13 `Fq2` products. -/
@[specialize] def mulLineD (O : FieldOps F) (T : TowerParams F) (f : Fq12 F) (l0 l1 l2 : Fq2 F) : Fq12 F :=
  let t0 := Fq6.scale O f.c0 l0
  let t1 := Fq6.mul01 O T f.c1 l1 l2
  let m := Fq6.mul01 O T (Fq6.add O f.c0 f.c1) (Fq2.add O l0 l1) l2
  ⟨Fq6.add O t0 (Fq6.mulByV O T t1), Fq6.sub O (Fq6.sub O m t0) t1⟩

/-- `f · (l0 + l1·w² + l2·w³)`: the line of an M-type twist, 13 `Fq2` products. -/
@[specialize] def mulLineM (O : FieldOps F) (T : TowerParams F) (f : Fq12 F) (l0 l1 l2 : Fq2 F) : Fq12 F :=
  let t0 := Fq6.mul01 O T f.c0 l0 l1
  let t1 := Fq6.mul1 O T f.c1 l2
  let m := Fq6.mul01 O T (Fq6.add O f.c0 f.c1) l0 (Fq2.add O l1 l2)
  ⟨Fq6.add O t0 (Fq6.mulByV O T t1), Fq6.sub O (Fq6.sub O m t0) t1⟩

@[specialize] def isOne (O : FieldOps F) (a : Fq12 F) : Bool :=
  O.eq a.c0.c0.c0 O.one && O.isZero a.c0.c0.c1 && Fq2.isZero O a.c0.c1 && Fq2.isZero O a.c0.c2 &&
    Fq6.isZero O a.c1

/-- Square-and-multiply with full squarings, for guards (any element). -/
def powLoop (O : FieldOps F) (T : TowerParams F) (base : Fq12 F) (e : Nat) : Nat → Fq12 F → Fq12 F
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr O T acc
    powLoop O T base e k (if e.testBit k then mul O T square base else square)

def pow (O : FieldOps F) (T : TowerParams F) (base : Fq12 F) (e : Nat) : Fq12 F :=
  if e = 0 then one O else powLoop O T base e (Nat.log2 e + 1) (one O)

/-- The flat form of `Tower.lean`: coefficients of `1, w, …, w⁵`. -/
def toFlat (toNat : F → Nat) (g : Fq12 F) : Fp12 :=
  ⟨Fq2.toNat toNat g.c0.c0, Fq2.toNat toNat g.c1.c0, Fq2.toNat toNat g.c0.c1,
   Fq2.toNat toNat g.c1.c1, Fq2.toNat toNat g.c0.c2, Fq2.toNat toNat g.c1.c2⟩

def ofFlat (ofNat : Nat → F) (a : Fp12) : Fq12 F :=
  ⟨⟨Fq2.ofNat ofNat a.c0, Fq2.ofNat ofNat a.c2, Fq2.ofNat ofNat a.c4⟩,
   ⟨Fq2.ofNat ofNat a.c1, Fq2.ofNat ofNat a.c3, Fq2.ofNat ofNat a.c5⟩⟩

/-- Kind: identity handling.
    Says: the zeroth power is one without entering the loop.
    Does not say: any other power is the field power (guards, not proved). -/
theorem pow_zero (O : FieldOps F) (T : TowerParams F) (base : Fq12 F) : pow O T base 0 = one O := by
  simp [pow]

/-- Kind: shape of the conjugation.
    Says: conjugation leaves the `Fq6` part of `1` unchanged, and conjugating twice negates
    the `w` part twice.
    Does not say: that double negation is the identity (that needs the field laws). -/
theorem conj_c0 (O : FieldOps F) (a : Fq12 F) :
    (conj O a).c0 = a.c0 ∧ (conj O (conj O a)).c1 = Fq6.neg O (Fq6.neg O a.c1) := by
  simp [conj]

#print axioms pow_zero
#print axioms conj_c0

end Fq12

end EVMCleanroom.Precompiles
