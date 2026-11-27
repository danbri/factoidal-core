import EVMCleanroom.Precompiles.Limb
import EVMCleanroom.Precompiles.Field

/-!
# Montgomery arithmetic on four and six limbs

An element `a` of the field of an odd modulus `N` is stored as the canonical
residue of `a · R`, with `R = 2^256` (four limbs) or `R = 2^384` (six limbs).
The product of two stored values is one schoolbook multiplication and one
Montgomery reduction (Montgomery 1985): `redc t = t · R⁻¹ mod N`. Sums,
differences and negations are the same as for plain residues.

`Mont256` serves the alt_bn128 base field and the secp256k1 scalar field,
`Mont384` the BLS12-381 base field. The parameters are literals in the curve
modules; build-time guards there check them against the modulus.

Nothing here is constant-time: `condSub`, the exponentiation and the inverse branch on data.
-/

namespace EVMCleanroom.Precompiles

/-- Parameters of a four-limb odd modulus: the modulus, `−N⁻¹ mod 2^64`,
    `R mod N` (the stored form of one) and `R² mod N`. -/
structure Mont256 where
  n : U256
  n0inv : UInt64
  one : U256
  r2 : U256

namespace Mont256

@[inline] def mul (M : Mont256) (a b : U256) : U256 := U256.redc M.n M.n0inv (U256.mulWide a b)
@[inline] def sqr (M : Mont256) (a : U256) : U256 := U256.redc M.n M.n0inv (U256.mulWide a a)
@[inline] def add (M : Mont256) (a b : U256) : U256 := U256.addMod M.n a b
@[inline] def sub (M : Mont256) (a b : U256) : U256 := U256.subMod M.n a b
@[inline] def neg (M : Mont256) (a : U256) : U256 := U256.negMod M.n a

/-- Stored form of a canonical residue. -/
@[inline] def toMont (M : Mont256) (a : U256) : U256 := mul M a M.r2
/-- The canonical residue of a stored value. -/
@[inline] def fromMont (M : Mont256) (a : U256) : U256 := U256.redc M.n M.n0inv a.widen

/-- Stored form of any natural number (reduced first). -/
def ofNat (M : Mont256) (x : Nat) : U256 := toMont M (U256.ofNat (x % M.n.toNat))
/-- The canonical residue as a natural number. -/
def toNat (M : Mont256) (a : U256) : Nat := (fromMont M a).toNat

/-- Square-and-multiply, most significant bit first, `bits` steps. -/
def powLoop (M : Mont256) (base : U256) (e : Nat) : Nat → U256 → U256
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr M acc
    powLoop M base e k (if e.testBit k then mul M square base else square)

def pow (M : Mont256) (base : U256) (e : Nat) : U256 := powLoop M base e (Nat.log2 e + 1) M.one

/-- Inverse through the `Nat` extended Euclid of `Fp.inv` (measured faster than a Fermat power
    on limbs: 36 µs against 49 µs); zero maps to zero. Variable-time. -/
def inv (M : Mont256) (a : U256) : U256 := ofNat M (Fp.inv M.n.toNat (toNat M a))

def ops (M : Mont256) : FieldOps U256 where
  zero := U256.zero
  one := M.one
  add := add M
  sub := sub M
  mul := mul M
  sqr := sqr M
  neg := neg M
  inv := inv M
  isZero := U256.isZero
  eq := U256.beq

end Mont256

/-- Parameters of a six-limb odd modulus. -/
structure Mont384 where
  n : U384
  n0inv : UInt64
  one : U384
  r2 : U384

namespace Mont384

@[inline] def mul (M : Mont384) (a b : U384) : U384 := U384.redc M.n M.n0inv (U384.mulWide a b)
@[inline] def sqr (M : Mont384) (a : U384) : U384 := U384.redc M.n M.n0inv (U384.mulWide a a)
@[inline] def add (M : Mont384) (a b : U384) : U384 := U384.addMod M.n a b
@[inline] def sub (M : Mont384) (a b : U384) : U384 := U384.subMod M.n a b
@[inline] def neg (M : Mont384) (a : U384) : U384 := U384.negMod M.n a

@[inline] def toMont (M : Mont384) (a : U384) : U384 := mul M a M.r2
@[inline] def fromMont (M : Mont384) (a : U384) : U384 := U384.redc M.n M.n0inv a.widen

def ofNat (M : Mont384) (x : Nat) : U384 := toMont M (U384.ofNat (x % M.n.toNat))
def toNat (M : Mont384) (a : U384) : Nat := (fromMont M a).toNat

def powLoop (M : Mont384) (base : U384) (e : Nat) : Nat → U384 → U384
  | 0, acc => acc
  | k+1, acc =>
    let square := sqr M acc
    powLoop M base e k (if e.testBit k then mul M square base else square)

def pow (M : Mont384) (base : U384) (e : Nat) : U384 := powLoop M base e (Nat.log2 e + 1) M.one

/-- Inverse through the `Nat` extended Euclid of `Fp.inv` (measured faster than a Fermat power
    on limbs: 53 µs against 105 µs); zero maps to zero. Variable-time. -/
def inv (M : Mont384) (a : U384) : U384 := ofNat M (Fp.inv M.n.toNat (toNat M a))

def ops (M : Mont384) : FieldOps U384 where
  zero := U384.zero
  one := M.one
  add := add M
  sub := sub M
  mul := mul M
  sqr := sqr M
  neg := neg M
  inv := inv M
  isZero := U384.isZero
  eq := U384.beq

end Mont384

end EVMCleanroom.Precompiles
