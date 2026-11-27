import EVMCleanroom.Precompiles.Curve

/-!
# Scalar multiplication by windows, and sums of scalar multiples

Additions to the generic curve code of `Curve.lean` (curves `y² = x³ + b`,
Jacobian coordinates, any `FieldOps` dictionary), used by the fast paths of
the group-operation precompiles. Every function on a hot path is marked
`@[specialize]`, so it is compiled again for each concrete field with direct
calls.

* `toAffineFast`: as `Curve.toAffine`, without the inversion when `Z = 1`.
* `addMixed`: Jacobian plus affine (the textbook chord rule with `Z₂ = 1`).
* `addAffine`: affine plus affine with one inversion, for a single addition
  whose result is wanted in affine form anyway.
* `windowMul`: one scalar multiple with a table of the multiples `0 … 15` and
  four doublings per four scalar bits.
* `straus`: a sum of scalar multiples with one shared doubling chain and one
  table per point (Straus 1964, as described in Bernstein, Doumen, Lange,
  Oosterwijk, "Faster batch forgery identification", 2012, section 3).
* `pippenger`: the bucket method for many points (Pippenger 1976, as
  described in the same paper, section 4): per window of `c` scalar bits every
  point is added into the bucket of its digit, and the buckets are combined
  with a running sum, `Σ d·B_d = Σ_j (B_j + … + B_max)`.
* `msm`: chooses between the two by the number of points.

Group laws are not proved, so none of these is proved equal to the
double-and-add of `Curve.mul`: they are compared with it by build-time guards
on fixed inputs (in the modules that instantiate them) and by the differential
runs of `evm-blsops`. Proved here: loop counts and the window choice bounds.

Nothing is constant-time: the loops branch on scalar digits and on the bit
length of the scalars. The precompiles handle public data only.
-/

namespace EVMCleanroom.Precompiles

namespace Curve

variable {F : Type}

/-- Affine coordinates, `none` for the point at infinity. One field inversion,
    none when `Z` is already one. -/
@[specialize] def toAffineFast (O : FieldOps F) (p : JPoint F) : Option (F × F) :=
  if O.isZero p.z then none
  else if O.eq p.z O.one then some (p.x, p.y)
  else
    let zi := O.inv p.z
    let zi2 := O.sqr zi
    some (O.mul p.x zi2, O.mul p.y (O.mul zi2 zi))

/-- `p + (qx, qy)` for an affine second operand, which is not the point at infinity. -/
@[specialize] def addMixed (O : FieldOps F) (p : JPoint F) (qx qy : F) : JPoint F :=
  if O.isZero p.z then ⟨qx, qy, O.one⟩
  else
    let z1z1 := O.sqr p.z
    let u2 := O.mul qx z1z1
    let s2 := O.mul (O.mul qy p.z) z1z1
    let h := O.sub u2 p.x
    let r := O.sub s2 p.y
    if O.isZero h then
      if O.isZero r then double O p else infinity O
    else
      let hh := O.sqr h
      let hhh := O.mul hh h
      let v := O.mul p.x hh
      let x3 := O.sub (O.sub (O.sqr r) hhh) (O.add v v)
      let y3 := O.sub (O.mul r (O.sub v x3)) (O.mul p.y hhh)
      ⟨x3, y3, O.mul h p.z⟩

/-- The sum of two affine points, neither at infinity, by the affine chord-and-tangent rule:
    one field inversion, and the result already has `Z = 1` (or is the point at infinity). -/
@[specialize] def addAffine (O : FieldOps F) (x1 y1 x2 y2 : F) : JPoint F :=
  if O.eq x1 x2 then
    if O.eq y1 y2 && !O.isZero y1 then
      let xx := O.sqr x1
      let slope := O.mul (O.add (O.add xx xx) xx) (O.inv (O.add y1 y1))
      let x3 := O.sub (O.sub (O.sqr slope) x1) x1
      ⟨x3, O.sub (O.mul slope (O.sub x1 x3)) y1, O.one⟩
    else infinity O
  else
    let slope := O.mul (O.sub y2 y1) (O.inv (O.sub x2 x1))
    let x3 := O.sub (O.sub (O.sqr slope) x1) x2
    ⟨x3, O.sub (O.mul slope (O.sub x1 x3)) y1, O.one⟩

/-- `count` doublings. -/
@[specialize] def doubleN (O : FieldOps F) : Nat → JPoint F → JPoint F
  | 0, p => p
  | count+1, p => doubleN O count (double O p)

/-- `count` doublings, none for the point at infinity. -/
@[inline] def shiftPoint (O : FieldOps F) (count : Nat) (p : JPoint F) : JPoint F :=
  if O.isZero p.z then p else doubleN O count p

@[specialize] def tableLoop (O : FieldOps F) (x y : F) : Nat → JPoint F → Array (JPoint F) → Array (JPoint F)
  | 0, _, table => table
  | count+1, last, table =>
    let next := addMixed O last x y
    tableLoop O x y count next (table.push next)

/-- The multiples `[0]P, [1]P, …, [15]P` of the affine point `P = (x, y)`. -/
@[specialize] def table16 (O : FieldOps F) (x y : F) : Array (JPoint F) :=
  tableLoop O x y 15 (infinity O) (#[infinity O])

/-- Number of `width`-bit windows that cover a scalar. -/
def windowCount (width k : Nat) : Nat := Nat.log2 k / width + 1

/-- One scalar and the table of multiples of its point. -/
abbrev StrausItem (F : Type) := Nat × Array (JPoint F)

/-- Add, for every item, the table entry of its digit at bit position `shift`. -/
@[specialize] def strausRow (O : FieldOps F) (items : Array (StrausItem F)) (shift : Nat) :
    Nat → JPoint F → JPoint F
  | 0, acc => acc
  | j+1, acc =>
    match items[j]? with
    | none => strausRow O items shift j acc
    | some item =>
      let digit := (item.1 >>> shift) % 16
      strausRow O items shift j
        (if digit = 0 then acc else add O acc (item.2.getD digit (infinity O)))

/-- `windows` rounds of four doublings and one table addition per item, most significant window first. -/
@[specialize] def strausLoop (O : FieldOps F) (items : Array (StrausItem F)) : Nat → JPoint F → JPoint F
  | 0, acc => acc
  | i+1, acc =>
    strausLoop O items i (strausRow O items (4 * i) items.size (shiftPoint O 4 acc))

/-- `[k](x, y)` with four-bit windows. -/
@[specialize] def windowMul (O : FieldOps F) (k : Nat) (x y : F) : JPoint F :=
  if k = 0 then infinity O
  else strausLoop O (#[(k, table16 O x y)]) (windowCount 4 k) (infinity O)

/-- A scalar and an affine point. -/
abbrev MsmItem (F : Type) := Nat × F × F

@[specialize] def strausTables (O : FieldOps F) (points : Array (MsmItem F)) :
    Nat → Array (StrausItem F) → Array (StrausItem F)
  | 0, out => out
  | j+1, out =>
    match points[j]? with
    | none => strausTables O points j out
    | some item => strausTables O points j (out.push (item.1, table16 O item.2.1 item.2.2))

/-- `Σ [kᵢ]Pᵢ` with one doubling chain; `bits` covers the longest scalar. -/
@[specialize] def straus (O : FieldOps F) (points : Array (MsmItem F)) (bits : Nat) : JPoint F :=
  strausLoop O (strausTables O points points.size #[]) ((bits + 3) / 4) (infinity O)

/-- Add every point into the bucket of its `mask`-wide digit at bit position `shift`
    (digit `d` goes to index `d − 1`; digit zero is skipped). -/
@[specialize] def bucketFill (O : FieldOps F) (points : Array (MsmItem F)) (shift mask : Nat) :
    Nat → Array (JPoint F) → Array (JPoint F)
  | 0, buckets => buckets
  | j+1, buckets =>
    match points[j]? with
    | none => bucketFill O points shift mask j buckets
    | some item =>
      let digit := (item.1 >>> shift) &&& mask
      bucketFill O points shift mask j
        (if digit = 0 then buckets
         else buckets.modify (digit - 1) fun bucket => addMixed O bucket item.2.1 item.2.2)

/-- `Σ d·B_d` by a running sum from the highest bucket down. -/
@[specialize] def bucketSum (O : FieldOps F) (buckets : Array (JPoint F)) : Nat → JPoint F → JPoint F → JPoint F
  | 0, _, total => total
  | j+1, running, total =>
    let running := add O running (buckets.getD j (infinity O))
    bucketSum O buckets j running (add O total running)

/-- One bucket pass per window of `width` bits, most significant window first.
    `mask = 2^width − 1` is also the number of buckets. -/
@[specialize] def pippengerLoop (O : FieldOps F) (points : Array (MsmItem F)) (width mask : Nat) :
    Nat → JPoint F → JPoint F
  | 0, acc => acc
  | i+1, acc =>
    let buckets := bucketFill O points (width * i) mask points.size (Array.replicate mask (infinity O))
    let window := bucketSum O buckets mask (infinity O) (infinity O)
    pippengerLoop O points width mask i (add O (shiftPoint O width acc) window)

/-- Number of bucket passes for scalars of `bits` bits with windows of `width` bits. -/
def passes (bits width : Nat) : Nat := (bits + width - 1) / width

/-- `Σ [kᵢ]Pᵢ` by the bucket method with windows of `width` bits. -/
@[specialize] def pippenger (O : FieldOps F) (points : Array (MsmItem F)) (bits width : Nat) : JPoint F :=
  pippengerLoop O points width (2 ^ width - 1) (passes bits width) (infinity O)

/-- Window width of the bucket method by the number of points. The thresholds minimise
    `passes · (11 n + 32 · 2^width)` field multiplications for 256-bit scalars (a mixed
    addition per point and two additions per bucket in every pass). -/
def bucketWidth (count : Nat) : Nat :=
  if count < 96 then 4
  else if count < 256 then 5
  else if count < 640 then 6
  else if count < 1536 then 7
  else if count < 3584 then 8
  else if count < 8192 then 9
  else 10

/-- From this many points on the bucket method is used instead of one table per point. -/
def bucketThreshold : Nat := 80

/-- `Σ [kᵢ]Pᵢ` for affine points and scalars below `2^bits`. -/
@[specialize] def msm (O : FieldOps F) (points : Array (MsmItem F)) (bits : Nat) : JPoint F :=
  if points.size < bucketThreshold then straus O points bits
  else pippenger O points bits (bucketWidth points.size)

/-- Kind: loop bound.
    Says: the bucket method makes at most one pass per scalar bit, and exactly
    `⌈bits / width⌉` passes; a pass handles each point once (`bucketFill` recurses on the
    number of points) and each bucket once (`bucketSum` recurses on the number of buckets).
    Does not say: the result is the group sum. -/
theorem passes_le (bits width : Nat) (h : 0 < width) : passes bits width ≤ bits := by
  unfold passes
  cases bits with
  | zero => exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
  | succ b =>
    apply Nat.div_le_of_le_mul
    have h1 : 1 * b ≤ width * b := Nat.mul_le_mul_right b h
    have h2 : width * (b + 1) = width * b + width := Nat.mul_succ width b
    omega

/-- Kind: loop bound.
    Says: the passes cover every scalar bit (`passes · width ≥ bits`).
    Does not say: the result is the group sum. -/
theorem passes_cover (bits width : Nat) (h : 0 < width) : bits ≤ passes bits width * width := by
  unfold passes
  have h1 := Nat.div_add_mod (bits + width - 1) width
  have h2 := Nat.mod_lt (bits + width - 1) h
  rw [Nat.mul_comm] at h1
  omega

/-- Kind: parameter bound.
    Says: the chosen window width is between 4 and 10 bits, so a pass has at most 1023 buckets.
    Does not say: the choice is optimal. -/
theorem bucketWidth_bounds (count : Nat) : 4 ≤ bucketWidth count ∧ bucketWidth count ≤ 10 := by
  unfold bucketWidth
  constructor <;> repeat' split
  all_goals omega

/-- Kind: identity handling.
    Says: a scalar multiple by zero is the point at infinity, without any loop.
    Does not say: anything for other scalars. -/
theorem windowMul_zero (O : FieldOps F) (x y : F) : windowMul O 0 x y = infinity O := by
  simp [windowMul]

#guard (List.range 300).all fun bits => (List.range 12).all fun w => passes bits (w + 1) * (w + 1) ≥ bits
#guard passes 256 4 == 64 && passes 256 5 == 52 && passes 255 5 == 51 && passes 0 4 == 0 && passes 1 4 == 1
#guard windowCount 4 1 == 1 && windowCount 4 15 == 1 && windowCount 4 16 == 2 && windowCount 4 (2 ^ 256 - 1) == 64

-- The windowed and bucket sums against double-and-add, on the small curve y² = x³ + 7 over 10007 elements.
private def small : FieldOps Nat := Fp.ops 10007
/- Test values are functions of a unit argument, compiled without closed-term extraction: a constant
   would be computed whenever a program that links this module starts. -/
set_option compiler.extract_closed false in
private def smallPointsOf (_ : Unit) : Array (Nat × Nat) :=
  ((List.range 400).filterMap fun x => (Fp.sqrt? 10007 ((x * x * x + 7) % 10007)).map fun y => (x, y)).toArray
private def reference (items : Array (MsmItem Nat)) : JPoint Nat :=
  items.foldl (fun acc item => add small acc (mul small item.1 (ofAffine small item.2.1 item.2.2))) (infinity small)
private def items (count seed : Nat) : Array (MsmItem Nat) :=
  let points := smallPointsOf ()
  ((List.range count).map fun i =>
    let point := points.getD (i % points.size) (0, 0)
    ((i * i * seed + 3 * i + seed % 5) % 65000 * (i % 3), point.1, point.2)).toArray
#guard (smallPointsOf ()).size ≥ 100 && (smallPointsOf ()).all fun point => onCurve small 7 point.1 point.2
#guard (List.range 40).all fun k =>
  ((smallPointsOf ()).extract 0 40).all fun point => same small (windowMul small (k * 331) point.1 point.2) (mul small (k * 331) (ofAffine small point.1 point.2))
#guard (List.range 12).all fun n => same small (straus small (items n 77) 17) (reference (items n 77))
#guard (List.range 12).all fun n => same small (straus small (items (3 * n) 5) 20) (reference (items (3 * n) 5))
#guard [1, 2, 3, 4, 5, 6, 7].all fun width =>
  (List.range 10).all fun n => same small (pippenger small (items (7 * n) 91) 17 width) (reference (items (7 * n) 91))
#guard same small (msm small (items 79 3) 17) (reference (items 79 3)) &&
  same small (msm small (items 80 3) 17) (reference (items 80 3)) &&
  same small (msm small (items 200 9) 17) (reference (items 200 9))
#guard ((smallPointsOf ()).extract 0 30).all fun point =>
  (toAffineFast small (addMixed small (mul small 5 (ofAffine small point.1 point.2)) point.1 point.2)) ==
    (toAffine small (mul small 6 (ofAffine small point.1 point.2))) &&
  (toAffineFast small (addMixed small (ofAffine small point.1 point.2) point.1 point.2)) ==
    (toAffine small (mul small 2 (ofAffine small point.1 point.2))) &&
  (toAffineFast small (addMixed small (ofAffine small point.1 point.2) point.1 (Fp.neg 10007 point.2))).isNone

-- The affine sum against the Jacobian one: all pairs of 40 points (equal points included), inverse points,
-- and points of order two when the curve has them.
#guard ((smallPointsOf ()).extract 0 40).all fun a => ((smallPointsOf ()).extract 0 40).all fun b =>
  toAffineFast small (addAffine small a.1 a.2 b.1 b.2) ==
    toAffine small (add small (ofAffine small a.1 a.2) (ofAffine small b.1 b.2)) &&
  (toAffineFast small (addAffine small a.1 a.2 a.1 (Fp.neg 10007 a.2))).isNone
#guard ((smallPointsOf ()).filter fun point => point.2 == 0).all fun a =>
  (toAffineFast small (addAffine small a.1 a.2 a.1 a.2)).isNone

#print axioms passes_le
#print axioms passes_cover
#print axioms bucketWidth_bounds
#print axioms windowMul_zero

end Curve

end EVMCleanroom.Precompiles
