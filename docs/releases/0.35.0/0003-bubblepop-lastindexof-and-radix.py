import sys
root=sys.argv[1]
def edit(p, pairs):
    s=open(p).read()
    for old,new in pairs:
        assert s.count(old)==1,(p,old[:70],s.count(old))
        s=s.replace(old,new)
    open(p,'w').write(s)
edit(root+'/Number.lean', [('''/-- A canonical array index (§6.1.7): the string of a Nat below 2^32 - 1. -/''','''/-- The digits of a fraction for `radixString`: `fraction` and `delta` are multiplied by the
radix for each digit; the digits stop when the rest is below `delta` (half the distance to the
next double), with a round to even at the end. The result is the digits and whether the round
carried into the integer part. -/
def radixFraction (r : Float) (radix : Nat) : Nat → Float → Float → Array Nat → Array Nat × Bool
  | 0, _, _, acc => (acc, false)
  | fuel + 1, fraction, delta, acc =>
    let fraction := fraction * r
    let delta := delta * r
    let digit := fraction.toUInt64.toNat
    let acc := acc.push digit
    let fraction := fraction - Float.ofNat digit
    if (fraction > 0.5 || (fraction == 0.5 && digit % 2 == 1)) && fraction + delta > 1 then
      -- round up: digits that become the radix are dropped, the one before them goes up
      let rec carry : Nat → Array Nat → Array Nat × Bool
        | 0, a => (a, false)
        | k + 1, a =>
          match a.back? with
          | none => (a, true)
          | some d => if d + 1 < radix then (a.pop.push (d + 1), false) else carry k a.pop
      carry (acc.size + 1) acc
    else if fraction ≥ delta then radixFraction r radix fuel fraction delta acc
    else (acc, false)

/-- Number::toString for a finite number and a radix from 2 to 36 that is not 10 (§21.1.3.6).
ECMA-262 leaves the digits of a fraction to the implementation ("a generalization" of radix
10). This is the method of V8 (`DoubleToRadixCString`): digits of the fraction until they
identify the double; for an integer of 2^53 or more, zeros for the digits that a double does
not have. -/
def radixString (x : Float) (radix : Nat) : String :=
  let digitCh := fun (d : Nat) => "0123456789abcdefghijklmnopqrstuvwxyz".toList.getD d '0'
  let v := x.abs
  let r := Float.ofNat radix
  let whole := v.floor
  let fraction := v - whole
  -- half the distance to the next double, at least the smallest double
  let half := 0.5 * (Float.ofBits (v.toBits + 1) - v)
  let least := Float.ofBits 1
  let delta := if half > least then half else least
  let (fdigits, carried) :=
    if fraction ≥ delta then radixFraction r radix 1200 fraction delta #[] else (#[], false)
  let whole := if carried then whole + 1 else whole
  -- an integer from 2^53: divide down, one zero for each division
  let rec scale : Nat → Float → Nat → Float × Nat
    | 0, w, z => (w, z)
    | k + 1, w, z => if w ≥ twoPow53F then scale k (w / r) (z + 1) else (w, z)
  let (w, zeros) := scale 1100 whole 0
  -- the digits of the integer (`Nat.toDigits` has no digit above `f`)
  let rec whole36 : Nat → Nat → List Char → List Char
    | 0, _, acc => acc
    | k + 1, m, acc =>
      let acc := digitCh (m % radix) :: acc
      if m < radix then acc else whole36 k (m / radix) acc
  let idigits := whole36 64 w.toUInt64.toNat [] ++ List.replicate zeros '0'
  let fpart := if fdigits.isEmpty then "" else "." ++ String.ofList (fdigits.toList.map digitCh)
  (if x < 0 then "-" else "") ++ String.ofList idigits ++ fpart

/-- A canonical array index (§6.1.7): the string of a Nat below 2^32 - 1. -/''')])
edit(root+'/Interp.lean', [('''        if radix == 10 || !isIntegral x then pure (.str (numToString x))
        else
          let i := truncInt x
          let ds := Nat.toDigits radix.toUInt64.toNat i.natAbs
          pure (.str ((if i < 0 then "-" else "") ++ String.ofList ds))''','''        if radix == 10 || !x.isFinite then pure (.str (numToString x))
        else pure (.str (radixString x radix.toUInt64.toNat))'''),
('''    | .arrayLastIndexOf =>
      let es ← elemsOf n thisV
      let found := (List.range es.size).reverse.find? fun i => strictEq es[i]! a0''','''    | .arrayLastIndexOf =>
      let es ← elemsOf n thisV
      -- §23.1.3.20: the search goes down from `fromIndex` (from the end when negative); the
      -- last index when there is no second argument
      let start ← if args.size > 1 then do pure (toIntegerOrInf (← toNum n a1))
        else pure (Float.ofNat es.size)
      let k := if start ≥ 0 then start else Float.ofNat es.size + start
      -- the indices below `stop` are searched
      let stop := if k < 0 then 0 else if k ≥ Float.ofNat es.size then es.size else k.toUInt64.toNat + 1
      let found := (List.range stop).reverse.find? fun i => strictEq es[i]! a0''')])
