/-
Harness/PrimBytesTest — the differential test of `L4Factoidal.Prim.Bytes`
(https://github.com/danbri/factoidal/issues/797).

`Prim.Bytes.stU64LE` is an `@[extern c inline]` primitive: its compiled code
is a C expression, not its Lean body. This executable compares it with
`Prim.Bytes.stU64LERef` (the Lean body, a separate definition that is not an
extern) on random and edge-case inputs, and checks the pure-Lean load
`ldU64LE` against `ldU64LESpec`. Run natively by `tests/prim/run.sh`, and in
the wasm32 build under node by the same script, so the same C source is
checked on each target.

Cases, for every array size in a fixed list and a random set:

- positions 0, 1, size-9, size-8, size-7, size-1, size, size+1, random ones,
  and the positions where `p + 8` wraps in `USize` (2^w - 1, 2^w - 7,
  2^w - 8, 2^w - 9, where w is `System.Platform.numBits`);
- values 0, 2^64 - 1, 0x0102030405060708 (to see the byte order) and random
  ones;
- the array exclusive (made fresh in `IO`, so the compiler cannot share it)
  and shared (another reference is live): the shared original must be
  unchanged after the store.

`Prim.Bytes.pushU64LE` (append 8 bytes) is compared with `pushU64LERef`
(eight `ByteArray.push`) on arrays of every listed size with capacity equal
to the size, 1, 7, 8, 9 and 16 bytes above it, 0 and half the size (so the
append must grow the array), exclusive and shared; and on chains of 120
appends from an empty array of several capacities, one intermediate array
kept live (shared). Checks: same bytes and size, size + 8, the shared
original unchanged, `ldU64LE` at the old size reads the value.

Checks per store case: the extern result equals the reference byte for byte and in
size; the shared original is unchanged; in bounds, `ldU64LE` reads back the
value written (the theorem `ldU64LE_stU64LE`, here on the C); `ldU64LE`
equals `ldU64LESpec` at every tested position.

Prints "prim-bytes: N pass, M fail (out of T)"; exit code 0 only when M = 0.
-/
import L4Factoidal.Prim.Bytes

open L4Factoidal.Prim.Bytes

namespace PrimBytesTest

/-- splitmix64. -/
def next (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- An array of `n` pseudo-random bytes from `seed`, made in `IO` so each call
    returns a new, exclusive array. -/
@[noinline] def mkArray (n : Nat) (seed : UInt64) : IO ByteArray := do
  let mut b := ByteArray.emptyWithCapacity n
  let mut s := seed
  for _ in [0:n] do
    let (z, s') := next s
    s := s'
    b := b.push z.toUInt8
  return b

def sameBytes (a b : ByteArray) : Bool := a.size == b.size && a.data == b.data

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  firstFails : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1,
                firstFails := if t.firstFails.size < 20 then t.firstFails.push what else t.firstFails }

/-- One case: array of size `n` from `seed`, position `p`, value `x`. -/
def runCase (t : Tally) (n : Nat) (seed : UInt64) (p : USize) (x : UInt64) : IO Tally := do
  let tag := s!"n={n} seed={seed} p={p.toNat} x={x}"
  -- Exclusive: a fresh array straight into the extern; a second fresh copy into the reference.
  let r1 := stU64LE (← mkArray n seed) p x
  let r2 := stU64LERef (← mkArray n seed) p x
  let mut t := t.check (sameBytes r1 r2) s!"exclusive: extern /= reference ({tag})"
  -- Shared: the original stays live after the call.
  let orig ← mkArray n seed
  let keep ← mkArray n seed
  let s1 := stU64LE orig p x
  let s2 := stU64LERef orig p x
  t := t.check (sameBytes s1 s2) s!"shared: extern /= reference ({tag})"
  t := t.check (sameBytes orig keep) s!"shared: original changed ({tag})"
  -- Read after write, in bounds.
  if p.toNat + 8 ≤ n then
    t := t.check (ldU64LE r1 p == x) s!"read after write ({tag})"
  -- Load against its specification, on the input and the output.
  t := t.check (ldU64LE orig p == ldU64LESpec orig p.toNat) s!"load /= spec ({tag})"
  t := t.check (ldU64LE r1 p == ldU64LESpec r1 p.toNat) s!"load /= spec after store ({tag})"
  return t

/-- An array of `n` pseudo-random bytes from `seed` with capacity `cap`
    (when `cap < n` the pushes grow it), made in `IO`. -/
@[noinline] def mkArrayCap (n cap : Nat) (seed : UInt64) : IO ByteArray := do
  let mut b := ByteArray.emptyWithCapacity cap
  let mut s := seed
  for _ in [0:n] do
    let (z, s') := next s
    s := s'
    b := b.push z.toUInt8
  return b

/-- One append case: array of size `n` and capacity `cap` from `seed`, value
    `x`. -/
def runPushCase (t : Tally) (n cap : Nat) (seed : UInt64) (x : UInt64) : IO Tally := do
  let tag := s!"push n={n} cap={cap} seed={seed} x={x}"
  -- Exclusive.
  let r1 := pushU64LE (← mkArrayCap n cap seed) x
  let r2 := pushU64LERef (← mkArrayCap n cap seed) x
  let mut t := t.check (sameBytes r1 r2) s!"exclusive: extern /= reference ({tag})"
  t := t.check (r1.size == n + 8) s!"size /= n + 8 ({tag})"
  t := t.check (ldU64LE r1 n.toUSize == x) s!"read after append ({tag})"
  -- Shared: the original stays live after the call.
  let orig ← mkArrayCap n cap seed
  let keep ← mkArrayCap n cap seed
  let s1 := pushU64LE orig x
  let s2 := pushU64LERef orig x
  t := t.check (sameBytes s1 s2) s!"shared: extern /= reference ({tag})"
  t := t.check (sameBytes orig keep) s!"shared: original changed ({tag})"
  return t

/-- A chain of `k` appends from an empty array of capacity `cap` (growth
    through every capacity boundary), compared after each append; at step
    `share` the intermediate array is also kept live (shared). -/
def runPushChain (t : Tally) (cap k share : Nat) (seed : UInt64) : IO Tally := do
  let mut a ← mkArrayCap 0 cap seed
  let mut b ← mkArrayCap 0 cap seed
  let mut t := t
  let mut s := seed
  let mut kept : ByteArray := ByteArray.empty
  for i in [0:k] do
    let (z, s') := next s
    s := s'
    if i == share then kept := a
    a := pushU64LE a z
    b := pushU64LERef b z
    t := t.check (sameBytes a b) s!"chain cap={cap} step={i}: extern /= reference"
  t := t.check (kept.size == 8 * (min share k)) s!"chain cap={cap}: kept array changed size"
  t := t.check (ldU64LE a (8 * (k - 1)).toUSize == ldU64LESpec b (8 * (k - 1))) s!"chain cap={cap}: last read"
  return t

def positions (n : Nat) (s : UInt64) : List USize :=
  let top : USize := 0 - 1
  let fixed : List Nat := [0, 1, n - 9, n - 8, n - 7, n - 1, n, n + 1]
  let rnd := (List.range 6).map fun k =>
    ((next (s + k.toUInt64)).1.toNat % (n + 16))
  (fixed ++ rnd).map Nat.toUSize ++ [top, top - 6, top - 7, top - 8]

def values (s : UInt64) : List UInt64 :=
  [0, 0xFFFFFFFFFFFFFFFF, 0x0102030405060708, (next s).1, (next (s + 1)).1]

def main : IO UInt32 := do
  let mut t : Tally := {}
  let fixedSizes : List Nat := [0, 1, 7, 8, 9, 15, 16, 17, 64, 1000]
  let mut s : UInt64 := 0x5EED
  let mut sizes := fixedSizes
  for _ in [0:20] do
    let (z, s') := next s
    s := s'
    sizes := sizes ++ [z.toNat % 300]
  for n in sizes do
    for p in positions n s do
      for x in values (s + n.toUInt64 + p.toUInt64) do
        t ← runCase t n (s + n.toUInt64) p x
    s := (next s).2
  -- Appends: every size of the list, capacities at and around the 8-byte
  -- boundary (spare 0, 1, 7, 8, 9, 16) and below the size (growth).
  for n in sizes do
    for cap in [0, n, n + 1, n + 7, n + 8, n + 9, n + 16, n / 2] do
      for x in values (s + n.toUInt64 + cap.toUInt64) do
        t ← runPushCase t n cap (s + n.toUInt64) x
    s := (next s).2
  for cap in [0, 1, 7, 8, 9, 13, 64, 800] do
    t ← runPushChain t cap 120 (cap % 37) (s + cap.toUInt64)
  for m in t.firstFails do
    IO.println s!"FAIL {m}"
  IO.println s!"prim-bytes: platform numBits {System.Platform.numBits}"
  IO.println s!"prim-bytes: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail})"
  return (if t.fail == 0 then 0 else 1)

end PrimBytesTest

def main : IO UInt32 := PrimBytesTest.main
