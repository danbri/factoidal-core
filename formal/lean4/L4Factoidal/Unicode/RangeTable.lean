/-
L4Factoidal.Unicode.RangeTable — a code point property table: sorted,
disjoint ranges `[lo, hi]`, each with a small value, looked up by binary
search (https://github.com/danbri/factoidal/issues/1167, milestone 4).

The generators under `tools/unicode/` write each table as one string
literal, `lo hi v;lo hi v;...` with `lo`, `hi` in hexadecimal and `v` in
decimal; `ofText` reads it once. A string literal compiles in constant
time, where an `Array` literal of tuples needs a raised `maxRecDepth`
(as the former `XPath4.GraphemeData` arrays did).
-/
namespace L4Factoidal.Unicode

/-- Sorted, disjoint ranges with one value each; `dflt` for a code point
in no range. -/
structure RangeTable where
  los : Array UInt32
  his : Array UInt32
  vals : Array UInt8
  dflt : UInt8 := 0
  deriving Inhabited

namespace RangeTable

private def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87
  else c.toNat - 55

/-- Read `lo hi v;...` (hex, hex, decimal). Malformed entries are skipped. -/
def ofText (t : String) (dflt : UInt8 := 0) : RangeTable := Id.run do
  let mut los : Array UInt32 := #[]
  let mut his : Array UInt32 := #[]
  let mut vals : Array UInt8 := #[]
  for e in t.splitOn ";" do
    match (e.splitOn " ").filter (· != "") with
    | [a, b, v] =>
      los := los.push (a.foldl (fun n c => n * 16 + hexDigitVal c) 0).toUInt32
      his := his.push (b.foldl (fun n c => n * 16 + hexDigitVal c) 0).toUInt32
      vals := vals.push v.toNat!.toUInt8
    | _ => pure ()
  pure { los, his, vals, dflt }

/-- The value of code point `c`. Binary search; the recursion depth is at
most `log2 size + 1`, and the fuel 40 covers every table of at most
2^39 ranges. -/
def get (t : RangeTable) (c : UInt32) : UInt8 :=
  let rec go (lo hi : Nat) : Nat → UInt8
    | 0 => t.dflt
    | f + 1 =>
      if lo ≥ hi then t.dflt
      else
        let mid := (lo + hi) / 2
        if c < t.los.getD mid 0 then go lo mid f
        else if c > t.his.getD mid 0 then go (mid + 1) hi f
        else t.vals.getD mid t.dflt
  go 0 t.los.size 40

@[inline] def getChar (t : RangeTable) (c : Char) : UInt8 := t.get c.val

#guard (ofText "41 5A 1;61 7A 2").get 0x42 == 1
#guard (ofText "41 5A 1;61 7A 2").get 0x7A == 2
#guard (ofText "41 5A 1;61 7A 2" 9).get 0x60 == 9
#guard (ofText "41 5A 1;61 7A 2").get 0x10FFFF == 0

end RangeTable
end L4Factoidal.Unicode
