/-
L4Factoidal.XPath4.Unicode — Unicode normalization (UAX #15, Unicode
16.0.0) and `fn:normalize-unicode` (F&O 4.0 §5.4.9).

The four forms NFC, NFD, NFKC and NFKD: full decomposition (canonical, or
compatibility) from the generated tables of `XPath4.UnicodeNormData`,
Hangul syllables by the algorithm of Unicode §3.12, the canonical
ordering algorithm (UAX #15 §3, stable ordering by combining class), and
the canonical composition algorithm (UAX #15 §4: a character is blocked
from the last starter when a character between them has class 0 or a
class not lower than its own).

`FULLY-NORMALIZED` is not supported (it raises `FOCH0003`, as F&O 4.0
§5.4.9 allows).
-/
import Std.Data.HashMap
import L4Factoidal.XPath4.UnicodeNormData

namespace L4Factoidal.XPath4.Unicode

open Std

def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0

def entries (t : String) : List (String × String) :=
  (t.splitOn ";").filterMap (fun e => match e.splitOn ":" with
    | [a, b] => some (a, b)
    | _ => none)

def cps (s : String) : List Nat := (s.splitOn " ").filter (· != "") |>.map hexVal

def cccMap : HashMap Nat Nat :=
  (entries UnicodeNormData.cccText).foldl (fun m (a, b) => m.insert (hexVal a) b.toNat!) {}

def canonMap : HashMap Nat (List Nat) :=
  (entries UnicodeNormData.canonText).foldl (fun m (a, b) => m.insert (hexVal a) (cps b)) {}

def compatMap : HashMap Nat (List Nat) :=
  (entries UnicodeNormData.compatText).foldl (fun m (a, b) => m.insert (hexVal a) (cps b)) {}

def pairKey (a b : Nat) : Nat := a * 0x110000 + b

def compMap : HashMap Nat Nat :=
  (entries UnicodeNormData.compText).foldl (fun m (a, b) =>
    match cps a with
    | [x, y] => m.insert (pairKey x y) (hexVal b)
    | _ => m) {}

def ccc (c : Nat) : Nat := cccMap.getD c 0

/-! ## Hangul (Unicode §3.12) -/

def sBase : Nat := 0xAC00
def lBase : Nat := 0x1100
def vBase : Nat := 0x1161
def tBase : Nat := 0x11A7
def lCount : Nat := 19
def vCount : Nat := 21
def tCount : Nat := 28
def nCount : Nat := vCount * tCount
def sCount : Nat := lCount * nCount

def hangulDecomp (c : Nat) : List Nat :=
  let si := c - sBase
  let l := lBase + si / nCount
  let v := vBase + (si % nCount) / tCount
  let t := tBase + si % tCount
  if t == tBase then [l, v] else [l, v, t]

def isHangulSyllable (c : Nat) : Bool := sBase ≤ c && c < sBase + sCount

/-- The full decomposition of one code point. -/
def decompChar (compat : Bool) (c : Nat) : List Nat :=
  if isHangulSyllable c then hangulDecomp c
  else match (if compat then compatMap.get? c else none) with
    | some d => d
    | none => canonMap.getD c [c]

/-- The canonical ordering algorithm: a stable insertion sort of each run
    of non-starters by combining class. -/
def reorder (xs : Array Nat) : Array Nat := Id.run do
  let mut a := xs
  for j in [1:a.size] do
    let mut k := j
    for _ in [0:j] do
      if k == 0 then break
      let x := a.getD k 0
      let y := a.getD (k - 1) 0
      let cx := ccc x
      if cx != 0 && ccc y > cx then
        a := (a.set! k y).set! (k - 1) x
        k := k - 1
      else break
  return a

def decompose (compat : Bool) (s : String) : Array Nat :=
  reorder (s.toList.foldl (fun acc c => acc ++ (decompChar compat c.toNat).toArray) #[])

/-- The primary composite of a pair, Hangul included. -/
def composePair (a b : Nat) : Option Nat :=
  if lBase ≤ a && a < lBase + lCount && vBase ≤ b && b < vBase + vCount then
    some (sBase + ((a - lBase) * vCount + (b - vBase)) * tCount)
  else if isHangulSyllable a && (a - sBase) % tCount == 0 && tBase < b && b < tBase + tCount then
    some (a + (b - tBase))
  else compMap.get? (pairKey a b)

/-- The canonical composition algorithm (UAX #15 §4). -/
def compose (xs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut starter : Option Nat := none
  let mut lastCcc : Nat := 0
  for c in xs do
    let cc := ccc c
    match starter with
    | some si =>
      let adjacent := out.size == si + 1
      let blocked := !adjacent && (lastCcc == 0 || lastCcc ≥ cc)
      match (if blocked then none else composePair (out.getD si 0) c) with
      | some comp =>
        out := out.set! si comp
      | none =>
        if cc == 0 then starter := some out.size
        out := out.push c
        lastCcc := cc
    | none =>
      if cc == 0 then starter := some out.size
      out := out.push c
      lastCcc := cc
  return out

def ofCps (xs : Array Nat) : String := String.ofList (xs.toList.map Char.ofNat)

/-- `form` is one of `NFC`, `NFD`, `NFKC`, `NFKD`; `none` for another. -/
def normalize (form : String) (s : String) : Option String :=
  if !["NFC", "NFD", "NFKC", "NFKD"].contains form then none
  else if s.toList.all (fun c => c.toNat < 0xA0) then some s
  else match form with
    | "NFD" => some (ofCps (decompose false s))
    | "NFKD" => some (ofCps (decompose true s))
    | "NFC" => some (ofCps (compose (decompose false s)))
    | "NFKC" => some (ofCps (compose (decompose true s)))
    | _ => none

/-! ## Checks (the examples of UAX #15 Figure 3 to 6, and F&O 4.0 §5.4.9) -/

#guard normalize "NFC" "Å" == some "Å"
#guard normalize "NFD" "Å" == some "Å"
#guard normalize "NFD" "ḍ̇" == some "ḍ̇"
#guard normalize "NFC" "ḍ̇" == some "ḍ̇"
#guard normalize "NFKC" "ﬁ" == some "fi"
#guard normalize "NFKD" "\u1E9B\u0323" == some "s\u0323\u0307"
#guard normalize "NFC" "각" == some "각"
#guard normalize "NFD" "각" == some "각"
#guard normalize "NFC" "Å" == some "Å"

end L4Factoidal.XPath4.Unicode
