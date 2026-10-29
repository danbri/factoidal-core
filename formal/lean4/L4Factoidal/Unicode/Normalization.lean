/-
L4Factoidal.Unicode.Normalization — Unicode Normalization Forms (UAX #15
revision 58, Unicode 18.0.0): `nfd`, `nfc`, `nfkd`, `nfkc`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

Full decomposition (§1.3: canonical, or compatibility) from the generated
tables of `Unicode.NormData`; Hangul syllables by the arithmetic of
Unicode §3.12; the canonical ordering algorithm (§3: a stable sort of each
run of non-starters by Canonical_Combining_Class); the canonical
composition algorithm (§4: a character is blocked from the last starter
when a character between them has class 0 or a class not lower than its
own). The primary composites exclude Full_Composition_Exclusion.

The work is done on arrays of code points (`Array Nat`), so a caller that
holds code points outside the Lean `Char` range (the conformance runner
checks every code point of the standard) needs no conversion. The String
functions are wrappers. All loops are `for`/`while` loops.
-/
import Std.Data.HashMap
import L4Factoidal.Unicode.RangeTable
import L4Factoidal.Unicode.NormData

namespace L4Factoidal.Unicode.Normalization

open Std

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0

private def entries (t : String) : List (String × String) :=
  (t.splitOn ";").filterMap (fun e => match e.splitOn ":" with
    | [a, b] => some (a, b)
    | _ => none)

private def cpsOf (s : String) : List Nat :=
  (s.splitOn " ").filter (· != "") |>.map hexVal

/-- Canonical_Combining_Class (value 0 for a code point not listed). -/
def cccTable : RangeTable := RangeTable.ofText NormData.cccText

def ccc (c : Nat) : Nat := (cccTable.get c.toUInt32).toNat

def canonMap : HashMap Nat (Array Nat) :=
  (entries NormData.canonText).foldl
    (fun m (a, b) => m.insert (hexVal a) (cpsOf b).toArray) {}

def compatMap : HashMap Nat (Array Nat) :=
  (entries NormData.compatText).foldl
    (fun m (a, b) => m.insert (hexVal a) (cpsOf b).toArray) {}

def pairKey (a b : Nat) : Nat := a * 0x110000 + b

def compMap : HashMap Nat Nat :=
  (entries NormData.compText).foldl (fun m (a, b) =>
    match cpsOf a with
    | [x, y] => m.insert (pairKey x y) (hexVal b)
    | _ => m) {}

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

def isHangulSyllable (c : Nat) : Bool := sBase ≤ c && c < sBase + sCount

/-- The full decomposition of one code point, appended to `out`. -/
def decompInto (compat : Bool) (c : Nat) (out : Array Nat) : Array Nat :=
  if c < 0xA0 then out.push c
  else if isHangulSyllable c then
    let si := c - sBase
    let out := (out.push (lBase + si / nCount)).push (vBase + (si % nCount) / tCount)
    if si % tCount == 0 then out else out.push (tBase + si % tCount)
  else match (if compat then compatMap.get? c else none) with
    | some d => out ++ d
    | none =>
      match canonMap.get? c with
      | some d => out ++ d
      | none => out.push c

/-- The canonical ordering algorithm: a stable insertion sort of each run of
non-starters by combining class. -/
def reorder (xs : Array Nat) : Array Nat := Id.run do
  let mut a := xs
  let n := a.size
  let mut i := 0
  while i < n do
    if ccc a[i]! == 0 then
      i := i + 1
    else
      let mut j := i + 1
      while j < n && ccc a[j]! != 0 do
        j := j + 1
      -- sort a[i..j]
      let mut k := i + 1
      while k < j do
        let x := a[k]!
        let cx := ccc x
        let mut m := k
        while m > i && ccc a[m - 1]! > cx do
          a := a.set! m a[m - 1]!
          m := m - 1
        a := a.set! m x
        k := k + 1
      i := j
  return a

/-- Full decomposition (canonical, or compatibility if `compat`) followed
by canonical ordering, over code points. -/
def decomposeCps (compat : Bool) (xs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty xs.size
  for c in xs do
    out := decompInto compat c out
  return reorder out

/-- The primary composite of a pair, Hangul included. -/
def composePair (a b : Nat) : Option Nat :=
  if lBase ≤ a && a < lBase + lCount && vBase ≤ b && b < vBase + vCount then
    some (sBase + ((a - lBase) * vCount + (b - vBase)) * tCount)
  else if isHangulSyllable a && (a - sBase) % tCount == 0 && tBase < b && b < tBase + tCount then
    some (a + (b - tBase))
  else compMap.get? (pairKey a b)

/-- The canonical composition algorithm (UAX #15 §4) over code points that
are already decomposed and canonically ordered. -/
def composeCps (xs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty xs.size
  let mut starter : Option Nat := none
  let mut lastCcc : Nat := 0
  for c in xs do
    let cc := ccc c
    let mut done := false
    if let some si := starter then
      let adjacent := out.size == si + 1
      let blocked := !adjacent && (lastCcc == 0 || lastCcc ≥ cc)
      if !blocked then
        if let some comp := composePair out[si]! c then
          out := out.set! si comp
          done := true
    if !done then
      if cc == 0 then starter := some out.size
      out := out.push c
      lastCcc := cc
  return out

def nfdCps (xs : Array Nat) : Array Nat := decomposeCps false xs
def nfkdCps (xs : Array Nat) : Array Nat := decomposeCps true xs
def nfcCps (xs : Array Nat) : Array Nat := composeCps (decomposeCps false xs)
def nfkcCps (xs : Array Nat) : Array Nat := composeCps (decomposeCps true xs)

def cpsOfString (s : String) : Array Nat :=
  s.foldl (fun a c => a.push c.toNat) #[]

def stringOfCps (xs : Array Nat) : String :=
  xs.foldl (fun s c => s.push (Char.ofNat c)) ""

/-- Normalization Form D. -/
def nfd (s : String) : String := stringOfCps (nfdCps (cpsOfString s))
/-- Normalization Form KD. -/
def nfkd (s : String) : String := stringOfCps (nfkdCps (cpsOfString s))
/-- Normalization Form C. -/
def nfc (s : String) : String := stringOfCps (nfcCps (cpsOfString s))
/-- Normalization Form KC. -/
def nfkc (s : String) : String := stringOfCps (nfkcCps (cpsOfString s))

/-! ## Checks (UAX #15 Figures 3 to 6) -/

#guard nfc "Å" == "Å"
#guard nfd "Å" == "Å"
#guard nfd "ḍ̇" == "ḍ̇"
#guard nfc "ḍ̇" == "ḍ̇"
#guard nfkc "ﬁ" == "fi"
#guard nfkd "ẛ̣" == "ṩ"
#guard nfc "ẛ̣" == "ẛ̣"
#guard nfkc "ẛ̣" == "ṩ"
#guard nfc "각" == "각"
#guard nfd "각" == "각"
#guard nfc "각" == "각"
#guard nfc "" == ""

end L4Factoidal.Unicode.Normalization
