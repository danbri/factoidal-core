/-
L4Factoidal.XPath4.Unicode — XPath compatibility APIs over the Unicode
18.0.0 normalization algorithms in L4Factoidal.Unicode.Normalization.

F&O 4.0 §5.4.9 FULLY-NORMALIZED puts a space before an initial composing
character and then applies NFC. XPath argument handling and unsupported
form errors remain in Serialize.normalizeUnicodeFn.
-/
import L4Factoidal.Unicode.Normalization

namespace L4Factoidal.XPath4.Unicode

open Std

def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0

/-- Combining class used by XPath collations, from the shared Unicode data. -/
def ccc (c : Nat) : Nat := L4Factoidal.Unicode.Normalization.ccc c

/-- Full decomposition of one code point, retained for XPath collations. -/
def decompChar (compat : Bool) (c : Nat) : List Nat :=
  (L4Factoidal.Unicode.Normalization.decompInto compat c #[]).toList

/-- Canonically ordered decomposition, retained for XPath collations. -/
def decompose (compat : Bool) (s : String) : Array Nat :=
  L4Factoidal.Unicode.Normalization.decomposeCps compat
    (L4Factoidal.Unicode.Normalization.cpsOfString s)

/-- `form` is one of `NFC`, `NFD`, `NFKC`, `NFKD`; `none` for another.
The low-character shortcut also preserves SerializeTheorems.normalize_low. -/
def normalize (form : String) (s : String) : Option String :=
  if !["NFC", "NFD", "NFKC", "NFKD"].contains form then none
  else if s.toList.all (fun c => c.toNat < 0xA0) then some s
  else match form with
    | "NFD" => some (L4Factoidal.Unicode.Normalization.nfd s)
    | "NFKD" => some (L4Factoidal.Unicode.Normalization.nfkd s)
    | "NFC" => some (L4Factoidal.Unicode.Normalization.nfc s)
    | "NFKC" => some (L4Factoidal.Unicode.Normalization.nfkc s)
    | _ => none

/-- Second characters of the shared normalizer's primary composite pairs.
Its pairKey encodes (a, b) as a * 0x110000 + b. -/
def secondOfPrimary : HashMap Nat Unit :=
  L4Factoidal.Unicode.Normalization.compMap.toList.foldl
    (fun m (key, _) => m.insert (key % 0x110000) ()) {}

/-- A composing character (F&O 4.0 §5.4.9): non-zero combining class,
second character of a primary composite, or Hangul vowel/trailing jamo. -/
def isComposing (c : Nat) : Bool :=
  ccc c != 0 || secondOfPrimary.contains c ||
  (L4Factoidal.Unicode.Normalization.vBase ≤ c &&
    c < L4Factoidal.Unicode.Normalization.vBase + L4Factoidal.Unicode.Normalization.vCount) ||
  (L4Factoidal.Unicode.Normalization.tBase < c &&
    c < L4Factoidal.Unicode.Normalization.tBase + L4Factoidal.Unicode.Normalization.tCount)

/-- FULLY-NORMALIZED: prepend a space if the first character composes,
then apply NFC (F&O 4.0 §5.4.9). -/
def fullyNormalize (s : String) : String :=
  let s := match s.toList with
    | c :: _ => if isComposing c.toNat then " " ++ s else s
    | [] => s
  (normalize "NFC" s).getD s

/-! ## Checks (the examples of UAX #15 Figure 3 to 6, and F&O 4.0 §5.4.9) -/

#guard fullyNormalize "blah" == "blah"
#guard fullyNormalize (String.ofList [Char.ofNat 2494]) == String.ofList [' ', Char.ofNat 2494]
#guard fullyNormalize (String.ofList [Char.ofNat 0x301, 'a']) == String.ofList [' ', Char.ofNat 0x301, 'a']
#guard fullyNormalize (String.ofList ['e', Char.ofNat 0x301]) == String.ofList [Char.ofNat 0xE9]

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
