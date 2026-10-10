/-
L4Factoidal.Text.CaseMapTests -- build-time checks of Unicode case mapping.

Every `#guard` is evaluated during `lake build`. The positive cases state what
the Unicode Standard (section 3.13, section 5.18) and CaseFolding.txt give;
the negative cases fail an implementation that maps the ASCII letters only
(Lean core `String.toUpper` / `toLower`), one that ignores SpecialCasing.txt,
one that skips the Final_Sigma rule, and one that applies a language-specific
rule. Issue: https://github.com/danbri/factoidal/issues/706.
-/
import L4Factoidal.Text.CaseMap

namespace L4Factoidal.Text.CaseMapTests

open L4Factoidal.Text.CaseMap
open L4Factoidal.Text.CaseMapData

/-- The code points of a string, for comparing strings that contain
combining characters. -/
def cps (s : String) : List Nat := s.toList.map Char.toNat

/-! ### 1. The generated tables

The numbers are the line counts the generator printed in the header of
`CaseMapData.lean`; a table that lost a row, or a run that expanded to the
wrong set, changes them. -/

#guard CaseMap.unicodeVersion == "15.1.0"

def runCount (rs : Array MapRange) : Nat :=
  rs.foldl (fun n r => n + (r.hi - r.lo) / r.stride + 1) 0

#guard runCount upperRanges == 1450
#guard runCount lowerRanges == 1433
#guard runCount foldRanges == 1457
#guard specialUpper.size == 102
#guard specialLower.size == 1

/-- Runs sorted by `lo`, each run inside itself, and the next run after it. -/
def runsSorted (rs : Array MapRange) : Bool :=
  (List.range rs.size).all fun i =>
    match rs[i]?, rs[i + 1]? with
    | some a, some b => a.lo ≤ a.hi && a.hi < b.lo && 0 < a.stride
    | some a, none => a.lo ≤ a.hi && 0 < a.stride
    | _, _ => false

#guard runsSorted upperRanges
#guard runsSorted lowerRanges
#guard runsSorted foldRanges

def keysAscending {α : Type} (a : Array (Nat × α)) : Bool :=
  (List.range a.size).all fun i =>
    match a[i]?, a[i + 1]? with
    | some x, some y => x.1 < y.1
    | _, _ => true

#guard keysAscending specialUpper
#guard keysAscending specialLower

def rangesDisjoint (a : Array (Nat × Nat)) : Bool :=
  (List.range a.size).all fun i =>
    match a[i]?, a[i + 1]? with
    | some x, some y => x.1 ≤ x.2 && x.2 + 1 < y.1
    | some x, none => x.1 ≤ x.2
    | _, _ => true

#guard rangesDisjoint casedRanges
#guard rangesDisjoint caseIgnorableRanges

/-! ### 2. Simple mappings at the edges of runs

The first and last code point of a run map; the code point after it does not;
a stride-2 run skips the in-between code point. -/

#guard simpleUpper 0x61 == 0x41            -- a
#guard simpleUpper 0x7A == 0x5A            -- z
#guard simpleUpper 0x7B == 0x7B            -- {
#guard simpleUpper 0x60 == 0x60            -- `
#guard simpleUpper 0xE9 == 0xC9            -- é
#guard simpleUpper 0xF7 == 0xF7            -- division sign, between two runs
#guard simpleUpper 0xFF == 0x178           -- ÿ
#guard simpleUpper 0xB5 == 0x39C           -- micro sign
#guard simpleUpper 0x101 == 0x100          -- ā, stride-2 run
#guard simpleUpper 0x100 == 0x100          -- Ā maps to itself
#guard simpleLower 0x100 == 0x101
#guard simpleLower 0x101 == 0x101
#guard simpleLower 0x130 == 0x69           -- İ, simple mapping (full mapping is longer)
#guard simpleLower 0x212A == 0x6B          -- KELVIN SIGN
#guard simpleLower 0x1E9E == 0xDF          -- LATIN CAPITAL LETTER SHARP S
#guard simpleUpper 0x131 == 0x49           -- dotless i
#guard simpleUpper 0xDF == 0xDF            -- ß has no simple uppercase
#guard caseFoldCp 0x41 == 0x61
#guard caseFoldCp 0x3C2 == 0x3C3           -- final sigma folds to sigma
#guard caseFoldCp 0x212A == 0x6B
#guard caseFoldCp 0x1E9E == 0xDF           -- status S
#guard caseFoldCp 0xDF == 0xDF             -- ß: only a full folding (F) exists
#guard caseFoldCp 0x130 == 0x130           -- İ: only F and T foldings exist
#guard caseFoldCp 0x131 == 0x131           -- ı: only a T folding exists
#guard caseFoldCp 0x13A0 == 0x13A0         -- Cherokee capitals fold to themselves
#guard caseFoldCp 0xAB70 == 0x13A0         -- Cherokee small letters fold to capitals
#guard caseFoldCp 0x10400 == 0x10428       -- Deseret

/-! ### 3. `upperCase` -/

#guard upperCase "" == ""
#guard upperCase "abc" == "ABC"
#guard upperCase "é" == "É"
#guard upperCase "ÿ" == "Ÿ"                -- the result is outside Latin-1
#guard upperCase "école" == "ÉCOLE"
#guard upperCase "ÉCOLE" == "ÉCOLE"        -- already upper case
#guard upperCase "straße" == "STRASSE"     -- SpecialCasing.txt: ß -> SS
#guard upperCase "ẞ" == "ẞ"                -- capital sharp s stays
#guard upperCase "ŉ" == "ʼN"               -- one character becomes two
#guard upperCase "ﬁ" == "FI"               -- ligature fi
#guard upperCase "ǆ" == "Ǆ"                -- dz with caron
#guard upperCase "ς" == "Σ"                -- final sigma
#guard upperCase "σ" == "Σ"
#guard upperCase "ΐ" == "Ϊ́"
#guard upperCase "i" == "I"                -- language-independent: not İ
#guard upperCase "ı" == "I"                -- dotless i
#guard upperCase "ᏸ" == "Ᏸ"      -- Cherokee small letter ye
#guard upperCase "ꭰ" == "Ꭰ"      -- Cherokee small letter a
#guard upperCase "𐐨" == "𐐀" -- Deseret small letter long i
#guard upperCase "𐐀" == "𐐀"
#guard upperCase "123 !?-_" == "123 !?-_"  -- no case
#guard upperCase "日本語" == "日本語"
#guard upperCase "ͅ" == "Ι"      -- combining ypogegrammeni
-- negative: an implementation that maps the ASCII letters only fails these
#guard upperCase "é" != "é"
#guard upperCase "ß" != "ß"
#guard upperCase "ß" != "ẞ"                -- the simple mapping does not exist; the full one is SS
-- the length changes, so a per-character map cannot be right
#guard (upperCase "ß").length == 2
#guard (upperCase "ΐ").length == 3

/-! ### 4. `lowerCase` -/

#guard lowerCase "" == ""
#guard lowerCase "ABC" == "abc"
#guard lowerCase "É" == "é"
#guard lowerCase "ÉCOLE" == "école"
#guard lowerCase "école" == "école"        -- already lower case
#guard lowerCase "ß" == "ß"                -- stays
#guard lowerCase "ẞ" == "ß"
#guard lowerCase "I" == "i"                -- language-independent: not ı
#guard cps (lowerCase "İ") == [0x69, 0x307] -- SpecialCasing.txt: i + combining dot above
#guard cps (lowerCase "İstanbul") == [0x69, 0x307, 0x73, 0x74, 0x61, 0x6E, 0x62, 0x75, 0x6C]
#guard lowerCase "K" == "k"           -- KELVIN SIGN
#guard lowerCase "Å" == "å"           -- ANGSTROM SIGN
#guard lowerCase "Ꭰ" == "ꭰ"      -- Cherokee capital letter a
#guard lowerCase "Ᏸ" == "ᏸ"
#guard lowerCase "𐐀" == "𐐨" -- Deseret
#guard lowerCase "123 !?-_" == "123 !?-_"
#guard lowerCase "日本語" == "日本語"
-- negative
#guard lowerCase "É" != "É"
#guard lowerCase "İ" != "i"                -- two characters, not the simple mapping
#guard (lowerCase "İ").length == 2
#guard lowerCase "K" != "K"

/-! #### Final_Sigma (Unicode section 3.13, Table 3-17)

`Σ` is `ς` after a cased letter (case-ignorable characters may intervene) when
no cased letter follows (case-ignorable characters may intervene); otherwise
`σ`. -/

#guard lowerCase "ΑΣ" == "ας"              -- word end
#guard lowerCase "ΑΣΑ" == "ασα"            -- cased letter follows
#guard lowerCase "Σ" == "σ"                -- nothing before
#guard lowerCase "ΣΑ" == "σα"
#guard lowerCase "ΑΣ " == "ας "            -- space: not case-ignorable, no cased letter follows
#guard lowerCase "ΑΣ Α" == "ας α"          -- space ends the lookahead
#guard lowerCase "ΑΣ." == "ας."            -- "." is case-ignorable
#guard lowerCase "ΑΣ.Α" == "ασ.α"          -- case-ignorable, then a cased letter follows
#guard lowerCase "Α.Σ" == "α.ς"            -- case-ignorable between the cased letter and sigma
#guard lowerCase "1Σ" == "1σ"              -- a digit is not a cased letter
#guard lowerCase "ΟΔΥΣΣΕΥΣ" == "οδυσσευς"  -- the example of the Unicode Standard
#guard lowerCase "ΑΣ́" == "ας́"  -- combining acute is case-ignorable
#guard lowerCase "ΑΣ́Α" == "ασ́α"
#guard lowerCase "ς" == "ς"                -- a lower-case sigma form is not changed
#guard lowerCase "σ" == "σ"
-- negative: the rule is not "sigma always becomes sigma" or "always final"
#guard lowerCase "ΑΣ" != "ασ"
#guard lowerCase "ΑΣΑ" != "αςα"
#guard lowerCase "Σ" != "ς"

/-! #### The one-pass path agrees with the context-aware loop

`lowerCase` takes the one-pass path for a string without U+03A3. The loop
`lowerGo` is the definition; the two must agree wherever the fast path applies. -/

#guard caseAffected.get.toList.all fun c =>
  c == 0x3A3 ||
    let s := String.singleton (Char.ofNat c)
    lowerNoSigma s == lowerGo s.toList [] ""
#guard ["", "ABC école", "İSTANBUL ẞ \u212A", "123 !?-_ 日本語 Ꭰ 𐐀"].all fun s =>
  lowerNoSigma s == lowerGo s.toList [] "" && lowerCase s == lowerNoSigma s
-- with a sigma the loop decides
#guard lowerCase "ΑΣ" != lowerNoSigma "ΑΣ"

/-! ### 5. `caseFold` -/

#guard caseFold "" == ""
#guard caseFold "ABC" == "abc"
#guard caseFold "ΑΣς" == "ασσ"
#guard caseFold "K" == "k"
#guard caseFold "ẞ" == "ß"                 -- simple folding keeps the length
#guard caseFold "ß" == "ß"
#guard caseFold "İ" == "İ"
#guard caseFold "ꭰ" == "Ꭰ"
#guard caseFold "123 !?" == "123 !?"
-- negative
#guard caseFold "É" != "É"
#guard (caseFold "ß").length == 1

/-! ### 6. Case-variants (F&O 3.1 section 5.6.1.1) -/

#guard caseVariants 0x6B == [0x4B, 0x6B, 0x212A]       -- k, K, KELVIN SIGN
#guard caseVariants 0x212A == [0x4B, 0x6B, 0x212A]
#guard caseVariants 0x131 == [0x49, 0x69, 0x131]       -- dotless i: fn:upper-case is I
#guard caseVariants 0x31 == [0x31]                     -- a digit has none
#guard caseVariants 0x2D == [0x2D]
#guard caseVariants 0xDF == [0xDF, 0x1E9E]
#guard caseVariants 0x3C3 == [0x3A3, 0x3C2, 0x3C3]
#guard caseVariants 0x13A0 == [0x13A0, 0xAB70]
#guard caseVariants 0x10400 == [0x10400, 0x10428]
#guard caseVariants 0x130 == [0x130]                   -- lower-case is two characters
#guard isCaseVariant 0x6B 0x212A
#guard !isCaseVariant 0x6B 0x6A
#guard !isCaseVariant 0xDF 0x53

/-- Every listed variant is a variant, and the relation is symmetric. -/
def variantsConsistent (c : Nat) : Bool :=
  (caseVariants c).all fun v => isCaseVariant c v && (caseVariants v).contains c

#guard caseAffected.get.toList.all variantsConsistent

/-- A sample of code points checked against EVERY case-affected code point: no
variant is missing from the grouped answer. -/
def variantsComplete (c : Nat) : Bool :=
  caseAffected.get.toList.all fun v => !isCaseVariant c v || (caseVariants c).contains v

#guard ((List.range caseAffected.get.size).filter (· % 64 == 0)).all fun i =>
  variantsComplete (caseAffected.get.getD i 0)
-- and the classes where the F&O relation and CaseFolding.txt differ, or that
-- have three members
#guard [0x49, 0x69, 0x131, 0x3B8, 0x3D1, 0x3F4, 0x398, 0x6B, 0x212A, 0x3C2, 0xDF, 0x1E9E].all variantsComplete

-- ciRanges
#guard ciRanges [(0x41, 0x5A)] == [(0x41, 0x5A), (0x61, 0x7A), (0x131, 0x131), (0x17F, 0x17F), (0x212A, 0x212A)]
#guard ciRanges [(0x31, 0x39)] == [(0x31, 0x39)]
#guard ciRanges [] == []
#guard ciRanges [(0x6B, 0x6B)] == [(0x4B, 0x4B), (0x6B, 0x6B), (0x212A, 0x212A)]
#guard ciRanges (ciRanges [(0x41, 0x5A)]) == ciRanges [(0x41, 0x5A)]
-- a range that already holds a class adds nothing for it
#guard ciRanges [(0x4B, 0x4B), (0x6B, 0x6B), (0x212A, 0x212A)] == ciRanges [(0x6B, 0x6B)]
-- the whole code space holds every variant already
#guard ciRanges [(0, 0x10FFFF)] == [(0, 0x10FFFF)]
-- ranges outside the code space (regular-expression sentinels) pass through
#guard ciRanges [(0x110000, 0x110000)] == [(0x110000, 0x110000)]
-- an empty interval is dropped
#guard ciRanges [(5, 3)] == []

/-! ### 7. Properties over every case-affected code point

These hold for the tables as generated; a regenerated table that breaks one
fails the build. -/

-- `lowerCase` of a lower-case string is the string.
#guard caseAffected.get.toList.all fun c =>
  let s := String.singleton (Char.ofNat c)
  lowerCase (lowerCase s) == lowerCase s

-- The search fold ignores the difference between a string and its `LCASE`:
-- the property the literal search index needs (`Storage.LiteralGramIndex`).
#guard caseAffected.get.toList.all fun c =>
  let s := String.singleton (Char.ofNat c)
  searchFold (lowerCase s).toList == searchFold s.toList

-- and with sigma in context
#guard ["ΑΣ", "ΑΣΑ", "Σ", "ΟΔΥΣΣΕΥΣ", "İSTANBUL ΑΣ.", "KELVIN"].all fun s =>
  searchFold (lowerCase s).toList == searchFold s.toList

-- The characterwise fold sends a substring to a substring: it is a
-- concatenation of images.
#guard searchFold "ΑΣ".toList ++ searchFold "ΑΣ".toList == searchFold "ΑΣΑΣ".toList
#guard (searchFold "İ".toList).length == 2
#guard searchFold "ΑΣ".toList == searchFold "ας".toList     -- sigma forms agree
#guard searchFold "ΑΣ".toList != searchFold "αρ".toList

/-! ### 8. Strings that are long and pathological

`lowerGo` and `casedAhead` are tail-recursive, so the depth of the call stack
does not grow with the length of the string. -/

#guard (lowerCase (String.ofList (List.replicate 20000 'Σ'))).length == 20000
#guard (upperCase (String.ofList (List.replicate 20000 'ß'))).length == 40000
-- a long run of case-ignorable characters between two sigmas
#guard lowerCase ("ΑΣ" ++ String.ofList (List.replicate 5000 '.') ++ "Α")
  == "ασ" ++ String.ofList (List.replicate 5000 '.') ++ "α"

end L4Factoidal.Text.CaseMapTests
