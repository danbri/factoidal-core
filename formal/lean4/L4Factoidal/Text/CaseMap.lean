/-
L4Factoidal.Text.CaseMap -- Unicode default case mapping, simple case
folding, and the case-variant relation of regular expressions.

Lean core's `String.toUpper` and `String.toLower` map the ASCII letters and
nothing else (`Char.toUpper` and `Char.toLower` change `a`-`z` and `A`-`Z`
only; `"ÉCOLE".toLower` is `"École"`). Several specifications name Unicode
case mapping, and this module is the one implementation of it:

  * `upperCase` / `lowerCase` -- XPath and XQuery Functions and Operators 3.1
    section 5.4.7 `fn:upper-case` and section 5.4.8 `fn:lower-case`
    (https://www.w3.org/TR/xpath-functions-31/#func-upper-case), which defer
    to the Unicode Standard; SPARQL 1.1 section 17.4.3.8 `UCASE` and
    section 17.4.3.9 `LCASE`, which are defined by those two functions; RIF-DTB
    `func:upper-case` and `func:lower-case`; the GREL functions `toUpperCase`
    and `toLowerCase`, which are Java `String.toUpperCase` and `toLowerCase`
    with the root locale.
  * `caseFold` -- simple case folding of CaseFolding.txt (statuses C and S),
    Unicode Standard section 5.18.
  * `caseVariants`, `ciRanges` -- the case-variant relation of the regular
    expression flag `i`, F&O 3.1 section 5.6.1.1
    (https://www.w3.org/TR/xpath-functions-31/#flags).

## What "default case mapping" means here

Unicode Standard section 3.13 (Default Case Algorithms) and section 5.18 (Case
Mappings).

  * A character maps through the unconditional FULL mapping of
    SpecialCasing.txt when it has one (so `ß` upper-cases to `SS` and `ŉ` to
    `ʼN`), and through the SIMPLE mapping of UnicodeData.txt otherwise.
  * The mapping is language-independent. The language-specific lines of
    SpecialCasing.txt (Lithuanian, Turkish, Azeri) are not applied: `I` lower-
    cases to `i`, and `İ` (U+0130) lower-cases to `i` followed by U+0307, in
    every language. This is Java's root-locale behaviour.
  * The one context rule that is not language-specific, Final_Sigma, is
    applied by `lowerCase`: capital sigma `Σ` (U+03A3) lower-cases to final
    sigma `ς` (U+03C2) when it is preceded by a cased letter, possibly with
    case-ignorable characters between, and is not followed by case-ignorable
    characters and then a cased letter; otherwise to `σ` (U+03C3).
  * Upper-casing has no context rule.

## Tables

`CaseMapData.lean` is generated from ONE pinned Unicode version by
`tools/gen_casemap.py`; its header records the source files and their SHA-256
digests. A table is a sorted array. A lookup is a binary search
(`upperBound`), so the cost of one character is logarithmic in the table
size, never linear. Characters below U+0080 skip the tables.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashMap
import L4Factoidal.Text.CaseMapData

namespace L4Factoidal.Text.CaseMap

open L4Factoidal.Text.CaseMapData

/-- The Unicode version of the tables. -/
def unicodeVersion : String := CaseMapData.unicodeVersion

/-! ## Binary search -/

/-- The number of leading elements of the sorted array `a` whose key is at
most `c`, searched in `[lo, hi)`. Call with `lo = 0` and `hi = a.size`. The
result `i` has `key a[i - 1] ≤ c` when `i > 0`, and `c < key a[i]` when
`i < a.size`. -/
def upperBound {α : Type} (a : Array α) (key : α → Nat) (c lo hi : Nat) : Nat :=
  if lo < hi then
    match a[(lo + hi) / 2]? with
    | some x =>
        if key x ≤ c then upperBound a key c ((lo + hi) / 2 + 1) hi
        else upperBound a key c lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo

/-- The number of leading elements whose key is STRICTLY below `c`: the index
of the first element with key at least `c`. -/
def lowerBound {α : Type} (a : Array α) (key : α → Nat) (c : Nat) : Nat :=
  if c = 0 then 0 else upperBound a key (c - 1) 0 a.size

/-! ## Table lookups -/

/-- The image of `c` under a table of stride runs, or `none` when no run maps
it. -/
def lookupRuns (rs : Array MapRange) (c : Nat) : Option Nat :=
  let i := upperBound rs (·.lo) c 0 rs.size
  if i = 0 then none
  else
    match rs[i - 1]? with
    | some r =>
        if c ≤ r.hi && (c - r.lo) % r.stride == 0
        then some (Int.toNat ((c : Int) + r.delta))
        else none
    | none => none

/-- The entry of a sorted association array whose key is `c`. -/
def lookupSpecial (tbl : Array (Nat × List Nat)) (c : Nat) : Option (List Nat) :=
  let i := upperBound tbl (·.1) c 0 tbl.size
  if i = 0 then none
  else
    match tbl[i - 1]? with
    | some (k, v) => if k == c then some v else none
    | none => none

/-- Is `c` inside one of the sorted, disjoint ranges? -/
def inSortedRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool :=
  let i := upperBound rs (·.1) c 0 rs.size
  if i = 0 then false
  else
    match rs[i - 1]? with
    | some (_, hi) => c ≤ hi
    | none => false

/-! ## Code-point level mappings -/

/-- UnicodeData.txt simple uppercase mapping; `c` itself when there is none. -/
def simpleUpper (c : Nat) : Nat := (lookupRuns upperRanges c).getD c

/-- UnicodeData.txt simple lowercase mapping; `c` itself when there is none. -/
def simpleLower (c : Nat) : Nat := (lookupRuns lowerRanges c).getD c

/-- Simple case folding, CaseFolding.txt statuses C and S; `c` itself when
there is none. -/
def caseFoldCp (c : Nat) : Nat := (lookupRuns foldRanges c).getD c

/-- The FULL uppercase mapping of one code point: the SpecialCasing.txt
unconditional mapping when there is one, else the simple mapping. `ß` gives
`[S, S]`. There is no context rule for upper-casing. -/
def fullUpper (c : Nat) : List Nat :=
  match lookupSpecial specialUpper c with
  | some cps => cps
  | none => [simpleUpper c]

/-- The FULL lowercase mapping of one code point WITHOUT context: the
SpecialCasing.txt unconditional mapping when there is one, else the simple
mapping. `İ` gives `[i, U+0307]`. Capital sigma gives `σ`: the Final_Sigma
rule needs the neighbouring characters and is applied by `lowerCase`. -/
def fullLower (c : Nat) : List Nat :=
  match lookupSpecial specialLower c with
  | some cps => cps
  | none => [simpleLower c]

/-- Unicode property Cased (DerivedCoreProperties.txt). -/
def isCased (c : Nat) : Bool := inSortedRanges casedRanges c

/-- Unicode property Case_Ignorable (DerivedCoreProperties.txt). -/
def isCaseIgnorable (c : Nat) : Bool := inSortedRanges caseIgnorableRanges c

/-! ## Strings -/

/-- Append one code point to a string. Every code point the tables produce is
a Unicode scalar value. -/
def pushCp (acc : String) (cp : Nat) : String := acc.push (Char.ofNat cp)

/-- Unicode full uppercase of a string: `fn:upper-case`, `UCASE`. The result
can be longer than the argument (`ß` gives `SS`). -/
def upperCase (s : String) : String :=
  s.foldl
    (fun acc c =>
      if c.val < 0x80 then acc.push c.toUpper
      else (fullUpper c.toNat).foldl pushCp acc)
    ""

/-- Does a cased letter follow, after zero or more case-ignorable characters?
This is the lookahead of the Final_Sigma condition. A character that is both
case-ignorable and cased ends the scan with `true`: the sequence "zero or more
case-ignorable characters, then a cased letter" is then present. -/
def casedAhead : List Char → Bool
  | [] => false
  | c :: rest =>
      if isCased c.toNat then true
      else if isCaseIgnorable c.toNat then casedAhead rest
      else false

/-- Does a cased letter precede, with only case-ignorable characters between?
`before` holds the characters before the position, nearest first. This is the
lookbehind of the Final_Sigma condition. -/
def casedBehind : List Char → Bool := casedAhead

/-- The Final_Sigma condition of Unicode Standard section 3.13, Table 3-17,
at a position whose preceding characters (nearest first) are `before` and
whose following characters are `after`. -/
def finalSigma (before after : List Char) : Bool :=
  casedBehind before && !casedAhead after

/-- The lowercase mapping loop. `before` is the input read so far, nearest
character first. -/
def lowerGo : List Char → List Char → String → String
  | [], _, acc => acc
  | c :: rest, before, acc =>
      let out : String :=
        if c.val < 0x80 then acc.push c.toLower
        else if c.val == 0x3A3 then
          acc.push (if finalSigma before rest then 'ς' else 'σ')
        else (fullLower c.toNat).foldl pushCp acc
      lowerGo rest (c :: before) out

/-- Lowercase of a string that has no capital sigma: no character needs its
neighbours, so one pass over the string suffices. `lowerCase` uses it when the
string holds no U+03A3, and `lowerGo` gives the same result there
(`CaseMapTests`). -/
def lowerNoSigma (s : String) : String :=
  s.foldl
    (fun acc c =>
      if c.val < 0x80 then acc.push c.toLower
      else (fullLower c.toNat).foldl pushCp acc)
    ""

/-- Unicode full lowercase of a string, with the Final_Sigma context rule:
`fn:lower-case`, `LCASE`. The result can be longer than the argument (`İ`
gives `i` and U+0307). -/
def lowerCase (s : String) : String :=
  if s.any (fun c => c.val == 0x3A3) then lowerGo s.toList [] "" else lowerNoSigma s

/-- Simple case folding of a string, character by character: CaseFolding.txt
statuses C and S. The result has the length of the argument. -/
def caseFold (s : String) : String :=
  s.map (fun c => Char.ofNat (caseFoldCp c.toNat))

/-! ## The case-variant relation of the regular expression flag `i`

F&O 3.1 section 5.6.1.1: with the flag `i`, a character C2 is a case-variant
of a character C1 when the XPath expression
`fn:lower-case(C1) eq fn:lower-case(C2) or fn:upper-case(C1) eq
fn:upper-case(C2)` is true for the two characters taken as strings of length
one. A character matches the set of itself and its case-variants; a character
range matches every character it matches without the flag, and every
case-variant of those. For example `[A-Z]` matches U+212A KELVIN SIGN,
because `fn:lower-case` of it is `k`.

This relation is not CaseFolding.txt: `ı` (U+0131, dotless i) is a case-variant
of `i` because its uppercase is `I`, and CaseFolding.txt has no common or
simple folding for it. -/

/-- The lowercase of one character as a string of length one. A lone capital
sigma has no cased letter before it, so Final_Sigma does not apply. -/
def lowerOfChar (c : Nat) : List Nat := fullLower c

/-- C2 is a case-variant of C1 (F&O 3.1 section 5.6.1.1). -/
def isCaseVariant (c1 c2 : Nat) : Bool :=
  lowerOfChar c1 == lowerOfChar c2 || fullUpper c1 == fullUpper c2

/-- The code points a run table maps. -/
def runKeys (rs : Array MapRange) : List Nat :=
  rs.toList.flatMap (fun r =>
    (List.range ((r.hi - r.lo) / r.stride + 1)).map (fun i => r.lo + i * r.stride))

/-- Sorted, without repeats. -/
def sortedDedup (xs : List Nat) : Array Nat :=
  let sorted := xs.toArray.qsort (· < ·)
  sorted.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- Every code point that can have a case-variant other than itself: those
whose uppercase or lowercase is not themselves, and the single code points
those map to. A code point outside this array is its own only variant. The
array is built on first use (a `Thunk`) so that a program which never asks for
a case-variant pays nothing at start-up. -/
def caseAffected : Thunk (Array Nat) := Thunk.mk fun _ =>
  let keys := runKeys upperRanges ++ runKeys lowerRanges
    ++ specialUpper.toList.map (·.1) ++ specialLower.toList.map (·.1)
  sortedDedup (keys ++ keys.flatMap (fun k => fullUpper k ++ fullLower k))

/-- The code points of `caseAffected` that lie in `[lo, hi]`. -/
def affectedIn (lo hi : Nat) : Array Nat :=
  let all := caseAffected.get
  all.extract (lowerBound all id lo) (upperBound all id hi 0 all.size)

/-- The two groupings that define the relation: the code points of
`caseAffected` by lowercase, and by uppercase. Built on first use. -/
def variantGroups : Thunk (Std.HashMap (List Nat) (List Nat) × Std.HashMap (List Nat) (List Nat)) :=
  Thunk.mk fun _ =>
    caseAffected.get.foldl
      (fun (byLower, byUpper) c =>
        ( byLower.insert (fullLower c) (c :: (byLower.getD (fullLower c) [])),
          byUpper.insert (fullUpper c) (c :: (byUpper.getD (fullUpper c) [])) ))
      (∅, ∅)

/-- `c` and all its case-variants, without repeats, ascending. -/
def caseVariants (c : Nat) : List Nat :=
  let groups := variantGroups.get
  let sameLower := groups.1.getD (fullLower c) []
  let sameUpper := groups.2.getD (fullUpper c) []
  (sortedDedup (c :: (sameLower ++ sameUpper))).toList

/-- Sort ascending and merge overlapping or adjacent intervals. Empty
intervals (`lo > hi`) are dropped. -/
def normalizeRanges (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let sorted := (rs.filter (fun r => r.1 ≤ r.2)).toArray.qsort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  let merged := sorted.foldl
    (fun (acc : List (Nat × Nat)) r =>
      match acc with
      | (a, b) :: t => if r.1 ≤ b + 1 then (a, Nat.max b r.2) :: t else r :: acc
      | [] => [r])
    []
  merged.reverse

/-- The code points a character class matches under the flag `i`: the class
itself and every case-variant of a code point in it. The result is sorted and
merged. -/
def ciRanges (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let base := normalizeRanges rs
  let baseArr := base.toArray
  let extras : List (Nat × Nat) :=
    base.flatMap (fun (lo, hi) =>
      (affectedIn lo hi).toList.flatMap (fun c =>
        (caseVariants c).filterMap (fun v =>
          if inSortedRanges baseArr v then none else some (v, v))))
  normalizeRanges (base ++ extras)

/-! ## The fold used by search indexes

A search index that answers `CONTAINS(LCASE(?x), "needle")` has to normalise
the indexed text and the needle by one function, and it must keep every row the
engine's `LCASE` would keep. `LCASE` is not a character map (`İ` gives two
characters, `Σ` depends on its neighbours), so the index fold is the
characterwise image below. It is the context-free full lowercase, with final
sigma and capital sigma both folded to `σ`, which are the only two outputs of
`lowerCase` that depend on context. -/

/-- The fold image of one character: `fullLower`, with `Σ` and `ς` as `σ`. -/
def searchFoldImage (c : Char) : List Char :=
  if c.val < 0x80 then [c.toLower]
  else if c.val == 0x3A3 || c.val == 0x3C2 then ['σ']
  else (fullLower c.toNat).map Char.ofNat

/-- The fold of a character sequence: a concatenation of images, so a
contiguous part of the input folds to a contiguous part of the result. -/
def searchFold (cs : List Char) : List Char := cs.flatMap searchFoldImage

end L4Factoidal.Text.CaseMap
