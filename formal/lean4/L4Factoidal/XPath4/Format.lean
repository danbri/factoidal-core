/-
L4Factoidal.XPath4.Format — formatting of numbers and dates (F&O 4.0
§5.4 `fn:format-integer`, §5.5 `fn:format-number`, §9.8
`fn:format-dateTime`, `fn:format-date`, `fn:format-time`) and
`fn:parse-ietf-date` (§9.9.1).

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c (`xpath-functions.xml` §5.4,
§5.5, §9.8; `function-catalog.xml`).

Languages: English, German, French and Italian (names, words, ordinals;
the other three are `XPath4.NumberWords`). Another language gives English
output, and the date functions then prefix `[Language: en]` (§9.8.4.8). Calendars: `AD` and `ISO`; another calendar gives `AD` output
with the prefix `[Calendar: AD]`. Places: an IANA zone name in `place` (`XPath4.Tz`) adjusts a dateTime
with a timezone to that zone's civil time; any other `place` is ignored.

Decimal digit families are the Unicode 15.1 `Nd` ranges (each a run of
ten code points with digit values 0 to 9; the list of zero digits below).
Letters and other numbers (categories L and N) are recognised for the
Latin, Greek, Cyrillic, Armenian, Hebrew, Arabic, Indic, Thai, CJK and
Hangul blocks and the Unicode number forms; a character outside those is
treated as a grouping separator, which is the rule for every character
that is not alphanumeric.
-/
import L4Factoidal.XPath4.Lib
import L4Factoidal.Fn.DateTime
import L4Factoidal.XPath4.Tz
import L4Factoidal.XPath4.NumberWords

namespace L4Factoidal.XPath4

open L4Factoidal.XSD
open L4Factoidal.Fn.DateTime (civilFromDays)

/-! ## Unicode digits and letters -/

/-- The zero digit of every Unicode 15.1 `Nd` digit family. -/
def ndZeros : List Nat := [0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66,
  0xbe6, 0xc66, 0xce6, 0xd66, 0xde6, 0xe50, 0xed0, 0xf20, 0x1040, 0x1090, 0x17e0, 0x1810,
  0x1946, 0x19d0, 0x1a80, 0x1a90, 0x1b50, 0x1bb0, 0x1c40, 0x1c50, 0xa620, 0xa8d0, 0xa900,
  0xa9d0, 0xa9f0, 0xaa50, 0xabf0, 0xff10, 0x104a0, 0x10d30, 0x11066, 0x110f0, 0x11136,
  0x111d0, 0x112f0, 0x11450, 0x114d0, 0x11650, 0x116c0, 0x11730, 0x118e0, 0x11950, 0x11c50,
  0x11d50, 0x11da0, 0x11f50, 0x16a60, 0x16ac0, 0x16b50, 0x1d7ce, 0x1d7d8, 0x1d7e2, 0x1d7ec,
  0x1d7f6, 0x1e140, 0x1e2f0, 0x1e4f0, 0x1e950, 0x1fbf0]

/-- The zero of the digit family `c` belongs to. -/
def digitZero? (c : Char) : Option Nat :=
  ndZeros.find? (fun z => z ≤ c.toNat && c.toNat < z + 10)

def isDigitU (c : Char) : Bool := (digitZero? c).isSome

/-- Letters (category L), approximately: see the module header. -/
def isLetterU (c : Char) : Bool :=
  let n := c.toNat
  c.isAlpha || n == 0xAA || n == 0xB5 || n == 0xBA ||
  (0xC0 ≤ n && n ≤ 0x24F && n != 0xD7 && n != 0xF7) || (0x250 ≤ n && n ≤ 0x2C1) ||
  (0x370 ≤ n && n ≤ 0x3FF && n != 0x375 && n != 0x37E && n != 0x384 && n != 0x385 && n != 0x387) ||
  (0x400 ≤ n && n ≤ 0x481) || (0x48A ≤ n && n ≤ 0x52F) ||
  (0x531 ≤ n && n ≤ 0x556) || (0x561 ≤ n && n ≤ 0x587) ||
  (0x5D0 ≤ n && n ≤ 0x5EA) || (0x620 ≤ n && n ≤ 0x64A) ||
  (0x905 ≤ n && n ≤ 0x939) || (0xE01 ≤ n && n ≤ 0xE30) ||
  (0x1E00 ≤ n && n ≤ 0x1FFF) || (0x3041 ≤ n && n ≤ 0x30FF) ||
  (0x4E00 ≤ n && n ≤ 0x9FFF) || (0xAC00 ≤ n && n ≤ 0xD7A3)

/-- Other numbers (categories Nl, No), approximately. -/
def isOtherNumber (c : Char) : Bool :=
  let n := c.toNat
  n == 0xB2 || n == 0xB3 || n == 0xB9 || (0xBC ≤ n && n ≤ 0xBE) ||
  (0x2070 ≤ n && n ≤ 0x2089 && n != 0x2071 && n != 0x2072 && n != 0x2073) ||
  (0x2150 ≤ n && n ≤ 0x2189) || (0x2460 ≤ n && n ≤ 0x249B) || (0x24EA ≤ n && n ≤ 0x24FF) ||
  (0x2776 ≤ n && n ≤ 0x2793) || (0x3007 == n) || (0x3021 ≤ n && n ≤ 0x3029)

def isAlnumU (c : Char) : Bool := isDigitU c || isLetterU c || isOtherNumber c

/-! ## Integer sequences -/

def radixDigits (r : Nat) (n : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | f + 1, m, acc => if m < r then m :: acc else go f (m / r) ((m % r) :: acc)
  if r < 2 then [n] else go 200 n []

def alphabet36 : String := "0123456789abcdefghijklmnopqrstuvwxyz"

/-- Bijective base-`k` numbering: 1 = first symbol. -/
def bijective (k : Nat) (n : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | f + 1, m, acc => if m == 0 then acc else go f ((m - 1) / k) (((m - 1) % k) :: acc)
  go 200 n []

def alphaSeq (upper : Bool) (n : Nat) : String :=
  String.ofList ((bijective 26 n).map (fun d => Char.ofNat ((if upper then 65 else 97) + d)))

def greekSeq (upper : Bool) (n : Nat) : String :=
  -- α..ω without final sigma (U+03C2); upper: Α..Ω without U+03A2
  let base := if upper then 0x391 else 0x3B1
  String.ofList ((bijective 24 n).map (fun d => Char.ofNat (base + (if d ≥ 17 then d + 1 else d))))

def romanSeq (upper : Bool) (n : Nat) : String :=
  let tbl : List (Nat × String) := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"),
    (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
  let rec go : Nat → Nat → List (Nat × String) → String
    | 0, _, _ => ""
    | _, _, [] => ""
    | f + 1, m, (v, s) :: rest => if m ≥ v then s ++ go f (m - v) ((v, s) :: rest) else go f m rest
  let s := go 100 n tbl
  if upper then s.toUpper else s

def onesW : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
  "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen",
  "eighteen", "nineteen"]
def tensW : List String := ["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy",
  "eighty", "ninety"]
def scalesW : List String := ["", "thousand", "million", "billion", "trillion", "quadrillion",
  "quintillion", "sextillion", "septillion", "octillion", "nonillion", "decillion"]

def words100 (n : Nat) : String :=
  if n < 20 then onesW.getD n ""
  else tensW.getD (n / 10) "" ++ (if n % 10 == 0 then "" else "-" ++ onesW.getD (n % 10) "")

def words1000 (n : Nat) : String :=
  if n < 100 then words100 n
  else onesW.getD (n / 100) "" ++ " hundred" ++ (if n % 100 == 0 then "" else " and " ++ words100 (n % 100))

/-- English cardinal words. -/
def wordsCard (n : Nat) : String :=
  if n == 0 then "zero" else
  let groups := (radixDigits 1000 n).reverse   -- least significant first
  let parts := (groups.zipIdx).filterMap (fun (g, i) =>
    if g == 0 then none
    else some (words1000 g ++ (if i == 0 then "" else " " ++ scalesW.getD i "")))
  let parts := parts.reverse
  -- "one thousand and five"
  match parts.reverse, groups with
  | last :: (_ :: _), g0 :: _ =>
    if g0 != 0 && g0 < 100 then
      String.intercalate " " (parts.dropLast) ++ " and " ++ last
    else String.intercalate " " parts
  | _, _ => String.intercalate " " parts

def ordinalWord (w : String) : String :=
  match w with
  | "one" => "first" | "two" => "second" | "three" => "third" | "five" => "fifth"
  | "eight" => "eighth" | "nine" => "ninth" | "twelve" => "twelfth"
  | _ => if w.endsWith "y" then (w.dropEnd 1).toString ++ "ieth" else w ++ "th"

/-- English ordinal words: the last word becomes ordinal. -/
def wordsOrd (n : Nat) : String :=
  let c := wordsCard n
  let cs := c.toList
  let idx := (cs.zipIdx.filter (fun (ch, _) => ch == ' ' || ch == '-')).getLast?.map (·.2)
  match idx with
  | some i => String.ofList (cs.take (i + 1)) ++ ordinalWord (String.ofList (cs.drop (i + 1)))
  | none => ordinalWord c

def ordSuffix (n : Nat) : String :=
  if n % 100 ≥ 11 && n % 100 ≤ 13 then "th"
  else match n % 10 with | 1 => "st" | 2 => "nd" | 3 => "rd" | _ => "th"

def titleCase (s : String) : String :=
  String.intercalate " " (((s.replace "-" " ").splitOn " ").map (fun w =>
    match w.toList with
    | c :: r => String.ofList (c.toUpper :: r)
    | [] => ""))

/-! ## Decimal digit patterns (§5.4.1) -/

structure DigitPat where
  mand : Nat
  total : Nat
  /-- The zero of the digit family (ASCII `0` for a radix). -/
  zero : Nat
  radix : Nat := 10
  upper : Bool := false
  /-- (position, character) of each grouping separator. -/
  seps : List (Nat × Char)
deriving Inhabited

def fmtErr {α} (msg : String) : M α := err "FODF1310" msg

/-- Parse a digit pattern. `radix` is `some r` for a `r^xxx` picture. -/
def parseDigitPat (tok : List Char) (radix : Option Nat) : M DigitPat := do
  -- classify: 0 optional, 1 mandatory, 2 separator
  let mut kinds : Array (Nat × Char) := #[]
  let mut zero : Option Nat := none
  let mut upper : Option Bool := none
  for c in tok do
    if c == '#' then kinds := kinds.push (0, c)
    else
      match radix with
      | some _ =>
        if c == 'x' || c == 'X' then
          match upper with
          | some u => if u != (c == 'X') then fmtErr "mixed x and X in a radix picture"
          | none => upper := some (c == 'X')
          kinds := kinds.push (1, c)
        else if isAlnumU c then fmtErr "a letter or digit in a radix picture"
        else kinds := kinds.push (2, c)
      | none =>
        match digitZero? c with
        | some z =>
          match zero with
          | some z0 => if z0 != z then fmtErr "digits from different families"
          | none => zero := some z
          kinds := kinds.push (1, c)
        | none =>
          if isAlnumU c then fmtErr "a letter in a decimal digit pattern"
          else kinds := kinds.push (2, c)
  let ks := kinds.toList
  if !(ks.any (·.1 == 1)) then fmtErr "no mandatory digit sign"
  -- optional digit signs precede the mandatory ones
  let firstMand := (ks.findIdx? (·.1 == 1)).getD 0
  if (ks.drop firstMand).any (·.1 == 0) then fmtErr "an optional digit sign after a mandatory one"
  match ks.head?, ks.getLast? with
  | some (2, _), _ => fmtErr "a grouping separator at the start"
  | _, some (2, _) => fmtErr "a grouping separator at the end"
  | _, _ => pure ()
  let pairs := ks.zip (ks.drop 1)
  if pairs.any (fun (a, b) => a.1 == 2 && b.1 == 2) then fmtErr "adjacent grouping separators"
  let digitsAfter (i : Nat) : Nat := ((ks.drop (i + 1)).filter (·.1 != 2)).length
  let seps := (ks.zipIdx.filter (·.1.1 == 2)).map (fun ((_, c), i) => (digitsAfter i, c))
  let total := (ks.filter (·.1 != 2)).length
  pure { mand := (ks.filter (·.1 == 1)).length, total, zero := zero.getD 0x30,
         radix := radix.getD 10, upper := upper.getD false, seps }

/-- The grouping separator template, as a function of the position. -/
def sepTemplate (p : DigitPat) : Nat → Option Char :=
  match p.seps with
  | [] => fun _ => none
  | (g0, c0) :: _ =>
    let g := (p.seps.map (·.1)).foldl min g0
    let regular := g > 0 && p.seps.all (fun (q, c) => c == c0 && q % g == 0) &&
      ((List.range p.total).all (fun k => k == 0 || k % g != 0 || (p.seps.any (·.1 == k))))
    if regular then fun q => if q > 0 && q % g == 0 then some c0 else none
    else fun q => (p.seps.find? (·.1 == q)).map (·.2)

def fmtDigitPat (p : DigitPat) (n : Nat) : String :=
  let ds := radixDigits p.radix n
  let ds := List.replicate (p.mand - min p.mand ds.length) 0 ++ ds
  let chars := ds.map (fun d =>
    if p.radix != 10 || p.zero == 0x30 then
      let c := alphabet36.toList.getD d '0'
      if p.upper then c.toUpper else c
    else Char.ofNat (p.zero + d))
  let len := chars.length
  let tmpl := sepTemplate p
  String.ofList (chars.zipIdx.flatMap (fun (c, i) =>
    let right := len - i
    if i > 0 then (match tmpl right with | some s => [s, c] | none => [c]) else [c]))

/-! ## fn:format-integer -/

/-- The format modifier: (ordinal?, alphabetic/traditional, the text in
    the parentheses). -/
def parseIntModifierV (m : String) : M (Bool × Option Char × Option String) := do
  let cs := m.toList
  let (ord, rest) ← match cs with
    | 'o' :: r => pure (true, r)
    | 'c' :: r => pure (false, r)
    | r => pure (false, r)
  let (variant, rest) ← match rest with
    | '(' :: r =>
      if cs.head? != some 'o' && cs.head? != some 'c' then fmtErr "a parenthesis without c or o" else
      match r.findIdx? (· == ')') with
      | some i =>
        if i == 0 then fmtErr "empty parentheses in the format modifier"
        else pure (some (String.ofList (r.take i)), r.drop (i + 1))
      | none => fmtErr "unclosed parenthesis in the format modifier"
    | r => pure (none, r)
  match rest with
  | [] => pure (ord, none, variant)
  | [c] => if c == 'a' || c == 't' then pure (ord, some c, variant) else fmtErr ("bad format modifier " ++ m)
  | _ => fmtErr ("bad format modifier " ++ m)

def parseIntModifier (m : String) : M (Bool × Option Char) := do
  let (o, a, _) ← parseIntModifierV m
  pure (o, a)

/-- Split the picture at its last semicolon (if any). -/
def splitPicture (pic : String) : String × String :=
  let cs := pic.toList
  match (cs.zipIdx.filter (·.1 == ';')).getLast? with
  | some (_, i) => (String.ofList (cs.take i), String.ofList (cs.drop (i + 1)))
  | none => (pic, "")

/-- A radix prefix `r^` (2 ≤ r ≤ 36) followed by a token with `x`/`X`. -/
def radixPrefix (tok : List Char) : Option (Nat × List Char) :=
  match tok.findIdx? (· == '^') with
  | some i =>
    let pre := tok.take i
    let rest := tok.drop (i + 1)
    if pre.isEmpty || !pre.all Char.isDigit || pre.head? == some '0' then none
    else
      let r := (String.ofList pre).toNat!
      if r ≥ 2 && r ≤ 36 && rest.any (fun c => c == 'x' || c == 'X') then some (r, rest) else none
  | none => none

/-- Format a non-negative number by a primary token (no sign). -/
def fmtIntToken (tok : List Char) (n : Nat) (ord : Bool) (lang : String)
    (variant : Option String := none) : M String := do
  -- words in German, French or Italian (`XPath4.NumberWords`)
  let words : String :=
    (if ord then NumberWords.ord? lang n variant else NumberWords.card? lang n).getD
      (if ord then wordsOrd n else wordsCard n)
  let capFirst (w : String) : String := match w.toList with
    | c :: r => Fn.String.upperCase (String.singleton c) ++ String.ofList r
    | [] => ""
  let titled : String :=
    if NumberWords.hasLang lang && n < 1000000000 then String.intercalate " " ((words.splitOn " ").map capFirst)
    else titleCase words
  match radixPrefix tok with
  | some (r, rest) =>
    let p ← parseDigitPat rest (some r)
    pure (fmtDigitPat p n ++ (if ord then ordSuffix n else ""))
  | none =>
  if tok.any isDigitU then
    let p ← parseDigitPat tok none
    pure (fmtDigitPat p n ++ (if ord then ordSuffix n else ""))
  else
    let dflt : M String := do
      pure (toString n ++ (if ord then ordSuffix n else ""))
    match String.ofList tok with
    | "A" => if n == 0 then dflt else pure (alphaSeq true n)
    | "a" => if n == 0 then dflt else pure (alphaSeq false n)
    | "I" => if n == 0 || n > 4999 then dflt else pure (romanSeq true n)
    | "i" => if n == 0 || n > 4999 then dflt else pure (romanSeq false n)
    | "w" => pure words
    | "W" => pure (Fn.String.upperCase words)
    | "Ww" => pure titled
    | "α" => if n == 0 then dflt else pure (greekSeq false n)
    | "Α" => if n == 0 then dflt else pure (greekSeq true n)
    | _ =>
      match tok with
      | [c] =>
        let k := c.toNat
        -- circled and parenthesised numbers, digit-full-stop
        if k == 0x2460 && n ≥ 1 && n ≤ 20 then pure (String.singleton (Char.ofNat (0x2460 + n - 1)))
        else if k == 0x2474 && n ≥ 1 && n ≤ 20 then pure (String.singleton (Char.ofNat (0x2474 + n - 1)))
        else if k == 0x2488 && n ≥ 1 && n ≤ 20 then pure (String.singleton (Char.ofNat (0x2488 + n - 1)))
        else if k == 0x2160 && n ≥ 1 && n ≤ 12 then pure (String.singleton (Char.ofNat (0x2160 + n - 1)))
        else if k == 0x2170 && n ≥ 1 && n ≤ 12 then pure (String.singleton (Char.ofNat (0x2170 + n - 1)))
        else if k == 0x3B1 && n ≥ 1 then pure (greekSeq false n)
        else if (k == 0x410 || k == 0x430) && n ≥ 1 && n ≤ 32 then
          pure (String.singleton (Char.ofNat (k + n - 1)))
        else dflt
      | _ => dflt

def formatInteger (v : Int) (pic : String) (lang : String) : M String := do
  let (tok, modi) := splitPicture pic
  if tok.isEmpty then fmtErr "empty primary format token"
  let (ord, _, variant) ← parseIntModifierV modi
  let s ← fmtIntToken tok.toList v.natAbs ord lang variant
  pure ((if v < 0 then "-" else "") ++ s)

/-! ## fn:format-number -/

/-- A decimal format (§5.5.1). Marker characters, and renditions. -/
structure DecFormat where
  decSep : Char := '.'
  decSepR : String := "."
  grpSep : Char := ','
  grpSepR : String := ","
  expSep : Char := 'e'
  expSepR : String := "e"
  infinity : String := "Infinity"
  minus : String := "-"
  nan : String := "NaN"
  percent : Char := '%'
  percentR : String := "%"
  permille : Char := '‰'
  permilleR : String := "‰"
  zero : Nat := 0x30
  digit : Char := '#'
  patSep : Char := ';'
deriving Inhabited

/-- Apply one property (name, value) to a decimal format. -/
def DecFormat.set (f : DecFormat) (k v : String) : M DecFormat := do
  let mr (v : String) : M (Char × String) :=
    match v.toList with
    | [c] => pure (c, v)
    | c :: ':' :: r => pure (c, String.ofList r)
    | _ => err "FODF1290" ("invalid value for decimal format property " ++ k)
  let one (v : String) : M Char :=
    match v.toList with
    | [c] => pure c
    | _ => err "FODF1290" ("invalid value for decimal format property " ++ k)
  match k with
  | "decimal-separator" => let (c, r) ← mr v; pure { f with decSep := c, decSepR := r }
  | "grouping-separator" => let (c, r) ← mr v; pure { f with grpSep := c, grpSepR := r }
  | "exponent-separator" => let (c, r) ← mr v; pure { f with expSep := c, expSepR := r }
  | "percent" => let (c, r) ← mr v; pure { f with percent := c, percentR := r }
  | "per-mille" => let (c, r) ← mr v; pure { f with permille := c, permilleR := r }
  | "infinity" => pure { f with infinity := v }
  | "minus-sign" => pure { f with minus := v }
  | "NaN" => pure { f with nan := v }
  | "zero-digit" =>
    let c ← one v
    match digitZero? c with
    | some z => if z == c.toNat then pure { f with zero := z } else err "FODF1290" "zero-digit must have digit value zero"
    | none => err "FODF1290" "zero-digit must be a digit"
  | "digit" => let c ← one v; pure { f with digit := c }
  | "pattern-separator" => let c ← one v; pure { f with patSep := c }
  | "format-name" => pure f
  | _ => err "FODF1290" ("unknown decimal format property " ++ k)

/-- The decimal format properties must be distinct characters. -/
def DecFormat.check (f : DecFormat) : M Unit := do
  let cs := [f.decSep, f.grpSep, f.percent, f.permille, f.digit, f.patSep, f.expSep]
  let ds := (List.range 10).map (fun d => Char.ofNat (f.zero + d))
  let all := cs ++ ds
  if all.length != (all.eraseDups).length then
    err "FODF1290" "decimal format properties are not distinct"

structure SubPic where
  pre : String
  suf : String
  intGroups : List Nat
  regular : Option Nat
  minInt : Nat
  scale : Nat
  fracGroups : List Nat
  minFrac : Nat
  maxFrac : Nat
  minExp : Nat
  pct : Bool
  pml : Bool
  hasDecSep : Bool
deriving Inhabited

def analyzeSub (f : DecFormat) (pic : List Char) : M SubPic := do
  let isFam (c : Char) := f.zero ≤ c.toNat && c.toNat < f.zero + 10
  let isActive0 (c : Char) := c == f.decSep || c == f.grpSep || c == f.digit || c == f.patSep || isFam c
  let isActiveE (c : Char) := isActive0 c || c == f.expSep
  -- exponent separator: preceded and followed by an active character
  let n := pic.length
  let idxs := List.range n
  let activeBefore (i : Nat) := (pic.take i).any isActive0
  let activeAfter (i : Nat) := (pic.drop (i + 1)).any isActive0
  let expIdxs := idxs.filter (fun i => pic.getD i ' ' == f.expSep && activeBefore i && activeAfter i)
  if expIdxs.length > 1 then fmtErr "more than one exponent separator"
  let expIdx := expIdxs.head?
  let isAct (i : Nat) := isActive0 (pic.getD i ' ') || expIdx == some i
  let actIdx := idxs.filter isAct
  let first := actIdx.head?.getD n
  let last := actIdx.getLast?.getD 0
  -- passive characters between active ones
  if idxs.any (fun i => !isAct i && i > first && i < last) then
    fmtErr "a passive character between active characters"
  let _ := isActiveE
  let pre := String.ofList (pic.take first)
  let suf := if actIdx.isEmpty then "" else String.ofList (pic.drop (last + 1))
  let pctN := (pic.filter (· == f.percent)).length
  let pmlN := (pic.filter (· == f.permille)).length
  if pctN + pmlN > 1 then fmtErr "more than one percent or per-mille sign"
  let body := if actIdx.isEmpty then [] else (pic.take (last + 1)).drop first
  let (mant, expo) := match expIdx with
    | some e => (body.take (e - first), body.drop (e - first + 1))
    | none => (body, [])
  if expIdx.isSome && pctN + pmlN > 0 then fmtErr "an exponent with percent or per-mille"
  if expIdx.isSome && (expo.isEmpty || !expo.all isFam) then fmtErr "the exponent must be digits"
  if (mant.filter (· == f.decSep)).length > 1 then fmtErr "more than one decimal separator"
  if !(mant.any (fun c => c == f.digit || isFam c)) then fmtErr "no digit in the mantissa"
  let (ip, fp, hasDec) := match mant.findIdx? (· == f.decSep) with
    | some i => (mant.take i, mant.drop (i + 1), true)
    | none => (mant, [], false)
  -- grouping separator checks
  let pairs := mant.zip (mant.drop 1)
  if pairs.any (fun (a, b) => a == f.grpSep && b == f.grpSep) then fmtErr "adjacent grouping separators"
  if pairs.any (fun (a, b) => (a == f.grpSep && b == f.decSep) || (a == f.decSep && b == f.grpSep)) then
    fmtErr "a grouping separator next to the decimal separator"
  if !hasDec && ip.getLast? == some f.grpSep then fmtErr "a grouping separator at the end of the integer part"
  -- digit order
  let ipD := ip.filter (fun c => c != f.grpSep)
  match ipD.findIdx? isFam with
  | some i => if (ipD.drop i).any (· == f.digit) then fmtErr "an optional digit after a mandatory digit in the integer part"
  | none => pure ()
  let fpD := fp.filter (fun c => c != f.grpSep)
  match fpD.findIdx? (· == f.digit) with
  | some i => if (fpD.drop i).any isFam then fmtErr "a mandatory digit after an optional digit in the fractional part"
  | none => pure ()
  -- variables
  let isDig (c : Char) := c == f.digit || isFam c
  let ipI := ip.zipIdx
  let intGroups := (ipI.filter (·.1 == f.grpSep)).map (fun (_, i) => ((ip.drop (i + 1)).filter isDig).length)
  let ipDigits := (ip.filter isDig).length
  let regular : Option Nat := match intGroups with
    | [] => none
    | g0 :: _ =>
      let g := intGroups.foldl min g0
      if g > 0 && intGroups.all (· % g == 0) &&
         ((List.range ipDigits).all (fun k => k == 0 || k % g != 0 || intGroups.contains k)) then some g else none
  let fpI := fp.zipIdx
  let fracGroups := (fpI.filter (·.1 == f.grpSep)).map (fun (_, i) => ((fp.take i).filter isDig).length)
  let mut minInt := (ip.filter isFam).length
  let scale := minInt
  let mut minFrac := (fp.filter isFam).length
  let mut maxFrac := (fp.filter isDig).length
  let minExp := (expo.filter isFam).length
  if minInt == 0 && maxFrac == 0 then
    if expIdx.isSome then minFrac := 1; maxFrac := 1
    else minInt := 1
  if expIdx.isSome && minInt == 0 && ip.any (· == f.digit) then minInt := 1
  if minInt == 0 && minFrac == 0 then minFrac := 1
  pure { pre, suf, intGroups, regular, minInt, scale, fracGroups, minFrac, maxFrac, minExp,
         pct := pctN > 0, pml := pmlN > 0, hasDecSep := hasDec }

/-- The digits of a decimal: integer part and fractional part (no sign). -/
def decDigits (d : Dec) : List Char × List Char :=
  let d := Dec.norm d
  let s := (toString d.mantissa.natAbs).toList
  let s := List.replicate (d.scale + 1 - min (d.scale + 1) s.length) '0' ++ s
  let ip := s.take (s.length - d.scale)
  let fp := s.drop (s.length - d.scale)
  let ip := ip.dropWhile (· == '0')
  (ip, fp)

/-- The shortest decimal that reads back as the double/float. -/
def decOfFloatShort (isF32 : Bool) (x : Float) : Dec :=
  if x == 0 then Dec.zero else
  let (d, q) := shortestDigits isF32 x
  let len := (toString d).length
  let e : Int := q - (len : Int) + 1
  let m : Int := if x < 0 then -(d : Int) else d
  if e ≥ 0 then Dec.norm ⟨m * (10 : Int) ^ e.toNat, 0⟩ else Dec.norm ⟨m, (-e).toNat⟩

def pow10Dec (k : Int) : Dec := if k ≥ 0 then ⟨(10 : Int) ^ k.toNat, 0⟩ else ⟨1, (-k).toNat⟩

def decMul (a b : Dec) : Dec := Dec.norm ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

def formatSub (f : DecFormat) (sp : SubPic) (absv : Dec) : String := Id.run do
  let v := if sp.pct then decMul absv (Dec.ofInt 100) else if sp.pml then decMul absv (Dec.ofInt 1000) else absv
  -- exponent
  let mut m := v
  let mut ex : Int := 0
  if sp.minExp > 0 && v.mantissa != 0 then
    let (ip, fp) := decDigits v
    -- position of the decimal exponent: v = 0.d1d2.. × 10^k
    let k : Int := if !ip.isEmpty then ip.length else -((fp.takeWhile (· == '0')).length : Int)
    ex := k - sp.scale
    m := decMul v (pow10Dec (-ex))
  let r := roundDec m sp.maxFrac true
  let (ip, fp) := decDigits r
  let fp := (fp.reverse.dropWhile (· == '0')).reverse
  let ip := List.replicate (sp.minInt - min sp.minInt ip.length) '0' ++ ip
  let fp := fp ++ List.replicate (sp.minFrac - min sp.minFrac fp.length) '0'
  let dig (c : Char) : String := String.singleton (Char.ofNat (f.zero + (c.toNat - 48)))
  let len := ip.length
  let isGrp (q : Nat) : Bool := match sp.regular with
    | some g => q > 0 && q % g == 0
    | none => sp.intGroups.contains q
  let mut out := ""
  for (c, i) in ip.zipIdx do
    if i > 0 && isGrp (len - i) then out := out ++ f.grpSepR
    out := out ++ dig c
  if !fp.isEmpty then
    out := out ++ f.decSepR
    for (c, i) in fp.zipIdx do
      if i > 0 && sp.fracGroups.contains i then out := out ++ f.grpSepR
      out := out ++ dig c
  if sp.minExp > 0 then
    let es := (toString ex.natAbs).toList
    let es := List.replicate (sp.minExp - min sp.minExp es.length) '0' ++ es
    out := out ++ f.expSepR ++ (if ex < 0 then f.minus else "") ++ String.join (es.map dig)
  let renderAffix (s : String) : String :=
    String.join (s.toList.map (fun c => if c == f.percent then f.percentR else if c == f.permille then f.permilleR else String.singleton c))
  pure (renderAffix sp.pre ++ out ++ renderAffix sp.suf)

def formatNumberWith (f : DecFormat) (x : Option Num) (pic : String) : M String := do
  f.check
  let cs := pic.toList
  let parts := (cs.splitOn f.patSep)
  let (posP, negP) ← match parts with
    | [p] => pure (p, none)
    | [p, q] => pure (p, some q)
    | _ => fmtErr "more than one pattern separator"
  let pos ← analyzeSub f posP
  let neg ← match negP with
    | some q => analyzeSub f q
    | none => pure { pos with pre := f.minus ++ pos.pre }
  match x with
  | none => pure f.nan
  | some n =>
    let isNeg : Bool := match n with
      | .i v => v < 0 | .d v => v.mantissa < 0
      | .f v => v < 0 || (v == 0 && (v.toBits >>> 63) == 1)
      | .g v => v < 0 || (v == 0 && (v.toBits >>> 63) == 1)
    let sp := if isNeg then neg else pos
    match n with
    | .f v | .g v =>
      if v.isNaN then return f.nan
      let big := v.isInf || ((sp.pct || sp.pml) && (v * 1000).isInf)
      if big then return (sp.pre ++ f.infinity ++ sp.suf)
    | _ => pure ()
    let d : Dec := match n with
      | .i v => Dec.ofInt v.natAbs
      | .d v => ⟨v.mantissa.natAbs, v.scale⟩
      | .f v => let x := decOfFloatShort true v; ⟨x.mantissa.natAbs, x.scale⟩
      | .g v => let x := decOfFloatShort false v; ⟨x.mantissa.natAbs, x.scale⟩
    pure (formatSub f sp d)

/-! ## Dates and times (§9.8) -/

def dateErr {α} (msg : String) : M α := err "FOFD1340" msg

def monthNames : List String := ["January", "February", "March", "April", "May", "June", "July",
  "August", "September", "October", "November", "December"]
def dayNames : List String := ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

/-- ISO day of the week, 1 = Monday. -/
def isoWeekday (y : Int) (m d : Nat) : Nat :=
  let z := daysFromCivil y m d   -- 1970-01-01 is a Thursday
  ((z + 3) % 7).toNat + 1

def dayOfYear (y : Int) (m d : Nat) : Nat := (daysFromCivil y m d - daysFromCivil y 1 1).toNat + 1

/-- ISO 8601 week number. -/
def isoWeek (y : Int) (m d : Nat) : Nat :=
  let wd := isoWeekday y m d
  let doy := dayOfYear y m d
  let w := (doy + 10 - wd) / 7
  if w == 0 then
    -- the last week of the previous year
    let pd := daysFromCivil y 1 1 - 1
    let (py, pm, pdd) := civilFromDays pd
    let pwd := isoWeekday py pm pdd
    let pdoy := dayOfYear py pm pdd
    (pdoy + 10 - pwd) / 7
  else if w == 53 then
    -- 53 only if Dec 31 of the year is a Thursday (or Friday in a leap year...)
    let dec31 := isoWeekday y 12 31
    if dec31 < 4 then 1 else 53
  else w

/-- Week in month: a week (Monday to Sunday) belongs to the month that
    holds its Thursday; the week holding the month's first Thursday is
    week 1. -/
def weekInMonth (y : Int) (m d : Nat) : Nat :=
  let wd := isoWeekday y m d
  let thu := daysFromCivil y m d + (4 - (wd : Int))
  let (_, _, td) := civilFromDays thu
  (td - 1) / 7 + 1

structure Marker where
  comp : Char
  pres1 : String
  pres2 : Option Char
  minW : Option Nat
  maxW : Option Nat

inductive PicPart where
  | lit (s : String)
  | mark (m : Marker)

def parseWidth (w : String) : M (Option Nat × Option Nat) := do
  let num (s : String) : M (Option Nat) :=
    if s == "*" then pure none
    else match s.toNat? with
      | some k => if k < 1 then dateErr "width must be at least 1" else pure (some k)
      | none => dateErr ("bad width " ++ w)
  match w.splitOn "-" with
  | [a] => pure (← num a, none)
  | [a, b] =>
    let mn ← num a
    let mx ← num b
    match mn, mx with
    | some x, some y => if y < x then dateErr "max width below min width" else pure (mn, mx)
    | _, _ => pure (mn, mx)
  | _ => dateErr ("bad width " ++ w)

def parseMarker (s : String) : M Marker := do
  let cs := s.toList.filter (fun c => !(c == ' ' || c == '\t' || c == '\n' || c == '\r'))
  match cs with
  | [] => dateErr "empty variable marker"
  | c :: rest =>
    if !"YMDdFWwHhPmsfZzCE".toList.contains c then dateErr ("unknown component " ++ String.singleton c)
    let (pm, w) := match (rest.zipIdx.filter (·.1 == ',')).getLast? with
      | some (_, i) => (rest.take i, some (String.ofList (rest.drop (i + 1))))
      | none => (rest, none)
    let (mn, mx) ← match w with
      | some w => parseWidth w
      | none => pure (none, none)
    let (p1, p2) := match pm with
      | [] => ("", none)
      | [x] => (String.singleton x, none)
      | xs =>
        let l := xs.getLast!
        if "atco".toList.contains l then (String.ofList xs.dropLast, some l) else (String.ofList xs, none)
    pure { comp := c, pres1 := p1, pres2 := p2, minW := mn, maxW := mx }

def parseDatePicture (pic : String) : M (List PicPart) := do
  let mut out : Array PicPart := #[]
  let mut lit := ""
  let mut cs := pic.toList
  for _ in [0:pic.length + 1] do
    match cs with
    | [] => break
    | '[' :: '[' :: r => lit := lit.push '['; cs := r
    | ']' :: ']' :: r => lit := lit.push ']'; cs := r
    | ']' :: _ => dateErr "unmatched ]"
    | '[' :: r =>
      match r.findIdx? (· == ']') with
      | some i =>
        if lit != "" then out := out.push (.lit lit); lit := ""
        out := out.push (.mark (← parseMarker (String.ofList (r.take i))))
        cs := r.drop (i + 1)
      | none => dateErr "unclosed ["
    | c :: r => lit := lit.push c; cs := r
  if lit != "" then out := out.push (.lit lit)
  pure out.toList

/-- Widen a decimal digit pattern to `w` mandatory digits (§9.8.4.4). -/
def widenPattern (tok : List Char) (w : Nat) : List Char :=
  let zero := ((tok.findSome? digitZero?).getD 0x30)
  let zc := Char.ofNat zero
  let mand := (tok.filter isDigitU).length
  if mand ≥ w then tok else
  -- replace optional signs from the right
  let rec repl : Nat → List Char → List Char
    | _, [] => []
    | k, c :: r => if c == '#' && k > 0 then zc :: repl (k - 1) r else c :: repl k r
  let need := w - mand
  let opts := (tok.filter (· == '#')).length
  let tok' := (repl (min need opts) tok.reverse).reverse
  List.replicate (need - min need opts) zc ++ tok'

def nameFmt (full : String) (p1 : String) (mn mx : Option Nat) : String :=
  let s := match p1 with
    | "N" => Fn.String.upperCase full
    | "n" => Fn.String.lowerCase full
    | _ => full
  let s := match mx with
    | some k => if s.length > k then (s.take (if k ≥ 3 then 3 else k)).toString else s
    | none => s
  match mn with
  | some k => s ++ String.ofList (List.replicate (k - min k s.length) ' ')
  | none => s

def isNameTok (p : String) : Bool := p == "N" || p == "n" || p == "Nn"

/-- A picture error inside a date picture is `FOFD1340`. -/
def asDateErr {α} (x : M α) : M α :=
  match x with
  | .error e => if e.code == "FODF1310" then err "FOFD1340" e.msg else .error e
  | ok => ok

/-- Format an integer component. -/
def fmtComp (mk : Marker) (dflt : String) (v : Nat) (lang : String := "en") : M String := asDateErr do
  let p1 := if mk.pres1 == "" || isNameTok mk.pres1 then dflt else mk.pres1
  let ord := mk.pres2 == some 'o'
  let tok := p1.toList
  if tok.any isDigitU && radixPrefix tok == none then
    let tok := match mk.minW with
      | some w => widenPattern tok w
      | none => tok
    let s ← fmtIntToken tok v ord lang
    pure s
  else
    let s ← fmtIntToken tok v ord lang
    match mk.minW with
    | some k => pure (s ++ String.ofList (List.replicate (k - min k s.length) ' '))
    | none => pure s

def tzString (mk : Marker) (tz : Option Int) (abbr : Option String := none) : M String := do
  let p1 := if mk.pres1 == "" then "01:01" else mk.pres1
  -- the N presentation with a recognised place: the zone abbreviation, when it is letters
  let named : Option String := match abbr with
    | some a => if p1 == "N" && !a.isEmpty && a.toList.all Char.isAlpha then some a else none
    | none => none
  if let some a := named then return a
  let gmt := if mk.comp == 'z' then "GMT" else ""
  match tz with
  | none => pure (if p1 == "Z" then "J" else "")
  | some off =>
    let sign := if off < 0 then "-" else "+"
    let a := off.natAbs
    let h := a / 60
    let mi := a % 60
    let pad (k : Nat) (n : Nat) : String :=
      let s := toString n; String.ofList (List.replicate (k - min k s.length) '0') ++ s
    if p1 == "Z" then
      if mi != 0 || h > 12 then
        pure (sign ++ pad 2 h ++ ":" ++ pad 2 mi)
      else if off == 0 then pure "Z"
      else if off > 0 then pure (String.singleton (Char.ofNat (if h ≤ 9 then 64 + h else 65 + h)))
      else pure (String.singleton (Char.ofNat (77 + h)))
    else
    let tok := p1.toList
    if !(tok.any isDigitU) then
      -- names etc.: fall back to 01:01
      pure (gmt ++ sign ++ pad 2 h ++ ":" ++ pad 2 mi)
    else
    if mk.pres2 == some 't' && off == 0 then pure "Z" else
    let zero := (tok.findSome? digitZero?).getD 0x30
    let fam (t : String) : String := String.ofList (t.toList.map (fun c =>
      if c.isDigit && zero != 0x30 then Char.ofNat (zero + (c.toNat - 48)) else c))
    let digits := tok.filter isDigitU
    let sep := tok.find? (fun c => !isDigitU c && c != '#')
    let hw := match sep with
      | some s => (tok.takeWhile (· != s)).filter isDigitU |>.length
      | none => if digits.length ≤ 2 then digits.length else digits.length - 2
    let body := match sep with
      | some s => pad hw h ++ String.singleton s ++ pad 2 mi
      | none =>
        if digits.length ≤ 2 then pad hw h ++ (if mi != 0 then ":" ++ pad 2 mi else "")
        else pad hw h ++ pad 2 mi
    pure (gmt ++ sign ++ fam body)

def fracSeconds (mk : Marker) (sec : Dec) : M String := do
  let (_, fp) := decDigits sec
  let fp := (fp.reverse.dropWhile (· == '0')).reverse
  let fp := if fp.isEmpty then ['0'] else fp
  let tok := (if mk.pres1 == "" || isNameTok mk.pres1 then "1" else mk.pres1).toList
  if !(tok.any isDigitU) then
    return String.ofList fp
  -- the reversed picture must be a valid decimal digit pattern
  let _ ← asDateErr (parseDigitPat tok.reverse none)
  let zero := (tok.findSome? digitZero?).getD 0x30
  let mand0 := (tok.filter isDigitU).length
  let tot0 := (tok.filter (fun c => isDigitU c || c == '#')).length
  let hasW := mk.minW.isSome || mk.maxW.isSome
  let (mand, tot) :=
    if !hasW && mand0 == 1 && tot0 == 1 then (1, 1000)
    else
      let mand := match mk.minW with | some w => max mand0 w | none => mand0
      let tot := max tot0 mand
      let tot := match mk.maxW with
        | some w => max tot w
        | none => if hasW then 1000 else tot
      (mand, tot)
  let ds := fp.take tot
  let ds := ds ++ List.replicate (mand - min mand ds.length) '0'
  -- digits beyond the mandatory ones lose their trailing zeros
  let extra := ((ds.drop mand).reverse.dropWhile (· == '0')).reverse
  let ds := ds.take mand ++ extra
  -- grouping separators, counted from the left
  let seps := (tok.zipIdx.filter (fun (c, _) => !(isDigitU c || c == '#'))).map (fun (c, i) =>
    (((tok.take i).filter (fun c => isDigitU c || c == '#')).length, c))
  let mut out := ""
  for (c, i) in ds.zipIdx do
    match seps.find? (·.1 == i) with
    | some (_, sc) => if i > 0 then out := out.push sc
    | none => pure ()
    out := out.push (Char.ofNat (zero + (c.toNat - 48)))
  pure out

def formatDT (kind : DTKind) (v0 : DTValue) (pic : String) (lang cal : Option String)
    (place : Option String := none) : M String := do
  let (v, abbr) : DTValue × Option String :=
    match place with
    | some p => if kind == .dateTime then
        (match placeAdjust v0 p with | some (v', a) => (v', some a) | none => (v0, none))
      else (v0, none)
    | none => (v0, none)
  let parts ← parseDatePicture pic
  let hasDate := kind != .time
  let hasTime := kind != .date
  let y := v.year.getD 0
  let mo := v.month.getD 1
  let d := v.day.getD 1
  let hr := v.hour.getD 0
  let mi := v.minute.getD 0
  let sec := v.second.getD Dec.zero
  let mut out := ""
  let langS : String := match lang with
    | some l => if NumberWords.hasLang l then l else "en"
    | none => "en"
  if let some l := lang then
    if !(l == "" || l.toLower == "en" || l.toLower.startsWith "en-" || NumberWords.hasLang l) then
      out := "[Language: en]"
  let fmtComp (mk : Marker) (dflt : String) (v : Nat) : M String := fmtComp mk dflt v langS
  let months := (NumberWords.months? langS).getD monthNames
  let days := (NumberWords.days? langS).getD dayNames
  if let some c := cal then
    let c := c.trim
    let isNC (t : String) : Bool := match t.toList with
      | h :: r => (h.isAlpha || h == '_') && r.all (fun ch => ch.isAlphanum || ch == '-' || ch == '_' || ch == '.')
      | [] => false
    let known := ["AD", "AH", "AME", "AM", "AP", "AS", "BE", "CB", "CE", "CL", "CS", "EE", "FE",
      "ISO", "JE", "KE", "KY", "ME", "MS", "NS", "OS", "RS", "SE", "SH", "SS", "TE", "VE", "VS"]
    let calLocal := if c.startsWith "Q{}" then (c.drop 3).toString else c
    if c.startsWith "Q{" && !c.startsWith "Q{}" then
      match c.splitOn "}" with
      | [_, l] => if isNC l then out := out ++ "[Calendar: AD]" else dateErr ("invalid calendar " ++ c)
      | _ => dateErr ("invalid calendar " ++ c)
    else if (calLocal.splitOn ":").length == 2 then
      match calLocal.splitOn ":" with
      | [p, l] => if isNC p && isNC l then out := out ++ "[Calendar: AD]" else dateErr ("invalid calendar " ++ c)
      | _ => dateErr ("invalid calendar " ++ c)
    else if !isNC calLocal then dateErr ("invalid calendar " ++ c)
    else if !known.contains calLocal then dateErr ("unknown calendar " ++ c)
    else if calLocal != "AD" && calLocal != "ISO" then out := out ++ "[Calendar: AD]"
  for p in parts do
    match p with
    | .lit s => out := out ++ s
    | .mark mk =>
      let needDate := "YMDdFWwE".toList.contains mk.comp
      let needTime := "HhPmsf".toList.contains mk.comp
      if needDate && !hasDate then err "FOFD1350" ("no date component " ++ String.singleton mk.comp)
      if needTime && !hasTime then err "FOFD1350" ("no time component " ++ String.singleton mk.comp)
      let s ← match mk.comp with
        | 'Y' =>
          let tok := mk.pres1.toList
          let isDP := tok.any isDigitU
          let n : Option Nat := match mk.maxW with
            | some k => some k
            | none =>
              if isDP then
                let w := (tok.filter (fun c => isDigitU c || c == '#')).length
                if w ≥ 2 then some w else none
              else none
          let yv := y.natAbs
          let yv := match n with | some k => yv % (10 ^ k) | none => yv
          if isNameTok mk.pres1 then fmtComp { mk with pres1 := "1" } "1" yv
          else fmtComp mk "1" yv
        | 'M' =>
          if isNameTok mk.pres1 then pure (nameFmt (months.getD (mo - 1) "") mk.pres1 mk.minW mk.maxW)
          else fmtComp mk "1" mo
        | 'D' => fmtComp mk "1" d
        | 'd' => fmtComp mk "1" (dayOfYear y mo d)
        | 'F' =>
          let wd := isoWeekday y mo d
          if mk.pres1 == "" || isNameTok mk.pres1 then
            pure (nameFmt (days.getD (wd - 1) "") (if mk.pres1 == "" then "n" else mk.pres1) mk.minW mk.maxW)
          else fmtComp mk "1" wd
        | 'W' => fmtComp mk "1" (isoWeek y mo d)
        | 'w' => fmtComp mk "1" (weekInMonth y mo d)
        | 'H' => fmtComp mk "1" hr
        | 'h' => fmtComp mk "1" (if hr % 12 == 0 then 12 else hr % 12)
        | 'P' =>
          let s := if hr < 12 then "Am" else "Pm"
          pure (nameFmt s (if mk.pres1 == "" then "n" else mk.pres1) mk.minW mk.maxW)
        | 'm' => fmtComp mk "01" mi
        | 's' => fmtComp mk "01" (sec.floorDiv.toNat)
        | 'f' => fracSeconds mk sec
        | 'Z' | 'z' => tzString mk v.tz abbr
        | 'C' => pure (nameFmt "AD" (if mk.pres1 == "" then "N" else mk.pres1) mk.minW mk.maxW)
        | 'E' => pure (nameFmt (if y > 0 then "AD" else "BC") (if mk.pres1 == "" then "N" else mk.pres1) mk.minW mk.maxW)
        | _ => dateErr "unknown component"
      out := out ++ s
  pure out

/-! ## fn:parse-ietf-date (§9.9.1)

The grammar, with `S` one or more whitespace characters:

    input     ::= S? (dayname ","? S)? ((datespec S time) | asctime) S?
    datespec  ::= daynum dsep monthname dsep year
    asctime   ::= monthname dsep daynum S time S year
    dsep      ::= S | (S? "-" S?)
    time      ::= hours ":" minutes (":" seconds)? (S? timezone)?
    timezone  ::= tzname | tzoffset (S? "(" S? tzname S? ")")?
    tzoffset  ::= ("+"|"-") tzhours ":"? tzminutes?

Names are matched without regard to case. A two-digit year is 19xx. -/

def ietfErr {α} : M α := err "FORG0010" "not a valid IETF date"

def isWsC (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
def skipWs (cs : List Char) : List Char := cs.dropWhile isWsC

/-- `S`: at least one whitespace character. -/
def needWs (cs : List Char) : M (List Char) :=
  match cs with
  | c :: _ => if isWsC c then pure (skipWs cs) else ietfErr
  | [] => ietfErr

def takeDigits (cs : List Char) : List Char × List Char := (cs.takeWhile Char.isDigit, cs.dropWhile Char.isDigit)

def tzNames : List (String × Int) := [("UT", 0), ("UTC", 0), ("GMT", 0), ("EST", -300), ("EDT", -240),
  ("CST", -360), ("CDT", -300), ("MST", -420), ("MDT", -360), ("PST", -480), ("PDT", -420)]

def monthAbbr : List String := ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
def dayAbbr : List String := ["mon", "tue", "wed", "thu", "fri", "sat", "sun",
  "monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]

def dsep (cs : List Char) : M (List Char) := do
  let r := skipWs cs
  match r with
  | '-' :: r2 => pure (skipWs r2)
  | _ => if r.length < cs.length then pure r else ietfErr

def monthName (cs : List Char) : M (Nat × List Char) := do
  let w := cs.takeWhile Char.isAlpha
  match monthAbbr.findIdx? (· == (String.ofList w).toLower) with
  | some i => pure (i + 1, cs.drop w.length)
  | none => ietfErr

def numOf (ds : List Char) : Nat := (String.ofList ds).toNat!

def dayNum (cs : List Char) : M (Nat × List Char) := do
  let (d, r) := takeDigits cs
  if d.isEmpty || d.length > 2 then ietfErr
  pure (numOf d, r)

def yearP (cs : List Char) : M (Int × List Char) := do
  let (yd, r) := takeDigits cs
  if yd.length == 2 then pure (1900 + numOf yd, r)
  else if yd.length == 4 then pure (numOf yd, r)
  else ietfErr

def tzName (cs : List Char) : Option (Int × List Char) :=
  let w := cs.takeWhile Char.isAlpha
  (tzNames.lookup (String.ofList w).toUpper).map (fun o => (o, cs.drop w.length))

def tzOffset (cs : List Char) : M (Option (Int × List Char)) := do
  let (neg, r) ← match cs with
    | '+' :: r => pure (false, r)
    | '-' :: r => pure (true, r)
    | _ => return none
  let (h, r) := takeDigits r
  let (hv, mv, r) ← match r with
    | ':' :: r2 =>
      let (m, r3) := takeDigits r2
      if h.isEmpty || h.length > 2 || (m.length != 0 && m.length != 2) then ietfErr
      pure (numOf h, (if m.isEmpty then 0 else numOf m), r3)
    | _ =>
      if h.length == 1 || h.length == 2 then pure (numOf h, 0, r)
      else if h.length == 3 || h.length == 4 then
        pure (numOf (h.take (h.length - 2)), numOf (h.drop (h.length - 2)), r)
      else ietfErr
  if mv > 59 then ietfErr
  let off : Int := hv * 60 + mv
  pure (some (if neg then -off else off, r))

/-- `time`: (hours, minutes, seconds, timezone, rest). -/
def timeP (cs : List Char) : M (Nat × Nat × Dec × Int × List Char) := do
  let (h, r) := takeDigits cs
  if h.isEmpty || h.length > 2 then ietfErr
  let r ← match r with | ':' :: r => pure r | _ => ietfErr
  let (m, r) := takeDigits r
  if m.length != 2 then ietfErr
  let mut ss : Dec := Dec.zero
  let mut r := r
  if r.head? == some ':' then
    let (sd, r2) := takeDigits r.tail
    if sd.length != 2 then ietfErr
    ss := Dec.ofInt (numOf sd)
    r := r2
    if r.head? == some '.' then
      let (fd, r3) := takeDigits r.tail
      if fd.isEmpty then ietfErr
      ss := Dec.add ss ⟨numOf fd, fd.length⟩
      r := r3
  -- optional timezone, after optional whitespace
  let r1 := skipWs r
  let mut tz : Int := 0
  match tzName r1 with
  | some (o, r2) => tz := o; r := r2
  | none =>
    match ← tzOffset r1 with
    | some (o, r2) =>
      tz := o
      r := r2
      let r3 := skipWs r2
      if r3.head? == some '(' then
        match tzName (skipWs r3.tail) with
        | some (_, r4) =>
          match skipWs r4 with
          | ')' :: r5 => r := r5
          | _ => ietfErr
        | none => ietfErr
    | none => pure ()
  pure (numOf h, numOf m, ss, tz, r)

def parseIetf (s : String) : M Atomic := do
  let mut cs := skipWs s.toList
  let word := cs.takeWhile Char.isAlpha
  if !word.isEmpty && dayAbbr.contains (String.ofList word).toLower then
    cs := cs.drop word.length
    if cs.head? == some ',' then cs := cs.tail
    cs ← needWs cs
  let (day, mon, year, hh, mm, ss, tz, rest) ←
    if (cs.head?.map Char.isDigit).getD false then do
      let (d, r) ← dayNum cs
      let r ← dsep r
      let (m, r) ← monthName r
      let r ← dsep r
      let (y, r) ← yearP r
      let r ← needWs r
      let (hh, mm, ss, tz, r) ← timeP r
      pure (d, m, y, hh, mm, ss, tz, r)
    else do
      let (m, r) ← monthName cs
      let r ← dsep r
      let (d, r) ← dayNum r
      let r ← needWs r
      let (hh, mm, ss, tz, r) ← timeP r
      let r ← needWs r
      let (y, r) ← yearP r
      pure (d, m, y, hh, mm, ss, tz, r)
  if !(skipWs rest).isEmpty then ietfErr
  if mon < 1 || mon > 12 || day < 1 || day > daysInMonth year mon then err "FORG0010" "day out of range"
  if hh > 24 || mm > 59 || Dec.cmp ss (Dec.ofInt 60) != .lt then err "FORG0010" "time out of range"
  if hh == 24 && (mm != 0 || ss.mantissa != 0) then err "FORG0010" "time out of range"
  if tz.natAbs > 14 * 60 then err "FORG0010" "timezone out of range"
  let pad (k : Nat) (n : Nat) : String :=
    let s := toString n; String.ofList (List.replicate (k - min k s.length) '0') ++ s
  let secS :=
    let (ip, fp) := decDigits ss
    let ipS := pad 2 (numOf ip)
    if fp.isEmpty then ipS else ipS ++ "." ++ String.ofList fp
  let tzS := if tz == 0 then "Z" else (if tz < 0 then "-" else "+") ++ pad 2 (tz.natAbs / 60) ++ ":" ++ pad 2 (tz.natAbs % 60)
  let lex := toString year ++ "-" ++ pad 2 mon ++ "-" ++ pad 2 day ++ "T" ++ pad 2 hh ++ ":" ++ pad 2 mm ++ ":" ++ secS ++ tzS
  -- the result is normalised to UTC
  let dt ← castFromString lex (.b .dateTime)
  pure dt

/-! ## The table -/

def dtOf (a : Atomic) : Option (DTKind × DTValue) :=
  match a.v with
  | .x (.dt k v) => some (k, v)
  | _ => none

def optStr (s : Seq) : Option String := (optAtom s).map (·.str)

def dateFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some x =>
    match dtOf x with
    | some (k, v) =>
      let s ← formatDT k v (strOf (argN a 1)) (optStr (argN a 2)) (optStr (argN a 3)) (optStr (argN a 4))
      pure (sStr s)
    | none => err "XPTY0004" "expected a date/time value"

def formatTable : List (String × LibFn) := [
  ent "format-integer" (fun _ _ a => do
    match optAtom (argN a 0) with
    | none => pure (sStr "")
    | some x =>
      match x.v with
      | .int i => pure (sStr (← formatInteger i (strOf (argN a 1)) ((optStr (argN a 2)).getD "en")))
      | _ => err "XPTY0004" "format-integer expects an integer"),
  ent "format-number" (fun _ e a => do
    let base : DecFormat := {}
    let opts := argN a 2
    let mut fmtName : Option String := none
    let mut props : List (String × String) := []
    match opts with
    | [] => pure ()
    | [.map kvs] =>
      for (k, v) in kvs do
        if k.str == "format-name" then
          match v with
          | [.atom q] => fmtName := some (match q.v with | .qn n => n.eqn | _ => "Q{}" ++ q.str)
          | _ => pure ()
        else props := props ++ [(k.str, strOf v)]
    | [.atom s] =>
      let nm := s.str.trim
      if nm.startsWith "Q{" then fmtName := some nm
      else
        match nm.splitOn ":" with
        | [p, l] =>
          match e.nsResolve p with
          | some u => fmtName := some ("Q{" ++ u ++ "}" ++ l)
          | none => err "FODF1280" ("unknown decimal format " ++ nm)
        | [l] => fmtName := some ("Q{}" ++ l)
        | _ => err "FODF1280" ("invalid decimal format name " ++ nm)
    | _ => err "XPTY0004" "bad decimal format argument"
    let mut f := base
    -- the named (or unnamed) format of the static context
    let key := fmtName.getD ""
    match e.decimalFormats.lookup key with
    | some ps => for (k, v) in ps do f ← f.set k v
    | none => if key != "" then err "FODF1280" ("unknown decimal format " ++ key)
    for (k, v) in props do f ← f.set k v
    let x := (optAtom (argN a 0)).bind Atomic.num?
    pure (sStr (← formatNumberWith f x (strOf (argN a 1))))),
  ent "format-dateTime" dateFn,
  ent "format-date" dateFn,
  ent "format-time" dateFn,
  ent "parse-ietf-date" (fun _ _ a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some s => pure (single (← parseIetf s.str)))
]

#guard (formatInteger 1234 "#,##0" "en").toOption == some "1,234"
#guard (formatInteger 255 "16^xxxx" "en").toOption == some "00ff"
#guard (formatInteger 21 "w;o" "en").toOption == some "twenty-first"
#guard (formatInteger 1999 "I" "en").toOption == some "MCMXCIX"
#guard (formatInteger 1 "Ww;o(-er)" "de").toOption == some "Erster"
#guard (formatInteger 2 "Ww;o" "fr").toOption == some "Deuxième"
#guard (formatInteger 5 "Ww;o(-a)" "it").toOption == some "Quinta"
#guard (formatNumberWith {} (some (.d ⟨123456789, 2⟩)) "#,##0.00").toOption == some "1,234,567.89"
#guard (formatNumberWith {} (some (.g 0.000123)) "0.0e0").toOption == some "1.2e-4"

end L4Factoidal.XPath4
