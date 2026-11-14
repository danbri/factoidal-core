import L4Factoidal.JS.Lexer
import L4Factoidal.Text.CaseMap
import L4Factoidal.Regex.UnicodeProps

/-!
# L4Factoidal.JS.Regex — regular expressions of the engine (§22.2)

## Parsing (§22.2.1)

The pattern grammar with the parameters UnicodeMode (`u` or `v`), UnicodeSetsMode (`v`) and
NamedCaptureGroups, and the Annex B grammar (B.1.2) when neither `u` nor `v` is given:

- alternatives, sequences, the quantifiers `*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}` (greedy and
  lazy), capturing, non-capturing and named groups, back references (`\1`, `\k<name>`),
  lookahead and lookbehind (positive and negative), `^`, `$`, `\b`, `\B`, `.`, classes;
- modifiers `(?ims-ims:…)` (they change `i`, `m` and `s` inside the group);
- duplicate group names in different alternatives, and the early errors of group names
  (an IdentifierName, unique unless the two groups cannot both take part);
- with `v`: class set expressions (nested classes, `&&`, `--`, `\q{…}`) and the reserved
  double punctuators;
- with `u` or `v`: the strict escapes (an unknown identity escape is a SyntaxError),
  `\u{…}`, surrogate pairs written as two escapes, and `\p{…}` with the General_Category
  values of `Regex/UnicodeProps` (Unicode 16.0). Other property names that are well formed
  match no character (open: the property data, a decision of its own);
- without them, Annex B: legacy octal escapes, `\8` and `\9`, `]`, `{` and `}` as characters,
  `\c` with no letter, quantified lookaheads.

Characters are code units without `u`/`v` and code points with them (§22.2.2: Input is a list
of code points under full Unicode). The subject is the engine's array of code units
(`Str.unitChars`); a value is `Str.charUnit` of a character, so a lone surrogate is its unit.

## Matching (§22.2.2)

A backtracking machine with an explicit stack, not continuation closures: the state is the
position, the captures, a list of frames still to match (`Frame`), and a stack of choice
points (`Choice`). Each step does one frame or takes one choice point, and costs at least one
unit of a step budget (a run of one character matcher costs its length). When the budget is
spent the answer is `Result.limit`: a catastrophic pattern ends with a defined refusal
(`run_budget_zero`, `run_rem_le`, `search_budget_zero`, `search_rem_le`), never a hang or a
deep native stack. Lookbehind matches backward (direction −1 of §22.2.2). Canonicalize
(§22.2.2.7.3) uses the case tables of `Text/CaseMap`: simple case folding with `u`/`v`, the
upper case mapping without.
-/

namespace L4Factoidal.JS.Re

open L4Factoidal.Text

inductive ClassItem where
  | ch (c : Nat)
  | range (lo hi : Nat)
  /-- `\d` (0), `\w` (1), `\s` (2), negated when `neg`. -/
  | esc (kind : Nat) (neg : Bool)
  /-- `\p{…}`: the code points of a property value as sorted, disjoint ranges (empty for a
  property this engine has no data for), complemented when `neg`. -/
  | ranges (rs : Array (Nat × Nat)) (neg : Bool)
  /-- A nested class (`v`): the union of its items, complemented when `neg`. -/
  | set (neg : Bool) (items : List ClassItem)
  /-- `A && B && …` (`v`). -/
  | inter (items : List ClassItem)
  /-- `A -- B -- …` (`v`). -/
  | diff (items : List ClassItem)
  deriving Inhabited, Repr

inductive Node where
  | empty
  | char (c : Nat) (ic : Bool)
  | any (dotAll : Bool)
  | cls (neg : Bool) (items : List ClassItem) (ic : Bool)
  | bol (ml : Bool)
  | eol (ml : Bool)
  | wordB (neg ic : Bool)
  | group (idx : Option Nat) (r : Node)
  | look (behind neg : Bool) (r : Node)
  /-- A back reference to the groups `ks` (one number, or the groups of a duplicated name,
  of which at most one has taken part). -/
  | backref (ks : List Nat) (ic : Bool)
  /-- A back reference by name, resolved to its numbers after parsing. -/
  | named (name : String) (ic : Bool)
  | seq (rs : List Node)
  | alt (rs : List Node)
  /-- A quantified atom: the captures `first + 1 .. first + count` are inside it. -/
  | rep (r : Node) (min : Nat) (max : Option Nat) (greedy : Bool) (first count : Nat)
  deriving Inhabited, Repr

structure Flags where
  global : Bool := false
  icase : Bool := false
  multiline : Bool := false
  dotAll : Bool := false
  unicode : Bool := false
  sticky : Bool := false
  hasIndices : Bool := false
  unicodeSets : Bool := false
  deriving Inhabited, Repr

/-- Full Unicode matching: the `u` or the `v` flag. -/
@[inline] def Flags.uv (f : Flags) : Bool := f.unicode || f.unicodeSets

/-- The flags of a flags string, or none for an unknown or repeated flag, or `u` with `v`
(§22.2.3.1). -/
def parseFlags (s : String) : Option Flags := Id.run do
  let mut f : Flags := {}
  let mut seen : List Char := []
  for c in s.toList do
    if seen.contains c then return none
    seen := c :: seen
    match c with
    | 'g' => f := { f with global := true }
    | 'i' => f := { f with icase := true }
    | 'm' => f := { f with multiline := true }
    | 's' => f := { f with dotAll := true }
    | 'u' => f := { f with unicode := true }
    | 'y' => f := { f with sticky := true }
    | 'd' => f := { f with hasIndices := true }
    | 'v' => f := { f with unicodeSets := true }
    | _ => return none
  if f.unicode && f.unicodeSets then return none
  return some f

/-- A compiled pattern: the tree, the number of capturing groups, their names (a name
appears once for each group that has it, in the order of the groups). -/
structure Compiled where
  node : Node
  groups : Nat
  names : Array (String × Nat)
  flags : Flags
  /-- A one character matcher every match starts with, for passing over start positions. -/
  lead : Option Node := none
  deriving Inhabited

/-- The group names once each, in the order they first appear, with all the groups of each. -/
def Compiled.namedGroups (re : Compiled) : Array (String × List Nat) :=
  re.names.foldl (fun acc (nm, k) =>
    match acc.findIdx? (·.1 == nm) with
    | some i => acc.modify i fun (n, ks) => (n, ks ++ [k])
    | none => acc.push (nm, [k])) #[]

/-- The capture of a name: the first of its groups that took part (`caps[k]` for group `k`). -/
def groupValue {α} (caps : Array (Option α)) (ks : List Nat) : Option α :=
  ks.findSome? fun k => (caps[k]?).join

/-! ## Unicode tables used by the pattern -/

def hexNat (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun v => (hexVal c).map (v * 16 + ·)) (some 0)

/-- Parse the ranges `lo-hi lo-hi …` of a line of `UnicodeProps.catText`. -/
def parseRanges (s : String) : Array (Nat × Nat) :=
  (s.splitOn " ").toArray.filterMap fun r =>
    match r.splitOn "-" with
    | [a, b] => do pure ((← hexNat a), (← hexNat b))
    | _ => none

/-- The General_Category table by two-letter value, read on first use. -/
def catTable : Thunk (List (String × Array (Nat × Nat))) := Thunk.mk fun _ =>
  (L4Factoidal.Regex.UnicodeProps.catText.splitOn "\n").filterMap fun line =>
    match line.splitOn ":" with
    | [k, v] => if k.length == 2 then some (k, parseRanges v) else none
    | _ => none

/-- Whether `c` is in sorted, disjoint ranges (binary search). -/
def inRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b) := rs[mid]!
    if c < a then hi := mid
    else if c > b then lo := mid + 1
    else return true
  return false

def hasCatTwo (k : String) (c : Nat) : Bool :=
  match catTable.get.find? (·.1 == k) with
  | some (_, rs) => inRanges rs c
  | none => false

/-- Sorted ranges merged where they touch. -/
def mergeRanges (rs : Array (Nat × Nat)) : Array (Nat × Nat) :=
  (rs.qsort fun a b => a.1 < b.1).foldl (fun acc (a, b) =>
    match acc.back? with
    | some (x, y) => if a ≤ y + 1 then acc.pop.push (x, max y b) else acc.push (a, b)
    | none => acc.push (a, b)) #[]

/-- The ranges of a General_Category value (two letters, a one-letter group, `LC`, `Cs`). -/
def catRangesOf (cat : String) : Array (Nat × Nat) :=
  if cat == "Cs" then #[(0xD800, 0xDFFF)]
  else if cat == "LC" then mergeRanges (["Lu", "Ll", "Lt"].foldl (fun acc k =>
    acc ++ ((catTable.get.find? (·.1 == k)).map (·.2)).getD #[]) #[])
  else if cat.length == 1 then
    mergeRanges ((catTable.get.foldl (fun acc (k, rs) => if k.startsWith cat then acc ++ rs else acc) #[]) ++
      (if cat == "C" then #[(0xD800, 0xDFFF)] else #[]))
  else ((catTable.get.find? (·.1 == cat)).map (·.2)).getD #[]

/-- The General_Category values and their long names (PropertyValueAliases.txt, `gc`). -/
def catNames : List (String × String) :=
  [("C", "Other"), ("Cc", "Control"), ("Cf", "Format"), ("Cn", "Unassigned"), ("Co", "Private_Use"),
   ("Cs", "Surrogate"), ("L", "Letter"), ("LC", "Cased_Letter"), ("Ll", "Lowercase_Letter"),
   ("Lm", "Modifier_Letter"), ("Lo", "Other_Letter"), ("Lt", "Titlecase_Letter"),
   ("Lu", "Uppercase_Letter"), ("M", "Mark"), ("Mc", "Spacing_Mark"), ("Me", "Enclosing_Mark"),
   ("Mn", "Nonspacing_Mark"), ("N", "Number"), ("Nd", "Decimal_Number"), ("Nl", "Letter_Number"),
   ("No", "Other_Number"), ("P", "Punctuation"), ("Pc", "Connector_Punctuation"),
   ("Pd", "Dash_Punctuation"), ("Pe", "Close_Punctuation"), ("Pf", "Final_Punctuation"),
   ("Pi", "Initial_Punctuation"), ("Po", "Other_Punctuation"), ("Ps", "Open_Punctuation"),
   ("S", "Symbol"), ("Sc", "Currency_Symbol"), ("Sk", "Modifier_Symbol"), ("Sm", "Math_Symbol"),
   ("So", "Other_Symbol"), ("Z", "Separator"), ("Zl", "Line_Separator"),
   ("Zp", "Paragraph_Separator"), ("Zs", "Space_Separator")]

/-- A General_Category value by short or long name (and the aliases `Combining_Mark`,
`digit`, `punct`, `cntrl`). -/
def catOf (v : String) : Option String :=
  if v == "Combining_Mark" then some "M" else if v == "digit" then some "Nd"
  else if v == "punct" then some "P" else if v == "cntrl" then some "Cc"
  else (catNames.find? fun (s, l) => s == v || l == v).map (·.1)

/-- The binary Unicode properties of ECMA-262 (table "Binary Unicode property aliases") with
their aliases: the names `\p{…}` accepts alone. Only `ASCII`, `ASCII_Hex_Digit`, `Any` and
`Assigned` have code points here; the others are accepted and match no character (the
property data is a decision of its own). -/
def binaryNames : List String :=
  ["ASCII", "ASCII_Hex_Digit", "AHex", "Alphabetic", "Alpha", "Any", "Assigned", "Bidi_Control",
   "Bidi_C", "Bidi_Mirrored", "Bidi_M", "Case_Ignorable", "CI", "Cased", "Changes_When_Casefolded",
   "CWCF", "Changes_When_Casemapped", "CWCM", "Changes_When_Lowercased", "CWL",
   "Changes_When_NFKC_Casefolded", "CWKCF", "Changes_When_Titlecased", "CWT",
   "Changes_When_Uppercased", "CWU", "Dash", "Default_Ignorable_Code_Point", "DI", "Deprecated", "Dep",
   "Diacritic", "Dia", "Emoji", "Emoji_Component", "EComp", "Emoji_Modifier", "EMod",
   "Emoji_Modifier_Base", "EBase", "Emoji_Presentation", "EPres", "Extended_Pictographic", "ExtPict",
   "Extender", "Ext", "Grapheme_Base", "Gr_Base", "Grapheme_Extend", "Gr_Ext", "Hex_Digit", "Hex",
   "IDS_Binary_Operator", "IDSB", "IDS_Trinary_Operator", "IDST", "ID_Continue", "IDC", "ID_Start",
   "IDS", "Ideographic", "Ideo", "Join_Control", "Join_C", "Logical_Order_Exception", "LOE",
   "Lowercase", "Lower", "Math", "Noncharacter_Code_Point", "NChar", "Pattern_Syntax", "Pat_Syn",
   "Pattern_White_Space", "Pat_WS", "Quotation_Mark", "QMark", "Radical", "Regional_Indicator", "RI",
   "Sentence_Terminal", "STerm", "Soft_Dotted", "SD", "Terminal_Punctuation", "Term",
   "Unified_Ideograph", "UIdeo", "Uppercase", "Upper", "Variation_Selector", "VS", "White_Space",
   "space", "XID_Continue", "XIDC", "XID_Start", "XIDS"]

/-- The properties of strings (`v` only, never negated). -/
def stringPropNames : List String :=
  ["Basic_Emoji", "Emoji_Keycap_Sequence", "RGI_Emoji_Modifier_Sequence", "RGI_Emoji_Flag_Sequence",
   "RGI_Emoji_Tag_Sequence", "RGI_Emoji_ZWJ_Sequence", "RGI_Emoji"]

/-- ID_Start (UAX #31): the letters, letter numbers and Other_ID_Start. -/
def isIdStartCp (c : Nat) : Bool :=
  if c < 128 then (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 36 || c == 95
  else ["Lu", "Ll", "Lt", "Lm", "Lo", "Nl"].any (hasCatTwo · c) ||
    [0x1885, 0x1886, 0x2118, 0x212E, 0x309B, 0x309C].contains c

/-- ID_Continue, with ZWNJ and ZWJ (IdentifierPartChar). -/
def isIdPartCp (c : Nat) : Bool :=
  if c < 128 then isIdStartCp c || (48 ≤ c && c ≤ 57)
  else isIdStartCp c || ["Mn", "Mc", "Nd", "Pc"].any (hasCatTwo · c) ||
    [0xB7, 0x387, 0x1369, 0x136A, 0x136B, 0x136C, 0x136D, 0x136E, 0x136F, 0x1370, 0x1371, 0x19DA,
      0x200C, 0x200D, 0x30FB, 0xFF65].contains c

/-! ## Parsing (§22.2.1) -/

structure Env where
  cs : Array Char
  /-- UnicodeMode: `u` or `v`. -/
  uv : Bool
  /-- UnicodeSetsMode: `v`. -/
  vm : Bool
  /-- NamedCaptureGroups: UnicodeMode, or a group name in the pattern. -/
  named : Bool
  /-- CountLeftCapturingParensWithin the pattern. -/
  nGroups : Nat

structure PS where
  pos : Nat := 0
  groups : Nat := 0
  names : Array (String × Nat) := #[]
  /-- For each entry of `names`: the alternatives it is in, as (disjunction, alternative). -/
  paths : Array (List (Nat × Nat)) := #[]
  path : List (Nat × Nat) := []
  disj : Nat := 0
  ic : Bool := false
  ml : Bool := false
  dot : Bool := false
  refs : List String := []

abbrev P := StateT PS (Except String)

def bad {α} (m : String) : P α := throw ("SyntaxError: Invalid regular expression: " ++ m)
def bump (k : Nat := 1) : P Unit := modify fun s => { s with pos := s.pos + k }
def setPos (i : Nat) : P Unit := modify fun s => { s with pos := i }

@[inline] def isDig (c : Nat) : Bool := 48 ≤ c && c ≤ 57
@[inline] def hexOf (c : Nat) : Option Nat :=
  if isDig c then some (c - 48) else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87) else none

/-- SyntaxCharacter (§22.2.1) and `/`. -/
def isSyntaxChar (c : Nat) : Bool := "^$\\.*+?()[]{}|/".toList.any (·.toNat == c)

/-- ClassSetReservedPunctuator (`v`). -/
def isReservedPunct (c : Nat) : Bool := "&-!#%,:;<=>@`~".toList.any (·.toNat == c)

def classEscapeKind (c : Nat) : Option (Nat × Bool) :=
  match c with
  | 100 => some (0, false) | 68 => some (0, true)
  | 119 => some (1, false) | 87 => some (1, true)
  | 115 => some (2, false) | 83 => some (2, true)
  | _ => none

/-- The deepest nesting of classes in a `v` pattern (a deeper one is a SyntaxError, "class
too deep"): the bound of the parser's and the matcher's recursion over classes. -/
def classDepth : Nat := 256

section
variable (e : Env)

@[inline] def at? (i : Nat) : Option Nat := (e.cs[i]?).map Str.charUnit
def peekV : P (Option Nat) := do pure (at? e (← get).pos)

def hexDigits (start count : Nat) : Option Nat := Id.run do
  let mut v := 0
  for k in [0:count] do
    match (at? e (start + k)).bind hexOf with
    | some d => v := v * 16 + d
    | none => return none
  return some v

/-- Decimal digits from `i`: the value (capped at 2^31) and the index after them. -/
def decimal (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut v := 0
  let mut j := i
  for _ in [0:e.cs.size] do
    match at? e j with
    | some c => if isDig c then v := min (v * 10 + (c - 48)) 2147483647; j := j + 1 else break
    | none => break
  return if j == i then none else some (v, j)

/-- A quantifier at `i`: min, max, greedy, and the index after it. -/
def quantAt (i : Nat) : Option (Nat × Option Nat × Bool × Nat) :=
  let lazyAt := fun (j : Nat) => if at? e j == some 63 then (false, j + 1) else (true, j)
  match at? e i with
  | some 42 => let (g, j) := lazyAt (i + 1); some (0, none, g, j)
  | some 43 => let (g, j) := lazyAt (i + 1); some (1, none, g, j)
  | some 63 => let (g, j) := lazyAt (i + 1); some (0, some 1, g, j)
  | some 123 =>
    match decimal e (i + 1) with
    | none => none
    | some (lo, j) =>
      match at? e j with
      | some 125 => let (g, k) := lazyAt (j + 1); some (lo, some lo, g, k)
      | some 44 =>
        if at? e (j + 1) == some 125 then let (g, k) := lazyAt (j + 2); some (lo, none, g, k)
        else match decimal e (j + 1) with
          | some (hi, k) => if at? e k == some 125 then let (g, k') := lazyAt (k + 1); some (lo, some hi, g, k') else none
          | none => none
      | _ => none
  | _ => none

/-- `\u` escapes at `i` (after the `u`): the value and the index after; with `uv`, `\u{…}` and
a surrogate pair written as two escapes. `none`: not an escape of this form. -/
def unicodeEsc (uv : Bool) (i : Nat) : Except String (Option (Nat × Nat)) := do
  if uv && at? e i == some 123 then
    let close := (List.range (e.cs.size - i)).find? fun k => at? e (i + 1 + k) == some 125
    match close with
    | some k =>
      if k == 0 then throw "SyntaxError: Invalid regular expression: invalid Unicode escape"
      match hexDigits e (i + 1) k with
      | some v => if v ≤ 0x10FFFF then return some (v, i + 2 + k)
                  else throw "SyntaxError: Invalid regular expression: invalid Unicode escape"
      | none => throw "SyntaxError: Invalid regular expression: invalid Unicode escape"
    | none => throw "SyntaxError: Invalid regular expression: invalid Unicode escape"
  let some v := hexDigits e i 4 | return none
  let pair := if uv && 0xD800 ≤ v && v < 0xDC00 && at? e (i + 4) == some 92 && at? e (i + 5) == some 117 then
      (hexDigits e (i + 6) 4).filter (fun lo => 0xDC00 ≤ lo && lo < 0xE000) else none
  match pair with
  | some lo => return some (0x10000 + (v - 0xD800) * 1024 + (lo - 0xDC00), i + 10)
  | none => return some (v, i + 4)

/-- LegacyOctalEscapeSequence (B.1.2) at `i`: up to three octal digits, at most 0o377. -/
def legacyOctal (i : Nat) : P Nat := do
  let d0 := (at? e i).getD 48
  let oct := fun (j : Nat) => (at? e j).filter fun c => 48 ≤ c && c ≤ 55
  match oct (i + 1) with
  | none => setPos (i + 1); pure (d0 - 48)
  | some d1 =>
    let v2 := (d0 - 48) * 8 + (d1 - 48)
    match oct (i + 2) with
    | some d2 => if d0 ≤ 51 then setPos (i + 3); pure (v2 * 8 + (d2 - 48)) else setPos (i + 2); pure v2
    | none => setPos (i + 2); pure v2

/-- A character escape after the `\` at `pos` (not a class escape, not a back reference):
its value, the position moved past it. Annex B forms without `u`/`v`. -/
def charEsc (inClass : Bool) : P Nat := do
  let i := (← get).pos + 1
  let some c := at? e i | bad "\\ at end of pattern"
  match c with
  | 110 => setPos (i + 1); pure 10
  | 114 => setPos (i + 1); pure 13
  | 116 => setPos (i + 1); pure 9
  | 118 => setPos (i + 1); pure 11
  | 102 => setPos (i + 1); pure 12
  | 99 => -- \c
    match at? e (i + 1) with
    | some l =>
      if (65 ≤ l && l ≤ 90) || (97 ≤ l && l ≤ 122) then setPos (i + 2); pure (l % 32)
      else if !e.uv && inClass && (isDig l || l == 95) then setPos (i + 2); pure (l % 32)
      else if e.uv then bad "invalid unicode escape"
      else setPos i; pure 92
    | none => if e.uv then bad "\\ at end of pattern" else setPos i; pure 92
  | 120 => -- \x
    match hexDigits e (i + 1) 2 with
    | some v => setPos (i + 3); pure v
    | none => if e.uv then bad "invalid escape" else setPos (i + 1); pure 120
  | 117 => -- \u
    match ← StateT.lift (unicodeEsc e e.uv (i + 1)) with
    | some (v, j) => setPos j; pure v
    | none => if e.uv then bad "invalid Unicode escape" else setPos (i + 1); pure 117
  | 48 => -- \0
    if !(at? e (i + 1)).any isDig then setPos (i + 1); pure 0
    else if e.uv then bad "invalid decimal escape"
    else legacyOctal e i
  | _ =>
    if isDig c then
      if e.uv then bad "invalid escape"
      else if c ≥ 56 then setPos (i + 1); pure c
      else legacyOctal e i
    else if e.uv then
      if isSyntaxChar c || (inClass && c == 45) || (e.vm && inClass && isReservedPunct c) then
        setPos (i + 1); pure c
      else bad "invalid escape"
    else if c == 107 && e.named then bad "invalid named reference"
    else setPos (i + 1); pure c

/-- `\p{…}` or `\P{…}` after the `\` at `pos` (UnicodeMode): a class item. -/
def propEsc (neg : Bool) : P ClassItem := do
  let i := (← get).pos + 2
  if at? e i != some 123 then bad "invalid property name"
  let close := (List.range (e.cs.size - i)).find? fun k => at? e (i + 1 + k) == some 125
  let some k := close | bad "invalid property name"
  let body := (List.range k).filterMap fun t => (at? e (i + 1 + t)).map Char.ofNat
  let ok := fun (c : Char) => c.isAlphanum || c == '_'
  let (name, value) := match body.splitOn '=' with
    | [a] => (String.ofList a, none)
    | [a, b] => (String.ofList a, some (String.ofList b))
    | _ => ("", none)
  if name.isEmpty || !name.all ok || (value.map (fun v => v.isEmpty || !v.all ok)).getD false then
    bad "invalid property name"
  setPos (i + 2 + k)
  match value with
  | some v =>
    if name == "General_Category" || name == "gc" then
      match catOf v with
      | some c => pure (.ranges (catRangesOf c) neg)
      | none => bad "invalid property name"
    else if name == "Script" || name == "sc" || name == "Script_Extensions" || name == "scx" then
      pure (.ranges #[] neg)
    else bad "invalid property name"
  | none =>
    match catOf name with
    | some c => pure (.ranges (catRangesOf c) neg)
    | none =>
      if name == "Any" then pure (.ranges #[(0, 0x10FFFF)] neg)
      else if name == "ASCII" then pure (.ranges #[(0, 127)] neg)
      else if name == "ASCII_Hex_Digit" || name == "AHex" then
        pure (.set neg [.range 48 57, .range 65 70, .range 97 102])
      else if name == "Assigned" then pure (.ranges (catRangesOf "Cn") (!neg))
      else if binaryNames.contains name then pure (.ranges #[] neg)
      else if e.vm && !neg && stringPropNames.contains name then pure (.ranges #[] neg)
      else bad "invalid property name"

/-- One class atom (ClassAtom, not `v`): a value, or a class escape item. -/
def classAtom : P (Nat ⊕ ClassItem) := do
  let i := (← get).pos
  let some c := at? e i | bad "missing /"
  if c != 92 then bump; return .inl c
  let some d := at? e (i + 1) | bad "\\ at end of pattern"
  match classEscapeKind d with
  | some (k, neg) => bump 2; return .inr (.esc k neg)
  | none =>
    if d == 98 then bump 2; return .inl 8
    if d == 45 then bump 2; return .inl 45
    if e.uv && (d == 112 || d == 80) then return .inr (← propEsc e (d == 80))
    if !e.uv && d == 107 then bump 2; return .inl 107
    return .inl (← charEsc e true)

/-- The items of a class (ClassContents without `v`) after `[` and `^`, up to `]`. -/
def classRanges : Nat → List ClassItem → P (List ClassItem)
  | 0, _ => bad "class too long"
  | fuel + 1, acc => do
    let some c ← peekV e | bad "missing /"
    if c == 93 then bump; return acc.reverse
    let a ← classAtom e
    let i := (← get).pos
    if at? e i == some 45 && at? e (i + 1) != some 93 && (at? e (i + 1)).isSome then
      bump
      let b ← classAtom e
      match a, b with
      | .inl lo, .inl hi =>
        if hi < lo then bad "range out of order in character class"
        classRanges fuel (.range lo hi :: acc)
      | _, _ =>
        if e.uv then bad "invalid character class"
        let toItem := fun (x : Nat ⊕ ClassItem) => match x with | .inl v => ClassItem.ch v | .inr it => it
        classRanges fuel (toItem b :: .ch 45 :: toItem a :: acc)
    else
      classRanges fuel ((match a with | .inl v => .ch v | .inr it => it) :: acc)

/-- ClassSetReservedDoublePunctuator at `i`. -/
def doublePunct (i : Nat) : Bool :=
  match at? e i, at? e (i + 1) with
  | some a, some b => a == b && "&!#$%*+,.:;<=>?@^`~".toList.any (·.toNat == a)
  | _, _ => false

/-- `\q{…}` after the `\` at `pos`: the single characters and the other strings. -/
def classStrings : P (List Nat × List (List Nat)) := do
  let i := (← get).pos
  if at? e (i + 2) != some 123 then bad "invalid escape"
  setPos (i + 3)
  let mut strs : List (List Nat) := []
  let mut cur : List Nat := []
  for _ in [0:e.cs.size] do
    let some x ← peekV e | bad "missing }"
    if x == 125 then bump; break
    if x == 124 then bump; strs := cur.reverse :: strs; cur := []; continue
    if x == 92 then
      if at? e ((← get).pos + 1) == some 98 then bump 2; cur := 8 :: cur
      else cur := (← charEsc e true) :: cur
    else
      if "()[]{}/-|".toList.any (·.toNat == x) || doublePunct e (← get).pos then
        bad "invalid character in class"
      bump; cur := x :: cur
  strs := cur.reverse :: strs
  let singles := strs.filterMap fun s => match s with | [x] => some x | _ => none
  return (singles, strs.filter fun s => s.length != 1)

mutual
/-- A ClassSetOperand or a range end (`v`) at the current position, and its strings (the
strings of `\q{…}` that are not one character). -/
def setOperand : Nat → P (ClassItem × List (List Nat))
  | 0 => bad "class too deep"
  | fuel + 1 => do
    let i := (← get).pos
    let some c := at? e i | bad "missing /"
    if c == 91 then
      bump
      let neg := at? e (i + 1) == some 94
      if neg then bump
      let (items, strs) ← setContents fuel
      if neg && !strs.isEmpty then bad "negated character class may contain strings"
      return (.set neg items, strs)
    if c == 92 then
      let some d := at? e (i + 1) | bad "\\ at end of pattern"
      if let some (k, neg) := classEscapeKind d then bump 2; return (.esc k neg, [])
      if d == 112 || d == 80 then return (← propEsc e (d == 80), [])
      if d == 113 then
        let (singles, multi) ← classStrings e
        return (.set false (singles.map .ch), multi)
      if d == 98 then bump 2; return (.ch 8, [])
      return (.ch (← charEsc e true), [])
    if doublePunct e i then bad "invalid set operation in character class"
    if "()[]{}/-|".toList.any (·.toNat == c) then bad "invalid character in class"
    bump
    return (.ch c, [])

/-- ClassSetExpression (`v`) after `[` and `^`, up to `]`: a union, an intersection or a
subtraction, and its strings. -/
def setContents : Nat → P (List ClassItem × List (List Nat))
  | 0 => bad "class too deep"
  | fuel + 1 => do
    if (← peekV e) == some 93 then bump; return ([], [])
    let (first, s0) ← setOperand fuel
    let i := (← get).pos
    let isOp := fun (j : Nat) (op : Nat) => at? e j == some op && at? e (j + 1) == some op
    if isOp i 38 || isOp i 45 then
      -- an intersection or a subtraction: one operator throughout, operands only
      let op := (at? e i).getD 0
      let mut items := #[first]
      let mut strs := s0
      let mut closed := false
      for _ in [0:e.cs.size] do
        let j := (← get).pos
        if at? e j == some 93 then bump; closed := true; break
        if !isOp j op then bad "invalid set operation in character class"
        if op == 38 && at? e (j + 2) == some 38 then bad "invalid set operation in character class"
        setPos (j + 2)
        let (it, s) ← setOperand fuel
        let k := (← get).pos
        if at? e k == some 45 && at? e (k + 1) != some 45 then bad "invalid set operation in character class"
        items := items.push it
        strs := if op == 38 then strs.filter (s.contains ·) else strs.filter (!s.contains ·)
      if !closed then bad "missing ]"
      return ([if op == 38 then .inter items.toList else .diff items.toList], strs)
    -- a union of operands and ranges
    let mut items : Array ClassItem := #[]
    let mut strs := s0
    let mut pend := first
    for _ in [0:e.cs.size + 1] do
      let j := (← get).pos
      if at? e j == some 45 && at? e (j + 1) != some 45 then
        let .ch lo := pend | bad "invalid character class"
        bump
        let (hiIt, _) ← setOperand fuel
        let .ch hi := hiIt | bad "invalid character class"
        if hi < lo then bad "range out of order in character class"
        items := items.push (.range lo hi)
        let k := (← get).pos
        if at? e k == some 93 then bump; return (items.toList, strs)
        if isOp k 38 || isOp k 45 then bad "invalid set operation in character class"
        if at? e k == none then bad "missing ]"
        let (nx, s) ← setOperand fuel
        strs := strs ++ s
        pend := nx
        continue
      items := items.push pend
      if at? e j == some 93 then bump; return (items.toList, strs)
      if isOp j 38 || isOp j 45 then bad "invalid set operation in character class"
      if at? e j == none then bad "missing ]"
      let (nx, s) ← setOperand fuel
      strs := strs ++ s
      pend := nx
    bad "class too long"
end

/-- A group name after `<`, up to `>` (RegExpIdentifierName, §22.2.1.6): escapes decoded, a
surrogate pair of the pattern one character. -/
def groupName : P String := do
  let mut out : Array Nat := #[]
  let mut closed := false
  for _ in [0:e.cs.size + 1] do
    let i := (← get).pos
    let some c := at? e i | bad "invalid capture group name"
    if c == 62 then bump; closed := true; break
    let (v, j) ← if c == 92 then do
        if at? e (i + 1) != some 117 then bad "invalid capture group name"
        match ← StateT.lift (unicodeEsc e true (i + 2)) with
        | some r => pure r
        | none => bad "invalid capture group name"
      else if 0xD800 ≤ c && c < 0xDC00 && (at? e (i + 1)).any (fun d => 0xDC00 ≤ d && d < 0xE000) then
        pure (0x10000 + (c - 0xD800) * 1024 + ((at? e (i + 1)).getD 0xDC00 - 0xDC00), i + 2)
      else pure (c, i + 1)
    let ok := if out.isEmpty then isIdStartCp v else isIdPartCp v
    if !ok || (0xD800 ≤ v && v < 0xE000) then bad "invalid capture group name"
    out := out.push v
    setPos j
  if out.isEmpty || !closed then bad "invalid capture group name"
  return String.ofList (out.toList.map Char.ofNat)

def closeP : P Unit := do
  if (← peekV e) == some 41 then bump else bad "missing )"

/-- The modifiers of `(?ims-ims:` at `i` (after `?`): the flags to add, to remove, and the
index of the `:`; `none` if this is not a modifier group. -/
def modifiersAt (i : Nat) : Option (List Nat × List Nat × Nat) := Id.run do
  let mut add : List Nat := []
  let mut rem : List Nat := []
  let mut minus := false
  let mut j := i
  for _ in [0:8] do
    match at? e j with
    | some 58 => return some (add.reverse, rem.reverse, j)
    | some 45 => if minus then return none else minus := true; j := j + 1
    | some c =>
      if c == 105 || c == 109 || c == 115 then
        if minus then rem := c :: rem else add := c :: add
        j := j + 1
      else return none
    | none => return none
  return none

end

/-- Two groups of one name might both take part unless some disjunction holds them in
different alternatives (MightBothParticipate, §22.2.1.1). -/
def bothParticipate (p q : List (Nat × Nat)) : Bool :=
  !(p.any fun (d, a) => q.any fun (d', a') => d == d' && a != a')

section
variable (e : Env)

mutual
def disjunction : Nat → P Node
  | 0 => bad "too deep"
  | fuel + 1 => do
    let d := (← get).disj
    let outer := (← get).path
    modify fun s => { s with disj := d + 1, path := (d, 0) :: outer }
    let first ← alternative fuel []
    let mut alts := #[first]
    for k in [1:e.cs.size + 2] do
      if (← peekV e) == some 124 then
        bump
        modify fun s => { s with path := (d, k) :: outer }
        alts := alts.push (← alternative fuel [])
      else break
    modify fun s => { s with path := outer }
    return if alts.size == 1 then first else .alt alts.toList

def alternative : Nat → List Node → P Node
  | 0, _ => bad "too long"
  | fuel + 1, acc => do
    match ← peekV e with
    | none | some 124 | some 41 =>
      return match acc with | [] => .empty | [x] => x | xs => .seq xs.reverse
    | some _ =>
      let t ← term fuel
      alternative fuel (t :: acc)

def term : Nat → P Node
  | 0 => bad "too deep"
  | fuel + 1 => do
    let i := (← get).pos
    let some c ← peekV e | return .empty
    let st ← get
    if c == 94 then bump; return .bol st.ml
    if c == 36 then bump; return .eol st.ml
    if c == 92 && at? e (i + 1) == some 98 then bump 2; return .wordB false st.ic
    if c == 92 && at? e (i + 1) == some 66 then bump 2; return .wordB true st.ic
    let firstGroup := st.groups
    let atom ← atomP fuel
    let j := (← get).pos
    match quantAt e j with
    | some (lo, hi, greedy, k) =>
      match atom with
      | .look true _ _ => bad "nothing to repeat"
      | .look false _ _ => if e.uv then bad "nothing to repeat" else pure ()
      | _ => pure ()
      if let some h := hi then
        if h < lo then bad "numbers out of order in {} quantifier"
      setPos k
      return .rep atom lo hi greedy firstGroup ((← get).groups - firstGroup)
    | none =>
      match at? e j with
      | some 42 | some 43 | some 63 => bad "nothing to repeat"
      | some 123 => if e.uv then bad "incomplete quantifier" else return atom
      | _ => return atom

def atomP : Nat → P Node
  | 0 => bad "too deep"
  | fuel + 1 => do
    let i := (← get).pos
    let some c ← peekV e | bad "unexpected end"
    let st ← get
    match c with
    | 46 => bump; return .any st.dot
    | 91 =>
      bump
      let neg := at? e (i + 1) == some 94
      if neg then bump
      if e.vm then
        let (items, strs) ← setContents e classDepth
        if neg && !strs.isEmpty then bad "negated character class may contain strings"
        if strs.isEmpty then return .cls neg items st.ic
        -- the strings, longest first, then the single characters (§22.2.2.9 CompileAtom)
        let sorted := (strs.toArray.qsort fun a b => a.length > b.length).toList
        let strNodes := sorted.map fun s => Node.seq (s.map (Node.char · st.ic))
        return .group none (.alt (strNodes ++ [.cls false items st.ic]))
      return .cls neg (← classRanges e (e.cs.size + 1) []) st.ic
    | 40 =>
      if at? e (i + 1) == some 63 then
        match at? e (i + 2) with
        | some 58 => bump 3; let r ← disjunction fuel; closeP e; return .group none r
        | some 61 => bump 3; let r ← disjunction fuel; closeP e; return .look false false r
        | some 33 => bump 3; let r ← disjunction fuel; closeP e; return .look false true r
        | some 60 =>
          if at? e (i + 3) == some 61 || at? e (i + 3) == some 33 then
            let neg := at? e (i + 3) == some 33
            bump 4
            let r ← disjunction fuel
            closeP e
            return .look true neg r
          else
            bump 3
            let name ← groupName e
            let idx := (← get).groups + 1
            let s ← get
            for k in [0:s.names.size] do
              if s.names[k]!.1 == name && bothParticipate s.paths[k]! s.path then
                bad "duplicate capture group name"
            modify fun s => { s with groups := idx, names := s.names.push (name, idx), paths := s.paths.push s.path }
            let r ← disjunction fuel; closeP e
            return .group (some idx) r
        | _ =>
          match modifiersAt e (i + 2) with
          | some (add, rem, colon) =>
            if add.isEmpty && rem.isEmpty then bad "invalid group"
            if add.eraseDups.length != add.length || rem.eraseDups.length != rem.length ||
                add.any rem.contains then bad "invalid flags in modifier group"
            setPos (colon + 1)
            let has := fun (f : Nat) (cur : Bool) => if add.contains f then true else if rem.contains f then false else cur
            modify fun s => { s with ic := has 105 s.ic, ml := has 109 s.ml, dot := has 115 s.dot }
            let r ← disjunction fuel
            closeP e
            modify fun s => { s with ic := st.ic, ml := st.ml, dot := st.dot }
            return .group none r
          | none => bad "invalid group"
      else
        bump
        let idx := (← get).groups + 1
        modify fun s => { s with groups := idx }
        let r ← disjunction fuel; closeP e
        return .group (some idx) r
    | 41 => bad "unmatched ')'"
    | 42 | 43 | 63 => bad "nothing to repeat"
    | 123 =>
      if e.uv then bad "lone quantifier brackets"
      if (quantAt e i).isSome then bad "nothing to repeat"
      bump; return .char 123 st.ic
    | 125 => if e.uv then bad "lone quantifier brackets" else bump; return .char 125 st.ic
    | 93 => if e.uv then bad "lone ']'" else bump; return .char 93 st.ic
    | 92 =>
      let some d := at? e (i + 1) | bad "\\ at end of pattern"
      match classEscapeKind d with
      | some (k, neg) => bump 2; return .cls false [.esc k neg] st.ic
      | none =>
        if e.uv && (d == 112 || d == 80) then return .cls false [← propEsc e (d == 80)] st.ic
        if isDig d && d != 48 then
          match decimal e (i + 1) with
          | some (v, j) =>
            if v ≤ e.nGroups then setPos j; return .backref [v] st.ic
            if e.uv then bad "invalid escape"
            return .char (← charEsc e false) st.ic
          | none => return .char (← charEsc e false) st.ic
        if d == 107 && e.named then
          if at? e (i + 2) != some 60 then bad "invalid named reference"
          bump 3
          let name ← groupName e
          modify fun s => { s with refs := name :: s.refs }
          return .named name st.ic
        return .char (← charEsc e false) st.ic
    | c => bump; return .char c st.ic
end

end

/-- Back references by name to their numbers (every group with that name). -/
def resolve (names : Array (String × Nat)) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n => match n with
    | .named name ic => .backref ((names.filter (·.1 == name)).toList.map (·.2)) ic
    | .group idx r => .group idx (resolve names fuel r)
    | .look b neg r => .look b neg (resolve names fuel r)
    | .seq rs => .seq (rs.map (resolve names fuel))
    | .alt rs => .alt (rs.map (resolve names fuel))
    | .rep r lo hi g f c => .rep (resolve names fuel r) lo hi g f c
    | n => n

/-- CountLeftCapturingParensWithin and whether the pattern has a GroupName (a scan that skips
escapes and classes). -/
def scanGroups (cs : Array Char) : Nat × Bool := Id.run do
  let mut n := 0
  let mut named := false
  let mut i := 0
  let mut inClass := false
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '\\' then i := i + 2; continue
    if inClass then
      if c == ']' then inClass := false
    else if c == '[' then inClass := true
    else if c == '(' then
      if cs[i+1]? != some '?' then n := n + 1
      else if cs[i+2]? == some '<' && cs[i+3]? != some '=' && cs[i+3]? != some '!' then
        n := n + 1; named := true
    i := i + 1
  return (n, named)

/-- A one character matcher every match starts with, when the pattern begins with one. -/
def leadOf : Nat → Node → Option Node
  | 0, _ => none
  | fuel + 1, n => match n with
    | .char .. | .cls .. | .any _ | .bol _ | .wordB .. => some n
    | .group _ r => leadOf fuel r
    | .seq (r :: _) => leadOf fuel r
    | .rep r lo _ _ _ _ => if lo ≥ 1 then leadOf fuel r else none
    | _ => none

/-- Compile a pattern with its flags (§22.2.3.4 RegExpInitialize): an error message
that starts with `SyntaxError:` when the pattern or the flags are not valid. -/
def compile (pattern flags : String) : Except String Compiled := do
  let some fl := parseFlags flags | throw s!"SyntaxError: Invalid regular expression flags '{flags}'"
  let uv := fl.uv
  -- code units without `u`/`v`, code points with them
  let cs := if uv then pattern.toList.toArray else Str.unitChars pattern
  let (nGroups, hasName) := scanGroups cs
  let env : Env := { cs, uv, vm := fl.unicodeSets, named := uv || hasName, nGroups }
  let (node, st) ← (disjunction env (4 * cs.size + 16)).run { ic := fl.icase, ml := fl.multiline, dot := fl.dotAll }
  if st.pos < cs.size then
    throw (if cs[st.pos]! == ')' then "SyntaxError: Invalid regular expression: unmatched ')'"
      else "SyntaxError: Invalid regular expression")
  for r in st.refs do
    if !(st.names.any (·.1 == r)) then throw "SyntaxError: Invalid regular expression: invalid named capture referenced"
  let node := resolve st.names (cs.size + 2) node
  return { node, groups := st.groups, names := st.names, flags := fl, lead := leadOf 64 node }

/-! ## Matching (§22.2.2) -/

/-- Canonicalize (§22.2.2.7.3): simple case folding with `u`/`v`, else the upper case
mapping when it is one character and does not take a non-ASCII character to ASCII. -/
def canon (uv : Bool) (c : Nat) : Nat :=
  if c < 128 then
    if uv then (if 65 ≤ c && c ≤ 90 then c + 32 else c) else (if 97 ≤ c && c ≤ 122 then c - 32 else c)
  else if uv then CaseMap.caseFoldCp c
  else match CaseMap.fullUpper c with
    | [u] => if u < 128 then c else u
    | _ => c

@[inline] def isLineTermN (c : Nat) : Bool := c == 10 || c == 13 || c == 0x2028 || c == 0x2029

/-- WordCharacters (§22.2.2.9.3): with `u`/`v` and `i`, also the characters that fold to one. -/
@[inline] def isWordN (uvIc : Bool) (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 ||
    (uvIc && (c == 0x17F || c == 0x212A))

def isSpaceN (c : Nat) : Bool :=
  c == 9 || c == 10 || c == 11 || c == 12 || c == 13 || c == 32 || c == 0xA0 || c == 0x1680 ||
    (0x2000 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F ||
    c == 0x3000 || c == 0xFEFF

/-- Whether a class item holds `c` (no case folding). -/
def itemHas (uvIc : Bool) : Nat → ClassItem → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, it, c => match it with
    | .ch x => c == x
    | .range lo hi => lo ≤ c && c ≤ hi
    | .esc k neg =>
      let r := match k with | 0 => 48 ≤ c && c ≤ 57 | 1 => isWordN uvIc c | _ => isSpaceN c
      r != neg
    | .ranges rs neg => inRanges rs c != neg
    | .set neg items => items.any (itemHas uvIc fuel · c) != neg
    | .inter items => !items.isEmpty && items.all (itemHas uvIc fuel · c)
    | .diff [] => false
    | .diff (a :: bs) => itemHas uvIc fuel a c && !bs.any (itemHas uvIc fuel · c)

/-- Whether a class holds `c`: with `i`, some member with the same Canonicalize. -/
def classHas (uv ic : Bool) (items : List ClassItem) (c : Nat) : Bool :=
  let uvIc := uv && ic
  items.any (itemHas uvIc (classDepth + 1) · c) ||
    (ic && (let k := canon uv c
      let cands := if c < 128 && !uv then
          [if 65 ≤ c && c ≤ 90 then c + 32 else if 97 ≤ c && c ≤ 122 then c - 32 else c]
        else CaseMap.caseVariants c
      cands.any fun x => x != c && canon uv x == k && items.any (itemHas uvIc (classDepth + 1) · x)))

/-- One character matcher node on the value `c`. -/
def oneChar (uv : Bool) (n : Node) (c : Nat) : Bool :=
  match n with
  | .char x ic => c == x || (ic && canon uv c == canon uv x)
  | .any dot => dot || !isLineTermN c
  | .cls neg items ic => classHas uv ic items c != neg
  | _ => false

@[inline] def isOneChar : Node → Bool
  | .char .. | .any _ | .cls .. => true
  | _ => false

/-- The character at `pos` going forward: its value and width (two for a surrogate pair
with `u`/`v`). -/
@[inline] def readF (cs : Array Char) (uv : Bool) (pos : Nat) : Option (Nat × Nat) :=
  if pos < cs.size then
    let c := Str.charUnit cs[pos]!
    if uv && 0xD800 ≤ c && c < 0xDC00 && pos + 1 < cs.size then
      let d := Str.charUnit cs[pos + 1]!
      if 0xDC00 ≤ d && d < 0xE000 then some (0x10000 + (c - 0xD800) * 0x400 + (d - 0xDC00), 2)
      else some (c, 1)
    else some (c, 1)
  else none

/-- The character before `pos` (matching backward, in a lookbehind). -/
@[inline] def readB (cs : Array Char) (uv : Bool) (pos : Nat) : Option (Nat × Nat) :=
  if pos == 0 || pos > cs.size then none else
    let c := Str.charUnit cs[pos - 1]!
    if uv && 0xDC00 ≤ c && c < 0xE000 && pos ≥ 2 then
      let d := Str.charUnit cs[pos - 2]!
      if 0xD800 ≤ d && d < 0xDC00 then some (0x10000 + (d - 0xD800) * 0x400 + (c - 0xDC00), 2)
      else some (c, 1)
    else some (c, 1)

inductive Frame where
  | node (n : Node) (fwd : Bool)
  | close (idx start : Nat) (fwd : Bool)
  /-- After one iteration of a quantified atom that began at `start`: the empty check of
  RepeatMatcher (when `checkEmpty`), then the rest of the repetition. -/
  | repLoop (r : Node) (min : Nat) (max : Option Nat) (greedy : Bool) (first count start : Nat)
      (checkEmpty fwd : Bool)
  /-- The end of a lookaround that began at `pos0` with the choice stack `h` deep. -/
  | lookEnd (neg : Bool) (pos0 h : Nat)
  /-- Fail now (take the next choice point). -/
  | failNow
  deriving Inhabited

abbrev Caps := Array (Option (Nat × Nat))

inductive Choice where
  | resume (pos : Nat) (caps : Caps) (k : List Frame)
  /-- A run of one character matcher: the counts from `j` to `stop`, `ends[j]` the position
  after `j` characters (`base ± j` when every character is one unit). -/
  | counts (base : Nat) (fwd : Bool) (ends : Option (Array Nat)) (j stop : Nat) (greedy : Bool)
      (caps : Caps) (k : List Frame)
  /-- A lazy run of one character matcher at `pos` after `j` characters: one more, then `k`. -/
  | lazy (r : Node) (fwd : Bool) (pos j : Nat) (hi : Option Nat) (caps : Caps) (k : List Frame)
  /-- The bottom of a lookaround: reached when its body has no match. -/
  | lookFail (neg : Bool) (pos : Nat) (caps : Caps) (k : List Frame)
  deriving Inhabited

structure Mach where
  pos : Nat
  caps : Caps
  k : List Frame
  stack : List Choice
  depth : Nat
  deriving Inhabited

inductive Step where
  | cont (m : Mach) (cost : Nat)
  | done (m : Mach)
  | fail

/-- The character next to `pos` in direction `fwd`: value and width. -/
@[inline] def readAt (cs : Array Char) (uv fwd : Bool) (pos : Nat) : Option (Nat × Nat) :=
  if fwd then readF cs uv pos else readB cs uv pos

@[inline] def posAt (base : Nat) (fwd : Bool) (ends : Option (Array Nat)) (j : Nat) : Nat :=
  match ends with
  | some a => a.getD j base
  | none => if fwd then base + j else base - j

/-- Whether the frames `k` can go on at `pos`: false only when the next frame is a one
character matcher in direction `fwd` that does not match there (a filter for the counts of a
greedy run). -/
def nextOk (cs : Array Char) (uv : Bool) (k : List Frame) (fwd : Bool) (pos : Nat) : Bool :=
  match k with
  | .node n fwd' :: _ =>
    if fwd' == fwd && isOneChar n then
      if !uv then
        if fwd then pos < cs.size && oneChar false n (Str.charUnit cs[pos]!)
        else pos > 0 && pos ≤ cs.size && oneChar false n (Str.charUnit cs[pos - 1]!)
      else match readAt cs uv fwd pos with
        | some (c, _) => oneChar uv n c
        | none => false
    else true
  | _ => true

/-- The first count from `j` toward `stop` (down when `greedy`) at which `k` can go on, at
most `j`'s distance from `stop` tries. -/
def firstCount (cs : Array Char) (uv : Bool) (k : List Frame) (base : Nat) (fwd : Bool)
    (ends : Option (Array Nat)) (j stop : Nat) (greedy : Bool) : Option Nat := Id.run do
  let mut t := j
  for _ in [0:(if greedy then j - stop else stop - j) + 1] do
    if nextOk cs uv k fwd (posAt base fwd ends t) then return some t
    t := if greedy then t - 1 else t + 1
  return none

/-- Take the top choice point. -/
def pop (cs : Array Char) (uv : Bool) (m : Mach) : Step :=
  match m.stack with
  | [] => .fail
  | ch :: rest =>
    let m := { m with stack := rest, depth := m.depth - 1 }
    match ch with
    | .resume p c k => .cont { m with pos := p, caps := c, k } 1
    | .counts base fwd ends j stop greedy caps k =>
      match firstCount cs uv k base fwd ends j stop greedy with
      | none => .cont { m with k := [.failNow] } (1 + (if greedy then j - stop else stop - j))
      | some i =>
        let m := if i == stop then m else
          { m with stack := .counts base fwd ends (if greedy then i - 1 else i + 1) stop greedy caps k :: m.stack,
                   depth := m.depth + 1 }
        .cont { m with pos := posAt base fwd ends i, caps, k } (1 + (if greedy then j - i else i - j))
    | .lazy r fwd p j hi caps k =>
      -- one more character; then, below `hi`, the next lazy choice; then the continuation
      match (if fwd then readF cs uv p else readB cs uv p) with
      | some (c, w) =>
        if oneChar uv r c then
          let p' := if fwd then p + w else p - w
          if hi == some (j + 1) then .cont { m with pos := p', caps, k } 1
          else .cont { m with pos := p', caps, k, stack := .lazy r fwd p' (j + 1) hi caps k :: m.stack,
                              depth := m.depth + 1 } 1
        else .cont { m with k := [.failNow] } 1
      | none => .cont { m with k := [.failNow] } 1
    | .lookFail neg p c k =>
      if neg then .cont { m with pos := p, caps := c, k } 1
      else .cont { m with k := [.failNow] } 1

/-- Clear the captures `first + 1 .. first + count` (RepeatMatcher step 4). -/
def clearCaps (caps : Caps) (first count : Nat) : Caps := Id.run do
  let mut c := caps
  for t in [first:first + count] do
    if t < c.size then c := c.set! t none
  return c

/-- The text of a back reference matches at `pos` (forward) or before it (backward): the
position after it. -/
def backrefOk (cs : Array Char) (uv ic : Bool) (a b pos : Nat) (fwd : Bool) : Option Nat :=
  let len := b - a
  let s := if fwd then pos else pos - len
  if (fwd && pos + len > cs.size) || (!fwd && len > pos) then none
  else if (List.range len).all (fun t =>
      let x := Str.charUnit cs[a + t]!
      let y := Str.charUnit cs[s + t]!
      x == y || (ic && canon uv x == canon uv y)) then
    some (if fwd then pos + len else s)
  else none

/-- The length of the run of a one character matcher from `pos` (at most `limit`), and with
`u`/`v` the position after each count. -/
def runOf (cs : Array Char) (uv : Bool) (r : Node) (fwd : Bool) (pos limit : Nat) : Nat × Option (Array Nat) := Id.run do
  if !uv then
    -- one unit a character: no widths to keep
    let mut j := 0
    for _ in [0:limit] do
      let q := if fwd then pos + j else pos - j - 1
      if (fwd && q < cs.size) || (!fwd && j < pos) then
        if oneChar false r (Str.charUnit cs[q]!) then j := j + 1 else break
      else break
    return (j, none)
  let mut p := pos
  let mut j := 0
  let mut ends : Array Nat := if uv then #[pos] else #[]
  for _ in [0:limit] do
    match (if fwd then readF cs uv p else readB cs uv p) with
    | some (c, w) =>
      if oneChar uv r c then
        p := if fwd then p + w else p - w
        j := j + 1
        if uv then ends := ends.push p
      else break
    | none => break
  return (j, if uv then some ends else none)

/-- One step of the machine. -/
def step (cs : Array Char) (uv : Bool) (m : Mach) : Step :=
  match m.k with
  | [] => .done m
  | f :: k =>
    let m := { m with k }
    match f with
    | .failNow => pop cs uv m
    | .close idx start fwd =>
      let v := if fwd then (start, m.pos) else (m.pos, start)
      .cont { m with caps := if idx ≥ 1 && idx ≤ m.caps.size then m.caps.set! (idx - 1) (some v) else m.caps } 1
    | .lookEnd neg pos0 h =>
      let cut := { m with stack := m.stack.drop (m.depth - h), depth := h }
      if neg then pop cs uv cut else .cont { cut with pos := pos0 } 1
    | .repLoop r lo hi greedy first count start checkEmpty fwd =>
      if checkEmpty && m.pos == start then pop cs uv m
      else .cont { m with k := .node (.rep r lo hi greedy first count) fwd :: k } 1
    | .node n fwd =>
      match n with
      | .empty => .cont m 1
      | .char .. | .any _ | .cls .. =>
        if !uv then
          -- one unit a character
          if fwd then
            if m.pos < cs.size && oneChar false n (Str.charUnit cs[m.pos]!) then .cont { m with pos := m.pos + 1 } 1
            else pop cs uv m
          else
            if m.pos > 0 && m.pos ≤ cs.size && oneChar false n (Str.charUnit cs[m.pos - 1]!) then .cont { m with pos := m.pos - 1 } 1
            else pop cs uv m
        else
        match readAt cs uv fwd m.pos with
        | some (c, w) =>
          if oneChar uv n c then .cont { m with pos := if fwd then m.pos + w else m.pos - w } 1 else pop cs uv m
        | none => pop cs uv m
      | .bol ml =>
        if m.pos == 0 || (ml && m.pos ≤ cs.size && isLineTermN (Str.charUnit cs[m.pos - 1]!)) then .cont m 1 else pop cs uv m
      | .eol ml =>
        if m.pos == cs.size || (ml && m.pos < cs.size && isLineTermN (Str.charUnit cs[m.pos]!)) then .cont m 1 else pop cs uv m
      | .wordB neg ic =>
        let w := fun (i : Nat) => isWordN (uv && ic) (Str.charUnit cs[i]!)
        let a := m.pos > 0 && m.pos ≤ cs.size && w (m.pos - 1)
        let b := m.pos < cs.size && w m.pos
        if (a != b) != neg then .cont m 1 else pop cs uv m
      | .group none r => .cont { m with k := .node r fwd :: k } 1
      | .group (some idx) r => .cont { m with k := .node r fwd :: .close idx m.pos fwd :: k } 1
      | .look behind neg r =>
        let h := m.depth
        .cont { m with k := .node r (!behind) :: .lookEnd neg m.pos h :: k,
                       stack := .lookFail neg m.pos m.caps k :: m.stack, depth := h + 1 } 1
      | .backref ks ic =>
        match groupValue m.caps (ks.map (· - 1)) with
        | none => .cont m 1
        | some (a, b) =>
          match backrefOk cs uv ic a b m.pos fwd with
          | some p => .cont { m with pos := p } (1 + (b - a) / 16)
          | none => pop cs uv m
      | .named _ _ => .cont m 1
      | .seq rs =>
        -- forward: the first element on top; backward (in a lookbehind): the last
        .cont { m with k := (if fwd then rs.reverse else rs).foldl (fun acc r => Frame.node r fwd :: acc) k } 1
      | .alt [] => pop cs uv m
      | .alt [r] => .cont { m with k := .node r fwd :: k } 1
      | .alt (r :: rs) =>
        .cont { m with k := .node r fwd :: k, stack := .resume m.pos m.caps (.node (.alt rs) fwd :: k) :: m.stack,
                       depth := m.depth + 1 } 1
      | .rep r lo hi greedy first count =>
        if hi == some 0 then .cont m 1
        else if greedy && isOneChar r then
          -- a greedy run of one character matcher: count it, then the shorter counts are
          -- one choice point
          let limit := match hi with | some h => min h cs.size | none => cs.size
          let (run, ends) := runOf cs uv r fwd m.pos limit
          if run < lo then pop cs uv m
          else match firstCount cs uv k m.pos fwd ends run lo true with
            | none => .cont { m with k := [.failNow] } (1 + 2 * run)
            | some i =>
              let stack := if i == lo then m.stack else
                .counts m.pos fwd ends (i - 1) lo true m.caps k :: m.stack
              .cont { m with pos := posAt m.pos fwd ends i, stack,
                             depth := if i == lo then m.depth else m.depth + 1 } (1 + run + (run - i))
        else if isOneChar r then
          -- a lazy run of one character matcher: the minimum, then one more at each choice
          let (run, ends) := runOf cs uv r fwd m.pos lo
          if run < lo then pop cs uv m
          else
            let p := posAt m.pos fwd ends lo
            if hi == some lo then .cont { m with pos := p } (1 + lo)
            else .cont { m with pos := p, stack := .lazy r fwd p lo hi m.caps k :: m.stack,
                                depth := m.depth + 1 } (1 + lo)
        else
          let cleared := clearCaps m.caps first count
          let hi' := hi.map (· - 1)
          let again := fun (chk : Bool) (lo' : Nat) => Frame.repLoop r lo' hi' greedy first count m.pos chk fwd
          if lo > 0 then
            .cont { m with caps := cleared, k := .node r fwd :: again false (lo - 1) :: k } 1
          else if greedy then
            .cont { m with caps := cleared, k := .node r fwd :: again true 0 :: k,
                           stack := .resume m.pos m.caps k :: m.stack, depth := m.depth + 1 } 1
          else
            .cont { m with stack := .resume m.pos cleared (.node r fwd :: again true 0 :: k) :: m.stack,
                           depth := m.depth + 1 } 1

/-- Run the machine with fuel and a step budget: the outcome (`some (some m)` a match ending
in `m`, `some none` no match) or `none`, the refusal when the budget is spent; and the budget
left. The fuel only makes the recursion structural: callers give fuel equal to the budget,
and each step costs at least one unit. -/
def run (cs : Array Char) (uv : Bool) : Nat → Nat → Mach → Option (Option Mach) × Nat
  | 0, b, _ => (none, b)
  | fuel + 1, b, m =>
    if b = 0 then (none, 0) else
    match step cs uv m with
    | .done m => (some (some m), b - 1)
    | .fail => (some none, b - 1)
    | .cont m' cost => if cost ≥ b then (none, 0) else run cs uv fuel (b - cost) m'

/-- Says: the budget left after a run is at most the budget given.
Does not say: how much of it a pattern needs. Kind: resource bound. -/
theorem run_rem_le (cs : Array Char) (uv : Bool) : ∀ (fuel b : Nat) (m : Mach), (run cs uv fuel b m).2 ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro b m; simp [run]
  | succ f ih =>
    intro b m
    unfold run
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, if_false]
      split
      · simp
      · simp
      · rename_i m' cost _
        by_cases hc : cost ≥ b
        · simp [hc]
        · simp only [hc, if_false]; have := ih (b - cost) m'; omega

/-- Says: with no budget the machine refuses (`none`) and does no step.
Does not say: which patterns reach the refusal. Kind: refusal at a bound. -/
theorem run_budget_zero (cs : Array Char) (uv : Bool) (fuel : Nat) (m : Mach) :
    run cs uv fuel 0 m = (none, 0) := by
  cases fuel <;> simp [run]

/-- The answer of a match attempt. -/
inductive Result where
  | ok (caps : Caps)
  | none
  /-- The step budget ran out: the defined refusal of a pattern that takes too long. -/
  | limit
  deriving Inhabited

/-- The step budget of one `exec` on a subject of `n` code units: 2^24 steps and 16 more for
each unit (a search tries every start; the budget stays far below 2^31 for any string the
engine allows, 2^28 bytes). -/
def budgetFor (n : Nat) : Nat := 16777216 + 16 * n

/-- One match attempt at `start`: the outcome and the budget left. -/
def attempt (re : Compiled) (cs : Array Char) (start b : Nat) : Option (Option Mach) × Nat :=
  run cs re.flags.uv b b { pos := start, caps := Array.replicate re.groups none,
                           k := [.node re.node true], stack := [], depth := 0 }

/-- The width of the character at `start` (one past the end). -/
def widthAt (cs : Array Char) (uv : Bool) (start : Nat) : Nat :=
  match readF cs uv start with | some (_, w) => w | none => 1

/-- A start position that cannot begin a match: not the pattern's `lead` character. -/
def skipAt (re : Compiled) (cs : Array Char) (start : Nat) : Bool :=
  match re.lead with
  | some (.bol ml) => !re.flags.sticky && start != 0 &&
      !(ml && start ≤ cs.size && isLineTermN (Str.charUnit cs[start - 1]!))
  | some (.wordB neg ic) => !re.flags.sticky &&
      (let w := fun (i : Nat) => isWordN (re.flags.uv && ic) (Str.charUnit cs[i]!)
       let a := start > 0 && start ≤ cs.size && w (start - 1)
       let b := start < cs.size && w start
       (a != b) == neg)
  | some n => !re.flags.sticky && (match readF cs re.flags.uv start with
    | some (c, _) => !oneChar re.flags.uv n c
    | none => true)
  | none => false

/-- The search of RegExpBuiltinExec (§22.2.7.2) from `start`: a match attempt at each start
position (only the first when sticky), moving by a code point with `u`/`v`. A start that
cannot begin a match (`lead`) is passed over without an attempt. -/
def search (re : Compiled) (cs : Array Char) : Nat → Nat → Nat → Result × Nat
  | 0, _, b => (.none, b)
  | fuel + 1, start, b =>
    if b = 0 then (.limit, 0)
    else if start > cs.size then (.none, b)
    else if skipAt re cs start then search re cs fuel (start + widthAt cs re.flags.uv start) b
    else match attempt re cs start b with
      | (some (some m), r) => (.ok (#[some (start, m.pos)] ++ m.caps), r)
      | (some none, r) =>
        if re.flags.sticky then (.none, r)
        else search re cs fuel (start + widthAt cs re.flags.uv start) r
      | (none, r) => (.limit, r)

/-- Says: a search with no budget refuses.
Does not say: anything about a search with budget. Kind: refusal at a bound. -/
theorem search_budget_zero (re : Compiled) (cs : Array Char) (fuel start : Nat) :
    search re cs (fuel + 1) start 0 = (.limit, 0) := by
  simp [search]

/-- Says: the budget left after a search is at most the budget given (the steps of all its
attempts come out of one budget). Kind: resource bound. -/
theorem search_rem_le (re : Compiled) (cs : Array Char) : ∀ (fuel start b : Nat), (search re cs fuel start b).2 ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro s b; simp [search]
  | succ f ih =>
    intro s b
    have hr : ∀ s b, (attempt re cs s b).2 ≤ b := fun s b => run_rem_le cs _ _ _ _
    simp only [search]
    by_cases hb : b = 0
    · simp [hb]
    rw [if_neg hb]
    by_cases hs : s > cs.size
    · rw [if_pos hs]; simp
    rw [if_neg hs]
    by_cases hk : skipAt re cs s = true
    · rw [if_pos hk]; exact ih _ _
    rw [if_neg hk]
    rcases h : attempt re cs s b with ⟨o, r⟩
    have hle := hr s b
    rw [h] at hle
    simp only at hle
    rcases o with _ | o
    · simpa using hle
    · rcases o with _ | m
      · by_cases hst : re.flags.sticky = true
        · simp [hst]; exact hle
        · simp [hst]; have := ih (s + widthAt cs re.flags.uv s) r; omega
      · simpa using hle

/-- RegExpBuiltinExec's search from `from_`, with the step budget (`budgetFor` by default):
the captures (capture 0 the whole match), no match, or the refusal; and the steps used. With
`u`/`v`, a start inside a surrogate pair starts at the pair (§22.2.7.2: the code point that
holds index lastIndex). -/
def execR (re : Compiled) (cs : Array Char) (from_ : Nat) (budget : Option Nat := none) : Result × Nat :=
  if from_ > cs.size then (.none, 0) else
  let b := budget.getD (budgetFor cs.size)
  let from_ := if re.flags.uv && from_ > 0 && from_ < cs.size &&
      (let c := Str.charUnit cs[from_]!; 0xDC00 ≤ c && c < 0xE000) &&
      (let d := Str.charUnit cs[from_ - 1]!; 0xD800 ≤ d && d < 0xDC00) then from_ - 1 else from_
  let (r, left) := search re cs (cs.size - from_ + 2) from_ b
  (r, b - left)

/-- `execR` without the steps, a refusal read as no match (for callers with their own bound:
URLPattern's components, whose patterns come from the page and whose inputs are URLs). -/
def exec (re : Compiled) (cs : Array Char) (from_ : Nat) : Option Caps :=
  match (execR re cs from_).1 with
  | .ok caps => some caps
  | _ => none

end L4Factoidal.JS.Re
