import L4Factoidal.JS.Lexer
import L4Factoidal.Regex.XPath40
import L4Factoidal.Unicode.RegexPropData

/-!
# L4Factoidal.JS.Regex — regular expressions of the engine (§22.2)

A backtracking matcher in the shape of §22.2.2 (Pattern Semantics): each node is a
Matcher that takes a state (the end index and the captures) and a continuation, and
answers the final state or failure. Every function takes fuel and passes a smaller one
to each recursive call, so all of it is total.

Supported: alternatives, sequences, the quantifiers `*`, `+`, `?`, `{n}`, `{n,}`,
`{n,m}` (greedy and lazy, with the empty check of RepeatMatcher step 2.b and the reset
of the captures inside the atom at each repetition), capturing, non-capturing and named
groups (a name may repeat in different alternatives), modifier groups `(?ims-ims:…)`, back
references (`\1`, `\k<name>`), lookahead and lookbehind (positive and negative; a lookbehind
matches backward, §22.2.2.4), `^`, `$`, `\b`, `\B`, `.`, classes with ranges and the escapes
`\d \D \w \W \s \S`, the character escapes of §22.2.1 (`\n \r \t \v \f \0 \cX \xHH \uHHHH
\u{H}`), identity escapes, the property escapes `\p{…}` and `\P{…}` with `u` or `v`
(§22.2.2.9: General_Category, Script and Script_Extensions by any of their value names, the
binary properties of ECMA-262's table, and with `v` the properties of strings; the data is
Unicode 17.0.0, the version of the Test262 tests at its pinned commit; any other name is a
SyntaxError), the class sets of `v` (nested classes, `&&`, `--`, `\q{…}`), and the Annex B forms
(`]` and `{` as characters when they start no quantifier). Flags: `d` (match indices), `g`,
`i`, `m`, `s`, `u`, `v`, `y`. With `u` or `v` the pattern and the subject are code points
(a surrogate pair is one character) and `i` compares by simple case folding; without them,
code units, and `i` compares by Canonicalize's upper case (§22.2.2.7.3).

A repetition of one character matcher (`.*`, `[a-z]+`, `\s*`) counts its matches in a
loop and then tries the continuation from the longest, so a long run does not nest one
call per character.
-/

namespace L4Factoidal.JS.Re

inductive ClassItem where
  | ch (c : Char)
  | range (lo hi : Char)
  /-- `\d` (0), `\w` (1), `\s` (2), negated when `neg`. -/
  | esc (kind : Nat) (neg : Bool)
  /-- `\p{…}` (`\P{…}` when `neg`): the code points of sorted, disjoint ranges. -/
  | prop (ranges : Array (Nat × Nat)) (neg : Bool)
  deriving Inhabited, Repr

inductive Node where
  | empty
  | char (c : Char)
  | any
  | cls (neg : Bool) (items : List ClassItem)
  | bol
  | eol
  | wordB (neg : Bool)
  | group (idx : Option Nat) (r : Node)
  | look (behind neg : Bool) (r : Node)
  | backref (n : Nat)
  /-- A back reference by name, resolved to its number after parsing. -/
  | named (name : String)
  | seq (rs : List Node)
  | alt (rs : List Node)
  | rep (r : Node) (min : Nat) (max : Option Nat) (greedy : Bool) (first : Nat)
  /-- A modifier group `(?add-rem:r)` (§22.2.2.3): the flags `i`, `m`, `s` set or cleared in `r`. -/
  | mods (add rem : List Char) (r : Node)
  /-- A class of the `v` flag: the code points whose Canonicalize is in the ranges (the ranges
  are already case folded under `i`). -/
  | vset (ranges : Array (Nat × Nat))
  /-- A back reference by a name that several groups share (in different alternatives): the
  one of them that took part in the match. -/
  | backrefAny (ks : List Nat)
  deriving Inhabited, Repr

structure Flags where
  global : Bool := false
  icase : Bool := false
  multiline : Bool := false
  dotAll : Bool := false
  /-- `u` or `v`: the pattern is matched as code points, with simple case folding under `i`. -/
  unicode : Bool := false
  sticky : Bool := false
  /-- `v` (unicodeSets). -/
  unicodeSets : Bool := false
  /-- `d` (hasIndices). -/
  hasIndices : Bool := false
  deriving Inhabited, Repr

/-- The flags of a flags string, or none for an unknown or repeated flag (§22.2.3.1). -/
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
  -- `u` and `v` together are a SyntaxError (§22.2.3.4 step 6)
  if f.unicode && f.unicodeSets then return none
  return some { f with unicode := f.unicode || f.unicodeSets }

/-- A compiled pattern: the tree, the number of capturing groups, their names. -/
structure Compiled where
  node : Node
  groups : Nat
  names : Array (String × Nat)
  flags : Flags
  deriving Inhabited

/-! ## Parsing (§22.2.1) -/

structure PS where
  pos : Nat := 0
  groups : Nat := 0
  names : Array (String × Nat) := #[]
  /-- The `u` flag: `\p{…}` is a property escape (else the identity escape `p`). -/
  unicode : Bool := false
  /-- The `v` flag: classes are class sets. -/
  sets : Bool := false
  /-- The `i` flag (class sets are case folded as they are read). -/
  icase : Bool := false
  /-- The pattern has a named group (then `\k` is always a named reference, §22.2.1.1). -/
  named : Bool := false

abbrev P := StateT PS (Except String)

/-! ### Property escapes (§22.2.2.9, UnicodeMatchProperty) -/

/-- Whether `c` is in the sorted, disjoint ranges `rs`: a binary search (at most 64 steps). -/
def inRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      let (a, b) := rs[mid]!
      if c < a then hi := mid
      else if c > b then lo := mid + 1
      else return true
  return false

/-- Sorted, merged ranges. -/
def rangesOf (rs : List (Nat × Nat)) : Array (Nat × Nat) :=
  (L4Factoidal.Text.CaseMap.normalizeRanges rs).toArray

/-- Ranges written as `RegexPropData` writes them: hexadecimal `lo` or `lo-hi`, comma-separated,
sorted and disjoint. -/
def rangesText (t : String) : Array (Nat × Nat) :=
  if t.isEmpty then #[] else
  (t.splitOn ",").toArray.map fun e =>
    match e.splitOn "-" with
    | [a, b] => (L4Factoidal.Regex.XPath40.hexNat a, L4Factoidal.Regex.XPath40.hexNat b)
    | _ => let a := L4Factoidal.Regex.XPath40.hexNat e; (a, a)

/-- The code points not in the sorted, disjoint ranges `rs` (of U+0000 to U+10FFFF). -/
def complementRanges (rs : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut next := 0
  for (a, b) in rs do
    if a > next then out := out.push (next, a - 1)
    next := b + 1
  if next ≤ 0x10FFFF then out := out.push (next, 0x10FFFF)
  return out

/-- The code points in both sorted, disjoint range lists. -/
def interRanges (a b : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:a.size + b.size] do
    if h : i < a.size then
      if h' : j < b.size then
        let (x1, y1) := a[i]
        let (x2, y2) := b[j]
        let lo := max x1 x2
        let hi := min y1 y2
        if lo ≤ hi then out := out.push (lo, hi)
        if y1 < y2 then i := i + 1 else j := j + 1
  return out

#guard interRanges #[(0, 10), (20, 30)] #[(5, 25)] = #[(5, 10), (20, 25)]

#guard complementRanges #[(0, 0x40), (0x5B, 0x10FFFF)] = #[(0x41, 0x5A)]
#guard complementRanges #[] = #[(0, 0x10FFFF)]
#guard rangesText "41-5A,61" = #[(0x41, 0x5A), (0x61, 0x61)]

open L4Factoidal.Unicode in
/-- The ranges of a General_Category value, by any of its names (PropertyValueAliases.txt):
the two-letter values from DerivedGeneralCategory.txt, the groups (L, LC, M, N, P, S, Z, C) as
their unions, Cn as the code points no other value has. -/
def gcRanges (name : String) : Option (Array (Nat × Nat)) :=
  match RegexPropData.gcAliases.find? (·.1 == name) with
  | none => none
  | some (_, short) =>
    let two (k : String) : List (Nat × Nat) :=
      ((RegexPropData.gc.find? (·.1 == k)).map (fun p => (rangesText p.2).toList)).getD []
    let assigned := fun (_ : Unit) => rangesOf (RegexPropData.gc.toList.flatMap fun p => (rangesText p.2).toList)
    if short == "Cn" then some (complementRanges (assigned ()))
    else if short == "C" then
      some (rangesOf ((complementRanges (assigned ())).toList ++ ["Cc", "Cf", "Cs", "Co"].flatMap two))
    else if short.length == 2 && short != "LC" then some (rangesOf (two short))
    else
      let parts := if short == "LC" then ["Lu", "Ll", "Lt"]
        else (RegexPropData.gc.toList.map (·.1)).filter (·.startsWith short)
      some (rangesOf (parts.flatMap two))

open L4Factoidal.Unicode in
/-- The ISO 15924 code of a Script value name (long name, code or other alias). -/
def scriptCode (name : String) : Option String :=
  (RegexPropData.scAliases.find? (·.1 == name)).map (·.2)

open L4Factoidal.Unicode in
/-- Script=`code` (ISO 15924): its code points; Unknown (Zzzz) is every code point of no script. -/
def scriptRanges (code : String) : Array (Nat × Nat) :=
  if code == "Zzzz" then
    complementRanges (rangesOf (RegexPropData.sc.toList.flatMap fun p => (rangesText p.2).toList))
  else ((RegexPropData.sc.find? (·.1 == code)).map (fun p => rangesText p.2)).getD #[]

open L4Factoidal.Unicode in
/-- Script_Extensions=`code` (§22.2.2.9 and UAX #24): the code points ScriptExtensions.txt lists
with `code`, and the code points of Script=`code` it does not list. -/
def scxRanges (code : String) : Array (Nat × Nat) :=
  let listed := rangesText RegexPropData.scxListed
  let own := (interRanges (scriptRanges code) (complementRanges listed)).toList
  let extra := ((RegexPropData.scx.find? (·.1 == code)).map (fun p => (rangesText p.2).toList)).getD []
  rangesOf (own ++ extra)

open L4Factoidal.Unicode in
/-- The code points of the property named `name` (`name` or `name=value`, §22.2.2.9
UnicodeMatchProperty and UnicodeMatchPropertyValue: names exactly as the tables of ECMA-262
spell them, no loose matching), or none for any other name (a SyntaxError). -/
def propertyRanges (name : String) : Option (Array (Nat × Nat)) :=
  match name.splitOn "=" with
  | [k, v] =>
    if k == "General_Category" || k == "gc" then gcRanges v
    else if k == "Script" || k == "sc" then (scriptCode v).map scriptRanges
    else if k == "Script_Extensions" || k == "scx" then (scriptCode v).map scxRanges
    else none
  | [k] =>
    match k with
    | "Any" => some #[(0, 0x10FFFF)]
    | "ASCII" => some #[(0, 0x7F)]
    | "Assigned" => (gcRanges "Cn").map complementRanges
    | _ =>
      match RegexPropData.binary.find? (fun (l, s, _) => l == k || (s.splitOn ",").contains k) with
      | some (_, _, t) => some (rangesText t)
      | none => gcRanges k
  | _ => none

#guard (propertyRanges "Script=Latin").isSome && (propertyRanges "sc=Latn").isSome
#guard (propertyRanges "Script_Extensions=Hira").isSome && (propertyRanges "Script=Foo").isNone
#guard (propertyRanges "ASCII=Y").isNone && (propertyRanges "General_Category").isNone
#guard (propertyRanges "Alphabetic").isSome && (propertyRanges "Alpha").isSome
#guard (propertyRanges "Other_Alphabetic").isNone && (propertyRanges "Block=Basic_Latin").isNone
#guard (propertyRanges "lu").isNone && (propertyRanges "Lu").isSome
#guard (propertyRanges "Cn").map (inRanges · 0x378) = some true
#guard (propertyRanges "Script_Extensions=Latn").map (inRanges · 0xB7) = some true
#guard (propertyRanges "Script=Latn").map (inRanges · 0xB7) = some false

section
variable (cs : Array Char)

def peekC : P (Option Char) := do pure cs[(← get).pos]?
def peekAt (k : Nat) : P (Option Char) := do pure cs[(← get).pos + k]?
def bump (k : Nat := 1) : P Unit := modify fun s => { s with pos := s.pos + k }

def hexDigits (start count : Nat) : Option Nat := Id.run do
  let mut v := 0
  for k in [0:count] do
    match cs[start + k]?.bind hexVal with
    | some d => v := v * 16 + d
    | none => return none
  return some v

/-- Decimal digits from `i`: the value and the index after them. -/
def decimal (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut v := 0
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c => if c.isDigit then v := v * 10 + (c.toNat - 48); j := j + 1 else break
    | none => break
  return if j == i then none else some (v, j)

/-- A quantifier at `i`: min, max, and the index after it (and after a lazy `?`). -/
def quantAt (i : Nat) : Option (Nat × Option Nat × Bool × Nat) :=
  let lazyAt := fun (j : Nat) => if cs[j]? == some '?' then (false, j + 1) else (true, j)
  match cs[i]? with
  | some '*' => let (g, j) := lazyAt (i + 1); some (0, none, g, j)
  | some '+' => let (g, j) := lazyAt (i + 1); some (1, none, g, j)
  | some '?' => let (g, j) := lazyAt (i + 1); some (0, some 1, g, j)
  | some '{' =>
    match decimal cs (i + 1) with
    | none => none
    | some (lo, j) =>
      match cs[j]? with
      | some '}' => let (g, k) := lazyAt (j + 1); some (lo, some lo, g, k)
      | some ',' =>
        if cs[j+1]? == some '}' then let (g, k) := lazyAt (j + 2); some (lo, none, g, k)
        else match decimal cs (j + 1) with
          | some (hi, k) => if cs[k]? == some '}' then let (g, k') := lazyAt (k + 1); some (lo, some hi, g, k') else none
          | none => none
      | _ => none
  | _ => none

/-- A character escape after `\` at `i` (not a class escape, not a back reference):
the character and the index after it. A lone surrogate is the character that holds it
(`Str.loneChar`); with `u` (`uni`) a pair of `\u` escapes is one character, and `\u{…}` is
an escape (§22.2.1 RegExpUnicodeEscapeSequence). -/
def charEscape (uni : Bool) (i : Nat) : Option (Char × Nat) :=
  match cs[i]? with
  | some 'n' => some ('\n', i + 1)
  | some 'r' => some ('\r', i + 1)
  | some 't' => some ('\t', i + 1)
  | some 'v' => some (Char.ofNat 11, i + 1)
  | some 'f' => some (Char.ofNat 12, i + 1)
  | some '0' => if (cs[i+1]?.map Char.isDigit) == some true then none else some (Char.ofNat 0, i + 1)
  | some 'c' =>
    match cs[i+1]? with
    | some l => if l.isAlpha then some (Char.ofNat (l.toNat % 32), i + 2) else some ('\\', i)
    | none => some ('\\', i)
  | some 'x' =>
    match hexDigits cs (i + 1) 2 with
    | some v => some (Char.ofNat v, i + 3)
    | none => some ('x', i + 1)
  | some 'u' =>
    if uni && cs[i+1]? == some '{' then
      let close := (List.range 8).find? fun k => cs[i + 2 + k]? == some '}'
      match close with
      | some k => if k == 0 then none else match hexDigits cs (i + 2) k with
        | some v => if v ≤ 0x10FFFF then some (Str.unitChar v, i + 3 + k) else none
        | none => none
      | none => some ('u', i + 1)
    else match hexDigits cs (i + 1) 4 with
      | some v =>
        -- A surrogate pair written as two escapes is one character.
        if uni && v ≥ 0xD800 && v ≤ 0xDBFF && cs[i+5]? == some '\\' && cs[i+6]? == some 'u' then
          match hexDigits cs (i + 7) 4 with
          | some lo => if lo ≥ 0xDC00 && lo ≤ 0xDFFF then
              some (Char.ofNat (0x10000 + (v - 0xD800) * 1024 + (lo - 0xDC00)), i + 11)
            else some (Str.unitChar v, i + 5)
          | none => some (Str.unitChar v, i + 5)
        else some (Str.unitChar v, i + 5)
      | none => some ('u', i + 1)
  | some c => some (c, i + 1)
  | none => none

/-- The Annex B reading of `\` and decimal digits that are not a back reference
(LegacyOctalEscapeSequence, else the digit itself): the characters they stand for. -/
def legacyDigits (ds : List Char) : List Char :=
  match ds with
  | d :: rest =>
    if d == '8' || d == '9' then d :: rest else
    -- up to three octal digits, at most 0o377
    let oct (c : Char) : Bool := '0' ≤ c && c ≤ '7'
    let take := if d ≤ '3' then 3 else 2
    let digits := (ds.take take).takeWhile oct
    let v := digits.foldl (fun a c => a * 8 + (c.toNat - 48)) 0
    Char.ofNat v :: ds.drop digits.length
  | [] => []

#guard legacyDigits "1".toList = [Char.ofNat 1] && legacyDigits "8".toList = ['8']
#guard legacyDigits "377".toList = [Char.ofNat 255] && legacyDigits "400".toList = [Char.ofNat 32, '0']

/-- IdentityEscape with `u` or `v` (§22.2.1): a SyntaxCharacter or `/`. -/
def identityOk (e : Char) : Bool := "^$\\.*+?()[]{}|/".contains e

def classEscapeKind : Char → Option (Nat × Bool)
  | 'd' => some (0, false) | 'D' => some (0, true)
  | 'w' => some (1, false) | 'W' => some (1, true)
  | 's' => some (2, false) | 'S' => some (2, true)
  | _ => none

/-- A property escape at `i` (`\p{…}` or `\P{…}`, with the `u` flag): its class item, with the
position moved past it; none when the text at `i` is not one. -/
def propEscape (i : Nat) : P (Option ClassItem) := do
  if !(← get).unicode || cs[i]? != some '\\' then return none
  let neg ← match cs[i+1]? with
    | some 'p' => pure false
    | some 'P' => pure true
    | _ => return none
  if cs[i+2]? != some '{' then throw "SyntaxError: Invalid regular expression: invalid property name"
  let close := (List.range 64).find? fun k => cs[i + 3 + k]? == some '}'
  match close with
  | none => throw "SyntaxError: Invalid regular expression: invalid property name"
  | some k =>
    let name := String.ofList (cs.extract (i + 3) (i + 3 + k)).toList
    match propertyRanges name with
    | some rs => modify (fun s => { s with pos := i + 4 + k }); return some (.prop rs neg)
    | none => throw s!"SyntaxError: Invalid regular expression: invalid property name '{name}'"

/-- The items of a class after `[` (and `^`), up to `]`. -/
def classItems : Nat → List ClassItem → P (List ClassItem)
  | 0, _ => throw "SyntaxError: Invalid regular expression: class too long"
  | fuel + 1, acc => do
    let some c ← peekC cs | throw "SyntaxError: Invalid regular expression: missing /"
    if c == ']' then bump; return acc.reverse
    let uni := (← get).unicode
    -- One class atom: a character or a class escape.
    let atom : P (Option Char ⊕ ClassItem) := do
      let i := (← get).pos
      if let some item ← propEscape cs i then return .inr item
      if c == '\\' then
        match cs[i+1]? with
        | some e =>
          match classEscapeKind e with
          | some (k, neg) => bump 2; return .inr (.esc k neg)
          | none =>
            if e == 'b' then bump 2; return .inl (some (Char.ofNat 8))
            else if e == '-' then bump 2; return .inl (some '-')
            else if !uni && e.isDigit && !(e == '0' && (cs[i+2]?.map Char.isDigit) != some true) then
              -- Annex B ClassEscape: a legacy octal escape (`\1` is U+0001), `\8` and `\9` themselves
              let ds := ((List.range 3).filterMap fun k => cs[i + 1 + k]?).takeWhile Char.isDigit
              match legacyDigits ds with
              | c :: rest => modify (fun s => { s with pos := i + 1 + (ds.length - rest.length) }); return .inl (some c)
              | [] => bump 2; return .inl (some e)
            else match charEscape cs uni (i + 1) with
              | some (ch, j) =>
                if uni && j == i + 2 && ch == e && !identityOk e then
                  throw "SyntaxError: Invalid regular expression: invalid escape"
                modify (fun s => { s with pos := j }); return .inl (some ch)
              | none =>
                if uni then throw "SyntaxError: Invalid regular expression: invalid escape"
                bump 2; return .inl (some e)
        | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
      else bump; return .inl (some c)
    let a ← atom
    match a with
    | .inr item =>
      -- with `u` or `v` a class escape cannot end a range (§22.2.1.1 early errors of
      -- NonemptyClassRanges); without, Annex B reads the `-` as a character
      let j := (← get).pos
      if uni && cs[j]? == some '-' && cs[j+1]? != some ']' && cs[j+1]?.isSome then
        throw "SyntaxError: Invalid regular expression: invalid character class range"
      classItems fuel (item :: acc)
    | .inl none => classItems fuel acc
    | .inl (some lo) =>
      let i := (← get).pos
      if cs[i]? == some '-' && cs[i+1]? != some ']' && cs[i+1]?.isSome then
        bump
        let c2 := (cs[i+1]?).getD ']'
        let b ← (do
          if let some item ← propEscape cs (i + 1) then return Sum.inr item
          if c2 == '\\' then
            match cs[i+2]? with
            | some e =>
              match classEscapeKind e with
              | some (k, neg) => bump 2; pure (Sum.inr (ClassItem.esc k neg))
              | none =>
                if e == 'b' then bump 2; pure (.inl (Char.ofNat 8))
                else if !uni && e.isDigit && !(e == '0' && (cs[i+3]?.map Char.isDigit) != some true) then
                  -- Annex B ClassEscape at the end of a range, as at its start (`[\240-\377]`,
                  -- Observable Plot's CSS class name pattern: issue 1161)
                  let ds := ((List.range 3).filterMap fun k => cs[i + 2 + k]?).takeWhile Char.isDigit
                  match legacyDigits ds with
                  | ch :: rest => modify (fun s => { s with pos := i + 2 + (ds.length - rest.length) }); pure (.inl ch)
                  | [] => bump 2; pure (.inl e)
                else match charEscape cs uni (i + 2) with
                  | some (ch, j) =>
                    if uni && j == i + 3 && ch == e && !identityOk e && e != '-' then
                      throw "SyntaxError: Invalid regular expression: invalid escape"
                    modify (fun s => { s with pos := j }); pure (.inl ch)
                  | none =>
                    if uni then throw "SyntaxError: Invalid regular expression: invalid escape"
                    bump 2; pure (.inl e)
            | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
          else do bump; pure (.inl c2) : P (Char ⊕ ClassItem))
        match b with
        | .inl hi =>
          if hi.toNat < lo.toNat then throw "SyntaxError: Invalid regular expression: range out of order in character class"
          classItems fuel (.range lo hi :: acc)
        | .inr item =>
          if uni then throw "SyntaxError: Invalid regular expression: invalid character class range"
          classItems fuel (item :: .ch '-' :: .ch lo :: acc)
      else classItems fuel (.ch lo :: acc)

/-! ### Class sets of the `v` flag (§22.2.1 ClassSetExpression, §22.2.2.9 CompileToCharSet) -/

/-- A class set: code point ranges (sorted, disjoint) and the strings of other lengths than one
(`\q{…}`, the properties of strings). -/
structure CSet where
  ranges : Array (Nat × Nat) := #[]
  strs : List (List Char) := []
  deriving Inhabited


def CSet.union (a b : CSet) : CSet :=
  { ranges := rangesOf (a.ranges.toList ++ b.ranges.toList), strs := a.strs ++ b.strs.filter (!a.strs.contains ·) }
def CSet.inter (a b : CSet) : CSet :=
  { ranges := interRanges a.ranges b.ranges, strs := a.strs.filter b.strs.contains }
def CSet.diff (a b : CSet) : CSet :=
  { ranges := interRanges a.ranges (complementRanges b.ranges), strs := a.strs.filter (!b.strs.contains ·) }

/-- One string of a class set as a set: a single character is a code point. -/
def CSet.ofStr (s : List Char) : CSet :=
  match s with
  | [c] => { ranges := #[(cpOf' c, cpOf' c)] }
  | _ => { strs := [s] }
where cpOf' (c : Char) : Nat := if Str.isLoneChar c then c.toNat - 0x10F000 + 0xD800 else c.toNat

/-- MaybeSimpleCaseFolding (§22.2.2.9.3) with `i`: each code point by its simple case folding (applied to each operand as it is read, so
complements are taken among folded code points)
(the code points case folding moves are taken out, their images put in). -/
def CSet.fold (a : CSet) : CSet := Id.run do
  let mut out : List (Nat × Nat) := []
  let mut moved : List (Nat × Nat) := []
  for (lo, hi) in a.ranges do
    for c in L4Factoidal.Text.CaseMap.affectedIn lo hi do
      let f := L4Factoidal.Text.CaseMap.caseFoldCp c
      if f != c then moved := (c, c) :: moved; out := (f, f) :: out
  let kept := interRanges a.ranges (complementRanges (rangesOf moved))
  let foldC (c : Char) : Char :=
    if Str.isLoneChar c then c else Char.ofNat (L4Factoidal.Text.CaseMap.caseFoldCp c.toNat)
  return { ranges := rangesOf (kept.toList ++ out), strs := a.strs.map (·.map foldC) }

open L4Factoidal.Unicode in
/-- A property of strings by name (with `v` only): RGI_Emoji is the union of the other six. -/
def stringProp (name : String) : Option CSet :=
  let one (p : String × String × String) : CSet :=
    { ranges := rangesText p.2.1,
      strs := (p.2.2.splitOn ";").filterMap fun seq =>
        if seq.isEmpty then none
        else some ((seq.splitOn " ").map fun h => Char.ofNat (L4Factoidal.Regex.XPath40.hexNat h)) }
  if name == "RGI_Emoji" then
    some (RegexPropData.stringProps.foldl (fun acc p => acc.union (one p)) {})
  else (RegexPropData.stringProps.find? (·.1 == name)).map one

/-- ClassSetSyntaxCharacter (§22.2.1): what a class set character may not be unescaped. -/
def setSyntax (c : Char) : Bool := "()[]{}/-\\|".contains c

/-- ClassSetReservedDoublePunctuator: a doubled one of these is reserved in a class set. -/
def setDoublePunct (c : Char) : Bool := "&!#$%*+,.:;<=>?@^`~".contains c

/-- ClassSetReservedPunctuator: may follow `\` in a class set. -/
def setPunct (c : Char) : Bool := "&-!#%,:;<=>@`~".contains c

/-- A ClassSetCharacter at the position: the character and the position after it, or none
when the text there is not one. -/
def setChar : P (Option Char) := do
  let i := (← get).pos
  let some c := cs[i]? | return none
  if c == '\\' then
    match cs[i+1]? with
    | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
    | some 'b' => bump 2; return some (Char.ofNat 8)
    | some e =>
      if setPunct e then bump 2; return some e
      if e.isAlphanum && (classEscapeKind e).isSome then return none
      if e == 'p' || e == 'P' || e == 'q' then return none
      match charEscape cs true (i + 1) with
      | some (ch, j) =>
        -- identity escapes with `u`/`v`: only the syntax characters and `/`
        if j == i + 2 && e == ch && !("^$\\.*+?()[]{}|/".contains e) then
          throw "SyntaxError: Invalid regular expression: invalid escape in a class set"
        modify (fun s => { s with pos := j }); return some ch
      | none => throw "SyntaxError: Invalid regular expression: invalid escape"
  if setSyntax c then return none
  if setDoublePunct c && cs[i+1]? == some c then
    throw "SyntaxError: Invalid regular expression: reserved double punctuator in a class set"
  bump; return some c

/-- `\q{…}` after the position of `\`: the strings of the disjunction. -/
def classStrings : P CSet := do
  bump 3
  let mut acc : CSet := {}
  let mut cur : List Char := []
  for _ in [0:cs.size] do
    match ← peekC cs with
    | some '}' => bump; return acc.union (CSet.ofStr cur.reverse)
    | some '|' => bump; acc := acc.union (CSet.ofStr cur.reverse); cur := []
    | some _ =>
      match ← setChar cs with
      | some c => cur := c :: cur
      | none => throw "SyntaxError: Invalid regular expression: invalid character in \\q{…}"
    | none => break
  throw "SyntaxError: Invalid regular expression: unterminated \\q{…}"

/-- A class escape in a class set at the position (`\d`, `\p{…}`, …) as a set, or none. -/
def setEscape : P (Option CSet) := do
  let i := (← get).pos
  if cs[i]? != some '\\' then return none
  match cs[i+1]? with
  | some 'q' =>
    if cs[i+2]? != some '{' then throw "SyntaxError: Invalid regular expression: invalid \\q"
    return some (← classStrings cs)
  | some e =>
    if e == 'p' || e == 'P' then
      -- a property of strings: only with `\p`
      if cs[i+2]? == some '{' then
        let close := (List.range 64).find? fun k => cs[i + 3 + k]? == some '}'
        if let some k := close then
          let name := String.ofList (cs.extract (i + 3) (i + 3 + k)).toList
          if let some set := stringProp name then
            if e == 'P' then throw "SyntaxError: Invalid regular expression: \\P of a property of strings"
            modify (fun s => { s with pos := i + 4 + k })
            return some set
      match ← propEscape cs i with
      | some (.prop rs neg) => return some { ranges := if neg then complementRanges rs else rs }
      | _ => throw "SyntaxError: Invalid regular expression: invalid property name"
    match classEscapeKind e with
    | some (k, neg) =>
      bump 2
      let base : Array (Nat × Nat) := match k with
        | 0 => #[(0x30, 0x39)]
        | 1 => #[(0x30, 0x39), (0x41, 0x5A), (0x5F, 0x5F), (0x61, 0x7A)]
        | _ => rangesOf ([(0x9,0xD),(0x20,0x20),(0xA0,0xA0),(0x1680,0x1680),(0x2000,0x200A),
                (0x2028,0x2029),(0x202F,0x202F),(0x205F,0x205F),(0x3000,0x3000),(0xFEFF,0xFEFF)])
      return some { ranges := if neg then complementRanges base else base }
    | none => return none
  | none => return none

/-- ClassSetExpression after `[` (and `^`), up to and past `]`: a union, an intersection
(`&&`) or a subtraction (`--`), never mixed; operands are characters, ranges (in a union),
escapes, `\q{…}` and nested classes. -/
def classSet : Nat → P CSet
  | 0 => throw "SyntaxError: Invalid regular expression: class too deep"
  | fuel + 1 => do
    -- one operand: a nested class, an escape, or a character (and maybe a range from it)
    let operand (allowRange : Bool) : P (CSet × Bool) := do
      let i := (← get).pos
      if cs[i]? == some '[' then
        bump
        let neg := (← peekC cs) == some '^'
        if neg then bump
        let s ← classSet fuel
        if neg then
          if !s.strs.isEmpty then throw "SyntaxError: Invalid regular expression: negated class with strings"
          return ({ ranges := complementRanges s.ranges }, false)
        return (s, false)
      let ic := (← get).icase
      let fold (x : CSet) : CSet := if ic then x.fold else x
      if let some s ← setEscape cs then return (fold s, false)
      match ← setChar cs with
      | none => throw "SyntaxError: Invalid regular expression: invalid class set operand"
      | some lo =>
        let j := (← get).pos
        if allowRange && cs[j]? == some '-' && cs[j+1]? != some '-' then
          bump
          match ← setChar cs with
          | some hi =>
            let a := CSet.ofStr.cpOf' lo
            let b := CSet.ofStr.cpOf' hi
            if b < a then throw "SyntaxError: Invalid regular expression: range out of order in character class"
            return (fold { ranges := #[(a, b)] }, true)
          | none => throw "SyntaxError: Invalid regular expression: invalid class set range"
        return (fold (CSet.ofStr [lo]), false)
    if (← peekC cs) == some ']' then bump; return {}
    let (first, wasRange) ← operand true
    let i := (← get).pos
    let op := if cs[i]? == some '&' && cs[i+1]? == some '&' then some '&'
      else if cs[i]? == some '-' && cs[i+1]? == some '-' then some '-' else none
    match op with
    | some o =>
      if wasRange then throw "SyntaxError: Invalid regular expression: a range in a set operation"
      let mut acc := first
      for _ in [0:cs.size] do
        let j := (← get).pos
        if cs[j]? == some ']' then bump; return acc
        if cs[j]? == some o && cs[j+1]? == some o then
          bump 2
          if o == '&' && cs[j+2]? == some '&' then throw "SyntaxError: Invalid regular expression: &&&"
          let (b, _) ← operand false
          acc := if o == '&' then acc.inter b else acc.diff b
        else throw "SyntaxError: Invalid regular expression: mixed set operations"
      throw "SyntaxError: Invalid regular expression: missing ]"
    | none =>
      let mut acc := first
      for _ in [0:cs.size] do
        let j := (← get).pos
        if cs[j]? == some ']' then bump; return acc
        if (cs[j]? == some '&' && cs[j+1]? == some '&') || (cs[j]? == some '-' && cs[j+1]? == some '-') then
          throw "SyntaxError: Invalid regular expression: mixed set operations"
        let (b, _) ← operand true
        acc := acc.union b
      throw "SyntaxError: Invalid regular expression: missing ]"

/-- A class set as a matcher node: its strings, longest first, then its code points, then the
empty string (§22.2.2.9 CompileAtom, CharacterClass with strings). -/
def CSet.toNode (s : CSet) : Node :=
  let cls := Node.vset s.ranges
  if s.strs.isEmpty then cls else
  -- longest first: by length buckets (no sort; the lengths are those of the strings themselves)
  let maxLen := s.strs.foldl (fun m w => max m w.length) 0
  let long := (List.range (maxLen + 1)).reverse.flatMap fun L =>
    if L > 1 then s.strs.filter (·.length == L) else []
  .alt (long.map (fun w => Node.seq (w.map Node.char)) ++ [cls] ++ (if s.strs.contains [] then [Node.empty] else []))

/-- A group name after `<`, up to `>`. -/
def groupName : P String := do
  -- RegExpIdentifierName (§22.2.1): IdentifierStartChar then IdentifierPartChars, each
  -- maybe written as `\uXXXX` (a pair of them for a supplementary character) or `\u{…}`
  let bad : P String := throw "SyntaxError: Invalid regular expression: invalid capture group name"
  let mut i := (← get).pos
  let mut out : Array Char := #[]
  for _ in [0:cs.size + 1] do
    match cs[i]? with
    | none => return ← bad
    | some '>' => break
    | some '\\' =>
      if cs[i+1]? != some 'u' then return ← bad
      match charEscape cs true (i + 1) with
      | some (c, j) => out := out.push c; i := j
      | none => return ← bad
    | some c =>
      -- a surrogate pair of code units (a pattern without `u`) is one code point
      if Str.isLoneChar c && c.toNat < 0x10F400 then
        match cs[i+1]? with
        | some d =>
          if Str.isLoneChar d && d.toNat ≥ 0x10F400 then
            out := out.push (Char.ofNat (0x10000 + (c.toNat - 0x10F000) * 1024 + (d.toNat - 0x10F400)))
            i := i + 2
            continue
        | none => pure ()
      out := out.push c
      i := i + 1
  if out.isEmpty then return ← bad
  for k in [0:out.size] do
    let c := out[k]!
    let ok := if c.toNat < 128 then c.isAlpha || c == '$' || c == '_' || (k > 0 && c.isDigit)
      else if k == 0 then inRanges ((propertyRanges "ID_Start").getD #[]) c.toNat
      else inRanges ((propertyRanges "ID_Continue").getD #[]) c.toNat || c.toNat == 0x200C || c.toNat == 0x200D
    if !ok then return ← bad
  modify fun s => { s with pos := i + 1 }
  return String.ofList out.toList

def closeP : P Unit := do
  if (← peekC cs) == some ')' then bump
  else throw "SyntaxError: Invalid regular expression: missing )"

mutual
def disjunction : Nat → P Node
  | 0 => throw "SyntaxError: Invalid regular expression: too deep"
  | fuel + 1 => do
    let first ← alternative fuel []
    let mut alts := #[first]
    for _ in [0:cs.size + 1] do
      if (← peekC cs) == some '|' then bump; alts := alts.push (← alternative fuel [])
      else break
    return if alts.size == 1 then first else .alt alts.toList

def alternative : Nat → List Node → P Node
  | 0, _ => throw "SyntaxError: Invalid regular expression: too long"
  | fuel + 1, acc => do
    match ← peekC cs with
    | none | some '|' | some ')' =>
      return match acc with | [] => .empty | [x] => x | xs => .seq xs.reverse
    | some _ =>
      let t ← term fuel
      alternative fuel (t :: acc)

def term : Nat → P Node
  | 0 => throw "SyntaxError: Invalid regular expression: too deep"
  | fuel + 1 => do
    let i := (← get).pos
    let some c ← peekC cs | return .empty
    -- Assertions (no quantifier, except lookaheads under Annex B).
    if c == '^' then bump; return .bol
    if c == '$' then bump; return .eol
    if c == '\\' && cs[i+1]? == some 'b' then bump 2; return .wordB false
    if c == '\\' && cs[i+1]? == some 'B' then bump 2; return .wordB true
    let firstGroup := (← get).groups
    let uniT := (← get).unicode
    let atom ← atomP fuel
    let j := (← get).pos
    match quantAt cs j with
    | some (lo, hi, greedy, k) =>
      match atom with
      | .look true _ _ => throw "SyntaxError: Invalid regular expression: nothing to repeat"
      | .look false _ _ =>
        -- a lookahead is quantifiable only without `u` or `v` (Annex B QuantifiableAssertion)
        if uniT then throw "SyntaxError: Invalid regular expression: nothing to repeat"
        modify fun s => { s with pos := k }
        return .rep atom lo hi greedy firstGroup
      | .bol | .eol | .wordB _ => throw "SyntaxError: Invalid regular expression: nothing to repeat"
      | _ =>
        if let some h := hi then
          if h < lo then throw "SyntaxError: Invalid regular expression: numbers out of order in {} quantifier"
        modify fun s => { s with pos := k }
        return .rep atom lo hi greedy firstGroup
    | none =>
      if j < cs.size && (cs[j]! == '*' || cs[j]! == '+' || cs[j]! == '?') then
        throw "SyntaxError: Invalid regular expression: nothing to repeat"
      return atom

def atomP : Nat → P Node
  | 0 => throw "SyntaxError: Invalid regular expression: too deep"
  | fuel + 1 => do
    let i := (← get).pos
    let some c ← peekC cs | throw "SyntaxError: Invalid regular expression: unexpected end"
    let uni := (← get).unicode
    let ic := (← get).icase
    let named := (← get).named
    match c with
    | '.' => bump; return .any
    | '[' =>
      bump
      let neg := (← peekC cs) == some '^'
      if neg then bump
      if (← get).sets then
        let s ← classSet cs (cs.size + 1)
        if neg then
          if !s.strs.isEmpty then throw "SyntaxError: Invalid regular expression: negated class with strings"
          return .vset (complementRanges s.ranges)
        return s.toNode
      return .cls neg (← classItems cs (cs.size + 1) [])
    | '(' =>
      if cs[i+1]? == some '?' then
        match cs[i+2]? with
        | some ':' => bump 3; let r ← disjunction fuel; closeP cs; return .group none r
        | some '=' => bump 3; let r ← disjunction fuel; closeP cs; return .look false false r
        | some '!' => bump 3; let r ← disjunction fuel; closeP cs; return .look false true r
        | some '<' =>
          if cs[i+3]? == some '=' || cs[i+3]? == some '!' then
            let neg := cs[i+3]? == some '!'
            bump 4
            let r ← disjunction fuel
            closeP cs
            return .look true neg r
          else
            bump 3
            let name ← groupName cs
            let idx := (← get).groups + 1
            modify fun s => { s with groups := idx, names := s.names.push (name, idx) }
            let r ← disjunction fuel; closeP cs
            return .group (some idx) r
        | some m =>
          -- a modifier group `(?ims-ims:…)` (§22.2.1 RegularExpressionModifiers and its early
          -- errors: only i, m, s; none twice; not both empty)
          if m != '-' && !"ims".contains m then throw "SyntaxError: Invalid regular expression: invalid group"
          let mut j := i + 2
          let mut add : List Char := []
          let mut rem : List Char := []
          let mut dash := false
          for _ in [0:8] do
            match cs[j]? with
            | some '-' =>
              if dash then throw "SyntaxError: Invalid regular expression: invalid group"
              dash := true; j := j + 1
            | some c =>
              if "ims".contains c then
                if add.contains c || rem.contains c then
                  throw "SyntaxError: Invalid regular expression: repeated flag in a modifier group"
                if dash then rem := c :: rem else add := c :: add
                j := j + 1
              else break
            | none => break
          if cs[j]? != some ':' || (dash && add.isEmpty && rem.isEmpty) then
            throw "SyntaxError: Invalid regular expression: invalid group"
          modify fun s => { s with pos := j + 1 }
          let r ← disjunction fuel; closeP cs
          return .mods add rem r
        | none => throw "SyntaxError: Invalid regular expression: invalid group"
      else
        bump
        let idx := (← get).groups + 1
        modify fun s => { s with groups := idx }
        let r ← disjunction fuel; closeP cs
        return .group (some idx) r
    | ')' => throw "SyntaxError: Invalid regular expression: unmatched ')'"
    | '*' | '+' | '?' => throw "SyntaxError: Invalid regular expression: nothing to repeat"
    | '{' =>
      if (quantAt cs i).isSome then throw "SyntaxError: Invalid regular expression: nothing to repeat"
      if uni then throw "SyntaxError: Invalid regular expression: lone quantifier brackets"
      bump; return .char '{'
    | '\\' =>
      if (← get).sets && (cs[i+1]? == some 'p' || cs[i+1]? == some 'P') then
        if let some s ← setEscape cs then
          return (if ic then s.fold else s).toNode
      if let some item ← propEscape cs i then return .cls false [item]
      match cs[i+1]? with
      | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
      | some e =>
        match classEscapeKind e with
        | some (k, neg) => bump 2; return .cls false [.esc k neg]
        | none =>
          if e.isDigit && e != '0' then
            match decimal cs (i + 1) with
            | some (v, j) => modify (fun s => { s with pos := j }); return .backref v
            | none => bump 2; return .char e
          else if e == 'k' && (uni || named) then
            -- `\k` is a back reference by name with `u`/`v` or when the pattern has named
            -- groups; otherwise (Annex B) the identity escape `k`
            if cs[i+2]? != some '<' then throw "SyntaxError: Invalid regular expression: invalid named reference"
            bump 3
            return .named (← groupName cs)
          else match charEscape cs uni (i + 1) with
            | some (ch, j) =>
              if uni && j ≤ i + 1 then throw "SyntaxError: Invalid regular expression: invalid escape"
              -- with `u` or `v` an identity escape is only of a syntax character or `/`
              if uni && j == i + 2 && ch == e && !identityOk e then
                throw "SyntaxError: Invalid regular expression: invalid escape"
              modify (fun s => { s with pos := j }); return .char ch
            | none =>
              if uni then throw "SyntaxError: Invalid regular expression: invalid escape"
              bump 2; return .char e
    | c =>
      -- a lone `]` or `}` is a character only without `u` or `v` (Annex B ExtendedPatternCharacter)
      if uni && (c == ']' || c == '}') then throw "SyntaxError: Invalid regular expression: lone quantifier brackets"
      bump; return .char c

end

end

/-- Whether a pattern (its characters) has a named group `(?<name>`. -/
def hasNamedGroup (cs : Array Char) : Bool := Id.run do
  let mut esc := false
  let mut cls := false
  for i in [0:cs.size] do
    let c := cs[i]!
    if esc then
      esc := false
    else if c == '\\' then
      esc := true
    else if cls then
      cls := c != ']'
    else if c == '[' then
      cls := true
    else if c == '(' && cs[i+1]? == some '?' && cs[i+2]? == some '<' &&
        cs[i+3]? != some '=' && cs[i+3]? != some '!' then
      return true
  return false

#guard hasNamedGroup "(?<a>x)".toList.toArray && !hasNamedGroup "(?<=a)\\(?<b>".toList.toArray

/-- The back reference numbers and names of a parsed pattern. -/
def refsOf : Nat → Node → List Nat × List String
  | 0, _ => ([], [])
  | fuel + 1, n => match n with
    | .backref k => ([k], [])
    | .named nm => ([], [nm])
    | .group _ r | .look _ _ r | .mods _ _ r | .rep r .. => refsOf fuel r
    | .seq rs | .alt rs => rs.foldl (fun (a, b) r => let (c, d) := refsOf fuel r; (a ++ c, b ++ d)) ([], [])
    | _ => ([], [])

/-- Back references by name to their numbers; a number past the groups is the
legacy escape of Annex B (`\1` with no group is U+0001, `\8` the character `8`). -/
def resolve (names : Array (String × Nat)) (groups : Nat) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n => match n with
    | .named name => match (names.filter (·.1 == name)).toList with
      | [] => .empty
      | [(_, k)] => .backref k
      | ps => .backrefAny (ps.map (·.2))
    | .backref k =>
      if k > groups then
        match legacyDigits (toString k).toList with
        | [c] => .char c
        | cs => .seq (cs.map Node.char)
      else .backref k
    | .group idx r => .group idx (resolve names groups fuel r)
    | .look b neg r => .look b neg (resolve names groups fuel r)
    | .seq rs => .seq (rs.map (resolve names groups fuel))
    | .alt rs => .alt (rs.map (resolve names groups fuel))
    | .rep r lo hi g f => .rep (resolve names groups fuel r) lo hi g f
    | .mods a b r => .mods a b (resolve names groups fuel r)
    | n => n

/-- The group names a node may capture in one match, or an error when two groups of one name
can both take part in a match (§22.2.1.1 early errors: duplicate names only in different
alternatives). `nameOf k` is the name of group `k`, if it has one. -/
def namesIn (nameOf : Nat → Option String) : Nat → Node → Except String (List String)
  | 0, _ => .ok []
  | fuel + 1, n => match n with
    | .group (some k) r => do
      let inner ← namesIn nameOf fuel r
      match nameOf k with
      | some nm =>
        if inner.contains nm then throw "SyntaxError: Invalid regular expression: duplicate capture group name"
        pure (nm :: inner)
      | none => pure inner
    | .group none r | .look _ _ r | .mods _ _ r | .rep r .. => namesIn nameOf fuel r
    | .seq rs => rs.foldlM (init := []) fun acc r => do
      let ns ← namesIn nameOf fuel r
      if ns.any acc.contains then throw "SyntaxError: Invalid regular expression: duplicate capture group name"
      pure (acc ++ ns)
    | .alt rs => rs.foldlM (init := []) fun acc r => do
      let ns ← namesIn nameOf fuel r
      pure (acc ++ ns.filter (!acc.contains ·))
    | _ => .ok []

/-- EscapeRegExpPattern (§22.2.6.13.1): the source text of a RegExp, written so that `/source/`
reads back as the same pattern: a `/` outside a class and line terminators escaped. -/
def escapeSource (src : String) : String := Id.run do
  let mut out := ""
  let mut esc := false
  let mut cls := false
  for c in src.toList do
    let lt := c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029
    let name := if c == '\n' then "n" else if c == '\r' then "r"
      else if c.toNat == 0x2028 then "u2028" else "u2029"
    if esc then
      out := out ++ (if lt then name else String.singleton c)
      esc := false
    else if lt then out := out ++ "\\" ++ name
    else if c == '\\' then out := out.push c; esc := true
    else if c == '/' && !cls then out := out ++ "\\/"
    else
      if c == '[' then cls := true else if c == ']' then cls := false
      out := out.push c
  return out

#guard escapeSource "a/b" = "a\\/b" && escapeSource "[/]" = "[/]" && escapeSource "\\/" = "\\/"
#guard escapeSource "a\nb" = "a\\nb"

/-- Compile a pattern with its flags (§22.2.3.4 RegExpInitialize): an error message
that starts with `SyntaxError:` when the pattern or the flags are not valid. -/
def compile (pattern flags : String) : Except String Compiled := do
  let some fl := parseFlags flags | throw s!"SyntaxError: Invalid regular expression flags '{flags}'"
  -- Without u or v the pattern is code units (a supplementary character is its two
  -- surrogates); with them, code points (§22.2.3.4 steps 9 and 10).
  let cs := if fl.unicode then pattern.toList.toArray else Str.unitChars pattern
  let (node, st) ← (disjunction cs (4 * cs.size + 16)).run { unicode := fl.unicode, sets := fl.unicodeSets, icase := fl.icase, named := hasNamedGroup cs }
  if st.pos < cs.size then
    throw (if cs[st.pos]! == ')' then "SyntaxError: Invalid regular expression: unmatched ')'"
      else "SyntaxError: Invalid regular expression")
  -- early errors: with `u`/`v` a back reference past the groups, and with `u`/`v` or named
  -- groups a `\k<name>` of no group (§22.2.1.1)
  let refs := refsOf (cs.size + 2) node
  if fl.unicode && refs.1.any (· > st.groups) then
    throw "SyntaxError: Invalid regular expression: invalid back reference"
  if (fl.unicode || !st.names.isEmpty) && refs.2.any (fun nm => !st.names.any (·.1 == nm)) then
    throw "SyntaxError: Invalid regular expression: invalid named reference"
  let nameOf (k : Nat) : Option String := (st.names.find? (·.2 == k)).map (·.1)
  if st.names.size > 1 then
    let _ ← namesIn nameOf (cs.size + 2) node
  return { node := resolve st.names st.groups (cs.size + 2) node, groups := st.groups, names := st.names, flags := fl }

/-! ## Matching (§22.2.2) -/

structure St where
  pos : Nat
  /-- Capture `k` (1-based) at index `k - 1`: start and end. -/
  caps : Array (Option (Nat × Nat))
  deriving Inhabited

/-- The code point a subject or pattern character stands for: the characters U+10F000 to
U+10F7FF hold lone surrogate units (`Str.loneChar`), any other character is itself. -/
def cpOf (c : Char) : Nat := if Str.isLoneChar c then c.toNat - 0x10F000 + 0xD800 else c.toNat

/-- Canonicalize (§22.2.2.7.3): without `i` the character; with `i` and `u` or `v` its simple
case folding (CaseFolding.txt, statuses C and S); with `i` alone its uppercase when that is one
code unit, unless it would take a character from outside ASCII into ASCII. -/
def canon (fl : Flags) (c : Char) : Char :=
  if !fl.icase then c else
  let n := c.toNat
  if n < 128 then
    if fl.unicode then (if 65 ≤ n && n ≤ 90 then Char.ofNat (n + 32) else c)
    else (if 97 ≤ n && n ≤ 122 then Char.ofNat (n - 32) else c)
  else if Str.isLoneChar c then c
  else if fl.unicode then Char.ofNat (L4Factoidal.Text.CaseMap.caseFoldCp n)
  else match L4Factoidal.Text.CaseMap.fullUpper n with
    | [u] => if u ≥ 0x10000 || u < 128 then c else Char.ofNat u
    | _ => c

#guard canon { icase := true } 'a' = 'A' && canon { icase := true, unicode := true } 'A' = 'a'
#guard canon { icase := true } (Char.ofNat 0x17F) = Char.ofNat 0x17F
#guard canon { icase := true, unicode := true } (Char.ofNat 0x212A) = 'k'
#guard canon { icase := true } (Char.ofNat 0xE9) = Char.ofNat 0xC9

def eqChar (fl : Flags) (a b : Char) : Bool := a == b || (fl.icase && canon fl a == canon fl b)

/-- WordCharacters (§22.2.2.9.4): `[A-Za-z0-9_]`, and with `u` (or `v`) and `i` the characters
whose case folding is one of them (U+017F and U+212A). -/
def isWordChar (fl : Flags) (c : Char) : Bool :=
  c.isAlphanum || c == '_' ||
    (fl.icase && fl.unicode && (c.toNat == 0x17F || c.toNat == 0x212A))

def isSpace (c : Char) : Bool := isWs c || isLineTerm c

/-- Whether character `c`, code point `cp`, is in the set of one class item (without case
folding). `cp` is `cpOf c` but for a surrogate pair read as one character with `u`: a code point
from U+10F000 to U+10F7FF is then itself, not the lone unit its character holds elsewhere. -/
def itemHas (fl : Flags) (c : Char) (cp : Nat) : ClassItem → Bool
  | .ch x => cpOf x == cp
  | .range lo hi => cpOf lo ≤ cp && cp ≤ cpOf hi
  | .esc k neg =>
    let r := match k with | 0 => c.isDigit | 1 => isWordChar fl c | _ => isSpace c
    if neg then !r else r
  | .prop rs neg => inRanges rs cp != neg

/-- The characters `d` with `canon d = canon c` (c among them): what a class is searched for
under `i` (CharacterSetMatcher, §22.2.2.7.1 step 4: some member whose Canonicalize is c's). -/
def caseCands (fl : Flags) (c : Char) : List Char :=
  if !fl.icase || Str.isLoneChar c then [c] else
  let k := canon fl c
  let vs := (L4Factoidal.Text.CaseMap.caseVariants c.toNat).filterMap fun v =>
    if v == c.toNat || v ≥ 0x110000 || (0xD800 ≤ v && v < 0xE000) then none
    else let d := Char.ofNat v; if canon fl d == k then some d else none
  c :: vs

/-- Whether one character (`c`, code point `cp`, as for `itemHas`) matches a node that is a
single character matcher. -/
def oneChar (fl : Flags) (n : Node) (c : Char) (cp : Nat := cpOf c) : Option Bool :=
  let plain := cp == cpOf c
  match n with
  | .char x => some (cpOf x == cp || (plain && fl.icase && canon fl c == canon fl x))
  | .any => some (fl.dotAll || !isLineTerm c)
  | .vset rs => some (inRanges rs (if plain then cpOf (canon fl c) else cp))
  | .cls neg items =>
    if !fl.icase || !plain then some (items.any (itemHas fl c cp) != neg)
    else
      let ds := caseCands fl c
      some (items.any (fun it => ds.any (fun d => itemHas fl d (cpOf d) it)) != neg)
  | _ => none

def setCap (st : St) (k : Nat) (v : Option (Nat × Nat)) : St :=
  { st with caps := if k ≥ 1 && k ≤ st.caps.size then st.caps.set! (k - 1) v else st.caps }

/-- The capture numbers `first + 1 ..` up to the groups counted at the end of the
atom: reset at each repetition (RepeatMatcher step 4). -/
def clearFrom (st : St) (first : Nat) (count : Nat) : St := Id.run do
  let mut caps := st.caps
  for k in [first:first + count] do
    if k < caps.size then caps := caps.set! k none
  return { st with caps }

/-- The number of capturing groups in a node. -/
def groupCount : Nat → Node → Nat
  | 0, _ => 0
  | fuel + 1, n => match n with
    | .group (some _) r => 1 + groupCount fuel r
    | .group none r | .look _ _ r | .mods _ _ r => groupCount fuel r
    | .rep r .. => groupCount fuel r
    | .seq rs | .alt rs => rs.foldl (fun a r => a + groupCount fuel r) 0
    | _ => 0

/-- The flags inside a modifier group `(?add-rem:…)` (§22.2.2.3 UpdateModifiers). -/
def applyMods (fl : Flags) (add rem : List Char) : Flags :=
  let on (c : Char) (cur : Bool) := if add.contains c then true else if rem.contains c then false else cur
  { fl with icase := on 'i' fl.icase, multiline := on 'm' fl.multiline, dotAll := on 's' fl.dotAll }

section
variable (cs : Array Char)

/-- The character read at `pos` going forward (`back` false) or the one before `pos` going
backward, and how many code units it is: with `u` or `v` a surrogate pair is one character
(§22.2.2: the pattern is matched against the list of code points).

Inlined: every caller matches on the answer at once, so the compiler removes the `some` and the
pair, and a character read allocates nothing (`docs/bubblepopjs-heap.md`, step 6). -/
@[inline] def readAt (uni back : Bool) (pos : Nat) : Option (Char × Nat) :=
  if !back then
    if h : pos < cs.size then
      let c := cs[pos]
      if uni && 0x10F000 ≤ c.toNat && c.toNat < 0x10F400 then
        match cs[pos + 1]? with
        | some d =>
          if 0x10F400 ≤ d.toNat && d.toNat < 0x10F800 then
            some (Char.ofNat (0x10000 + (c.toNat - 0x10F000) * 1024 + (d.toNat - 0x10F400)), 2)
          else some (c, 1)
        | none => some (c, 1)
      else some (c, 1)
    else none
  else
    if pos == 0 then none else
    let d := cs[pos - 1]!
    if uni && pos ≥ 2 && 0x10F400 ≤ d.toNat && d.toNat < 0x10F800 then
      let c := cs[pos - 2]!
      if 0x10F000 ≤ c.toNat && c.toNat < 0x10F400 then
        some (Char.ofNat (0x10000 + (c.toNat - 0x10F000) * 1024 + (d.toNat - 0x10F400)), 2)
      else some (d, 1)
    else some (d, 1)

def atWordBoundary (fl : Flags) (pos : Nat) : Bool :=
  let a := pos > 0 && isWordChar fl cs[pos - 1]!
  let b := pos < cs.size && isWordChar fl cs[pos]!
  a != b

/-- The code point of a character `readAt` read as `w` units: a pair is its code point, a single
unit is `cpOf` (a lone surrogate's character stands for the unit). -/
def cpRead (c : Char) (w : Nat) : Nat := if w == 2 then c.toNat else cpOf c

/-- One step of a single character matcher from `pos`: the position after it. Inlined, as `readAt`. -/
@[inline] def step1 (fl : Flags) (back : Bool) (n : Node) (pos : Nat) : Option Nat :=
  match readAt cs fl.unicode back pos with
  | some (c, w) => if oneChar fl n c (cpRead c w) == some true then some (if back then pos - w else pos + w) else none
  | none => none

/-- The longest run of characters matching a single character node from `pos` (forward, one
code unit each), at most `limit`. -/
def runLength (fl : Flags) (n : Node) (pos limit : Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:limit] do
    if pos + k < cs.size && oneChar fl n cs[pos + k]! == some true then k := k + 1 else break
  return k

/-- The positions after 0, 1, 2, … matches of a single character node from `pos`, at most
`limit` matches (any direction, characters of any width). -/
def runEnds (fl : Flags) (back : Bool) (n : Node) (pos limit : Nat) : Array Nat := Id.run do
  let mut ends := #[pos]
  let mut p := pos
  for _ in [0:limit] do
    match step1 cs fl back n p with
    | some q => ends := ends.push q; p := q
    | none => break
  return ends

/-- Try the continuation at each count from `hi` down to `lo` (greedy) or up (lazy). -/
def tryCounts (pos : Nat) (st : St) (k : St → Option St) (lo hi : Nat) (greedy : Bool) : Option St := Id.run do
  for t in [0:hi - lo + 1] do
    let c := if greedy then hi - t else lo + t
    match k { st with pos := pos + c } with
    | some r => return some r
    | none => pure ()
  return none

/-- As `tryCounts`, at the positions `ends[lo]` to `ends[ends.size - 1]`. -/
def tryEnds (ends : Array Nat) (st : St) (k : St → Option St) (lo : Nat) (greedy : Bool) : Option St := Id.run do
  let hi := ends.size - 1
  for t in [0:hi - lo + 1] do
    let c := if greedy then hi - t else lo + t
    match k { st with pos := ends[c]! } with
    | some r => return some r
    | none => pure ()
  return none

/-- The matcher of a node (§22.2.2 CompilePattern), in direction `back` (forward, or backward
inside a lookbehind, §22.2.2.4), with the flags in force there (`fl`, changed by modifier
groups). -/
def matchNode : Nat → Flags → Bool → Node → St → (St → Option St) → Option St
  | 0, _, _, _, _, _ => none
  | fuel + 1, fl, back, node, st, k =>
    match node with
    | .empty => k st
    | .char _ | .any | .cls .. | .vset _ =>
      match step1 cs fl back node st.pos with
      | some p => k { st with pos := p }
      | none => none
    | .bol =>
      if st.pos == 0 || (fl.multiline && isLineTerm cs[st.pos - 1]!) then k st else none
    | .eol =>
      if st.pos == cs.size || (fl.multiline && st.pos < cs.size && isLineTerm cs[st.pos]!) then k st else none
    | .wordB neg => if atWordBoundary cs fl st.pos != neg then k st else none
    | .group none r => matchNode fuel fl back r st k
    | .mods add rem r => matchNode fuel (applyMods fl add rem) back r st k
    | .group (some idx) r =>
      let start := st.pos
      matchNode fuel fl back r st fun st' =>
        k (setCap st' idx (some (if back then (st'.pos, start) else (start, st'.pos))))
    | .look behind neg r =>
      let r' := matchNode fuel fl behind r st some
      if neg then (if r'.isNone then k st else none)
      else match r' with
        | some st' => k { st with caps := st'.caps }
        | none => none
    | .backref idx =>
      match st.caps[idx - 1]?.join with
      | none => k st
      | some (a, b) =>
        let len := b - a
        if back then
          if len ≤ st.pos && (List.range len).all (fun t => eqChar fl cs[a + t]! cs[st.pos - len + t]!) then
            k { st with pos := st.pos - len }
          else none
        else if st.pos + len ≤ cs.size && (List.range len).all (fun t => eqChar fl cs[a + t]! cs[st.pos + t]!) then
          k { st with pos := st.pos + len }
        else none
    | .named _ => k st
    | .backrefAny ks =>
      match ks.find? (fun j => (st.caps[j - 1]?.join).isSome) with
      | some j => matchNode fuel fl back (.backref j) st k
      | none => k st
    | .seq [] => k st
    | .seq (r :: rs) =>
      if back then
        -- backward: the last term first (§22.2.2.3, Alternative with direction backward)
        match rs.getLast? with
        | none => matchNode fuel fl back r st k
        | some l => matchNode fuel fl back l st fun st' => matchNode fuel fl back (.seq (r :: rs.dropLast)) st' k
      else
        match r with
        | .char _ | .any | .cls .. | .vset _ =>
          -- a single character first: the continuation for the rest is made only when it
          -- matches, so a start position that fails on its first character makes no closure
          -- (`matchNode_seq` in `RegexTheorems.lean`: the same answer as the general rule below)
          match step1 cs fl back r st.pos with
          | some p => matchNode fuel fl back (.seq rs) { st with pos := p } k
          | none => none
        -- an assertion first (`^`, `$`, `\b`): the same, so a pattern anchored with `^` that is
        -- tried at a later start position fails with no closure made
        | .bol =>
          if st.pos == 0 || (fl.multiline && isLineTerm cs[st.pos - 1]!) then matchNode fuel fl back (.seq rs) st k
          else none
        | .eol =>
          if st.pos == cs.size || (fl.multiline && st.pos < cs.size && isLineTerm cs[st.pos]!) then
            matchNode fuel fl back (.seq rs) st k
          else none
        | .wordB neg => if atWordBoundary cs fl st.pos != neg then matchNode fuel fl back (.seq rs) st k else none
        | _ => matchNode fuel fl back r st fun st' => matchNode fuel fl back (.seq rs) st' k
    | .alt [] => none
    | .alt (r :: rs) =>
      match matchNode fuel fl back r st k with
      | some x => some x
      | none => matchNode fuel fl back (.alt rs) st k
    | .rep r lo hi greedy first =>
      match r with
      | .char _ | .any | .cls .. | .vset _ =>
        if !fl.unicode && !back then
          let limit := match hi with | some h => h | none => cs.size - st.pos
          let run := runLength cs fl r st.pos limit
          if run < lo then none else tryCounts st.pos st k lo run greedy
        else
          let limit := match hi with | some h => h | none => cs.size
          let ends := runEnds cs fl back r st.pos limit
          if ends.size ≤ lo then none else tryEnds ends st k lo greedy
      | _ =>
        let count := groupCount 1000 r
        let st0 := clearFrom st first count
        if lo > 0 then
          matchNode fuel fl back r st0 fun st' => matchNode fuel fl back (.rep r (lo - 1) (hi.map (· - 1)) greedy first) st' k
        else if hi == some 0 then k st
        else
          let once := fun (_ : Unit) => matchNode fuel fl back r st0 fun st' =>
            if st'.pos == st.pos then none else matchNode fuel fl back (.rep r 0 (hi.map (· - 1)) greedy first) st' k
          if greedy then
            match once () with
            | some x => some x
            | none => k st
          else
            match k st with
            | some x => some x
            | none => once ()
end

/-- Fuel of one match attempt: the nesting the continuations may reach. -/
def matchFuel (n : Nat) : Nat := 64 * n + 4096

/-- RegExpBuiltinExec's search (§22.2.7.2): the first match at `from` or after (only at
`from` when sticky). The match start and the captures, capture 0 the whole match. -/
def exec (re : Compiled) (cs : Array Char) (from_ : Nat) : Option (Array (Option (Nat × Nat))) := Id.run do
  if from_ > cs.size then return none
  let fuel := matchFuel cs.size
  let init : St := { pos := 0, caps := Array.replicate re.groups none }
  let mut start := from_
  for _ in [0:cs.size - from_ + 1] do
    match matchNode cs fuel re.flags false re.node { init with pos := start } some with
    | some st => return some (#[some (start, st.pos)] ++ st.caps)
    | none => if re.flags.sticky then return none
    -- the next start: past a surrogate pair at once with u or v (AdvanceStringIndex)
    match readAt cs re.flags.unicode false start with
    | some (_, w) => start := start + w
    | none => return none
  return none

/-! ### The search as a recursion

`exec` is the reference: a `for` over the start positions with the start in a mutable variable.
Compiled, each position made the loop's state pair, its step, and the matcher's state record with
the captures array built again (61% of the allocations of the marked workload were in that loop).
`execFast` is the same search as a recursion on the count of positions left, with the empty
captures made once (`exec_eq_fast`); the compiled program runs `execFastA` below, which also stops
an anchored search at once. -/

/-- The search of `exec` from `start`, for `k` more start positions. -/
def execLoop (re : Compiled) (cs : Array Char) (fuel : Nat) (caps0 : Array (Option (Nat × Nat))) :
    Nat → Nat → Option (Array (Option (Nat × Nat)))
  | 0, _ => none
  | k + 1, start =>
    match matchNode cs fuel re.flags false re.node { pos := start, caps := caps0 } some with
    | some st => some (#[some (start, st.pos)] ++ st.caps)
    | none =>
      if re.flags.sticky then none else
      match readAt cs re.flags.unicode false start with
      | some (_, w) => execLoop re cs fuel caps0 k (start + w)
      | none => none

/-- `exec`, by `execLoop`. -/
def execFast (re : Compiled) (cs : Array Char) (from_ : Nat) : Option (Array (Option (Nat × Nat))) :=
  if from_ > cs.size then none
  else execLoop re cs (matchFuel cs.size) (Array.replicate re.groups none) (cs.size - from_ + 1) from_

/-- **Kind: refinement.** `execFast` gives the match `exec` gives (or none), for every compiled
expression, subject and start. Does not say anything about speed. -/
theorem exec_eq_fast : @exec = @execFast := by
  funext re cs from_
  unfold exec execFast
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · rfl
  · rename_i hfrom
    have hsz : [:cs.size - from_ + 1].size = cs.size - from_ + 1 := by simp [Std.Legacy.Range.size]
    rw [hsz]
    clear hfrom hsz
    generalize cs.size - from_ + 1 = m
    generalize hl : List.range' 0 m = l
    have hlen : m = l.length := by rw [← hl, List.length_range']
    rw [hlen]
    clear hlen hl
    generalize from_ = start
    induction l generalizing start with
    | nil => rfl
    | cons a as ih =>
      simp only [List.forIn_cons, List.length_cons, execLoop]
      cases hm : matchNode cs (matchFuel cs.size) re.flags false re.node
          { pos := start, caps := Array.replicate re.groups none } some with
      | some st => rfl
      | none =>
        by_cases hs : re.flags.sticky = true
        · rw [if_pos hs, if_pos hs]; rfl
        · rw [if_neg hs, if_neg hs]
          cases hr : readAt cs re.flags.unicode false start with
          | none => rfl
          | some p =>
            obtain ⟨c, w⟩ := p
            exact ih (start + w)

#print axioms exec_eq_fast

/-! ### A pattern anchored with `^`

A pattern that starts with `^`, with `m` not set, can match only at position 0. The search tried
every later start position all the same: each made the matcher's state record and failed at the
assertion (the whole length of the subject for each failed test of an anchored pattern, which is
how a tokeniser uses them: the marked workload made 3.0 M state records this way).
`execLoopA` stops at the first start position past 0 when the pattern is anchored. -/

/-- The pattern can match only at position 0: it starts with `^` and `m` is not set. -/
def anchoredStart (fl : Flags) (node : Node) : Bool :=
  !fl.multiline && match node with
    | .bol => true
    | .seq (.bol :: _) => true
    | _ => false

/-- An anchored pattern does not match at a position past 0, whatever the continuation. -/
theorem matchNode_anchored (cs : Array Char) (fl : Flags) (node : Node) (h : anchoredStart fl node = true)
    (fuel pos : Nat) (caps : Array (Option (Nat × Nat))) (k : St → Option St) (hpos : pos ≠ 0) :
    matchNode cs (fuel + 1) fl false node { pos := pos, caps := caps } k = none := by
  unfold anchoredStart at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hm, hn⟩ := h
  rw [matchNode.eq_def]
  cases node with
  | bol => simp [hpos, hm]
  | seq rs =>
    cases rs with
    | nil => simp at hn
    | cons r rs =>
      cases r with
      | bol => simp [hpos, hm]
      | _ => simp at hn
  | _ => simp at hn

/-- A search that starts past position 0 finds nothing when the pattern is anchored. -/
theorem execLoop_anchored (re : Compiled) (cs : Array Char) (fuel : Nat) (caps0 : Array (Option (Nat × Nat)))
    (h : anchoredStart re.flags re.node = true) :
    ∀ (k start : Nat), start ≠ 0 → execLoop re cs (fuel + 1) caps0 k start = none := by
  intro k
  induction k with
  | zero => intro start _; rfl
  | succ k ih =>
    intro start hs
    rw [execLoop, matchNode_anchored cs re.flags re.node h fuel start caps0 some hs]
    by_cases hst : re.flags.sticky = true
    · simp only [hst, if_true]
    · simp only [hst, if_false]
      cases hr : readAt cs re.flags.unicode false start with
      | none => rfl
      | some p =>
        obtain ⟨c, w⟩ := p
        exact ih (start + w) (by omega)

/-- The search of `execLoop`, stopped at the first start position past 0 when the pattern is
anchored (`anch`): one test for each position. -/
def execLoopA (re : Compiled) (cs : Array Char) (fuel : Nat) (caps0 : Array (Option (Nat × Nat))) (anch : Bool) :
    Nat → Nat → Option (Array (Option (Nat × Nat)))
  | 0, _ => none
  | k + 1, start =>
    if anch && start != 0 then none else
    match matchNode cs fuel re.flags false re.node { pos := start, caps := caps0 } some with
    | some st => some (#[some (start, st.pos)] ++ st.caps)
    | none =>
      if re.flags.sticky then none else
      match readAt cs re.flags.unicode false start with
      | some (_, w) => execLoopA re cs fuel caps0 anch k (start + w)
      | none => none

/-- `execLoopA` with the pattern's own `anchoredStart` is `execLoop`, for every count and start. -/
theorem execLoopA_eq (re : Compiled) (cs : Array Char) (fuel : Nat) (caps0 : Array (Option (Nat × Nat))) :
    ∀ (k start : Nat), execLoopA re cs (fuel + 1) caps0 (anchoredStart re.flags re.node) k start
      = execLoop re cs (fuel + 1) caps0 k start := by
  intro k
  induction k with
  | zero => intro start; rfl
  | succ k ih =>
    intro start
    rw [execLoopA]
    by_cases hc : (anchoredStart re.flags re.node && start != 0) = true
    · simp only [hc, if_true]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact (execLoop_anchored re cs fuel caps0 hc.1 (k + 1) start hc.2).symm
    · simp only [hc]
      rw [execLoop]
      cases hm : matchNode cs (fuel + 1) re.flags false re.node { pos := start, caps := caps0 } some with
      | some st => rfl
      | none =>
        by_cases hst : re.flags.sticky = true
        · simp [hst]
        · simp only [hst, if_false]
          cases hr : readAt cs re.flags.unicode false start with
          | none => rfl
          | some p =>
            obtain ⟨c, w⟩ := p
            exact ih (start + w)

/-- `exec`, by `execLoopA`. -/
def execFastA (re : Compiled) (cs : Array Char) (from_ : Nat) : Option (Array (Option (Nat × Nat))) :=
  if from_ > cs.size then none
  else execLoopA re cs (matchFuel cs.size) (Array.replicate re.groups none) (anchoredStart re.flags re.node)
    (cs.size - from_ + 1) from_

/-- **Kind: refinement.** `execFastA` gives the match `exec` gives (or none), for every compiled
expression, subject and start. Does not say anything about speed. -/
@[csimp] theorem exec_eq_fastA : @exec = @execFastA := by
  rw [exec_eq_fast]
  funext re cs from_
  unfold execFast execFastA
  have hf : matchFuel cs.size = (64 * cs.size + 4095) + 1 := rfl
  rw [hf, execLoopA_eq]

#print axioms matchNode_anchored
#print axioms exec_eq_fastA

end L4Factoidal.JS.Re
