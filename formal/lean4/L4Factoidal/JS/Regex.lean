import L4Factoidal.JS.Lexer
import L4Factoidal.Regex.XPath40
import L4Factoidal.Unicode.ScriptData
import L4Factoidal.Unicode.EmojiData

/-!
# L4Factoidal.JS.Regex — regular expressions of the engine (§22.2)

A backtracking matcher in the shape of §22.2.2 (Pattern Semantics): each node is a
Matcher that takes a state (the end index and the captures) and a continuation, and
answers the final state or failure. Every function takes fuel and passes a smaller one
to each recursive call, so all of it is total.

Supported: alternatives, sequences, the quantifiers `*`, `+`, `?`, `{n}`, `{n,}`,
`{n,m}` (greedy and lazy, with the empty check of RepeatMatcher step 2.b and the reset
of the captures inside the atom at each repetition), capturing, non-capturing and named
groups, back references (`\1`, `\k<name>`), lookahead and lookbehind (positive and
negative), `^`, `$`, `\b`, `\B`, `.`, classes with ranges and the escapes `\d \D \w \W
\s \S`, the character escapes of §22.2.1 (`\n \r \t \v \f \0 \cX \xHH \uHHHH \u{H}`),
identity escapes, the property escapes `\p{…}` and `\P{…}` with the `u` flag (§22.2.2.9:
General_Category values by short or long name, `Script=` by ISO 15924 code, the binary
properties `Any`, `ASCII`, `ASCII_Hex_Digit`, `ID_Start`, `ID_Continue`, `White_Space` and the
emoji properties of UTS #51 but `Extended_Pictographic`; any other name is a SyntaxError), and the Annex B forms (`]` and `{` as characters when they start no
quantifier). Flags: `g`, `i`, `m`, `s`, `u`, `y` (`d` and `v` are accepted and do not
change matching). Characters are Unicode scalar values, as the engine's strings are
(design record, section 7); `i` compares by simple case mapping of each character.

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
  deriving Inhabited, Repr

structure Flags where
  global : Bool := false
  icase : Bool := false
  multiline : Bool := false
  dotAll : Bool := false
  unicode : Bool := false
  sticky : Bool := false
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
    | 'd' | 'v' => pure ()
    | _ => return none
  return some f

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

/-- The General_Category values by long name (PropertyValueAliases.txt), to their short names. -/
def gcLong : List (String × String) :=
  [("Letter","L"),("Cased_Letter","LC"),("Uppercase_Letter","Lu"),("Lowercase_Letter","Ll"),
   ("Titlecase_Letter","Lt"),("Modifier_Letter","Lm"),("Other_Letter","Lo"),("Mark","M"),
   ("Combining_Mark","M"),("Nonspacing_Mark","Mn"),("Spacing_Mark","Mc"),("Enclosing_Mark","Me"),
   ("Number","N"),("Decimal_Number","Nd"),("digit","Nd"),("Letter_Number","Nl"),("Other_Number","No"),
   ("Punctuation","P"),("punct","P"),("Connector_Punctuation","Pc"),("Dash_Punctuation","Pd"),
   ("Open_Punctuation","Ps"),("Close_Punctuation","Pe"),("Initial_Punctuation","Pi"),
   ("Final_Punctuation","Pf"),("Other_Punctuation","Po"),("Symbol","S"),("Math_Symbol","Sm"),
   ("Currency_Symbol","Sc"),("Modifier_Symbol","Sk"),("Other_Symbol","So"),("Separator","Z"),
   ("Space_Separator","Zs"),("Line_Separator","Zl"),("Paragraph_Separator","Zp"),("Other","C"),
   ("Control","Cc"),("cntrl","Cc"),("Format","Cf"),("Surrogate","Cs"),("Private_Use","Co"),
   ("Unassigned","Cn")]

/-- The ranges of a General_Category value, by short or long name. -/
def gcRanges (name : String) : Option (List (Nat × Nat)) :=
  let short := ((gcLong.find? (·.1 == name)).map (·.2)).getD name
  if short == "LC" then
    some (["Lu","Ll","Lt"].flatMap fun k => (L4Factoidal.Regex.XPath40.categoryRanges k).getD [])
  else if short == "Cs" then some [(0xD800, 0xDFFF)]
  else if short.length ≤ 2 && short.all Char.isAlpha && (short.get 0).isUpper then
    L4Factoidal.Regex.XPath40.categoryRanges short
  else none

/-- ID_Start (DerivedCoreProperties.txt): L, Nl and Other_ID_Start, without Pattern_Syntax and
Pattern_White_Space (of these only U+2E2F is a letter). -/
def idStart : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ =>
  let base := ((gcRanges "L").getD []) ++ ((gcRanges "Nl").getD []) ++
    [(0x1885,0x1886),(0x2118,0x2118),(0x212E,0x212E),(0x309B,0x309C)]
  rangesOf (base.flatMap fun (a, b) =>
    if a ≤ 0x2E2F && 0x2E2F ≤ b then [(a, 0x2E2E), (0x2E30, b)] else [(a, b)])

/-- ID_Continue: ID_Start, Mn, Mc, Nd, Pc and Other_ID_Continue (Unicode 16: with U+200C,
U+200D, U+30FB and U+FF65). -/
def idContinue : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ =>
  rangesOf (idStart.get.toList ++ (["Mn","Mc","Nd","Pc"].flatMap fun k => (gcRanges k).getD []) ++
    [(0xB7,0xB7),(0x387,0x387),(0x1369,0x1371),(0x19DA,0x19DA),(0x200C,0x200D),(0x30FB,0x30FB),(0xFF65,0xFF65)])

/-- `lo hi v;` hexadecimal rows of a range table text, with their values. -/
def tableRows (text : String) : List (Nat × Nat × Nat) :=
  (text.splitOn ";").filterMap fun row =>
    match row.splitOn " " with
    | [a, b, v] => match v.toNat? with
      | some n => some (L4Factoidal.Regex.XPath40.hexNat a, L4Factoidal.Regex.XPath40.hexNat b, n)
      | none => none
    | _ => none

/-- The ranges of the rows whose value `test` takes. -/
def tableRanges (text : String) (test : Nat → Bool) : List (Nat × Nat) :=
  (tableRows text).filterMap fun (a, b, v) => if test v then some (a, b) else none

/-- The code points of the property named `name` (`name` or `name=value`), or none for a name
that is not one of the supported properties (a SyntaxError). -/
def propertyRanges (name : String) : Option (Array (Nat × Nat)) :=
  match name.splitOn "=" with
  | [k, v] =>
    if k == "General_Category" || k == "gc" then (gcRanges v).map rangesOf
    else if k == "Script" || k == "sc" then
      match L4Factoidal.Unicode.ScriptData.codes.findIdx? (· == v) with
      | some i => if i == 0 then none else some (rangesOf (tableRanges L4Factoidal.Unicode.ScriptData.tableText (· == i)))
      | none => none
    else none
  | [k] =>
    match k with
    | "Any" => some #[(0, 0x10FFFF)]
    | "ASCII" => some #[(0, 0x7F)]
    | "ASCII_Hex_Digit" | "AHex" => some #[(0x30,0x39),(0x41,0x46),(0x61,0x66)]
    | "ID_Start" | "IDS" => some idStart.get
    | "ID_Continue" | "IDC" => some idContinue.get
    | "White_Space" | "space" => some (rangesOf [(0x9,0xD),(0x20,0x20),(0x85,0x85),(0xA0,0xA0),(0x1680,0x1680),
        (0x2000,0x200A),(0x2028,0x2029),(0x202F,0x202F),(0x205F,0x205F),(0x3000,0x3000)])
    | "Emoji" => some (rangesOf (tableRanges L4Factoidal.Unicode.EmojiData.emojiText fun v => v &&& 16 != 0))
    | "Emoji_Presentation" | "EPres" => some (rangesOf (tableRanges L4Factoidal.Unicode.EmojiData.emojiText fun v => v &&& 1 != 0))
    | "Emoji_Modifier" | "EMod" => some (rangesOf (tableRanges L4Factoidal.Unicode.EmojiData.emojiText fun v => v &&& 2 != 0))
    | "Emoji_Modifier_Base" | "EBase" => some (rangesOf (tableRanges L4Factoidal.Unicode.EmojiData.emojiText fun v => v &&& 4 != 0))
    | "Emoji_Component" | "EComp" => some (rangesOf (tableRanges L4Factoidal.Unicode.EmojiData.emojiText fun v => v &&& 8 != 0))
    | _ => (gcRanges k).map rangesOf
  | _ => none

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
the character and the index after it. -/
def charEscape (i : Nat) : Option (Char × Nat) :=
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
    if cs[i+1]? == some '{' then
      let close := (List.range 8).find? fun k => cs[i + 2 + k]? == some '}'
      match close with
      | some k => match hexDigits cs (i + 2) k with
        | some v => if v ≤ 0x10FFFF then some (Char.ofNat v, i + 3 + k) else none
        | none => none
      | none => some ('u', i + 1)
    else match hexDigits cs (i + 1) 4 with
      | some v =>
        -- A surrogate pair written as two escapes is one character.
        if v ≥ 0xD800 && v ≤ 0xDBFF && cs[i+5]? == some '\\' && cs[i+6]? == some 'u' then
          match hexDigits cs (i + 7) 4 with
          | some lo => if lo ≥ 0xDC00 && lo ≤ 0xDFFF then
              some (Char.ofNat (0x10000 + (v - 0xD800) * 1024 + (lo - 0xDC00)), i + 11)
            else some (Char.ofNat 0xFFFD, i + 5)
          | none => some (Char.ofNat 0xFFFD, i + 5)
        else if v ≥ 0xD800 && v ≤ 0xDFFF then some (Char.ofNat 0xFFFD, i + 5)
        else some (Char.ofNat v, i + 5)
      | none => some ('u', i + 1)
  | some c => some (c, i + 1)
  | none => none

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
            else match charEscape cs (i + 1) with
              | some (ch, j) => modify (fun s => { s with pos := j }); return .inl (some ch)
              | none => bump 2; return .inl (some e)
        | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
      else bump; return .inl (some c)
    let a ← atom
    match a with
    | .inr item => classItems fuel (item :: acc)
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
                else match charEscape cs (i + 2) with
                  | some (ch, j) => modify (fun s => { s with pos := j }); pure (.inl ch)
                  | none => bump 2; pure (.inl e)
            | none => throw "SyntaxError: Invalid regular expression: \\ at end of pattern"
          else do bump; pure (.inl c2) : P (Char ⊕ ClassItem))
        match b with
        | .inl hi =>
          if hi.toNat < lo.toNat then throw "SyntaxError: Invalid regular expression: range out of order in character class"
          classItems fuel (.range lo hi :: acc)
        | .inr item => classItems fuel (item :: .ch '-' :: .ch lo :: acc)
      else classItems fuel (.ch lo :: acc)

/-- A group name after `<`, up to `>`. -/
def groupName : P String := do
  let i := (← get).pos
  let close := (List.range 64).find? fun k => cs[i + k]? == some '>'
  match close with
  | some k =>
    let name := String.ofList (cs.extract i (i + k)).toList
    if name.isEmpty then throw "SyntaxError: Invalid regular expression: invalid capture group name"
    modify fun s => { s with pos := i + k + 1 }
    return name
  | none => throw "SyntaxError: Invalid regular expression: invalid capture group name"

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
    let atom ← atomP fuel
    let j := (← get).pos
    match quantAt cs j with
    | some (lo, hi, greedy, k) =>
      match atom with
      | .look true _ _ => throw "SyntaxError: Invalid regular expression: nothing to repeat"
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
    match c with
    | '.' => bump; return .any
    | '[' =>
      bump
      let neg := (← peekC cs) == some '^'
      if neg then bump
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
        | _ => throw "SyntaxError: Invalid regular expression: invalid group"
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
      bump; return .char '{'
    | '\\' =>
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
          else if e == 'k' && cs[i+2]? == some '<' then
            bump 3
            return .named (← groupName cs)
          else match charEscape cs (i + 1) with
            | some (ch, j) => modify (fun s => { s with pos := j }); return .char ch
            | none => bump 2; return .char e
    | c => bump; return .char c

end

end

/-- Back references by name to their numbers; a number past the groups is the
character escape of Annex B (an octal-like `\8` is the character `8`). -/
def resolve (names : Array (String × Nat)) (groups : Nat) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n => match n with
    | .named name => match names.find? (·.1 == name) with
      | some (_, k) => .backref k
      | none => .empty
    | .backref k => if k > groups then .char (Char.ofNat (48 + k % 10)) else .backref k
    | .group idx r => .group idx (resolve names groups fuel r)
    | .look b neg r => .look b neg (resolve names groups fuel r)
    | .seq rs => .seq (rs.map (resolve names groups fuel))
    | .alt rs => .alt (rs.map (resolve names groups fuel))
    | .rep r lo hi g f => .rep (resolve names groups fuel r) lo hi g f
    | n => n

/-- Compile a pattern with its flags (§22.2.3.4 RegExpInitialize): an error message
that starts with `SyntaxError:` when the pattern or the flags are not valid. -/
def compile (pattern flags : String) : Except String Compiled := do
  let some fl := parseFlags flags | throw s!"SyntaxError: Invalid regular expression flags '{flags}'"
  let cs := pattern.toList.toArray
  let (node, st) ← (disjunction cs (4 * cs.size + 16)).run { unicode := fl.unicode }
  if st.pos < cs.size then
    throw (if cs[st.pos]! == ')' then "SyntaxError: Invalid regular expression: unmatched ')'"
      else "SyntaxError: Invalid regular expression")
  return { node := resolve st.names st.groups (cs.size + 2) node, groups := st.groups, names := st.names, flags := fl }

/-! ## Matching (§22.2.2) -/

structure St where
  pos : Nat
  /-- Capture `k` (1-based) at index `k - 1`: start and end. -/
  caps : Array (Option (Nat × Nat))
  deriving Inhabited

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def isSpace (c : Char) : Bool := isWs c || isLineTerm c

/-- Simple case folding of one character (Canonicalize, §22.2.2.7.3, by lower case). -/
def fold (c : Char) : Char :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then Char.ofNat (n + 32)
  else if (0xC0 ≤ n && n ≤ 0xDE && n != 0xD7) then Char.ofNat (n + 32)
  else if 0x391 ≤ n && n ≤ 0x3A9 && n != 0x3A2 then Char.ofNat (n + 32)
  else if 0x410 ≤ n && n ≤ 0x42F then Char.ofNat (n + 32)
  else c

def eqChar (icase : Bool) (a b : Char) : Bool := a == b || (icase && fold a == fold b)

def itemMatches (icase : Bool) (c : Char) : ClassItem → Bool
  | .ch x => eqChar icase c x
  | .range lo hi =>
    (lo ≤ c && c ≤ hi) || (icase && (let f := fold c; (lo ≤ f && f ≤ hi) ||
      List.any [c.toUpper, c.toLower] fun d => lo ≤ d && d ≤ hi))
  | .esc k neg =>
    let r := match k with | 0 => c.isDigit | 1 => isWordChar c | _ => isSpace c
    if neg then !r else r
  | .prop rs neg =>
    let r := inRanges rs c.toNat ||
      (icase && List.any [fold c, c.toUpper, c.toLower] fun d => inRanges rs d.toNat)
    if neg then !r else r

/-- Whether one character matches a node that is a single character matcher. -/
def oneChar (fl : Flags) (n : Node) (c : Char) : Option Bool :=
  match n with
  | .char x => some (eqChar fl.icase c x)
  | .any => some (fl.dotAll || !isLineTerm c)
  | .cls neg items => some (items.any (itemMatches fl.icase c) != neg)
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
    | .group none r | .look _ _ r => groupCount fuel r
    | .rep r .. => groupCount fuel r
    | .seq rs | .alt rs => rs.foldl (fun a r => a + groupCount fuel r) 0
    | _ => 0

section
variable (cs : Array Char) (fl : Flags)

def atWordBoundary (pos : Nat) : Bool :=
  let a := pos > 0 && isWordChar cs[pos - 1]!
  let b := pos < cs.size && isWordChar cs[pos]!
  a != b

/-- The longest run of characters matching a single character node from `pos`, at most
`limit`. -/
def runLength (n : Node) (pos limit : Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:limit] do
    if pos + k < cs.size && oneChar fl n cs[pos + k]! == some true then k := k + 1 else break
  return k

/-- Try the continuation at each count from `hi` down to `lo` (greedy) or up (lazy). -/
def tryCounts (pos : Nat) (st : St) (k : St → Option St) (lo hi : Nat) (greedy : Bool) : Option St := Id.run do
  for t in [0:hi - lo + 1] do
    let c := if greedy then hi - t else lo + t
    match k { st with pos := pos + c } with
    | some r => return some r
    | none => pure ()
  return none

def matchNode : Nat → Node → St → (St → Option St) → Option St
  | 0, _, _, _ => none
  | fuel + 1, node, st, k =>
    match node with
    | .empty => k st
    | .char _ | .any | .cls .. =>
      if h : st.pos < cs.size then
        if oneChar fl node cs[st.pos] == some true then k { st with pos := st.pos + 1 } else none
      else none
    | .bol =>
      if st.pos == 0 || (fl.multiline && isLineTerm cs[st.pos - 1]!) then k st else none
    | .eol =>
      if st.pos == cs.size || (fl.multiline && st.pos < cs.size && isLineTerm cs[st.pos]!) then k st else none
    | .wordB neg => if atWordBoundary cs st.pos != neg then k st else none
    | .group none r => matchNode fuel r st k
    | .group (some idx) r =>
      let start := st.pos
      matchNode fuel r st fun st' => k (setCap st' idx (some (start, st'.pos)))
    | .look false neg r =>
      let r' := matchNode fuel r st some
      if neg then (if r'.isNone then k st else none)
      else match r' with
        | some st' => k { st with caps := st'.caps }
        | none => none
    | .look true neg r =>
      -- Lookbehind: some start before the position whose match ends here.
      let found := (List.range (st.pos + 1)).findSome? fun d =>
        matchNode fuel r { st with pos := st.pos - d } fun st' => if st'.pos == st.pos then some st' else none
      if neg then (if found.isNone then k st else none)
      else match found with
        | some st' => k { st with caps := st'.caps }
        | none => none
    | .backref idx =>
      match st.caps[idx - 1]?.join with
      | none => k st
      | some (a, b) =>
        let len := b - a
        if st.pos + len ≤ cs.size && (List.range len).all (fun t => eqChar fl.icase cs[a + t]! cs[st.pos + t]!) then
          k { st with pos := st.pos + len }
        else none
    | .named _ => k st
    | .seq [] => k st
    | .seq (r :: rs) => matchNode fuel r st fun st' => matchNode fuel (.seq rs) st' k
    | .alt [] => none
    | .alt (r :: rs) =>
      match matchNode fuel r st k with
      | some x => some x
      | none => matchNode fuel (.alt rs) st k
    | .rep r lo hi greedy first =>
      match r with
      | .char _ | .any | .cls .. =>
        let limit := match hi with | some h => h | none => cs.size - st.pos
        let run := runLength cs fl r st.pos limit
        if run < lo then none else tryCounts st.pos st k lo run greedy
      | _ =>
        let count := groupCount 1000 r
        let st0 := clearFrom st first count
        if lo > 0 then
          matchNode fuel r st0 fun st' => matchNode fuel (.rep r (lo - 1) (hi.map (· - 1)) greedy first) st' k
        else if hi == some 0 then k st
        else
          let once := fun (_ : Unit) => matchNode fuel r st0 fun st' =>
            if st'.pos == st.pos then none else matchNode fuel (.rep r 0 (hi.map (· - 1)) greedy first) st' k
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
  for d in [0:cs.size - from_ + 1] do
    let start := from_ + d
    match matchNode cs re.flags fuel re.node { init with pos := start } some with
    | some st => return some (#[some (start, st.pos)] ++ st.caps)
    | none => if re.flags.sticky then return none
  return none

end L4Factoidal.JS.Re
