/-
L4Factoidal.DOM.Selectors — Selectors Level 4 on the DOM arena, for `querySelector`,
`querySelectorAll`, `matches` and `closest` (DOM §4.2.6 "scope-match a selectors string").

Specification: Selectors Level 4 (W3C Working Draft, 2022-11-11, and the editor's draft of
2026-11), CSS Syntax Level 3 §4 for the tokens (identifiers with escapes, strings), HTML
§4.16 for the pseudo-classes whose meaning HTML defines (`:link`, `:checked`,
`:disabled`, `:enabled`) and HTML §4.16.2 for the attribute values that match ASCII
case-insensitively in HTML documents.

Parsed: type and universal selectors with a namespace prefix (`*|`, `|`; a declared
prefix is a SyntaxError, as `querySelector` has no namespace map), `#id`, `.class`,
attribute selectors (`=`, `~=`, `|=`, `^=`, `$=`, `*=`, the `i` and `s` flags, a namespace
prefix), the structural pseudo-classes (`:root`, `:empty`, `:first-child`, `:last-child`,
`:only-child`, `:first-of-type`, `:last-of-type`, `:only-of-type`, `:nth-child(An+B [of S])`,
`:nth-last-child`, `:nth-of-type`, `:nth-last-of-type`), `:not()`, `:is()`, `:where()`,
`:scope`, `:lang()`, `:link`, `:any-link`, `:checked`, `:disabled`, `:enabled`, the
pseudo-classes of user state (`:hover`, `:active`, `:focus`, `:focus-within`,
`:focus-visible`, `:visited`, `:target`), which match nothing here, the pseudo-elements
`::before`, `::after`, `::first-line`, `::first-letter` (also with one colon), which never
match an element, and the four combinators. Anything else is a SyntaxError.

Matching walks up the tree from the subject, with a fuel bound of the arena size for each
walk. It recurses once per compound of a complex selector (at most `maxCompounds`) and once
per nesting level of `:not()`/`:is()` (at most `maxNesting`); nothing here recurses once per
node of the document. The parser and the matcher are total: each takes fuel (`parseFuel`,
`matchFuel`) that these bounds never exhaust.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.DOM.CustomElements
import L4Factoidal.HTML.Dimension
import L4Factoidal.Unicode.Bidi

namespace L4Factoidal.DOM.Selectors
open L4Factoidal.DOM

/-- A namespace prefix of a type or attribute selector. -/
inductive NsSel where
  /-- no prefix: any namespace for a type selector, no namespace for an attribute -/
  | default
  /-- `*|` -/
  | any
  /-- `|` -/
  | none
  deriving BEq, Repr, Inhabited

inductive AttrOp where
  | present | eq | includes | dash | pre | suf | sub
  deriving BEq, Repr, Inhabited

/-- `:nth-child` and friends: which one, and `An+B`. -/
inductive NthKind where
  | child | lastChild | ofType | lastOfType
  deriving BEq, Repr, Inhabited

mutual
inductive Simple where
  /-- a type selector (`name := none` is `*`) -/
  | type (ns : NsSel) (name : Option String)
  | id (v : String)
  | cls (v : String)
  /-- `[ns|name op value flag]`; `ci` for the `i` flag, `cs` for the `s` flag -/
  | attr (ns : NsSel) (name : String) (op : AttrOp) (value : String) (ci cs : Bool)
  /-- a pseudo-class without argument -/
  | pseudo (name : String)
  | nth (kind : NthKind) (a b : Int) (of : Option (List Complex))
  | not (sels : List Complex)
  | is (sels : List Complex)
  /-- `:has(<relative-selector-list>)`: each relative selector is a complex selector
  whose first compound carries the relative combinator (' ' when none is written),
  matched against the elements after the anchor in that relation -/
  | has (sels : List Complex)
  | lang (ranges : List String)
  /-- the elements, in ascending order, where the `:has()` of a compound was found to hold:
  what the cascade puts in its place once it has looked at the whole document
  (`Rendering.CSS.resolveHas`), so that matching does not search again for each element -/
  | anchors (ids : Array Nat)
  /-- a pseudo-element: never the subject -/
  | never

/-- A complex selector: compounds from left to right, each after its combinator
(' ', '>', '+', '~'; the first one's is ' '). -/
inductive Complex where
  | mk (parts : List (Char × List Simple))
end

instance : Inhabited Simple := ⟨.never⟩
instance : Inhabited Complex := ⟨.mk []⟩

/-! ## Tokens (CSS Syntax §4.3) -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n'
def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10
def nameStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat ≥ 0x80
def nameChar (c : Char) : Bool := nameStart c || c.isDigit || c == '-'

/-- The input after CSS Syntax §3.3 preprocessing (CR LF, CR, FF are LF; U+0000 is U+FFFD). -/
def preprocessRaw (s : String) : Array Char := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\r' then
      out := out.push '\n'
      if cs[i+1]? == some '\n' then i := i + 1
    else if c == '\x0C' then out := out.push '\n'
    else if c == '\x00' then out := out.push '�'
    else out := out.push c
    i := i + 1
  return out

/-- The characters of a selector without its comments (CSS Syntax §4.3.2: a comment is no
token). Inside a string a comment is text. A comment between two name characters
separates two tokens: inside `[...]` it is white space (`[foo=bar/**/i]` has the flag
`i`); elsewhere it is a character no selector has, so the two names stay two tokens and
the selector is not read as one name. -/
def stripComments (cs : Array Char) : Array Char := Id.run do
  let mut out := #[]
  let mut i := 0
  let mut quote : Option Char := none
  let mut depth : Nat := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    match quote with
    | some q =>
      out := out.push c
      if c == '\\' then
        if let some d := cs[i+1]? then
          out := out.push d
          i := i + 1
      else if c == q then quote := none
      i := i + 1
    | none =>
      if c == '/' && cs[i+1]? == some '*' then
        -- skip to the end of the comment (or of the text)
        let mut j := i + 2
        for _ in [0:cs.size] do
          if j + 1 ≥ cs.size || (cs[j]! == '*' && cs[j+1]! == '/') then break
          j := j + 1
        let after := cs[j+2]?
        let before := out.back?
        if (before.map nameChar).getD false && (after.map nameChar).getD false then
          out := out.push (if depth > 0 then ' ' else '`')
        i := j + 2
      else
        if c == '"' || c == '\'' then quote := some c
        else if c == '[' then depth := depth + 1
        else if c == ']' then depth := depth - 1
        else if c == '\\' then
          out := out.push c
          i := i + 1
          if let some d := cs[i]? then
            out := out.push d
            i := i + 1
          continue
        out := out.push c
        i := i + 1
  return out

/-- The input of the selector parser: preprocessed (CSS Syntax §3.3) and without comments. -/
def preprocess (s : String) : Array Char := stripComments (preprocessRaw s)

structure P where
  cs : Array Char
  i : Nat := 0
  /-- `:is()` and `:where()` read their argument as a plain selector list, not a forgiving
  one: the parse of `CSS.supports("selector(...)")` (CSS Conditional 4 §3), where an
  invalid selector anywhere makes the condition false. -/
  strict : Bool := false

abbrev PM := StateT P (Except String)

instance {α : Type} : Inhabited (PM α) := ⟨throw "SyntaxError"⟩

def peek (k : Nat := 0) : PM (Option Char) := do
  let p ← get
  return p.cs[p.i + k]?
def bump (k : Nat := 1) : PM Unit := modify fun p => { p with i := p.i + k }
def fail {α} : PM α := throw "SyntaxError"
def atEnd : PM Bool := do return (← peek).isNone

def skipWs : PM Bool := do
  let mut any := false
  for _ in [0:(← get).cs.size + 1] do
    match ← peek with
    | some c =>
      if isWs c then
        bump
        any := true
      else break
    | none => break
  return any

def validEscapeAt (k : Nat) : PM Bool := do
  return (← peek k) == some '\\' && (← peek (k + 1)) != some '\n'

def startsIdent : PM Bool := do
  match ← peek with
  | some '-' =>
    match ← peek 1 with
    | some c => return nameStart c || c == '-' || (← validEscapeAt 1)
    | none => return false
  | some c => return nameStart c || (← validEscapeAt 0)
  | none => return false

/-- Consume an escaped code point; the backslash is consumed. -/
def escaped : PM Char := do
  match ← peek with
  | none => return '�'
  | some c =>
    if isHex c then
      let mut v := 0
      let mut n := 0
      for _ in [0:6] do
        match ← peek with
        | some h =>
          if isHex h then
            v := v * 16 + hexVal h
            n := n + 1
            bump
          else break
        | none => break
      if let some w := ← peek then if isWs w then bump
      if v == 0 || (0xD800 ≤ v && v ≤ 0xDFFF) || v > 0x10FFFF then return '�'
      return Char.ofNat v
    else
      bump
      return c

def ident : PM String := do
  if !(← startsIdent) then fail
  let mut out := ""
  for _ in [0:(← get).cs.size + 1] do
    if ← validEscapeAt 0 then
      bump
      out := out.push (← escaped)
    else match ← peek with
      | some c =>
        if nameChar c then
          out := out.push c
          bump
        else break
      | none => break
  return out

/-- A string token; the quote is at the cursor. A newline in it is an error here. -/
def str : PM String := do
  let some q ← peek | fail
  bump
  let mut out := ""
  for _ in [0:(← get).cs.size + 1] do
    match ← peek with
    | none => return out
    | some c =>
      if c == q then
        bump
        return out
      else if c == '\n' then fail
      else if c == '\\' then
        match ← peek 1 with
        | none =>
          bump
          return out
        | some '\n' => bump 2
        | some _ =>
          bump
          out := out.push (← escaped)
      else
        out := out.push c
        bump
  return out

/-! ## The grammar (Selectors §18) -/

def lowerAscii (s : String) : String := s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- `An+B` (CSS Syntax §6), up to `of` or `)`. -/
def anPlusB (src : String) : Option (Int × Int) :=
  let s := lowerAscii (String.ofList (src.toList.filter (!isWs ·)))
  if s == "odd" then some (2, 1) else if s == "even" then some (2, 0) else
  let intOf := fun (t : String) => if t.isEmpty then none else
    let (neg, body) := if t.startsWith "-" then (true, (t.drop 1).toString) else if t.startsWith "+" then (false, (t.drop 1).toString) else (false, t)
    if body.isEmpty || !body.all Char.isDigit then none else
    let v : Int := body.toNat!
    some (if neg then -v else v)
  match s.splitOn "n" with
  | [b] => (intOf b).map fun v => (0, v)
  | [a, b] =>
    let av : Option Int := if a == "" || a == "+" then some 1 else if a == "-" then some (-1) else intOf a
    let bv : Option Int := if b == "" then some 0 else if b.startsWith "+" || b.startsWith "-" then intOf b else none
    match av, bv with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none

/-- The raw text up to the `)` that closes this level (strings and nesting respected). -/
def argText : PM String := do
  let mut depth := 0
  let mut out := ""
  for _ in [0:(← get).cs.size + 1] do
    match ← peek with
    | none => fail
    | some c =>
      if c == ')' && depth == 0 then return out
      if c == '(' then depth := depth + 1
      if c == ')' then depth := depth - 1
      out := out.push c
      bump
  fail

def legacyPseudoElements : List String := ["before", "after", "first-line", "first-letter"]
/-- Pseudo-elements with no argument (CSS Pseudo-Elements 4, CSS Lists, HTML, CSS View
Transitions, CSS Forms): valid, and never the subject of a match on the DOM. A name that
starts with `-webkit-` is valid too (Selectors 4 §3.6.2, for web compatibility). -/
def pseudoElements : List String :=
  legacyPseudoElements ++ ["selection", "placeholder", "marker", "backdrop", "file-selector-button",
    "target-text", "spelling-error", "grammar-error", "search-text", "cue", "details-content",
    "view-transition", "checkmark", "picker-icon", "scroll-marker", "scroll-marker-group", "column"]
/-- The view transition pseudo-elements that take a name (CSS View Transitions 2 §4). -/
def viewTransitionPseudoElements : List String :=
  ["view-transition-group", "view-transition-image-pair", "view-transition-old", "view-transition-new",
   "view-transition-group-children"]
/-- The structural pseudo-classes: what an element is by its place in the tree. -/
def structuralPseudoClasses : List String :=
  ["root", "empty", "first-child", "last-child", "only-child", "first-of-type", "last-of-type", "only-of-type"]
/-- The pseudo-classes of user action, the ones that may follow any pseudo-element
(Selectors 4 §3.6.4). -/
def userActionPseudoClasses : List String := ["hover", "active", "focus", "focus-visible", "focus-within"]
/-- The pseudo-classes of the scrollbar pseudo-elements (`::-webkit-scrollbar` and its
parts): valid after them only. -/
def scrollbarPseudoClasses : List String :=
  ["horizontal", "vertical", "decrement", "increment", "start", "end", "double-button", "single-button",
   "no-button", "corner-present", "window-inactive"]
def plainPseudoClasses : List String :=
  structuralPseudoClasses ++
  ["scope", "link", "any-link", "checked", "disabled", "enabled", "hover", "active",
   "focus", "focus-within", "focus-visible", "visited", "target", "defined",
   -- input states read from the element's attributes (HTML §4.16.3)
   "required", "optional", "read-only", "read-write", "placeholder-shown", "default", "indeterminate",
   "open", "heading",
   -- states this engine does not hold for a match on the tree: valid, never true
   "valid", "invalid", "in-range", "out-of-range", "user-valid", "user-invalid", "autofill",
   "-webkit-autofill", "popover-open", "modal", "fullscreen", "picture-in-picture", "playing", "paused",
   "seeking", "buffering", "stalled", "muted", "volume-locked", "host", "has-slotted",
   "active-view-transition"]

/-- Whether pseudo-element `n` may follow pseudo-element `pe` in a compound (CSS
Pseudo-Elements 4 §4, CSS Multicol 2 §2.1, CSS Shadow Parts, CSS Forms): `::marker` and
`::column` after `::before`/`::after`, `::scroll-marker` after `::column`, a pseudo-element
that is not itself a tree root after `::part()` and `::slotted()`, a `-webkit-` one after a
`-webkit-` one. No other pair. -/
def pseudoElementAfter (pe n : String) : Bool :=
  if pe == "before" || pe == "after" then n == "marker" || n == "column"
  else if pe == "column" then n == "scroll-marker"
  else if pe == "part" || pe == "slotted" then
    !["part", "slotted", "column", "view-transition"].contains n && !viewTransitionPseudoElements.contains n
  else pe.startsWith "-webkit-" && n.startsWith "-webkit-"

/-- A compound has a pseudo-element. -/
def hasPseudoElement (c : List Simple) : Bool :=
  c.any fun s => match s with
    | .never => true
    | _ => false

/-- A complex selector has a pseudo-element in one of its compounds. -/
def Complex.hasPseudoElement : Complex → Bool
  | .mk parts => parts.any fun p => Selectors.hasPseudoElement p.2

/-- A compound has a `:has()`. -/
def compoundHasHas (c : List Simple) : Bool :=
  c.any fun s => match s with
    | .has _ => true
    | _ => false

/-- A complex selector has a `:has()` in a compound, or in an `:is()`, `:where()` or
`:not()` of one: `:has()` may not be nested in `:has()` (Selectors 4 §4.5). -/
def Complex.mentionsHas : Complex → Bool
  | .mk parts => parts.any fun p => compoundHasHas p.2 || p.2.any fun s => match s with
    | .is sels | .not sels => sels.any fun c => match c with
      | .mk ps => ps.any fun q => compoundHasHas q.2
    | _ => false

/-- The names of `::part()`: one or more identifiers separated by white space. -/
def partNames (t : String) : Bool :=
  let ws := (t.split (fun c => isWs c)).toList.map (·.toString) |>.filter (· != "")
  !ws.isEmpty && ws.all fun w =>
    match w.toList with
    | c :: rest => (nameStart c || c == '-' || c == '\\') && rest.all fun x => nameChar x || x == '\\'
    | [] => false

/-- The most compound selectors in one complex selector, and the deepest nesting of
`:not()`, `:is()` and `:nth-child(… of …)`: matching recurses once per compound and once
per nesting level, so these bound its stack. A longer selector is refused as invalid. -/
def maxCompounds : Nat := 1024
def maxNesting : Nat := 32

def expectClose : PM Unit := do
  if (← peek) == some ')' then bump else fail

def attrSel : PM Simple := do
  let _ ← skipWs
  let mut ns := NsSel.default
  let mut name := ""
  match ← peek with
  | some '*' =>
    if (← peek 1) == some '|' && (← peek 2) != some '=' then
      bump 2
      ns := .any
      name ← ident
    else fail
  | some '|' =>
    bump
    ns := .none
    name ← ident
  | _ =>
    name ← ident
    if (← peek) == some '|' && (← peek 1) != some '=' then fail -- an undeclared prefix
  let _ ← skipWs
  let op ← match ← peek with
    | some ']' =>
      bump
      return .attr ns name .present "" false false
    | some '=' =>
      bump
      pure AttrOp.eq
    | some c =>
      if (← peek 1) != some '=' then fail
      let o ← match c with
        | '~' => pure AttrOp.includes | '|' => pure .dash | '^' => pure .pre
        | '$' => pure .suf | '*' => pure .sub | _ => fail
      bump 2
      pure o
    | none => fail
  let _ ← skipWs
  let value ← match ← peek with
    | some '"' | some '\'' => str
    | _ => ident
  let _ ← skipWs
  let mut ci := false
  let mut cs := false
  if ← startsIdent then
    let f := lowerAscii (← ident)
    if f == "i" then ci := true else if f == "s" then cs := true else fail
    let _ ← skipWs
  if (← peek) != some ']' then fail
  bump
  return .attr ns name op value ci cs

/-- The parser's fuel: each nesting level of a selector list takes three steps
(`selectorList`, `complex`, `compound`), so `maxNesting` levels are allowed. -/
def parseFuel : Nat := 3 * maxNesting

mutual
/-- A selector list: complex selectors separated by commas. The fuel bounds nesting
(`parseFuel`). -/
def selectorList : Nat → PM (List Complex)
  | 0 => fail
  | fuel + 1 => do
    let mut out := #[]
    for _ in [0:(← get).cs.size + 1] do
      let _ ← skipWs
      out := out.push (← complex fuel)
      let _ ← skipWs
      match ← peek with
      | some ',' => bump
      | _ => break
    return out.toList

/-- A relative selector list (Selectors 4 §4.5, the argument of `:has()`): complex
selectors, each after an optional combinator, which is kept on its first compound. -/
def relativeList : Nat → PM (List Complex)
  | 0 => fail
  | fuel + 1 => do
    let mut out := #[]
    for _ in [0:(← get).cs.size + 1] do
      let _ ← skipWs
      let mut comb := ' '
      if let some c := ← peek then
        if c == '>' || c == '+' || c == '~' then
          bump
          comb := c
          let _ ← skipWs
      let c ← complex fuel
      match c with
      | .mk ((_, first) :: rest) => out := out.push (Complex.mk ((comb, first) :: rest))
      | .mk [] => fail
      let _ ← skipWs
      match ← peek with
      | some ',' => bump
      | _ => break
    return out.toList

/-- A forgiving selector list (Selectors 4 §4.2.1, the argument of `:is()` and `:where()`):
each comma-separated item that is not a valid complex selector is left out (a comma inside
brackets or a string separates nothing). -/
def forgivingList : Nat → PM (List Complex)
  | 0 => fail
  | fuel + 1 => do
    let mut out := #[]
    for _ in [0:(← get).cs.size + 1] do
      let _ ← skipWs
      if (← peek) == some ')' then break
      let start ← get
      let item ← tryCatch (do
          let c ← complex fuel
          let _ ← skipWs
          match ← peek with
          | some ',' | some ')' => pure (some c)
          | _ => fail) (fun _ => pure none)
      match item with
      | some c => out := out.push c
      | none =>
        -- skip the item: to the next ',' or ')' outside brackets and strings
        set start
        let mut depth := 0
        let mut quote : Option Char := none
        for _ in [0:(← get).cs.size + 1] do
          match ← peek with
          | none => break
          | some ch =>
            if (ch == ',' || ch == ')') && depth == 0 && quote.isNone then break
            match quote with
            | some q =>
              if ch == q then quote := none
            | none =>
              if ch == '"' || ch == '\'' then quote := some ch
              else if ch == '(' || ch == '[' then depth := depth + 1
              else if (ch == ')' || ch == ']') && depth > 0 then depth := depth - 1
            bump
      match ← peek with
      | some ',' => bump
      | _ => break
    return out.toList

def complex : Nat → PM Complex
  | 0 => fail
  | fuel + 1 => do
    let mut parts : Array (Char × List Simple) := #[]
    let mut comb := ' '
    for _ in [0:(← get).cs.size + 1] do
      let c ← compound fuel
      parts := parts.push (comb, c)
      -- a bound on the compounds of one complex selector: matching recurses once per compound
      if parts.size > maxCompounds then fail
      let ws ← skipWs
      match ← peek with
      | some ',' | some ')' | none => break
      | some c' =>
        -- a pseudo-element ends its complex selector (Selectors 4 §3.6)
        if hasPseudoElement c then fail
        if c' == '>' || c' == '+' || c' == '~' then
          bump
          comb := c'
          let _ ← skipWs
        else if ws then comb := ' '
        else fail
    return .mk parts.toList

def compound : Nat → PM (List Simple)
  | 0 => fail
  | fuel + 1 => do
    let mut out : Array Simple := #[]
    -- type selector with an optional namespace prefix
    let start := (← get).i
    match ← peek with
    | some '*' =>
      bump
      if (← peek) == some '|' && (← peek 1) != some '=' then
        bump
        if (← peek) == some '*' then
          bump
          out := out.push (.type .any none)
        else out := out.push (.type .any (some (← ident)))
      else out := out.push (.type .default none)
    | some '|' =>
      bump
      if (← peek) == some '*' then
        bump
        out := out.push (.type .none none)
      else out := out.push (.type .none (some (← ident)))
    | _ =>
      if ← startsIdent then
        let name ← ident
        if (← peek) == some '|' && (← peek 1) != some '=' then fail -- an undeclared prefix
        out := out.push (.type .default (some name))
    -- the pseudo-element met in this compound ("" none): after one, only pseudo-classes
    -- that the pseudo-element allows, and pseudo-elements
    let mut pe := ""
    for _ in [0:(← get).cs.size + 1] do
      match ← peek with
      | some '#' =>
        if !pe.isEmpty then fail
        bump
        if !(← startsIdent) then
          -- a hash token may start with a digit or "-" + digit in CSS, but an ID selector
          -- needs an identifier
          fail
        out := out.push (.id (← ident))
      | some '.' =>
        if !pe.isEmpty then fail
        bump
        out := out.push (.cls (← ident))
      | some '[' =>
        if !pe.isEmpty then fail
        bump
        out := out.push (← attrSel)
      | some ':' =>
        bump
        if (← peek) == some ':' then
          bump
          let n := lowerAscii (← ident)
          if pe == "view-transition" || viewTransitionPseudoElements.contains pe then fail
          if !pe.isEmpty && !pseudoElementAfter pe n then fail
          if (← peek) == some '(' then
            bump
            if n == "part" then
              let t ← argText
              if !partNames t then fail
              bump
            else if n == "slotted" then
              let _ ← skipWs
              let c ← compound fuel
              if hasPseudoElement c then fail
              let _ ← skipWs
              expectClose
            else if n == "highlight" || n == "picker" then
              let _ ← skipWs
              let _ ← ident
              let _ ← skipWs
              expectClose
            else if n == "scroll-button" then
              -- `::scroll-button(*)` or a direction (CSS Overflow 5 §3.1)
              let _ ← skipWs
              if (← peek) == some '*' then bump
              else
                let d := lowerAscii (← ident)
                if !["up", "down", "left", "right", "block-start", "block-end", "inline-start", "inline-end"].contains d then fail
              let _ ← skipWs
              expectClose
            else if viewTransitionPseudoElements.contains n then
              -- `*` or a name, then classes, with no white space between them
              let _ ← skipWs
              if (← peek) == some '*' then bump
              else
                let name := lowerAscii (← ident)
                if ["default", "unset", "initial", "inherit", "revert", "revert-layer", "none"].contains name then fail
              for _ in [0:(← get).cs.size + 1] do
                if (← peek) == some '.' then
                  bump
                  let _ ← ident
                else break
              let _ ← skipWs
              expectClose
            else fail
            pe := n
            out := out.push .never
          else if pseudoElements.contains n || n.startsWith "-webkit-" then
            pe := n
            -- the pseudo-element by name as well, for the styles of a pseudo-element
            -- (`matchesPseudo`); `.never` keeps the selector from matching an element
            out := (out.push .never).push (.pseudo ("::" ++ n))
          else fail
        else
          let n := lowerAscii (← ident)
          -- after a pseudo-element: `::part()` takes every pseudo-class but the structural
          -- ones and `:has()`; a named view transition pseudo-element takes `:only-child`;
          -- `::view-transition` takes none; the others take the user action pseudo-classes
          if !pe.isEmpty then
            if (← peek) == some '(' then
              if pe != "part" || n == "has" || n.startsWith "nth-" then fail
            else if legacyPseudoElements.contains n then pure ()
            else if pe == "part" then
              if structuralPseudoClasses.contains n then fail
            else if viewTransitionPseudoElements.contains pe then
              if n != "only-child" then fail
            else if pe == "view-transition" || pe == "column" then fail
            else if !(userActionPseudoClasses.contains n ||
                (pe.startsWith "-webkit-scrollbar" || pe == "-webkit-resizer") && scrollbarPseudoClasses.contains n) then fail
          if (← peek) == some '(' then
            bump
            let _ ← skipWs
            match n with
            | "not" =>
              let l ← selectorList fuel
              let _ ← skipWs
              expectClose
              if l.any (·.hasPseudoElement) then fail
              out := out.push (.not l)
            | "is" | "where" =>
              let l ← if (← get).strict then selectorList fuel else forgivingList fuel
              let _ ← skipWs
              expectClose
              out := out.push (.is l)
            | "matches" | "-webkit-any" =>
              let l ← selectorList fuel
              let _ ← skipWs
              expectClose
              out := out.push (.is l)
            | "has" =>
              let l ← relativeList fuel
              let _ ← skipWs
              expectClose
              if l.any (·.hasPseudoElement) || l.any (·.mentionsHas) then fail
              out := out.push (.has l)
            | "dir" =>
              let t := lowerAscii (← ident)
              let _ ← skipWs
              expectClose
              out := out.push (.pseudo ("dir(" ++ t ++ ")"))
            | "heading" =>
              -- `:heading(<integer>#)`: the heading levels
              let t ← argText
              bump
              let levels := (t.splitOn ",").map fun x => x.trimAscii.toString
              if levels.isEmpty || !levels.all (fun x => !x.isEmpty && x.all Char.isDigit) then fail
              out := out.push (.pseudo ("heading(" ++ ",".intercalate levels ++ ")"))
            | "state" =>
              let _ ← ident
              let _ ← skipWs
              expectClose
              out := out.push (.pseudo "state()")
            | "host" | "host-context" =>
              -- `:host(<compound-selector>)` (CSS Scoping 1 §3.2.1): matches no element of a
              -- document tree
              let _ ← skipWs
              let c ← compound fuel
              if hasPseudoElement c then fail
              let _ ← skipWs
              expectClose
              out := out.push (.pseudo (n ++ "()"))
            | "lang" =>
              let t ← argText
              bump
              let ranges := (t.splitOn ",").map (fun r => (r.trimAscii.toString.dropWhile (· == '"')).toString.takeWhile (· != '"') |>.toString)
              out := out.push (.lang ranges)
            | "nth-child" | "nth-last-child" | "nth-of-type" | "nth-last-of-type" =>
              let kind := match n with
                | "nth-child" => NthKind.child | "nth-last-child" => .lastChild
                | "nth-of-type" => .ofType | _ => .lastOfType
              -- the An+B part runs to `of` (nth-child only) or `)`
              let p0 := (← get).i
              let t ← argText
              let (ab, ofPart) := match (t.splitOn " of ") with
                | [x] => (x, false)
                | x :: _ => (x, true)
                | [] => (t, false)
              let some (a, b) := anPlusB ab | fail
              if ofPart then
                if kind != .child && kind != .lastChild then fail
                set { (← get) with i := p0 + ab.length + 4 }
                let l ← selectorList fuel
                let _ ← skipWs
                expectClose
                out := out.push (.nth kind a b (some l))
              else
                bump
                out := out.push (.nth kind a b none)
            | _ => fail
          else if legacyPseudoElements.contains n then
            if !pe.isEmpty && !pseudoElementAfter pe n then fail
            pe := n
            out := (out.push .never).push (.pseudo ("::" ++ n))
          else if plainPseudoClasses.contains n || (!pe.isEmpty && scrollbarPseudoClasses.contains n) then
            out := out.push (.pseudo n)
          else fail
      | _ => break
    if (← get).i == start then fail
    return out.toList

end

/-- Parse a selectors string; `none` when it is invalid (a SyntaxError). -/
def parse (s : String) (strict : Bool := false) : Option (List Complex) :=
  match (do
      let l ← selectorList parseFuel
      let _ ← skipWs
      if !(← atEnd) then fail
      return l : PM (List Complex)).run { cs := preprocess s, strict := strict } with
  | .ok (l, _) => some l
  | .error _ => none

#guard (parse ":is(:foo, .a)").isSome && (parse ":is(:foo, .a)" true).isNone && (parse ":is(.a, .b)" true).isSome

/-! ## Matching -/

/-- HTML §4.16.2: attribute values that match ASCII case-insensitively on HTML elements
of HTML documents. -/
def caseInsensitiveAttrs : List String :=
  ["accept", "accept-charset", "align", "alink", "axis", "bgcolor", "charset", "checked",
   "clear", "codetype", "color", "compact", "declare", "defer", "dir", "direction", "disabled",
   "enctype", "face", "frame", "hreflang", "http-equiv", "lang", "language", "link", "media",
   "method", "multiple", "nohref", "noresize", "noshade", "nowrap", "readonly", "rel", "rev",
   "rules", "scope", "scrolling", "selected", "shape", "target", "text", "type", "valign",
   "valuetype", "vlink"]

def htmlOf (d : Dom) (k : NodeId) : Bool :=
  let x := d.get k
  x.ns == some htmlNS && (d.get x.doc).htmlDoc

def attrsMatching (d : Dom) (k : NodeId) (ns : NsSel) (name : String) : List Attr :=
  let x := d.get k
  let name := if htmlOf d k then lowerAscii name else name
  x.attrs.toList.filter fun a => a.lname == name &&
    match ns with | .any => true | .default | .none => a.ns.isNone

/-! ### Matching without building strings

Selector matching runs for each element and each candidate rule of a cascade, so the
tests below read the bytes of the strings they compare and allocate nothing: a type or
attribute name compared with ASCII letters taken in lower case, a class looked for among the
words of the `class` attribute. Each agrees with the form that builds strings (`lowerAscii`,
`wsSplit`); the guards after them compare the two. Lower-casing ASCII touches only the bytes
0x41 to 0x5A, which never occur inside a multi-byte UTF-8 sequence, so a byte-wise
comparison is a character-wise one. -/

/-- Byte `i` of `s`'s UTF-8 encoding, 0 past its end. -/
@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/-- An ASCII upper-case letter's byte in lower case; any other byte as it is. -/
@[inline] def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- Bytes `i` onwards of `c` and `d` agree, `d`'s taken in ASCII lower case (a loop over the
bytes: a tail call). -/
def eqLowerFrom (c d : String) (i : Nat) : Bool :=
  if i < c.utf8ByteSize then byteAt c i == lowerByte (byteAt d i) && eqLowerFrom c d (i + 1) else true
termination_by c.utf8ByteSize - i

/-- `c == lowerAscii d`, with no string built. -/
def eqLowerAscii (c d : String) : Bool :=
  c.utf8ByteSize == d.utf8ByteSize && eqLowerFrom c d 0

/-- An ASCII white space byte of the `class` attribute (HTML §2.3.4: space, tab, LF, FF, CR). -/
@[inline] def wsByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 12 || b == 13

/-- The bytes of `v` are at byte `i` of `s` (a loop over `v`'s bytes: a tail call). -/
def bytesAt (s v : String) (i j : Nat) : Bool :=
  if j < v.utf8ByteSize then byteAt s (i + j) == byteAt v j && bytesAt s v i (j + 1) else true
termination_by v.utf8ByteSize - j

/-- The first white space byte of `s` at or after `j`, or its end (a loop: a tail call). -/
def skipWord (s : String) (j : Nat) : Nat :=
  if j < s.utf8ByteSize then (if wsByte (byteAt s j) then j else skipWord s (j + 1)) else j
termination_by s.utf8ByteSize - j

theorem skipWord_ge (s : String) (j : Nat) : skipWord s j ≥ j := by
  unfold skipWord
  split
  · split
    · omega
    · have := skipWord_ge s (j + 1); omega
  · omega
termination_by s.utf8ByteSize - j

/-- From byte `i` of `s` (at the start of a word or in the white space before one), whether a
word of `s` is `v`: each word is compared where it starts, then skipped (a loop over the
bytes: a tail call). -/
def tokenFrom (s v : String) (i : Nat) : Bool :=
  if i < s.utf8ByteSize then
    if wsByte (byteAt s i) then tokenFrom s v (i + 1)
    else
      let e := i + v.utf8ByteSize
      if e ≤ s.utf8ByteSize && bytesAt s v i 0 && (e == s.utf8ByteSize || wsByte (byteAt s e)) then true
      else tokenFrom s v (skipWord s (i + 1))
  else false
termination_by s.utf8ByteSize - i
decreasing_by
  all_goals simp_wf
  · omega
  · have := skipWord_ge s (i + 1); omega

/-- `(wsSplit s).contains v`, with no string built: a non-empty `v` is one of the words of
`s`. -/
def hasToken (s v : String) : Bool := v.utf8ByteSize != 0 && tokenFrom s v 0

def wsSplit (s : String) : List String :=
  (s.map fun c => if c == '\t' || c == '\n' || c == '\x0C' || c == '\r' then ' ' else c).splitOn " " |>.filter (· != "")

#guard ["", "a", "a b", " a\tb\n", "ab a", "aa", "a\x0Cb", "é a", "x y z a"].all fun s =>
  ["a", "b", "ab", "", "é", "z"].all fun v => hasToken s v == (wsSplit s).contains v
#guard ["div", "DIV", "Div", "dív", "DÍV", "", "a-b", "A_B"].all fun n =>
  ["div", "dív", "", "a-b", "a_b"].all fun c => eqLowerAscii c n == (c == lowerAscii n)

def attrValueMatches (op : AttrOp) (v want : String) : Bool :=
  match op with
  | .present => true
  | .eq => v == want
  | .includes => !want.isEmpty && !(want.any isWs) && (wsSplit v).contains want
  | .dash => v == want || v.startsWith (want ++ "-")
  | .pre => !want.isEmpty && v.startsWith want
  | .suf => !want.isEmpty && v.endsWith want
  | .sub => !want.isEmpty && (v.splitOn want).length > 1

def elementSiblings (d : Dom) (k : NodeId) : Array NodeId :=
  match (d.get k).parent with
  | some p => (d.get p).kids.filter fun c => (d.get c).type == .element
  | none => #[k]

/-! ### Sibling positions without a sibling array

The structural pseudo-classes ask where an element is among its element siblings. These read
the parent's child list in place, from the element outwards, and stop at the first sibling
that answers (`:first-child` looks back to the nearest element sibling only); none builds
an array. `elementSiblings` stays as the definition they agree with (guards below). -/

/-- The parent's children and the element's place among them. -/
def kidPlace (d : Dom) (k : NodeId) : Option (Array NodeId × Nat) :=
  match (d.get k).parent with
  | some p => let kids := (d.get p).kids; (kids.findIdx? (· == k)).map fun i => (kids, i)
  | none => none

/-- An element child before place `j` satisfies `pred`, looking from the nearest (a loop:
a tail call). -/
def elemBefore (d : Dom) (kids : Array NodeId) (pred : NodeId → Bool) : Nat → Bool
  | 0 => false
  | j + 1 =>
    let c := kids[j]!
    if (d.get c).type == .element && pred c then true else elemBefore d kids pred j

/-- An element child from place `j` on satisfies `pred` (a loop: a tail call). -/
def elemAfter (d : Dom) (kids : Array NodeId) (pred : NodeId → Bool) (j : Nat) : Bool :=
  if h : j < kids.size then
    let c := kids[j]
    if (d.get c).type == .element && pred c then true else elemAfter d kids pred (j + 1)
  else false
termination_by kids.size - j

/-- The element children in places `j` to `hi` that satisfy `pred`, counted (a loop: a tail
call). -/
def elemCount (d : Dom) (kids : Array NodeId) (pred : NodeId → Bool) (j hi acc : Nat) : Nat :=
  if j < hi then
    let c := kids[j]!
    elemCount d kids pred (j + 1) hi (if (d.get c).type == .element && pred c then acc + 1 else acc)
  else acc
termination_by hi - j

/-- Whether element `k` is the first (`last` false) or last of its element siblings that
satisfy `pred` (`pred` holds of `k`). -/
def edgeSib (d : Dom) (k : NodeId) (pred : NodeId → Bool) (last : Bool) : Bool :=
  match kidPlace d k with
  | some (kids, i) => if last then !elemAfter d kids pred (i + 1) else !elemBefore d kids pred i
  | none => false

/-- The 1-based place of element `k` among its element siblings that satisfy `pred`,
counted from the start, or from the end with `fromEnd`. -/
def sibPos (d : Dom) (k : NodeId) (pred : NodeId → Bool) (fromEnd : Bool) : Option Nat :=
  (kidPlace d k).map fun (kids, i) =>
    if fromEnd then elemCount d kids pred (i + 1) kids.size 0 + 1 else elemCount d kids pred 0 i 0 + 1

def nthOk (a b : Int) (pos : Nat) : Bool :=
  let p : Int := pos
  if a == 0 then p == b else
  let n := (p - b) / a
  (p - b) % a == 0 && n ≥ 0

def attrVal? (d : Dom) (k : NodeId) (name : String) : Option String :=
  ((d.get k).attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

def isHtml (d : Dom) (k : NodeId) (names : List String) : Bool :=
  let x := d.get k
  x.type == .element && x.ns == some htmlNS && names.contains x.lname

/-- HTML §4.16.3: a form control that is disabled (its own attribute, an `optgroup`, or a
disabled `fieldset` ancestor outside its first `legend`). -/
def disabledEl (d : Dom) (k : NodeId) : Bool := Id.run do
  if !isHtml d k ["button", "input", "select", "textarea", "optgroup", "option", "fieldset"] then return false
  if (attrVal? d k "disabled").isSome then return true
  if isHtml d k ["option"] then
    if let some p := (d.get k).parent then
      if isHtml d p ["optgroup"] && (attrVal? d p "disabled").isSome then return true
  let mut child := k
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p =>
      if isHtml d p ["fieldset"] && (attrVal? d p "disabled").isSome then
        let firstLegend := (d.get p).kids.find? fun c => isHtml d c ["legend"]
        if firstLegend != some child then return true
      child := p
      cur := (d.get p).parent
  return false

def langOf (d : Dom) (k : NodeId) : Option String := Id.run do
  let mut cur := some k
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some p =>
      let x := d.get p
      if x.type == .element then
        if let some a := x.attrs.find? (fun a => a.ns == some xmlNS && a.lname == "lang") then return some a.value
        if let some a := x.attrs.find? (fun a => a.ns.isNone && a.lname == "lang") then return some a.value
      cur := x.parent
  return none

/-- The rank of an `h1`–`h6` element of HTML (1 to 6), 0 for any other node. -/
def headingRank (x : Node) : Nat :=
  if x.type != .element || x.ns != some htmlNS then 0 else
  match x.lname with
  | "h1" => 1 | "h2" => 2 | "h3" => 3 | "h4" => 4 | "h5" => 5 | "h6" => 6 | _ => 0

/-- The heading offset of node `k` (whatwg/html PR 11086): the `headingoffset` values
(non-negative integers; anything else counts 0) of the node and its ancestors, up to and
including the nearest one with `headingreset`, at most 9. -/
def headingOffset (d : Dom) (k : NodeId) : Nat := Id.run do
  let mut offset := 0
  let mut cur := some k
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some p =>
      let y := d.get p
      if y.type == .element then
        let v := ((y.attrs.find? fun a => a.ns.isNone && a.lname == "headingoffset").bind fun a =>
          L4Factoidal.HTML.Dimension.parseNonNegative a.value).getD 0
        offset := min 9 (offset + v)
        if y.attrs.any fun a => a.ns.isNone && a.lname == "headingreset" then break
      cur := y.parent
  return offset

/-- The heading level of an `h1`–`h6` element (HTML "heading level"): its rank plus its
heading offset, at most 9; `none` for other nodes. -/
def headingLevel (d : Dom) (k : NodeId) : Option Nat :=
  if headingRank (d.get k) == 0 then none else some (min 9 (headingRank (d.get k) + headingOffset d k))

/-- Says: a heading level is between 1 and 9. -/
theorem headingLevel_bounds (d : Dom) (k : NodeId) (n : Nat) (h : headingLevel d k = some n) :
    1 ≤ n ∧ n ≤ 9 := by
  unfold headingLevel at h
  split at h
  · cases h
  · rename_i hr
    cases h
    simp only [beq_iff_eq] at hr
    omega

/-- Says: only the six heading elements have a level. -/
theorem headingLevel_rank (d : Dom) (k : NodeId) (n : Nat) (h : headingLevel d k = some n) :
    headingRank (d.get k) ≠ 0 := by
  unfold headingLevel at h
  split at h
  · cases h
  · rename_i hr; simpa using hr

/-- The `contenteditable` state that an element and its ancestors give it (HTML §6.8.1): the
nearest element with a valid `contenteditable` value decides; `false` decides no. -/
def editableEl (d : Dom) (k : NodeId) : Bool := Id.run do
  let mut cur := some k
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p =>
      let y := d.get p
      if y.type == .element && y.ns == some htmlNS then
        match (y.attrs.find? fun a => a.ns.isNone && a.lname == "contenteditable").map (lowerAscii ·.value) with
        | some "" | some "true" | some "plaintext-only" => return true
        | some "false" => return false
        | _ => pure ()
      cur := y.parent
  return false

/-- The nearest `form` ancestor of a node (its form owner when it has no `form` attribute). -/
def formAncestor (d : Dom) (k : NodeId) : Option NodeId := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some p => if isHtml d p ["form"] then return some p else cur := (d.get p).parent
  return none

def radioChecked (d : Dom) (k : NodeId) : Bool :=
  ((d.get k).checkedness.getD (attrVal? d k "checked").isSome)

/-- `:indeterminate` (HTML §4.16.3), as far as the tree tells: a radio button whose group
(the same non-empty name, tree and form) has no checked button, and a `progress` element
with no `value` attribute. (A checkbox's indeterminate flag is a script's, not here.) -/
def indeterminate (d : Dom) (k : NodeId) : Bool :=
  (isHtml d k ["progress"] && (attrVal? d k "value").isNone) ||
  (isHtml d k ["input"] && lowerAscii ((attrVal? d k "type").getD "") == "radio" &&
    (match attrVal? d k "name" with
     | none | some "" => !radioChecked d k
     | some nm =>
       let root := d.root k
       let form := formAncestor d k
       !((d.treeOrder root).any fun j => isHtml d j ["input"] && lowerAscii ((attrVal? d j "type").getD "") == "radio" &&
          attrVal? d j "name" == some nm && formAncestor d j == form && radioChecked d j)))

/-- HTML §4.16.3 `:read-write`: an `input` that takes text and a `textarea`, neither
`readonly` nor disabled, and an editing host or an element in one (`contenteditable`). -/
def readWrite (d : Dom) (k : NodeId) : Bool :=
  let ro := (attrVal? d k "readonly").isSome || disabledEl d k
  if isHtml d k ["input"] then
    !ro && !["hidden", "checkbox", "radio", "file", "submit", "image", "reset", "button", "range", "color"].contains
      (lowerAscii ((attrVal? d k "type").getD ""))
  else if isHtml d k ["textarea"] then !ro
  else Id.run do
    let mut cur := some k
    for _ in [0:d.size + 1] do
      match cur with
      | none => return false
      | some n =>
        match (attrVal? d n "contenteditable").map lowerAscii with
        | some "false" => return false
        | some _ => return true
        | none => cur := (d.get n).parent
    return false

/-- The matcher's fuel: a step per compound of a complex selector and a few per nesting
level of `:not()`/`:is()`/`:nth-child(… of …)`; with the parser's bounds it is never
exhausted. -/
def matchFuel : Nat := (maxNesting + 1) * (maxCompounds + 8)

/-- The parent of a node when it is an element. -/
def parentElement (d : Dom) (n : NodeId) : Option NodeId :=
  (d.get n).parent.bind fun p => if (d.get p).type == .element then some p else none

/-- The element sibling before a node. -/
def prevElement (d : Dom) (n : NodeId) : Option NodeId :=
  let sibs := elementSiblings d n
  match sibs.toList.findIdx? (· == n) with
  | some i => if i == 0 then none else sibs[i - 1]?
  | none => none

/-- The element siblings after a node, nearest first. -/
def followingElements (d : Dom) (n : NodeId) : Array NodeId :=
  let sibs := elementSiblings d n
  match sibs.toList.findIdx? (· == n) with
  | some i => sibs.extract (i + 1) sibs.size
  | none => #[]

/-- Element `x` stands to the anchor `a` as the combinator `comb` of a relative selector
says (Selectors 4 §4.5): a descendant (' '), a child, the next sibling, a later sibling. -/
def related (d : Dom) (a : NodeId) (comb : Char) (x : NodeId) : Bool :=
  match comb with
  | '>' => parentElement d x == some a
  | '+' => prevElement d x == some a
  | '~' => (d.get x).parent == (d.get a).parent && (followingElements d a).contains x
  | _ => Id.run do
    let mut cur := (d.get x).parent
    for _ in [0:d.size + 1] do
      match cur with
      | none => return false
      | some p => if p == a then return true else cur := (d.get p).parent
    return false

/-- The elements a relative selector with combinator `comb` can have as its subject, for
the anchor `k`: with one compound, exactly the elements in that relation; with more, the
descendants of `k` (' ', '>') or its later siblings and their descendants ('+', '~'). -/
def hasCandidates (d : Dom) (k : NodeId) (comb : Char) (single : Bool) : Array NodeId :=
  let els := fun (a : Array NodeId) => a.filter fun c => (d.get c).type == .element
  if comb == ' ' || (comb == '>' && !single) then els (d.treeOrder k false)
  else if comb == '>' then els (d.get k).kids
  else
    let after := followingElements d k
    let after := if comb == '+' then after.extract 0 1 else after
    if single then after else after.foldl (fun acc s => acc ++ els (d.treeOrder s true)) #[]

/-- The directionality of an element (HTML §3.2.6.4): its `dir` attribute (`ltr`, `rtl`;
`auto`, and `bdi` with none, by the first strong character of its text, skipping `bdi`,
`script`, `style`, `textarea` and elements with a `dir`), else its parent's; left to right
at the root. True: right to left. The walk up is bounded by the arena size. -/
def isRtl (d : Dom) (k : NodeId) : Bool := Id.run do
  let mut cur := some k
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some n =>
      let x := d.get n
      if x.type != .element then return false
      let dir := (attrVal? d n "dir").map lowerAscii
      if dir == some "rtl" then return true
      if dir == some "ltr" then return false
      if dir == some "auto" || (dir.isNone && isHtml d n ["bdi"]) then
        let mut pending : List NodeId := x.kids.toList
        for _ in [0:d.size + 1] do
          match pending with
          | [] => return false
          | c :: rest =>
            let y := d.get c
            pending := rest
            if y.type == .text then
              for ch in y.data.toList do
                match Unicode.bidiClassOf ch with
                | .L => return false
                | .R | .AL => return true
                | _ => pure ()
            else if y.type == .element && !["bdi", "script", "style", "textarea"].contains y.lname &&
                (attrVal? d c "dir").isNone then
              pending := y.kids.toList ++ pending
        return false
      cur := x.parent
  return false

mutual
def matchSimple (d : Dom) (scope : Option NodeId) : Nat → NodeId → Simple → Bool
  | 0, _, _ => false
  | fuel + 1, k, s =>
    match s with
    | .type ns name =>
      let x := d.get k
      let nsOk := match ns with
        | .default | .any => true
        | .none => x.ns.isNone
      nsOk && match name with
        | none => true
        | some n => if htmlOf d k then eqLowerAscii x.lname n else x.lname == n
    | .id v => (d.get k).attrs.any fun a => a.ns.isNone && a.lname == "id" && a.value == v
    | .cls v => match attrVal? d k "class" with
      | some c => hasToken c v
      | none => false
    | .attr ns name op value ci cs =>
      let x := d.get k
      let html := htmlOf d k
      -- the attributes `attrsMatching` gives, tested in place
      x.attrs.any fun a =>
        (if html then eqLowerAscii a.lname name else a.lname == name) &&
        (match ns with | .any => true | .default | .none => a.ns.isNone) &&
        (match op with
          | .present => true
          | _ =>
            let ins := ci || (!cs && html && caseInsensitiveAttrs.any (eqLowerAscii · name))
            if ins then attrValueMatches op (lowerAscii a.value) (lowerAscii value) else attrValueMatches op a.value value)
    | .pseudo n =>
      let x := d.get k
      -- an element sibling of the same type (`:first-of-type` and the like)
      let sameKind := fun (c : NodeId) => (d.get c).lname == x.lname && (d.get c).ns == x.ns
      match n with
      | "root" => match x.parent with | some p => (d.get p).type == .document | none => false
      | "empty" => x.kids.all fun c =>
          let y := d.get c
          y.type != .element && !((y.type == .text || y.type == .cdata) && !y.data.isEmpty)
      | "first-child" => edgeSib d k (fun _ => true) false
      | "last-child" => edgeSib d k (fun _ => true) true
      | "only-child" => edgeSib d k (fun _ => true) false && edgeSib d k (fun _ => true) true
      | "first-of-type" => edgeSib d k sameKind false
      | "last-of-type" => edgeSib d k sameKind true
      | "only-of-type" => edgeSib d k sameKind false && edgeSib d k sameKind true
      | "scope" => match scope with | some s => s == k | none => x.parent.any fun p => (d.get p).type == .document
      | "link" | "any-link" => isHtml d k ["a", "area"] && (attrVal? d k "href").isSome
      | "checked" =>
        -- the checkedness of a checkbox or radio button and the selectedness of an option:
        -- the value a script or a click set (`Node.checkedness`), else the content attribute
        (isHtml d k ["input"] && (x.checkedness.getD (attrVal? d k "checked").isSome) &&
          ["checkbox", "radio"].contains (lowerAscii ((attrVal? d k "type").getD ""))) ||
        (isHtml d k ["option"] && (x.checkedness.getD (attrVal? d k "selected").isSome))
      | "disabled" => disabledEl d k
      | "enabled" => isHtml d k ["button", "input", "select", "textarea", "optgroup", "option", "fieldset"] && !disabledEl d k
      -- the element states that the page's objects set (`Node.states`)
      | "defined" => !(x.ns == some htmlNS && CustomElements.validName x.lname) || x.states / 4 % 2 == 1
      | "popover-open" => x.states % 2 == 1
      | "modal" => x.states / 2 % 2 == 1
      -- the focused element (`Node.states` bit 8, set by the page's `focus()`); a shadow host
      -- has the focus when an element of its shadow tree has it (Selectors 4 §9.4), and
      -- `:focus-within` reads the shadow-including descendants
      | "focus" | "focus-visible" =>
        x.states / 8 % 2 == 1 ||
          (match x.shadow with
           | some s => (CustomElements.reach d s).any fun j => (d.get j).states / 8 % 2 == 1
           | none => false)
      | "focus-within" => (CustomElements.reach d k).any fun j => (d.get j).states / 8 % 2 == 1
      | "required" => isHtml d k ["input", "select", "textarea"] && (attrVal? d k "required").isSome
      | "optional" => isHtml d k ["input", "select", "textarea"] && (attrVal? d k "required").isNone
      | "read-write" => readWrite d k
      | "read-only" => !readWrite d k
      | "placeholder-shown" =>
        isHtml d k ["input", "textarea"] && (attrVal? d k "placeholder").isSome &&
          ((attrVal? d k "value").getD "").isEmpty && x.kids.isEmpty
      | "default" =>
        (isHtml d k ["input"] && (attrVal? d k "checked").isSome &&
          ["checkbox", "radio"].contains (lowerAscii ((attrVal? d k "type").getD ""))) ||
        (isHtml d k ["option"] && (attrVal? d k "selected").isSome)
      | "indeterminate" => indeterminate d k
      | "open" => isHtml d k ["details", "dialog"] && (attrVal? d k "open").isSome
      -- `:heading` and `:heading(levels)` by the heading level (headingoffset, headingreset)
      | "heading" => (headingLevel d k).isSome
      | "dir(ltr)" => !isRtl d k
      | "dir(rtl)" => isRtl d k
      | _ =>
        if n.startsWith "heading(" then
          match headingLevel d k with
          | some l => (((n.drop 8).dropEnd 1).toString.splitOn ",").any fun t => t.toNat? == some l
          | none => false
        else false
    | .nth kind a b of =>
      let x := d.get k
      if x.parent.isNone then false else
      match of with
      | some l =>
        if (kind == .child || kind == .lastChild) then
          -- `of S`: the element must match S, and its place is among the siblings that do
          let sibs := elementSiblings d k
          let pool := sibs.filter fun c => matchList d scope fuel c l
          match pool.toList.findIdx? (· == k) with
          | none => false
          | some i => nthOk a b (if kind == .child then i + 1 else pool.size - i)
        else
          let same := fun (c : NodeId) => (d.get c).lname == x.lname && (d.get c).ns == x.ns
          match sibPos d k same (kind == .lastOfType) with
          | some pos => nthOk a b pos
          | none => false
      | none =>
        -- the place counted in the parent's child list in place, no sibling array
        let same := fun (c : NodeId) => (d.get c).lname == x.lname && (d.get c).ns == x.ns
        let pred := if kind == .ofType || kind == .lastOfType then same else fun _ => true
        match sibPos d k pred (kind == .lastChild || kind == .lastOfType) with
        | some pos => nthOk a b pos
        | none => false
    | .not l => !matchList d scope fuel k l
    | .is l => matchList d scope fuel k l
    | .has rels => rels.any fun rel => match rel with
      | .mk parts =>
        let comb := (parts.head?.map (·.1)).getD ' '
        (hasCandidates d k comb (parts.length == 1)).any fun e => matchFrom d scope (some k) fuel e parts.reverse
    | .anchors ids => (ids.binSearch k (· < ·)).isSome
    | .lang ranges => match langOf d k with
      | some v => ranges.any fun r =>
          let r := lowerAscii r
          let v := lowerAscii v
          r == "*" || v == r || v.startsWith (r ++ "-")
      | none => false
    | .never => false

def matchCompound (d : Dom) (scope : Option NodeId) : Nat → NodeId → List Simple → Bool
  | 0, _, _ => false
  | fuel + 1, k, c => (d.get k).type == .element && c.all (matchSimple d scope fuel k)

/-- The parts are reversed: the subject first, each with the combinator between it and the
part to its left. -/
def matchFrom (d : Dom) (scope : Option NodeId) (anchor : Option NodeId) : Nat → NodeId → List (Char × List Simple) → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, k, (comb, c) :: rest =>
    if !matchCompound d scope fuel k c then false else
    match rest with
    | [] =>
      -- the leftmost compound: in a relative selector (`:has()`), its combinator is the
      -- relation to the anchor
      match anchor with
      | none => true
      | some a => related d a comb k
    | _ =>
      let up := parentElement d
      let prevEl := prevElement d
      match comb with
      | '>' => match up k with | some p => matchFrom d scope anchor fuel p rest | none => false
      | '+' => match prevEl k with | some p => matchFrom d scope anchor fuel p rest | none => false
      | '~' => Id.run do
        let mut cur := prevEl k
        for _ in [0:d.size + 1] do
          match cur with
          | none => return false
          | some p => if matchFrom d scope anchor fuel p rest then return true else cur := prevEl p
        return false
      | _ => Id.run do
        let mut cur := up k
        for _ in [0:d.size + 1] do
          match cur with
          | none => return false
          | some p => if matchFrom d scope anchor fuel p rest then return true else cur := up p
        return false

/-- A complex selector, matched from its subject (the last compound) leftwards. -/
def matchComplex (d : Dom) (scope : Option NodeId) : Nat → NodeId → Complex → Bool
  | 0, _, _ => false
  | fuel + 1, k, .mk parts => matchFrom d scope none fuel k parts.reverse

def matchList (d : Dom) (scope : Option NodeId) : Nat → NodeId → List Complex → Bool
  | 0, _, _ => false
  | fuel + 1, k, l => l.any (matchComplex d scope fuel k)
end

/-- The pseudo-element a complex selector's subject names (`::before` is "before"), if any. -/
def Complex.pseudoElement : Complex → Option String
  | .mk parts =>
    match parts.getLast? with
    | some (_, c) => c.findSome? fun s => match s with
      | .pseudo n => if n.startsWith "::" then some (n.drop 2).toString else none
      | _ => none
    | none => none

/-- Whether `c` selects pseudo-element `pe` of element `k` (CSS Pseudo-Elements 4 §2): its
subject names `pe`, and the rest of the subject compound and the compounds before it match
`k` and its relatives. -/
def matchesPseudo (d : Dom) (k : NodeId) (c : Complex) (pe : String) : Bool :=
  c.pseudoElement == some pe &&
    match c with
    | .mk parts =>
      match parts.reverse with
      | (comb, last) :: before =>
        let last' := last.filter fun s => match s with
          | .never => false
          | .pseudo n => !n.startsWith "::"
          | _ => true
        (d.get k).type == .element && matchComplex d none matchFuel k (.mk ((comb, last') :: before).reverse)
      | [] => false

/-- `element.matches(selectors)` with `scope` the element (DOM §4.9). -/
def elementMatches (d : Dom) (k : NodeId) (l : List Complex) : Bool :=
  (d.get k).type == .element && matchList d (some k) matchFuel k l

/-- `querySelectorAll(selectors)` (DOM §4.2.6): the descendant elements of `root` that
match, in tree order, with `root` as the scoping root. -/
def querySelectorAll (d : Dom) (root : NodeId) (l : List Complex) (first : Bool := false) : Array NodeId := Id.run do
  let mut out := #[]
  for k in d.treeOrder root false do
    if (d.get k).type == .element && matchList d (some root) matchFuel k l then
      out := out.push k
      if first then return out
  return out

/-- `element.closest(selectors)` (DOM §4.9): the first inclusive ancestor element that
matches, with the element as the scope. -/
def closest (d : Dom) (k : NodeId) (l : List Complex) : Option NodeId := Id.run do
  let mut cur := some k
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some p =>
      if (d.get p).type != .element then return none
      if matchList d (some k) matchFuel p l then return some p
      cur := (d.get p).parent
  return none

/-! ## Tests: the pseudo-classes of element states (`Node.states`, `Node.checkedness`) -/

/-- Document 0 > `div[popover]` (1) showing, `dialog` (2) modal, `my-el` (3) not defined,
`my-el` (4) defined, `input[type=checkbox]` (5) checked by script, `option[selected]` (6)
unselected by script. -/
private def stateTree : Dom :=
  let el := fun (lname : String) (attrs : List (String × String)) (states : Nat) (checked : Option Bool) =>
    ({ type := .element, ns := some htmlNS, lname, parent := some 0, states, checkedness := checked,
       attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray } : Node)
  { nodes := #[{ type := .document, kids := #[1, 2, 3, 4, 5, 6] },
      el "div" [("popover", "")] 1 none, el "dialog" [("open", "")] 2 none, el "my-el" [] 0 none, el "my-el" [] 4 none,
      el "input" [("type", "checkbox")] 0 (some true), el "option" [("selected", "")] 0 (some false)] }

private def matchesSel (k : NodeId) (sel : String) : Bool :=
  match parse sel with
  | some l => elementMatches stateTree k l
  | none => false

#guard matchesSel 1 ":popover-open" && !matchesSel 2 ":popover-open" && !matchesSel 3 ":popover-open"
#guard matchesSel 2 ":modal" && !matchesSel 1 ":modal"
#guard matchesSel 1 ":defined" && !matchesSel 3 ":defined" && matchesSel 4 ":defined" && matchesSel 3 ":not(:defined)"
#guard matchesSel 5 ":checked" && !matchesSel 6 ":checked"
#guard !matchesSel 1 ":focus" && !matchesSel 1 ":focus-within"
#guard elementMatches ({ nodes := stateTree.nodes.modify 1 fun n => { n with states := 9 } } : Dom) 1 ((parse ":focus").getD []) &&
  elementMatches ({ nodes := stateTree.nodes.modify 1 fun n => { n with states := 9 } } : Dom) 1 ((parse ":focus-within:popover-open").getD [])

end L4Factoidal.DOM.Selectors
