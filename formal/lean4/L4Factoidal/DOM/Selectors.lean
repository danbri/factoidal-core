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
node of the document.
-/
import L4Factoidal.DOM.Arena

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
  | lang (ranges : List String)
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
def preprocess (s : String) : Array Char := Id.run do
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

structure P where
  cs : Array Char
  i : Nat := 0

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
def plainPseudoClasses : List String :=
  ["root", "empty", "first-child", "last-child", "only-child", "first-of-type", "last-of-type",
   "only-of-type", "scope", "link", "any-link", "checked", "disabled", "enabled", "hover", "active",
   "focus", "focus-within", "focus-visible", "visited", "target", "defined"]

/-- The most compound selectors in one complex selector, and the deepest nesting of
`:not()`, `:is()` and `:nth-child(… of …)`: matching recurses once per compound and once
per nesting level, so these bound its stack. A longer selector is refused as invalid. -/
def maxCompounds : Nat := 1024
def maxNesting : Nat := 32

mutual
/-- A selector list: complex selectors separated by commas. `depth` bounds nesting. -/
partial def selectorList (depth : Nat) : PM (List Complex) := do
  if depth == 0 then fail
  let mut out := #[]
  for _ in [0:(← get).cs.size + 1] do
    let _ ← skipWs
    out := out.push (← complex depth)
    let _ ← skipWs
    match ← peek with
    | some ',' => bump
    | _ => break
  return out.toList

partial def complex (depth : Nat) : PM Complex := do
  let mut parts : Array (Char × List Simple) := #[]
  let mut comb := ' '
  for _ in [0:(← get).cs.size + 1] do
    let c ← compound depth
    parts := parts.push (comb, c)
    -- a bound on the compounds of one complex selector: matching recurses once per compound
    if parts.size > maxCompounds then fail
    let ws ← skipWs
    match ← peek with
    | some ',' | some ')' | none => break
    | some c =>
      if c == '>' || c == '+' || c == '~' then
        bump
        comb := c
        let _ ← skipWs
      else if ws then comb := ' '
      else fail
  return .mk parts.toList

partial def compound (depth : Nat) : PM (List Simple) := do
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
  for _ in [0:(← get).cs.size + 1] do
    match ← peek with
    | some '#' =>
      bump
      if !(← startsIdent) then
        -- a hash token may start with a digit or "-" + digit in CSS, but an ID selector
        -- needs an identifier
        fail
      out := out.push (.id (← ident))
    | some '.' =>
      bump
      out := out.push (.cls (← ident))
    | some '[' =>
      bump
      out := out.push (← attrSel)
    | some ':' =>
      bump
      if (← peek) == some ':' then
        bump
        let n := lowerAscii (← ident)
        if legacyPseudoElements.contains n then out := out.push .never else fail
      else
        let n := lowerAscii (← ident)
        if (← peek) == some '(' then
          bump
          let _ ← skipWs
          match n with
          | "not" =>
            let l ← selectorList (depth - 1)
            let _ ← skipWs
            expectClose
            out := out.push (.not l)
          | "is" | "where" | "matches" | "-webkit-any" =>
            let l ← selectorList (depth - 1)
            let _ ← skipWs
            expectClose
            out := out.push (.is l)
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
              let l ← selectorList (depth - 1)
              let _ ← skipWs
              expectClose
              out := out.push (.nth kind a b (some l))
            else
              bump
              out := out.push (.nth kind a b none)
          | _ => fail
        else if legacyPseudoElements.contains n then out := out.push .never
        else if plainPseudoClasses.contains n then out := out.push (.pseudo n)
        else fail
    | _ => break
  if (← get).i == start then fail
  return out.toList

partial def expectClose : PM Unit := do
  if (← peek) == some ')' then bump else fail

partial def attrSel : PM Simple := do
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
end

/-- Parse a selectors string; `none` when it is invalid (a SyntaxError). -/
def parse (s : String) : Option (List Complex) :=
  match (do
      let l ← selectorList maxNesting
      let _ ← skipWs
      if !(← atEnd) then fail
      return l : PM (List Complex)).run { cs := preprocess s } with
  | .ok (l, _) => some l
  | .error _ => none

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

def wsSplit (s : String) : List String :=
  (s.map fun c => if c == '\t' || c == '\n' || c == '\x0C' || c == '\r' then ' ' else c).splitOn " " |>.filter (· != "")

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

mutual
partial def matchSimple (d : Dom) (scope : Option NodeId) (k : NodeId) : Simple → Bool
  | .type ns name =>
    let x := d.get k
    let nsOk := match ns with
      | .default | .any => true
      | .none => x.ns.isNone
    nsOk && match name with
      | none => true
      | some n => x.lname == (if htmlOf d k then lowerAscii n else n)
  | .id v => (d.get k).attrs.any fun a => a.ns.isNone && a.lname == "id" && a.value == v
  | .cls v => match attrVal? d k "class" with
    | some c => (wsSplit c).contains v
    | none => false
  | .attr ns name op value ci cs =>
    let ins := ci || (!cs && htmlOf d k && caseInsensitiveAttrs.contains (lowerAscii name))
    (attrsMatching d k ns name).any fun a =>
      if ins then attrValueMatches op (lowerAscii a.value) (lowerAscii value) else attrValueMatches op a.value value
  | .pseudo n =>
    let x := d.get k
    let sibs := elementSiblings d k
    let sameType := sibs.filter fun c => (d.get c).lname == x.lname && (d.get c).ns == x.ns
    match n with
    | "root" => match x.parent with | some p => (d.get p).type == .document | none => false
    | "empty" => x.kids.all fun c =>
        let y := d.get c
        y.type != .element && !((y.type == .text || y.type == .cdata) && !y.data.isEmpty)
    | "first-child" => x.parent.isSome && sibs[0]? == some k
    | "last-child" => x.parent.isSome && sibs.back? == some k
    | "only-child" => x.parent.isSome && sibs.size == 1
    | "first-of-type" => x.parent.isSome && sameType[0]? == some k
    | "last-of-type" => x.parent.isSome && sameType.back? == some k
    | "only-of-type" => x.parent.isSome && sameType.size == 1
    | "scope" => match scope with | some s => s == k | none => x.parent.any fun p => (d.get p).type == .document
    | "link" | "any-link" => isHtml d k ["a", "area"] && (attrVal? d k "href").isSome
    | "checked" =>
      (isHtml d k ["input"] && (attrVal? d k "checked").isSome &&
        ["checkbox", "radio"].contains (lowerAscii ((attrVal? d k "type").getD ""))) ||
      (isHtml d k ["option"] && (attrVal? d k "selected").isSome)
    | "disabled" => disabledEl d k
    | "enabled" => isHtml d k ["button", "input", "select", "textarea", "optgroup", "option", "fieldset"] && !disabledEl d k
    | "defined" => true
    | _ => false
  | .nth kind a b of =>
    let x := d.get k
    if x.parent.isNone then false else
    let sibs := elementSiblings d k
    let pool := match kind, of with
      | .child, some l | .lastChild, some l => sibs.filter fun c => matchList d scope c l
      | .ofType, _ | .lastOfType, _ => sibs.filter fun c => (d.get c).lname == x.lname && (d.get c).ns == x.ns
      | _, _ => sibs
    match pool.toList.findIdx? (· == k) with
    | none => false
    | some i =>
      let pos := match kind with | .child | .ofType => i + 1 | _ => pool.size - i
      nthOk a b pos
  | .not l => !matchList d scope k l
  | .is l => matchList d scope k l
  | .lang ranges => match langOf d k with
    | some v => ranges.any fun r =>
        let r := lowerAscii r
        let v := lowerAscii v
        r == "*" || v == r || v.startsWith (r ++ "-")
    | none => false
  | .never => false

partial def matchCompound (d : Dom) (scope : Option NodeId) (k : NodeId) (c : List Simple) : Bool :=
  (d.get k).type == .element && c.all (matchSimple d scope k)

/-- The parts are reversed: the subject first, each with the combinator between it and the
part to its left. -/
partial def matchFrom (d : Dom) (scope : Option NodeId) (k : NodeId) : List (Char × List Simple) → Bool
  | [] => true
  | (comb, c) :: rest =>
    if !matchCompound d scope k c then false else
    match rest with
    | [] => true
    | _ =>
      let up := fun (n : NodeId) => (d.get n).parent.bind fun p => if (d.get p).type == .element then some p else none
      let prevEl := fun (n : NodeId) =>
        let sibs := elementSiblings d n
        match sibs.toList.findIdx? (· == n) with
        | some i => if i == 0 then none else sibs[i - 1]?
        | none => none
      match comb with
      | '>' => match up k with | some p => matchFrom d scope p rest | none => false
      | '+' => match prevEl k with | some p => matchFrom d scope p rest | none => false
      | '~' => Id.run do
        let mut cur := prevEl k
        for _ in [0:d.size + 1] do
          match cur with
          | none => return false
          | some p => if matchFrom d scope p rest then return true else cur := prevEl p
        return false
      | _ => Id.run do
        let mut cur := up k
        for _ in [0:d.size + 1] do
          match cur with
          | none => return false
          | some p => if matchFrom d scope p rest then return true else cur := up p
        return false

/-- A complex selector, matched from its subject (the last compound) leftwards. -/
partial def matchComplex (d : Dom) (scope : Option NodeId) (k : NodeId) (c : Complex) : Bool :=
  match c with
  | .mk parts => matchFrom d scope k parts.reverse

partial def matchList (d : Dom) (scope : Option NodeId) (k : NodeId) (l : List Complex) : Bool :=
  l.any (matchComplex d scope k)
end

/-- `element.matches(selectors)` with `scope` the element (DOM §4.9). -/
def elementMatches (d : Dom) (k : NodeId) (l : List Complex) : Bool :=
  (d.get k).type == .element && matchList d (some k) k l

/-- `querySelectorAll(selectors)` (DOM §4.2.6): the descendant elements of `root` that
match, in tree order, with `root` as the scoping root. -/
def querySelectorAll (d : Dom) (root : NodeId) (l : List Complex) (first : Bool := false) : Array NodeId := Id.run do
  let mut out := #[]
  for k in d.treeOrder root false do
    if (d.get k).type == .element && matchList d (some root) k l then
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
      if matchList d (some k) p l then return some p
      cur := (d.get p).parent
  return none

end L4Factoidal.DOM.Selectors
