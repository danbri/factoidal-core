/-
L4Factoidal.XPath4.Ixml — `fn:invisible-xml` (F&O 4.0 §14.8.x, "Invisible
XML"), over Invisible XML 1.0 (https://invisiblexml.org/1.0/, 2022-06-20).

* An ixml grammar is a list of rules (`Rule`) over factors (`Factor`). A
  grammar written as text is parsed by the Earley parser below with the ixml
  grammar of the ixml 1.0 specification (`ixmlGrammarText`, the file
  https://invisiblexml.org/1.0/ixml.ixml, version 2022-06-07), which gives its
  XML form; the XML form (from that parse, or given as an `element(Q{}ixml)`)
  is then read into the `Rule` list (`grammarOfXml`). The ixml grammar itself
  is read once by a small recursive-descent parser (`Boot`), with fuel.
* `compile` turns the rules into plain context-free productions over
  character classes: groups, options and repetitions become new hidden
  nonterminals (left-recursive for the repetitions), and a string literal
  becomes one terminal per character.
* `recognize` is an Earley recognizer (Earley 1970) with the nullable
  prediction rule of Aycock and Horspool (2002), over Unicode code points.
  It accepts every context-free grammar, ambiguous and left-recursive ones
  included.
* `buildTree` walks the chart from the root down, with an explicit task
  stack (no stack frame per tree node), and chooses the first derivation at
  each node. When a node has more than one derivation (or a derivation
  through a cycle), the input is ambiguous and the root gets
  `ixml:state="ambiguous"`. The tree is serialized while it is built, per
  ixml 1.0 §"Parse trees and their serialization": a nonterminal marked `^`
  is an element, `@` an attribute whose value is the text of its subtree,
  `-` is replaced by its content; a terminal marked `-` is dropped; an
  insertion is text.
* On failure the result is a document whose root element has
  `ixml:state="failed"` and says where the parse stopped; with the option
  `fail-on-error` it is the error FOIX0002. A grammar that does not parse or
  is not valid (a nonterminal with no rule, a rule defined twice, a bad
  class, range or hex value) is the error FOIX0001.

The class tables are the General_Category tables of `Regex.UnicodeProps`
(Unicode 16.0.0), through `Regex.XPath40.categoryRanges`.
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.Regex.XPath40
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.XPath4.Ixml

open L4Factoidal.XML

def nsIxml : String := "http://invisiblexml.org/NS"

/-! ## Grammars -/

/-- The mark of a nonterminal (ixml 1.0 `@mark`). -/
inductive Mark where
  | attr | elem | hide
deriving DecidableEq, Repr, Inhabited

def Mark.ofString? : String → Option Mark
  | "@" => some .attr | "^" => some .elem | "-" => some .hide | _ => none

/-- A member of a character set. -/
inductive Member where
  | chars (cs : List Nat)
  | range (lo hi : Nat)
  | cls (code : String)
deriving Repr, Inhabited

inductive Factor where
  | nt (mark : Option Mark) (name : String)
  /-- A string or hex literal; `hidden` for the tmark `-`. -/
  | lit (hidden : Bool) (cs : List Nat)
  | cset (hidden : Bool) (excl : Bool) (ms : List Member)
  | ins (s : String)
  | grp (alts : List (List Factor))
  | rep0 (f : Factor) (sep : Option Factor)
  | rep1 (f : Factor) (sep : Option Factor)
  | opt (f : Factor)
deriving Inhabited

structure Rule where
  mark : Option Mark
  name : String
  alts : List (List Factor)
deriving Inhabited

def ixmlGrammarText : String := String.join [
  "{version 2022-06-07}\n",
  "         ixml: s, prolog?, rule++RS, s.\n",
  "           -s: (whitespace; comment)*. {Optional spacing}\n",
  "          -RS: (whitespace; comment)+. {Required spacing}\n",
  "  -whitespace: -[Zs]; tab; lf; cr.\n",
  "         -tab: -#9.\n",
  "          -lf: -#a.\n",
  "          -cr: -#d.\n",
  "      comment: -\"{\", (cchar; comment)*, -\"}\".\n",
  "       -cchar: ~[\"{}\"].\n",
  "       prolog: version, s.\n",
  "      version: -\"ixml\", RS, -\"version\", RS, string, s, -'.' .\n",
  "         rule: (mark, s)?, name, s, -[\"=:\"], s, -alts, -\".\".\n",
  "        @mark: [\"@^-\"].\n",
  "         alts: alt++(-[\";|\"], s).\n",
  "          alt: term**(-\",\", s).\n",
  "        -term: factor;\n",
  "               option;\n",
  "               repeat0;\n",
  "               repeat1.\n",
  "      -factor: terminal;\n",
  "               nonterminal;\n",
  "               insertion;\n",
  "               -\"(\", s, alts, -\")\", s.\n",
  "      repeat0: factor, (-\"*\", s; -\"**\", s, sep).\n",
  "      repeat1: factor, (-\"+\", s; -\"++\", s, sep).\n",
  "       option: factor, -\"?\", s.\n",
  "          sep: factor.\n",
  "  nonterminal: (mark, s)?, name, s.\n",
  "        @name: namestart, namefollower*.\n",
  "   -namestart: [\"_\"; L].\n",
  "-namefollower: namestart; [\"-.·‿⁀\"; Nd; Mn].\n",
  "    -terminal: literal; \n",
  "               charset.\n",
  "      literal: quoted;\n",
  "               encoded.\n",
  "      -quoted: (tmark, s)?, string, s.\n",
  "       @tmark: [\"^-\"].\n",
  "      @string: -'\"', dchar+, -'\"';\n",
  "               -\"'\", schar+, -\"'\".\n",
  "        dchar: ~['\"'; #a; #d];\n",
  "               '\"', -'\"'. {all characters except line breaks; quotes must be doubled}\n",
  "        schar: ~[\"'\"; #a; #d];\n",
  "               \"'\", -\"'\". {all characters except line breaks; quotes must be doubled}\n",
  "     -encoded: (tmark, s)?, -\"#\", hex, s.\n",
  "         @hex: [\"0\"-\"9\"; \"a\"-\"f\"; \"A\"-\"F\"]+.\n",
  "     -charset: inclusion; \n",
  "               exclusion.\n",
  "    inclusion: (tmark, s)?,          set.\n",
  "    exclusion: (tmark, s)?, -\"~\", s, set.\n",
  "         -set: -\"[\", s,  (member, s)**(-[\";|\"], s), -\"]\", s.\n",
  "       member: string;\n",
  "               -\"#\", hex;\n",
  "               range;\n",
  "               class.\n",
  "       -range: from, s, -\"-\", s, to.\n",
  "        @from: character.\n",
  "          @to: character.\n",
  "   -character: -'\"', dchar, -'\"';\n",
  "               -\"'\", schar, -\"'\";\n",
  "               \"#\", hex.\n",
  "       -class: code.\n",
  "        @code: capital, letter?.\n",
  "     -capital: [\"A\"-\"Z\"].\n",
  "      -letter: [\"a\"-\"z\"].\n",
  "    insertion: -\"+\", s, (string; -\"#\", hex), s.\n"]


/-! ## The bootstrap parser

A recursive-descent parser for the ixml syntax, used once, for
`ixmlGrammarText`. Every other grammar text is parsed by the Earley parser
with the grammar this parser reads. The recursion is on the nesting of
parentheses only (with fuel); lists are loops. -/

namespace Boot

abbrev P := StateT Nat (Except String)

def peek (cs : Array Char) : P (Option Char) := do pure cs[(← get)]?

def adv : P Unit := modify (· + 1)

def isWsC (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- `s`: whitespace and (nested) comments. -/
def skipS (cs : Array Char) : P Unit := do
  let mut depth := 0
  for _ in [0:cs.size + 1] do
    match cs[(← get)]? with
    | none => break
    | some c =>
      if depth > 0 then
        if c == '{' then depth := depth + 1
        else if c == '}' then depth := depth - 1
        adv
      else if c == '{' then depth := 1; adv
      else if isWsC c then adv
      else break
  if depth > 0 then throw "unterminated comment"

def expect (cs : Array Char) (c : Char) : P Unit := do
  if (← peek cs) == some c then adv else throw s!"expected {c} at {← get}"

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `hex` after `#`. -/
def pHex (cs : Array Char) : P Nat := do
  let mut v := 0
  let mut k := 0
  for _ in [0:cs.size + 1] do
    match (← peek cs).bind hexDigit? with
    | some d => v := v * 16 + d; k := k + 1; adv
    | none => break
  if k == 0 then throw "expected a hex digit"
  pure v

/-- A quoted string; a doubled quote stands for one. -/
def pString (cs : Array Char) : P (List Nat) := do
  let some q ← peek cs | throw "expected a string"
  adv
  let mut out : Array Nat := #[]
  for _ in [0:cs.size + 1] do
    match ← peek cs with
    | none => throw "unterminated string"
    | some c =>
      if c == q then
        adv
        if (← peek cs) == some q then out := out.push c.toNat; adv
        else return out.toList
      else if c == '\n' || c == '\r' then throw "line break in a string"
      else out := out.push c.toNat; adv
  throw "unterminated string"

def isNameStart (c : Char) : Bool := c.isAlpha || c == '_'
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_'

def pName (cs : Array Char) : P String := do
  let some c ← peek cs | throw "expected a name"
  if !isNameStart c then throw s!"expected a name at {← get}"
  let mut out := ""
  for _ in [0:cs.size + 1] do
    match ← peek cs with
    | some c => if isNameChar c then out := out.push c; adv else break
    | none => break
  pure out

/-- A string or `#hex`, as code points. -/
def pStrOrHex (cs : Array Char) : P (List Nat) := do
  if (← peek cs) == some '#' then adv; pure [← pHex cs] else pString cs

/-- `set`: `[` members `]`. -/
def pSet (cs : Array Char) : P (List Member) := do
  expect cs '['
  skipS cs
  let mut ms : Array Member := #[]
  for _ in [0:cs.size + 1] do
    match ← peek cs with
    | some ']' => adv; skipS cs; return ms.toList
    | some ';' | some '|' => adv; skipS cs
    | some '"' | some '\'' | some '#' =>
      let lo ← pStrOrHex cs
      skipS cs
      if (← peek cs) == some '-' then
        adv; skipS cs
        let hi ← pStrOrHex cs
        match lo, hi with
        | [a], [b] => ms := ms.push (.range a b)
        | _, _ => throw "a range needs single characters"
      else ms := ms.push (.chars lo)
      skipS cs
    | some c =>
      if 'A' ≤ c && c ≤ 'Z' then
        adv
        let mut code := String.singleton c
        match ← peek cs with
        | some d => if 'a' ≤ d && d ≤ 'z' then code := code.push d; adv
        | none => pure ()
        ms := ms.push (.cls code)
        skipS cs
      else throw s!"unexpected {c} in a set"
    | none => throw "unterminated set"
  throw "unterminated set"

mutual
def pAlts (cs : Array Char) : Nat → P (List (List Factor))
  | 0 => throw "too deep"
  | f + 1 => do
    let mut out : Array (List Factor) := #[]
    for _ in [0:cs.size + 1] do
      out := out.push (← pAlt cs f)
      match ← peek cs with
      | some ';' | some '|' => adv; skipS cs
      | _ => break
    pure out.toList

def pAlt (cs : Array Char) : Nat → P (List Factor)
  | 0 => throw "too deep"
  | f + 1 => do
    match ← peek cs with
    | some ';' | some '|' | some ')' | some '.' => return []
    | _ => pure ()
    let mut out : Array Factor := #[]
    for _ in [0:cs.size + 1] do
      out := out.push (← pTerm cs f)
      match ← peek cs with
      | some ',' => adv; skipS cs
      | _ => break
    pure out.toList

def pTerm (cs : Array Char) : Nat → P Factor
  | 0 => throw "too deep"
  | f + 1 => do
    let x ← pFactor cs f
    match ← peek cs with
    | some '*' =>
      adv
      if (← peek cs) == some '*' then
        adv; skipS cs; pure (.rep0 x (some (← pFactor cs f)))
      else skipS cs; pure (.rep0 x none)
    | some '+' =>
      adv
      if (← peek cs) == some '+' then
        adv; skipS cs; pure (.rep1 x (some (← pFactor cs f)))
      else skipS cs; pure (.rep1 x none)
    | some '?' => adv; skipS cs; pure (.opt x)
    | _ => pure x

def pFactor (cs : Array Char) : Nat → P Factor
  | 0 => throw "too deep"
  | f + 1 => do
    match ← peek cs with
    | some '(' =>
      adv; skipS cs
      let a ← pAlts cs f
      expect cs ')'; skipS cs
      pure (.grp a)
    | some '+' =>
      adv; skipS cs
      let s ← pStrOrHex cs
      skipS cs
      pure (.ins (String.ofList (s.map Char.ofNat)))
    | _ =>
      let mk : Option Mark ← match ← peek cs with
        | some '@' => do adv; skipS cs; pure (some Mark.attr)
        | some '^' => do adv; skipS cs; pure (some Mark.elem)
        | some '-' => do adv; skipS cs; pure (some Mark.hide)
        | _ => pure none
      let hidden := mk == some Mark.hide
      match ← peek cs with
      | some '"' | some '\'' | some '#' =>
        let s ← pStrOrHex cs
        skipS cs
        pure (.lit hidden s)
      | some '[' => pure (.cset hidden false (← pSet cs))
      | some '~' => adv; skipS cs; pure (.cset hidden true (← pSet cs))
      | _ =>
        let n ← pName cs
        skipS cs
        pure (.nt mk n)
end

def pRule (cs : Array Char) : P Rule := do
  let mk : Option Mark ← match ← peek cs with
    | some c => match Mark.ofString? (String.singleton c) with
      | some m => do adv; skipS cs; pure (some m)
      | none => pure none
    | none => pure none
  let n ← pName cs
  skipS cs
  match ← peek cs with
  | some '=' | some ':' => adv
  | _ => throw s!"expected = or : at {← get}"
  skipS cs
  let alts ← pAlts cs 64
  expect cs '.'
  skipS cs
  pure { mark := mk, name := n, alts }

def pGrammar (cs : Array Char) : P (List Rule) := do
  skipS cs
  let mut rs : Array Rule := #[]
  for _ in [0:cs.size + 1] do
    if (← get) ≥ cs.size then break
    rs := rs.push (← pRule cs)
  pure rs.toList

def parse (s : String) : Except String (List Rule) :=
  (pGrammar s.toList.toArray).run' 0

end Boot

/-! ## Productions -/

/-- A terminal: a set of code points, as sorted disjoint ranges, or its
    complement. -/
structure CharClass where
  excl : Bool
  ranges : Array (Nat × Nat)
deriving Inhabited

/-- Binary search over sorted disjoint ranges. -/
def inRanges (rs : Array (Nat × Nat)) (x : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b) := rs.getD mid (0, 0)
    if x < a then hi := mid
    else if x > b then lo := mid + 1
    else return true
  return false

def CharClass.matches (c : CharClass) (x : Nat) : Bool := inRanges c.ranges x != c.excl

/-- An exclusion matches exactly the code points its inclusion does not. -/
theorem CharClass.matches_excl (r : Array (Nat × Nat)) (x : Nat) :
    ({ excl := true, ranges := r } : CharClass).matches x =
      !({ excl := false, ranges := r } : CharClass).matches x := by
  cases h : inRanges r x <;> simp [CharClass.matches, h]

inductive Sym where
  /-- A nonterminal with the mark it is serialized with. -/
  | nt (id : Nat) (mark : Mark)
  | tm (id : Nat) (hidden : Bool)
  | ins (s : String)
deriving Inhabited

structure Prod where
  lhs : Nat
  rhs : Array Sym
deriving Inhabited

structure BNF where
  names : Array String
  prods : Array Prod
  byLhs : Array (Array Nat)
  terms : Array CharClass
  nullable : Array Bool
  rootMark : Mark
deriving Inhabited

structure CState where
  names : Array String
  prods : Array Prod := #[]
  terms : Array CharClass := #[]

abbrev CM := StateT CState (Except String)

def newNT : CM Nat := do
  let s ← get
  set { s with names := s.names.push "" }
  pure s.names.size

def addProd (l : Nat) (rhs : Array Sym) : CM Unit :=
  modify fun s => { s with prods := s.prods.push { lhs := l, rhs } }

def addTerm (c : CharClass) : CM Nat := do
  let s ← get
  set { s with terms := s.terms.push c }
  pure s.terms.size

def validCp (n : Nat) : Bool := n ≤ 0x10FFFF && !(0xD800 ≤ n && n ≤ 0xDFFF)

def memberRanges (m : Member) : Except String (List (Nat × Nat)) :=
  match m with
  | .chars cs => if cs.all validCp then .ok (cs.map fun c => (c, c)) else .error "invalid character"
  | .range a b =>
    if !(validCp a && validCp b) then .error "invalid character in a range"
    else if a > b then .error "a range whose first character is after its last"
    else .ok [(a, b)]
  | .cls code => match Regex.XPath40.categoryRanges code with
    | some rs => .ok rs
    | none => .error ("unknown character class " ++ code)

def liftE {α} (x : Except String α) : CM α :=
  match x with
  | .ok v => pure v
  | .error e => throw e

def compileFactor (env : Std.HashMap String (Nat × Mark)) : Nat → Factor → CM (Array Sym)
  | 0, _ => throw "grammar too deep"
  | f + 1, x => match x with
    | .nt mk n => match env.get? n with
      | some (i, rm) => pure #[.nt i (mk.getD rm)]
      | none => throw ("no rule for the nonterminal " ++ n)
    | .lit h cs => do
      if !cs.all validCp then throw "invalid character in a literal"
      let mut out := #[]
      for c in cs do
        out := out.push (.tm (← addTerm { excl := false, ranges := #[(c, c)] }) h)
      pure out
    | .cset h ex ms => do
      let mut rs := []
      for m in ms do rs := rs ++ (← liftE (memberRanges m))
      let t ← addTerm { excl := ex, ranges := (Text.CaseMap.normalizeRanges rs).toArray }
      pure #[.tm t h]
    | .ins s => pure #[.ins s]
    | .grp alts => do
      let g ← newNT
      for a in alts do
        let mut syms := #[]
        for y in a do syms := syms ++ (← compileFactor env f y)
        addProd g syms
      pure #[.nt g .hide]
    | .opt y => do
      let o ← newNT
      let ys ← compileFactor env f y
      addProd o #[]
      addProd o ys
      pure #[.nt o .hide]
    | .rep1 y sep => do
      let r ← newNT
      let ys ← compileFactor env f y
      let ss ← match sep with
        | some s => compileFactor env f s
        | none => pure #[]
      addProd r ys
      addProd r ((#[Sym.nt r .hide] ++ ss) ++ ys)
      pure #[.nt r .hide]
    | .rep0 y sep => do
      let r ← newNT
      let ys ← compileFactor env f y
      let ss ← match sep with
        | some s => compileFactor env f s
        | none => pure #[]
      addProd r ys
      addProd r ((#[Sym.nt r .hide] ++ ss) ++ ys)
      let o ← newNT
      addProd o #[]
      addProd o #[.nt r .hide]
      pure #[.nt o .hide]

/-- Productions of a grammar. Nonterminal `i < rules.length` is rule `i`;
    nonterminal 0 is the start symbol. -/
def compile (rules : List Rule) : Except String BNF := do
  if rules.isEmpty then throw "a grammar has at least one rule"
  let mut env : Std.HashMap String (Nat × Mark) := {}
  let mut i := 0
  for r in rules do
    if env.contains r.name then throw ("the rule " ++ r.name ++ " is defined twice")
    env := env.insert r.name (i, r.mark.getD .elem)
    i := i + 1
  let act : CM Unit := do
    let mut k := 0
    for r in rules do
      for a in r.alts do
        let mut syms := #[]
        for y in a do syms := syms ++ (← compileFactor env 256 y)
        addProd k syms
      k := k + 1
  let ((), st) ← act.run { names := (rules.map (·.name)).toArray }
  let nn := st.names.size
  let mut byLhs : Array (Array Nat) := Array.replicate nn #[]
  for j in [0:st.prods.size] do
    let p := st.prods.getD j default
    byLhs := byLhs.modify p.lhs (·.push j)
  let mut nul : Array Bool := Array.replicate nn false
  for _ in [0:nn + 1] do
    let mut changed := false
    for p in st.prods do
      if nul.getD p.lhs false then continue
      if p.rhs.all (fun s => match s with
          | .ins _ => true | .tm _ _ => false | .nt b _ => nul.getD b false) then
        nul := nul.set! p.lhs true
        changed := true
    if !changed then break
  pure { names := st.names, prods := st.prods, byLhs, terms := st.terms, nullable := nul,
         rootMark := (rules.head?.bind (·.mark)).getD .elem }

/-! ## The Earley recognizer -/

structure Item where
  prod : Nat
  dot : Nat
  orig : Nat
deriving BEq, Hashable, Inhabited

structure Chart where
  sets : Array (Array Item)
  seen : Array (Std.HashSet Item)
  /-- Per set: the items whose next symbol is a nonterminal, by it. -/
  wait : Array (Std.HashMap Nat (Array Item))

def Chart.add (ch : Chart) (g : BNF) (i : Nat) (it : Item) : Chart :=
  if (ch.seen.getD i {}).contains it then ch
  else
    let seen := ch.seen.modify i (·.insert it)
    let sets := ch.sets.modify i (·.push it)
    let wait := match ((g.prods.getD it.prod default).rhs)[it.dot]? with
      | some (.nt b _) => ch.wait.modify i (fun m => m.insert b ((m.getD b #[]).push it))
      | _ => ch.wait
    { sets, seen, wait }

def BNF.dots (g : BNF) : Nat := g.prods.foldl (fun n p => n + p.rhs.size + 1) 0

/-- The chart, and the last position whose set is not empty. -/
def recognize (g : BNF) (inp : Array Nat) : Chart × Nat := Id.run do
  let n := inp.size
  let mut ch : Chart := { sets := Array.replicate (n + 1) #[], seen := Array.replicate (n + 1) {},
                          wait := Array.replicate (n + 1) {} }
  for q in g.byLhs.getD 0 #[] do ch := ch.add g 0 ⟨q, 0, 0⟩
  let mut last := 0
  let dots := g.dots
  for i in [0:n + 1] do
    if (ch.sets.getD i #[]).isEmpty then break
    last := i
    let mut j := 0
    for _ in [0:dots * (i + 1) + 1] do
      let set := ch.sets.getD i #[]
      if h : j < set.size then
        let it := set[j]
        j := j + 1
        let p := g.prods.getD it.prod default
        match p.rhs[it.dot]? with
        | none =>
          for w in (ch.wait.getD it.orig {}).getD p.lhs #[] do
            ch := ch.add g i { w with dot := w.dot + 1 }
        | some (.nt b _) =>
          for q in g.byLhs.getD b #[] do ch := ch.add g i ⟨q, 0, i⟩
          if g.nullable.getD b false then ch := ch.add g i { it with dot := it.dot + 1 }
        | some (.tm t _) =>
          if h2 : i < n then
            if (g.terms.getD t default).matches inp[i] then
              ch := ch.add g (i + 1) { it with dot := it.dot + 1 }
        | some (.ins _) => ch := ch.add g i { it with dot := it.dot + 1 }
      else break
  (ch, last)

def BNF.accepts (g : BNF) (ch : Chart) (n : Nat) : Bool :=
  (g.byLhs.getD 0 #[]).any fun q =>
    (ch.seen.getD n {}).contains ⟨q, (g.prods.getD q default).rhs.size, 0⟩

/-! ## Tree building and serialization -/

/-- The completed items of each set: `(nonterminal, origin) ↦ productions`,
    and `nonterminal ↦ origins`. -/
structure Done where
  prods : Array (Std.HashMap (Nat × Nat) (Array Nat))
  origs : Array (Std.HashMap Nat (Array Nat))

def mkDone (g : BNF) (ch : Chart) : Done := Id.run do
  let mut ps : Array (Std.HashMap (Nat × Nat) (Array Nat)) := #[]
  let mut os : Array (Std.HashMap Nat (Array Nat)) := #[]
  for set in ch.sets do
    let mut pm : Std.HashMap (Nat × Nat) (Array Nat) := {}
    let mut om : Std.HashMap Nat (Array Nat) := {}
    for it in set do
      let p := g.prods.getD it.prod default
      if it.dot == p.rhs.size then
        let key := (p.lhs, it.orig)
        match pm.get? key with
        | some l => pm := pm.insert key (l.push it.prod)
        | none =>
          pm := pm.insert key #[it.prod]
          om := om.insert p.lhs ((om.getD p.lhs #[]).push it.orig)
    ps := ps.push pm
    os := os.push om
  { prods := ps, origs := os }

inductive Task where
  | build (a s e : Nat) (mark : Mark)
  | chr (pos : Nat) (hidden : Bool)
  | ins (s : String)
  | close (a s e : Nat)

/-- Split production `p` over `[s, e]`: the child tasks, left to right, or
    `none`; and whether a choice was left open (another split, or a child
    that is already open on the path: a cycle). -/
def decompose (g : BNF) (ch : Chart) (d : Done) (opn : Std.HashSet (Nat × Nat × Nat))
    (p s e : Nat) : Option (List Task) × Bool := Id.run do
  let prod := g.prods.getD p default
  let k := prod.rhs.size
  let mut pos := e
  let mut kids : List Task := []
  let mut amb := false
  for jj in [0:k] do
    let j := k - 1 - jj
    match prod.rhs.getD j default with
    | .tm _ h =>
      if pos == 0 then return (none, amb)
      if !(ch.seen.getD (pos - 1) {}).contains ⟨p, j, s⟩ then return (none, amb)
      kids := .chr (pos - 1) h :: kids
      pos := pos - 1
    | .ins str =>
      if !(ch.seen.getD pos {}).contains ⟨p, j, s⟩ then return (none, amb)
      kids := .ins str :: kids
    | .nt b mk =>
      let mut chosen : Option Nat := none
      for m in (d.origs.getD pos {}).getD b #[] do
        if m < s || m > pos then continue
        if !(ch.seen.getD m {}).contains ⟨p, j, s⟩ then continue
        if opn.contains (b, m, pos) then amb := true; continue
        if chosen.isSome then amb := true else chosen := some m
      match chosen with
      | none => return (none, amb)
      | some m =>
        kids := .build b m pos mk :: kids
        pos := m
  if pos != s then return (none, amb)
  return (some kids, amb)

inductive FKind where
  | elem (name : String)
  | attr (name : String)
  | hide

structure Frame where
  kind : FKind
  inAttr : Bool
  attrs : Array (String × String) := #[]
  kids : Array Node := #[]
  buf : String := ""

def Frame.flush (f : Frame) : Frame :=
  if f.buf.isEmpty then f else { f with kids := f.kids.push (.text f.buf), buf := "" }

def Frame.addKid (f : Frame) (k : Node) : Frame :=
  match k with
  | .text t => { f with buf := f.buf ++ t }
  | k => let f := f.flush; { f with kids := f.kids.push k }

/-- Close frame `f` into its parent. -/
def closeInto (f p : Frame) : Except String Frame :=
  match f.kind with
  | .elem name =>
    let f := f.flush
    let names := f.attrs.map (·.1)
    if (names.toList.eraseDups).length != names.size then
      .error ("two attributes named the same on the element " ++ name)
    else
      .ok (p.addKid (.element name (f.attrs.toList.map fun (n, v) => ⟨n, v⟩) f.kids.toList))
  | .attr name => .ok { p with attrs := p.attrs.push (name, f.buf) }
  | .hide =>
    let p := f.kids.foldl Frame.addKid p
    .ok { p with buf := p.buf ++ f.buf, attrs := p.attrs ++ f.attrs }

def popFrame (fs : Array Frame) : Except String (Array Frame) := do
  match fs.back?, fs.pop.back? with
  | some f, some p => pure (fs.pop.pop.push (← closeInto f p))
  | _, _ => throw "frame stack underflow"

/-- Build the first parse tree and serialize it: the root element, and
    whether the parse is ambiguous. -/
def buildTree (g : BNF) (ch : Chart) (inp : Array Nat) : Except String (Node × Bool) := do
  let n := inp.size
  let d := mkDone g ch
  let mut tasks : Array Task := #[.build 0 0 n g.rootMark]
  let mut frames : Array Frame := #[{ kind := .hide, inAttr := false }]
  let mut opn : Std.HashSet (Nat × Nat × Nat) := {}
  let mut amb := false
  let bound := 1000000 + 64 * (n + 1) * (g.prods.size + 1)
  for _ in [0:bound] do
    match tasks.back? with
    | none => break
    | some t =>
      tasks := tasks.pop
      match t with
      | .build a s e mk =>
        let cands := ((d.prods.getD e {}).get? (a, s)).getD #[]
        let mut chosen : Option (List Task) := none
        for p in cands do
          let (r, am) := decompose g ch d opn p s e
          if am then amb := true
          match r with
          | some ks => if chosen.isSome then amb := true else chosen := some ks
          | none => pure ()
        match chosen with
        | none => throw "no derivation (an infinitely ambiguous grammar)"
        | some ks =>
          opn := opn.insert (a, s, e)
          let top := frames.back?.getD { kind := .hide, inAttr := false }
          let name := g.names.getD a ""
          let fr : Frame :=
            if top.inAttr then { kind := .hide, inAttr := true }
            else match mk with
              | .elem => { kind := .elem name, inAttr := false }
              | .attr => { kind := .attr name, inAttr := true }
              | .hide => { kind := .hide, inAttr := false }
          frames := frames.push fr
          tasks := tasks.push (.close a s e)
          for k in ks.reverse do tasks := tasks.push k
      | .chr pos h =>
        if !h then
          let c := Char.ofNat (inp.getD pos 0)
          frames := frames.modify (frames.size - 1) fun f => { f with buf := f.buf.push c }
      | .ins str =>
        frames := frames.modify (frames.size - 1) fun f => { f with buf := f.buf ++ str }
      | .close a s e =>
        opn := opn.erase (a, s, e)
        frames ← popFrame frames
  if !tasks.isEmpty then throw "the parse tree is too large"
  let root := (frames.back?.getD { kind := .hide, inAttr := false }).flush
  if !root.attrs.isEmpty then throw "an attribute outside every element"
  match root.kids.toList with
  | [.element t as ks] =>
    if amb then
      pure (.element t (as ++ [⟨"xmlns:ixml", nsIxml⟩, ⟨"ixml:state", "ambiguous"⟩]) ks, true)
    else pure (.element t as ks, false)
  | _ => throw "the serialization is not a single element"

inductive Outcome where
  | ok (n : Node) (ambiguous : Bool)
  | fail (pos : Nat) (msg : String)

def parseCps (g : BNF) (inp : Array Nat) : Outcome :=
  let (ch, last) := recognize g inp
  if g.accepts ch inp.size then
    match buildTree g ch inp with
    | .ok (nd, a) => .ok nd a
    | .error m => .fail inp.size m
  else if last == inp.size then .fail last "unexpected end of input"
  else .fail last "no parse"

def toCps (s : String) : Array Nat := (s.toList.map Char.toNat).toArray

/-- The failure document's root element (ixml 1.0: an implementation reports
    the failure with `ixml:state="failed"` on the root). -/
def failElem (inp : Array Nat) (pos : Nat) (msg : String) : Node := Id.run do
  let mut line := 1
  let mut col := 1
  for i in [0:min pos inp.size] do
    if inp.getD i 0 == 10 then line := line + 1; col := 1 else col := col + 1
  let unexp := match inp[pos]? with
    | some c => [Node.element "unexpected" [] [.text (String.singleton (Char.ofNat c))]]
    | none => []
  let el (t v : String) : Node := .element t [] [.text v]
  return .element "failed" [⟨"xmlns:ixml", nsIxml⟩, ⟨"ixml:state", "failed"⟩]
    ([el "line" (toString line), el "column" (toString col), el "pos" (toString pos)] ++ unexp ++
      [el "message" msg])

/-! ## The XML form of a grammar -/

def attrOf (as : List Attribute) (k : String) : Option String := (as.find? (·.name == k)).map (·.value)

def hexOf (s : String) : Except String Nat :=
  if s.isEmpty then .error "empty hex value"
  else s.foldl (fun acc c => do
    let v ← acc
    match Boot.hexDigit? c with
    | some d => pure (v * 16 + d)
    | none => throw ("bad hex value " ++ s)) (.ok 0)

def litOf (as : List Attribute) : Except String (List Nat) :=
  match attrOf as "string", attrOf as "hex" with
  | some s, _ => .ok (s.toList.map Char.toNat)
  | none, some h => do pure [← hexOf h]
  | none, none => .error "a literal needs a string or hex attribute"

def charOf (s : String) : Except String Nat :=
  match s.toList with
  | [c] => .ok c.toNat
  | '#' :: h => hexOf (String.ofList h)
  | _ => .error ("bad range character " ++ s)

def markOf (as : List Attribute) (k : String) : Except String (Option Mark) :=
  match attrOf as k with
  | none => .ok none
  | some m => match Mark.ofString? m with
    | some v => .ok (some v)
    | none => .error ("bad mark " ++ m)

def memberOf (as : List Attribute) : Except String Member :=
  match attrOf as "string", attrOf as "hex", attrOf as "from", attrOf as "to", attrOf as "code" with
  | some s, _, _, _, _ => .ok (.chars (s.toList.map Char.toNat))
  | _, some h, _, _, _ => do pure (.chars [← hexOf h])
  | _, _, some a, some b, _ => do pure (.range (← charOf a) (← charOf b))
  | _, _, _, _, some c => .ok (.cls c)
  | _, _, _, _, _ => .error "a member needs string, hex, from and to, or code"

def elems (ks : List Node) : List (String × List Attribute × List Node) :=
  ks.filterMap fun k => match k with
    | .element t a c => if t == "comment" then none else some (t, a, c)
    | _ => none

mutual
def factorOf : Nat → String × List Attribute × List Node → Except String Factor
  | 0, _ => .error "grammar too deep"
  | f + 1, (t, as, ks) => match t with
    | "nonterminal" => do
      let some n := attrOf as "name" | throw "a nonterminal needs a name"
      pure (.nt (← markOf as "mark") n)
    | "literal" => do
      let tm ← markOf as "tmark"
      pure (.lit (tm == some .hide) (← litOf as))
    | "inclusion" | "exclusion" => do
      let tm ← markOf as "tmark"
      let mut ms := #[]
      for (mt, ma, _) in elems ks do
        if mt != "member" then throw ("unexpected " ++ mt ++ " in a character set")
        ms := ms.push (← memberOf ma)
      pure (.cset (tm == some .hide) (t == "exclusion") ms.toList)
    | "insertion" => do
      let cs ← litOf as
      pure (.ins (String.ofList (cs.map Char.ofNat)))
    | "alts" => do pure (.grp (← altsOf f ks))
    | "option" => match elems ks with
      | [x] => do pure (.opt (← factorOf f x))
      | _ => throw "an option has one factor"
    | "repeat0" | "repeat1" => do
      let (y, sep) ← match elems ks with
        | [x] => pure (x, none)
        | [x, ("sep", _, sk)] => match elems sk with
          | [s] => pure (x, some s)
          | _ => throw "a separator has one factor"
        | _ => throw "a repetition has one factor and an optional separator"
      let yf ← factorOf f y
      let sf ← match sep with
        | some s => do pure (some (← factorOf f s))
        | none => pure none
      pure (if t == "repeat0" then .rep0 yf sf else .rep1 yf sf)
    | _ => .error ("unexpected element " ++ t ++ " in a grammar")

def altsOf : Nat → List Node → Except String (List (List Factor))
  | 0, _ => .error "grammar too deep"
  | f + 1, ks => do
    let mut out := #[]
    for (t, _, aks) in elems ks do
      if t != "alt" then throw ("unexpected " ++ t ++ " where an alt is expected")
      let mut fs := #[]
      for x in elems aks do fs := fs.push (← factorOf f x)
      out := out.push fs.toList
    pure out.toList
end

/-- The rules of a grammar in its XML form (an `ixml` element). -/
def grammarOfXml (nd : Node) : Except String (List Rule) :=
  match nd with
  | .element "ixml" _ ks => do
    let mut rs := #[]
    for (t, as, rks) in elems ks do
      if t == "prolog" then continue
      if t != "rule" then throw ("unexpected " ++ t ++ " in an ixml element")
      let some n := attrOf as "name" | throw "a rule needs a name"
      let alts ← altsOf 256 rks
      if alts.isEmpty then throw ("the rule " ++ n ++ " has no alternative")
      rs := rs.push { mark := ← markOf as "mark", name := n, alts }
    pure rs.toList
  | _ => .error "a grammar is an ixml element"

/-- The ixml grammar, compiled once. -/
def ixmlBNF : Except String BNF := Boot.parse ixmlGrammarText >>= compile

/-- A grammar from its text: parsed with the ixml grammar, then read. -/
def bnfOfText (src : String) : Except String BNF := do
  let gb ← ixmlBNF
  match parseCps gb (toCps src) with
  | .ok nd _ => compile (← grammarOfXml nd)
  | .fail pos msg => throw s!"the grammar does not parse at {pos}: {msg}"

/-- Parse `input` with the grammar text `g`: the root element, or the
    failure element. -/
def runText (g input : String) : Except String Node := do
  let b ← bnfOfText g
  let inp := toCps input
  match parseCps b inp with
  | .ok nd _ => pure nd
  | .fail pos msg => pure (failElem inp pos msg)

/-! ## `fn:invisible-xml` -/

/-- An element node as an XML tree (names in no namespace; attributes in a
    namespace, such as `ixml:state`, are left out). -/
def xdmToXml (e : Env) (n : NodeRef) : Nat → Option Node
  | 0 => none
  | f + 1 =>
    let r := e.nrec n
    match r.kind with
    | .element =>
      let as := r.attrs.toList.filterMap fun a =>
        let ar := e.nrec (n.at a)
        if ar.name.uri == "" then some (⟨ar.name.loc, ar.value⟩ : Attribute) else none
      let ks := r.children.toList.filterMap fun c =>
        let cr := e.nrec (n.at c)
        match cr.kind with
        | .element => xdmToXml e (n.at c) f
        | .text => some (.text cr.value)
        | _ => none
      some (.element r.name.loc as ks)
    | _ => none

def foix1 {α} (msg : String) : M α := err "FOIX0001" ("invalid ixml grammar: " ++ msg)

/-- The grammar argument: absent (the ixml grammar), a grammar text, or the
    XML form as an element. -/
def bnfOfArg (e : Env) (g : Seq) : M BNF :=
  match g with
  | [] => match ixmlBNF with
    | .ok b => pure b
    | .error m => foix1 m
  | [.atom a] => match bnfOfText a.str with
    | .ok b => pure b
    | .error m => foix1 m
  | [.node n] =>
    match xdmToXml e n 100000 with
    | some nd => match grammarOfXml nd >>= compile with
      | .ok b => pure b
      | .error m => foix1 m
    | none => foix1 "the grammar is not an ixml element"
  | _ => err "XPTY0004" "the grammar is a string or an ixml element"

def failOnError (opts : Seq) : M Bool :=
  match optLookup opts "fail-on-error" with
  | none => pure false
  | some [.atom ⟨_, .bool b⟩] => pure b
  | some _ => err "XPTY0004" "the option fail-on-error must be a single xs:boolean"

def ixmlQ (l : String) : QN := { uri := nsFN, loc := l }

def gKey (g : Seq) : String :=
  match g with
  | [.atom a] => "s:" ++ a.str
  | [.node n] => "n:" ++ toString n.doc ++ ":" ++ toString n.idx
  | _ => "ixml"

/-- `fn:invisible-xml($grammar, $options)`: the grammar is read and checked
    now (FOIX0001); the result is an inline function over the internal
    `ixml-parse#`, with the grammar and the option in its closure. -/
def invisibleXmlFn : LibFn := fun _ e a => do
  let g := argN a 0
  let fail ← failOnError (argN a 1)
  let _ ← bnfOfArg e g
  let vG : QN := { uri := "http://factoidal/internal", loc := "ixml-grammar" }
  let vF : QN := { uri := "http://factoidal/internal", loc := "ixml-fail" }
  let vIn : QN := { uri := "", loc := "input" }
  pure [.fn (.inline [(vIn, parseTy "xs:string")] (parseTy "item()")
    (.call (ixmlQ "ixml-parse#") [some (.var vG), some (.var vF), some (.var vIn)] []) false
    [(vG, g), (vF, [.atom (Atomic.ofBool fail)])])]

def ixmlParseFn : LibFn := fun _ e a => do
  let g := argN a 0
  let b ← bnfOfArg e g
  let fail := boolOf (argN a 1)
  let input := strOf (argN a 2)
  let inp := toCps input
  let nd ← match parseCps b inp with
    | .ok nd _ => pure nd
    | .fail pos msg =>
      if fail then err "FOIX0002" s!"the input does not parse at {pos}: {msg}"
      else pure (failElem inp pos msg)
  let doc := Doc.ofNodes [nd]
  pure [doc.rootItem (runtimeDocId "invisible-xml" (gKey g ++ "\x00" ++ input))]

def ixmlTable : List (String × LibFn) :=
  [("invisible-xml", invisibleXmlFn), ("ixml-parse#", ixmlParseFn)]

/-! ## Tests -/

#guard ixmlBNF.isOk

#guard (runText "S=A. A='a'." "a").toOption ==
  some (.element "S" [] [.element "A" [] [.text "a"]])

#guard (runText "date = year, -'-', month, -'-', day .
           year = d, d, d, d .
           month = '0', d | '1', ['0'|'1'|'2'] .
           day = ['0'|'1'|'2'], d | '3', ['0'|'1'] .
           -d = ['0'-'9'] ." "2023-10-31").toOption ==
  some (.element "date" [] [.element "year" [] [.text "2023"], .element "month" [] [.text "10"],
    .element "day" [] [.text "31"]])

-- attributes, insertions, left recursion
#guard (runText "e = n, -'+', m. @n = ['0'-'9']+, +'!'. @m = ['0'-'9']+." "1+23").toOption ==
  some (.element "e" [⟨"n", "1!"⟩, ⟨"m", "23"⟩] [])

#guard (runText "S = S, 'a' | 'a'." "aaa").toOption ==
  some (.element "S" [] [.element "S" [] [.element "S" [] [.text "a"], .text "a"], .text "a"])

#guard (runText "S: 'a'." "b").toOption.map (fun n => match n with
  | .element t _ _ => t | _ => "") == some "failed"

-- an ambiguous grammar
#guard (runText "S = A | B. A = 'a'. B = 'a'." "a").toOption ==
  some (.element "S" [⟨"xmlns:ixml", nsIxml⟩, ⟨"ixml:state", "ambiguous"⟩] [.element "A" [] [.text "a"]])

-- a grammar text in error
#guard !(bnfOfText "(((((").isOk
#guard !(bnfOfText "S = T.").isOk

end L4Factoidal.XPath4.Ixml
