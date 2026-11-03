/-
L4Factoidal.Regex.XPath40 — the regular-expression dialect of XPath and
XQuery Functions and Operators 4.0 (F&O 4.0 §6.1 "Regular expression
syntax", §6.2 "Flags"), on the shared engine of `Regex.XPath`.

F&O 4.0 §6.1 takes the XSD 1.1 Part 2 Appendix G grammar as its baseline
and adds: reluctant quantifiers, captured groups (also named, `(?<name>...)`),
back-references `\N` and `\k<name>`, the assertions `^` `$` `\b` `\B`, lookahead
and lookbehind (`(?=` `(?!` `(?<=` `(?<!` and the `(*positive_lookahead:...)`
forms), the single-character escapes `\$` and `\#`, comments with the flag
`c`, and the rule that an assertion is not followed by a quantifier.

This module is a separate parser. The parsers of `Regex.XSDPattern` and the
capturing parser of `Regex.XPath` are not changed, so the XSD facet, SPARQL
(F&O 2.0 / 3.1 through `Regex.Profiles`), SHACL, CSVW, ShEx, RIF and JSON
Schema dialects keep their languages. Only the profile `Profiles.Dialect.xpath40`
and the XPath 4.0 function library call `compile` here.

Differences from the XSD-flavour parser that the 4.0 grammar requires:

* character classes follow XSD 1.1 G.4.1 exactly: an unescaped `[` is only
  the start of a subtraction `-[...]`; the hyphen rules of production [80];
  `[^]` and `[]` are errors; a range must not be reversed; subtraction
  `[a-z-[aeiou]]` is supported, also nested;
* `\p{X}` / `\P{X}` over the Unicode 16.0.0 General_Category values and
  blocks (`Regex.UnicodeProps`); an unknown block name is an error
  (F&O 4.0 §6.1.7);
* `\d` is `\p{Nd}`, `\w` is `[#x0000-#x10FFFF]-[\p{P}\p{Z}\p{C}]`
  (XSD 1.1 G.4.2.5), not the ASCII classes of `XSDPattern`;
* `\u`, `\U`, `\f`, `\/` are not escapes in this grammar and are errors;
* with the flag `x`, every whitespace character outside a character class
  is removed before parsing, also after a backslash (F&O 4.0 §6.2:
  `hello\ sworld` is `hello\sworld`).

Matching. A pattern whose language the sentinel encoding of `Regex.XPath`
can represent (no back-reference, lookaround or word boundary; anchors not
under a quantifier and at most one `^` and one `$` on any path, `$` never
before `^`) is matched by the derivative engine, as the other dialects are.
Any other pattern sets `Compiled.ordered`, and `isMatch` uses the ordered
matcher `cmatchE`, which `fn:replace`, `fn:tokenize`, `fn:analyze-string` and
`fn:matching-segments` use for every pattern. That matcher is total (fuel
bounded); its fuel adequacy is not proved.

Known limits: quantifier bounds above 1000 are refused by the caller
(`XPath4.Lib.compileRe`, FOER0000), because a counted repetition is expanded.
-/
import L4Factoidal.Regex.XPath
import L4Factoidal.Regex.UnicodeProps

namespace L4Factoidal.Regex.XPath40

open XSDPattern (ciLit dotRegex nameStartCharRanges nameCharRanges)

/-! ## Unicode property tables -/

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (XSDPattern.hexVal c.toNat).getD 0) 0

def parseRangeList (s : String) : List (Nat × Nat) :=
  (s.splitOn " ").filterMap fun t =>
    match t.splitOn "-" with
    | [a, b] => if a.isEmpty || b.isEmpty then none else some (hexNat a, hexNat b)
    | _ => none

/-- `Name:lo-hi lo-hi` lines. Block names contain `-` but never `:`. -/
def parseTable (txt : String) : List (String × List (Nat × Nat)) :=
  (txt.splitOn "\n").filterMap fun line =>
    match line.splitOn ":" with
    | [k, v] => some (k, parseRangeList v)
    | _ => none

/-- The General_Category table, parsed on first use. -/
def categories : Thunk (List (String × List (Nat × Nat))) :=
  Thunk.mk fun _ => parseTable UnicodeProps.catText

/-- The block table, parsed on first use. -/
def blocks : Thunk (List (String × List (Nat × Nat))) :=
  Thunk.mk fun _ => parseTable UnicodeProps.blockText

/-- XSD 1.1 G.4.2.2 `IsCategory`: a two-letter General_Category value, or one
    letter for the union of the values that start with it. Cs is not a value
    of this grammar. -/
def categoryRanges (name : String) : Option (List (Nat × Nat)) :=
  let tbl := categories.get
  match name.toList with
  | [c] =>
    if "LMNPZSC".toList.contains c then
      some (Text.CaseMap.normalizeRanges
        ((tbl.filter (fun (k, _) => k.toList.head? == some c)).flatMap (·.2)))
    else none
  | [_, _] => tbl.lookup name
  | _ => none

/-- XSD 1.1 G.4.2.3 `IsBlock`: `Is` and one or more of `[a-zA-Z0-9-]`; the
    name must be a block of the tables (F&O 4.0 §6.1.7: an unknown block name
    is an error). -/
def blockRanges (name : String) : Option (List (Nat × Nat)) :=
  match name.toList with
  | 'I' :: 's' :: rest =>
    if !rest.isEmpty && rest.all (fun c => c.isAlphanum || c == '-') then
      (blocks.get).lookup (String.ofList rest)
    else none
  | _ => none

/-- `\p{X}`: a category or a block. -/
def propRanges (name : String) : Option (List (Nat × Nat)) :=
  match categoryRanges name with
  | some rs => some rs
  | none => blockRanges name

/-- `\W` of XSD 1.1 G.4.2.5: the punctuation, separator and other
    characters. -/
def nonWordRanges : Thunk (List (Nat × Nat)) := Thunk.mk fun _ =>
  Text.CaseMap.normalizeRanges
    (((categoryRanges "P").getD []) ++ ((categoryRanges "Z").getD []) ++
      ((categoryRanges "C").getD []))

/-- `\w` of XSD 1.1 G.4.2.5: `[#x0000-#x10FFFF]-[\p{P}\p{Z}\p{C}]`. -/
def wordRanges : Thunk (List (Nat × Nat)) := Thunk.mk fun _ =>
  complementRanges nonWordRanges.get

/-- `\d` of XSD 1.1 G.4.2.5: `\p{Nd}`. -/
def digitRanges : Thunk (List (Nat × Nat)) := Thunk.mk fun _ =>
  (categoryRanges "Nd").getD []

/-- `A - B` over sorted, disjoint interval lists, as `¬(¬A ∪ B)`. -/
def diffRanges (a b : List (Nat × Nat)) : List (Nat × Nat) :=
  complementRanges (Text.CaseMap.normalizeRanges (complementRanges a ++ b))

/-! ## Lexical preprocessing (F&O 4.0 §6.1.2 and §6.2) -/

def isWs (c : Nat) : Bool := c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20

/-- Flag `c`: remove each comment, from a `#` that is not escaped and not in a
    character class to the next `#` or the end. Inside a comment backslashes
    and brackets have no meaning. `depth` counts open character classes. -/
def stripComments : List Nat → Nat → Bool → List Nat → List Nat
  | [], _, _, acc => acc.reverse
  | c :: t, depth, true, acc =>
    if c == 0x23 then stripComments t depth false acc else stripComments t depth true acc
  | c :: t, depth, false, acc =>
    if c == 0x5C then
      match t with
      | d :: t2 => stripComments t2 depth false (d :: c :: acc)
      | [] => (c :: acc).reverse
    else if c == 0x5B then stripComments t (depth + 1) false (c :: acc)
    else if c == 0x5D then stripComments t (depth - 1) false (c :: acc)
    else if c == 0x23 && depth == 0 then stripComments t depth true acc
    else stripComments t depth false (c :: acc)

/-- Flag `x`: remove whitespace outside character classes. Outside a class
    the whitespace after a backslash goes too, so `\ s` is `\s` (F&O 4.0 §6.2
    example `hello\ sworld`). `esc` is set after a backslash. -/
def stripWs : List Nat → Nat → Bool → List Nat → List Nat
  | [], _, _, acc => acc.reverse
  | c :: t, depth, esc, acc =>
    if depth == 0 then
      if isWs c then stripWs t depth esc acc
      else if esc then stripWs t depth false (c :: acc)
      else if c == 0x5C then stripWs t depth true (c :: acc)
      else if c == 0x5B then stripWs t 1 false (c :: acc)
      else stripWs t depth false (c :: acc)
    else
      if esc then stripWs t depth false (c :: acc)
      else if c == 0x5C then stripWs t depth true (c :: acc)
      else if c == 0x5B then stripWs t (depth + 1) false (c :: acc)
      else if c == 0x5D then stripWs t (depth - 1) false (c :: acc)
      else stripWs t depth false (c :: acc)

/-! ## The abstract syntax -/

/-- A parsed F&O 4.0 regular expression. Character sets are already expanded
    for the flag `i` where §6.2 says so. -/
inductive Node where
  /-- one character from a set of code points (sorted, disjoint) -/
  | chars : List (Nat × Nat) → Node
  /-- the wildcard `.` -/
  | dot : Node
  | eps : Node
  | cat : Node → Node → Node
  | alt : Node → Node → Node
  /-- capturing subexpression with its group number -/
  | group : Nat → Node → Node
  /-- `rep a min max greedy`; `max = none` is unbounded -/
  | rep : Node → Nat → Option Nat → Bool → Node
  | bol : Node
  | eol : Node
  /-- `\b` (`false`) or `\B` (`true`) -/
  | wordB : Bool → Node
  /-- lookahead; `true` is negative -/
  | ahead : Bool → Node → Node
  /-- lookbehind; `true` is negative; the body is a `simpleRegExp` -/
  | behind : Bool → Node → Node
  | backref : Nat → Node
  deriving Repr, Inhabited

/-- Parser state: the next group number, the groups whose `)` has been read,
    and the group names. -/
structure St where
  next : Nat := 1
  closed : List Nat := []
  names : List (Nat × String) := []
  deriving Repr, Inhabited

/-! ## Escapes -/

/-- F&O 4.0 §6.1.3 `SingleCharEsc`: `\` and one of `nrt\|.?*+(){}$-[]^#`. -/
def singleCharEsc (c : Nat) : Option Nat :=
  if c == 0x6E then some 0x0A
  else if c == 0x72 then some 0x0D
  else if c == 0x74 then some 0x09
  else if "\\|.?*+(){}$-[]^#".toList.any (fun d => d.toNat == c) then some c
  else none

/-- An item of a character class or an escape atom: one character (with a
    mark for an unescaped character), or a set (a class escape). -/
inductive Item where
  | single : Nat → Bool → Item
  | set : List (Nat × Nat) → Item

/-- `\p{...}` / `\P{...}` after the letter: the name up to `}`. -/
def readProp (t : List Nat) : Option (String × List Nat) :=
  match t with
  | 0x7B :: rest =>
    let name := rest.takeWhile (· != 0x7D)
    match rest.drop name.length with
    | 0x7D :: rest2 => some (stringOfCps name, rest2)
    | _ => none
  | _ => none

/-- XSD 1.1 G.4.2 `charClassEsc` and `SingleCharEsc` after the backslash
    (`letter` is the character after it). -/
def escapeItem (letter : Nat) (t : List Nat) : Option (Item × List Nat) :=
  match singleCharEsc letter with
  | some c => some (.single c false, t)
  | none =>
    let set (rs : List (Nat × Nat)) := some (Item.set rs, t)
    if letter == 0x73 then set [(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)]          -- \s
    else if letter == 0x53 then set (complementRanges [(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)])
    else if letter == 0x69 then set (Text.CaseMap.normalizeRanges nameStartCharRanges)   -- \i
    else if letter == 0x49 then set (complementRanges (Text.CaseMap.normalizeRanges nameStartCharRanges))
    else if letter == 0x63 then set (Text.CaseMap.normalizeRanges nameCharRanges)        -- \c
    else if letter == 0x43 then set (complementRanges (Text.CaseMap.normalizeRanges nameCharRanges))
    else if letter == 0x64 then set digitRanges.get                                      -- \d
    else if letter == 0x44 then set (complementRanges digitRanges.get)
    else if letter == 0x77 then set wordRanges.get                                       -- \w
    else if letter == 0x57 then set nonWordRanges.get
    else if letter == 0x70 || letter == 0x50 then                                        -- \p \P
      match readProp t with
      | none => none
      | some (name, rest) =>
        match propRanges name with
        | none => none
        | some rs => some (.set (if letter == 0x70 then rs else complementRanges rs), rest)
    else none

/-- One class item: an escape, or a character other than `[` and `]`. -/
def classItem : List Nat → Option (Item × List Nat)
  | [] => none
  | c :: t =>
    if c == 0x5C then
      match t with
      | letter :: t2 => escapeItem letter t2
      | [] => none
    else if c == 0x5B || c == 0x5D then none
    else some (.single c true, t)

/-! ## Character classes (XSD 1.1 G.4.1) -/

/-- The parts of a positive character group, up to `]` or a subtraction `-[`.
    Returns the code points (with the case-variants under `ci`), the rest after
    `]` or after `-[`, and whether a subtraction follows. `n` counts the
    parts: a group has at least one. -/
def classParts (ci : Bool) :
    Nat → List Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × List Nat × Bool)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, h :: t, acc, n =>
    if h == 0x5D then (if n == 0 then none else some (acc, t, false))
    else if h == 0x2D && t.head? == some 0x5B then
      (if n == 0 then none else some (acc, t.drop 1, true))
    else
      match classItem (h :: t) with
      | none => none
      | some (.set rs, rest) => classParts ci fuel rest (acc ++ rs) (n + 1)
      | some (.single c unesc, rest) =>
        let lit (x : Nat) := ciLit ci [(x, x)]
        match rest with
        | 0x2D :: r2 =>
          match r2 with
          | 0x5B :: _ => classParts ci fuel rest (acc ++ lit c) (n + 1)
          | 0x5D :: _ => classParts ci fuel r2 (acc ++ lit c ++ lit 0x2D) (n + 2)
          | 0x2D :: 0x5B :: _ => classParts ci fuel r2 (acc ++ lit c ++ lit 0x2D) (n + 2)
          | _ =>
            -- a range; neither end is an unescaped hyphen
            if unesc && c == 0x2D then none
            else
              match classItem r2 with
              | some (.single e unescE, r3) =>
                if (unescE && e == 0x2D) || e < c then none
                else classParts ci fuel r3 (acc ++ ciLit ci [(c, e)]) (n + 1)
              | _ => none
        | _ => classParts ci fuel rest (acc ++ lit c) (n + 1)

/-- A character class expression after its `[`: the code points it matches
    (sorted, disjoint) and the rest after its `]`. -/
def classExpr (ci : Bool) : Nat → List Nat → Option (List (Nat × Nat) × List Nat)
  | 0, _ => none
  | fuel + 1, input =>
    let (neg, body) := match input with
      | 0x5E :: t => (true, t)
      | _ => (false, input)
    match classParts ci (body.length + 1) body [] 0 with
    | none => none
    | some (rs, rest, sub) =>
      let base := Text.CaseMap.normalizeRanges rs
      let g := if neg then complementRanges base else base
      if sub then
        match classExpr ci fuel rest with
        | some (srs, 0x5D :: rest2) => some (diffRanges g srs, rest2)
        | _ => none
      else some (g, rest)

/-! ## Quantifiers -/

/-- `{n}`, `{n,}`, `{n,m}` after the `{`. -/
def quantity (t : List Nat) : Option (Nat × Option Nat × List Nat) :=
  match XSDPattern.readUint t with
  | none => none
  | some (n, t1) =>
    match t1 with
    | 0x7D :: t2 => some (n, some n, t2)
    | 0x2C :: 0x7D :: t3 => some (n, none, t3)
    | 0x2C :: t2 =>
      match XSDPattern.readUint t2 with
      | some (m, 0x7D :: t4) => if n ≤ m then some (n, some m, t4) else none
      | _ => none
    | _ => none

/-- F&O 4.0 `quantifier`: `?`, `*`, `+` or `{quantity}`, then an optional `?`
    for a reluctant quantifier. `none` inside: an invalid quantifier. -/
def quantifier (input : List Nat) : Option (Option (Nat × Option Nat × Bool × List Nat)) :=
  let lazy (rest : List Nat) : Bool × List Nat :=
    match rest with
    | 0x3F :: r => (false, r)
    | _ => (true, rest)
  match input with
  | 0x3F :: t => let (g, r) := lazy t; some (some (0, some 1, g, r))
  | 0x2A :: t => let (g, r) := lazy t; some (some (0, none, g, r))
  | 0x2B :: t => let (g, r) := lazy t; some (some (1, none, g, r))
  | 0x7B :: t =>
    match quantity t with
    | none => none
    | some (n, m, r) => let (g, r') := lazy r; some (some (n, m, g, r'))
  | _ => some none

/-! ## The parser -/

/-- `groupName`: an ASCII letter, then ASCII letters or digits. -/
def readName (t : List Nat) : Option (String × List Nat) :=
  let isL (c : Nat) := (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A)
  let isD (c : Nat) := 0x30 ≤ c && c ≤ 0x39
  let name := t.takeWhile (fun c => isL c || isD c)
  match name, t.drop name.length with
  | c :: _, 0x3E :: rest => if isL c then some (stringOfCps name, rest) else none
  | _, _ => none

def startsWith (pre : String) (t : List Nat) : Option (List Nat) :=
  let p := cpsOfString pre
  if t.take p.length == p then some (t.drop p.length) else none

/-- Read the digits of a back-reference after its first digit `d`: a further
    digit belongs to it while the number stays at most the count of capturing
    left parentheses read so far (F&O 4.0 §6.1.6). -/
def backrefDigits (opened : Nat) : Nat → List Nat → Nat × List Nat
  | n, c :: t =>
    if 0x30 ≤ c && c ≤ 0x39 && n * 10 + (c - 0x30) ≤ opened then
      backrefDigits opened (n * 10 + (c - 0x30)) t
    else (n, c :: t)
  | n, [] => (n, [])

mutual
  def pAlt (ci : Bool) : Nat → List Nat → St → Option (Node × List Nat × St)
    | 0, _, _ => none
    | fuel + 1, input, st =>
      match pSeq ci fuel input st with
      | none => none
      | some (r1, rest, st1) =>
        match rest with
        | 0x7C :: t =>
          match pAlt ci fuel t st1 with
          | none => none
          | some (r2, rest2, st2) => some (.alt r1 r2, rest2, st2)
        | _ => some (r1, rest, st1)

  def pSeq (ci : Bool) : Nat → List Nat → St → Option (Node × List Nat × St)
    | 0, _, _ => none
    | fuel + 1, input, st =>
      match input with
      | [] => some (.eps, [], st)
      | h :: _ =>
        if h == 0x7C || h == 0x29 then some (.eps, input, st)
        else
          match pPiece ci fuel input st with
          | none => none
          | some (r1, rest, st1) =>
            match rest with
            | [] => some (r1, [], st1)
            | h2 :: _ =>
              if h2 == 0x7C || h2 == 0x29 then some (r1, rest, st1)
              else
                match pSeq ci fuel rest st1 with
                | none => none
                | some (r2, rest2, st2) => some (.cat r1 r2, rest2, st2)

  /-- `piece ::= (atom quantifier?) | assertion`. -/
  def pPiece (ci : Bool) : Nat → List Nat → St → Option (Node × List Nat × St)
    | 0, _, _ => none
    | fuel + 1, input, st =>
      match pAtom ci fuel input st with
      | none => none
      | some (a, rest, st1, isAssertion) =>
        match quantifier rest with
        | none => none
        | some none => some (a, rest, st1)
        | some (some (n, m, greedy, rest2)) =>
          if isAssertion then none else some (.rep a n m greedy, rest2, st1)

  /-- An atom or an assertion; the flag is set for an assertion. -/
  def pAtom (ci : Bool) : Nat → List Nat → St → Option (Node × List Nat × St × Bool)
    | 0, _, _ => none
    | fuel + 1, input, st =>
      match input with
      | [] => none
      | h :: t =>
        if h == 0x28 then pGroup ci fuel t st
        else if h == 0x5B then
          match classExpr ci (t.length + 1) t with
          | none => none
          | some (rs, rest) => some (.chars rs, rest, st, false)
        else if h == 0x2E then some (.dot, t, st, false)
        else if h == 0x5E then some (.bol, t, st, true)
        else if h == 0x24 then some (.eol, t, st, true)
        else if h == 0x5C then
          match t with
          | [] => none
          | letter :: t2 =>
            if letter == 0x62 then some (.wordB false, t2, st, true)
            else if letter == 0x42 then some (.wordB true, t2, st, true)
            else if 0x31 ≤ letter && letter ≤ 0x39 then
              let (n, rest) := backrefDigits (st.next - 1) (letter - 0x30) t2
              if st.closed.contains n then some (.backref n, rest, st, false) else none
            else if letter == 0x6B then
              match t2 with
              | 0x3C :: t3 =>
                match readName t3 with
                | none => none
                | some (name, rest) =>
                  match st.names.find? (·.2 == name) with
                  | some (n, _) => if st.closed.contains n then some (.backref n, rest, st, false) else none
                  | none => none
              | _ => none
            else
              match escapeItem letter t2 with
              | some (.single c _, rest) => some (.chars (ciLit ci [(c, c)]), rest, st, false)
              | some (.set rs, rest) => some (.chars rs, rest, st, false)
              | none => none
        else if XSDPattern.isAtomMeta h then none
        else some (.chars (ciLit ci [(h, h)]), t, st, false)

  /-- After `(`: the group forms of F&O 4.0 §6.1.3. -/
  def pGroup (ci : Bool) : Nat → List Nat → St → Option (Node × List Nat × St × Bool)
    | 0, _, _ => none
    | fuel + 1, t, st =>
      let close (body : Option (Node × List Nat × St)) (k : Node → St → Node × St) (assertion : Bool) :
          Option (Node × List Nat × St × Bool) :=
        match body with
        | some (r, 0x29 :: rest, st1) => let (n, st2) := k r st1; some (n, rest, st2, assertion)
        | _ => none
      match t with
      | 0x3F :: 0x3A :: t2 => close (pAlt ci fuel t2 st) (fun r s => (r, s)) false
      | 0x3F :: 0x3D :: t2 => close (pAlt ci fuel t2 st) (fun r s => (.ahead false r, s)) true
      | 0x3F :: 0x21 :: t2 => close (pAlt ci fuel t2 st) (fun r s => (.ahead true r, s)) true
      | 0x3F :: 0x3C :: 0x3D :: t2 => close (pAlt ci fuel t2 st) (fun r s => (.behind false r, s)) true
      | 0x3F :: 0x3C :: 0x21 :: t2 => close (pAlt ci fuel t2 st) (fun r s => (.behind true r, s)) true
      | 0x3F :: 0x3C :: t2 =>
        match readName t2 with
        | none => none
        | some (name, t3) =>
          if st.names.any (·.2 == name) then none
          else
            let g := st.next
            close (pAlt ci fuel t3 { st with next := g + 1, names := st.names ++ [(g, name)] })
              (fun r s => (.group g r, { s with closed := g :: s.closed })) false
      | 0x3F :: _ => none
      | 0x2A :: t2 =>
        match startsWith "positive_lookahead:" t2, startsWith "negative_lookahead:" t2,
            startsWith "positive_lookbehind:" t2, startsWith "negative_lookbehind:" t2 with
        | some t3, _, _, _ => close (pAlt ci fuel t3 st) (fun r s => (.ahead false r, s)) true
        | _, some t3, _, _ => close (pAlt ci fuel t3 st) (fun r s => (.ahead true r, s)) true
        | _, _, some t3, _ => close (pAlt ci fuel t3 st) (fun r s => (.behind false r, s)) true
        | _, _, _, some t3 => close (pAlt ci fuel t3 st) (fun r s => (.behind true r, s)) true
        | none, none, none, none => none
      | _ =>
        let g := st.next
        close (pAlt ci fuel t { st with next := g + 1 })
          (fun r s => (.group g r, { s with closed := g :: s.closed })) false
end

/-! ## Checks and translations -/

/-- F&O 4.0 §6.1.8.5 `simpleRegExp`: the alternatives of a lookbehind body,
    each a sequence of single-character atoms, with its length. -/
def simpleAlts : Node → Option (List (List Node))
  | .alt a b => do let x ← simpleAlts a; let y ← simpleAlts b; pure (x ++ y)
  | n => (simpleSeq n).map (fun s => [s])
where
  simpleSeq : Node → Option (List Node)
    | .eps => some []
    | .chars rs => some [.chars rs]
    | .dot => some [.dot]
    | .cat a b => do let x ← simpleSeq a; let y ← simpleSeq b; pure (x ++ y)
    | _ => none

/-- Every lookbehind body is a `simpleRegExp`. -/
def lookbehindsSimple : Node → Bool
  | .behind _ a => (simpleAlts a).isSome
  | .cat a b | .alt a b => lookbehindsSimple a && lookbehindsSimple b
  | .group _ a | .rep a _ _ _ | .ahead _ a => lookbehindsSimple a
  | _ => true

/-- Can the sentinel encoding represent the anchors? `some (b, e)` says
    whether a `^` / `$` can occur; `none` that it cannot represent them, or that
    the node needs the ordered matcher. -/
def sentinelAnchors : Node → Option (Bool × Bool)
  | .bol => some (true, false)
  | .eol => some (false, true)
  | .chars _ | .dot | .eps => some (false, false)
  | .cat a b => do
    let (ab, ae) ← sentinelAnchors a
    let (bb, be) ← sentinelAnchors b
    if (ab && bb) || (ae && be) || (ae && bb) then none else some (ab || bb, ae || be)
  | .alt a b => do
    let (ab, ae) ← sentinelAnchors a
    let (bb, be) ← sentinelAnchors b
    some (ab || bb, ae || be)
  | .group _ a => sentinelAnchors a
  | .rep a _ _ _ => do
    let (x, y) ← sentinelAnchors a
    if x || y then none else some (false, false)
  | .wordB _ | .ahead _ _ | .behind _ _ | .backref _ => none

structure Opts where
  ci : Bool
  dotAll : Bool
  multiline : Bool

def dotRe (o : Opts) : Re := if o.dotAll then Exec.anyChar else dotRegex

/-- The derivative regex, with `^` / `$` as the sentinel code points. Only
    used when `sentinelAnchors` accepts the node. -/
def toRe (o : Opts) : Node → Re
  | .chars rs => .ranges rs
  | .dot => dotRe o
  | .eps => .eps
  | .cat a b => .cat (toRe o a) (toRe o b)
  | .alt a b => .alt (toRe o a) (toRe o b)
  | .group _ a => toRe o a
  | .rep a n m _ =>
    let r := toRe o a
    match m with
    | none => .cat (XSDPattern.repeatExact r n) (.star r)
    | some m => .cat (XSDPattern.repeatExact r n) (XSDPattern.repeatOpt r (m - n))
  | .bol => .ranges [(beginSentinel, beginSentinel)]
  | .eol => .ranges [(endSentinel, endSentinel)]
  | .wordB _ | .ahead _ _ | .behind _ _ | .backref _ => .empty

/-- A lookbehind as ordered-matcher nodes: a positive one holds when one
    alternative matches before the position, a negative one when none does. -/
def behindCRe (neg : Bool) : List (Nat × CRe) → CRe
  | [] => if neg then .eps else .leaf .empty
  | [(k, c)] => .behind neg k c
  | (k, c) :: rest =>
    if neg then .cat (.behind true k c) (behindCRe neg rest)
    else .alt (.behind false k c) (behindCRe neg rest)

/-- A single-character atom of a lookbehind body. -/
def simpleCRe (o : Opts) : Node → CRe
  | .chars rs => .leaf (.ranges rs)
  | .dot => .leaf (dotRe o)
  | _ => .eps

/-- The ordered-matcher tree. -/
def toCRe (o : Opts) : Node → CRe
  | .chars rs => .leaf (.ranges rs)
  | .dot => .leaf (dotRe o)
  | .eps => .eps
  | .cat a b => .cat (toCRe o a) (toCRe o b)
  | .alt a b => .alt (toCRe o a) (toCRe o b)
  | .group n a => .group n (toCRe o a)
  | .rep a n m greedy =>
    let r := toCRe o a
    match m with
    | none => if n == 0 then .star greedy r else .cat (CRe.repeatExact r n) (.star greedy r)
    | some m => .cat (CRe.repeatExact r n) (CRe.repeatOpt r greedy (m - n))
  | .bol => if o.multiline then .lineStart else .anchorStart
  | .eol => if o.multiline then .lineEnd else .anchorEnd
  | .wordB neg => .wordB neg wordRanges.get
  | .ahead neg a => .ahead neg (toCRe o a)
  | .behind neg a =>
    let alts := ((simpleAlts a).getD []).map (fun s =>
      (s.length, s.foldr (fun x acc => .cat (simpleCRe o x) acc) CRe.eps))
    behindCRe neg alts
  | .backref n => .backref o.ci n

/-! ## Compilation -/

/-- The flag characters of F&O 4.0 §6.2. -/
def validFlags (flags : String) : Bool :=
  flags.toList.all fun ch => "smixqc".toList.contains ch

/-- Parse a pattern (after the flag rewrites) into its tree and group names. -/
def parse (ci : Bool) (cps : List Nat) : Option (Node × St) :=
  match pAlt ci (16 * (cps.length + 4)) cps {} with
  | some (r, [], st) => if lookbehindsSimple r then some (r, st) else none
  | _ => none

/-- Compile an F&O 4.0 pattern with flags. Errors: `invalidFlags`
    (err:FORX0001), `invalidPattern` (err:FORX0002). A pattern that matches
    the empty string is not an error here (F&O 4.0 §6.3). -/
def compile (pattern : String) (flags : String) : Except RegexError Compiled :=
  if !validFlags flags then .error (.invalidFlags flags)
  else
    let hasI := flagHas flags 'i'
    let hasQ := flagHas flags 'q'
    let hasS := flagHas flags 's' && !hasQ
    let hasX := flagHas flags 'x' && !hasQ
    let hasC := flagHas flags 'c' && !hasQ
    let hasM := flagHas flags 'm' && !hasQ
    let wrap (p : Re) : Re :=
      if hasM then .cat sigmaAllStar (.cat (absorbMarkers p) sigmaAllStar)
      else .cat gapLeft (.cat p gapRight)
    let cps0 := cpsOfString pattern
    if hasQ then
      let core := literalRegex hasI cps0
      .ok { matchRe := wrap core, capt := .leaf core, multiline := false,
            literalReplacement := true }
    else
      let cps1 := if hasC then stripComments cps0 0 false [] else cps0
      let cps2 := if hasX then stripWs cps1 0 false [] else cps1
      match parse hasI cps2 with
      | none => .error (.invalidPattern pattern)
      | some (node, st) =>
        let o : Opts := { ci := hasI, dotAll := hasS, multiline := hasM }
        let capt := toCRe o node
        match sentinelAnchors node with
        | some _ =>
          .ok { matchRe := wrap (toRe o node), capt, multiline := hasM,
                finalNewline := hasM, names := st.names }
        | none =>
          .ok { matchRe := .empty, capt, multiline := hasM, ordered := true,
                finalNewline := hasM, names := st.names }

end L4Factoidal.Regex.XPath40
