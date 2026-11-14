/-
L4Factoidal.Rendering.CssValues.Grammar — the CSS value definition syntax (CSS Values 4 §2)
as data, and one matcher for it.

A property's grammar is text, as the specifications write it
(`<line-width> || <line-style> || <color>`). `vds` reads that text into a grammar `G`;
`matchG` matches component values against a `G` and gives the canonical value: keywords in
lower case, numbers and units normalised (`Numeric`), colours in their canonical form, the
parts of `||` and `&&` in the order of the grammar, one space between values.

The same matcher gives the computed value when the environment has a context (`Env.ctx`):
the leaves then make lengths absolute and resolve colours. So the specified value, the
computed value and the answer of `CSS.supports` are one function with different leaves.

The matcher is a list-of-successes parser bounded by fuel: it is total, and it tries the
alternatives of the grammar in order, so a value that the grammar accepts in some way is
accepted (up to the bound `cap` on the alternatives kept at each step).
-/
import L4Factoidal.Rendering.CssValues.Numeric

namespace L4Factoidal.Rendering.CssValues

/-- A grammar of the value definition syntax. -/
inductive G where
  /-- A keyword (lower case). The table may write `a=b`: the keyword `a`, whose canonical
  form is `b` (`xyz=xyz-d65`); `a=` is a keyword that is left out of the canonical value
  (a default that is not serialised). This is the table's notation, not the specifications'. -/
  | kw (s : String)
  /-- A literal delimiter: `/`, `,` and the like. -/
  | lit (c : Char)
  /-- `<name>` or `<name [lo,hi]>`: a basic type or a non-terminal. -/
  | ref (name : String) (lo hi : Option Rat)
  /-- `<'property'>`: the grammar of a property; its match is tagged with the name. -/
  | prop (name : String)
  /-- `name( ... )`. -/
  | fn (name : String) (arg : G)
  /-- A simple block: `'[' ... ']'` or `( ... )`. -/
  | block (opener : Char) (g : G)
  /-- Juxtaposition: all, in order. -/
  | seq (xs : List G)
  /-- `|`: exactly one. -/
  | oneOf (xs : List G)
  /-- `||`: one or more, in any order. -/
  | anyOf (xs : List G)
  /-- `&&`: all, in any order. -/
  | allOf (xs : List G)
  /-- A multiplier: `*`, `+`, `?`, `{lo,hi}`, and `#` (comma separated). -/
  | rep (g : G) (lo : Nat) (hi : Option Nat) (comma : Bool)
  /-- `[ ... ]!`: the group must produce at least one value. -/
  | req (g : G)
  deriving Inhabited

/-! ### Reading the syntax -/

/-- A token of the value definition syntax. -/
inductive VT where
  | word (s : String)
  | ref (name : String) (isProp : Bool) (lo hi : Option Rat)
  | fnOpen (name : String)
  | lit (c : Char)
  | lbr | rbr | lpar | rpar | qlb | qrb | bar | dbar | damp
  | star | plus | qmark | hash | bang
  | braces (lo : Nat) (hi : Option Nat)
  deriving DecidableEq, Repr, Inhabited

def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-- One bound of a range: a number (a unit after it is ignored), or `∞` for no bound. -/
def rangeBound (cs : List Char) : Option Rat :=
  let cs := trimChars cs
  if startsNumber cs then some (consumeNumber cs).1 else none

/-- `<...>` contents: a property reference, or a name with an optional range. -/
def refToken (cs : List Char) : VT :=
  let cs := trimChars cs
  match cs with
  | '\'' :: rest => .ref (String.ofList (rest.takeWhile (· != '\''))) true none none
  | _ =>
    let name := cs.takeWhile fun c => c != ' ' && c != '['
    let after := (cs.drop name.length).dropWhile (· != '[')
    match after with
    | '[' :: r =>
      let inner := r.takeWhile (· != ']')
      let lo := inner.takeWhile (· != ',')
      let hi := (inner.drop lo.length).drop 1
      .ref (String.ofList name) false (rangeBound lo) (rangeBound hi)
    | _ => .ref (String.ofList name) false none none

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '@' || c == '='

/-- The tokens of a grammar text. -/
def vdsTokens : Nat → List Char → List VT → List VT
  | 0, _, acc => acc.reverse
  | fuel + 1, cs, acc =>
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c == ' ' || c == '\n' || c == '\t' then vdsTokens fuel rest acc
      else if c == '<' then
        let inner := rest.takeWhile (· != '>')
        vdsTokens fuel ((rest.drop inner.length).drop 1) (refToken inner :: acc)
      else if c == '\'' then
        let inner := rest.takeWhile (· != '\'')
        let after := (rest.drop inner.length).drop 1
        match inner with
        | ['['] => vdsTokens fuel after (.qlb :: acc)
        | [']'] => vdsTokens fuel after (.qrb :: acc)
        | _ => vdsTokens fuel after (inner.reverse.map VT.lit ++ acc)
      else if c == '[' then vdsTokens fuel rest (.lbr :: acc)
      else if c == ']' then vdsTokens fuel rest (.rbr :: acc)
      else if c == '(' then vdsTokens fuel rest (.lpar :: acc)
      else if c == ')' then vdsTokens fuel rest (.rpar :: acc)
      else if c == '|' then
        match rest with
        | '|' :: r => vdsTokens fuel r (.dbar :: acc)
        | _ => vdsTokens fuel rest (.bar :: acc)
      else if c == '&' then
        match rest with
        | '&' :: r => vdsTokens fuel r (.damp :: acc)
        | _ => vdsTokens fuel rest (.lit c :: acc)
      else if c == '*' then vdsTokens fuel rest (.star :: acc)
      else if c == '+' then vdsTokens fuel rest (.plus :: acc)
      else if c == '?' then vdsTokens fuel rest (.qmark :: acc)
      else if c == '#' then vdsTokens fuel rest (.hash :: acc)
      else if c == '!' then vdsTokens fuel rest (.bang :: acc)
      else if c == '{' then
        let inner := rest.takeWhile (· != '}')
        let lo := inner.takeWhile Char.isDigit
        let hiPart := (inner.drop lo.length)
        let hi : Option Nat := match hiPart with
          | ',' :: h => let hd := (trimChars h).takeWhile Char.isDigit; if hd.isEmpty then none else some (digitsVal hd)
          | _ => some (digitsVal lo)
        vdsTokens fuel ((rest.drop inner.length).drop 1) (.braces (digitsVal lo) hi :: acc)
      else if isWordChar c then
        let w := cs.takeWhile isWordChar
        let after := cs.drop w.length
        match after with
        | '(' :: r => vdsTokens fuel r (.fnOpen (String.ofList w) :: acc)
        | _ => vdsTokens fuel after (.word (lower (String.ofList w)) :: acc)
      else vdsTokens fuel rest (.lit c :: acc)

/-- The multipliers after a term. -/
def vdsMults (g : G) : List VT → G × List VT
  | .star :: rest => vdsMults (.rep g 0 none false) rest
  | .plus :: rest => vdsMults (.rep g 1 none false) rest
  | .qmark :: rest => vdsMults (.rep g 0 (some 1) false) rest
  | .hash :: .braces lo hi :: rest => vdsMults (.rep g lo hi true) rest
  | .hash :: rest => vdsMults (.rep g 1 none true) rest
  | .braces lo hi :: rest => vdsMults (.rep g lo hi false) rest
  | .bang :: rest => vdsMults (.req g) rest
  | rest => (g, rest)

mutual
  /-- A grammar at a combinator level: 0 `|`, 1 `||`, 2 `&&`, 3 juxtaposition. -/
  def vdsLevel : Nat → Nat → List VT → Option (G × List VT)
    | 0, _, _ => none
    | fuel + 1, level, ts =>
      if level ≥ 3 then vdsSeq fuel ts []
      else
        match vdsLevel fuel (level + 1) ts with
        | none => none
        | some (g, rest) => vdsSepLoop fuel level rest [g]
  def vdsSepLoop : Nat → Nat → List VT → List G → Option (G × List VT)
    | 0, _, _, _ => none
    | fuel + 1, level, ts, acc =>
      let sep := if level == 0 then VT.bar else if level == 1 then VT.dbar else VT.damp
      let finish : Option (G × List VT) := match acc.reverse with
        | [g] => some (g, ts)
        | gs => some ((if level == 0 then .oneOf gs else if level == 1 then .anyOf gs else .allOf gs), ts)
      match ts with
      | t :: rest =>
        if t == sep then
          match vdsLevel fuel (level + 1) rest with
          | some (g, rest') => vdsSepLoop fuel level rest' (g :: acc)
          | none => none
        else finish
      | [] => finish
  def vdsSeq : Nat → List VT → List G → Option (G × List VT)
    | 0, _, _ => none
    | fuel + 1, ts, acc =>
      let finish : Option (G × List VT) := match acc.reverse with
        | [g] => some (g, ts)
        | gs => some (.seq gs, ts)
      match ts with
      | [] => finish
      | .bar :: _ => finish
      | .dbar :: _ => finish
      | .damp :: _ => finish
      | .rbr :: _ => finish
      | .rpar :: _ => finish
      | .qrb :: _ => finish
      | _ =>
        match vdsTerm fuel ts with
        | some (g, rest) => vdsSeq fuel rest (g :: acc)
        | none => none
  def vdsTerm : Nat → List VT → Option (G × List VT)
    | 0, _ => none
    | fuel + 1, ts =>
      match ts with
      | .word s :: rest => some (vdsMults (.kw s) rest)
      | .ref name isProp lo hi :: rest => some (vdsMults (if isProp then .prop name else .ref name lo hi) rest)
      | .lit c :: rest => some (vdsMults (.lit c) rest)
      | .lbr :: rest =>
        match vdsLevel fuel 0 rest with
        | some (g, .rbr :: rest') => some (vdsMults g rest')
        | _ => none
      | .fnOpen name :: rest =>
        match vdsLevel fuel 0 rest with
        | some (g, .rpar :: rest') => some (vdsMults (.fn name g) rest')
        | _ => none
      | .lpar :: rest =>
        match vdsLevel fuel 0 rest with
        | some (g, .rpar :: rest') => some (vdsMults (.block '(' g) rest')
        | _ => none
      | .qlb :: rest =>
        match vdsLevel fuel 0 rest with
        | some (g, .qrb :: rest') => some (vdsMults (.block '[' g) rest')
        | _ => none
      | _ => none
end

/-- The grammar a text of the value definition syntax denotes. -/
def vds (s : String) : Option G :=
  let cs := s.toList
  let ts := vdsTokens (cs.length + 1) cs []
  match vdsLevel (4 * ts.length + 8) 0 ts with
  | some (g, []) => some g
  | _ => none

/-! ### Matching -/

/-- What the matcher needs from outside: the non-terminals, the property grammars, the
colour parser, and the context of computed values (`none`: specified values). -/
structure Env where
  syntaxOf : String → Option String
  propSyntax : String → Option String
  color : CV → Option String
  ctx : Option Ctx := none

/-- The matches of a grammar at the start of some component values: for each, the
canonical values it gives and the values left. -/
abbrev Res := List (List CV × List CV)

/-- The most alternatives kept at each step. -/
def cap : Nat := 24

/-- The name that tags the match of `<'property'>` (U+0001 then the property name). -/
def tagName (p : String) : String := "\x01" ++ p

def isTag (name : String) : Bool := name.toList.head? == some '\x01'

def cssWide : List String := ["inherit", "initial", "unset", "revert", "revert-layer"]

def G.isComma : G → Bool
  | .lit c => c == ','
  | _ => false

/-- Juxtaposition. A comma of the grammar is left out of the value where the items before
it (since the start or the last comma) or all the items after it are left out (CSS Values
4 §2.1): `emitted` says that an item gave a value since the start or the last comma. -/
def seqWith (m : G → List CV → Res) : List G → Bool → List CV → Res
  | [], _, ts => [([], ts)]
  | g :: gs, emitted, ts =>
    if g.isComma then
      if !emitted then seqWith m gs false ts
      else
        let withComma : Res := match ts with
          | .tok .comma :: rest =>
            (seqWith m gs false rest).filterMap fun (o2, r2) =>
              if o2.isEmpty then none else some (CV.tok .comma :: o2, r2)
          | _ => []
        let without : Res := (seqWith m gs false ts).filter fun (o2, r2) => o2.isEmpty && r2.length == ts.length
        (withComma ++ without).take cap
    else
      ((m g ts).flatMap fun (o1, r1) =>
        (seqWith m gs (emitted || !o1.isEmpty) r1).map fun (o2, r2) => (o1 ++ o2, r2)).take cap

/-- A multiplier, as a loop over the number of repetitions (a tail call, so a list of any
length uses no stack): `frontier` holds the matches of `n` repetitions (their values in
reverse, the values left), `done` the finished matches, the most repetitions first. Each
repetition takes at least one value. -/
def repLoop (m : G → List CV → Res) (g : G) (lo : Nat) (hi : Option Nat) (comma : Bool) :
    Nat → Nat → List (List (List CV) × List CV) → Res → Res
  | 0, _, _, done => done
  | fuel + 1, n, frontier, done =>
    if frontier.isEmpty then done
    else
      let stops : Res := if n ≥ lo then frontier.map fun (chunks, ts) => (chunks.reverse.flatten, ts) else []
      let done := (stops ++ done).take cap
      if (hi.map fun h => decide (n ≥ h)).getD false then done
      else
        let next := (frontier.flatMap fun (chunks, ts) =>
          let start : Option (List CV) :=
            if comma && n > 0 then
              match ts with
              | .tok .comma :: r => some r
              | _ => none
            else some ts
          match start with
          | none => []
          | some ts1 =>
            (m g ts1).filterMap fun (o1, r1) =>
              if r1.length < ts1.length then
                some ((if comma && n > 0 then CV.tok .comma :: o1 else o1) :: chunks, r1)
              else none).take cap
        repLoop m g lo hi comma fuel (n + 1) next done

/-- A multiplier: more repetitions first. -/
def repWith (m : G → List CV → Res) (g : G) (lo : Nat) (hi : Option Nat) (comma : Bool) (ts : List CV) : Res :=
  repLoop m g lo hi comma (ts.length + 2) 0 [([], ts)] []

/-- Insert by index: the list stays in the order of the grammar. -/
def insertIdx (x : Nat × List CV) (xs : List (Nat × List CV)) : List (Nat × List CV) :=
  (xs.filter fun y => y.1 < x.1) ++ x :: (xs.filter fun y => !(y.1 < x.1))

/-- `||` (`all = false`) and `&&` (`all = true`): the parts in any order, each at most
once and each taking at least one value; the output is in the order of the grammar. -/
def setWith (m : G → List CV → Res) (all : Bool) : Nat → List (Nat × G) → List (Nat × List CV) → List CV → Res
  | 0, _, _, _ => []
  | fuel + 1, unused, done, ts =>
    let finish : Res := [((done.map (·.2)).flatten, ts)]
    let stop : Res :=
      if all then
        if unused.all (fun (_, g) => (m g ts).any fun (_, r) => r.length == ts.length) then finish else []
      else if done.isEmpty then [] else finish
    let more : Res := unused.flatMap fun (i, g) =>
      (m g ts).flatMap fun (o, r) =>
        if r.length < ts.length then
          setWith m all fuel (unused.filter (·.1 != i)) (insertIdx (i, o) done) r
        else []
    (more ++ stop).take cap

def indexed (gs : List G) : List (Nat × G) := (List.range gs.length).zip gs

/-- One component value read by `f`. -/
def oneCV (f : CV → Option CV) : List CV → Res
  | cv :: rest =>
    match f cv with
    | some o => [([o], rest)]
    | none => []
  | [] => []

/-- A basic type, or a non-terminal expanded through `m`. -/
def leaf (env : Env) (m : G → List CV → Res) (name : String) (lo hi : Option Rat) (ts : List CV) : Res :=
  let num := fun (req : NumReq) => oneCV (numeric env.ctx { req with lo := lo, hi := hi }) ts
  match name with
  | "number" => num { kind := .number }
  | "integer" => num { kind := .number, integer := true }
  | "length" => num { kind := .length }
  | "percentage" => num { kind := .percent }
  | "length-percentage" => num { kind := .length, allowPct := true }
  | "angle" => num { kind := .angle }
  | "angle-percentage" => num { kind := .angle, allowPct := true }
  | "time" => num { kind := .time }
  | "time-percentage" => num { kind := .time, allowPct := true }
  | "frequency" => num { kind := .frequency }
  | "frequency-percentage" => num { kind := .frequency, allowPct := true }
  | "resolution" => num { kind := .resolution }
  | "flex" => num { kind := .flex }
  | "zero" => oneCV (fun cv => match cv with
      | .tok (.num v _) => if v == 0 then some (.tok (.dim 0 true "deg")) else none
      | _ => none) ts
  | "string" => oneCV (fun cv => match cv with
      | .tok (.str s) => some (.tok (.str s))
      | _ => none) ts
  | "url" => oneCV (fun cv => match cv with
      | .tok (.url s) => some (.raw ("url(" ++ serializeString s ++ ")"))
      | .fn name args =>
        if lower name == "url" || lower name == "src" then
          match stripWs args with
          | [.tok (.str s)] => some (.raw (lower name ++ "(" ++ serializeString s ++ ")"))
          | _ => none
        else none
      | _ => none) ts
  | "custom-ident" => oneCV (fun cv => match cv with
      | .tok (.ident s) => if cssWide.contains (lower s) || lower s == "default" then none else some (.tok (.ident s))
      | _ => none) ts
  | "dashed-ident" | "custom-property-name" => oneCV (fun cv => match cv with
      | .tok (.ident s) => if s.length > 2 && (s.toList.take 2) == ['-', '-'] then some (.tok (.ident s)) else none
      | _ => none) ts
  | "ident" => oneCV (fun cv => match cv with
      | .tok (.ident s) => some (.tok (.ident s))
      | _ => none) ts
  | "color" | "hex-color" => oneCV (fun cv => (env.color cv).map CV.raw) ts
  | "declaration-value" | "any-value" => if ts.isEmpty then [] else [([.raw (rawText ts)], [])]
  | _ =>
    match (env.syntaxOf name).bind vds with
    | some g => m g ts
    | none => []

/-- The matches of grammar `g` at the start of `ts`. -/
def matchG (env : Env) : Nat → G → List CV → Res
  | 0, _, _ => []
  | fuel + 1, g, ts =>
    match g with
    | .kw s =>
      match ts with
      | .tok (.ident i) :: rest =>
        match s.splitOn "=" with
        | [k] => if lower i == k then [([.tok (.ident k)], rest)] else []
        | [k, canon] => if lower i == k then [(if canon == "" then [] else [.tok (.ident canon)], rest)] else []
        | _ => []
      | _ => []
    | .lit c =>
      match ts with
      | .tok .comma :: rest => if c == ',' then [([.tok .comma], rest)] else []
      | .tok .colon :: rest => if c == ':' then [([.tok .colon], rest)] else []
      | .tok (.delim d) :: rest => if d == c then [([.tok (.delim d)], rest)] else []
      | _ => []
    | .ref name lo hi => leaf env (matchG env fuel) name lo hi ts
    | .prop name =>
      match (env.propSyntax name).bind vds with
      | some g' => (matchG env fuel g' ts).map fun (o, r) => ([CV.fn (tagName name) o], r)
      | none => []
    | .fn name arg =>
      match ts with
      | .fn n args :: rest =>
        if lower n == lower name then
          ((matchG env fuel arg (stripWs args)).filterMap fun (o, r) =>
            if r.isEmpty then some ([CV.fn name o], rest) else none).take 1
        else []
      | _ => []
    | .block opener inner =>
      match ts with
      | .block o body :: rest =>
        if o == opener then
          ((matchG env fuel inner (stripWs body)).filterMap fun (o', r) =>
            if r.isEmpty then some ([CV.block opener o'], rest) else none).take 1
        else []
      | _ => []
    | .seq gs => seqWith (matchG env fuel) gs false ts
    | .oneOf gs => (gs.flatMap fun g' => matchG env fuel g' ts).take cap
    | .anyOf gs => setWith (matchG env fuel) false (gs.length + 1) (indexed gs) [] ts
    | .allOf gs => setWith (matchG env fuel) true (gs.length + 1) (indexed gs) [] ts
    | .rep g' lo hi comma => repWith (matchG env fuel) g' lo hi comma ts
    | .req g' => (matchG env fuel g' ts).filter fun (o, _) => !o.isEmpty

/-- The depth the matcher may go to: grammar nesting plus non-terminal expansion. -/
def matchFuel : Nat := 96

/-- The canonical values of `cvs` under grammar `g`: the first match that takes all of
them (tags of `<'property'>` matches are kept). -/
def matchAll (env : Env) (g : G) (cvs : List CV) : Option (List CV) :=
  (matchG env matchFuel g cvs).findSome? fun (o, r) => if r.isEmpty then some o else none

/-- Remove the tags of property matches, splicing their contents in place. -/
def untag : Nat → List CV → List CV
  | 0, cvs => cvs
  | fuel + 1, cvs => cvs.flatMap fun cv => match cv with
    | .fn name args => if isTag name then untag fuel args else [.fn name (untag fuel args)]
    | .block o body => [.block o (untag fuel body)]
    | cv => [cv]

/-- Whether the values hold a function named `name` at any depth. -/
def hasFn (name : String) : Nat → List CV → Bool
  | 0, _ => false
  | fuel + 1, cvs => cvs.any fun cv => match cv with
    | .fn n args => lower n == name || hasFn name fuel args
    | .block _ body => hasFn name fuel body
    | _ => false

/-- Whether the values hold a token that makes any declaration invalid at the top level
(CSS Syntax 3 §5.4.4: bad strings, bad urls, unmatched closing tokens, a top-level `;` or `!`, a `{}` block). -/
def hasBadToken : Nat → Bool → List CV → Bool
  | 0, _, _ => true
  | fuel + 1, top, cvs => cvs.any fun cv => match cv with
    | .tok .badStr | .tok .badUrl | .tok .rparen | .tok .rbracket | .tok .rbrace => true
    | .tok .semicolon => top
    | .tok (.delim '!') => top
    | .fn _ args => hasBadToken fuel false args
    | .block o body => (top && o == '{') || hasBadToken fuel false body
    | _ => false

/-! ### Tests -/

private def testEnv : Env :=
  { syntaxOf := fun n => match n with
      | "line-width" => some "<length [0,∞]> | thin | medium | thick"
      | "line-style" => some "none | hidden | dotted | dashed | solid | double | groove | ridge | inset | outset"
      | "shadow" => some "<color>? && [ <length>{2} <length [0,∞]>? <length>? ] && inset?"
      | "fit()" => some "fit-content( <length-percentage [0,∞]> )"
      | _ => none
    propSyntax := fun p => match p with
      | "margin-top" => some "<length-percentage> | auto"
      | _ => none
    color := fun cv => match cv with
      | .tok (.ident s) => if ["red", "blue"].contains (lower s) then some (lower s) else none
      | _ => none }

private def run (grammar value : String) (ctx : Option Ctx := none) : Option String :=
  match vds grammar with
  | none => some "BAD GRAMMAR"
  | some g => (matchAll { testEnv with ctx := ctx } g (stripWs (CV.parse value))).map fun o => serialize (untag 8 o)

#guard run "auto | <length>" "AUTO" == some "auto"
#guard run "auto | <length>" "1PX" == some "1px"
#guard run "auto | <length>" "1px 2px" == none
#guard run "<line-width> || <line-style> || <color>" "RED solid 1px" == some "1px solid red"
#guard run "<line-width> || <line-style> || <color>" "solid" == some "solid"
#guard run "<line-width> || <line-style> || <color>" "solid solid" == none
#guard run "<line-width> || <line-style> || <color>" "" == none
#guard run "<line-width> || <line-style> || <color>" "-1px solid" == none
#guard run "<'margin-top'>{1,4}" "1px auto 2%" == some "1px auto 2%"
#guard run "<'margin-top'>{1,4}" "1px 1px 1px 1px 1px" == none
#guard run "<shadow>#" "1px 2px red, inset 0 0 3px blue" == some "red 1px 2px, blue 0px 0px 3px inset"
#guard run "none | <shadow>#" "none" == some "none"
#guard run "<length>#" "1px,2px , 3px" == some "1px, 2px, 3px"
#guard run "<length>#" "1px,2px," == none
#guard run "<length>#{2}" "1px, 2px" == some "1px, 2px"
#guard run "<length>#{2}" "1px" == none
#guard run "[ <length> | <percentage> ]{2} / <number>" "1px 2% / 3" == some "1px 2% / 3"
#guard run "<fit()> | auto" "FIT-CONTENT( 10% )" == some "fit-content(10%)"
#guard run "<fit()> | auto" "fit-content(-1px)" == none
#guard run "[ a | b ]? c" "c" == some "c"
#guard run "[ a | b ]? c" "b c" == some "b c"
#guard run "a && b? && c" "c a" == some "a c"
#guard run "a && b? && c" "c" == none
#guard run "[ a? b? ]!" "" == none
#guard run "[ a? b? ]!" "b" == some "b"
#guard run "'[' <custom-ident>* ']'" "[ x y ]" == some "[x y]"
#guard run "<custom-ident>" "inherit" == none
#guard run "<string>+" "'a' \"b\"" == some "\"a\" \"b\""
#guard run "<url>" "url(a.png)" == some "url(\"a.png\")"
#guard run "<length>" "2em" (some {}) == some "32px"
#guard run "f( <length> , <length>? )" "f(1px)" == some "f(1px)"
#guard run "f( <length> , <length>? )" "f(1px,)" == none
#guard run "f( <length> , <length>? )" "F(1px, 2px)" == some "f(1px, 2px)"
#guard run "f( [ a || b ]? , <length># )" "f(1px, 2px)" == some "f(1px, 2px)"
#guard run "f( [ a || b ]? , <length># )" "f(b a, 1px)" == some "f(a b, 1px)"
#guard run "f( [ a || b ]? , <length># )" "f(, 1px)" == none
#guard run "a , b? , c" "a, c" == some "a, c"
#guard run "in [ xyz=xyz-d65 | lab ] [ shorter= hue= | longer hue ]?" "in XYZ shorter hue" == some "in xyz-d65"
#guard run "in [ xyz=xyz-d65 | lab ] [ shorter= hue= | longer hue ]?" "in lab longer hue" == some "in lab longer hue"
#guard run "a , b? , c" "a, , c" == none
#guard run "translateX( <length> )" "TRANSLATEX(1px)" == some "translateX(1px)"
#guard run "<integer [1,∞]>" "0" == none
#guard run "<integer [1,∞]>" "2" == some "2"

end L4Factoidal.Rendering.CssValues
