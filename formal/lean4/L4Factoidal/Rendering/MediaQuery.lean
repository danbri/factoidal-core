/-! Media queries (Media Queries Level 4, W3C CR), the subset this engine evaluates.

A media query list is read into `Query` values, or into nothing when it uses syntax or a
feature that this module does not read. The caller decides what nothing means: a `media`
attribute that can not be read is refused in strict mode and skipped in liberal mode
(`WebDocument`), and an `@media` block that can not be read does not apply.

Read here (MQ4 §2, §3, §4):
* media types `all`, `screen`, `print`; other names, the deprecated types (`tv`,
  `speech`, ...) included, are types that match nothing (MQ4 §2.3);
* the modifiers `only` and `not` before a type, and `not` before one condition;
* conditions joined by `and` (`or` is not read);
* the features `width`, `min-width`, `max-width`, `height`, `min-height`, `max-height`,
  in the `name: value` form and the range form (`width >= 600px`,
  `400px <= width < 800px`), `orientation` and `prefers-color-scheme`;
* lengths in `px`, `em` and `rem` (16 px, the initial font size, MQ4 §1.3), and `0`.

A feature whose value the environment does not give (`Env.width = none`) is unknown, and
a query with an unknown feature is false, with `not` or without it (MQ4 §3.4: unknown
evaluates as false at the top level). An empty list is true (MQ4 §2.1). -/
namespace L4Factoidal.Rendering.MediaQuery

/-- What a media query is evaluated against. Widths and heights are CSS pixels. -/
structure Env where
  medium : String := "screen"
  width : Option Float := none
  height : Option Float := none
  /-- `prefers-color-scheme: dark` holds; `none` when the host does not say. -/
  dark : Option Bool := none
  deriving Repr, Inhabited

inductive Cmp where
  | lt | le | eq | ge | gt
  deriving Repr, DecidableEq

def Cmp.flip : Cmp → Cmp
  | .lt => .gt | .le => .ge | .eq => .eq | .ge => .le | .gt => .lt

def Cmp.test (c : Cmp) (a b : Float) : Bool :=
  match c with
  | .lt => a < b | .le => a <= b | .eq => a == b | .ge => a >= b | .gt => a > b

inductive Feature where
  /-- The viewport width compared with a length: `width cmp px`. -/
  | width (cmp : Cmp) (px : Float)
  | height (cmp : Cmp) (px : Float)
  | dark (on : Bool)
  | portrait (on : Bool)
  deriving Repr

/-- One query: `not`, the media type (none: any), and the features, all of which must hold. -/
structure Query where
  negated : Bool := false
  type : Option String := none
  features : List Feature := []
  deriving Repr

inductive Tok where
  | word (s : String) | lp | rp | colon | comma | op (c : Cmp)
  deriving Repr, DecidableEq

private def wordChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '%'
private def space (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
private def flush (cur : String) (acc : List Tok) : List Tok := if cur.isEmpty then acc else .word cur :: acc

/-- Tokens of a query list, lower case. A character outside this grammar gives none. -/
def tokenize : List Char → String → List Tok → Option (List Tok)
  | [], cur, acc => some (flush cur acc).reverse
  | '<' :: '=' :: cs, cur, acc => tokenize cs "" (.op .le :: flush cur acc)
  | '>' :: '=' :: cs, cur, acc => tokenize cs "" (.op .ge :: flush cur acc)
  | c :: cs, cur, acc =>
    if wordChar c then tokenize cs (cur.push c.toLower) acc
    else
      let acc := flush cur acc
      if space c then tokenize cs "" acc
      else if c == '(' then tokenize cs "" (.lp :: acc)
      else if c == ')' then tokenize cs "" (.rp :: acc)
      else if c == ':' then tokenize cs "" (.colon :: acc)
      else if c == ',' then tokenize cs "" (.comma :: acc)
      else if c == '<' then tokenize cs "" (.op .lt :: acc)
      else if c == '>' then tokenize cs "" (.op .gt :: acc)
      else if c == '=' then tokenize cs "" (.op .eq :: acc)
      else none

/-- A plain decimal number: digits with at most one point. -/
def decimal (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => if !a.isEmpty && a.all Char.isDigit then a.toNat?.map Nat.toFloat else none
  | [a,b] =>
    if (a.isEmpty && b.isEmpty) || !a.all Char.isDigit || !b.all Char.isDigit || b.length > 9 then none
    else
      let whole := (if a.isEmpty then 0 else a.toNat?.getD 0).toFloat
      let frac := (if b.isEmpty then 0 else b.toNat?.getD 0).toFloat / (10 ^ b.length).toFloat
      some (whole+frac)
  | _ => none

/-- A length in CSS px: `px`, `em` and `rem` (16 px), or `0`. -/
def length (s : String) : Option Float :=
  if s == "0" then some 0
  else if s.endsWith "rem" then (decimal (s.dropEnd 3).toString).map (· * 16)
  else if s.endsWith "em" then (decimal (s.dropEnd 2).toString).map (· * 16)
  else if s.endsWith "px" then decimal (s.dropEnd 2).toString
  else none

/-- A feature of the `name: value` form. -/
def plain (name value : String) : Option Feature :=
  match name with
  | "width" => (length value).map (.width .eq)
  | "min-width" => (length value).map (.width .ge)
  | "max-width" => (length value).map (.width .le)
  | "height" => (length value).map (.height .eq)
  | "min-height" => (length value).map (.height .ge)
  | "max-height" => (length value).map (.height .le)
  | "prefers-color-scheme" =>
    if value == "dark" then some (.dark true) else if value == "light" then some (.dark false) else none
  | "orientation" =>
    if value == "portrait" then some (.portrait true) else if value == "landscape" then some (.portrait false) else none
  | _ => none

/-- A range feature `name cmp value`. -/
def range (name : String) (c : Cmp) (value : String) : Option Feature :=
  match name with
  | "width" => (length value).map (.width c)
  | "height" => (length value).map (.height c)
  | _ => none

/-- The features inside one pair of parentheses. -/
def inParens : List Tok → Option (List Feature)
  | [.word n, .colon, .word v] => (plain n v).map ([·])
  | [.word a, .op c, .word b] =>
    -- `width >= 600px` or `600px <= width`: the name is the word that is not a length.
    if (length a).isNone then (range a c b).map ([·]) else (range b c.flip a).map ([·])
  | [.word v1, .op c1, .word n, .op c2, .word v2] => do
    let a ← range n c1.flip v1
    let b ← range n c2 v2
    some [a,b]
  | _ => none

/-- `( ... ) and ( ... ) ...` up to the end, after the features `acc`. A loop: each step is a
tail call (the tail-recursion gate). -/
def conditions : Nat → List Tok → List Feature → Option (List Feature)
  | 0, _, _ => none
  | _+1, [], acc => some acc
  | fuel+1, .lp :: rest, acc =>
    match rest.span (· != .rp) with
    | (inside, .rp :: after) =>
      match inParens inside with
      | none => none
      | some here =>
        match after with
        | [] => some (acc ++ here)
        | .word "and" :: more@(_ :: _) => conditions fuel more (acc ++ here)
        | _ => none
    | _ => none
  | _+1, _, _ => none

private def reserved : List String := ["and","or","not","only","layer"]

/-- One query of a list. -/
def query (ts : List Tok) : Option Query :=
  let typed := fun (negated : Bool) (rest : List Tok) => match rest with
    | [.word t] => if reserved.contains t then none else some {negated, type := some t}
    | .word t :: .word "and" :: more@(_ :: _) =>
      if reserved.contains t then none
      else (conditions (more.length+1) more []).map fun fs => {negated, type := some t, features := fs}
    | _ => none
  match ts with
  | .word "only" :: rest => typed false rest
  | .word "not" :: .lp :: rest =>
    -- `not` before a condition takes one parenthesised condition (MQ4 §3).
    if rest.getLast? != some .rp || rest.count .rp != 1 then none
    else (inParens rest.dropLast).map fun fs => {negated := true, features := fs}
  | .word "not" :: rest => typed true rest
  | .lp :: _ => (conditions (ts.length+1) ts []).map fun fs => {features := fs}
  | rest => typed false rest

/-- Split the tokens at the commas of the list. -/
def splitList (ts : List Tok) : List (List Tok) :=
  (ts.foldl (fun (acc : List (List Tok)) t => match acc with
    | [] => if t == .comma then [[],[]] else [[t]]
    | cur :: done => if t == .comma then [] :: (cur.reverse :: done) else (t :: cur) :: done) []
  |> fun acc => match acc with
    | [] => []
    | cur :: done => (cur.reverse :: done).reverse)

/-- A media query list, or none when one of its queries can not be read. An empty or
blank list is the empty list. -/
def parse (text : String) : Option (List Query) := do
  let ts ← tokenize text.toList "" []
  if ts.isEmpty then return []
  (splitList ts).mapM query

def Feature.eval (env : Env) : Feature → Option Bool
  | .width c px => env.width.map (c.test · px)
  | .height c px => env.height.map (c.test · px)
  | .dark on => env.dark.map (· == on)
  | .portrait on => match env.width, env.height with
    | some w, some h => some ((h >= w) == on)
    | _, _ => none

def typeMatches (env : Env) : Option String → Bool
  | none => true
  | some t => t == "all" || t == env.medium

/-- A query holds. An unknown feature makes it false, with `not` or without. -/
def Query.eval (env : Env) (q : Query) : Bool :=
  match q.features.mapM (·.eval env) with
  | none => false
  | some values =>
    let holds := typeMatches env q.type && values.all id
    if q.negated then !holds else holds

/-- A list holds when it is empty or one of its queries holds. -/
def evalList (env : Env) (qs : List Query) : Bool := qs.isEmpty || qs.any (·.eval env)

/-- Whether `text` holds in `env`; none when it can not be read. -/
def holds (env : Env) (text : String) : Option Bool := (parse text).map (evalList env)

/-- `holds`, with a list that can not be read false (an `@media` block that does not apply). -/
def applies (env : Env) (text : String) : Bool := (holds env text).getD false

/-- A list that can not be read is never read as true. -/
theorem applies_readable (env : Env) (text : String) (h : applies env text = true) :
    ∃ qs, parse text = some qs ∧ evalList env qs = true := by
  unfold applies holds at h
  cases hp : parse text with
  | none => simp [hp] at h
  | some qs => exact ⟨qs, rfl, by simpa [hp] using h⟩

private def wide : Env := {width := some 800, height := some 600, dark := some false}
private def narrow : Env := {width := some 400, height := some 700, dark := some true}
#guard holds wide "" == some true && holds wide "all" == some true && holds wide "screen" == some true
#guard holds wide "print" == some false && holds {wide with medium := "print"} "print" == some true
#guard holds wide "(min-width: 500px)" == some true && holds narrow "(min-width: 500px)" == some false
#guard holds wide "(max-width: 600px)" == some false && holds narrow "(max-width: 600px)" == some true
#guard holds wide "screen and (min-width: 31.25em)" == some true && holds narrow "screen and (min-width:31.25em)" == some false
#guard holds wide "only screen and (min-width: 500px) and (max-width: 1000px)" == some true
#guard holds wide "not print" == some true && holds wide "not screen" == some false
#guard holds wide "not screen and (min-width: 900px)" == some true
#guard holds wide "not (min-width: 500px)" == some false && holds narrow "not (min-width: 500px)" == some true
#guard holds wide "print, (min-width: 500px)" == some true && holds narrow "print, (min-width: 500px)" == some false
#guard holds wide "(prefers-color-scheme: dark)" == some false && holds narrow "(prefers-color-scheme: dark)" == some true
#guard holds wide "(prefers-color-scheme: light)" == some true
#guard holds wide "(width >= 600px)" == some true && holds narrow "(width >= 600px)" == some false
#guard holds wide "(400px <= width < 900px)" == some true && holds narrow "(500px <= width < 900px)" == some false
#guard holds wide "(orientation: landscape)" == some true && holds narrow "(orientation: portrait)" == some true
#guard holds wide "tv" == some false && holds wide "speech" == some false && holds wide "SCREEN" == some true
-- What this module does not read: none.
#guard holds wide "(min-resolution: 2dppx)" == none && holds wide "(hover: hover)" == none
#guard holds wide "screen or print" == none && holds wide "(min-width: 500px) or (max-width: 100px)" == none
#guard holds wide "(min-width: calc(10px + 2em))" == none && holds wide "and" == none
#guard holds wide "(min-width: 500px) and" == none && holds wide "screen," == none
-- With no width (the environment does not say), a width query is false, with `not` too.
#guard holds {} "(min-width: 500px)" == some false && holds {} "not (min-width: 500px)" == some false
#guard holds {} "screen" == some true && holds {} "not print" == some true
#guard !applies wide "(hover: hover)" && applies wide "screen and (max-width: 900px)"

end L4Factoidal.Rendering.MediaQuery
