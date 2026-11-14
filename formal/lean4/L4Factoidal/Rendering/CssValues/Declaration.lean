/-
L4Factoidal.Rendering.CssValues.Declaration — the CSS declaration block of CSSOM §6.6: the
state behind `element.style`.

A block is a list of longhand declarations with canonical values (`Decl`). It is read from
text (`Block.parse`: the `style` attribute, or `cssText`), changed (`set`, `removeProperty`)
and written back as text (`Block.text`, CSSOM "serialize a CSS declaration block", with
shorthands put back together where all their longhands are there). The page's
`CSSStyleDeclaration` is glue over `styleOp`: the block lives in the `style` attribute, so
there is no second copy of the state.

A shorthand that has no generic shape here (`Properties.shapeOf`) is kept whole under its
own name: it parses, serialises and round-trips, and its longhands read as "".
-/
import L4Factoidal.Rendering.CssValues.Properties

namespace L4Factoidal.Rendering.CssValues

/-- One declaration of a block: a property name of the table (or a custom property), its
canonical value, and the important flag. -/
structure Decl where
  name : String
  value : String
  important : Bool := false
  deriving Repr, DecidableEq, Inhabited

abbrev Block := List Decl

/-! ### Splitting a block text -/

/-- Split CSS text at the top-level occurrences of `sep`: not inside strings, brackets or
comments (comments are dropped). Tail recursive: `cur` and `acc` are reversed. -/
def splitTop (sep : Char) : Nat → List Char → Nat → Option Char → List Char → List (List Char) → List (List Char)
  | 0, _, _, _, cur, acc => (cur.reverse :: acc).reverse
  | fuel + 1, cs, depth, quote, cur, acc =>
    match cs with
    | [] => (cur.reverse :: acc).reverse
    | c :: rest =>
      match quote with
      | some q =>
        if c == '\\' then
          match rest with
          | d :: rest' => splitTop sep fuel rest' depth quote (d :: c :: cur) acc
          | [] => splitTop sep fuel rest depth quote (c :: cur) acc
        else splitTop sep fuel rest depth (if c == q then none else quote) (c :: cur) acc
      | none =>
        if c == '/' && rest.head? == some '*' then
          splitTop sep fuel (skipComment (rest.length + 1) (rest.drop 1)) depth quote cur acc
        else if c == '\\' then
          match rest with
          | d :: rest' => splitTop sep fuel rest' depth quote (d :: c :: cur) acc
          | [] => splitTop sep fuel rest depth quote (c :: cur) acc
        else if c == '"' || c == '\'' then splitTop sep fuel rest depth (some c) (c :: cur) acc
        else if c == '(' || c == '[' || c == '{' then splitTop sep fuel rest (depth + 1) quote (c :: cur) acc
        else if c == ')' || c == ']' || c == '}' then splitTop sep fuel rest (depth - 1) quote (c :: cur) acc
        else if c == sep && depth == 0 then splitTop sep fuel rest depth quote [] (cur.reverse :: acc)
        else splitTop sep fuel rest depth quote (c :: cur) acc

/-- A value text and whether it ends with `!important` (CSS Syntax 3 §5.4.6). -/
def splitImportant (cs : List Char) : List Char × Bool :=
  let r := cs.reverse.dropWhile isWs
  if (r.take 9).map Char.toLower == "important".toList.reverse then
    match (r.drop 9).dropWhile isWs with
    | '!' :: r' => (r'.reverse, true)
    | _ => (cs, false)
  else (cs, false)

/-- One piece of a block text as name, value text and important flag. -/
def declOf (piece : List Char) : Option (String × String × Bool) :=
  match splitTop ':' (piece.length + 1) piece 0 none [] [] with
  | name :: v :: more =>
    let name := trimText (String.ofList name)
    let valueChars := (v :: more).foldl (fun acc part => if acc.isEmpty then part else acc ++ ':' :: part) []
    -- the first part may be empty: keep the colons of the rest
    let valueChars := if v.isEmpty && !more.isEmpty then ':' :: valueChars else valueChars
    let (value, important) := splitImportant valueChars
    if name.isEmpty then none else some (name, String.ofList value, important)
  | _ => none

/-! ### The block -/

def Block.find (b : Block) (name : String) : Option Decl := b.find? (·.name == name)

def Block.remove (b : Block) (name : String) : Block := b.filter (·.name != name)

/-- Set a declaration where the property already is, else at the end (CSSOM §6.6.1 "set a
CSS declaration"). -/
def Block.put (b : Block) (d : Decl) : Block :=
  if b.any (·.name == d.name) then b.map fun x => if x.name == d.name then d else x
  else b ++ [d]

/-- Set a declaration at the end, removing an earlier one of the property (parsing). -/
def Block.putLast (b : Block) (d : Decl) : Block := b.remove d.name ++ [d]

/-- The block a text denotes (CSSOM §6.6.1 "parse a CSS declaration block"): invalid
declarations are dropped, shorthands expanded, the last declaration of a property wins. -/
def Block.parse (text : String) : Block :=
  let cs := preprocess text.toList
  let pieces := splitTop ';' (cs.length + 1) cs 0 none [] []
  pieces.foldl (fun b piece =>
    match declOf piece with
    | none => b
    | some (name, value, important) =>
      match expand name value with
      | none => b
      | some ds => ds.foldl (fun b (n, v) => b.putLast { name := n, value := v, important := important }) b) []

/-- The declarations of a block text whose property name (lower case) is in `names`: the
others are not parsed. For a reader that wants one property (`ComputedGeneric.cascaded`),
so that reading one computed value does not parse every declaration of the block. -/
def Block.parseOnly (names : List String) (text : String) : Block :=
  let cs := preprocess text.toList
  let pieces := splitTop ';' (cs.length + 1) cs 0 none [] []
  pieces.foldl (fun b piece =>
    match declOf piece with
    | none => b
    | some (name, value, important) =>
      if !names.contains (propertyName name) then b
      else
        match expand name value with
        | none => b
        | some ds => ds.foldl (fun b (n, v) => b.putLast { name := n, value := v, important := important }) b) []

/-- The property names a block text declares, as written (lower case, except custom
properties): no value is parsed. -/
def declNames (text : String) : List String :=
  let cs := preprocess text.toList
  (splitTop ';' (cs.length + 1) cs 0 none [] []).filterMap fun piece =>
    (declOf piece).map fun (name, _, _) => if isCustom name then name else lower name

/-- The longhand declarations of shorthand `row`, when all are in the block with one
important flag. -/
def Block.longhandsOf (b : Block) (row : Property) : Option (List Decl) :=
  let ds := row.longhands.filterMap b.find
  match ds with
  | [] => none
  | d :: rest =>
    if ds.length == row.longhands.length && rest.all (·.important == d.important) then some ds else none

/-- `getPropertyValue` (CSSOM §6.6.1): the value of a longhand, or of a shorthand when all
its longhands are set and can be written as one value; "" otherwise. -/
def Block.get (b : Block) (property : String) : String :=
  let p := propertyName property
  match b.find p with
  | some d => d.value
  | none =>
    match lookup p with
    | none => ""
    | some row =>
      if row.longhands.isEmpty then ""
      else
        match b.longhandsOf row with
        | none => ""
        | some ds => recombine row fun l => ((ds.find? (·.name == l)).map (·.value)).getD ""

/-- `getPropertyPriority`: "important" or "". -/
def Block.priority (b : Block) (property : String) : String :=
  let p := propertyName property
  match b.find p with
  | some d => if d.important then "important" else ""
  | none =>
    match lookup p with
    | none => ""
    | some row =>
      match b.longhandsOf row with
      | some (d :: _) => if d.important then "important" else ""
      | _ => ""

/-- `removeProperty`: the declarations of the property (for a shorthand, of its longhands)
removed. -/
def Block.removeProperty (b : Block) (property : String) : Block :=
  let p := propertyName property
  match lookup p with
  | none => b.remove p
  | some row => row.longhands.foldl Block.remove (b.remove p)

/-- `setProperty(property, value, priority)` (CSSOM §6.6.1): an empty value removes the
property; a priority other than "" or "important" and a value that does not parse leave
the block as it is. -/
def Block.set (b : Block) (property value priority : String) : Block :=
  if trimText value == "" then b.removeProperty property
  else if !(priority == "" || lower priority == "important") then b
  else
    match expand property value with
    | none => b
    | some ds =>
      ds.foldl (fun b (n, v) => b.put { name := n, value := v, important := lower priority == "important" }) b

/-- The property names of the block in order (`item`, `length`). -/
def Block.names (b : Block) : List String := b.map (·.name)

/-- For each longhand, the shorthands with a generic shape that have it among their
longhands: most longhands first; legacy aliases left out. Built once (a lazy constant). -/
def shorthandIndex : Thunk (Std.HashMap String (List Property)) := Thunk.mk fun _ =>
  let rows := Data.properties.toList.filterMap fun (n, _, _, _, ls) =>
    if ls == "" || (aliasMap.get.contains n) then none
    else
      match lookup n with
      | some row => if (shapeOf row).isSome then some row else none
      | none => none
  let rows := rows.mergeSort fun a b => a.longhands.length ≥ b.longhands.length
  rows.foldl (fun m row =>
    row.longhands.foldl (fun m l => m.insert l ((m[l]?).getD [] ++ [row])) m) {}

/-- The shorthands with a generic shape that have `name` among their longhands. -/
def shorthandsOf (name : String) : List Property := (shorthandIndex.get[name]?).getD []

def declText (name value : String) (important : Bool) : String :=
  name ++ ": " ++ value ++ (if important then " !important" else "") ++ ";"

/-- CSSOM §6.6.1 "serialize a CSS declaration block": each declaration once, as part of
the first shorthand that can stand for it and its fellows, else alone. -/
def Block.textLoop : Nat → Block → List String → List String
  | 0, _, out => out.reverse
  | fuel + 1, b, out =>
    match b with
    | [] => out.reverse
    | d :: rest =>
      let viaShorthand := (shorthandsOf d.name).findSome? fun row =>
        match Block.longhandsOf b row with
        | none => none
        | some ds =>
          let v := recombine row fun l => ((ds.find? (·.name == l)).map (·.value)).getD ""
          if v == "" then none else some (row, v)
      match viaShorthand with
      | some (row, v) =>
        Block.textLoop fuel (rest.filter fun x => !row.longhands.contains x.name) (declText row.name v d.important :: out)
      | none => Block.textLoop fuel rest (declText d.name d.value d.important :: out)

def Block.text (b : Block) : String := " ".intercalate (Block.textLoop (b.length + 1) b [])

/-! ### The page's protocol -/

/-- The operations of a page's `CSSStyleDeclaration` and of `CSS.supports`, as text: the
fields of `q` are separated by U+0000, the first is the verb.

- `get` block property → the value
- `pri` block property → "important" or ""
- `set` block property value priority → the new block text, or U+0001 when the block is as it was
- `rem` block property → the new block text (or U+0001), U+0000, the old value
- `txt` text → the block text in canonical form (`cssText`)
- `names` block → the property names, separated by U+0000
- `sup` property value → "1" or "0"
- `val` property value → "1" and the canonical value, or "0" -/
def styleOp (q : String) : String :=
  match q.splitOn "\x00" with
  | ["get", block, property] => (Block.parse block).get property
  | ["pri", block, property] => (Block.parse block).priority property
  | ["set", block, property, value, priority] =>
    let b := Block.parse block
    let b' := b.set property value priority
    if b' == b then "\x01" else b'.text
  | ["rem", block, property] =>
    let b := Block.parse block
    let b' := b.removeProperty property
    (if b' == b then "\x01" else b'.text) ++ "\x00" ++ b.get property
  | ["txt", text] => (Block.parse text).text
  | ["names", block] => "\x00".intercalate (Block.parse block).names
  | ["sup", property, value] => if supports property value then "1" else "0"
  | ["val", property, value] =>
    match specified property value with
    | some v => "1" ++ v
    | none => "0"
  | _ => ""

/-! ### Tests and theorems -/

#guard (Block.parse "color: RED; margin: 1px 2px").text == "color: red; margin: 1px 2px;"
#guard (Block.parse "color: red; color: blue").text == "color: blue;"
#guard (Block.parse "color: red; nonsense: 1; width: -1px; height: 2px").text == "color: red; height: 2px;"
#guard (Block.parse "color: red !important").text == "color: red !important;"
#guard (Block.parse "background-image: url(\"a;b:c\"); top: 0").text == "background-image: url(\"a;b:c\"); top: 0px;"
#guard (Block.parse "--x:  a:b ; color: var(--x)").text == "--x: a:b; color: var(--x);"
#guard (Block.parse "margin-top: 1px; margin-right: 2px; margin-bottom: 1px; margin-left: 2px").text == "margin: 1px 2px;"
#guard (Block.parse "margin: 1px; margin-left: 3px").get "margin" == "1px 1px 1px 3px"
#guard (Block.parse "margin: 1px").get "margin-left" == "1px"
#guard (Block.parse "margin: 1px").get "MARGIN" == "1px"
#guard (Block.parseOnly ["margin-left", "margin"] "color: red; margin: 1px; margin-left: 2px; top: 0").get "margin-left" == "2px"
#guard (Block.parseOnly ["margin-left", "margin"] "color: red; top: 0").length == 0
#guard (Block.parse "margin-top: 1px").get "margin" == ""
#guard (Block.parse "border: 1px solid red").text == "border: 1px solid red;"
#guard (Block.parse "border: 1px solid red; border-top-color: blue").text ==
  "border-width: 1px; border-style: solid; border-color: blue red red;"
#guard ((Block.parse "color: red").set "color" "blue" "").text == "color: blue;"
#guard ((Block.parse "color: red").set "color" "1px" "").text == "color: red;"
#guard ((Block.parse "color: red").set "color" "" "").text == ""
#guard ((Block.parse "color: red").set "width" "1px" "IMPORTANT").text == "color: red; width: 1px !important;"
#guard ((Block.parse "color: red").set "width" "1px" "x").text == "color: red;"
#guard ((Block.parse "margin: 1px").removeProperty "margin").text == ""
#guard (Block.parse "margin: 1px").names == ["margin-top", "margin-right", "margin-bottom", "margin-left"]
#guard (Block.parse "font: normal lighter italic ultra-condensed xx-large/1.2 monospace").get "font" ==
  "italic lighter ultra-condensed xx-large / 1.2 monospace"
#guard (Block.parse "font: 16px serif").text == "font: 16px serif;"
#guard (Block.parse "font: 16px serif; font-kerning: none").get "font" == ""
#guard (Block.parse "font: 16px serif").get "font-weight" == "normal"
#guard styleOp "set\x00color: red\x00width\x001PX\x00" == "color: red; width: 1px;"
#guard styleOp "get\x00color: #F00\x00color" == "rgb(255, 0, 0)"
#guard styleOp "sup\x00display\x00grid" == "1"
#guard styleOp "sup\x00display\x00gridd" == "0"
#guard styleOp "rem\x00color: red; top: 0\x00color" == "top: 0px;\x00red"
#guard styleOp "rem\x00color: red\x00top" == "\x01\x00"
#guard styleOp "set\x00color: red\x00width\x00-1px\x00" == "\x01"
#guard styleOp "set\x00COLOR:RED\x00color\x00red\x00" == "\x01"

/-- Kind: structure. Says: after `put`, the block answers the declaration that was put for
its property. Does not say: where in the block it is (in place when the property was
there, else at the end). -/
theorem Block.find_put (b : Block) (d : Decl) : (b.put d).find d.name = some d := by
  unfold Block.put Block.find
  split
  · rename_i h
    induction b with
    | nil => simp at h
    | cons x xs ih =>
      simp only [List.map_cons, List.find?_cons]
      by_cases hx : x.name == d.name
      · simp [hx]
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        simp only [List.any_cons, hx, Bool.false_or] at h
        exact ih h
  · rename_i h
    simp only [Bool.not_eq_true, List.any_eq_false] at h
    rw [List.find?_append]
    have : List.find? (fun x => x.name == d.name) b = none := by
      rw [List.find?_eq_none]
      intro x hx
      simpa using h x hx
    simp [this]

/-- Kind: structure. Says: after `remove`, the block has no declaration of that property.
Does not say: anything about a shorthand whose longhands remain (`removeProperty` removes
those). -/
theorem Block.find_remove (b : Block) (name : String) : (b.remove name).find name = none := by
  unfold Block.remove Block.find
  rw [List.find?_eq_none]
  intro x hx
  have := (List.mem_filter.mp hx).2
  simpa using this

theorem find_map_put (b : Block) (d : Decl) (name : String) (h : name ≠ d.name) :
    List.find? (fun x => x.name == name) (b.map fun x => if x.name == d.name then d else x) =
      List.find? (fun x => x.name == name) b := by
  have h1 : (d.name == name) = false := by
    simp
    exact fun e => h e.symm
  induction b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hx : x.name == d.name
    · have hxe : x.name = d.name := by simpa using hx
      have h2 : (x.name == name) = false := by
        rw [hxe]
        exact h1
      simp only [hx, ↓reduceIte, h1, h2]
      exact ih
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      rw [ih]

/-- Kind: structure. Says: `put` does not change what the block answers for another
property. Does not say: that the order of the other declarations is kept (it is, but
the statement is about `find`). -/
theorem Block.find_put_other (b : Block) (d : Decl) (name : String) (h : name ≠ d.name) :
    (b.put d).find name = b.find name := by
  unfold Block.put Block.find
  split
  · exact find_map_put b d name h
  · rw [List.find?_append]
    have h1 : (d.name == name) = false := by
      simp
      exact fun e => h e.symm
    cases List.find? (fun x => x.name == name) b <;> simp [h1]

end L4Factoidal.Rendering.CssValues
