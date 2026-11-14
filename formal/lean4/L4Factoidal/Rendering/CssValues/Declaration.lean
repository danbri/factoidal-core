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

/-- The properties that `all` sets (CSS Cascade 4 §3.2): every one but `direction`,
`unicode-bidi` and the custom properties. -/
def allSets (name : String) : Bool :=
  name != "all" && name != "direction" && name != "unicode-bidi" && !isCustom name

/-- Set a declaration where the property already is, else at the end (CSSOM §6.6.1 "set a
CSS declaration"). A declaration of `all` stands for every property it sets: those
declarations are taken out and it goes at the end. -/
def Block.put (b : Block) (d : Decl) : Block :=
  if d.name == "all" then (b.filter fun x => x.name != "all" && !allSets x.name) ++ [d]
  else if b.any (·.name == d.name) then b.map fun x => if x.name == d.name then d else x
  else b ++ [d]

/-- Set a declaration at the end, removing an earlier one of the property (parsing). -/
def Block.putLast (b : Block) (d : Decl) : Block :=
  if d.name == "all" then (b.filter fun x => x.name != "all" && !allSets x.name) ++ [d]
  else b.remove d.name ++ [d]

/-! ### Descriptors -/

/-- The text of a value with its comments taken out. A loop over the characters (a tail
call). -/
def dropComments (cs : List Char) (inComment : Bool) (acc : Array Char) : List Char :=
  match cs with
  | [] => acc.toList
  | '/' :: '*' :: rest => dropComments rest true acc
  | '*' :: '/' :: rest => if inComment then dropComments rest false acc else dropComments rest false ((acc.push '*').push '/')
  | c :: rest => if inComment then dropComments rest true acc else dropComments rest false (acc.push c)

/-- The number of hex digits `ds`. -/
def hexNat (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * 16 + ((hexVal c).getD 0)) 0

/-- Upper-case hex digits of `n`, at least one. -/
def hexUpper (n : Nat) : String := (String.ofList (Nat.toDigits 16 n)).toUpper

/-- One `<urange>` (CSS Syntax 3 §7.1), from its text with comments taken out, in canonical
form (`U+A0-AF`): `u+`, then one to six hex digits and question marks (the digits first),
or one to six hex digits, `-` and one to six hex digits; the range is in order and ends at
or below U+10FFFF. Whitespace inside is not a range. -/
def urangeOf (t : String) : Option String :=
  match t.toList with
  | u :: '+' :: rest =>
    if u != 'u' && u != 'U' then none else
    let isHex := fun (c : Char) => (hexVal c).isSome
    let hex := rest.takeWhile isHex
    let after := rest.drop hex.length
    let qs := after.takeWhile (· == '?')
    let after := after.drop qs.length
    let n := hex.length + qs.length
    if n == 0 || n > 6 then none else
    let range : Option (Nat × Nat) :=
      if !qs.isEmpty then
        if after.isEmpty then some (hexNat (hex ++ qs.map fun _ => '0'), hexNat (hex ++ qs.map fun _ => 'f')) else none
      else match after with
        | [] => some (hexNat hex, hexNat hex)
        | '-' :: last =>
          if !last.isEmpty && last.length ≤ 6 && last.all isHex then some (hexNat hex, hexNat last) else none
        | _ => none
    match range with
    | some (a, b) =>
      if a > b || b > 0x10FFFF then none
      else some ("U+" ++ hexUpper a ++ (if a == b then "" else "-" ++ hexUpper b))
    | none => none
  | _ => none

/-- The `@font-face` descriptors (CSS Fonts 4 §4): `unicode-range` a list of ranges in
canonical form, `font-display` one of its keywords; the others are kept as written. -/
def fontFaceDescriptors : List String :=
  ["font-family", "src", "font-style", "font-weight", "font-stretch", "font-width", "unicode-range",
   "font-feature-settings", "font-variation-settings", "font-named-instance", "font-display",
   "font-language-override", "ascent-override", "descent-override", "line-gap-override", "size-adjust"]

/-- The font technologies of `tech()` this engine accepts (CSS Fonts 4 §4.3.1); the others
(`incremental`, `color-SVG`, `features-graphite`) drop their component. -/
def fontTechs : List String :=
  ["features-opentype", "features-aat", "color-colrv0", "color-colrv1", "color-sbix", "color-cbdt", "variations", "palettes"]

/-- The `@font-face` `src` descriptor (CSS Fonts 4 §4.3): its components that parse, each
`url()` with an optional `format()` and an optional `tech()` of known keywords after it,
or `local()`; a component that does not parse is left out, and with none left the value is
none. Technology keywords are written in lower case. -/
def fontSrcValue (v : String) : Option String :=
  let formats := ["collection", "embedded-opentype", "opentype", "svg", "truetype", "woff", "woff2"]
  let one := fun (piece : List CV) => match stripWs piece with
    | [.fn f args] =>
      if lower f == "local" then (if (stripWs args).isEmpty then none else some (serialize [.fn "local" (stripWs args)]))
      else if lower f == "url" then some (serialize [.fn f args])
      else none
    | url :: rest =>
      let isUrl := match url with
        | .tok (.url _) => true
        | .fn f _ => lower f == "url"
        | _ => false
      if !isUrl then none else
      let fmt : Option (Option String) := match rest with
        | .fn f args :: _ =>
          if lower f != "format" then some none
          else match stripWs args with
            | [.tok (.ident k)] => if formats.contains (lower k) then some (some (lower k)) else none
            | [.tok (.str t)] => some (some (serialize [.tok (.str t)]))
            | _ => none
        | _ => some none
      match fmt with
      | none => none
      | some f =>
        let rest := if f.isSome then rest.drop 1 else rest
        let tech : Option (Option String) := match rest with
          | [] => some none
          | [.fn t args] =>
            if lower t != "tech" then none
            else
              let items := (splitCommas args).map stripWs
              let ks := items.filterMap fun it => match it with
                | [.tok (.ident k)] => if fontTechs.contains (lower k) then some (lower k) else none
                | _ => none
              if items.isEmpty || ks.length != items.length then none else some (some (", ".intercalate ks))
          | _ => none
        match tech with
        | none => none
        | some t => some (serialize [url] ++ (match f with
            | some k => " format(" ++ k ++ ")"
            | none => "") ++ (match t with
            | some k => " tech(" ++ k ++ ")"
            | none => ""))
    | [] => none
  let parts := (splitCommas (CV.parse v)).filterMap one
  if parts.isEmpty then none else some (", ".intercalate parts)

#guard fontSrcValue "url(\"foo.ttf\") tech(color-COLRv0)" == some "url(\"foo.ttf\") tech(color-colrv0)"
#guard (["url(\"foo.ttf\") tech()", "url(\"foo.ttf\") tech(\"variations\")", "url(\"foo.ttf\") tech(features-opentype color-COLRv0)",
  "url(\"foo.ttf\") tech(xyzzy, features-opentype)", "url(\"foo.ttf\") tech(features-opentype) format(opentype)",
  "url(\"foo.ttf\") dummy(\"opentype\") tech(variations)", "url(\"foo.ttf\") format(opentype) tech(features-opentype) dummy(something)"].map fontSrcValue).all (·.isNone)
#guard (fontSrcValue "url(\"foo.ttf\") tech(incremental), url(\"bar.html\")").isSome &&
  (fontSrcValue "url(\"foo.ttf\") format(dummy), url(\"foo.ttf\") tech(variations)").isSome &&
  (fontSrcValue "url(\"foo.ttf\") format(opentype) tech(features-opentype)").isSome && (fontSrcValue "url(x.woff)").isSome

/-- The value of descriptor `name` of an at-rule (`ctx`, such as `font-face`), when the
value is one: `none` for a name that is no descriptor of the rule or a value that does not
parse. -/
def descriptorValue (ctx name value : String) : Option String :=
  let n := lower name
  let v := trimText value
  if ctx != "font-face" || !fontFaceDescriptors.contains n || v == "" then none
  else if n == "unicode-range" then
    let pieces := ((String.ofList (dropComments v.toList false #[])).splitOn ",").map trimText
    (pieces.mapM urangeOf).map (", ".intercalate ·)
  else if n == "src" then fontSrcValue v
  else if n == "font-display" then
    let k := lower v
    if ["auto", "block", "swap", "fallback", "optional"].contains k then some k else none
  else some v

/-- The declarations a declaration `name: value` stands for: in a style block (`ctx` empty)
the property's longhands (`expand`); in an at-rule's block the descriptor. -/
def expandIn (ctx name value : String) : Option (List (String × String)) :=
  if ctx == "" then expand name value
  else (descriptorValue ctx name value).map fun v => [(lower name, v)]

/-- The block before the declarations `ds` that a declaration of `name` stands for are put:
a shorthand kept whole for its `var()` and its longhands replace each other (a later
`background: green` takes out an earlier `background: var(--x)`, and the other way). -/
def Block.clearFor (b : Block) (name : String) (ds : List (String × String)) : Block :=
  let p := propertyName name
  match ds with
  | [(n, _)] =>
    if n == p then
      match lookup p with
      | some row => if row.longhands.isEmpty then b else b.filter fun x => !row.longhands.contains x.name
      | none => b
    else b.remove p
  | _ => b.remove p

/-- A style block reads properties only: no descriptor is taken in one. -/
theorem descriptorValue_style (name value : String) : descriptorValue "" name value = none := by
  simp [descriptorValue]

/-- In a style block a declaration stands for what `expand` gives. -/
theorem expandIn_style (name value : String) : expandIn "" name value = expand name value := by
  simp [expandIn]

/-- The block a text denotes (CSSOM §6.6.1 "parse a CSS declaration block"): invalid
declarations are dropped, shorthands expanded, the last declaration of a property wins.
`ctx`: the at-rule whose descriptors the block has (empty for a style block). -/
def Block.parse (text : String) (ctx : String := "") : Block :=
  let cs := preprocess text.toList
  let pieces := splitTop ';' (cs.length + 1) cs 0 none [] []
  pieces.foldl (fun b piece =>
    match declOf piece with
    | none => b
    | some (name, value, important) =>
      match expandIn ctx name value with
      | none => b
      | some ds => ds.foldl (fun b (n, v) => b.putLast { name := n, value := v, important := important }) (b.clearFor name ds)) []

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
  -- a longhand not declared is the `all` declaration's value when there is one
  let viaAll := fun (l : String) => (b.find "all").bind fun d => if allSets l then some { d with name := l } else none
  let ds := row.longhands.filterMap fun l => (b.find l).orElse fun _ => viaAll l
  match ds with
  | [] => none
  | d :: rest =>
    if ds.length == row.longhands.length && rest.all (·.important == d.important) then some ds else none

/-- A shorthand's value from its longhands' declarations: a CSS-wide keyword that all of
them have is the shorthand's value; else `recombine`. -/
def recombineDecls (row : Property) (ds : List Decl) : String :=
  match ds with
  | d :: rest =>
    if cssWide.contains d.value && rest.all (·.value == d.value) then d.value
    else recombine row fun l => ((ds.find? (·.name == l)).map (·.value)).getD ""
  | [] => ""

/-- The value of shorthand `p` from its longhands, when they can be written as one. -/
def Block.getShorthand (b : Block) (p : String) : String :=
    match lookup p with
    | none => ""
    | some row =>
      if row.longhands.isEmpty then ""
      else
        match b.longhandsOf row with
        | none => ""
        | some ds => recombineDecls row ds

/-- `getPropertyValue` (CSSOM §6.6.1): the value of a longhand, or of a shorthand when all
its longhands are set and can be written as one value; "" otherwise. -/
def Block.get (b : Block) (property : String) : String :=
  let p := propertyName property
  match b.find p with
  | some d =>
    -- `all` is its value only while no property it sets is declared after it
    if p == "all" && b.any (fun x => allSets x.name) then "" else d.value
  | none =>
    match (if allSets p then b.find "all" else none) with
    | some d => if (lookup p).any (·.longhands.isEmpty) then d.value else b.getShorthand p
    | none => b.getShorthand p

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
def Block.set (b : Block) (property value priority : String) (ctx : String := "") : Block :=
  if trimText value == "" then b.removeProperty property
  else if !(priority == "" || lower priority == "important") then b
  else
    match expandIn ctx property value with
    | none => b
    | some ds =>
      ds.foldl (fun b (n, v) => b.put { name := n, value := v, important := lower priority == "important" }) (b.clearFor property ds)

/-- The property names of the block in order (`item`, `length`). -/
def Block.names (b : Block) : List String := b.map (·.name)

/-- For each longhand, the shorthands with a generic shape that have it among their
longhands: most longhands first; legacy aliases left out. Built once (a lazy constant). -/
def shorthandIndex : Thunk (Std.HashMap String (List Property)) := Thunk.mk fun _ =>
  let rows := Data.properties.toList.filterMap fun (n, _, _, _, ls) =>
    if ls == "" || (aliasMap.get.contains n) then none
    else
      match lookup n with
      | some row => if recombinable row then some row else none
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
          let v := recombineDecls row ds
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
- `val` property value → "1" and the canonical value, or "0"

A verb written `ctx:verb` (`font-face:set`) works on a block of the descriptors of at-rule
`ctx` (`descriptorValue`). -/
def styleOp (q : String) : String :=
  -- a verb `ctx:verb` is on the block of an at-rule's descriptors (`font-face:set`)
  let (ctx, fields) := match q.splitOn "\x00" with
    | verb :: rest =>
      match verb.splitOn ":" with
      | [c, v] => (c, v :: rest)
      | _ => ("", verb :: rest)
    | [] => ("", [])
  match fields with
  | ["get", block, property] => (Block.parse block ctx).get property
  | ["pri", block, property] => (Block.parse block ctx).priority property
  | ["set", block, property, value, priority] =>
    let b := Block.parse block ctx
    let b' := b.set property value priority ctx
    if b' == b then "\x01" else b'.text
  | ["rem", block, property] =>
    let b := Block.parse block ctx
    let b' := b.removeProperty property
    (if b' == b then "\x01" else b'.text) ++ "\x00" ++ b.get property
  | ["txt", text] => (Block.parse text ctx).text
  | ["names", block] => "\x00".intercalate (Block.parse block ctx).names
  | ["sup", property, value] => if supports property value then "1" else "0"
  | ["val", property, value] =>
    match specified property value with
    | some v => "1" ++ v
    | none => "0"
  | _ => ""

/-! ### Tests and theorems -/

#guard (Block.parse "color: RED; margin: 1px 2px").text == "color: red; margin: 1px 2px;"
-- a CSS-wide keyword on a shorthand; a shorthand's var() form and its longhands replace each other
#guard styleOp "get\x00background-position: inherit\x00background-position" == "inherit"
#guard styleOp "txt\x00background: var(--prop); background: green" == "background: green;"
#guard styleOp "txt\x00margin: 1px; margin: var(--m)" == "margin: var(--m);"
-- all (cssstyledeclaration-all-shorthand.html)
#guard (Block.parse "all: revert").get "all" == "revert" && (Block.parse "all: revert; width: 50px").get "all" == ""
#guard (Block.parse "width: 50px; all: revert").get "width" == "revert" && (Block.parse "width: 50px; all: revert").get "all" == "revert"
#guard (Block.parse "all: revert; width: 50px; all: unset").get "width" == "unset"
#guard (Block.parse "width: 50px; all: revert; width: 100px").get "width" == "100px"
#guard (Block.parse "direction: rtl; all: unset").get "direction" == "rtl"
#guard ((Block.parse "").set "all" "revert" "").get "color" == "revert"
-- unicode-range (urange-parsing.html)
#guard ["u/**/+/**/a/**/?", "u+abc", "U+AbC", "u+a", "u+a????", "u/**/+0a/**/?", "u+00000a", "u+1e9a", "u/**/+0/**/?",
  "u+000000", "u+0?????", "u+1e3", "u+1e-20", "u/**/+0/**/-0a", "u+000000-0aaaaa", "u+0-1"].map
  (descriptorValue "font-face" "unicode-range") ==
  ["U+A0-AF", "U+ABC", "U+ABC", "U+A", "U+A0000-AFFFF", "U+A0-AF", "U+A", "U+1E9A", "U+0-F", "U+0", "U+0-FFFFF", "U+1E3",
   "U+1E-20", "U+0-A", "U+0-AAAAA", "U+0-1"].map some
#guard (["u+efg", "u+ abc", "u +abc", "u+aaaaaaa", "u+aaaaaa?", "u+a?a", "u+aaaaaa", "u+a?????", "u/**/0", "u+0000000",
  "u+0?a", "u+0+0a", "u+0?-0a", "u+0-0a?", "u+222222-22222a", "u-0-1", "u+"].map
  (descriptorValue "font-face" "unicode-range")).all (·.isNone)
#guard descriptorValue "font-face" "unicode-range" "u+0-7f, U+A?" == some "U+0-7F, U+A0-AF"
#guard styleOp "font-face:get\x00unicode-range: u+a?\x00unicode-range" == "U+A0-AF"
#guard styleOp "font-face:set\x00font-family: x\x00unicode-range\x00u+0-1\x00" == "font-family: x; unicode-range: U+0-1;"
#guard styleOp "font-face:set\x00font-family: x\x00unicode-range\x00u+efg\x00" == "\x01"
#guard styleOp "set\x00\x00unicode-range\x00u+0-1\x00" == "\x01"
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
#guard (Block.parse "grid-area: auto / i / auto / i").get "grid-area" == "auto / i"
#guard (Block.parse "grid-area: --a").get "grid-area" == "--a"
#guard (Block.parse "grid-row: auto / auto").get "grid-row" == "auto"
#guard (Block.parse "text-box: none auto").get "text-box" == "normal"
#guard (Block.parse "flex: none").get "flex" == "0 0 auto"
-- keywords of a shorthand that are not its parts: `white-space` (CSS Text 4 §3.1)
#guard (Block.parse "white-space: pre").get "white-space" == "pre"
#guard (Block.parse "white-space: pre-line").get "white-space-collapse" == "preserve-breaks"
#guard (Block.parse "white-space: preserve nowrap").get "white-space" == "pre"
#guard (Block.parse "white-space: nowrap").get "white-space" == "nowrap"
-- an alternative that does not name its parts keeps the shorthand whole
#guard (Block.parse "block-step: up").get "block-step" == "none"
#guard (Block.parse "block-step: 10px down").get "block-step" == "10px down"
#guard (Block.parse "grid: [a] \"a\" 10px").get "grid" == "[a] \"a\" 10px"
#guard (Block.parse "grid-template: \"a\" \"b\"").get "grid-template" == "\"a\" \"b\""
#guard (Block.parse "grid: auto-flow / 10px").get "grid" == "auto-flow / 10px"
#guard (Block.parse "rule: repeat(auto, 5px solid green)").get "rule" == "repeat(auto, 5px solid green)"
#guard (Block.parse "rule: thick, dashed, hotpink").get "row-rule-color" == "currentcolor, currentcolor, hotpink"
#guard (Block.parse "column-rule: repeat(4, blue, 5px red)").get "column-rule" == "repeat(4, blue, 5px red)"
#guard (Block.parse "row-rule: currentcolor none medium, repeat(auto, 5px solid red)").get "row-rule" ==
  "medium, repeat(auto, 5px solid red)"
#guard (Block.parse "corner: round").get "corner" == "0px"
#guard (Block.parse "corner: round 3px").get "corner" == "3px"
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
there, else at the end; `all` at the end). -/
theorem Block.find_put (b : Block) (d : Decl) (hd : d.name ≠ "all") : (b.put d).find d.name = some d := by
  unfold Block.put Block.find
  rw [if_neg (by simpa using hd)]
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

/-- Kind: structure. Says: after `put` of an `all` declaration, the block answers it for
`all` (an earlier `all` is gone). -/
theorem Block.find_put_all (b : Block) (d : Decl) (hd : d.name = "all") : (b.put d).find "all" = some d := by
  unfold Block.put Block.find
  rw [if_pos (by simp [hd]), List.find?_append]
  have : List.find? (fun x => x.name == "all") (b.filter fun x => x.name != "all" && !allSets x.name) = none := by
    rw [List.find?_eq_none]
    intro x hx
    have := (List.mem_filter.mp hx).2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
    simpa using this.1
  simp [this, hd]

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

/-- Kind: structure. Says: `put` of a declaration other than `all` does not change what the
block answers for another property. Does not say: that the order of the other declarations
is kept (it is, but the statement is about `find`). -/
theorem Block.find_put_other (b : Block) (d : Decl) (name : String) (h : name ≠ d.name)
    (hd : d.name ≠ "all") :
    (b.put d).find name = b.find name := by
  unfold Block.put Block.find
  rw [if_neg (by simpa using hd)]
  split
  · exact find_map_put b d name h
  · rw [List.find?_append]
    have h1 : (d.name == name) = false := by
      simp
      exact fun e => h e.symm
    cases List.find? (fun x => x.name == name) b <;> simp [h1]

end L4Factoidal.Rendering.CssValues
