/-
L4Factoidal.Rendering.SheetReader — the rules of a style sheet text, as the cascade needs
them: every style rule with what surrounds it resolved.

CSS Syntax 3 §5.4 (rules, blocks and declarations), CSS Conditional 3 (`@media`,
`@supports`), CSS Cascade 5 §6.4 (`@layer`) and CSS Nesting 1. One pass over the text, with
the open rules on a list (no recursion on the nesting of the sheet):

- a style rule gives a `Leaf` with its selector list and its declarations;
- the rules inside `@media` carry the query lists of every `@media` around them (`media`):
  the reader does not know the viewport, so a caller filters (`CSS.parseInRaw`);
- the rules inside `@supports` are read when the condition holds (the `supports` argument),
  and skipped when it does not;
- the rules inside `@layer` carry their layer (`layer`, the path of names) and its place in
  the layer order of the sheet (`rank`: 0 unlayered, 1 the first layer declared);
- a rule nested in a style rule has its selector made absolute (`nest`): `&` is the parent
  selector, a selector with no `&` is a descendant of it; declarations after a nested rule
  are a rule of their own after it, as CSS Nesting says (the nested declarations rule);
- `@container`, `@scope`, `@starting-style` and `@document` blocks are skipped: this engine
  evaluates none of them, and their contents must not apply unconditionally;
- every other at-rule (`@font-face`, `@keyframes`, `@import`, `@property` ...) is a `Leaf`
  with its name in `kind` and its block as written in `body`, for the reader of that rule.

Declarations are split as CSS Syntax says: a `;` or `:` inside a string, `url()`, or a
`()`, `[]` or `{}` block does not end a declaration (`url(data:image/png;base64,...)`).

Cost: one pass to drop comments, one over the text; each character is pushed once on a
buffer. Nothing here knows properties or values.
-/
import L4Factoidal.Rendering.SupportsCondition

namespace L4Factoidal.Rendering.SheetReader

private def trim (s : String) : String := s.trimAscii.toString

/-- A declaration as written: the name (lower case unless a custom property), the value
without `!important`. -/
structure Decl where
  name : String
  value : String
  important : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A style rule (`kind` empty) or another at-rule of a sheet, with the `@media` query
lists and the cascade layer it is in. -/
structure Leaf where
  /-- Empty for a style rule; else the at-rule's name in lower case, without the `@`. -/
  kind : String := ""
  /-- The selector list of a style rule, nesting resolved; the prelude of an at-rule. -/
  prelude : String := ""
  decls : List Decl := []
  /-- The block of an at-rule as written; empty for a statement (`@import ...;`). -/
  body : String := ""
  /-- The query lists of the `@media` rules around it, innermost first: all must hold. -/
  media : List String := []
  /-- The cascade layer: the path of names; empty when unlayered. -/
  layer : List String := []
  /-- The place of the layer in the layer order (`rankOf`): 0 unlayered, 1 the lowest. -/
  rank : Nat := 0
  deriving Repr, BEq, Inhabited

/-! ### Comments -/

/-- The text without its comments (CSS Syntax 3 §4.3.2). A `/*` in a string does not start
one; a comment that never closes runs to the end. One pass. -/
def stripComments (source : String) : String :=
  if (source.splitOn "/*").length == 1 then source else Id.run do
  let mut out := ""
  let mut quote : Option Char := none
  let mut esc := false
  let mut slash := false
  let mut comment := false
  let mut star := false
  for c in source.toList do
    if comment then
      if star && c == '/' then
        comment := false
        star := false
      else star := c == '*'
    else if slash && c == '*' then
      slash := false
      comment := true
    else
      if slash then
        slash := false
        out := out.push '/'
      match quote with
      | some q =>
        out := out.push c
        if esc then esc := false
        else if c == '\\' then esc := true
        else if c == q || c == '\n' then quote := none
      | none =>
        if esc then
          esc := false
          out := out.push c
        else if c == '/' then slash := true
        else
          out := out.push c
          if c == '"' || c == '\'' then quote := some c
          else if c == '\\' then esc := true
  if slash then out := out.push '/'
  return out

#guard stripComments "a/* x */b" == "ab"
#guard stripComments "a{content:\"/* no */\"}/* yes */" == "a{content:\"/* no */\"}"
#guard stripComments "a/b" == "a/b"
#guard stripComments "a /* never closes" == "a "
#guard stripComments "a/**/b/***/c//*x*/d" == "abc/d"
#guard stripComments "url(a/b)/" == "url(a/b)/"

/-! ### Lists and declarations -/

/-- `source` split at the commas outside strings, parentheses and brackets (CSS Syntax 3
§5.3.11). One pass. -/
def splitCommas (source : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut quote : Option Char := none
  let mut esc := false
  for c in source.toList do
    if esc then
      esc := false
      item := item.push c
    else if c == '\\' then
      esc := true
      item := item.push c
    else if let some q := quote then
      item := item.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      item := item.push c
    else if c == '(' || c == '[' then
      depth := depth + 1
      item := item.push c
    else if c == ')' || c == ']' then
      depth := depth - 1
      item := item.push c
    else if c == ',' && depth == 0 then
      out := out.push item
      item := ""
    else item := item.push c
  return (out.push item).toList

/-- `source` split at the white space outside strings, parentheses and brackets: the
component values of a value such as `0 calc(1px + 2px) var(--a, 1px 2px)`. One pass. -/
def splitWords (source : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut quote : Option Char := none
  let mut esc := false
  for c in source.toList do
    if esc then
      esc := false
      item := item.push c
    else if c == '\\' then
      esc := true
      item := item.push c
    else if let some q := quote then
      item := item.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      item := item.push c
    else if c == '(' || c == '[' then
      depth := depth + 1
      item := item.push c
    else if c == ')' || c == ']' then
      depth := depth - 1
      item := item.push c
    else if (c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c') && depth == 0 then
      if !item.isEmpty then out := out.push item
      item := ""
    else item := item.push c
  return (if item.isEmpty then out else out.push item).toList

#guard splitCommas "a, b" == ["a", " b"]
#guard splitCommas ":is(a, b) c, [x=\"1,2\"]" == [":is(a, b) c", " [x=\"1,2\"]"]
#guard splitCommas "" == [""]
#guard splitWords "0  calc(1px + 2px)\n var(--a, 1px 2px)" == ["0", "calc(1px + 2px)", "var(--a, 1px 2px)"]
#guard splitWords "  " == []

/-- A character of a property name as written. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '\\' || c.toNat ≥ 0x80

/-- One declaration from its text (`name: value`, with an optional `!important`): none when
there is no colon or the name is not a property name (CSS Syntax 3 §5.4.6). The name is in
lower case, except a custom property's, which is case-sensitive (CSS Variables 1 §2). -/
def declOf (text : String) : Option Decl :=
  match text.splitOn ":" with
  | name :: first :: more =>
    let name := trim name
    if name.isEmpty || !name.toList.all isNameChar then none
    else
      let name := if name.startsWith "--" then name else name.toLower
      let value := trim (":".intercalate (first :: more))
      if value.contains '!' && value.toLower.endsWith "important" then
        let before := trim (value.dropEnd 9).toString
        if before.endsWith "!" then some { name, value := trim (before.dropEnd 1).toString, important := true }
        else some { name, value }
      else some { name, value }
  | _ => none

#guard declOf "color: red" == some { name := "color", value := "red" }
#guard declOf " COLOR : Red !IMPORTANT " == some { name := "color", value := "Red", important := true }
#guard declOf "--Main: a:b ! important" == some { name := "--Main", value := "a:b", important := true }
#guard declOf "background: url(data:image/png;base64,AA==)" == some { name := "background", value := "url(data:image/png;base64,AA==)" }
#guard declOf "color red" == none
#guard declOf "a b: c" == none
#guard declOf ": c" == none
#guard declOf "x: very-important" == some { name := "x", value := "very-important" }

/-- The declarations of a declaration list (a `style` attribute, CSS Syntax 3 §5.3.8): split
at the `;` outside strings and blocks; an item that is not a declaration is dropped. -/
def splitDecls (text : String) : List Decl := Id.run do
  let mut out : Array Decl := #[]
  let mut buf := ""
  let mut closers : List Char := []
  let mut quote : Option Char := none
  let mut esc := false
  for c in (stripComments text).toList do
    match quote with
    | some q =>
      buf := buf.push c
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == q || c == '\n' then quote := none
    | none =>
      if esc then
        esc := false
        buf := buf.push c
      else if c == '\\' then
        esc := true
        buf := buf.push c
      else if c == '"' || c == '\'' then
        quote := some c
        buf := buf.push c
      else if c == ';' && closers.isEmpty then
        if let some d := declOf buf then out := out.push d
        buf := ""
      else
        buf := buf.push c
        if c == '(' then closers := ')' :: closers
        else if c == '[' then closers := ']' :: closers
        else if c == '{' then closers := '}' :: closers
        else if closers.head? == some c then closers := closers.drop 1
  if let some d := declOf buf then out := out.push d
  return out.toList

#guard (splitDecls "color: red; margin: 0 auto").map (·.name) == ["color", "margin"]
#guard (splitDecls "background: url(data:image/png;base64,AA==); color: blue").map (·.value) == ["url(data:image/png;base64,AA==)", "blue"]
#guard (splitDecls "content: \"a;b\"; x: (1;2); y: 3").map (·.value) == ["\"a;b\"", "(1;2)", "3"]
#guard (splitDecls "color: red /* ; x: y */; top: 0").map (·.name) == ["color", "top"]
#guard splitDecls "" == []
#guard splitDecls ";;" == []

/-! ### Nesting -/

/-- `s` with each `&` outside a string replaced by `by_`. -/
def replaceAmp (s by_ : String) : String := Id.run do
  let mut out := ""
  let mut quote : Option Char := none
  let mut esc := false
  for c in s.toList do
    if esc then
      esc := false
      out := out.push c
    else if c == '\\' then
      esc := true
      out := out.push c
    else if let some q := quote then
      out := out.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      out := out.push c
    else if c == '&' then out := out ++ by_
    else out := out.push c
  return out

/-- `s` has a nesting selector `&`. -/
def hasAmp (s : String) : Bool := s.contains '&' && replaceAmp s "" != s

/-- One selector of a nested rule, made absolute (CSS Nesting 1 §2.1, §3). `single`: the
parent selector list is one selector. `&` stands for `:is(parent)`; a selector with no `&`
is relative to the parent (a descendant, or what its leading combinator says). When the
parent is one selector and `&` is only at the start, the parent is written out in its
place, which matches the same elements with the same specificity as `:is(parent)` there. -/
def nestOne (parent : String) (single : Bool) (s : String) : String :=
  let t := trim s
  if hasAmp t then
    if single && t.startsWith "&" && !hasAmp (t.drop 1).toString then parent ++ (t.drop 1).toString
    else replaceAmp t (":is(" ++ parent ++ ")")
  else (if single then parent else ":is(" ++ parent ++ ")") ++ " " ++ t

/-- The selector list of a rule nested in a style rule with selector list `parent`; at the
top level (`parent` empty) the list as written. -/
def nest (parent prelude : String) : String :=
  if parent.isEmpty then prelude
  else
    let single := (splitCommas parent).length == 1
    ", ".intercalate ((splitCommas prelude).map (nestOne parent single))

/-- At the top level a selector list is what was written. -/
theorem nest_top (prelude : String) : nest "" prelude = prelude := by
  simp [nest]

#guard nest ".a" "&:hover" == ".a:hover"
#guard nest ".a" ".b" == ".a .b"
#guard nest ".a" "> .b, + .c" == ".a > .b, .a + .c"
#guard nest ".a .b" "&.c" == ".a .b.c"
#guard nest ".a" ".b &" == ".b :is(.a)"
#guard nest ".a, .b" "& .c" == ":is(.a, .b) .c"
#guard nest ".a, .b" ".c" == ":is(.a, .b) .c"
#guard nest ".a" "& + &" == ":is(.a) + :is(.a)"
#guard nest ".a" "[title=\"&\"]" == ".a [title=\"&\"]"

/-! ### Cascade layers -/

/-- `layers` with the layer `path` and each layer it is nested in, each once, in the order
they are first named (CSS Cascade 5 §6.4.1). At most 4096 layers are kept. -/
def register (layers : Array (List String)) (path : List String) : Array (List String) :=
  (List.range path.length).foldl (fun ls i =>
    let q := path.take (i + 1)
    if ls.contains q || ls.size ≥ 4096 then ls else ls.push q) layers

/-- Where a layer stands among the layers: for each layer it is nested in and for itself,
the index of first naming, then a last entry above every index. Layers are ordered by
these lists, lexicographically: sibling layers by first naming, and a layer's nested layers
below the layer's own rules (CSS Cascade 5 §6.4.3). -/
def layerKey (layers : Array (List String)) (path : List String) : List Nat :=
  (List.range path.length).map (fun i => (layers.findIdx? (· == path.take (i + 1))).getD layers.size) ++ [layers.size]

/-- `a` is before `b` in the lexicographic order of lists of numbers. -/
def keyLT : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then keyLT as bs else a < b

/-- The place of layer `path` in the layer order: 0 for no layer (unlayered rules), else 1
more than the number of layers that are before it. A later place wins among normal
declarations and loses among important ones (`CSS.layerPosition`). -/
def rankOf (layers : Array (List String)) (path : List String) : Nat :=
  if path.isEmpty then 0
  else
    let key := layerKey layers path
    1 + (layers.filter fun q => keyLT (layerKey layers q) key).size

theorem rankOf_unlayered (layers : Array (List String)) : rankOf layers [] = 0 := by
  simp [rankOf]

theorem rankOf_pos (layers : Array (List String)) (path : List String) (h : path ≠ []) :
    0 < rankOf layers path := by
  unfold rankOf
  cases path with
  | nil => exact absurd rfl h
  | cons a as => simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]; omega

theorem keyLT_irrefl (a : List Nat) : keyLT a a = false := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [keyLT, ih]

theorem keyLT_asymm (a b : List Nat) : keyLT a b = true → keyLT b a = false := by
  induction a generalizing b with
  | nil => cases b <;> simp [keyLT]
  | cons x xs ih =>
    cases b with
    | nil => simp [keyLT]
    | cons y ys =>
      simp only [keyLT]
      by_cases hxy : x = y
      · subst hxy
        simpa using ih ys
      · have hyx : ¬ y = x := fun h => hxy h.symm
        simp only [beq_iff_eq, hxy, hyx, if_false, decide_eq_true_eq, decide_eq_false_iff_not]
        omega

#guard register #[] ["a", "b"] == #[["a"], ["a", "b"]]
#guard register #[["a"]] ["b"] == #[["a"], ["b"]]
-- `@layer a, b; @layer a.x`: a.x < a < b
#guard (let ls := register (register (register #[] ["a"]) ["b"]) ["a", "x"]
  [rankOf ls ["a", "x"], rankOf ls ["a"], rankOf ls ["b"], rankOf ls []]) == [1, 2, 3, 0]

/-! ### The reader -/

/-- An open rule: the selector list its declarations are for (empty outside a style rule),
the `@media` conditions and the layer, and the declarations read since the last rule
given out (last first). -/
structure Frame where
  selector : String := ""
  media : List String := []
  layer : List String := []
  decls : List Decl := []
  deriving Inhabited

/-- `out` with the declarations of an open rule as a style rule, when it has any. -/
def flushed (out : Array Leaf) (f : Frame) : Array Leaf :=
  if f.selector.isEmpty || f.decls.isEmpty then out
  else out.push { prelude := f.selector, decls := f.decls.reverse, media := f.media, layer := f.layer }

/-- The name of an at-rule prelude (`@name rest`), in lower case, and the rest. -/
def atName (p : String) : String × String :=
  let cs := (p.drop 1).toString
  let name := (cs.takeWhile fun c => c.isAlphanum || c == '-' || c == '_').toString
  (name.toLower, trim (cs.drop name.length).toString)

/-- Block at-rules whose contents are not read: conditions this engine does not evaluate
(their rules must not apply unconditionally), and `@supports` and `@layer` blocks that
reach this list because their condition is false or their prelude is not one name. -/
def skippedBlocks : List String :=
  ["container", "scope", "starting-style", "document", "-moz-document", "supports", "layer"]

/-- A selector prelude without the `<!--` and `-->` that CSS Syntax 3 §5.4.1 ignores at the
top level of a sheet. -/
def plainPrelude (p : String) : String :=
  let p := if p.startsWith "<!--" then trim (p.drop 4).toString else p
  if p.startsWith "-->" then trim (p.drop 3).toString else p

/-- The name of the `n`th anonymous layer of a sheet: not a name a sheet can write. -/
def anonName (n : Nat) : String := "\x01" ++ toString n

/-- The layer path of an `@layer` name (`a.b`), under the layer `parent`. -/
def layerPath (parent : List String) (name : String) : List String :=
  parent ++ ((trim name).splitOn ".").map trim

/-- The text before a `{` is the start of a custom property declaration (`--name: ...`),
whose value may hold a block (CSS Variables 1 §2). No selector starts so. -/
def customValueStart (buf : String) : Bool :=
  let p := trim buf
  p.startsWith "--" && p.contains ':'

/-- The pieces of a sheet text: the text up to each `{`, `}` or `;` that is outside a
string and outside a `()`, `[]` or value block (CSS Syntax 3 §5.4.8), with that character;
the last piece ends with the character 0. `quote` is the open quote (0: none), `esc` a
pending backslash, `closers` the closing characters of the open blocks, innermost first.
A tail call per character: this is the loop over the text, and it keeps no other state. -/
def scan : List Char → String → Char → Bool → List Char → Array (String × Char) → Array (String × Char)
  | [], buf, _, _, _, out => out.push (buf, '\x00')
  | c :: rest, buf, quote, esc, closers, out =>
    if quote != '\x00' then
      if esc then scan rest (buf.push c) quote false closers out
      else if c == '\\' then scan rest (buf.push c) quote true closers out
      else if c == quote || c == '\n' then scan rest (buf.push c) '\x00' false closers out
      else scan rest (buf.push c) quote false closers out
    else if esc then scan rest (buf.push c) quote false closers out
    else if c == '\\' then scan rest (buf.push c) quote true closers out
    else if c == '"' || c == '\'' then scan rest (buf.push c) c false closers out
    else match closers with
      | k :: more =>
        if c == k then scan rest (buf.push c) quote false more out
        else if c == '(' then scan rest (buf.push c) quote false (')' :: closers) out
        else if c == '[' then scan rest (buf.push c) quote false (']' :: closers) out
        else if c == '{' then scan rest (buf.push c) quote false ('}' :: closers) out
        else scan rest (buf.push c) quote false closers out
      | [] =>
        if c == '(' then scan rest (buf.push c) quote false [')'] out
        else if c == '[' then scan rest (buf.push c) quote false [']'] out
        else if c == '{' then
          if customValueStart buf then scan rest (buf.push c) quote false ['}'] out
          else scan rest "" quote false [] (out.push (buf, c))
        else if c == '}' || c == ';' then scan rest "" quote false [] (out.push (buf, c))
        else scan rest (buf.push c) quote false closers out

/-- The pieces of a sheet text without its comments. -/
def pieces (source : String) : Array (String × Char) :=
  scan (stripComments source).toList "" '\x00' false [] #[]

/-- Every character of a text is in one piece: the pieces, each with its ending
character, are as long as the text and one more (the 0 that ends the last piece). -/
theorem scan_length (cs : List Char) (buf : String) (quote : Char) (esc : Bool) (closers : List Char)
    (out : Array (String × Char)) :
    ((scan cs buf quote esc closers out).toList.map fun p => p.1.length + 1).sum =
      (out.toList.map fun p => p.1.length + 1).sum + buf.length + cs.length + 1 := by
  induction cs generalizing buf quote esc closers out with
  | nil => simp [scan]; omega
  | cons c rest ih =>
    unfold scan
    split
    · split
      · rw [ih]; simp [String.length_push]; omega
      · split
        · rw [ih]; simp [String.length_push]; omega
        · split <;> (rw [ih]; simp [String.length_push]; omega)
    · split
      · rw [ih]; simp [String.length_push]; omega
      · split
        · rw [ih]; simp [String.length_push]; omega
        · split
          · rw [ih]; simp [String.length_push]; omega
          · split
            · split
              · rw [ih]; simp [String.length_push]; omega
              · split
                · rw [ih]; simp [String.length_push]; omega
                · split
                  · rw [ih]; simp [String.length_push]; omega
                  · split <;> (rw [ih]; simp [String.length_push]; omega)
            · split
              · rw [ih]; simp [String.length_push]; omega
              · split
                · rw [ih]; simp [String.length_push]; omega
                · split
                  · split
                    · rw [ih]; simp [String.length_push]; omega
                    · rw [ih]; simp; omega
                  · split
                    · rw [ih]; simp; omega
                    · rw [ih]; simp [String.length_push]; omega

/-- The rules of a sheet text, in order (see the head of this file). `supports` evaluates
the condition of an `@supports` rule. A sheet that stops early closes its open blocks.
The loop is over the pieces of the text (`pieces`): one step for each rule, declaration
and block end. -/
def read (supports : String → Bool) (source : String) : Array Leaf := Id.run do
  let mut out : Array Leaf := #[]
  let mut stack : List Frame := []
  let mut top : Frame := {}
  let mut layers : Array (List String) := #[]
  let mut anon := 0
  -- the text of a prelude that a `;` did not end (outside a style rule)
  let mut carry := ""
  -- the depth inside the block of an at-rule that is kept as written, or skipped
  let mut raw := 0
  let mut rawBody := ""
  let mut rawLeaf : Option Leaf := none
  -- no rule but `@charset`, `@import` and `@layer` statements so far: `@import` is valid
  let mut head := true
  for (text, term) in pieces source do
    if raw > 0 then
      if term == '}' && raw == 1 then
        if let some leaf := rawLeaf then out := out.push { leaf with body := rawBody ++ text }
        raw := 0
        rawBody := ""
        rawLeaf := none
      else if term == '\x00' then rawBody := rawBody ++ text
      else
        rawBody := (rawBody ++ text).push term
        if term == '{' then raw := raw + 1
        else if term == '}' then raw := raw - 1
    else if term == '{' then
      let p := trim (carry ++ text)
      carry := ""
      head := false
      if p.startsWith "@" then
        let (name, rest) := atName p
        if name == "media" then
          out := flushed out top
          stack := { top with decls := [] } :: stack
          top := { top with decls := [], media := rest :: top.media }
        else if name == "supports" && supports rest then
          out := flushed out top
          stack := { top with decls := [] } :: stack
          top := { top with decls := [] }
        else if name == "layer" && (splitCommas rest).length == 1 then
          let path := if rest.isEmpty then top.layer ++ [anonName anon] else layerPath top.layer rest
          if rest.isEmpty then anon := anon + 1
          layers := register layers path
          out := flushed out top
          stack := { top with decls := [] } :: stack
          top := { top with decls := [], layer := path }
        else
          raw := 1
          rawLeaf := if skippedBlocks.contains name then none
            else some { kind := name, prelude := rest, media := top.media, layer := top.layer }
      else if p.isEmpty then
        raw := 1
        rawLeaf := none
      else
        out := flushed out top
        stack := { top with decls := [] } :: stack
        top := { selector := nest top.selector (plainPrelude p), media := top.media, layer := top.layer }
    else if term == '}' then
      if !top.selector.isEmpty then
        if let some d := declOf text then top := { top with decls := d :: top.decls }
      carry := ""
      match stack with
      | f :: rest =>
        out := flushed out top
        top := f
        stack := rest
      | [] => pure ()
    else if term == ';' then
      let p := trim (carry ++ text)
      if p.startsWith "@" then
        let (name, rest) := atName p
        if name == "layer" then
          for n in splitCommas rest do
            layers := register layers (layerPath top.layer n)
        else if name == "import" then
          -- valid only before every other rule (CSS Cascade 5 §6.1)
          if head then out := out.push { kind := name, prelude := rest }
        else
          if name != "charset" then head := false
          out := out.push { kind := name, prelude := rest, media := top.media, layer := top.layer }
        carry := ""
      else if !top.selector.isEmpty then
        if let some d := declOf text then top := { top with decls := d :: top.decls }
      else
        -- outside a style rule a `;` does not end a selector: it is part of one that
        -- is then not a selector, and its rule is dropped
        carry := (carry ++ text).push ';'
    else if !top.selector.isEmpty then
      -- the end of the text
      if let some d := declOf text then top := { top with decls := d :: top.decls }
  if raw > 0 then
    if let some leaf := rawLeaf then out := out.push { leaf with body := rawBody }
  out := flushed out top
  for f in stack do out := flushed out f
  return out.map fun leaf => if leaf.layer.isEmpty then leaf else { leaf with rank := rankOf layers leaf.layer }

/-! ### `@import` -/

/-- An `@import` rule (CSS Cascade 5 §6.1): the URL as written, the layer it imports into
(`some ""` an anonymous one), the `supports()` condition and the media query list. -/
structure Import where
  url : String
  layer : Option String := none
  supports : Option String := none
  media : String := ""
  deriving Repr, BEq, Inhabited

/-- The text of a quoted string or of `url(...)` at the start of `s`, and what follows. -/
def urlAndRest (s : String) : Option (String × String) :=
  let unquote := fun (t : String) =>
    let t := trim t
    if t.length ≥ 2 && (t.startsWith "\"" || t.startsWith "'") then ((t.drop 1).dropEnd 1).toString else t
  if s.startsWith "\"" || s.startsWith "'" then
    let q := s.front
    match ((s.drop 1).toString.splitOn q.toString) with
    | inner :: rest => some (inner, q.toString.intercalate rest)
    | [] => none
  else if (s.take 4).toString.toLower == "url(" then
    match ((s.drop 4).toString.splitOn ")") with
    | inner :: rest => some (unquote inner, ")".intercalate rest)
    | [] => none
  else none

/-- `name(...)` at the start of `s`: its contents and what follows. -/
def fnAndRest (name s : String) : Option (String × String) :=
  if (s.take (name.length + 1)).toString.toLower == name ++ "(" then
    (CssSupports.inParens (s.drop (name.length + 1)).toString.toList).map fun (inner, rest) =>
      (String.ofList inner, String.ofList rest)
  else none

/-- An `@import` prelude read: `<url> [layer | layer(<name>)]? [supports(<condition>)]?
<media-query-list>?`; none when it does not start with a URL. -/
def importOf (prelude : String) : Option Import :=
  match urlAndRest (trim prelude) with
  | none => none
  | some (url, rest) =>
    let rest := trim rest
    let (layer, rest) := match fnAndRest "layer" rest with
      | some (name, r) => (some (trim name), trim r)
      | none =>
        if rest.toLower == "layer" || (rest.take 6).toString.toLower == "layer " then (some "", trim (rest.drop 5).toString)
        else (none, rest)
    let (supports, rest) := match fnAndRest "supports" rest with
      | some (cond, r) => (some (trim cond), trim r)
      | none => (none, rest)
    some { url, layer, supports, media := rest }

/-- The `@import` rules of a sheet, in order: those before every rule other than
`@charset` and `@layer` statements (CSS Cascade 5 §6.1: a later one is invalid, and `read`
leaves it out). A host
fetches each URL and reads the sheet in its place, in the layer and under the conditions
given; nothing here fetches. -/
def imports (source : String) : List Import :=
  (read (fun _ => false) source).toList.filterMap
    fun leaf => if leaf.kind == "import" then importOf leaf.prelude else none

#guard imports "@charset \"utf-8\"; @import url(a.css); @import 'b.css' screen and (min-width: 1px); p{} @import 'late.css';" ==
  [{ url := "a.css" }, { url := "b.css", media := "screen and (min-width: 1px)" }]
#guard imports "@import url(\"c.css\") layer(base) supports(display: grid) print;" ==
  [{ url := "c.css", layer := some "base", supports := some "display: grid", media := "print" }]
#guard imports "@import \"d.css\" layer;" == [{ url := "d.css", layer := some "" }]
#guard imports "@layer a, b; @import url(e.css);" == [{ url := "e.css" }]
#guard imports "p { color: red }" == []

/-! ### Examples -/

private def show_ (source : String) : List (String × String × List String × Nat) :=
  ((read CssSupports.ruleHolds source).toList.filter (·.kind.isEmpty)).map fun leaf =>
    (leaf.prelude, "; ".intercalate (leaf.decls.map fun d => d.name ++ ": " ++ d.value ++ (if d.important then " !" else "")), leaf.media, leaf.rank)

#guard show_ "a { color: red; margin: 0 } b{top:1px}" == [("a", "color: red; margin: 0", [], 0), ("b", "top: 1px", [], 0)]
-- strings, URLs and blocks do not end a declaration
#guard show_ ".u { background: url(data:image/png;base64,AA==); content: \"};\"; color: blue }" ==
  [(".u", "background: url(data:image/png;base64,AA==); content: \"};\"; color: blue", [], 0)]
-- @media in @media: both conditions; rules after the inner block keep the outer one
#guard show_ "@media (min-width: 600px) { @media (max-width: 900px) { .m { color: green } } .n { color: pink } } .o{top:0}" ==
  [(".m", "color: green", ["(max-width: 900px)", "(min-width: 600px)"], 0), (".n", "color: pink", ["(min-width: 600px)"], 0), (".o", "top: 0", [], 0)]
-- @supports: read when the condition holds
#guard show_ "@supports (display: grid) { .g { display: grid } } @supports (display: nonsense) { .h { top: 0 } } .i{top:0}" ==
  [(".g", "display: grid", [], 0), (".i", "top: 0", [], 0)]
#guard show_ "@supports not (display: nonsense) { @media print { .g { top: 0 } } }" == [(".g", "top: 0", ["print"], 0)]
-- nesting
#guard show_ ".p { color: red; &:hover { color: blue } .q { color: teal } top: 0 }" ==
  [(".p", "color: red", [], 0), (".p:hover", "color: blue", [], 0), (".p .q", "color: teal", [], 0), (".p", "top: 0", [], 0)]
#guard show_ ".a, .b { > .c { top: 0; .d & { left: 0 } } }" ==
  [(":is(.a, .b) > .c", "top: 0", [], 0), (".d :is(:is(.a, .b) > .c)", "left: 0", [], 0)]
#guard show_ ".a { @media print { color: red; .b { top: 0 } } }" ==
  [(".a", "color: red", ["print"], 0), (".a .b", "top: 0", ["print"], 0)]
-- layers: order of first naming; unlayered rules are rank 0
#guard show_ "@layer base, theme; @layer theme { a { top: 0 } } @layer base { a { top: 1px } } a { top: 2px } @layer { a { top: 3px } }" ==
  [("a", "top: 0", [], 2), ("a", "top: 1px", [], 1), ("a", "top: 2px", [], 0), ("a", "top: 3px", [], 3)]
#guard show_ "@layer a { @layer b { p { top: 0 } } p { top: 1px } } @layer a.b { q { top: 0 } }" ==
  [("p", "top: 0", [], 1), ("p", "top: 1px", [], 2), ("q", "top: 0", [], 1)]
-- skipped blocks, kept at-rules, a sheet that stops early
#guard show_ "@container (min-width: 1px) { a { top: 0 } } @scope (.x) { b { top: 0 } } c { top: 0 }" == [("c", "top: 0", [], 0)]
#guard show_ "@font-face { font-family: A; src: url(a.ttf) } @keyframes k { from { top: 0 } to { top: 1px } } a { top: 0 }" == [("a", "top: 0", [], 0)]
#guard ((read CssSupports.ruleHolds "@media print { @font-face { font-family: A } } @keyframes k { from { top: 0 } }").toList.map
  fun leaf => (leaf.kind, leaf.prelude, leaf.body, leaf.media)) ==
  [("font-face", "", " font-family: A ", ["print"]), ("keyframes", "k", " from { top: 0 } ", [])]
#guard show_ "a { color: red" == [("a", "color: red", [], 0)]
#guard show_ "a { color: red; b { top: 0" == [("a", "color: red", [], 0), ("a b", "top: 0", [], 0)]
#guard show_ "<!-- a { top: 0 } --> b { top: 0 }" == [("a", "top: 0", [], 0), ("b", "top: 0", [], 0)]
-- escapes in selectors (utility class names), a custom property holding a block
#guard show_ ".md\\:flex { display: flex } .w-1\\/2 { width: 50% }" == [(".md\\:flex", "display: flex", [], 0), (".w-1\\/2", "width: 50%", [], 0)]
#guard show_ "a { --x: { b: c }; color: red }" == [("a", "--x: { b: c }; color: red", [], 0)]
-- a rule with no selector is dropped with its block; a stray `}` is passed
#guard show_ "{ color: red } } a { top: 0 }" == [("a", "top: 0", [], 0)]
-- the declarations of a rule agree with those of a declaration list
#guard ((read CssSupports.ruleHolds "x { color: red; background: url(a;b) ; --v: (1;2); top: 0 !important }").toList.map (·.decls)) ==
  [splitDecls "color: red; background: url(a;b) ; --v: (1;2); top: 0 !important"]

end L4Factoidal.Rendering.SheetReader
