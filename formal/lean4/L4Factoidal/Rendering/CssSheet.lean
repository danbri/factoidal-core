/-
L4Factoidal.Rendering.CssSheet — the rules of a style sheet as CSSOM shows them (CSSOM §6.4):
the state behind `CSSStyleSheet.cssRules`, `insertRule`, `deleteRule`, and a rule's
`cssText`, `selectorText` and `style`.

As with `element.style` (`CssValues.Declaration`), there is one copy of the state: the text
of the sheet. `rulesOf` reads the rules of a text; `insertRule`, `deleteRule`, `setSelector`
and `setBody` give the text of the changed sheet, each rule in its canonical form. The page's
objects are glue over `sheetOp`.

A style rule whose selector `DOM.Selectors` does not read is not a rule here (it is dropped,
and `insertRule` refuses it with a SyntaxError): the sheet shows what the engine applies.
-/
import L4Factoidal.Rendering.CssValues.Declaration
import L4Factoidal.DOM.Selectors

namespace L4Factoidal.Rendering.CssSheet
open L4Factoidal.Rendering.CssValues

/-- A rule as written: the prelude (before `{` or `;`), and the text of its block. -/
structure RawRule where
  prelude : String
  body : Option String
  deriving Repr, DecidableEq, Inhabited

def trimCs (cs : List Char) : List Char :=
  ((cs.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- The rules of a sheet text, as written (CSS Syntax 3 §5.4.1 "consume a list of rules").
`depth` counts open `{`; `inBody` says the block has started. Tail recursive. -/
def splitRules : Nat → List Char → Nat → Option Char → Bool → List Char → List Char → List RawRule → List RawRule
  | 0, _, _, _, _, _, _, acc => acc.reverse
  | fuel + 1, cs, depth, quote, inBody, prelude, body, acc =>
    let finish := fun (acc : List RawRule) =>
      let p := trimCs prelude.reverse
      if p.isEmpty && !inBody then acc
      else { prelude := String.ofList p, body := if inBody then some (String.ofList body.reverse) else none } :: acc
    match cs with
    | [] => (finish acc).reverse
    | c :: rest =>
      let push := fun (c : Char) => if inBody then (prelude, c :: body) else (c :: prelude, body)
      match quote with
      | some q =>
        if c == '\\' then
          match rest with
          | d :: rest' =>
            let (p, b) := if inBody then (prelude, d :: c :: body) else (d :: c :: prelude, body)
            splitRules fuel rest' depth quote inBody p b acc
          | [] => splitRules fuel rest depth quote inBody prelude body acc
        else
          let (p, b) := push c
          splitRules fuel rest depth (if c == q then none else quote) inBody p b acc
      | none =>
        if c == '/' && rest.head? == some '*' then
          splitRules fuel (skipComment (rest.length + 1) (rest.drop 1)) depth quote inBody prelude body acc
        else if c == '"' || c == '\'' then
          let (p, b) := push c
          splitRules fuel rest depth (some c) inBody p b acc
        else if c == '{' then
          if inBody then splitRules fuel rest (depth + 1) quote inBody prelude (c :: body) acc
          else splitRules fuel rest 1 quote true prelude [] acc
        else if c == '}' then
          if inBody then
            if depth ≤ 1 then splitRules fuel rest 0 quote false [] [] (finish acc)
            else splitRules fuel rest (depth - 1) quote inBody prelude (c :: body) acc
          else splitRules fuel rest depth quote inBody prelude body acc
        else if c == ';' && !inBody then
          -- a statement at-rule ends here; a qualified rule with no block is dropped
          let p := trimCs prelude.reverse
          if p.head? == some '@' then splitRules fuel rest 0 quote false [] [] (finish acc)
          else splitRules fuel rest 0 quote false [] [] acc
        else
          let (p, b) := push c
          splitRules fuel rest depth quote inBody p b acc

def rawRules (text : String) : List RawRule :=
  let cs := preprocess text.toList
  -- CDO and CDC are ignored at the top level of a sheet
  let cs := (String.ofList cs).replace "<!--" "" |>.replace "-->" "" |>.toList
  splitRules (cs.length + 1) cs 0 none false [] [] []

/-! ### Selectors as text -/

/-- The text of an attribute selector's contents (CSSOM §6.7.2): `name`, `name="value"`,
`name="value" i`. -/
def attrText (body : List CV) : String :=
  let parts := stripWs body
  let isOp := fun (cv : CV) => match cv with
    | .tok (.delim c) => c == '=' || c == '~' || c == '|' || c == '^' || c == '$' || c == '*'
    | _ => false
  -- the name: idents, `*` and `|` up to the operator
  let isBar := fun (cv : CV) => match cv with
    | .tok (.delim '|') => true
    | _ => false
  let isEq := fun (cv : CV) => match cv with
    | .tok (.delim '=') => true
    | _ => false
  let isStar := fun (cv : CV) => match cv with
    | .tok (.delim '*') => true
    | _ => false
  let name := parts.takeWhile fun cv => !(isOp cv) || isBar cv || isStar cv
  -- `|=` is an operator, `ns|name` is a name: the name stops at a `|` followed by `=`
  let name := match name.reverse with
    | last :: before =>
      if (isBar last || isStar last) && ((parts.drop name.length).head?.map isEq).getD false then before.reverse else name
    | [] => name
  let rest := parts.drop name.length
  let nameText := String.join (name.map fun cv => match cv with
    | .tok (.ident s) => serializeIdent s
    | .tok t => t.css
    | _ => "")
  let op := rest.takeWhile isOp
  let after := rest.drop op.length
  let opText := String.join (op.map fun cv => match cv with
    | .tok t => t.css
    | _ => "")
  match after with
  | [] => nameText
  | v :: flags =>
    let value := match v with
      | .tok (.str s) => serializeString s
      | .tok (.ident s) => serializeString s
      | cv => serialize [cv]
    let flag := match flags with
      | [.tok (.ident f)] => " " ++ lower f
      | _ => ""
    nameText ++ opText ++ value ++ flag

def selectorFunctions : List String := ["is", "not", "where", "has", "matches", "-webkit-any", "host", "host-context", "slotted"]

/-- The canonical text of a selector (CSSOM §6.7.2 "serialize a group of selectors"), from
its tokens: one space for the descendant combinator, ` > `, ` + `, ` ~ `, `, `. The loop
over the tokens is a tail call; the arguments of `:is()` and its like are one level down
(at most `maxNesting` levels). -/
def selectorTokensText : Nat → List CV → String
  | 0, _ => ""
  | fuel + 1, cvs =>
    let piece := fun (cv : CV) => match cv with
      | .tok (.ident s) => serializeIdent s
      | .tok (.hash s _) => "#" ++ serializeIdent s
      | .tok t => t.css
      | .block '[' body => "[" ++ attrText body ++ "]"
      | .block o body => String.singleton o ++ rawText body ++ String.singleton (closerChar o)
      | .fn name args =>
        let n := lower name
        if selectorFunctions.contains n then n ++ "(" ++ selectorTokensText fuel args ++ ")"
        else n ++ "(" ++ rawText args ++ ")"
      | .raw s => s
    -- state: the text so far, a pending descendant space, values to skip white space before
    let step := fun (acc : String × Bool × Bool) (cv : CV) =>
      let (out, pendingSpace, afterCombinator) := acc
      match cv with
      | .tok .ws => (out, !out.isEmpty && !afterCombinator, afterCombinator)
      | .tok .comma => (out ++ ", ", false, true)
      | .tok (.delim c) =>
        if c == '>' || c == '+' || c == '~' then (out ++ " " ++ String.singleton c ++ " ", false, true)
        else (out ++ (if pendingSpace then " " else "") ++ String.singleton c, false, false)
      | cv => (out ++ (if pendingSpace then " " else "") ++ piece cv, false, false)
    ((trimWs cvs).foldl step ("", false, false)).1

/-- The canonical text of a selector text, when `DOM.Selectors` reads it; `none` is a
SyntaxError. -/
def selectorText (s : String) : Option String :=
  if (L4Factoidal.DOM.Selectors.parse s).isSome then
    let cvs := CV.parse s
    some (selectorTokensText (cvSize 64 cvs + 2) cvs)
  else none

/-! ### Rules -/

/-- A rule of a sheet as CSSOM shows it. `kind` is the name of the interface without the
`CSS` and `Rule` (`Style`, `Media`, `Import` ...); `type` is `CSSRule.type`; `prelude` is
the canonical selector, condition or name; `body` the text of the block as written. -/
structure Rule where
  kind : String
  type : Nat
  prelude : String
  body : String
  cssText : String
  deriving Repr, DecidableEq, Inhabited

/-- The canonical text of an at-rule prelude: its tokens with one space between them,
keywords in lower case outside strings and functions. -/
def preludeText (s : String) : String :=
  let cvs := trimWs (CV.parse s)
  let rec go : Nat → List CV → String
    | 0, _ => ""
    | fuel + 1, cvs =>
      " ".intercalate ((stripWs cvs).map fun cv => match cv with
        | .tok (.ident s) => serializeIdent s
        | .tok t => t.css
        | .block '(' body =>
          -- a media or supports feature: `(name: value)`
          let inner := stripWs body
          match inner with
          | .tok (.ident name) :: .tok .colon :: value => "(" ++ lower name ++ ": " ++ go fuel value ++ ")"
          | _ => "(" ++ go fuel body ++ ")"
        | .block o body => String.singleton o ++ go fuel body ++ String.singleton (closerChar o)
        | .fn name args => lower name ++ "(" ++ rawText args ++ ")"
        | .raw s => s)
  (go (cvSize 64 cvs + 2) cvs).replace " ," ","

def indent (s : String) : String := "  " ++ s.replace "\n" "\n  "

/-- The at-rules with a block of rules, and `CSSRule.type` of each (0 where CSSOM gives no
number). -/
def groupRules : List (String × String × Nat) :=
  [("media", "Media", 4), ("supports", "Supports", 12), ("container", "Container", 0),
   ("layer", "LayerBlock", 0), ("scope", "Scope", 0), ("starting-style", "StartingStyle", 0),
   ("document", "Document", 13)]

/-- The at-rules with a block of declarations. -/
def declRules : List (String × String × Nat) :=
  [("font-face", "FontFace", 5), ("page", "Page", 6), ("property", "Property", 0),
   ("counter-style", "CounterStyle", 11), ("position-try", "PositionTry", 0),
   ("font-palette-values", "FontPaletteValues", 0), ("view-transition", "ViewTransition", 0)]

/-- A rule as written as a CSSOM rule; `none` when it is not a rule this engine has. The
recursion is on the nesting of group rules (`depth` levels are read); the rules of one
block are a `filterMap`. -/
def ruleOf : Nat → RawRule → Option Rule
  | 0, _ => none
  | fuel + 1, raw =>
    let cs := raw.prelude.toList
    match cs with
    | '@' :: rest =>
      let name := lower (String.ofList (rest.takeWhile isNameChar))
      let after := preludeText (String.ofList (rest.dropWhile isNameChar))
      let head := "@" ++ name ++ (if after == "" then "" else " " ++ after)
      match raw.body with
      | none =>
        if name == "import" then some ⟨"Import", 3, after, "", head ++ ";"⟩
        else if name == "namespace" then some ⟨"Namespace", 10, after, "", head ++ ";"⟩
        else if name == "layer" && after != "" then some ⟨"LayerStatement", 0, after, "", head ++ ";"⟩
        else none
      | some body =>
        match groupRules.find? (·.1 == name) with
        | some (_, kind, type) =>
          let inner := ((rawRules body).filterMap (ruleOf fuel)).map (·.cssText)
          let text := if inner.isEmpty then head ++ " {\n}" else head ++ " {\n" ++ "\n".intercalate (inner.map indent) ++ "\n}"
          some ⟨kind, type, after, body, text⟩
        | none =>
          match declRules.find? (·.1 == name) with
          | some (_, kind, type) =>
            -- descriptors are kept as written (they are not properties of the table)
            let decls := (splitTop ';' (body.length + 1) body.toList 0 none [] []).filterMap fun piece =>
              (declOf piece).map fun (n, v, _) => lower n ++ ": " ++ trimText v ++ ";"
            let text := if decls.isEmpty then head ++ " { }" else head ++ " { " ++ " ".intercalate decls ++ " }"
            some ⟨kind, type, after, body, text⟩
          | none =>
            if name == "keyframes" || name == "-webkit-keyframes" then
              let frames := (rawRules body).map fun r => preludeText r.prelude ++ " { " ++ (Block.parse (r.body.getD "")).text ++ " }"
              let text := "@keyframes " ++ after ++ " { " ++ (if frames.isEmpty then "" else "\n  " ++ "\n  ".intercalate frames ++ "\n") ++ "}"
              some ⟨"Keyframes", 7, after, body, text⟩
            else if name == "font-feature-values" then some ⟨"FontFeatureValues", 14, after, body, head ++ " { " ++ trimText body ++ " }"⟩
            else none
    | _ =>
      match raw.body, selectorText raw.prelude with
      | some body, some sel =>
        let block := (Block.parse body).text
        some ⟨"Style", 1, sel, body, sel ++ " { " ++ block ++ (if block == "" then "" else " ") ++ "}"⟩
      | _, _ => none

/-- The most nesting of group rules that is read. -/
def nesting : Nat := 64

/-- The rules of a sheet text. -/
def rulesOf (text : String) : List Rule := (rawRules text).filterMap (ruleOf nesting)

/-- The text of a sheet with these rules. -/
def textOf (rules : List Rule) : String := "\n".intercalate (rules.map (·.cssText))

/-- The one rule a rule text is (CSSOM §6.4.2 "parse a CSS rule"); `none`: a SyntaxError. -/
def parseRule (text : String) : Option Rule :=
  match rawRules text with
  | [raw] => ruleOf nesting raw
  | _ => none

/-- An error of a sheet operation, as the name of the DOMException. -/
inductive SheetError where
  | syntax | indexSize | hierarchyRequest | invalidState
  deriving Repr, DecidableEq

def SheetError.name : SheetError → String
  | .syntax => "SyntaxError"
  | .indexSize => "IndexSizeError"
  | .hierarchyRequest => "HierarchyRequestError"
  | .invalidState => "InvalidStateError"

/-- `insertRule(rule, index)` (CSSOM §6.4.2 "insert a CSS rule"): the rules with the new
rule at `index`. An `@import` goes before every other rule, `@namespace` before style
rules. -/
def insertRule (rules : List Rule) (text : String) (index : Nat) : Except SheetError (List Rule) :=
  if index > rules.length then .error .indexSize
  else
    match parseRule text with
    | none => .error .syntax
    | some rule =>
      let before := rules.take index
      let after := rules.drop index
      let isImport := fun (r : Rule) => r.kind == "Import"
      let isHead := fun (r : Rule) => r.kind == "Import" || r.kind == "LayerStatement" || r.kind == "Namespace"
      if isImport rule && before.any (fun r => !(isImport r || r.kind == "LayerStatement")) then .error .hierarchyRequest
      else if !isHead rule && after.any isImport then .error .hierarchyRequest
      else if rule.kind == "Namespace" && rules.any (fun r => !isHead r) then .error .invalidState
      else .ok (before ++ rule :: after)

/-- `deleteRule(index)` (CSSOM §6.4.2 "remove a CSS rule"). -/
def deleteRule (rules : List Rule) (index : Nat) : Except SheetError (List Rule) :=
  if index ≥ rules.length then .error .indexSize
  else .ok (rules.take index ++ rules.drop (index + 1))

/-- A style rule with a new selector; the rule as it was when the selector is not valid. -/
def setSelector (rule : Rule) (selector : String) : Rule :=
  if rule.kind != "Style" then rule
  else
    match selectorText selector with
    | none => rule
    | some sel =>
      let block := (Block.parse rule.body).text
      { rule with prelude := sel, cssText := sel ++ " { " ++ block ++ (if block == "" then "" else " ") ++ "}" }

/-- A style rule with a new declaration block (the text of `rule.style`). -/
def setBody (rule : Rule) (body : String) : Rule :=
  if rule.kind != "Style" then rule
  else
    let block := (Block.parse body).text
    { rule with body := block, cssText := rule.prelude ++ " { " ++ block ++ (if block == "" then "" else " ") ++ "}" }

def replaceAt (rules : List Rule) (index : Nat) (f : Rule → Rule) : List Rule :=
  (List.range rules.length).zip rules |>.map fun (i, r) => if i == index then f r else r

def ruleFields (r : Rule) : String :=
  "\x02".intercalate [r.kind, toString r.type, r.prelude, r.body, r.cssText]

/-- The operations of a page's style sheet objects, as text: the fields of `q` are
separated by U+0000, the first is the verb. A changed sheet is answered as U+0000 and its
text; an error as U+0001 and the name of the DOMException.

- `rules` text → the rules, separated by U+0001; each is kind, type, prelude, body and
  cssText separated by U+0002
- `insert` text rule index, `delete` text index
- `setsel` text index selector, `setbody` text index block
- `selector` text → "1" and the canonical selector, or "0"
- `canon` text → the sheet text in canonical form -/
def sheetOp (q : String) : String :=
  let answer := fun (r : Except SheetError (List Rule)) => match r with
    | .ok rules => "\x00" ++ textOf rules
    | .error e => "\x01" ++ e.name
  match q.splitOn "\x00" with
  | ["rules", text] => "\x01".intercalate ((rulesOf text).map ruleFields)
  | ["insert", text, rule, index] => answer (insertRule (rulesOf text) rule (index.toNat?.getD 0))
  | ["delete", text, index] =>
    match index.toNat? with
    | some i => answer (deleteRule (rulesOf text) i)
    | none => "\x01IndexSizeError"
  | ["setsel", text, index, selector] => answer (.ok (replaceAt (rulesOf text) (index.toNat?.getD 0) (setSelector · selector)))
  | ["setbody", text, index, body] => answer (.ok (replaceAt (rulesOf text) (index.toNat?.getD 0) (setBody · body)))
  | ["selector", text] =>
    match selectorText text with
    | some s => "1" ++ s
    | none => "0"
  | ["canon", text] => textOf (rulesOf text)
  | _ => ""

/-! ### Tests and theorems -/

#guard (rulesOf "a { color: RED } b{}").map (·.cssText) == ["a { color: red; }", "b { }"]
#guard (rulesOf "a { color: red; } /* x */ @media screen { b { top: 0 } }").map (·.kind) == ["Style", "Media"]
#guard (rulesOf "@media (MIN-WIDTH:100px) and screen { b { top: 0 } }").map (·.cssText) ==
  ["@media (min-width: 100px) and screen {\n  b { top: 0px; }\n}"]
#guard (rulesOf "@import url(a.css); a{}").map (·.kind) == ["Import", "Style"]
#guard (rulesOf "a:nonsense { } b { }").map (·.prelude) == ["b"]
#guard (rulesOf "a{b:c;} garbage; d{}").length == 2
#guard (rulesOf ".x { font: 16px simple; }").map (·.cssText) == [".x { font: 16px simple; }"]
#guard (rulesOf ".x { font: 16px 0simple; }").map (·.cssText) == [".x { }"]
#guard selectorText "a>b  ~ c ,d   e" == some "a > b ~ c, d e"
#guard selectorText "  DIV#Id.cls[ foo = bar ]:hover " == some "DIV#Id.cls[foo=\"bar\"]:hover"
#guard selectorText "a[b='c' I]" == some "a[b=\"c\" i]"
#guard selectorText "a:not( .b , c )" == some "a:not(.b, c)"
#guard selectorText "a >" == none
#guard selectorText "" == none
#guard (insertRule (rulesOf "a{}") "b{}" 0).toOption.map textOf == some "b { }\na { }"
#guard (insertRule (rulesOf "a{}") "b{}" 2).toOption == none
#guard (insertRule (rulesOf "a{}") "b{" 1).toOption.map textOf == some "a { }\nb { }"
#guard (insertRule (rulesOf "a{}") "b{} c{}" 1).toOption == none
#guard (insertRule (rulesOf "a{}") ":bogus{}" 1).toOption == none
#guard (insertRule (rulesOf "a{}") "@import url(x.css);" 1).toOption == none
#guard (deleteRule (rulesOf "a{} b{}") 0).toOption.map textOf == some "b { }"
#guard (deleteRule (rulesOf "a{}") 1).toOption == none
#guard sheetOp "insert\x00a{}\x00b{color:red}\x001" == "\x00a { }\nb { color: red; }"
#guard sheetOp "insert\x00a{}\x00}\x001" == "\x01SyntaxError"
#guard sheetOp "delete\x00a{}\x005" == "\x01IndexSizeError"
#guard sheetOp "selector\x00a  >  b" == "1a > b"

/-- Kind: bounds. Says: `insertRule` at a valid index with an accepted rule gives one more
rule. Does not say: where the rule is (it is at `index`, by the definition). -/
theorem insertRule_length (rules : List Rule) (text : String) (index : Nat) (out : List Rule)
    (h : insertRule rules text index = .ok out) : out.length = rules.length + 1 := by
  unfold insertRule at h
  split at h
  · cases h
  · rename_i hi
    split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h
            have : index ≤ rules.length := Nat.le_of_not_lt hi
            simp [List.length_append, List.length_take, List.length_drop]
            omega

/-- Kind: policy. Says: `insertRule` refuses an index past the end of the list with an
IndexSizeError, whatever the rule text. Does not say: that the rule text is examined. -/
theorem insertRule_index (rules : List Rule) (text : String) (index : Nat) (h : index > rules.length) :
    insertRule rules text index = .error .indexSize := by
  unfold insertRule
  simp [h]

/-- Kind: bounds. Says: `deleteRule` at a valid index gives one rule fewer. Does not say:
which rules remain (those before and after `index`, by the definition). -/
theorem deleteRule_length (rules : List Rule) (index : Nat) (out : List Rule)
    (h : deleteRule rules index = .ok out) : out.length + 1 = rules.length := by
  unfold deleteRule at h
  split at h
  · cases h
  · rename_i hi
    cases h
    simp [List.length_append, List.length_take, List.length_drop]
    omega

end L4Factoidal.Rendering.CssSheet
