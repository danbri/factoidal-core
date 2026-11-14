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
import L4Factoidal.Rendering.MediaQuery
import L4Factoidal.Rendering.CssRegister

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

def nthFunctions : List String := ["nth-child", "nth-last-child", "nth-of-type", "nth-last-of-type"]

/-- The canonical text of An+B (CSSOM §6.7.2, "serialize an <an+b> value"): `2n+1` for
`odd`, `n` and `-n` for a of 1 and -1, no `+0`, the integer alone when a is 0. -/
def anbText (a b : Int) : String :=
  let aPart := if a == 1 then "n" else if a == -1 then "-n" else toString a ++ "n"
  if a == 0 then toString b
  else if b == 0 then aPart
  else if b > 0 then aPart ++ "+" ++ toString b
  else aPart ++ toString b

#guard anbText 2 1 == "2n+1" && anbText 2 0 == "2n" && anbText 0 (-1) == "-1" && anbText 1 0 == "n" &&
  anbText (-1) (-5) == "-n-5" && anbText 5 (-5) == "5n-5"

/-- The text of the argument of an `:nth-*()` from its tokens: a number token after the
first one is written with its sign (the tokens of `2n+1` are `2n` and `+1`; a number with
no sign could not follow there, CSS Syntax §6). -/
def anbSource (cvs : List CV) : String :=
  -- the state: the text so far, and whether a number here was written with its sign
  let (out, _) := (trimWs cvs).foldl (fun (acc : String × Bool) cv =>
    let (s, signed) := acc
    match cv with
    | .tok (.num v _) => (s ++ (if signed && v ≥ 0 then "+" else "") ++ serialize [cv], false)
    | .tok .ws => (s ++ " ", signed)
    | .tok (.delim _) => (s ++ serialize [cv], false)
    | cv => (s ++ serialize [cv], true)) ("", false)
  out

def selectorFunctions : List String := ["is", "not", "where", "has", "matches", "-webkit-any", "host", "host-context", "slotted"]

/-- The name of an `@keyframes` rule (CSS Animations 1 §3): one `<custom-ident>` (not `none`,
`default` or a CSS-wide keyword) or a string that is not empty. -/
def keyframesName (prelude : String) : Bool :=
  match stripWs (CV.parse prelude) with
  | [.tok (.ident n)] => !["none", "default", "initial", "inherit", "unset", "revert", "revert-layer"].contains (lower n)
  | [.tok (.str t)] => t != ""
  | _ => false

#guard ["foo", "--foo", "\"a b\"", "None2"].all keyframesName
#guard !(["none", "DEFAULT", "inherit", "revert-layer", "12", "-12", "12foo", "foo.bar", "one two", "one, two", "\"\""].any keyframesName)

/-- The tokens of a selector without a universal selector that is the whole compound before
a pseudo-element (`*::before` is written `::before`, CSSOM §6.7.2: a lone universal selector
with no namespace is left out when the compound has more). `boundary`: the previous token
ends a compound. A loop over the tokens (a tail call). -/
def dropStar (acc : Array CV) (boundary : Bool) : List CV → Array CV
  | [] => acc
  | .tok (.delim '*') :: .tok .colon :: .tok .colon :: rest =>
    if boundary then dropStar ((acc.push (.tok .colon)).push (.tok .colon)) false rest
    else dropStar (((acc.push (.tok (.delim '*'))).push (.tok .colon)).push (.tok .colon)) false rest
  | cv :: rest =>
    let ends := match cv with
      | .tok .ws | .tok .comma => true
      | .tok (.delim c) => c == '>' || c == '+' || c == '~'
      | _ => false
    dropStar (acc.push cv) ends rest

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
        else if nthFunctions.contains n then
          -- the An+B part in its canonical form, then `of` and the selector list
          let t := anbSource args
          match t.splitOn " of " with
          | ab :: rest =>
            match L4Factoidal.DOM.Selectors.anPlusB ab with
            | some (a, b) =>
              let ofText := if rest.isEmpty then "" else " of " ++ selectorTokensText fuel (CV.parse (" of ".intercalate rest))
              n ++ "(" ++ anbText a b ++ ofText ++ ")"
            | none => n ++ "(" ++ t ++ ")"
          | [] => n ++ "(" ++ t ++ ")"
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
    ((dropStar #[] true (trimWs cvs)).toList.foldl step ("", false, false)).1

/-- The canonical text of a selector text, when `DOM.Selectors` reads it; `none` is a
SyntaxError. -/
def selectorText (s : String) : Option String :=
  if (L4Factoidal.DOM.Selectors.parse s).isSome then
    let cvs := CV.parse s
    some (selectorTokensText (cvSize 64 cvs + 2) cvs)
  else none

#guard selectorText ":nth-child(odd)" == some ":nth-child(2n+1)"
#guard selectorText ":nth-child( +n )" == some ":nth-child(n)"
#guard selectorText "li:nth-last-of-type(-N-5)" == some "li:nth-last-of-type(-n-5)"
#guard selectorText ":nth-child(2n+0 of .a,b)" == some ":nth-child(2n of .a, b)"
#guard selectorText ":nth-child(5n -3)" == some ":nth-child(5n-3)" && selectorText ":nth-child(-n+ 6)" == some ":nth-child(-n+6)"
#guard selectorText "*::before" == some "::before"
#guard selectorText "a > *::marker, *::after" == some "a > ::marker, ::after"
#guard selectorText "*:hover" == some "*:hover"
#guard selectorText "ns|*::before" == none || selectorText "ns|*::before" == some "ns|*::before"

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

/-- The text of a media query list split at its top-level commas. A loop over the
characters (a tail call). -/
def topCommaPieces (cs : List Char) (depth : Nat) (cur : String) (acc : List String) : List String :=
  match cs with
  | [] => (cur :: acc).reverse
  | c :: rest =>
    if c == ',' && depth == 0 then topCommaPieces rest depth "" (cur :: acc)
    else if c == '(' || c == '[' || c == '{' then topCommaPieces rest (depth + 1) (cur.push c) acc
    else if c == ')' || c == ']' || c == '}' then topCommaPieces rest (depth - 1) (cur.push c) acc
    else topCommaPieces rest depth (cur.push c) acc

/-- The media query list of an `@media` prelude as CSSOM shows it (Media Queries 4 §3,
CSSOM §4.2): a query with a syntax error is `not all`, the others as written in canonical
form. -/
def mediaListText (prelude : String) : String :=
  let ts := MediaQuery.tokenize prelude.toList "" []
  if ts.isEmpty then prelude else
  let bad := (MediaQuery.groups ts).map fun (b, items) => (MediaQuery.query b items).malformed
  let pieces := (topCommaPieces prelude.toList 0 "" []).map fun t => t.trimAscii.toString
  if pieces.length != bad.length then prelude
  else ", ".intercalate ((pieces.zip bad).map fun (t, m) => if m then "not all" else t)

#guard mediaListText "screen, only (orientation)" == "screen, not all"
#guard mediaListText "not and" == "not all" && mediaListText "layer" == "not all"
#guard mediaListText "(min-width: 100px) and screen" == "not all"
#guard mediaListText "screen and (min-width: 100px), print" == "screen and (min-width: 100px), print"
#guard mediaListText "(orientation) and not (orientation)" == "not all"

/-- A selector list of an `@scope` prelude, when it is one: no pseudo-element; a scope
limit (`to (...)`) may start with a combinator and use `&` (read as `:scope`). -/
def scopeSelectors (limit : Bool) (body : List CV) : Option String :=
  let text := rawText body
  let probe := if limit then
      let t := text.replace "&" ":scope"
      String.intercalate ", " ((t.splitOn ",").map fun part =>
        let p := part.trimAscii.toString
        if p.startsWith ">" || p.startsWith "+" || p.startsWith "~" then ":scope " ++ p else p)
    else text.replace "&" ":scope"
  match L4Factoidal.DOM.Selectors.parse probe with
  | some l =>
    if l.isEmpty || l.any (·.hasPseudoElement) then none
    else some (selectorTokensText (cvSize 64 body + 2) body).trimAscii.toString
  | none => none

/-- The canonical prelude of `@scope` (CSS Cascade 6 §2.1): `(<scope-start>)`, `to
(<scope-end>)`, both, or nothing; `none` when the prelude is not one of these. -/
def scopePrelude (prelude : String) : Option String :=
  let isTo := fun (cv : CV) => match cv with
    | .tok (.ident k) => lower k == "to"
    | _ => false
  match stripWs (CV.parse prelude) with
  | [] => some ""
  | [.block '(' a] => (scopeSelectors false a).map fun x => "(" ++ x ++ ")"
  | [to, .block '(' b] => if isTo to then (scopeSelectors true b).map fun y => "to (" ++ y ++ ")" else none
  | [.block '(' a, to, .block '(' b] =>
    if !isTo to then none
    else match scopeSelectors false a, scopeSelectors true b with
      | some x, some y => some ("(" ++ x ++ ") to (" ++ y ++ ")")
      | _, _ => none
  | _ => none

#guard scopePrelude " (.a)to (.b)" == some "(.a) to (.b)"
#guard scopePrelude "(.a:hover, #b, div)" == some "(.a:hover, #b, div)"
#guard scopePrelude "(.a) to (> .b)" == some "(.a) to (> .b)"
#guard scopePrelude "(.a) to (& > &)" == some "(.a) to (& > &)"
#guard scopePrelude "" == some ""
#guard (["()", "to ()", "(div::before)", "div", "(.a) unknown (.c)", "1px", "(.a) from (.c)", "(.c <> .d)"].map scopePrelude).all (·.isNone)

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
      let after := if name == "media" then mediaListText after else after
      -- an @scope prelude (CSS Cascade 6 §2.1): its selectors written as selectors; a
      -- prelude that is not one drops the rule
      let scope := if name == "scope" then scopePrelude (String.ofList (rest.dropWhile isNameChar)) else some after
      let after := scope.getD after
      let head := "@" ++ name ++ (if after == "" then "" else " " ++ after)
      if scope.isNone then none else
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
            if name == "property" then
              -- an `@property` rule that is not a valid registration is dropped (CSS
              -- Properties and Values API 1 §3)
              (CssRegister.propertyRuleOf after body).map fun r => ⟨kind, type, after, body, head ++ " { " ++ r.text ++ " }"⟩
            else
            -- descriptors are kept as written (they are not properties of the table)
            let decls := (splitTop ';' (body.length + 1) body.toList 0 none [] []).filterMap fun piece =>
              (declOf piece).map fun (n, v, _) => lower n ++ ": " ++ trimText v ++ ";"
            let text := if decls.isEmpty then head ++ " { }" else head ++ " { " ++ " ".intercalate decls ++ " }"
            some ⟨kind, type, after, body, text⟩
          | none =>
            if (name == "keyframes" || name == "-webkit-keyframes") && keyframesName after then
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
  | ["property", prelude, body] =>
    -- CSSPropertyRule: syntax, inherits ("1"/"0"), initial value ("1" and the value, or "0")
    match CssRegister.propertyRuleOf prelude body with
    | some r => "\x00".intercalate [r.syn, if r.inherits then "1" else "0", match r.initial with
        | some v => "1" ++ v
        | none => "0"]
    | none => ""
  | _ => ""

/-! ### Tests and theorems -/

#guard (rulesOf "a { color: RED } b{}").map (·.cssText) == ["a { color: red; }", "b { }"]
#guard (rulesOf "@property --a { initial-value: 0px; inherits: true; syntax: '<length>' } @property --b { inherits: true }").map (·.cssText) ==
  ["@property --a { syntax: \"<length>\"; inherits: true; initial-value: 0px; }"]
#guard sheetOp "property\x00--a\x00syntax: '*'; inherits: false" == "*\x000\x000"
#guard (rulesOf "a { color: red; } /* x */ @media screen { b { top: 0 } }").map (·.kind) == ["Style", "Media"]
#guard (rulesOf "@media (MIN-WIDTH:100px) and screen { b { top: 0 } }").map (·.cssText) ==
  ["@media not all {\n  b { top: 0px; }\n}"]
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
