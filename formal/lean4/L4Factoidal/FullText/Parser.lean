/-
L4Factoidal.FullText.Parser — the grammar of XQuery and XPath Full Text
3.0 (W3C Recommendation, Appendix A, productions FTContainsExpr to
FTIgnoreOption, FTScoreVar and FTOptionDecl), as an extension of the
XPath 4.0 parser.

`ftPostConcat` is the `ExtGrammar.postConcat` hook of `XPath4.Parser`:
after every StringConcatExpr the parser asks it whether `contains text`
follows (production FTContainsExpr, between ComparisonExpr and
StringConcatExpr). Embedded expressions (FTWordsValue `{ Expr }`, FTWeight,
the AdditiveExprs of FTRange and FTWindow, the UnionExpr of
FTIgnoreOption) are parsed by the host parser through `SubParsers`.

The selection is kept in the expression tree as `Expr.ext` nodes with
tags `ft.*` (the encoding is listed at `ftTags`); `FullText.Eval` reads it
back. Static errors raised here: XPST0003 (syntax) and FTST0019 (two match
options of one group in one FTMatchOptions).
-/
import L4Factoidal.XPath4.Parser

namespace L4Factoidal.FullText

open L4Factoidal.XPath4

/-- The tags of the `Expr.ext` nodes of a full-text selection:

* `ft.contains` `[lhs, sel]` or `[lhs, sel, ignore]`; `ss` = the
  `declare ft-option` settings of the prolog, one string per declaration;
* `ft.words` `[value]`, `ss = [mode]` (`any`, `any word`, `all`,
  `all words`, `phrase`);
* `ft.times` `sel :: range`, `ss = [range kind]`;
* `ft.or`, `ft.and`, `ft.mildnot` `[a, b]`; `ft.not` `[a]`;
* `ft.opts` `[sel]`, `ss` = the match options (`encodeOpt`);
* `ft.weight` `[sel, w]`;
* `ft.order` `[sel]`; `ft.window` `[sel, n]`, `ss = [unit]`;
  `ft.distance` `sel :: range`, `ss = [unit, range kind]`;
  `ft.scope` `[sel]`, `ss = [same|different, sentence|paragraph]`;
  `ft.content` `[sel]`, `ss = [start|end|entire]`;
* `ft.extsel` `[sel]` or `[]`, `ss` = the pragma names. -/
def ftTags : List String :=
  ["ft.contains", "ft.words", "ft.times", "ft.or", "ft.and", "ft.mildnot", "ft.not", "ft.opts",
   "ft.weight", "ft.order", "ft.window", "ft.distance", "ft.scope", "ft.content", "ft.extsel"]

/-- The field separator inside an encoded match option. -/
def fsep : String := "\x1f"
/-- The separator between the options of one `declare ft-option`. -/
def osep : String := "\x1d"

/-- Run a sub-parser of the host at the current offset. -/
def subP {α} (f : List (String × String) → Nat → Except Err (α × Nat)) : P α := do
  let c ← read
  let i ← get
  match f c.ns i with
  | .ok (a, j) => set j; pure a
  | .error e => throw e

/-- Is the next keyword `k` followed by keyword `k2`? Consumes both if so. -/
def eatKw2 (k k2 : String) : P Bool := do
  let i ← get
  if ← eatKw k then
    if ← eatKw k2 then return true
  set i
  pure false

/-- A string literal; `lit` expands XQuery references. -/
def pLit (lit : String → Except Err String) : P String := do
  let raw ← pStringLit
  match lit raw with
  | .ok v => pure v
  | .error e => throw e

/-- An unsigned integer literal (FTLiteralRange). -/
def pIntLit : P Nat := do
  ws
  let c ← read
  let i ← get
  let mut j := i
  let mut v := 0
  for _ in [0:c.s.size] do
    let ch := chAt c.s j
    if ch.isDigit then v := v * 10 + (ch.toNat - 48); j := j + 1 else break
  if j == i then synErr "expected an integer literal"
  if isNameStart (chAt c.s j) || chAt c.s j == '.' then synErr "expected an integer literal"
  set j
  pure v

/-- An EQName, expanded (`Q{uri}local`). -/
def pEQNameStr : P String := do
  match ← peekQName with
  | some (p, u, l, e) =>
    set e
    let uri ← match u, p with
      | some uu, _ => pure uu
      | none, some pp => lookupNs pp
      | none, none => pure ""
    pure ("Q{" ++ uri ++ "}" ++ l)
  | none => synErr "expected a name"

/-! ## Ranges -/

/-- FTRange (with AdditiveExprs): the kind and the expressions. -/
def pRange (sp : SubParsers) : P (String × List Expr) := do
  if ← eatKw "exactly" then return ("exactly", [← subP sp.additive])
  if ← eatKw2 "at" "least" then return ("atleast", [← subP sp.additive])
  if ← eatKw2 "at" "most" then return ("atmost", [← subP sp.additive])
  if ← eatKw "from" then
    let a ← subP sp.additive
    expectKw "to"
    let b ← subP sp.additive
    return ("fromto", [a, b])
  synErr "expected a range (exactly, at least, at most, from)"

/-- FTLiteralRange: the kind and the bounds. -/
def pLitRange : P (Option (String × Nat × Nat)) := do
  if ← eatKw "exactly" then let n ← pIntLit; return some ("exactly", n, n)
  if ← eatKw2 "at" "least" then let n ← pIntLit; return some ("atleast", n, 0)
  if ← eatKw2 "at" "most" then let n ← pIntLit; return some ("atmost", n, 0)
  if ← eatKw "from" then
    let a ← pIntLit
    expectKw "to"
    let b ← pIntLit
    return some ("fromto", a, b)
  pure none

/-! ## Match options (§3.4) -/

/-- FTThesaurusID or `default`, encoded as `tid` fields. -/
def pThesId (lit : String → Except Err String) : P String := do
  if ← eatKw "default" then return "tid" ++ fsep ++ "#default"
  expectKw "at"
  let uri ← pLit lit
  let rel ← if ← eatKw "relationship" then pure (some (← pLit lit)) else pure none
  let rng ← pLitRange
  if rng.isSome then expectKw "levels"
  let (k, a, b) := rng.getD ("", 0, 0)
  pure ("tid" ++ fsep ++ uri ++ fsep ++ (rel.getD "\x00") ++ fsep ++ k ++ fsep ++ toString a ++ fsep ++ toString b)

/-- FTStopWords: `at URI` or a list of string literals. -/
def pStopWords (lit : String → Except Err String) : P String := do
  if ← eatKw "at" then return "uri" ++ fsep ++ (← pLit lit)
  if ← eatS "(" then
    let mut ws : Array String := #[← pLit lit]
    for _ in [0:100000] do
      if ← eatS "," then ws := ws.push (← pLit lit) else break
    expectS ")"
    return "list" ++ fsep ++ String.intercalate fsep ws.toList
  synErr "expected stop words (at URI or a list)"

/-- One FTMatchOption: its group and its encoding. -/
def pMatchOption (lit : String → Except Err String) : P (String × List String) := do
  if ← eatKw "language" then return ("lang", ["lang" ++ fsep ++ (← pLit lit)])
  if ← eatKw "wildcards" then return ("wild", ["wild" ++ fsep ++ "1"])
  if ← eatKw2 "no" "wildcards" then return ("wild", ["wild" ++ fsep ++ "0"])
  if ← eatKw "stemming" then return ("stem", ["stem" ++ fsep ++ "1"])
  if ← eatKw2 "no" "stemming" then return ("stem", ["stem" ++ fsep ++ "0"])
  if ← eatKw2 "case" "insensitive" then return ("case", ["case" ++ fsep ++ "insensitive"])
  if ← eatKw2 "case" "sensitive" then return ("case", ["case" ++ fsep ++ "sensitive"])
  if ← eatKw "lowercase" then return ("case", ["case" ++ fsep ++ "lower"])
  if ← eatKw "uppercase" then return ("case", ["case" ++ fsep ++ "upper"])
  if ← eatKw2 "diacritics" "insensitive" then return ("diac", ["diac" ++ fsep ++ "insensitive"])
  if ← eatKw2 "diacritics" "sensitive" then return ("diac", ["diac" ++ fsep ++ "sensitive"])
  if ← eatKw2 "no" "thesaurus" then return ("thes", ["thes" ++ fsep ++ "none"])
  if ← eatKw "thesaurus" then
    if ← eatS "(" then
      let mut ids : Array String := #[← pThesId lit]
      for _ in [0:100000] do
        if ← eatS "," then
          if ← atKw "default" then synErr "default is only allowed first in a thesaurus list"
          ids := ids.push (← pThesId lit)
        else break
      expectS ")"
      return ("thes", ("thes" ++ fsep ++ "use") :: ids.toList)
    return ("thes", ["thes" ++ fsep ++ "use", ← pThesId lit])
  if ← eatKw "no" then
    expectKw "stop"; expectKw "words"
    return ("stop", ["stop" ++ fsep ++ "none"])
  if ← eatKw "stop" then
    expectKw "words"
    let base ← if ← eatKw "default" then pure ("stop" ++ fsep ++ "default")
      else pure ("stop" ++ fsep ++ (← pStopWords lit))
    let mut ops : Array String := #[]
    for _ in [0:100000] do
      if ← eatKw "union" then ops := ops.push ("stopop" ++ fsep ++ "union" ++ fsep ++ (← pStopWords lit))
      else if ← eatKw "except" then ops := ops.push ("stopop" ++ fsep ++ "except" ++ fsep ++ (← pStopWords lit))
      else break
    return ("stop", base :: ops.toList)
  if ← eatKw "option" then
    let q ← pEQNameStr
    let v ← pLit lit
    return ("ext", ["ext" ++ fsep ++ q ++ fsep ++ v])
  synErr "expected a match option after 'using'"

/-- FTMatchOptions: `("using" FTMatchOption)+`; err:FTST0019 when two
    options of one group occur. -/
def pMatchOptions (lit : String → Except Err String) : P (List String) := do
  let mut groups : List String := []
  let mut out : Array String := #[]
  for _ in [0:100000] do
    if ← eatKw "using" then
      let (g, enc) ← pMatchOption lit
      if g != "ext" && groups.contains g then
        throw { code := "FTST0019", msg := "two match options of the group " ++ g }
      groups := g :: groups
      out := out ++ enc.toArray
    else break
  pure out.toList

/-! ## Selections (§3) -/

/-- Pragma (`(# EQName contents #)`): the expanded name. -/
def pPragma : P String := do
  expectS "(#"
  let c ← read
  let i ← get
  let i := skipWsF c.s (c.s.size + 1) 0 i
  set i
  let nm ← pEQNameStr
  -- the contents up to `#)`
  let c ← read
  let mut j ← get
  for _ in [0:c.s.size] do
    if j + 1 ≥ c.s.size then synErr "unterminated pragma"
    if chAt c.s j == '#' && chAt c.s (j + 1) == ')' then break
    j := j + 1
  set (j + 2)
  pure nm

/-- FTUnit ::= "words" | "sentences" | "paragraphs" -/
def pUnit : P String := do
  if ← eatKw "words" then return "words"
  if ← eatKw "sentences" then return "sentences"
  if ← eatKw "paragraphs" then return "paragraphs"
  synErr "expected words, sentences or paragraphs"

-- The selection grammar; the fuel bounds the nesting.
mutual

/-- FTSelection ::= FTOr FTPosFilter* -/
def pSelection (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    let mut s ← pOr lit sp n
    for _ in [0:100000] do
      if ← eatKw "ordered" then s := .ext "ft.order" [s] [] [] []
      else if ← eatKw "window" then
        let k ← subP sp.additive
        let u ← pUnit
        s := .ext "ft.window" [s, k] [] [] [u]
      else if ← eatKw "distance" then
        let (rk, rs) ← pRange sp
        let u ← pUnit
        s := .ext "ft.distance" (s :: rs) [] [] [u, rk]
      else if ← atKw "same" <||> atKw "different" then
        let same ← eatKw "same"
        if !same then let _ ← eatKw "different"
        let u ← if ← eatKw "sentence" then pure "sentence"
          else if ← eatKw "paragraph" then pure "paragraph"
          else synErr "expected sentence or paragraph"
        s := .ext "ft.scope" [s] [] [] [if same then "same" else "different", u]
      else if ← eatKw2 "at" "start" then s := .ext "ft.content" [s] [] [] ["start"]
      else if ← eatKw2 "at" "end" then s := .ext "ft.content" [s] [] [] ["end"]
      else if ← eatKw2 "entire" "content" then s := .ext "ft.content" [s] [] [] ["entire"]
      else break
    pure s

/-- FTOr ::= FTAnd ( "ftor" FTAnd )* -/
def pOr (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    let mut a ← pAnd lit sp n
    for _ in [0:100000] do
      if ← eatKw "ftor" then a := .ext "ft.or" [a, ← pAnd lit sp n] [] [] [] else break
    pure a

/-- FTAnd ::= FTMildNot ( "ftand" FTMildNot )* -/
def pAnd (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    let mut a ← pMildNot lit sp n
    for _ in [0:100000] do
      if ← eatKw "ftand" then a := .ext "ft.and" [a, ← pMildNot lit sp n] [] [] [] else break
    pure a

/-- FTMildNot ::= FTUnaryNot ( "not" "in" FTUnaryNot )* -/
def pMildNot (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    let mut a ← pUnaryNot lit sp n
    for _ in [0:100000] do
      if ← eatKw2 "not" "in" then a := .ext "ft.mildnot" [a, ← pUnaryNot lit sp n] [] [] [] else break
    pure a

/-- FTUnaryNot ::= ("ftnot")? FTPrimaryWithOptions -/
def pUnaryNot (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    if ← eatKw "ftnot" then return .ext "ft.not" [← pPrimaryWithOptions lit sp n] [] [] []
    pPrimaryWithOptions lit sp n

/-- FTPrimaryWithOptions ::= FTPrimary FTMatchOptions? FTWeight? -/
def pPrimaryWithOptions (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    let mut p ← pPrimary lit sp n
    let os ← pMatchOptions lit
    if !os.isEmpty then p := .ext "ft.opts" [p] [] [] os
    if ← eatKw "weight" then
      expectS "{"
      let w ← subP sp.expr
      expectS "}"
      p := .ext "ft.weight" [p, w] [] [] []
    pure p

/-- FTPrimary ::= (FTWords FTTimes?) | ("(" FTSelection ")") | FTExtensionSelection -/
def pPrimary (lit : String → Except Err String) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "full-text selection too deeply nested"
  | n + 1 => do
    if ← atS "(#" then
      let mut names : Array String := #[← pPragma]
      for _ in [0:100000] do
        if ← atS "(#" then names := names.push (← pPragma) else break
      expectS "{"
      if ← eatS "}" then return .ext "ft.extsel" [] [] [] names.toList
      let s ← pSelection lit sp n
      expectS "}"
      return .ext "ft.extsel" [s] [] [] names.toList
    if ← eatS "(" then
      let s ← pSelection lit sp n
      expectS ")"
      return s
    -- FTWords ::= FTWordsValue FTAnyallOption?
    let v ← if ← eatS "{" then
        let e ← subP sp.expr
        expectS "}"
        pure e
      else do
        ws
        let c ← read
        let ch := chAt c.s (← get)
        if ch == '"' || ch == '\'' then pure (Expr.lit (Atomic.ofStr (← pLit lit)))
        else synErr "expected a full-text selection"
    let mode ← if ← eatKw "any" then
        (if ← eatKw "word" then pure "any word" else pure "any")
      else if ← eatKw "all" then
        (if ← eatKw "words" then pure "all words" else pure "all")
      else if ← eatKw "phrase" then pure "phrase"
      else pure "any"
    let w := Expr.ext "ft.words" [v] [] [] [mode]
    if ← eatKw "occurs" then
      let (rk, rs) ← pRange sp
      expectKw "times"
      return .ext "ft.times" (w :: rs) [] [] [rk]
    pure w

end

/-- The `contains text` tail after a StringConcatExpr `lhs`
    (FTContainsExpr, FTIgnoreOption). -/
def pContainsTail (lit : String → Except Err String) (sp : SubParsers) (lhs : Expr) : P (Option Expr) := do
  let i ← get
  if !(← eatKw "contains") then return none
  if !(← eatKw "text") then set i; return none
  let sel ← pSelection lit sp 200
  let c ← read
  let decls := match c.ns.lookup "#ftopt" with
    | some d => (d.splitOn "\x1e").filter (· != "")
    | none => []
  if ← eatKw2 "without" "content" then
    let ig ← subP sp.union
    return some (.ext "ft.contains" [lhs, sel, ig] [] [] decls)
  pure (some (.ext "ft.contains" [lhs, sel] [] [] decls))

/-- The `ExtGrammar.postConcat` hook. -/
def ftPostConcat (lit : String → Except Err String) (s : Array Char) (ns : List (String × String))
    (sp : SubParsers) (lhs : Expr) (i : Nat) : Except Err (Option (Expr × Nat)) :=
  match ((pContainsTail lit sp lhs).run { s, ns }).run i with
  | .ok (some e, j) => .ok (some (e, j))
  | .ok (none, _) => .ok none
  | .error e => .error e

end L4Factoidal.FullText
