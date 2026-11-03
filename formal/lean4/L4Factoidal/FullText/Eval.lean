/-
L4Factoidal.FullText.Eval — the evaluation of `contains text`
(XQuery and XPath Full Text 3.0 §2.2, §4.3 `fts:FTContainsExpr`) inside
the XPath 4.0 / XQuery 4.0 evaluator.

`evalFt` receives an `ft.contains` node of the expression tree (built by
`FullText.Parser`) from `XQuery4.Runtime.evalExt`, with callbacks into the
evaluator. It

1. evaluates the left operand (the search context items) and the
   FTIgnoreOption (the nodes to ignore, which must be nodes: XPTY0004);
2. resolves the selection to an `RSel`: the FTWordsValue expressions are
   atomized to strings, the FTRange and FTWindow expressions are coerced
   to `xs:integer`, the weights to `xs:double` (|w| > 1000 is FTDY0016),
   the stop word lists and thesauri are read from the resources of the
   dynamic context (a URI that is not there is FTST0008 or FTST0018);
3. tokenizes each search context item (`FullText.Tokenize`): a node by
   its text nodes in document order, without the ignored subtrees
   (`fts:reconstruct`), each text node a paragraph segment; an attribute,
   text, comment or processing-instruction node or an atomic value by
   its string value;
4. returns true when `FullText.containsCtx` holds for some item.

The static match options of the module (`declare ft-option`) are
applied first, then the options inside the selection.
-/
import L4Factoidal.FullText.Select
import L4Factoidal.FullText.Parser
import L4Factoidal.XPath4.Core

namespace L4Factoidal.FullText

open L4Factoidal.XPath4

/-- The callbacks into the evaluator. -/
structure FtCb where
  eval : Env → Expr → M Seq

/-- An error of the pure layer as an XPath error. -/
def liftE {α} (r : Except (String × String) α) : M α :=
  match r with
  | .ok a => .ok a
  | .error (c, m) => .error { code := c, msg := m }

/-! ## Resources: stop word lists and thesauri -/

/-- The text of a resource of the dynamic context by URI. -/
def resourceText (env : Env) (uri : String) : Option String :=
  match env.resources.lookup uri with
  | some t => some t
  | none =>
    match env.resourceBytes.lookup uri with
    | some b => String.fromUTF8? b
    | none => none

/-- A stop word list: the words of the resource, separated by white space. -/
def stopListOf (env : Env) (uri : String) : M (List String) :=
  match resourceText env uri with
  | some t => pure ((t.split (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')).toList.map
      (·.toString) |>.filter (· != ""))
  | none => err "FTST0008" ("stop word list not found: " ++ uri)

/-- The implementation-defined default stop word list (§3.4.7
    `stop words default`): the default list of the W3C XQuery and XPath
    Full Text test suite (XQFTTS, `StopWordList.xml`; the qt4tests feature
    `fullText-defaults` requires it). -/
def defaultStopWords : List String :=
  ["and", "the", "then", "it", "of", "in", "not", "been", "numerous"]

/-- The local name of an XML tag. -/
def localOf (t : String) : String :=
  match t.splitOn ":" with
  | [_, l] => l
  | _ => t

def childNamed (n : L4Factoidal.XML.Node) (l : String) : List L4Factoidal.XML.Node :=
  n.allChildElements.filter (fun c => (c.elementTag.map localOf) == some l)

def childText (n : L4Factoidal.XML.Node) (l : String) : String :=
  match childNamed n l with
  | c :: _ => c.textContent.trim
  | [] => ""

/-- The relations of a `synonym` element and of the `synonym` elements
    nested in it (a nested synonym is one level further from the term of
    its parent). -/
def synEdges : Nat → String → L4Factoidal.XML.Node → List (String × List (String × String))
  | 0, _, _ => []
  | f + 1, from_, s =>
    let t := childText s "term"
    (from_, [(t, childText s "relationship")]) ::
      (childNamed s "synonym").flatMap (fun n => synEdges f t n)

/-- A thesaurus document (the XQFTTS thesaurus format: `entry` elements
    with a `term` and `synonym` elements, each with a `term`, a
    `relationship` and nested `synonym` elements). -/
def parseThesaurus (t : String) : Option Thesaurus :=
  match L4Factoidal.XML.parseXML t with
  | .error _ => none
  | .ok d =>
    let roots := d.children.filter (fun n => n.elementTag.isSome)
    some (roots.flatMap (fun r => (childNamed r "entry").flatMap (fun e =>
      (childNamed e "synonym").flatMap (fun s => synEdges 64 (childText e "term") s))))

def thesaurusOf (env : Env) (uri : String) : M Thesaurus :=
  match resourceText env uri with
  | none => err "FTST0018" ("thesaurus not found: " ++ uri)
  | some t => match parseThesaurus t with
    | some th => pure th
    | none => err "FTST0018" ("thesaurus not readable: " ++ uri)

/-- The default thesaurus (§3.4.3 `thesaurus default`): the default
    thesaurus of the W3C Full Text test suite (XQFTTS,
    `UsabilityThesaurus.xml`; the qt4tests feature `fullText-defaults`
    requires it). -/
def defaultThesaurus : Thesaurus :=
  [("duties", [("tasks", "UF")]), ("duty", [("task", "UF")]), ("people", [("users", "NT")]),
   ("web site components", [("navigation", "NT")]), ("web site components", [("layout", "NT")]),
   ("web site components", [("terminology", "NT")]),
   ("web site components", [("navigation", "narrower terms")]),
   ("web site components", [("layout", "narrower terms")]),
   ("web site components", [("terminology", "narrower terms")]),
   ("quote", [("remarked", "UF")]), ("quote", [("remarked", "synonyms")]),
   ("letters", [("correspondence", "BT")]), ("sucessfull", [("successful", "misspelling-of")]),
   ("AIDS", [("Hepatitis", "disease in this category")]),
   ("AIDS", [("Tuberculosis", "disease in this category")]),
   ("program", [("software", "UF")]), ("infrastructure", [("networks", "NT")]),
   ("networks", [("Web", "NT")])]

/-- The languages of the language option (§3.4.1, err:FTST0009): a
    language tag (`xs:language`) whose primary subtag has two or three
    letters (an ISO 639 code). Only English has a stemmer. -/
def languageSupported (v : String) : Bool :=
  let parts := v.splitOn "-"
  let prim := parts.headD ""
  (prim.length == 2 || prim.length == 3) && prim.toList.all Char.isAlpha &&
  parts.tail.all (fun p => 1 ≤ p.length && p.length ≤ 8 && p.toList.all Char.isAlphanum)

/-! ## Decoding the match options -/

def fields (s : String) : List String := s.splitOn fsep

/-- Stop words of an FTStopWords encoding (`uri` or `list`). -/
def stopSource (env : Env) : List String → M (List String)
  | "uri" :: u :: _ => stopListOf env u
  | "list" :: ws => pure ws
  | _ => pure []

/-- Read the encoded match options of one FTMatchOptions. -/
def decodeOpts (env : Env) (enc : List String) : M POpts := do
  let mut p : POpts := {}
  let mut thes : List ThesSpec := []
  let mut thesUse := false
  let mut stopAcc : Option (List String) := none
  for e in enc do
    match fields e with
    | ["case", v] =>
      p := { p with caseO := some (match v with
        | "sensitive" => .sensitive | "lower" => .lower | "upper" => .upper | _ => .insensitive) }
    | ["diac", v] => p := { p with diacriticsSensitive := some (v == "sensitive") }
    | ["stem", v] => p := { p with stem := some (v == "1") }
    | ["wild", v] => p := { p with wild := some (v == "1") }
    | ["lang", v] =>
      if !languageSupported v then err "FTST0009" ("language not supported: " ++ v)
      p := { p with lang := some v }
    | ["thes", "none"] => p := { p with thes := some [] }
    | ["thes", "use"] => thesUse := true
    | "tid" :: "#default" :: _ => thes := thes ++ [{ data := defaultThesaurus }]
    | ["tid", uri, rel, k, a, b] =>
      let data ← thesaurusOf env uri
      let a := (a.toNat?.getD 0 : Int)
      let b := (b.toNat?.getD 0 : Int)
      let levels : Option Range := match k with
        | "exactly" => some (.exactly a) | "atleast" => some (.atLeast a)
        | "atmost" => some (.atMost a) | "fromto" => some (.fromTo a b) | _ => none
      thes := thes ++ [{ data, rel := if rel == "\x00" then none else some rel, levels }]
    | ["stop", "none"] => stopAcc := some []
    | ["stop", "default"] => stopAcc := some defaultStopWords
    | "stop" :: rest => stopAcc := some (← stopSource env rest)
    | "stopop" :: op :: rest =>
      let ws ← stopSource env rest
      let cur := stopAcc.getD []
      stopAcc := some (if op == "union" then cur ++ ws else cur.filter (fun w => !ws.contains w))
    | _ => pure ()
  if thesUse then p := { p with thes := some thes }
  if let some s := stopAcc then p := { p with stop := some s }
  pure p

/-! ## Resolving a selection -/

/-- An integer operand of FTRange or FTWindow (expected type `xs:integer`). -/
def intOf (env : Env) (s : Seq) : M Int := do
  match ← env.coerce (parseTy "xs:integer") s "full-text range" with
  | [.atom a] => match a.v with
    | .int i => pure i
    | _ => err "XPTY0004" "a full-text range needs an xs:integer"
  | _ => err "XPTY0004" "a full-text range needs one xs:integer"

def rangeOf (env : Env) (cb : FtCb) (kind : String) (es : List Expr) : M Range := do
  let vs ← es.mapM (fun e => do intOf env (← cb.eval env e))
  match kind, vs with
  | "exactly", [n] => pure (.exactly n)
  | "atleast", [n] => pure (.atLeast n)
  | "atmost", [n] => pure (.atMost n)
  | "fromto", [m, n] => pure (.fromTo m n)
  | _, _ => err "XPST0003" "bad full-text range"

def wmodeOf : String → WMode
  | "any word" => .anyWord | "all words" => .allWords | "phrase" => .phrase
  | "all" => .all | _ => .any

def unitOf : String → Unit_
  | "sentences" => .sentences | "paragraphs" => .paragraphs | _ => .words

/-- Resolve a selection tree (fuel bounds the depth). -/
def resolve (env : Env) (cb : FtCb) : Nat → Expr → M RSel
  | 0, _ => err "XPST0003" "full-text selection too deeply nested"
  | n + 1, e =>
    match e with
    | .ext "ft.words" [v] _ _ ss => do
      -- the FTWordsValue has the expected type xs:string* (§3.2)
      let s ← env.coerce (parseTy "xs:string*") (← cb.eval env v) "FTWordsValue"
      let as ← env.atomize s
      pure (.words (as.map Atomic.str) (wmodeOf (ss.headD "any")))
    | .ext "ft.times" (s :: rs) _ _ ss => do
      pure (.times (← resolve env cb n s) (← rangeOf env cb (ss.headD "") rs))
    | .ext "ft.or" [a, b] _ _ _ => do pure (.or (← resolve env cb n a) (← resolve env cb n b))
    | .ext "ft.and" [a, b] _ _ _ => do pure (.and (← resolve env cb n a) (← resolve env cb n b))
    | .ext "ft.mildnot" [a, b] _ _ _ => do pure (.mildNot (← resolve env cb n a) (← resolve env cb n b))
    | .ext "ft.not" [a] _ _ _ => do pure (.unaryNot (← resolve env cb n a))
    | .ext "ft.opts" [s] _ _ ss => do pure (.opts (← resolve env cb n s) (← decodeOpts env ss))
    | .ext "ft.weight" [s, w] _ _ _ => do
      let r ← resolve env cb n s
      let wv ← env.coerce (parseTy "xs:double") (← cb.eval env w) "weight"
      match wv with
      | [.atom a] => match a.v with
        | .dbl f =>
          if f.abs > 1000.0 || f.isNaN then err "FTDY0016" "a weight outside -1000 to 1000"
          else pure (.weight r f)
        | _ => err "XPTY0004" "a weight needs an xs:double"
      | _ => err "XPTY0004" "a weight needs one xs:double"
    | .ext "ft.order" [s] _ _ _ => do pure (.order (← resolve env cb n s))
    | .ext "ft.window" [s, k] _ _ ss => do
      let r ← resolve env cb n s
      pure (.window r (unitOf (ss.headD "")) (← intOf env (← cb.eval env k)))
    | .ext "ft.distance" (s :: rs) _ _ ss => do
      let r ← resolve env cb n s
      pure (.distance r (unitOf (ss.headD "")) (← rangeOf env cb (ss.getD 1 "") rs))
    | .ext "ft.scope" [s] _ _ ss => do
      pure (.scope (← resolve env cb n s) (ss.headD "" == "same")
        (if ss.getD 1 "" == "sentence" then .sentence else .paragraph))
    | .ext "ft.content" [s] _ _ ss => do
      pure (.content (← resolve env cb n s)
        (match ss.headD "" with | "start" => .atStart | "end" => .atEnd | _ => .entire))
    | .ext "ft.extsel" [s] _ _ _ => resolve env cb n s
    | .ext "ft.extsel" [] _ _ _ => err "XQST0079" "an extension selection with no selection and no known pragma"
    | _ => err "XPST0003" "not a full-text selection"

/-! ## Tokenizing a search context item (`fts:reconstruct`, §4.1) -/

/-- The text segments of the subtree of node `i` of `d` in document order,
    without the ignored nodes (indices of `d`): a new segment starts at
    each element boundary. One loop over the indices of the subtree. -/
def segmentsOf (d : Doc) (i : Nat) (ignored : List Nat) : List String := Id.run do
  let r := d.get i
  match r.kind with
  | .element | .document =>
    let mut out : Array String := #[]
    let mut cur : String := ""
    let mut lastParent : Option Nat := none
    let mut j := i + 1
    for _ in [0:r.last - i + 1] do
      if j > r.last then break
      let x := d.get j
      if ignored.contains j then
        -- the reconstructed node has no boundary there (`fts:reconstruct`
        -- merges the adjacent text)
        j := (if x.last > j then x.last else j) + 1
      else
        match x.kind with
        | .text =>
          if lastParent != x.parent && cur != "" then out := out.push cur; cur := ""
          cur := cur ++ x.value
          lastParent := x.parent
          j := j + 1
        | .element =>
          if cur != "" then out := out.push cur; cur := ""
          lastParent := none
          j := j + 1
        | _ => j := j + 1
    if cur != "" then out := out.push cur
    return out.toList
  | _ => return [r.value]

/-- The tokens of one search context item. -/
def ctxOfItem (env : Env) (ignore : List NodeRef) (it : Item) : M (Option Ctx) := do
  match it with
  | .node n =>
    if ignore.any (fun g => g == n) then return none
    let d := env.doc n
    let ign := (ignore.filter (fun g => g.doc == n.doc)).map (·.idx)
    pure (some (Ctx.ofToks (tokenizeSegments (segmentsOf d n.idx ign))))
  | .atom a => pure (some (Ctx.ofToks (tokenizeString a.str)))
  | _ => err "FOTY0013" "a function item as a full-text search context"

/-- Apply the `declare ft-option` settings, then the selection. -/
def evalContains (env : Env) (cb : FtCb) (es : List Expr) (decls : List String) : M Bool := do
  match es with
  | lhs :: sel :: rest =>
    let items ← cb.eval env lhs
    let ignore ← match rest with
      | [ig] => do
        let s ← cb.eval env ig
        match nodesOf s with
        | some ns => pure ns
        | none => err "XPTY0004" "without content needs nodes"
      | _ => pure []
    let mut o : EOpts := {}
    for d in decls do
      o := o.replace (← decodeOpts env (d.splitOn osep))
    let r ← resolve env cb 1000 sel
    for it in items do
      if let some c ← ctxOfItem env ignore it then
        if ← liftE (containsCtx c o r) then return true
    pure false
  | _ => err "XPST0003" "bad contains text expression"

/-- The score of `contains text` (§2.3): from the AllMatches of the best
    item, see `scoreOfMatches`. -/
def scoreContains (env : Env) (cb : FtCb) (es : List Expr) (decls : List String) : M Float := do
  match es with
  | lhs :: sel :: rest =>
    let items ← cb.eval env lhs
    let ignore ← match rest with
      | [ig] => do
        match nodesOf (← cb.eval env ig) with
        | some ns => pure ns
        | none => err "XPTY0004" "without content needs nodes"
      | _ => pure []
    let mut o : EOpts := {}
    for d in decls do
      o := o.replace (← decodeOpts env (d.splitOn osep))
    let r ← resolve env cb 1000 sel
    let mut best := 0.0
    for it in items do
      if let some c ← ctxOfItem env ignore it then
        let am ← liftE (evalSel c o r 0)
        let s := scoreOfMatches am
        if s > best then best := s
    pure best
  | _ => err "XPST0003" "bad contains text expression"

/-- The score of an expression (§2.3, §4.4 `fts:score`): a
    `contains text` is scored by `scoreContains`; `and` takes the smaller
    and `or` the larger score of its operands; any other expression scores
    1 when its effective boolean value is true (or it has none) and 0
    otherwise. -/
def scoreExpr (env : Env) (cb : FtCb) : Nat → Expr → M Float
  | 0, _ => pure 0.0
  | n + 1, e =>
    match e with
    | .ext "ft.contains" es _ _ ss => scoreContains env cb es ss
    | .bin .and a b => do
      let x ← scoreExpr env cb n a
      let y ← scoreExpr env cb n b
      pure (if x < y then x else y)
    | .bin .or a b => do
      let x ← scoreExpr env cb n a
      let y ← scoreExpr env cb n b
      pure (if x < y then y else x)
    | _ => do
      let v ← cb.eval env e
      match ebv v with
      | .ok b => pure (if b then 1.0 else 0.0)
      | .error _ => pure (if v.isEmpty then 0.0 else 1.0)

/-- The predicates that select the items of an expression, last step first. -/
def lastPreds : Expr → List Expr
  | .slash _ b => lastPreds b
  | .step _ _ ps => ps
  | .dstep _ _ ps => ps
  | .filter _ p => [p]
  | _ => []

/-- `fts:scoreSequence` (§4.4): one score per item of the expression; an
    item selected by predicates gets the smallest score of the predicates
    with the item as the context, any other item scores 1. -/
def scoreSeq (env : Env) (cb : FtCb) (e : Expr) : M Seq := do
  let items ← cb.eval env e
  let ps := lastPreds e
  let mut out : Array Item := #[]
  for it in items do
    let env' := { env with ctx := some [it], pos := 1, size := 1 }
    let mut sc := 1.0
    for p in ps do
      let x ← scoreExpr env' cb 100 p
      if x < sc then sc := x
    out := out.push (.atom (Atomic.ofDbl sc))
  pure out.toList

/-- The `ext` dispatcher for the `ft.*` tags. -/
def evalFt (cb : FtCb) (env : Env) (tag : String) (es : List Expr) (ss : List String) : M Seq := do
  match tag with
  | "ft.contains" => pure (sBool (← evalContains env cb es ss))
  | "ft.score" => match es with
    | [e] => pure (single (Atomic.ofDbl (← scoreExpr env cb 100 e)))
    | _ => err "XPST0003" "bad score"
  | "ft.scoreSeq" => match es with
    | [e] => scoreSeq env cb e
    | _ => err "XPST0003" "bad score"
  | "ft.scoreAt" => match es with
    | [sq, p] => do
      let s ← cb.eval env sq
      let k ← intOf env (← cb.eval env p)
      pure (if k ≥ 1 && k.toNat ≤ s.length then [s.getD (k.toNat - 1) default] else [single (Atomic.ofDbl 0.0)].flatten)
    | _ => err "XPST0003" "bad score"
  | _ => err "XPST0003" ("a full-text selection outside contains text: " ++ tag)

end L4Factoidal.FullText
