/-
L4Factoidal.XQuery4.Grammar — the expression productions that XQuery
4.0 adds to XPath 4.0 (XQuery 4.0 editor's draft,
https://qt4cg.org/specifications/xquery-40/xquery-40.html, Appendix A;
qtspecs commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c).

The productions plug into the XPath 4.0 parser through its
`ExtGrammar` hook (`XPath4.Parser`): the parser tries `exprSingle` at
every ExprSingle and `primary` at every PrimaryExpr, and calls back
into its own `Expr`, `ExprSingle` and `SequenceType` parsers through
`SubParsers`. So an XQuery expression and an XPath expression share one
parser, and an expression with no XQuery construct parses to the same
tree in both languages.

Productions:

* FLWOR (§4.13): `for` (item, `member`, `key`/`value`, `allowing
  empty`, `at`), `let`, `where`, `while`, `count`, `order by`,
  `group by`, `for tumbling|sliding window`, `return`. A FLWOR of
  `for`/`let`/`where` clauses only is written as the nested XPath
  `for`/`let`/`if` (`flworToXPath`); the others become the tuple-stream
  node `ext "flwor"` of `XQuery4.Runtime`;
* `switch` and `typeswitch` (§4.19), also with braces (4.0);
* `try`/`catch`/`finally` (§4.20);
* direct constructors (§4.12.1): elements with attributes, namespace
  declaration attributes, enclosed expressions, CDATA sections, entity
  and character references, boundary whitespace (§4.12.1.4); comments
  and processing instructions;
* computed constructors (§4.12.3): `element`, `attribute`, `text`,
  `comment`, `processing-instruction`, `document`, `namespace`;
* `ordered`/`unordered` (no effect), extension expressions `(# #)`,
  string constructors ``` ``[ … `{ }` … ]`` ```;
* `validate` is parsed and raises `XQST0075` (no schema support).
-/
import L4Factoidal.XQuery4.Runtime

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

/-- The prolog settings the expression grammar needs. -/
structure Cfg where
  boundaryPreserve : Bool := false
  /-- Named item types of the prolog. -/
  types : List (QN × IType) := []
  /-- The first pass over a prolog: unknown type names are `item()`. -/
  lenient : Bool := false
  /-- `declare copy-namespaces` (§5.8): preserve, inherit. -/
  copyPreserve : Bool := true
  copyInherit : Bool := true
deriving Inhabited

/-! ## Helpers -/

def subE {α} (f : List (String × String) → Nat → Except Err (α × Nat)) : P α := do
  let c ← read
  let i ← get
  match f c.ns i with
  | .ok (a, j) => set j; pure a
  | .error e => throw e

def curCh : P Char := peekAt 0

def isWsCh (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- A lexical QName exactly at offset `i` (no whitespace): prefix (or
    ""), local, end. -/
def qnameAt (s : Array Char) (i : Nat) : Option (String × String × Nat) :=
  match ncnameAt s i with
  | none => none
  | some (n, e) =>
    if chAt s e == ':' then
      match ncnameAt s (e + 1) with
      | some (l, e2) => some (n, l, e2)
      | none => none
    else some ("", n, e)

/-- XML character (XML 1.0 production [2]). -/
def isXmlChar (n : Nat) : Bool :=
  n == 0x9 || n == 0xA || n == 0xD || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) ||
  (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- Read an entity or character reference at `i` (which is `&`):
    the character and the end offset. -/
def refAt (s : Array Char) (i : Nat) : Except Err (Char × Nat) := do
  let close (j : Nat) : Nat := Id.run do
    let mut k := j
    for _ in [0:12] do
      if chAt s k == ';' || k ≥ s.size then break
      k := k + 1
    k
  let j := close (i + 1)
  if chAt s j != ';' then throw { code := "XPST0003", msg := "unterminated reference" }
  let body := String.ofList ((List.range (j - i - 1)).map (fun k => chAt s (i + 1 + k)))
  let ch : Option Char := match body with
    | "lt" => some '<' | "gt" => some '>' | "amp" => some '&' | "quot" => some '"' | "apos" => some '\''
    | _ => none
  match ch with
  | some c => pure (c, j + 1)
  | none =>
    if body.startsWith "#x" then
      let ds := (body.drop 2).toString.toList
      if ds.isEmpty || !ds.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) then
        throw { code := "XPST0003", msg := "bad character reference &" ++ body ++ ";" }
      let v := ds.foldl (fun a c => a * 16 + hexVal c) 0
      if !isXmlChar v then throw { code := "XQST0090", msg := "character reference to a non-XML character" }
      pure (Char.ofNat v, j + 1)
    else if body.startsWith "#" then
      let ds := (body.drop 1).toString.toList
      if ds.isEmpty || !ds.all Char.isDigit then
        throw { code := "XPST0003", msg := "bad character reference &" ++ body ++ ";" }
      let v := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      if !isXmlChar v then throw { code := "XQST0090", msg := "character reference to a non-XML character" }
      pure (Char.ofNat v, j + 1)
    else throw { code := "XPST0003", msg := "unknown entity &" ++ body ++ ";" }

/-- XQuery string literals: entity and character references expanded
    (§4.2.1, production [233] StringLiteral). -/
def expandRefs (t : String) : Except Err String := do
  if !t.contains '&' then return t
  let s := t.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  for _ in [0:s.size + 1] do
    if i ≥ s.size then break
    let c := chAt s i
    if c == '&' then
      let (ch, j) ← refAt s i
      out := out.push ch; i := j
    else out := out.push c; i := i + 1
  pure (String.ofList out.toList)

/-! ## FLWOR -/

/-- One FLWOR clause as parsed. -/
inductive Clause where
  | forI (kind : String) (v : QN) (vt : IType) (pos : QN) (allowing : Bool) (src : Expr)
  | forKV (k v pos : QN) (src : Expr)
  | letC (v : QN) (vt : IType) (e : Expr)
  | whereC (e : Expr)
  | whileC (e : Expr)
  | countC (v : QN)
  | orderC (keys : List Expr) (specs : List String)
  | groupC (keys : List Expr) (vs : List QN)
  | window (sliding : Bool) (v : QN) (vt : IType) (src : Expr) (s : List QN) (sc : Expr)
      (e : List QN) (ec : Option Expr) (only : Bool)
deriving Inhabited

/-- Can the clause be written as XPath `for`/`let`/`if`? -/
def Clause.simple : Clause → Bool
  | .forI _ _ _ _ allowing _ => !allowing
  | .forKV .. | .letC .. | .whereC .. => true
  | _ => false

/-- A FLWOR of simple clauses as nested XPath 4.0 expressions: `for`
    is `Expr.forE`, `let` is `Expr.letE`, `where` is `Expr.ifE` with
    the empty sequence in the else branch (§4.13.2, §4.13.3, §4.13.5). -/
def flworToXPath : List Clause → Expr → Expr
  | [], ret => ret
  | .forI kind v vt pos _ src :: cs, ret =>
      .forE (if kind == "member" then .member else .item) v none
        (if isNoName pos then none else some pos) vt src (flworToXPath cs ret)
  | .forKV k v pos src :: cs, ret =>
      .forE .entry (if isNoName k then { uri := "#none", loc := "#key" } else k)
        (if isNoName v then none else some v)
        (if isNoName pos then none else some pos) (.seq .item .star) src (flworToXPath cs ret)
  | .letC v vt e :: cs, ret => .letE v vt e (flworToXPath cs ret)
  | .whereC c :: cs, ret => .ifE c (flworToXPath cs ret) (.seq [])
  | _ :: cs, ret => flworToXPath cs ret

def Clause.toExt : Clause → Expr
  | .forI kind v vt pos allowing src => .ext "c:for" [src] [vt] [v, pos] [kind, if allowing then "1" else "0"]
  | .forKV k v pos src => .ext "c:forkv" [src] [] [k, v, pos] []
  | .letC v vt e => .ext "c:let" [e] [vt] [v] []
  | .whereC e => .ext "c:where" [e] [] [] []
  | .whileC e => .ext "c:while" [e] [] [] []
  | .countC v => .ext "c:count" [] [] [v] []
  | .orderC ks sp => .ext "c:order" ks [] [] sp
  | .groupC ks vs => .ext "c:group" ks [] vs []
  | .window sl v vt src s sc e ec only =>
      .ext "c:window" (src :: sc :: ec.toList) [vt] (v :: s ++ e) [if sl then "sliding" else "tumbling", if only then "1" else "0"]

/-- The FLWOR expression of the clauses and the return expression. -/
def mkFlwor (cs : List Clause) (ret : Expr) : Expr :=
  if cs.all Clause.simple then flworToXPath cs ret
  else .ext "flwor" (cs.map Clause.toExt ++ [ret]) [] [] []

def pVar : P QN := do
  expectS "$"
  match ← peekQName with
  | some (p, u, l, e) => set e; resolve p u l ""
  | none => synErr "expected a variable name"

def pOptType (sp : SubParsers) : P IType := do
  if ← eatKw "as" then subE sp.seqType else pure (.seq .item .star)

/-- Is the next keyword `k` followed (after whitespace) by character
    `c`? -/
def kwThen (k : String) (c : Char) : P Bool := do
  match ← afterName with
  | some (n, c1, _) => pure (n == k && c1 == c)
  | none => pure false

def kwThenKw (k k2 : String) : P Bool := do
  ws
  let c ← read
  let i ← get
  match ncnameAt c.s i with
  | some (n, e) =>
    if n != k then pure false else
    let j := skipWsF c.s (c.s.size + 1) 0 e
    match ncnameAt c.s j with
    | some (n2, _) => pure (n2 == k2)
    | none => pure false
  | none => pure false

def isFlworStart : P Bool := do
  if ← kwThen "for" '$' then return true
  if ← kwThen "let" '$' then return true
  for k2 in ["member", "key", "value", "tumbling", "sliding"] do
    if ← kwThenKw "for" k2 then return true
  pure false

def pForBinding (sp : SubParsers) : P Clause := do
  if ← eatKw "member" then
    let v ← pVar
    let vt ← pOptType sp
    let pos ← if ← eatKw "at" then pVar else pure noName
    expectKw "in"
    pure (.forI "member" v vt pos false (← subE sp.exprSingle))
  else if ← atKw "key" then
    adv 3
    let k ← pVar
    let _ ← pOptType sp
    let v ← if ← eatKw "value" then pVar else pure noName
    let _ ← if isNoName v then pure (.seq .item .star) else pOptType sp
    let pos ← if ← eatKw "at" then pVar else pure noName
    expectKw "in"
    pure (.forKV k v pos (← subE sp.exprSingle))
  else if ← atKw "value" then
    adv 5
    let v ← pVar
    let _ ← pOptType sp
    let pos ← if ← eatKw "at" then pVar else pure noName
    expectKw "in"
    pure (.forKV noName v pos (← subE sp.exprSingle))
  else
    let v ← pVar
    let vt ← pOptType sp
    let allowing ← if ← eatKw "allowing" then expectKw "empty"; pure true else pure false
    let pos ← if ← eatKw "at" then pVar else pure noName
    if ← eatKw "score" then synErr "full-text score variables are not supported"
    expectKw "in"
    pure (.forI "item" v vt pos allowing (← subE sp.exprSingle))

/-- A window start or end condition's variables: current, `at`,
    `previous`, `next`. -/
def pWindowVars : P (List QN) := do
  let cur ← if (← curChWs) == '$' then pVar else pure noName
  let p ← if ← eatKw "at" then pVar else pure noName
  let pr ← if ← eatKw "previous" then pVar else pure noName
  let nx ← if ← eatKw "next" then pVar else pure noName
  pure [cur, p, pr, nx]
where
  curChWs : P Char := do ws; peekAt 0

def pWindow (sp : SubParsers) : P Clause := do
  let sliding ← eatKw "sliding"
  if !sliding then expectKw "tumbling"
  expectKw "window"
  let v ← pVar
  let vt ← pOptType sp
  expectKw "in"
  let src ← subE sp.exprSingle
  -- 4.0: the start condition, and the `when` parts, may be absent (true)
  let tru : Expr := .lit (Atomic.ofBool true)
  let (s, sc) ← if ← eatKw "start" then
      let s ← pWindowVars
      let sc ← if ← eatKw "when" then subE sp.exprSingle else pure tru
      pure (s, sc)
    else pure ([noName, noName, noName, noName], tru)
  let only ← eatKw "only"
  if only || (← atKw "end") then
    expectKw "end"
    let e ← pWindowVars
    let ec ← if ← eatKw "when" then subE sp.exprSingle else pure tru
    let names := (v :: s ++ e).filter (fun q => !isNoName q)
    if names.length != names.eraseDups.length then
      throw { code := "XQST0103", msg := "two window variables with one name" }
    pure (.window sliding v vt src s sc e (some ec) only)
  else
    if sliding then synErr "a sliding window needs an end condition"
    let names := (v :: s).filter (fun q => !isNoName q)
    if names.length != names.eraseDups.length then
      throw { code := "XQST0103", msg := "two window variables with one name" }
    pure (.window sliding v vt src s sc [noName, noName, noName, noName] none false)

def pFlwor (sp : SubParsers) : P Expr := do
  let mut cs : Array Clause := #[]
  let mut ret : Option Expr := none
  for _ in [0:100000] do
    if ← eatKw "for" then
      if (← atKw "tumbling") || (← atKw "sliding") then
        cs := cs.push (← pWindow sp)
      else
        for _ in [0:10000] do
          cs := cs.push (← pForBinding sp)
          if !(← eatS ",") then break
    else if ← eatKw "let" then
      for _ in [0:10000] do
        ws
        let c ← read
        let j ← get
        let open_ := chAt c.s (j+1)
        if chAt c.s j == '$' && (open_ == '(' || open_ == '[' || open_ == '{') then
          -- destructuring (XPath 4.0 §4.12.2), as the XPath parser
          -- desugars it: a fresh variable, then one binding per name
          set (j + 2)
          let close := if open_ == '(' then ")" else if open_ == '[' then "]" else "}"
          let mut vs : Array (QN × IType) := #[]
          for _ in [0:1000] do
            let v ← pVar
            let vt ← pOptType sp
            vs := vs.push (v, vt)
            if !(← eatS ",") then break
          expectS close
          let dflt : IType := if open_ == '(' then .seq .item .star else if open_ == '[' then .anyArr else .anyMap
          let st ← if ← atKw "as" then pOptType sp else pure dflt
          expectS ":="
          let e ← subE sp.exprSingle
          let tmp : QN := { uri := "#let", loc := toString j }
          cs := cs.push (.letC tmp st e)
          let k := vs.size
          for ((v, vt), idx) in vs.toList.zip (List.range k) do
            let pos : Expr := .lit (Atomic.ofInt (idx + 1))
            let rhs : Expr :=
              if open_ == '(' then
                if idx + 1 == k then .call { uri := nsFN, loc := "subsequence" } [some (.var tmp), some pos] []
                else .call { uri := nsFN, loc := "items-at" } [some (.var tmp), some pos] []
              else if open_ == '[' then .call { uri := nsARR, loc := "get" } [some (.var tmp), some pos] []
              else .lookup (.var tmp) (some (.lit (Atomic.ofStr v.loc)))
            cs := cs.push (.letC v vt rhs)
        else
          let v ← pVar
          let vt ← pOptType sp
          expectS ":="
          cs := cs.push (.letC v vt (← subE sp.exprSingle))
        if !(← eatS ",") then break
    else if ← eatKw "where" then cs := cs.push (.whereC (← subE sp.exprSingle))
    else if ← atKw "while" then
      expectKw "while"
      cs := cs.push (.whileC (← subE sp.exprSingle))
    else if ← kwThen "count" '$' then
      expectKw "count"
      cs := cs.push (.countC (← pVar))
    else if (← kwThenKw "order" "by") || (← kwThenKw "stable" "order") then
      let _ ← eatKw "stable"
      expectKw "order"; expectKw "by"
      let mut keys : Array Expr := #[]
      let mut specs : Array String := #[]
      for _ in [0:10000] do
        keys := keys.push (← subE sp.exprSingle)
        let desc ← if ← eatKw "descending" then pure true else
          let _ ← eatKw "ascending"; pure false
        let emp ← if ← eatKw "empty" then
            if ← eatKw "greatest" then pure "g" else expectKw "least"; pure "l"
          else pure "?"
        if ← eatKw "collation" then
          let _ ← pStringLit
        specs := specs.push ((if desc then "d" else "a") ++ emp)
        if !(← eatS ",") then break
      -- "?" (no empty modifier) takes the prolog default: the runtime reads specs[0]
      cs := cs.push (.orderC keys.toList ("l" :: specs.toList.map (fun s => if s.endsWith "?" then (s.dropEnd 1).toString else s)))
    else if ← kwThenKw "group" "by" then
      expectKw "group"; expectKw "by"
      let mut keys : Array Expr := #[]
      let mut vs : Array QN := #[]
      for _ in [0:10000] do
        let v ← pVar
        let vt ← pOptType sp
        let e ← if ← eatS ":=" then
            let x ← subE sp.exprSingle
            pure (Expr.letE v vt x (.var v))
          else pure (.var v)
        if ← eatKw "collation" then
          let _ ← pStringLit
        keys := keys.push e
        vs := vs.push v
        if !(← eatS ",") then break
      cs := cs.push (.groupC keys.toList vs.toList)
    else if ← eatKw "return" then
      ret := some (← subE sp.exprSingle)
      break
    else
      synErr "expected a FLWOR clause or 'return'"
  match ret with
  | some r => pure (mkFlwor cs.toList r)
  | none => synErr "FLWOR expression without 'return'"

/-! ## switch, typeswitch, try -/

def pSwitch (sp : SubParsers) : P Expr := do
  expectKw "switch"
  expectS "("
  let op ← if ← eatS ")" then pure (Expr.lit (Atomic.ofBool true)) else
    let e ← subE sp.expr
    expectS ")"; pure e
  let braced ← eatS "{"
  let mut clauses : Array (List Expr × Expr) := #[]
  for _ in [0:100000] do
    if !(← atKw "case") then break
    let mut cases : Array Expr := #[]
    for _ in [0:10000] do
      if !(← eatKw "case") then break
      cases := cases.push (← subE sp.expr)
    expectKw "return"
    clauses := clauses.push (cases.toList, ← subE sp.exprSingle)
  if clauses.isEmpty then synErr "switch without a case clause"
  expectKw "default"; expectKw "return"
  let d ← subE sp.exprSingle
  if braced then expectS "}"
  pure (.ext "switch" ([op, d] ++ clauses.toList.flatMap (fun (cs, r) => cs ++ [r])) [] []
    (clauses.toList.map (fun (cs, _) => toString cs.length)))

def pTypeswitch (sp : SubParsers) : P Expr := do
  expectKw "typeswitch"
  expectS "("
  let op ← subE sp.expr
  expectS ")"
  let braced ← eatS "{"
  let mut types : Array IType := #[]
  let mut vars : Array QN := #[]
  let mut rets : Array Expr := #[]
  for _ in [0:100000] do
    if !(← eatKw "case") then break
    let v ← if (← peekWs) == '$' then
        let v ← pVar
        expectKw "as"; pure v
      else pure noName
    let mut ts : Array IType := #[← subE sp.seqType]
    for _ in [0:1000] do
      if ← eatS "|" then ts := ts.push (← subE sp.seqType) else break
    expectKw "return"
    types := types.push (if ts.size == 1 then ts[0]! else .choice ts.toList)
    vars := vars.push v
    rets := rets.push (← subE sp.exprSingle)
  if types.isEmpty then synErr "typeswitch without a case clause"
  expectKw "default"
  let dv ← if (← peekWs) == '$' then pVar else pure noName
  expectKw "return"
  let d ← subE sp.exprSingle
  if braced then expectS "}"
  pure (.ext "typeswitch" (op :: rets.toList ++ [d]) types.toList (vars.toList ++ [dv]) [])
where
  peekWs : P Char := do ws; peekAt 0

/-- `{ Expr? }`. -/
def pBraced (sp : SubParsers) : P Expr := do
  expectS "{"
  if ← eatS "}" then pure (.seq []) else
  let e ← subE sp.expr
  expectS "}"
  pure e

/-- A catch clause's name tests, as `Runtime.catchMatches` reads them. -/
def pCatchTest : P String := do
  ws
  let c ← read
  let i ← get
  if chAt c.s i == '*' && chAt c.s (i+1) != ':' then adv 1; pure "*"
  else match ← peekQName with
    | some (p, u, l, e) =>
      set e
      if p == some "*" then pure ("*:" ++ l)
      else
        let uri ← match u with
          | some uu => pure uu
          | none => match p with
            | some pp => lookupNs pp
            | none => pure ((c.ns.lookup "").getD "")
        pure ("Q{" ++ uri ++ "}" ++ l)
    | none => synErr "expected a catch name test"

def pTry (sp : SubParsers) : P Expr := do
  expectKw "try"
  let body ← pBraced sp
  let mut tests : Array String := #[]
  let mut hs : Array Expr := #[]
  for _ in [0:10000] do
    if !(← eatKw "catch") then break
    let mut ts : Array String := #[← pCatchTest]
    for _ in [0:1000] do
      if ← eatS "|" then ts := ts.push (← pCatchTest) else break
    tests := tests.push (String.intercalate "|" ts.toList)
    hs := hs.push (← pBraced sp)
  let fin ← if ← kwThen "finally" '{' then expectKw "finally"; pure (some (← pBraced sp)) else pure none
  if tests.isEmpty && fin.isNone then synErr "try without catch"
  pure (.ext "try" (body :: hs.toList ++ fin.toList) [] []
    (tests.toList ++ (if fin.isSome then ["#finally"] else [])))

/-! ## Direct constructors -/

/-- Mark a constructor with its offset in the query text, so that two
    constructors with equal content give nodes of different identity. -/
def tagAt (i : Nat) : Expr → Expr
  | .ext tag es ts qs ss =>
    if ["elem", "attr", "text", "comment", "pi", "doc", "ns"].contains tag then
      .ext tag es ts qs (ss ++ ["#at" ++ toString i])
    else .ext tag es ts qs ss
  | e => e



/-- The static namespace bindings, for computed names at run time. -/
def staticNs : P (List QN) := do
  let c ← read
  pure (c.ns.map (fun (p, u) => nsBinding p u))

def readUntil (s : Array Char) (i : Nat) (stop : String) : Option (String × Nat) := Id.run do
  let st := stop.toList
  let mut j := i
  for _ in [0:s.size + 1] do
    if j ≥ s.size then return none
    if (List.range st.length).all (fun k => chAt s (j + k) == st.getD k ' ') then
      return some (String.ofList ((List.range (j - i)).map (fun k => chAt s (i + k))), j + st.length)
    j := j + 1
  none

/-- A direct comment `<!-- … -->` at `<`. -/
def pDirComment : P Expr := do
  let c ← read
  let i ← get
  match readUntil c.s (i + 4) "-->" with
  | some (t, e) =>
    if (t.splitOn "--").length > 1 || t.endsWith "-" then synErr "'--' in a direct comment"
    set e
    pure (.ext "comment" [.lit (Atomic.ofStr t)] [] [] [])
  | none => synErr "unterminated comment"

/-- A direct processing instruction `<?target content?>` at `<`. -/
def pDirPI : P Expr := do
  let c ← read
  let i ← get
  match ncnameAt c.s (i + 2) with
  | some (t, e) =>
    if t.toLower == "xml" then synErr "processing instruction target xml"
    if chAt c.s e != '?' && !isWsCh (chAt c.s e) then synErr "bad processing instruction"
    match readUntil c.s e "?>" with
    | some (body, e2) =>
      set e2
      let body := String.ofList (body.toList.dropWhile isWsCh)
      pure (.ext "pi" [.lit (Atomic.ofStr t), .lit (Atomic.ofStr body)] [] [] [])
    | none => synErr "unterminated processing instruction"
  | none => synErr "bad processing instruction target"

/-- Normalise attribute value whitespace (§4.12.1.1): tab, newline and
    carriage return in literal text become spaces. -/
def normAttrCh (c : Char) : Char := if c == '\t' || c == '\n' || c == '\r' then ' ' else c

/-- A direct attribute value in quotes `q` at offset `i` (after the
    quote): its parts, literal strings and enclosed expressions. -/
def pAttrValue (sp : SubParsers) (q : Char) : P (List Expr × Bool) := do
  let c ← read
  let mut parts : Array Expr := #[]
  let mut buf : Array Char := #[]
  let mut literal := true
  for _ in [0:c.s.size + 1] do
    let i ← get
    if i ≥ c.s.size then synErr "unterminated attribute value"
    let ch := chAt c.s i
    if ch == q then
      if chAt c.s (i+1) == q then buf := buf.push q; adv 2
      else adv 1; break
    else if ch == '{' && chAt c.s (i+1) == '{' then buf := buf.push '{'; adv 2
    else if ch == '}' && chAt c.s (i+1) == '}' then buf := buf.push '}'; adv 2
    else if ch == '}' then synErr "unescaped '}' in an attribute value"
    else if ch == '<' then synErr "'<' in an attribute value"
    else if ch == '{' then
      if !buf.isEmpty then parts := parts.push (.lit (Atomic.ofStr (String.ofList buf.toList)))
      buf := #[]
      literal := false
      adv 1
      ws
      if (← curCh) == '}' then adv 1
      else
        let e ← subE sp.expr
        expectS "}"
        parts := parts.push e
    else if ch == '&' then
      match refAt c.s i with
      | .ok (r, j) => buf := buf.push r; set j
      | .error e => throw e
    else buf := buf.push (normAttrCh ch); adv 1
  if !buf.isEmpty then parts := parts.push (.lit (Atomic.ofStr (String.ofList buf.toList)))
  pure (parts.toList, literal)

/-- The literal string of an attribute value with no enclosed expression. -/
def litString (ps : List Expr) : String :=
  String.join (ps.map (fun p => match p with | .lit a => a.str | _ => ""))

/-- A piece of direct element content while it is read. -/
inductive CPiece where
  /-- Literal characters; `keep` when the run has a reference or CDATA
      (boundary whitespace is then not stripped). -/
  | chars (s : String) (keep : Bool)
  | expr (e : Expr)
  /-- A nested constructor or an enclosed expression (a boundary). -/
  | bound (e : Expr)

/-- Boundary whitespace (§4.12.1.4): a run of whitespace characters
    between two boundaries is removed unless preserved. -/
def contentExprs (cfg : Cfg) (ps : List CPiece) : List Expr :=
  ps.filterMap (fun p => match p with
    | .chars s keep =>
      if !cfg.boundaryPreserve && !keep && s.all isWsCh then none
      else some (.lit (Atomic.ofStr s))
    | .expr e => some e
    | .bound e => some e)

/-- Skip a quoted attribute value at `i` (after the quote), with the
    enclosed expressions in it (brace depth, string literals). Returns
    the raw text when it has no enclosed expression, and the end. -/
def skipAttrValue (s : Array Char) (q : Char) (i : Nat) : Option String × Nat := Id.run do
  let mut j := i
  let mut depth := 0
  let mut lit := true
  let mut buf : Array Char := #[]
  for _ in [0:s.size + 1] do
    if j ≥ s.size then break
    let ch := chAt s j
    if depth == 0 then
      if ch == q then
        if chAt s (j+1) == q then buf := buf.push q; j := j + 2; continue
        j := j + 1; break
      if ch == '{' && chAt s (j+1) == '{' then buf := buf.push '{'; j := j + 2; continue
      if ch == '}' && chAt s (j+1) == '}' then buf := buf.push '}'; j := j + 2; continue
      if ch == '{' then depth := 1; lit := false; j := j + 1; continue
      buf := buf.push ch; j := j + 1
    else
      if ch == '{' then depth := depth + 1; j := j + 1
      else if ch == '}' then depth := depth - 1; j := j + 1
      else if ch == '"' || ch == '\'' then
        let mut k := j + 1
        for _ in [0:s.size + 1] do
          if k ≥ s.size then break
          if chAt s k == ch then
            if chAt s (k+1) == ch then k := k + 2 else break
          else k := k + 1
        j := k + 1
      else j := j + 1
  (if lit then some (String.ofList buf.toList) else none, j)

/-- The namespace declaration attributes of a start tag, read ahead
    (they are in scope for every attribute of the tag, §4.12.1.2). -/
def scanDecls (s : Array Char) (i : Nat) : List (String × String) := Id.run do
  let mut j := i
  let mut out : List (String × String) := []
  for _ in [0:s.size + 1] do
    let k := skipWsF s (s.size + 1) 0 j
    let ch := chAt s k
    if ch == '/' || ch == '>' || k ≥ s.size then break
    let some (ap, al, ae) := qnameAt s k | break
    let k2 := skipWsF s (s.size + 1) 0 ae
    if chAt s k2 != '=' then break
    let k3 := skipWsF s (s.size + 1) 0 (k2 + 1)
    let q := chAt s k3
    if q != '"' && q != '\'' then break
    let (lit, e) := skipAttrValue s q (k3 + 1)
    if (ap == "" && al == "xmlns") || ap == "xmlns" then
      match lit with
      | some v =>
        let v := (expandRefs v).toOption.getD v
        out := out ++ [(if ap == "" then "" else al, v)]
      | none => pure ()
    j := e
  out

/-- The attributes of a start tag (after the name, up to `/` or `>`):
    namespace declarations and the other attributes. -/
def pStartTag (sp : SubParsers) : P (List (String × String) × Array (String × String × List Expr × Bool)) := do
  let c ← read
  let mut decls : List (String × String) := []
  let mut ats : Array (String × String × List Expr × Bool) := #[]
  for _ in [0:100000] do
    let j ← get
    let k := skipWsF c.s (c.s.size + 1) 0 j
    let ch := chAt c.s k
    if ch == '/' || ch == '>' then set k; break
    if k == j then synErr "expected whitespace before an attribute"
    let some (ap, al, ae) := qnameAt c.s k | synErr "bad attribute name"
    set ae
    ws; expectS "="; ws
    let q := chAt c.s (← get)
    if q != '"' && q != '\'' then synErr "expected a quoted attribute value"
    adv 1
    let (parts, literal) ← pAttrValue sp q
    if (ap == "" && al == "xmlns") || ap == "xmlns" then
      if !literal then throw { code := "XQST0022", msg := "a namespace declaration with an enclosed expression" }
      let uri := litString parts
      let p := if ap == "" then "" else al
      if p == "xml" && uri != nsXML then throw { code := "XQST0070", msg := "the xml prefix rebound" }
      if p == "xmlns" then throw { code := "XQST0070", msg := "the xmlns prefix declared" }
      if uri == nsXML && p != "xml" then throw { code := "XQST0070", msg := "the xml namespace bound to another prefix" }
      if uri == "http://www.w3.org/2000/xmlns/" then throw { code := "XQST0070", msg := "the xmlns namespace declared" }
      if decls.any (·.1 == p) then throw { code := "XQST0071", msg := "duplicate namespace declaration" }
      decls := decls ++ [(p, uri)]
    else
      ats := ats.push (ap, al, parts, literal)
  pure (decls, ats)

/-- The copy-namespaces mode, as strings in an `elem` node. -/
def copyFlags (cfg : Cfg) : List String :=
  (if cfg.copyPreserve then [] else ["#no-preserve"]) ++ (if cfg.copyInherit then [] else ["#no-inherit"])

def pDirElem (cfg : Cfg) (sp : SubParsers) : Nat → P Expr
  | 0 => synErr "direct constructors nested too deeply"
  | f + 1 => do
    let c ← read
    let i ← get
    -- at '<'
    let some (pfx, loc, e) := qnameAt c.s (i + 1) | synErr "bad element name"
    set e
    let pre := scanDecls c.s e
    let nsA := pre ++ c.ns.filter (fun (p, _) => !pre.any (·.1 == p))
    let (decls, ats) ← withReader (fun c => { c with ns := nsA }) (pStartTag sp)
    let outer := c.ns
    let ns' := decls ++ outer.filter (fun (p, _) => !decls.any (·.1 == p))
    withReader (fun c => { c with ns := ns' }) do
      let resolveP (p : String) : P String :=
        if p == "xml" then pure nsXML else lookupNs p
      let uri ← if pfx == "" then pure ((ns'.lookup "").getD "") else resolveP pfx
      let name : QN := { uri, loc, pfx }
      let sns ← staticNs
      let mut attrEs : Array Expr := #[]
      let mut seen : List (String × String) := []
      for (ap, al, parts, _) in ats do
        let auri ← if ap == "" then pure "" else resolveP ap
        if seen.contains (auri, al) then throw { code := "XQST0040", msg := "duplicate attribute " ++ al }
        seen := (auri, al) :: seen
        attrEs := attrEs.push (.ext "attr" (.lit (Atomic.ofQN { uri := auri, loc := al, pfx := ap }) :: parts) [] sns ["d"])
      let declStrs := decls.map (fun (p, u) => p ++ "\x00" ++ u) ++ copyFlags cfg
      let s := c.s
      if chAt s (← get) == '/' then
        adv 1; expectS ">"
        return .ext "elem" (.lit (Atomic.ofQN name) :: attrEs.toList) [] sns ("d" :: declStrs)
      adv 1  -- '>'
      -- content
      let mut ps : Array CPiece := #[]
      let mut buf : Array Char := #[]
      let mut keep := false
      for _ in [0:s.size + 1] do
        let j ← get
        if j ≥ s.size then synErr "unterminated element constructor"
        let ch := chAt s j
        let flush (ps : Array CPiece) (buf : Array Char) (keep : Bool) : Array CPiece :=
          if buf.isEmpty then ps else ps.push (.chars (String.ofList buf.toList) keep)
        if ch == '<' then
          if chAt s (j+1) == '/' then
            ps := flush ps buf keep; buf := #[]
            let some (ep, el, ee) := qnameAt s (j + 2) | synErr "bad end tag"
            if ep != pfx || el != loc then synErr ("end tag </" ++ (if ep == "" then el else ep ++ ":" ++ el) ++ "> does not match")
            set ee; ws; expectS ">"
            break
          else if chAt s (j+1) == '!' && chAt s (j+2) == '[' then
            -- CDATA section
            match readUntil s (j + 9) "]]>" with
            | some (t, e2) =>
              if String.ofList ((List.range 9).map (fun k => chAt s (j + k))) != "<![CDATA[" then synErr "bad CDATA section"
              buf := buf ++ t.toList.toArray; keep := true; set e2
            | none => synErr "unterminated CDATA section"
          else
            ps := flush ps buf keep; buf := #[]; keep := false
            let e ← if chAt s (j+1) == '!' then pDirComment
              else if chAt s (j+1) == '?' then pDirPI
              else pDirElem cfg sp f
            ps := ps.push (.bound (tagAt j e))
        else if ch == '{' && chAt s (j+1) == '{' then buf := buf.push '{'; adv 2
        else if ch == '}' && chAt s (j+1) == '}' then buf := buf.push '}'; adv 2
        else if ch == '}' then synErr "unescaped '}' in element content"
        else if ch == '{' then
          ps := flush ps buf keep; buf := #[]; keep := false
          adv 1
          ws
          if (← curCh) == '}' then
            adv 1
            ps := ps.push (.bound (.seq []))
          else
            let e ← subE sp.expr
            expectS "}"
            ps := ps.push (.bound e)
        else if ch == '&' then
          match refAt s j with
          | .ok (r, e2) => buf := buf.push r; keep := true; set e2
          | .error er => throw er
        else
          -- line endings are normalised to a newline (XML 1.0 §2.11)
          if ch == '\r' then
            buf := buf.push '\n'
            adv (if chAt s (j+1) == '\n' then 2 else 1)
          else buf := buf.push ch; adv 1
      let kids := contentExprs cfg ps.toList
      pure (.ext "elem" (.lit (Atomic.ofQN name) :: attrEs.toList ++ kids) [] sns ("d" :: declStrs))

/-! ## Computed constructors and other primaries -/

/-- `element`/`attribute`/`processing-instruction`/`namespace`: a name
    (static, `{ expr }`, or 4.0 string literal) then the content. -/
def pCompName (sp : SubParsers) (kind : String) : P Expr := do
  ws
  if (← curCh) == '{' then pBraced sp
  else
  -- 4.0: a QName literal `#name` (white space may follow the `#`)
  if (← curCh) == '#' then adv 1; ws
  match ← peekQName with
    | some (p, u, l, e) =>
      set e
      if kind == "pi" || kind == "ns" then
        if p.isSome || u.isSome then synErr "an NCName is required here"
        pure (.lit (Atomic.ofStr l))
      else
        let c ← read
        let dflt := if kind == "attr" then "" else (c.ns.lookup "").getD ""
        let q ← match p, u with
          | some "xml", none => pure { uri := nsXML, loc := l, pfx := "xml" }
          | some "xmlns", none => pure { uri := "http://www.w3.org/2000/xmlns/", loc := l, pfx := "xmlns" }
          | _, _ => resolve p u l dflt
        pure (.lit (Atomic.ofQN q))
    | none => synErr "expected a constructor name"

/-- The names that start a computed constructor (or another XQuery
    primary) where the XPath step grammar would read a name test. -/
def compKeywords : List String :=
  ["element", "attribute", "text", "comment", "document", "processing-instruction", "namespace",
   "ordered", "unordered", "validate"]

/-- Does a computed constructor start at `i`? -/
def startsComputed (s : Array Char) (i : Nat) : Bool :=
  match ncnameAt s i with
  | some (n, e) =>
    if !compKeywords.contains n then false else
    if chAt s e == ':' && isNameStart (chAt s (e+1)) then false else
    if chAt s e == ':' && chAt s (e+1) == ':' then false else
    let j := skipWsF s (s.size + 1) 0 e
    let c := chAt s j
    if c == '{' then
      -- `ordered {`, `text {`, `element {` ...; not the map/array forms
      true
    else if n == "validate" then
      match ncnameAt s j with
      | some (m, _) => m == "lax" || m == "strict" || m == "as" || m == "type"
      | none => false
    else if n == "element" || n == "attribute" || n == "processing-instruction" || n == "namespace" then
      -- a name (or a QName literal `#name`) then '{'
      let j := if c == '#' then skipWsF s (s.size + 1) 0 (j + 1) else j
      let c := chAt s j
      match qnameAt s j with
      | some (_, _, e2) => chAt s (skipWsF s (s.size + 1) 0 e2) == '{'
      | none =>
        -- Q{uri}local
        if c == 'Q' && chAt s (j+1) == '{' then true else false
    else false
  | none => false

def pStringConstructor (sp : SubParsers) : P Expr := do
  -- at "``["
  adv 3
  let c ← read
  let s := c.s
  let mut parts : Array Expr := #[]
  let mut buf : Array Char := #[]
  for _ in [0:s.size + 1] do
    let j ← get
    if j ≥ s.size then synErr "unterminated string constructor"
    if chAt s j == ']' && chAt s (j+1) == '`' && chAt s (j+2) == '`' then adv 3; break
    if chAt s j == '`' && chAt s (j+1) == '{' then
      if !buf.isEmpty then parts := parts.push (.lit (Atomic.ofStr (String.ofList buf.toList)))
      buf := #[]
      adv 2
      ws
      if (← curCh) == '}' && (← peekAt 1) == '`' then adv 2
      else
        let e ← subE sp.expr
        ws
        expectS "}`"
        parts := parts.push (.call { uri := "#tmpl", loc := "#tmpl" } [some e] [])
    else buf := buf.push (chAt s j); adv 1
  if !buf.isEmpty then parts := parts.push (.lit (Atomic.ofStr (String.ofList buf.toList)))
  pure (.tmpl parts.toList)

def pExtensionExpr (sp : SubParsers) : P Expr := do
  -- one or more (# QName contents #)
  for _ in [0:1000] do
    ws
    if !((← curCh) == '(' && (← peekAt 1) == '#') then break
    adv 2
    let c ← read
    let i ← get
    let j := skipWsF c.s (c.s.size + 1) 0 i
    let some (p, _, _) := qnameAt c.s j | synErr "bad pragma name"
    if p != "" then
      let _ ← lookupNs p
    else if !(c.s.getD j ' ' == 'Q') then
      throw { code := "XPST0081", msg := "a pragma name needs a namespace" }
    match readUntil c.s j "#)" with
    | some (_, e) => set e
    | none => synErr "unterminated pragma"
  ws
  if (← curCh) != '{' then synErr "extension expression without braces"
  adv 1
  ws
  if (← curCh) == '}' then
    adv 1
    pure (.ext "error" [] [] [] ["XQST0079", "an extension expression with no expression"])
  else
    let e ← subE sp.expr
    expectS "}"
    pure e

def primaryP (cfg : Cfg) (sp : SubParsers) : P (Option Expr) := do
  ws
  let i0 ← get
  match ← primaryP0 cfg sp with
  | some e => pure (some (tagAt i0 e))
  | none => pure none
where
  primaryP0 (cfg : Cfg) (sp : SubParsers) : P (Option Expr) := do
  let c ← read
  let i ← get
  let s := c.s
  let ch := chAt s i
  if ch == '<' then
    let ch1 := chAt s (i+1)
    if ch1 == '!' && chAt s (i+2) == '-' && chAt s (i+3) == '-' then return some (← pDirComment)
    if ch1 == '?' then return some (← pDirPI)
    if isNameStart ch1 then return some (← pDirElem cfg sp 10000)
    return none
  if ch == '`' && chAt s (i+1) == '`' && chAt s (i+2) == '[' then return some (← pStringConstructor sp)
  if ch == '(' && chAt s (i+1) == '#' then return some (← pExtensionExpr sp)
  if ch == '%' then
    -- annotations on an inline function (ignored), then the function
    for _ in [0:100] do
      ws
      if (← curCh) != '%' then break
      adv 1
      match ← peekQName with
      | some (p, _, _, e) =>
        if let some pp := p then let _ ← lookupNs pp
        set e
      | none => synErr "bad annotation"
      if ← eatS "(" then
        for _ in [0:100] do
          ws
          let c2 ← curCh
          if c2 == '"' || c2 == '\'' then let _ ← pStringLit
          else if c2 == '-' || c2.isDigit || c2 == '.' then
            let _ ← eatS "-"
            let _ ← pNumber
          else if (← kwThen "true" '(') || (← kwThen "false" '(') then
            let some (_, e2) := ncnameAt (← read).s (← get) | synErr "bad annotation value"
            set e2; expectS "("; expectS ")"
          else synErr "an annotation value must be a literal"
          if !(← eatS ",") then break
        expectS ")"
    if !((← kwThen "function" '(') || (← kwThen "fn" '(') || (← kwThen "function" '{') || (← kwThen "fn" '{')) then
      synErr "annotations must be followed by a function"
    return some (← subE sp.exprSingle)
  if !startsComputed s i then return none
  let some (kw, _) := ncnameAt s i | return none
  adv kw.length
  let sns ← staticNs
  match kw with
  | "element" =>
    let nm ← pCompName sp "elem"
    let body ← pBraced sp
    pure (some (.ext "elem" [nm, body] [] sns ("c" :: copyFlags cfg)))
  | "attribute" =>
    let nm ← pCompName sp "attr"
    let body ← pBraced sp
    pure (some (.ext "attr" [nm, body] [] sns ["c"]))
  | "processing-instruction" =>
    let nm ← pCompName sp "pi"
    let body ← pBraced sp
    pure (some (.ext "pi" [nm, body] [] [] []))
  | "namespace" =>
    let nm ← pCompName sp "ns"
    let body ← pBraced sp
    pure (some (.ext "ns" [nm, body] [] [] []))
  | "text" => pure (some (.ext "text" [← pBraced sp] [] [] []))
  | "comment" => pure (some (.ext "comment" [← pBraced sp] [] [] []))
  | "document" => pure (some (.ext "doc" [← pBraced sp] [] [] []))
  | "ordered" | "unordered" => pure (some (← pBraced sp))
  | "validate" =>
    if ← eatKw "type" then let _ ← peekQName
    else if ← eatKw "as" then let _ ← peekQName
    else
      let _ ← eatKw "lax"
      let _ ← eatKw "strict"
    -- skip a type name if any, then the braces
    ws
    if (← curCh) != '{' then
      match ← peekQName with
      | some (_, _, _, e) => set e
      | none => pure ()
    let _ ← pBraced sp
    pure (some (.ext "error" [] [] [] ["XQST0075", "validate is not supported (no schema support)"]))
  | _ => pure none

def exprSingleP (sp : SubParsers) : P (Option Expr) := do
  if ← isFlworStart then return some (← pFlwor sp)
  if ← kwThen "switch" '(' then return some (← pSwitch sp)
  if ← kwThen "typeswitch" '(' then return some (← pTypeswitch sp)
  if ← kwThen "try" '{' then return some (← pTry sp)
  pure none

/-! ## The grammar extension -/

def runP {α} (p : P α) (s : Array Char) (ns : List (String × String)) (i : Nat) :
    Except Err (α × Nat) :=
  (p.run { s, ns }).run i

def liftOpt (r : Except Err (Option Expr × Nat)) : Except Err (Option (Expr × Nat)) :=
  match r with
  | .ok (some e, j) => .ok (some (e, j))
  | .ok (none, _) => .ok none
  | .error e => .error e

/-- The XQuery 4.0 grammar extension for the XPath 4.0 parser. -/
def grammar (cfg : Cfg) : ExtGrammar where
  exprSingle s ns sp i := liftOpt (runP (exprSingleP sp) s ns i)
  primary s ns sp i := liftOpt (runP (primaryP cfg sp) s ns i)
  startsPrimary s i := startsComputed s i
  stringLit := expandRefs

/-- Does an XPath 4.0 computed node constructor start at `i`? XPath 4.0
    §4.12 has the computed constructors of XQuery, with a name written
    only as a QName literal `#name` or an enclosed expression
    (CompNodeName and CompNodeNCName without UnreservedName). -/
def startsComputedXPath (s : Array Char) (i : Nat) : Bool :=
  match ncnameAt s i with
  | some (n, e) =>
    if !["element", "attribute", "text", "comment", "document", "processing-instruction", "namespace"].contains n then false
    else if chAt s e == ':' then false
    else
      let j := skipWsF s (s.size + 1) 0 e
      let c := chAt s j
      if c == '{' then true
      else if c == '#' then n == "element" || n == "attribute" || n == "processing-instruction" || n == "namespace"
      else false
  | none => false

/-- The XPath 4.0 profile of the extension: the computed node
    constructors only (XPath 4.0 §4.12); string literals are not
    expanded. -/
def xpathGrammar : ExtGrammar where
  exprSingle _ _ _ _ := .ok none
  primary s ns sp i := if startsComputedXPath s i then liftOpt (runP (primaryP {} sp) s ns i) else .ok none
  startsPrimary s i := startsComputedXPath s i
  stringLit v := .ok v
  xquery := false

end L4Factoidal.XQuery4
