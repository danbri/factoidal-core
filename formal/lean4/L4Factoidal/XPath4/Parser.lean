/-
L4Factoidal.XPath4.Parser — a recursive-descent parser for XPath 4.0
(XPath 4.0 editor's draft, Appendix A; qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c).

Scannerless: the parser reads characters and decides each token in
context, which is how the grammar's lexical rules (§A.3) are stated —
`div` is an operator after an operand and a name test before one, `*`
is multiplication after an operand and a wildcard before one.

Recursion is bounded by an explicit FUEL argument that decreases on
every nested call (no `partial def`); running out of fuel is the
static error `XPST0003` with a message saying so, never a wrong parse.

Implemented: every production of the XPath 4.0 expression grammar
EXCEPT `jnode()` types, destructuring
`let $( )`/`$[ ]`/`${ }` bindings, computed node constructors, the
`declare default element namespace` prolog and schema-element /
schema-attribute types. Those raise `XPST0003` naming the construct.
-/
import L4Factoidal.XPath4.Syntax
import L4Factoidal.XPath4.RecordTypes

namespace L4Factoidal.XPath4

structure PCtx where
  s : Array Char
  /-- Namespace bindings for prefixes (static context). -/
  ns : List (String × String)

abbrev P := ReaderT PCtx (StateT Nat (Except Err))

def defaultNs : List (String × String) :=
  [("xs", nsXS), ("fn", nsFN), ("math", nsMATH), ("map", nsMAP), ("array", nsARR),
   ("err", nsERR), ("xml", nsXML), ("local", "http://www.w3.org/2005/xquery-local-functions"),
   ("xsi", "http://www.w3.org/2001/XMLSchema-instance")]

def synErr {α} (msg : String) : P α := throw { code := "XPST0003", msg }

def chAt (s : Array Char) (i : Nat) : Char := s.getD i '\x00'

def isNameStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || (c.toNat ≥ 0xC0 && c.toNat != 0xD7 && c.toNat != 0xF7 && c.toNat != 0x2212)

def isNameCh (c : Char) : Bool :=
  isNameStart c || c.isDigit || c == '-' || c == '.' || c.toNat == 0xB7

/-- Skip whitespace and (nested) comments `(: … :)`. -/
def skipWsF (s : Array Char) : Nat → Nat → Nat → Nat
  | 0, _, i => i
  | f + 1, depth, i =>
    let c := chAt s i
    if i ≥ s.size then i
    else if c == '(' && chAt s (i+1) == ':' then skipWsF s f (depth + 1) (i + 2)
    else if depth > 0 && c == ':' && chAt s (i+1) == ')' then skipWsF s f (depth - 1) (i + 2)
    else if depth > 0 then skipWsF s f depth (i + 1)
    else if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipWsF s f depth (i + 1)
    else i

def ws : P Unit := do
  let c ← read
  let i ← get
  set (skipWsF c.s (c.s.size + 1) 0 i)

def pos : P Nat := get

def peekAt (k : Nat) : P Char := do
  let c ← read
  let i ← get
  pure (chAt c.s (i + k))

/-- Does the input at the current position (after whitespace) start
    with `t`? -/
def atS (t : String) : P Bool := do
  ws
  let c ← read
  let i ← get
  let cs := t.toList
  pure ((List.range cs.length).all (fun k => chAt c.s (i + k) == cs.getD k ' '))

def adv (n : Nat) : P Unit := modify (· + n)

def eatS (t : String) : P Bool := do
  if ← atS t then adv t.length; pure true else pure false

def expectS (t : String) : P Unit := do
  if ← eatS t then pure () else
    let i ← get
    synErr ("expected '" ++ t ++ "' at offset " ++ toString i)

/-- Read an NCName starting exactly at offset `i`. -/
def ncnameAt (s : Array Char) (i : Nat) : Option (String × Nat) :=
  if !isNameStart (chAt s i) then none
  else
    let rec go (j : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => j
      | f + 1 => if isNameCh (chAt s j) then go (j + 1) f else j
    let j := go (i + 1) s.size
    -- a trailing '.' or '-' is part of the name per XML rules; keep it
    some (String.ofList ((List.range (j - i)).map (fun k => chAt s (i + k))), j)

/-- Peek a lexical QName (or `Q{uri}local`) at the current position.
    Returns `(prefix?, uri?, local, end)`; the local may be `*` for
    `p:*`, the prefix may be `*` for `*:l`. -/
def peekQName : P (Option (Option String × Option String × String × Nat)) := do
  ws
  let c ← read
  let i ← get
  let s := c.s
  if chAt s i == 'Q' && chAt s (i+1) == '{' then
    let rec findClose (j : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => j
      | f + 1 => if j ≥ s.size || chAt s j == '}' then j else findClose (j + 1) f
    let j := findClose (i + 2) s.size
    let uri := String.ofList ((List.range (j - i - 2)).map (fun k => chAt s (i + 2 + k)))
    if chAt s (j+1) == '*' then pure (some (none, some uri, "*", j + 2))
    else match ncnameAt s (j + 1) with
      | some (l, e) => pure (some (none, some uri, l, e))
      | none => pure none
  else if chAt s i == '*' && chAt s (i+1) == ':' then
    match ncnameAt s (i + 2) with
    | some (l, e) => pure (some (some "*", none, l, e))
    | none => pure none
  else
  match ncnameAt s i with
  | none => pure none
  | some (n, e) =>
    if chAt s e == ':' && chAt s (e+1) == '*' && chAt s (e+2) != ':' then pure (some (some n, none, "*", e + 2))
    else if chAt s e == ':' && isNameStart (chAt s (e+1)) then
      match ncnameAt s (e + 1) with
      | some (l, e2) => pure (some (some n, none, l, e2))
      | none => pure (some (none, none, n, e))
    else pure (some (none, none, n, e))

def lookupNs (p : String) : P String := do
  let c ← read
  match c.ns.lookup p with
  | some u => pure u
  | none => match defaultNs.lookup p with
    | some u => pure u
    | none => throw { code := "XPST0081", msg := "undeclared namespace prefix " ++ p }

/-- Resolve a lexical name; `dflt` is the namespace of an unprefixed name. -/
def resolve (pfx : Option String) (uri : Option String) (l : String) (dflt : String) : P QN := do
  match uri with
  | some u => pure { uri := u, loc := l }
  | none => match pfx with
    | some p => pure { uri := ← lookupNs p, loc := l, pfx := p }
    | none => pure { uri := dflt, loc := l }

/-- Is the next non-space text the keyword `k` (followed by a non-name
    character)? -/
def atKw (k : String) : P Bool := do
  ws
  let c ← read
  let i ← get
  match ncnameAt c.s i with
  | some (n, _) => pure (n == k)
  | none => pure false

def eatKw (k : String) : P Bool := do
  if ← atKw k then adv k.length; pure true else pure false

def expectKw (k : String) : P Unit := do
  if ← eatKw k then pure () else synErr ("expected '" ++ k ++ "'")

/-- The character after the next name (skipping whitespace), and
    whether a name is there. -/
def afterName : P (Option (String × Char × Char)) := do
  ws
  let c ← read
  let i ← get
  match ← peekQName with
  | some (_, _, n, e) =>
      let j := skipWsF c.s (c.s.size + 1) 0 e
      set i
      pure (some (n, chAt c.s j, chAt c.s (j+1)))
  | none => set i; pure none

/-! ## Literals -/

def digitsUs (s : Array Char) (i : Nat) (ok : Char → Bool) : List Char × Nat :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : List Char × Nat :=
    match fuel with
    | 0 => (acc.reverse, j)
    | f + 1 =>
      let c := chAt s j
      if ok c then go (j + 1) (c :: acc) f
      else if c == '_' && ok (chAt s (j+1)) && !acc.isEmpty then go (j + 1) acc f
      else (acc.reverse, j)
  go i [] s.size

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
  else c.toNat - 55

def pNumber : P Expr := do
  ws
  let c ← read
  let i ← get
  let s := c.s
  if chAt s i == '0' && (chAt s (i+1) == 'x' || chAt s (i+1) == 'X') then
    let (ds, j) := digitsUs s (i + 2) (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))
    if ds.isEmpty then synErr "bad hex literal"
    set j
    pure (.lit (Atomic.ofInt (ds.foldl (fun a c => a * 16 + hexVal c) 0)))
  else if chAt s i == '0' && (chAt s (i+1) == 'b' || chAt s (i+1) == 'B') then
    let (ds, j) := digitsUs s (i + 2) (fun c => c == '0' || c == '1')
    if ds.isEmpty then synErr "bad binary literal"
    set j
    pure (.lit (Atomic.ofInt (ds.foldl (fun a c => a * 2 + (c.toNat - 48)) 0)))
  else
    let (ip, j) := digitsUs s i Char.isDigit
    let (fp, j, hasDot) :=
      if chAt s j == '.' && chAt s (j+1) != '.' then
        let (f, j2) := digitsUs s (j + 1) Char.isDigit
        (f, j2, true)
      else ([], j, false)
    if ip.isEmpty && fp.isEmpty then synErr "bad numeric literal"
    if chAt s j == 'e' || chAt s j == 'E' then
      let k := j + 1
      let (sgn, k) := if chAt s k == '+' || chAt s k == '-' then ([chAt s k], k + 1) else ([], k)
      let (es, k2) := digitsUs s k Char.isDigit
      if es.isEmpty then synErr "bad exponent"
      set k2
      if isNameStart (chAt s k2) then synErr "name directly after a numeric literal"
      let lex := String.ofList (ip ++ (if hasDot then '.' :: fp else []) ++ 'e' :: sgn ++ es)
      match floatOfLex? (if ip.isEmpty then "0" ++ lex else lex) with
      | some f => pure (.lit (Atomic.ofDbl f))
      | none => synErr "bad double literal"
    else
      set j
      if isNameStart (chAt s j) then synErr "name directly after a numeric literal"
      if hasDot then
        let m : Int := (ip ++ fp).foldl (fun a c => a * 10 + (c.toNat - 48 : Nat)) 0
        pure (.lit (Atomic.ofDec ⟨m, fp.length⟩))
      else pure (.lit (Atomic.ofInt ((ip.foldl (fun a c => a * 10 + (c.toNat - 48)) 0 : Nat) : Int)))

def pStringLit : P String := do
  ws
  let c ← read
  let i ← get
  let s := c.s
  let q := chAt s i
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : Option (List Char × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      if j ≥ s.size then none
      else
        let ch := chAt s j
        if ch == q then
          if chAt s (j+1) == q then go (j + 2) (q :: acc) f
          else some (acc.reverse, j + 1)
        else go (j + 1) (ch :: acc) f
  match go (i + 1) [] (s.size + 1) with
  | some (cs, e) => set e; pure (String.ofList cs)
  | none => synErr "unterminated string literal"

/-! ## The grammar -/

def kindTestNames : List String :=
  ["node", "text", "comment", "element", "attribute", "document-node",
   "processing-instruction", "namespace-node", "schema-element", "schema-attribute",
   "xnode", "jnode"]

def reservedFnNames : List String :=
  kindTestNames ++ ["array", "empty-sequence", "fn", "function", "if", "item", "map",
   "record", "switch", "typeswitch", "enum"]

def atomicTypeOf (q : QN) : P IType := do
  if q.uri == nsXS then
    if q.loc == "numeric" then
      pure (.choice [.atomic (.b .double), .atomic (.b .float), .atomic (.b .decimal)])
    else match atypeOfName? q.loc with
      | some t =>
        if t == .b .anyAtomicType || !(t == .b .nmtokens || t == .b .idrefs || t == .b .entities) then
          pure (.atomic t)
        else throw { code := "XPST0051", msg := "not an atomic type: " ++ q.show }
      | none => throw { code := "XPST0051", msg := "unknown type " ++ q.show }
  else throw { code := "XPST0051", msg := "unknown type " ++ q.show }

/-- `MarkedNCName` etc. are not needed; this reads a name test. -/
def pNameTest (dflt : String) : P NameTest := do
  ws
  if ← atS "*" then
    let c ← read
    let i ← get
    if chAt c.s (i+1) == ':' && isNameStart (chAt c.s (i+2)) then
      match ← peekQName with
      | some (_, _, l, e) => set e; pure (.loc l)
      | none => synErr "bad name test"
    else adv 1; pure .any
  else match ← peekQName with
    | some (p, u, l, e) =>
        set e
        if p == some "*" then pure (.loc l)
        else if l == "*" then
          match u with
          | some uu => pure (.ns uu)
          | none => pure (.ns (← lookupNs (p.getD "")))
        else pure (.name (← resolve p u l dflt))
    | none => synErr "expected a name test"

/-- The first argument of `jnode(...)` (XPath 4.0 §3.2.12). -/
def pJKeyTest : P JKeyTest := do
  ws
  let ch ← peekAt 0
  if ← eatS "*" then pure .any
  else if ch == '(' then
    adv 1; expectS ")"; pure .root
  else if ch == '"' || ch == '\'' then pure (.key (Atomic.ofStr (← pStringLit)))
  else if ch == '#' then
    adv 1
    match ← peekQName with
    | some (p, u, l, e) =>
        set e
        pure (.key (Atomic.ofQN (← resolve p u l "")))
    | none => synErr "bad QName literal"
  else if ch.isDigit || ch == '.' || ch == '-' then
    let neg ← eatS "-"
    match ← pNumber with
    | .lit a =>
      if !neg then pure (.key a) else
      match a.num? with
      | some v => pure (.key (numNeg v).atomic)
      | none => synErr "bad numeric constant"
    | _ => synErr "bad numeric constant"
  else
    match ← afterName with
    | some (nm, '(', _) =>
      if nm == "true" || nm == "false" then
        adv nm.length; expectS "("; expectS ")"
        pure (.key (Atomic.ofBool (nm == "true")))
      else synErr "bad jnode() key"
    | _ =>
      match ← peekQName with
      | some (none, none, l, e) => set e; pure (.key (Atomic.ofStr l))
      | _ => synErr "bad jnode() key"

def pOcc (t : IType) : P IType := do
  -- occurrence indicator directly follows the item type
  let c ← read
  let i ← get
  let j := skipWsF c.s (c.s.size + 1) 0 i
  let ch := chAt c.s j
  if ch == '?' then set (j + 1); pure (.seq t .opt)
  else if ch == '*' then set (j + 1); pure (.seq t .star)
  else if ch == '+' then set (j + 1); pure (.seq t .plus)
  else pure t

mutual

def pSeqType : Nat → P IType
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    if ← atKw "empty-sequence" then
      adv "empty-sequence".length; expectS "("; expectS ")"; pure .empty
    else
      let t ← pItemType n
      pOcc t

def pItemType : Nat → P IType
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    if ← eatS "(" then
      let t ← pItemType n
      let mut ts := [t]
      for _ in [0:1000] do
        if ← eatS "|" then ts := ts ++ [← pItemType n] else break
      expectS ")"
      pure (if ts.length == 1 then t else .choice ts)
    else
    match ← afterName with
    | some (nm, '(', _) =>
      match ← peekQName with
      | some (none, none, _, e) =>
        set e; expectS "("
        match nm with
        | "item" => expectS ")"; pure .item
        | "node" => expectS ")"; pure .anyNode
        | "xnode" => expectS ")"; pure .xnode
        | "jnode" =>
            -- XPath 4.0 §3.2.12: jnode((* | () | NCName | Constant) (, SequenceType)?)
            if ← eatS ")" then pure (.jnodeT .any none)
            else
              let k ← pJKeyTest
              let vt ← if ← eatS "," then pure (some (← pSeqType n)) else pure none
              expectS ")"
              pure (.jnodeT k vt)
        | "text" => expectS ")"; pure .text
        | "comment" => expectS ")"; pure .comment
        | "namespace-node" => expectS ")"; pure .nsNode
        | "processing-instruction" =>
            if ← eatS ")" then pure (.pi none)
            else
              let t ← if (← peekAt 0) == '"' || (← peekAt 0) == '\'' then pStringLit
                      else match ← peekQName with
                        | some (_, _, l, e) => set e; pure l
                        | none => synErr "bad processing-instruction() test"
              expectS ")"; pure (.pi (some t))
        | "element" | "attribute" =>
            if ← eatS ")" then pure (if nm == "element" then .elem none else .attr none)
            else
              let t ← pNameTest ""
              -- union of names, then an optional type name
              for _ in [0:100] do
                if ← eatS "|" then let _ ← pNameTest "" else break
              let ty ← if ← eatS "," then
                  ws
                  match ← peekQName with
                  | some (p, u, l, e) =>
                    set e
                    let q ← resolve p u l ""
                    let nil ← eatS "?"
                    pure (some (q, nil))
                  | none => synErr "expected a type name"
                else pure none
              expectS ")"
              let t' : Option NameTest := match t with
                | .any => none
                | other => some other
              match ty with
              | none => pure (if nm == "element" then .elem (some t) else .attr (some t))
              | some (q, nil) =>
                pure (if nm == "element" then .elemT t' q nil else .attrT t' q)
        | "schema-element" | "schema-attribute" =>
            ws
            match ← peekQName with
            | some (p, u, l, e) =>
              set e
              let q ← resolve p u l ""
              expectS ")"
              pure (if nm == "schema-element" then .schemaElem q else .schemaAttr q)
            | none => synErr ("expected a name in " ++ nm ++ "()")
        | "document-node" =>
            if ← eatS ")" then pure (.doc none)
            else
              let t ← pItemType n
              expectS ")"; pure (.doc (some t))
        | "function" | "fn" =>
            if ← eatS "*" then expectS ")"; pure .anyFn
            else
              let mut ps : List IType := []
              if !(← eatS ")") then
                for _ in [0:1000] do
                  if ← eatS "$" then
                    let _ ← pNameTest ""
                    expectKw "as"
                  ps := ps ++ [← pSeqType n]
                  if !(← eatS ",") then break
                expectS ")"
              expectKw "as"
              let r ← pSeqType n
              pure (.fnT ps r)
        | "map" =>
            if ← eatS "*" then expectS ")"; pure .anyMap
            else
              let k ← pItemType n
              expectS ","
              let v ← pSeqType n
              expectS ")"; pure (.mapT k v)
        | "array" =>
            if ← eatS "*" then expectS ")"; pure .anyArr
            else
              let m ← pSeqType n
              expectS ")"; pure (.arrT m)
        | "record" =>
            if ← eatS "*" then expectS ")"; pure .anyMap
            else
              let mut fs : List (String × Bool × IType) := []
              let mut ext := false
              if !(← eatS ")") then
                for _ in [0:1000] do
                  if ← eatS "*" then ext := true; break
                  let fname ← if (← peekAt 0) == '"' || (← peekAt 0) == '\'' then pStringLit
                    else match ← peekQName with
                      | some (_, _, l, e) => set e; pure l
                      | none => synErr "bad record field"
                  let opt ← eatS "?"
                  let ft ← if ← eatKw "as" then pSeqType n else pure (.seq .item .star)
                  fs := fs ++ [(fname, opt, ft)]
                  if !(← eatS ",") then break
                expectS ")"
              pure (.record fs ext)
        | "enum" =>
            let mut vs : List String := []
            for _ in [0:10000] do
              vs := vs ++ [← pStringLit]
              if !(← eatS ",") then break
            expectS ")"; pure (.enum vs)
        | "empty-sequence" => expectS ")"; pure .empty
        | other => throw { code := "XPST0003", msg := "unsupported item type " ++ other ++ "()" }
      | _ =>
        match ← peekQName with
        | some (p, u, l, e) => set e; atomicTypeOf (← resolve p u l "")
        | none => synErr "expected an item type"
    | _ =>
      match ← peekQName with
      | some (p, u, l, e) =>
        set e
        let q ← resolve p u l ""
        match (if q.uri == nsFN then recordTypesRaw.lookup q.loc else none), n with
        | some src, n' + 1 =>
          -- a named record type of F&O 4.0: parse its record(...) text
          let save ← get
          let t ← withReader (fun c => { c with s := src.toList.toArray, ns := defaultNs }) (do
            set 0
            pItemType n')
          set save
          pure t
        | _, _ => atomicTypeOf q
      | none => synErr "expected an item type"

end

/-- A placeholder `?` is an argument when followed by `,` or `)`. -/
def atPlaceholder : P Bool := do
  ws
  let c ← read
  let i ← get
  if chAt c.s i != '?' then pure false
  else
    let j := skipWsF c.s (c.s.size + 1) 0 (i + 1)
    pure (chAt c.s j == ',' || chAt c.s j == ')')

def dosStep : Expr := .step .descendantOrSelf (.kind .anyNode) []

mutual

def pExpr : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let e ← pExprSingle n
    if ← atS "," then
      let mut es := [e]
      for _ in [0:100000] do
        if ← eatS "," then es := es ++ [← pExprSingle n] else break
      pure (.seq es)
    else pure e

def pEnclosed : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    expectS "{"
    if ← eatS "}" then pure (.seq [])
    else
      let e ← pExpr n
      expectS "}"
      pure e

def pVarName : Nat → P QN
  | 0 => synErr "expression too deeply nested"
  | _ + 1 => do
    expectS "$"
    ws
    match ← peekQName with
    | some (p, u, l, e) => set e; resolve p u l ""
    | none => synErr "expected a variable name"

def pTypeDecl : Nat → P IType
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    if ← eatKw "as" then pSeqType n else pure (.seq .item .star)

/-- `for` clauses, then `let`/`for`/`return`. -/
def pForLetReturn : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    if ← isForStart then pFor n
    else if ← isLetStart then pLet n
    else
      expectKw "return"
      pExprSingle n

def isForStart : P Bool := do
  match ← afterName with
  | some ("for", '$', _) => pure true
  | some ("for", 'm', _) | some ("for", 'k', _) | some ("for", 'v', _) =>
      -- for member / key / value
      let c ← read
      let i ← get
      let j := skipWsF c.s (c.s.size + 1) 0 (i + 3)
      match ncnameAt c.s j with
      | some (w, e) =>
        let k := skipWsF c.s (c.s.size + 1) 0 e
        pure ((w == "member" || w == "key" || w == "value") && chAt c.s k == '$')
      | none => pure false
  | _ => pure false

def isLetStart : P Bool := do
  match ← afterName with
  | some ("let", '$', _) => pure true
  | _ => pure false

def pFor : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    expectKw "for"
    let mut binds : List (ForKind × QN × Option QN × Option QN × IType × Expr) := []
    for _ in [0:1000] do
      let mut kind := ForKind.item
      let mut v2 : Option QN := none
      let mut v : QN := default
      let mut vt : IType := .seq .item .star
      if ← eatKw "member" then
        kind := .member
        v ← pVarName n; vt ← pTypeDecl n
      else if ← eatKw "key" then
        kind := .entry
        v ← pVarName n; vt ← pTypeDecl n
        if ← eatKw "value" then
          v2 := some (← pVarName n); let _ ← pTypeDecl n
      else if ← eatKw "value" then
        kind := .entry
        -- value only: bind the value; key unnamed
        v := { uri := "#none", loc := "#key" }
        v2 := some (← pVarName n); let _ ← pTypeDecl n
      else
        v ← pVarName n; vt ← pTypeDecl n
      let posv ← if ← eatKw "at" then pure (some (← pVarName n)) else pure none
      expectKw "in"
      let src ← pExprSingle n
      binds := binds ++ [(kind, v, v2, posv, vt, src)]
      if !(← atS ",") then break
      -- a comma continues the clause only if a binding follows
      let c ← read
      let i ← get
      let j := skipWsF c.s (c.s.size + 1) 0 (i + 1)
      if chAt c.s j == '$' || (ncnameAt c.s j |>.map (·.1)) == some "member"
         || (ncnameAt c.s j |>.map (·.1)) == some "key" || (ncnameAt c.s j |>.map (·.1)) == some "value" then
        adv 1
      else break
    let body ← pForLetReturn n
    pure (binds.foldr (fun (k, v, v2, pv, vt, src) acc => .forE k v v2 pv vt src acc) body)

def pLet : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    expectKw "let"
    let mut binds : List (QN × IType × Expr) := []
    for _ in [0:1000] do
      let c ← read
      let i ← get
      let j := skipWsF c.s (c.s.size + 1) 0 i
      let k := skipWsF c.s (c.s.size + 1) 0 (j + 1)
      let open_ := chAt c.s k
      if chAt c.s j == '$' && (open_ == '(' || open_ == '[' || open_ == '{') then
        -- destructuring binding (XPath 4.0 §4.12.2): desugared to a
        -- binding of a fresh variable and one binding per name
        set (k + 1)
        let close := if open_ == '(' then ")" else if open_ == '[' then "]" else "}"
        let mut vs : List (QN × IType) := []
        for _ in [0:1000] do
          let v ← pVarName n
          let vt ← pTypeDecl n
          vs := vs ++ [(v, vt)]
          if !(← eatS ",") then break
        expectS close
        let dflt : IType := if open_ == '(' then .seq .item .star else if open_ == '[' then .anyArr else .anyMap
        let st ← if ← atKw "as" then pTypeDecl n else pure dflt
        expectS ":="
        let e ← pExprSingle n
        let tmp : QN := { uri := "#let", loc := toString j }
        binds := binds ++ [(tmp, st, e)]
        let k := vs.length
        for ((v, vt), idx) in vs.zip (List.range k) do
          let pos : Expr := .lit (Atomic.ofInt (idx + 1))
          let rhs : Expr :=
            if open_ == '(' then
              if idx + 1 == k then .call { uri := nsFN, loc := "subsequence" } [some (.var tmp), some pos] []
              else .call { uri := nsFN, loc := "items-at" } [some (.var tmp), some pos] []
            else if open_ == '[' then .call { uri := nsARR, loc := "get" } [some (.var tmp), some pos] []
            else .lookup (.var tmp) (some (.lit (Atomic.ofStr v.loc)))
          binds := binds ++ [(v, vt, rhs)]
        if !(← eatS ",") then break
        continue
      let v ← pVarName n
      let vt ← pTypeDecl n
      expectS ":="
      let e ← pExprSingle n
      binds := binds ++ [(v, vt, e)]
      if !(← eatS ",") then break
    let body ← pForLetReturn n
    pure (binds.foldr (fun (v, vt, e) acc => .letE v vt e acc) body)

def pExprSingle : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    if ← isForStart then pFor n
    else if ← isLetStart then pLet n
    else
    match ← afterName with
    | some ("some", '$', _) | some ("every", '$', _) =>
        let every ← eatKw "every"
        if !every then expectKw "some"
        let mut binds : List (QN × IType × Expr) := []
        for _ in [0:1000] do
          let v ← pVarName n
          let vt ← pTypeDecl n
          expectKw "in"
          let e ← pExprSingle n
          binds := binds ++ [(v, vt, e)]
          if !(← eatS ",") then break
        expectKw "satisfies"
        let sat ← pExprSingle n
        pure (binds.foldr (fun (v, vt, e) acc => .quant every v vt e acc) sat)
    | some ("if", '(', _) =>
        expectKw "if"; expectS "("
        let c ← pExpr n
        expectS ")"
        if ← atS "{" then
          let t ← pEnclosed n
          if ← eatKw "else" then
            if ← atKw "if" then
              let e ← pExprSingle n
              pure (.ifE c t e)
            else
              let e ← pEnclosed n
              pure (.ifE c t e)
          else pure (.ifE c t (.seq []))
        else
          expectKw "then"
          let t ← pExprSingle n
          expectKw "else"
          let e ← pExprSingle n
          pure (.ifE c t e)
    | _ => pLevel n 0

/-- The binary-operator levels: 0 `or`, 1 `and`, 2 comparisons,
    3 `otherwise`, 4 `||`, 5 `to`, 6 `+ -`, 7 `* div idiv mod`,
    8 `union |`, 9 `intersect except`; 10 is the unary chain. -/
def pLevel : Nat → Nat → P Expr
  | 0, _ => synErr "expression too deeply nested"
  | n + 1, lvl => do
    if lvl ≥ 10 then pInstance n
    else
      let mut a ← pLevel n (lvl + 1)
      for _ in [0:100000] do
        match ← opAt lvl with
        | some (op, len) =>
            adv len
            let b ← pLevel n (lvl + 1)
            a := .bin op a b
            if lvl == 2 || lvl == 5 then break
        | none => break
      pure a

def opAt (lvl : Nat) : P (Option (BOp × Nat)) := do
  ws
  let c ← read
  let i ← get
  let s := c.s
  let ch := chAt s i
  let ch1 := chAt s (i+1)
  let kw : Option String := (ncnameAt s i).map (·.1)
  match lvl with
  | 0 => pure (if kw == some "or" then some (.or, 2) else none)
  | 1 => pure (if kw == some "and" then some (.and, 3) else none)
  | 2 =>
    if ch == '=' && ch1 != '>' && !(ch1 == '!' && chAt s (i+2) == '>') && !(ch1 == '?' && chAt s (i+2) == '>') then pure (some (.geq, 1))
    else if ch == '!' && ch1 == '=' then pure (some (.gne, 2))
    else if ch == '<' && ch1 == '<' then pure (some (.precedes, 2))
    else if ch == '<' && ch1 == '=' then pure (some (.gle, 2))
    else if ch == '<' then pure (some (.glt, 1))
    else if ch == '>' && ch1 == '>' then pure (some (.follows, 2))
    else if ch == '>' && ch1 == '=' then pure (some (.gge, 2))
    else if ch == '>' then pure (some (.ggt, 1))
    else match kw with
      | some "eq" => pure (some (.veq, 2)) | some "ne" => pure (some (.vne, 2))
      | some "lt" => pure (some (.vlt, 2)) | some "le" => pure (some (.vle, 2))
      | some "gt" => pure (some (.vgt, 2)) | some "ge" => pure (some (.vge, 2))
      | some "is" => pure (some (.is, 2)) | some "is-not" => pure (some (.isNot, 6))
      | some "precedes" => pure (some (.precedes, 8)) | some "follows" => pure (some (.follows, 7))
      | some "precedes-or-is" => pure (some (.precedesOrIs, 14))
      | some "follows-or-is" => pure (some (.followsOrIs, 13))
      | _ => pure none
  | 3 => pure (if kw == some "otherwise" then some (.otherwise, 9) else none)
  | 4 => pure (if ch == '|' && ch1 == '|' then some (.concat, 2) else none)
  | 5 => pure (if kw == some "to" then some (.to, 2) else none)
  | 6 =>
    if ch == '+' then pure (some (.add, 1))
    else if ch == '-' && ch1 != '>' then pure (some (.sub, 1))
    else pure none
  | 7 =>
    if ch == '*' then pure (some (.mul, 1))
    else if ch == '×' then pure (some (.mul, 1))
    else if ch == '÷' then pure (some (.div, 1))
    else match kw with
      | some "div" => pure (some (.div, 3)) | some "idiv" => pure (some (.idiv, 4))
      | some "mod" => pure (some (.mod, 3)) | _ => pure none
  | 8 =>
    if ch == '|' && ch1 != '|' then pure (some (.union, 1))
    else pure (if kw == some "union" then some (.union, 5) else none)
  | 9 => match kw with
    | some "intersect" => pure (some (.intersect, 9))
    | some "except" => pure (some (.except, 6))
    | _ => pure none
  | _ => pure none

def pInstance : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let one : P Expr := do
      let e ← pTreat n
      if ← atKw "instance" then
        adv 8; expectKw "of"
        pure (.instOf e (← pSeqType n))
      else pure e
    let mut e ← one
    -- XPath 4.0 §4.15.4 `A but with B`: `map:merge((A, B), {'duplicates':'use-last'})`
    -- (no value here carries a record type annotation, so the result is
    -- not checked against the record type of A)
    for _ in [0:10000] do
      if ← atKw "but" then
        adv 3; expectKw "with"
        let b ← one
        e := .call { uri := nsMAP, loc := "merge" }
          [some (.seq [e, b]), some (.mapC [(.lit (Atomic.ofStr "duplicates"), .lit (Atomic.ofStr "use-last"))])] []
      else break
    pure e

def pTreat : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let e ← pCastable n
    if ← atKw "treat" then
      adv 5; expectKw "as"
      pure (.treat e (← pSeqType n))
    else pure e

def pCastTarget : Nat → P (IType × Bool)
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let t ← pItemType n
    let c ← read
    let i ← get
    let j := skipWsF c.s (c.s.size + 1) 0 i
    if chAt c.s j == '?' then set (j + 1); pure (t, true) else pure (t, false)

def pCastable : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let e ← pCast n
    if ← atKw "castable" then
      adv 8; expectKw "as"
      let (t, o) ← pCastTarget n
      pure (.castable e t o)
    else pure e

def pCast : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let e ← pPipeline n
    if ← atKw "cast" then
      adv 4; expectKw "as"
      let (t, o) ← pCastTarget n
      pure (.cast e t o)
    else pure e

def pPipeline : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut a ← pArrow n
    for _ in [0:100000] do
      if ← eatS "->" then
        let b ← pArrow n
        a := .pipe a b
      else break
    pure a

/-- An arrow target: returns the function expression (or static
    name) and the argument list. -/
def pArrowTarget : Nat → P (Sum (QN) Expr × List (Option Expr) × List (String × Option Expr))
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    let ch ← peekAt 0
    if ch == '$' then
      let v ← pVarName n
      let (args, _) ← pArgs n
      pure (.inr (.var v), args, [])
    else if ch == '(' then
      adv 1
      let e ← pExpr n
      expectS ")"
      let (args, _) ← pArgs n
      pure (.inr e, args, [])
    else
      match ← afterName with
      | some ("function", _, _) | some ("fn", _, _) | some ("map", '{', _) | some ("array", '{', _) =>
          let f ← pPrimary n
          let (args, _) ← pArgs n
          pure (.inr f, args, [])
      | _ =>
        if ch == '{' || ch == '[' then
          let f ← pPrimary n
          let (args, _) ← pArgs n
          pure (.inr f, args, [])
        else
        match ← peekQName with
        | some (p, u, l, e) =>
            set e
            let q ← resolve p u l nsFN
            let (args, kw) ← pArgs n
            pure (.inl q, args, kw)
        | none => synErr "expected an arrow target"

def pArrow : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut a ← pUnary n
    for _ in [0:100000] do
      if ← eatS "=>" then
        match ← pArrowTarget n with
        | (.inl q, args, kw) => a := .call q (some a :: args) kw
        | (.inr f, args, _) => a := .dyn f (some a :: args)
      else if ← eatS "=!>" then
        match ← pArrowTarget n with
        | (.inl q, args, _) => a := .mapArrow a (.fref q (args.length + 1)) args
        | (.inr f, args, _) => a := .mapArrow a f args
      else break
    pure a

def pUnary : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    if ← eatS "-" then pure (.neg (← pUnary n))
    else if ← eatS "+" then pure (.plus (← pUnary n))
    else pSimpleMap n

def pSimpleMap : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut a ← pPath n
    for _ in [0:100000] do
      ws
      if (← peekAt 0) == '!' && (← peekAt 1) != '=' && (← peekAt 1) != '>' then
        adv 1
        let b ← pPath n
        a := .smap a b
      else break
    pure a

/-- Can a relative path start here? (For the lone `/`.) -/
def canStartRel : P Bool := do
  ws
  let ch ← peekAt 0
  let ch1 ← peekAt 1
  if isNameStart ch || ch == '*' || ch == '@' || ch == '.' || ch == '$' || ch == '"' || ch == '\''
     || ch == '(' || ch.isDigit || ch == '[' || ch == '`' || (ch == '?' && ch1 != '?') then pure true
  else pure (ch == '{' || ch == '#')

def pPath : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    if ← eatS "//" then
      let r ← pRel n
      pure (.slash (.slash .root dosStep) r)
    else if ← atS "/" then
      adv 1
      -- leading lone slash: `/` alone, or followed by something that is
      -- not the start of a relative path
      let c ← read
      let i ← get
      let j := skipWsF c.s (c.s.size + 1) 0 i
      let ch := chAt c.s j
      -- an operator-looking start after '/' means a lone slash
      if ch == '*' then
        -- `/*` is a wildcard step (xgc: leading-lone-slash)
        let r ← pRel n
        pure (.slash .root r)
      else if (← canStartRel) && !(ch == '<' || ch == '=' || ch == '!') then
        -- names that are operators after a lone slash still start a path
        let r ← pRel n
        pure (.slash .root r)
      else pure .root
    else pRel n

def pRel : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut a ← pStep n
    for _ in [0:100000] do
      if ← eatS "//" then
        let b ← pStep n
        a := .slash (.slash a dosStep) b
      else if ← atS "/" then
        adv 1
        let b ← pStep n
        a := .slash a b
      else break
    pure a

def pPreds : Nat → P (List Expr)
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut ps : List Expr := []
    for _ in [0:10000] do
      if ← eatS "[" then
        let p ← pExpr n
        expectS "]"
        ps := ps ++ [p]
      else break
    pure ps

/-- A node test after an axis. -/
def pNodeTest : Nat → Axis → P NodeTest
  | 0, _ => synErr "expression too deeply nested"
  | n + 1, ax => do
    ws
    if ← eatS "(" then
      let mut ts := [← pNodeTest n ax]
      for _ in [0:1000] do
        if ← eatS "|" then ts := ts ++ [← pNodeTest n ax] else break
      expectS ")"
      pure (.union ts)
    else
    match ← afterName with
    | some (nm, '(', _) =>
      if kindTestNames.contains nm then pure (.kind (← pItemType n))
      else synErr ("unexpected function call in a step: " ++ nm)
    | _ =>
      let star := (← peekAt 0) == '*'
      match ← peekQName with
      | some (none, none, l, _) =>
        if star || l == "*" then pure (.name (← pNameTest ""))
        else pure (.ncname (← pNameTest "") l)
      | _ => pure (.name (← pNameTest (if ax == .attribute then "" else "")))

def pStep : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    let ch ← peekAt 0
    let ch1 ← peekAt 1
    if ch == '.' && ch1 == '.' then
      adv 2
      let ps ← pPreds n
      pure (.step .parent (.kind .anyNode) ps)
    else if ch == '@' then
      adv 1
      let t ← pNodeTest n .attribute
      let ps ← pPreds n
      pure (.step .attribute t ps)
    else if ch == '*' then
      let t ← pNodeTest n .child
      let ps ← pPreds n
      pure (.step .child t ps)
    else
    match ← afterName with
    | some (nm, ':', ':') =>
      match axisOfName? nm with
      | some ax =>
          let _ ← peekQName
          adv nm.length; ws; expectS "::"
          ws
          if (← peekAt 0) == '{' then
            -- a dynamic node test (XPath 4.0 §4.7.5.2)
            let e ← pEnclosed n
            let ps ← pPreds n
            pure (.dstep ax e ps)
          else
          let t ← pNodeTest n ax
          let ps ← pPreds n
          pure (.step ax t ps)
      | none => synErr ("unknown axis " ++ nm)
    | some (nm, '(', _) =>
      if kindTestNames.contains nm then
        let t ← pNodeTest n .child
        let ax := match t with
          | .kind (.attr _) => Axis.attribute
          | .kind .nsNode => Axis.namespace
          | _ => Axis.child
        let ps ← pPreds n
        pure (.step ax t ps)
      else pPostfix n
    | some (nm, c1, c2) =>
      -- a name: a step unless it is a primary-expression keyword
      let isPrimaryKw :=
        (c1 == '#' && (c2.isDigit || c2 == ' ' || c2 == '\t' || c2 == '\n' || c2 == '\r' || c2 == '(')) ||
        ((nm == "map" || nm == "array") && c1 == '{') ||
        ((nm == "fn" || nm == "function") && (c1 == '{' || c1 == '('))
      if isPrimaryKw then pPostfix n
      else
        let t ← pNodeTest n .child
        let ps ← pPreds n
        pure (.step .child t ps)
    | none => pPostfix n

def pArgs : Nat → P (List (Option Expr) × List (String × Option Expr))
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    expectS "("
    if ← eatS ")" then pure ([], [])
    else
      let mut args : List (Option Expr) := []
      let mut kws : List (String × Option Expr) := []
      for _ in [0:100000] do
        -- keyword argument `name := value`
        let c ← read
        let i ← get
        let j := skipWsF c.s (c.s.size + 1) 0 i
        let kwName : Option String :=
          match ncnameAt c.s j with
          | some (nm, e) =>
              let k := skipWsF c.s (c.s.size + 1) 0 e
              if chAt c.s k == ':' && chAt c.s (k+1) == '=' then some nm else none
          | none => none
        match kwName with
        | some nm =>
            set j; adv nm.length; expectS ":="
            if ← atPlaceholder then expectS "?"; kws := kws ++ [(nm, none)]
            else kws := kws ++ [(nm, some (← pExprSingle n))]
        | none =>
            if !kws.isEmpty then synErr "positional argument after keyword argument"
            if ← atPlaceholder then expectS "?"; args := args ++ [none]
            else args := args ++ [some (← pExprSingle n)]
        if !(← eatS ",") then break
      expectS ")"
      pure (args, kws)

def pKeySpec : Nat → P (Option Expr)
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    let ch ← peekAt 0
    if ch == '*' then adv 1; pure none
    else if ch == '(' then
      adv 1
      if ← eatS ")" then pure (some (.seq []))
      else
        let e ← pExpr n
        expectS ")"; pure (some e)
    else if ch == '$' then pure (some (.var (← pVarName n)))
    else if ch == '"' || ch == '\'' then pure (some (.lit (Atomic.ofStr (← pStringLit))))
    else if ch.isDigit then pure (some (← pNumber))
    else if ch == '.' then adv 1; pure (some .ctx)
    else if ch == '#' then
      -- a QName literal as the key (XPath 4.0 KeySpecifier)
      adv 1
      match ← peekQName with
      | some (p, u, l, e) =>
          set e
          let q ← resolve p u l ""
          pure (some (.lit (Atomic.ofQN q)))
      | none => synErr "bad QName literal"
    else
      let c ← read
      let i ← get
      match ncnameAt c.s i with
      | some (nm, e) => set e; pure (some (.lit (Atomic.ofStr nm)))
      | none => synErr "bad lookup key"

def pPostfix : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    let mut a ← pPrimary n
    for _ in [0:100000] do
      ws
      let ch ← peekAt 0
      if ch == '[' then
        adv 1
        let p ← pExpr n
        expectS "]"
        a := .filter a p
      else if ch == '(' then
        let (args, _) ← pArgs n
        a := .dyn a args
      else if ch == '?' && (← peekAt 1) != '?' then
        adv 1
        let k ← pKeySpec n
        a := .lookup a k
      else if ch == '=' && (← peekAt 1) == '?' && (← peekAt 2) == '>' then
        -- XPath 4.0 §4.15.5 method call `M =?> N(args)`: for each map $m
        -- in M, `$m?N($m, args)` (a variable name no source text can bind)
        adv 3
        ws
        let c ← read
        let i ← get
        let some (nm, e) := ncnameAt c.s i | synErr "expected a method name after =?>"
        set e
        let (args, kw) ← pArgs n
        if !kw.isEmpty || args.any Option.isNone then
          synErr "a method call cannot have keyword arguments or placeholders"
        let v : QN := { uri := "", loc := "#method-target" }
        a := .forE .item v none none (.seq .item .star) a
          (.dyn (.lookup (.var v) (some (.lit (Atomic.ofStr nm)))) (some (.var v) :: args))
      else break
    pure a

def pInlineFn : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    -- after `function` / `fn`
    ws
    if (← peekAt 0) == '{' then
      let body ← pEnclosed n
      pure (.inline [] (.seq .item .star) body true)
    else
      expectS "("
      let mut ps : List (QN × IType) := []
      if !(← eatS ")") then
        for _ in [0:1000] do
          let v ← pVarName n
          let t ← pTypeDecl n
          ps := ps ++ [(v, t)]
          if !(← eatS ",") then break
        expectS ")"
      let r ← pTypeDecl n
      let body ← pEnclosed n
      pure (.inline ps r body false)

def pMapEntries : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    expectS "{"
    if ← eatS "}" then pure (.mapC [])
    else
      let mut es : List (Expr × Expr) := []
      for _ in [0:100000] do
        let k ← pExprSingle n
        if ← eatS ":" then
          let v ← pExprSingle n
          es := es ++ [(k, v)]
        else
          -- an entry without ':' is a map expression whose entries are merged
          es := es ++ [(k, .call { uri := "#merge", loc := "#merge" } [] [])]
        if !(← eatS ",") then break
      expectS "}"
      pure (.mapC es)

def pTemplate : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    -- at '`'
    adv 1
    let mut parts : List Expr := []
    let mut buf : List Char := []
    let c ← read
    for _ in [0:c.s.size + 1] do
      let i ← get
      if i ≥ c.s.size then synErr "unterminated string template"
      let ch := chAt c.s i
      let ch1 := chAt c.s (i+1)
      if ch == '`' && ch1 == '`' then buf := buf ++ ['`']; adv 2
      else if ch == '`' then adv 1; break
      else if ch == '{' && ch1 == '{' then buf := buf ++ ['{']; adv 2
      else if ch == '}' && ch1 == '}' then buf := buf ++ ['}']; adv 2
      else if ch == '}' then synErr "unescaped '}' in string template"
      else if ch == '{' then
        if !buf.isEmpty then parts := parts ++ [.lit (Atomic.ofStr (String.ofList buf))]
        buf := []
        let e ← pEnclosed n
        parts := parts ++ [.call { uri := "#tmpl", loc := "#tmpl" } [some e] []]
      else buf := buf ++ [ch]; adv 1
    if !buf.isEmpty then parts := parts ++ [.lit (Atomic.ofStr (String.ofList buf))]
    pure (.tmpl parts)

def pPrimary : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    ws
    let ch ← peekAt 0
    let ch1 ← peekAt 1
    if ch.isDigit || (ch == '.' && ch1.isDigit) then pNumber
    else if ch == '"' || ch == '\'' then pure (.lit (Atomic.ofStr (← pStringLit)))
    else if ch == '`' then pTemplate n
    else if ch == '$' then pure (.var (← pVarName n))
    else if ch == '(' then
      adv 1
      if ← eatS ")" then pure (.seq [])
      else
        let e ← pExpr n
        expectS ")"
        -- parenthesised: wrap single so `(a, b)[1]` filters the whole
        pure (match e with | .seq es => .seq es | other => .seq [other])
    else if ch == '.' then adv 1; pure .ctx
    else if ch == '[' then
      adv 1
      if ← eatS "]" then pure (.arrS [])
      else
        let mut es : List Expr := []
        for _ in [0:100000] do
          es := es ++ [← pExprSingle n]
          if !(← eatS ",") then break
        expectS "]"
        pure (.arrS es)
    else if ch == '{' then pMapEntries n
    else if ch == '?' then
      adv 1
      pure (.ulookup (← pKeySpec n))
    else if ch == '#' then
      adv 1
      match ← peekQName with
      | some (p, u, l, e) =>
          set e
          let q ← resolve p u l ""
          pure (.lit (Atomic.ofQN q))
      | none => synErr "bad QName literal"
    else
    match ← afterName with
    | some ("map", '{', _) => expectKw "map"; pMapEntries n
    | some ("array", '{', _) => expectKw "array"; pure (.arrC (← pEnclosed n))
    | some ("function", c1, _) | some ("fn", c1, _) =>
        if c1 == '(' || c1 == '{' then
          let _ ← eatKw "function"
          let _ ← eatKw "fn"
          pInlineFn n
        else synErr "bad function expression"
    | some (_, '#', _) =>
        match ← peekQName with
        | some (p, u, l, e) =>
            set e
            let q ← resolve p u l nsFN
            expectS "#"
            ws
            let c ← read
            let i ← get
            let (ds, j) := digitsUs c.s i Char.isDigit
            if ds.isEmpty then synErr "expected the arity after #"
            set j
            pure (.fref q (ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0))
        | none => synErr "bad named function reference"
    | some (nm, '(', _) =>
        if reservedFnNames.contains nm then
          match ← peekQName with
          | some (none, none, _, _) => synErr ("reserved function name " ++ nm)
          | _ => pCallAfterName n
        else pCallAfterName n
    | _ => synErr "unexpected token"

def pCallAfterName : Nat → P Expr
  | 0 => synErr "expression too deeply nested"
  | n + 1 => do
    match ← peekQName with
    | some (p, u, l, e) =>
        set e
        let q ← resolve p u l nsFN
        let (args, kw) ← pArgs n
        pure (.call q args kw)
    | none => synErr "expected a function name"

end

/-- Parse a complete XPath 4.0 expression, with optional namespace
    declarations prolog. -/
def parseXPath (src : String) (ns : List (String × String) := []) : M Expr :=
  let p : P Expr := do
    -- prolog: declare namespace p = "uri";
    let mut extra : List (String × String) := []
    for _ in [0:100] do
      if ← atKw "declare" then
        let save ← get
        adv 7
        if ← eatKw "namespace" then
          let c ← read
          ws
          let i ← get
          match ncnameAt c.s i with
          | some (pf, e) =>
              set e; expectS "="
              let u ← pStringLit
              expectS ";"
              extra := extra ++ [(pf, u)]
          | none => synErr "bad namespace declaration"
        else set save; break
      else break
    let e ← withReader (fun c => { c with ns := extra ++ c.ns }) (pExpr 100000)
    ws
    let c ← read
    let i ← get
    if i < c.s.size then synErr ("unexpected text at offset " ++ toString i ++ ": '" ++
       String.ofList ((List.range (min 20 (c.s.size - i))).map (fun k => chAt c.s (i + k))) ++ "'")
    pure e
  match (p.run { s := src.toList.toArray, ns }).run 0 with
  | .ok (e, _) => .ok e
  | .error e => .error e

/-- Parse a sequence type on its own (function signatures, tests). -/
def parseSeqType (src : String) : M IType :=
  match ((do let t ← pSeqType 1000; ws; pure t : P IType).run { s := src.toList.toArray, ns := [] }).run 0 with
  | .ok (t, _) => .ok t
  | .error e => .error e

#guard (parseXPath "1 + 2 * 3").isOk
#guard (parseXPath "for $x in 1 to 3 return $x * 2").isOk
#guard (parseXPath "map { 'a' : 1 }?a").isOk
#guard (parseXPath "/a/b[@c = 1]//d").isOk
#guard (parseXPath "function($x as xs:integer) as xs:integer { $x + 1 }(2)").isOk
#guard (parseXPath "(1, 2) => sum()").isOk
#guard (parseXPath "1 +").toOption.isNone
#guard (parseSeqType "map(xs:string, item()*)?").isOk

end L4Factoidal.XPath4
