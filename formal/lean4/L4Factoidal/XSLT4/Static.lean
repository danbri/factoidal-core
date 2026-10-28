/-
L4Factoidal.XSLT4.Static — the static context of a stylesheet element and
the parsing of what its attributes hold: XPath expressions (§5.3),
sequence types, attribute and text value templates (§5.6), patterns
(§6.3) and their default priorities (§6.4).

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28).
-/
import L4Factoidal.XSLT4.Ast

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- The static context of a stylesheet element (§5.3): what it
    inherits from its ancestors in the stylesheet module. -/
structure SCx where
  /-- In-scope namespace bindings (prefix, URI), effective, newest first. -/
  ns : List (String × String) := []
  /-- `xpath-default-namespace` (§5.3.2). -/
  xpathNs : String := ""
  expandText : Bool := false
  /-- The effective `version` (§3.9): "1.0" turns on the
      backwards-compatible behaviour. -/
  version : String := "4.0"
  excl : List String := []
  ext : List String := []
  defaultMode : String := "#unnamed"
  baseUri : String := ""
  preserveWs : Bool := false
  defaultCollation : String := ""
  /-- The native in-scope namespaces (for the namespace nodes of literal
      result elements); `ns` differs when `fixed-namespaces` is in force. -/
  nat : List (String × String) := []
  /-- The fixed namespace bindings of the module (§3.6.1), if any. -/
  fixedNs : Option (List (String × String)) := none
  /-- Named item types (`xsl:item-type`, `xsl:record-type`, §5.4): the
      expanded name and the text of the item type. -/
  types : List (QN × String) := []
deriving Inhabited

/-- The value of a `version` attribute, in thousandths (a decimal,
    §3.9); `none` when it is not a decimal. -/
def versionMilli (v : String) : Option Nat :=
  let t := v.trimAscii.toString
  match t.splitOn "." with
  | [a] => a.toNat?.map (· * 1000)
  | [a, b] =>
    let b3 := (b ++ "000").take 3
    match (if a == "" then some 0 else a.toNat?), b3.toString.toNat? with
    | some x, some y => some (x * 1000 + y)
    | _, _ => none
  | _ => none

/-- Backwards-compatible behaviour (§3.9): a version below 2.0. -/
def SCx.backCompat (c : SCx) : Bool :=
  match versionMilli c.version with
  | some k => k < 2000
  | none => false

/-- Forwards-compatible behaviour (§3.10): a version above 4.0. -/
def SCx.forwardsCompat (c : SCx) : Bool :=
  match versionMilli c.version with
  | some k => k > 4000
  | none => false

/-- The bindings the XPath parser sees (no default namespace entry). -/
def SCx.xpNs (c : SCx) : List (String × String) :=
  let ns := (c.ns.filter (fun (p, _) => p != "")).foldl (fun acc (p, u) =>
    if acc.any (·.1 == p) then acc else acc ++ [(p, u)]) []
  -- `xpath-default-namespace` is also the namespace of unprefixed type
  -- names (§5.1.2)
  if c.xpathNs == "" then ns else ("#type", c.xpathNs) :: ns

/-! ## `xpath-default-namespace`: unprefixed element names in name
tests and element type tests take this namespace. -/

def ntDefault (d : String) : NameTest → NameTest
  | .name q => if q.uri == "" && q.pfx == "" then .name { q with uri := d } else .name q
  | t => t

def itDefault (d : String) : Nat → IType → IType
  | 0, t => t
  | f + 1, t =>
    match t with
    | .elem (some n) => .elem (some (ntDefault d n))
    | .doc (some i) => .doc (some (itDefault d f i))
    | .seq i o => .seq (itDefault d f i) o
    | .choice ts => .choice (ts.map (itDefault d f))
    | .fnT as r => .fnT (as.map (itDefault d f)) (itDefault d f r)
    | .mapT k v => .mapT (itDefault d f k) (itDefault d f v)
    | .arrT m => .arrT (itDefault d f m)
    | t => t

def nodeTestDefault (d : String) (ax : Axis) : NodeTest → NodeTest
  | .name t => if ax == .attribute || ax == .namespace then .name t else .name (ntDefault d t)
  | .kind t => .kind (itDefault d 50 t)
  | .ncname t l => if ax == .attribute || ax == .namespace then .ncname t l else .ncname (ntDefault d t) l
  | .union ts => .union (ts.map (fun t => match t with
      | .name n => if ax == .attribute || ax == .namespace then .name n else .name (ntDefault d n)
      | .kind k => .kind (itDefault d 50 k)
      | u => u))

/-- Apply `xpath-default-namespace` throughout an expression. -/
def exprDefault (d : String) : Nat → Expr → Expr
  | 0, e => e
  | f + 1, e =>
    let r := exprDefault d f
    let ro : Option Expr → Option Expr := fun o => o.map r
    let rt := fun t => itDefault d 50 t
    match e with
    | .seq es => .seq (es.map r)
    | .slash a b => .slash (r a) (r b)
    | .step ax t ps => .step ax (nodeTestDefault d ax t) (ps.map r)
    | .filter a p => .filter (r a) (r p)
    | .call q as kw => .call q (as.map ro) (kw.map (fun (k, v) => (k, ro v)))
    | .dyn g as => .dyn (r g) (as.map ro)
    | .inline ps ret body foc => .inline (ps.map (fun (q, t) => (q, rt t))) (rt ret) (r body) foc
    | .mapC es => .mapC (es.map (fun (k, v) => (r k, r v)))
    | .arrS es => .arrS (es.map r)
    | .arrC a => .arrC (r a)
    | .lookup a k => .lookup (r a) (ro k)
    | .ulookup k => .ulookup (ro k)
    | .bin op a b => .bin op (r a) (r b)
    | .neg a => .neg (r a)
    | .plus a => .plus (r a)
    | .ifE c t x => .ifE (r c) (r t) (r x)
    | .forE k v v2 pv vt src body => .forE k v v2 pv (rt vt) (r src) (r body)
    | .letE v vt x body => .letE v (rt vt) (r x) (r body)
    | .quant ev v vt src sat => .quant ev v (rt vt) (r src) (r sat)
    | .instOf a t => .instOf (r a) (rt t)
    | .treat a t => .treat (r a) (rt t)
    | .cast a t o => .cast (r a) t o
    | .castable a t o => .castable (r a) t o
    | .smap a b => .smap (r a) (r b)
    | .pipe a b => .pipe (r a) (r b)
    | .mapArrow a g as => .mapArrow (r a) (r g) (as.map ro)
    | .tmpl ps => .tmpl (ps.map r)
    | other => other

/-- Replace the names of named item types in an expression or a type
    by their definitions, in parentheses. A name is replaced where it is
    a whole QName token outside string literals, not after `$`, `@`, `/`,
    `:` or `#`, and not before `(`, `#` or `:`. Up to 10 rounds, for types
    that refer to other named types. -/
def expandTypes (types : List (QN × String)) (ns : List (String × String)) : Nat → String → String
  | 0, s => s
  | f + 1, s =>
    if types.isEmpty then s else
    let cs := s.toList.toArray
    let isNC (c : Char) := isNameCh c
    Id.run do
      let mut out : String := ""
      let mut i := 0
      let mut q : Option Char := none
      let mut changed := false
      for _ in [0:cs.size + 1] do
        if i ≥ cs.size then break
        let c := cs[i]!
        match q with
        | some qc => out := out.push c; i := i + 1; if c == qc then q := none
        | none =>
          if c == '"' || c == '\'' then q := some c; out := out.push c; i := i + 1
          else if isNameStart c && (i == 0 || !(isNC cs[i-1]! || ['$', '@', '/', ':', '#', '{', '}'].contains cs[i-1]!)) then
            -- read a QName
            let mut j := i
            let mut tok := ""
            for _ in [0:cs.size] do
              if j < cs.size && (isNC cs[j]! || (cs[j]! == ':' && j + 1 < cs.size && isNameStart cs[j+1]! && !tok.contains ':')) then
                tok := tok.push cs[j]!; j := j + 1
              else break
            let nextC := (List.range (cs.size - j)).findSome? (fun k =>
              let d := cs[j + k]!
              if d == ' ' || d == '\n' || d == '\t' || d == '\r' then none else some d)
            let qn? : Option QN := match tok.splitOn ":" with
              | [l] => some { uri := "", loc := l }
              | [p, l] => (ns.lookup p).map (fun u => { uri := u, loc := l })
              | _ => none
            let hit := match qn? with
              | some qn => if nextC == some '(' || nextC == some '#' || nextC == some ':' then none
                           else (types.find? (fun (t, _) => t == qn)).map (·.2)
              | none => none
            match hit with
            | some d => out := out ++ "(" ++ d ++ ")"; changed := true
            | none => out := out ++ tok
            i := j
          else out := out.push c; i := i + 1
      return if changed then expandTypes types ns f out else out

/-- Parse an XPath expression in the static context `c`. -/
def SCx.parse (c : SCx) (src : String) : M Expr := do
  let src := expandTypes c.types c.ns 10 src
  let e ← match parseXPath src c.xpNs with
    | .ok e => pure e
    | .error er => throw { er with msg := er.msg ++ " in '" ++ src ++ "'" }
  pure (if c.xpathNs == "" then e else exprDefault c.xpathNs 100000 e)

/-- Parse a sequence type in the static context `c`. -/
def SCx.parseType (c : SCx) (src : String) : M IType := do
  let src := expandTypes c.types c.ns 10 src
  let p : P IType := do let t ← pSeqType 1000; ws; pure t
  match (p.run { s := src.toList.toArray, ns := c.xpNs }).run 0 with
  | .ok (t, i) =>
      if i < src.length then err "XTSE0020" ("invalid sequence type '" ++ src ++ "'")
      else pure (if c.xpathNs == "" then t else itDefault c.xpathNs 50 t)
  | .error _ => err "XTSE0020" ("invalid sequence type '" ++ src ++ "'")

/-- Resolve a lexical QName (or EQName) in the static context; the
    default namespace applies when `useDefault`. -/
def SCx.qname (c : SCx) (s : String) (useDefault : Bool := false) (code : String := "XTSE0280") : M QN := do
  let s := s.trimAscii.toString
  if s.startsWith "Q{" then
    match (s.drop 2).toString.splitOn "}" with
    | [u, l] => pure { uri := u, loc := l }
    | _ => err code ("invalid EQName '" ++ s ++ "'")
  else match s.splitOn ":" with
    | [l] =>
        if l == "" then err code "empty name" else
        pure { uri := if useDefault then (c.ns.lookup "").getD "" else "", loc := l }
    | [p, l] =>
        if p == "xml" then pure { uri := nsXML, loc := l, pfx := p } else
        match c.ns.lookup p with
        | some u => pure { uri := u, loc := l, pfx := p }
        | none => err code ("undeclared namespace prefix '" ++ p ++ "' in '" ++ s ++ "'")
    | _ => err code ("invalid QName '" ++ s ++ "'")

/-! ## Value templates (§5.6) -/

/-- Split a value template into fixed text and expression texts. An
    expression ends at the `}` that closes its first `{`, outside string
    literals and comments; `{{` and `}}` in fixed text stand for single
    braces. -/
def splitTemplate (s : String) : M (List (Bool × String)) := do
  let cs := s.toList.toArray
  let mut out : Array (Bool × String) := #[]
  let mut buf : String := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '{' then
      if cs.getD (i+1) ' ' == '{' then buf := buf.push '{'; i := i + 2
      else
        if buf != "" then out := out.push (false, buf); buf := ""
        -- scan the expression
        let mut depth := 1
        let mut j := i + 1
        let mut q : Option Char := none
        let mut cmt := 0
        let mut e : String := ""
        for _ in [0:cs.size + 1] do
          if j ≥ cs.size then break
          let d := cs[j]!
          match q with
          | some qc =>
              e := e.push d
              if d == qc then q := none
              j := j + 1
          | none =>
            if cmt > 0 then
              if d == ':' && cs.getD (j+1) ' ' == ')' then cmt := cmt - 1; e := e ++ ":)"; j := j + 2
              else if d == '(' && cs.getD (j+1) ' ' == ':' then cmt := cmt + 1; e := e ++ "(:"; j := j + 2
              else e := e.push d; j := j + 1
            else if d == '(' && cs.getD (j+1) ' ' == ':' then cmt := 1; e := e ++ "(:"; j := j + 2
            else if d == '"' || d == '\'' then q := some d; e := e.push d; j := j + 1
            else if d == '{' then depth := depth + 1; e := e.push d; j := j + 1
            else if d == '}' then
              depth := depth - 1
              if depth == 0 then break
              e := e.push d; j := j + 1
            else e := e.push d; j := j + 1
        if j ≥ cs.size then err "XTSE0350" ("unclosed '{' in value template '" ++ s ++ "'")
        out := out.push (true, e)
        i := j + 1
    else if c == '}' then
      if cs.getD (i+1) ' ' == '}' then buf := buf.push '}'; i := i + 2
      else err "XTSE0370" ("unescaped '}' in value template '" ++ s ++ "'")
    else buf := buf.push c; i := i + 1
  if buf != "" then out := out.push (false, buf)
  pure out.toList

/-- The text of an expression with its comments `(: ... :)` (which
    nest) removed, outside string literals. -/
def dropComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut depth := 0
  let mut q : Option Char := none
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let d := cs[i]!
    let nx := cs.getD (i+1) ' '
    if depth > 0 then
      if d == ':' && nx == ')' then depth := depth - 1; i := i + 2
      else if d == '(' && nx == ':' then depth := depth + 1; i := i + 2
      else i := i + 1
    else match q with
      | some qc =>
        out := out.push d
        if d == qc then q := none
        i := i + 1
      | none =>
        if d == '(' && nx == ':' then depth := 1; out := out.push ' '; i := i + 2
        else
          if d == '"' || d == '\'' then q := some d
          out := out.push d; i := i + 1
  pure out

def SCx.avt (c : SCx) (s : String) : M Avt := do
  let parts ← splitTemplate s
  parts.mapM (fun (isE, t) => do
    if isE then
      if (dropComments t).trimAscii.toString == "" then pure (AvtPart.lit "")
      else pure (AvtPart.expr (← c.parse t))
    else pure (AvtPart.lit t))

/-! ## Patterns (§6.3) -/

def exprFlat : Nat → Expr → List Expr
  | 0, e => [e]
  | f + 1, .slash a b => exprFlat f a ++ exprFlat f b
  | _, e => [e]

/-- The alternatives of a union pattern (§6.8: one template rule each). -/
def exprAlternatives : Nat → Expr → List Expr
  | 0, e => [e]
  | f + 1, .bin .union a b => exprAlternatives f a ++ exprAlternatives f b
  | _, e => [e]

/-- Is this a step usable at the end of a pattern? -/
def isPatternAxis (ax : Axis) : Bool :=
  ax == .child || ax == .attribute || ax == .self || ax == .descendant ||
  ax == .descendantOrSelf || ax == .namespace

/-- The number of derivation steps from a primitive type down to `b`
    (1 for a primitive type). -/
def derivDepth (b : L4Factoidal.XSD.Builtin) : Nat := Id.run do
  let mut cur := b
  let mut k := 1
  for _ in [0:30] do
    if cur.primitive == some cur then break
    match cur.base? with
    | some p => cur := p; k := k + 1
    | none => break
  return k

/-- The default priority of a type pattern `~T` (the priorities the
    xslt40-test `priority` test set gives for the 4.0 draft). -/
def typePriority : Nat → IType → Float
  | 0, _ => 0.5
  | f + 1, t =>
    match t with
    | .item => -1
    | .anyNode | .anyFn | .elem none | .attr none | .elem (some .any) | .attr (some .any)
    | .text | .comment | .nsNode | .pi none | .doc none => -0.5
    | .atomic (.b .anyAtomicType) => -0.5
    | .elem (some (.name _)) | .attr (some (.name _)) | .pi (some _) => 0
    | .elem (some _) | .attr (some _) => -0.25
    | .anyArr | .anyMap => -0.25
    | .record _ true => -0.25
    | .enum _ => 0.25
    | .atomic (.b b) => 0.5 - Float.pow 2 (-(Float.ofNat (derivDepth b)))
    | .choice ts =>
        let ps := ts.map (typePriority f)
        if ts.all (fun x => match x with | .atomic _ => true | _ => false) then
          ps.foldl max (-1) else 0
    | _ => 0.25

/-- Is this `.` under a chain of predicates? -/
def filterBase : Expr → Bool
  | .ctx => true
  | .filter a _ => filterBase a
  | _ => false

/-- The default priority of one pattern alternative (§6.4). -/
def defaultPriority (e : Expr) : Float :=
  let ofTest (ax : Axis) (t : NodeTest) : Float :=
    let t := match t with
      | .ncname n _ => NodeTest.name n
      | t => t
    match t with
    | .name (.name _) => 0
    | .name (.ns _) | .name (.loc _) => -0.25
    | .name .any => -0.5
    | .kind (.elem (some (.name _))) | .kind (.attr (some (.name _))) => 0
    | .kind (.elem (some (.ns _))) | .kind (.attr (some (.ns _))) => -0.25
    | .kind (.elem (some (.loc _))) | .kind (.attr (some (.loc _))) => -0.25
    | .kind (.pi (some _)) => 0
    | .kind (.doc (some (.elem (some (.name _))))) => 0
    | .kind (.doc (some _)) => -0.25
    | .kind _ => -0.5
    | .union _ => -0.5
    | _ => 0.5
  let _ := ofTest
  match e with
  | .step ax t [] => if isPatternAxis ax then ofTest ax t else 0.5
  | .root => -0.5
  | .ctx => -1
  | .filter a _ => if filterBase a then 1 else 0.5
  | .instOf .ctx ty => typePriority 50 ty
  | _ => 0.5

/-- A pattern argument: a variable reference or a literal (§6.3.2). -/
def patArgOk : Option Expr → Bool
  | some (.var _) | some (.lit _) => true
  | some (.neg (.lit _)) => true
  | _ => false

/-- The functions a pattern may call (§6.3.2). -/
def patFnOk (q : QN) (k : Nat) : Bool :=
  q.uri == nsFN && (match q.loc with
    | "doc" => k == 1 | "id" | "element-with-id" => k == 1 || k == 2
    | "key" => k == 2 || k == 3 | "root" => k == 0
    | _ => false)

/-- Static check of the forms XSLT allows in an XNode pattern (§6.3.2). -/
def patternOk : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | f + 1, top, e =>
    match e with
    | .bin .union a b | .bin .intersect a b | .bin .except a b => patternOk f top a && patternOk f top b
    | .seq [a] => patternOk f top a
    | .root => true
    | .ctx => top
    | .instOf .ctx _ => top
    | .filter a _ => patternOk f top a
    | .step ax _ _ => isPatternAxis ax
    | .var _ => true
    | .call q args kw => kw.isEmpty && patFnOk q args.length && args.all (fun a => patArgOk a)
    | .slash a b => patternOk f false a && patternOk f false b && (match b with
        | .var _ | .root => false
        | _ => true)
    | _ => false

/-! ## Walking expressions (for static checks) -/

/-- The operand expressions of an expression. -/
def exprKids : Expr → List Expr
  | .seq es | .arrS es | .tmpl es | .ext _ es _ _ _ | .step _ _ es => es
  | .slash a b | .filter a b | .bin _ a b | .smap a b | .pipe a b
  | .letE _ _ a b | .forE _ _ _ _ _ a b | .quant _ _ _ a b => [a, b]
  | .dstep _ e ps => e :: ps
  | .call _ as kw => as.filterMap id ++ kw.filterMap (·.2)
  | .dyn f as => f :: as.filterMap id
  | .mapArrow a g as => a :: g :: as.filterMap id
  | .inline _ _ b _ | .arrC b | .neg b | .plus b | .instOf b _ | .treat b _
  | .cast b _ _ | .castable b _ _ => [b]
  | .mapC es => es.flatMap (fun (k, v) => [k, v])
  | .lookup e k => e :: k.toList
  | .ulookup k => k.toList
  | .ifE c t e => [c, t, e]
  | _ => []

/-- Every subexpression (breadth first, `fuel` rounds). -/
def exprAll : Nat → List Expr → List Expr
  | 0, _ => []
  | _, [] => []
  | f + 1, es => es ++ exprAll f (es.flatMap exprKids)

/-- The names of the functions an expression calls statically or by a
    named function reference. -/
def exprCalls (e : Expr) : List QN :=
  (exprAll 10000 [e]).filterMap (fun x => match x with
    | .call q _ _ => some q
    | .fref q _ => some q
    | _ => none)

/-- The function of the XSLT grouping and merging family that a
    pattern must not call, with its error code (§14.2, §15.5). -/
def patternForbidden (e : Expr) : Option (String × String) :=
  (exprCalls e).findSome? (fun q =>
    if q.uri != nsFN then none else
    match q.loc with
    | "current-group" => some ("XTSE1060", "current-group")
    | "current-grouping-key" => some ("XTSE1070", "current-grouping-key")
    | "current-merge-group" => some ("XTSE3470", "current-merge-group")
    | "current-merge-key" | "current-merge-key-array" => some ("XTSE3500", q.loc)
    | _ => none)

/-- Parse a pattern. `~T` and `type(T)` (with predicates) are type
    patterns of the 4.0 draft that the test suite uses; `.` with
    predicates is a simple pattern (§6.3.3); everything else is read as
    the XPath expression of an XNode pattern. -/
def SCx.pattern0 (c : SCx) (src : String) : M Pattern := do
  let t := src.trimAscii.toString
  if t == "" then err "XTSE0340" "empty pattern" else
  let typed? : Option (String × Bool) :=
    if t.startsWith "~" then some ((t.drop 1).toString, false)
    else if t.startsWith "type(" then some ((t.drop 5).toString, true)
    else none
  match typed? with
  | some (rest, paren) =>
    let p : P (IType × Nat) := do
      let ty ← pItemType 1000
      if paren then expectS ")"
      ws
      pure (ty, ← get)
    match (p.run { s := rest.toList.toArray, ns := c.xpNs }).run 0 with
    | .ok ((ty, i), _) =>
      let ty := if c.xpathNs == "" then ty else itDefault c.xpathNs 50 ty
      let tail := String.ofList (rest.toList.drop i)
      let base : Expr := .instOf .ctx ty
      if tail.trimAscii.toString == "" then pure { e := base, src := t }
      else
        match c.parse ("." ++ tail) with
        | .ok e =>
          -- replace the `.` at the bottom of the predicate chain
          let rec swap : Nat → Expr → Expr
            | 0, e => e
            | f + 1, .filter a pr => .filter (swap f a) pr
            | _, .ctx => base
            | _, e => e
          pure { e := swap 100 e, src := t }
        | .error er => err "XTSE0340" ("invalid pattern '" ++ t ++ "': " ++ er.msg)
    | .error er => err "XTSE0340" ("invalid pattern '" ++ t ++ "': " ++ er.msg)
  | none =>
  match c.parse t with
  | .ok e => if patternOk 1000 true e then pure { e, src := t }
             else err "XTSE0340" ("'" ++ t ++ "' is not a pattern")
  | .error er => err "XTSE0340" ("invalid pattern '" ++ t ++ "': " ++ er.msg)

def SCx.pattern (c : SCx) (src : String) : M Pattern := do
  let p ← c.pattern0 src
  match patternForbidden p.e with
  | some (code, f) => err code (f ++ "() is used in the pattern '" ++ p.src ++ "'")
  | none => pure p

end L4Factoidal.XSLT4
