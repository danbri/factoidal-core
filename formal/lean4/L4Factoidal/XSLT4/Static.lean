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
deriving Inhabited

def SCx.backCompat (c : SCx) : Bool :=
  match c.version.toList with
  | '1' :: _ => true
  | _ => false

def SCx.forwardsCompat (c : SCx) : Bool :=
  match (c.version.splitOn ".").head?.bind String.toNat? with
  | some k => k > 4
  | none => false

/-- The bindings the XPath parser sees (no default namespace entry). -/
def SCx.xpNs (c : SCx) : List (String × String) :=
  (c.ns.filter (fun (p, _) => p != "")).foldl (fun acc (p, u) =>
    if acc.any (·.1 == p) then acc else acc ++ [(p, u)]) []

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

/-- Parse an XPath expression in the static context `c`. -/
def SCx.parse (c : SCx) (src : String) : M Expr := do
  let e ← match parseXPath src c.xpNs with
    | .ok e => pure e
    | .error er => throw { er with msg := er.msg ++ " in '" ++ src ++ "'" }
  pure (if c.xpathNs == "" then e else exprDefault c.xpathNs 100000 e)

/-- Parse a sequence type in the static context `c`. -/
def SCx.parseType (c : SCx) (src : String) : M IType := do
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

def SCx.avt (c : SCx) (s : String) : M Avt := do
  let parts ← splitTemplate s
  parts.mapM (fun (isE, t) => do
    if isE then
      if t.trimAscii.toString == "" then pure (AvtPart.lit "")
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

/-- The default priority of one pattern alternative (§6.4). -/
def defaultPriority (e : Expr) : Float :=
  let ofTest (ax : Axis) (t : NodeTest) : Float :=
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
  let _ := ofTest
  match e with
  | .step ax t [] => if isPatternAxis ax then ofTest ax t else 0.5
  | .root => -0.5
  | .ctx => -1
  | .filter .ctx _ => 1
  | _ => 0.5

/-- Parse a pattern. `.` with predicates and `atomic(T)` are simple
    patterns (§6.3.3, §6.3.4); everything else is read as the XPath
    expression of an XNode pattern. -/
def SCx.pattern (c : SCx) (src : String) : M Pattern := do
  let t := src.trimAscii.toString
  if t == "" then err "XTSE0340" "empty pattern" else
  match c.parse t with
  | .ok e => pure { e, src := t }
  | .error er => err "XTSE0340" ("invalid pattern '" ++ t ++ "': " ++ er.msg)

/-- Static check of the forms XSLT allows in an XNode pattern (§6.3.2). -/
def patternOk : Nat → Expr → Bool
  | 0, _ => false
  | f + 1, e =>
    match e with
    | .bin .union a b | .bin .intersect a b | .bin .except a b => patternOk f a && patternOk f b
    | .root | .ctx => true
    | .filter a _ => patternOk f a
    | .step ax _ _ => isPatternAxis ax
    | .var _ => true
    | .call _ _ _ => true
    | .slash a b => patternOk f a && patternOk f b
    | _ => false

end L4Factoidal.XSLT4
