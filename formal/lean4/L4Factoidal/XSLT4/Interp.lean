/-
L4Factoidal.XSLT4.Interp — the evaluation of a compiled stylesheet.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28). Section numbers below cite it.

`run` evaluates a sequence constructor to a list of `Out`; it is one
mutual definition with template invocation, parameter passing and
sorting, total by a FUEL argument that decreases on every nested call
(exhausting it is the dynamic error `FOER0000`). XPath expressions are
evaluated by `XPath4.eval`; the XSLT functions and the stylesheet
functions reach it through the host hook `Env.host`, built in
`XSLT4.Transform` from `run`.

The dynamic state that the XSLT functions read (`current()`, the
current group and grouping key, the regex groups, the current merge
group) is kept in variable bindings with names in the reserved
namespace `#xsl`, so an inline function item captures it with the
rest of its closure.
-/
import L4Factoidal.XSLT4.Compile

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-! ## Reserved bindings -/

def xv (l : String) : QN := { uri := "#xsl", loc := l }
def vCurrent : QN := xv "current"
def vGroup : QN := xv "group"
def vGroupKey : QN := xv "group-key"
def vRegex : QN := xv "regex"
def vSeed : QN := xv "seed"
def vMergeGroup : QN := xv "merge-group"
def vMergeKey : QN := xv "merge-key"
def vOutUri : QN := xv "output-uri"
/-- The current mode, for `fn:apply-templates` with `#current`. -/
def vMode : QN := xv "mode"
/-- The tunnel parameters in force, for `fn:apply-templates`. -/
def vTunnel : QN := xv "tunnel"

/-- The key of the map that stands for an `xsl:array-member` parcel. -/
def memberKey : Atomic := Atomic.ofQN (xv "array-member")

/-- The value bound to the grouping key when the current group has no
    grouping key. -/
def noGroupKey : Seq := [.atom (Atomic.ofQN (xv "no-group-key"))]

/-! ## State -/

structure XSt where
  /-- The base of the document numbers this run gives to new trees. -/
  base : Nat := 0
  counter : Nat := 0
  msgs : Array String := #[]
  /-- The messages as document nodes (§23.1). -/
  msgDocs : Array Item := #[]
  /-- Secondary results: href, value, output definition key, and the
      serialization parameters of the instruction. -/
  results : Array (String × Seq × String × List (String × String)) := #[]
  /-- `xsl:break` / `xsl:next-iteration` signal of the innermost
      `xsl:iterate`: `(isBreak, new parameter values)`. -/
  iterSignal : Option (Bool × List (QN × Seq)) := none
deriving Inhabited

abbrev XM := StateT XSt M

def xerr {α} (code msg : String) : XM α := throw { code, msg }

def liftX {α} (x : M α) : XM α := fun s => do let v ← x; pure (v, s)

/-- `x`, with any error replaced by error `code`. -/
def orErr {α} (x : M α) (code msg : String) : XM α :=
  match x with
  | .ok v => pure v
  | .error _ => xerr code msg

def orElseM {α} (x : M α) (d : α) : α :=
  match x with
  | .ok v => v
  | .error _ => d

def freshId : XM Nat := do
  let s ← get
  set { s with counter := s.counter + 1 }
  pure ((2 : Nat) ^ 44 + s.base * 1048576 + s.counter)

/-! ## The dynamic context of an instruction -/

structure Ctx where
  env : Env
  mode : String := "#unnamed"
  rule : Option Tmpl := none
  tunnel : List (QN × Seq) := []
  /-- In a stylesheet function (no current template rule, §10.3). -/
  inFn : Bool := false
  backCompat : Bool := false
  /-- Temporary output state (§25.2): in a variable, parameter or
      function body, `xsl:result-document` is an error. -/
  tempOut : Bool := false
deriving Inhabited

def Ctx.focus (cx : Ctx) (i : Item) (p sz : Nat) : Ctx := { cx with env := cx.env.focus i p sz }
def Ctx.bind (cx : Ctx) (q : QN) (v : Seq) : Ctx := { cx with env := cx.env.bind q v }
def Ctx.noFocus (cx : Ctx) : Ctx := { cx with env := { cx.env with ctx := none, pos := 0, size := 0 } }

/-- Evaluate an XPath expression of the stylesheet. -/
def evalX (cx : Ctx) (e : Expr) : XM Seq := do
  let s ← get
  set { s with counter := s.counter + 1 }
  let seed := s.base * 1048576 + s.counter
  let vars := (vSeed, sInt seed) :: cx.env.vars
  let vars := match cx.env.ctx with
    | some c => (vCurrent, c) :: vars
    | none => vars
  let vars := (vMode, [.atom (Atomic.ofStr cx.mode)]) :: vars
  let vars := if cx.tunnel.isEmpty then vars
    else (vTunnel, [.map (cx.tunnel.map (fun (q, v) => (Atomic.ofQN q, v)))]) :: vars
  match eval 100000 { cx.env with vars, compat10 := cx.backCompat } e with
  | .ok v => pure v
  | .error er =>
    -- in backwards-compatible mode a call of an unknown function is the
    -- dynamic error XTDE1425 (§3.9)
    if cx.backCompat && er.code == "XPST0017" then xerr "XTDE1425" er.msg else throw er

def evalBool (cx : Ctx) (e : Expr) : XM Bool := do
  liftX (ebv (← evalX cx e))

def atomStr (cx : Ctx) (s : Seq) : XM String := do
  let as ← liftX (cx.env.atomize s)
  pure (String.intercalate " " (as.map Atomic.str))

/-- The string value of an attribute value template. -/
def avtStr (cx : Ctx) (a : Avt) : XM String := do
  let mut out := ""
  for p in a do
    match p with
    | .lit s => out := out ++ s
    | .expr e => out := out ++ (← atomStr cx (← evalX cx e))
  pure out

def optAvtStr (cx : Ctx) (a : Option Avt) : XM (Option String) :=
  match a with
  | none => pure none
  | some x => some <$> avtStr cx x

/-- A type error of a conversion to a declared type, reported with the
    XSLT code of the construct (§9.4: XTTE0570 for variables, XTTE0590
    for parameters, XTTE0780 for function results). -/
def typeErrAs {α} (code : String) (x : M α) : M α :=
  match x with
  | .error e => if code != "" && (e.code == "XPTY0004" || e.code == "FORG0001") then .error { e with code } else .error e
  | ok => ok

/-! ## Values of sequence constructors -/

/-- The items of a list of `Out` (new trees get new document numbers). -/
def materializeAll (env : Env) (os : List Out) : XM Seq := do
  let mut out : Array Item := #[]
  for o in os do
    match o with
    | .item i => out := out.push i
    | o =>
      let id ← freshId
      out := out.push (← liftX (materialize env id o))
  pure out.toList

/-- The string value of an `Out` that is a node. -/
def outString (env : Env) : Nat → Out → String
  | 0, _ => ""
  | f + 1, o =>
    match o with
    | .item (.node n) => env.nodeString n
    | .item (.atom a) => a.str
    | .item _ => ""
    | .elem _ _ cs | .doc cs _ => String.join (cs.map (fun c => match c with
        | .attr .. | .nsN .. | .comment .. | .pi .. => ""
        | .item (.node n) =>
            let k := (env.nrec n).kind
            if k == .attribute || k == .namespace || k == .comment || k == .pi then "" else env.nodeString n
        | .item (.atom a) => a.str
        | c => outString env f c))
    | .attr _ v | .text v | .comment v | .pi _ v | .nsN _ v => v

/-- §5.7.2 constructing simple content: zero-length text nodes are
    removed, adjacent text nodes merged, the rest atomized, the parts
    joined with `sep`. -/
def simpleContent (env : Env) (os : List Out) (sep : String) : XM String := do
  let mut parts : Array String := #[]
  let mut prevText := false
  for o in os do
    let (isText, strs) ← match o with
      | .text s => pure (true, [s])
      | .item (.node n) =>
          if (env.nrec n).kind == .text then pure (true, [env.nodeString n])
          else pure (false, [env.nodeString n])
      | .item (.atom a) => pure (false, [a.str])
      | .item (.arr ms) => do
          let as ← liftX (env.atomize [.arr ms])
          pure (false, as.map Atomic.str)
      | .item _ => xerr "FOTY0013" "a function item cannot be atomized"
      | o => pure (false, [outString env 10000 o])
    if isText then
      let s := strs.headD ""
      if s == "" then continue
      if prevText then
        parts := parts.pop.push (parts.back! ++ s)
      else parts := parts.push s
      prevText := true
    else
      for s in strs do parts := parts.push s
      prevText := false
  pure (String.intercalate sep parts.toList)

/-! ## Patterns (§6.3) -/

def _root_.L4Factoidal.XPath4.Env.parentOf (e : Env) (n : NodeRef) : Option NodeRef :=
  (e.nrec n).parent.map (n.at ·)

/-- Does one step of a pattern match node `n`? Predicates are evaluated
    over the nodes of the same axis from the parent (or, for a node
    with no parent, over the node alone). -/
def stepMatches (env : Env) (ax : Axis) (t : NodeTest) (preds : List Expr) (n : NodeRef) : M Bool := do
  let r := env.nrec n
  let axOk := match ax with
    | .attribute => r.kind == .attribute
    | .namespace => r.kind == .namespace
    | .child | .descendant =>
        r.kind != .attribute && r.kind != .namespace &&
        (r.kind != .document || (match t with | .kind (.doc _) => true | _ => false))
    | _ => true
  if !axOk then return false
  let ax' := if ax == .self || ax == .descendantOrSelf then
      (if r.kind == .attribute then Axis.attribute else Axis.child) else ax
  if !(env.testMatches ax' n t) then return false
  if preds.isEmpty then return true
  match (if r.kind == .document then none else env.parentOf n) with
  | some p =>
      let ax2 := if ax' == .attribute then Axis.attribute else if ax' == .namespace then .namespace else .child
      let res ← eval 100000 (env.focus (.node p) 1 1) (.step ax2 t preds)
      pure (res.any (fun i => match i with | .node m => m == n | _ => false))
  | none =>
      let res ← eval 100000 (env.focus (.node n) 1 1) (.step .self t preds)
      pure (res.any (fun i => match i with | .node m => m == n | _ => false))

def isDos : Expr → Bool
  | .step .descendantOrSelf (.kind .anyNode) [] => true
  | _ => false

mutual
/-- Does item `it` match the pattern expression `p`? -/
def patMatch (env : Env) : Nat → Expr → Item → M Bool
  | 0, _, _ => pure false
  | f + 1, p, it =>
    match p with
    | .seq [a] => patMatch env f a it
    | .bin .union a b => do
        if ← patMatch env f a it then pure true else patMatch env f b it
    | .bin .intersect a b => do
        if ← patMatch env f a it then patMatch env f b it else pure false
    | .bin .except a b => do
        if ← patMatch env f a it then (do pure !(← patMatch env f b it)) else pure false
    | .ctx => pure true
    | .instOf .ctx ty => pure (env.itemMatches it ty)
    | .filter .ctx pr => do
        let r ← eval 100000 (env.focus it 1 1) (.filter .ctx pr)
        pure !r.isEmpty
    | .filter (.seq [a]) pr => do
        -- a predicate on a parenthesized XNode pattern (§6.3.2.2): the
        -- node is in `root(.)//((a)[pr])`, or `((a)[pr])` evaluated at
        -- the root when `a` is rooted
        let .node n := it | return false
        let rt := env.treeRoot n
        let rooted := match (exprFlat 1000 a).head? with
          | some .root | some (.call ..) | some (.var _) => true
          | _ => false
        let whole : Expr := .filter (.seq [a]) pr
        let e := if rooted then whole else .slash (.step .descendantOrSelf (.kind .anyNode) []) whole
        let r ← eval 100000 (env.focus (.node rt) 1 1) e
        pure (r.any (fun i => match i with | .node m => m == n | _ => false))
    | .filter a pr => do
        -- a predicate on a function call
        if !(← patMatch env f a it) then return false
        let r ← eval 100000 (env.focus it 1 1) (.filter .ctx pr)
        pure !r.isEmpty
    | _ =>
      match it with
      | .node n => pathMatch env f (exprFlat 1000 p).reverse n
      | _ => pure false

/-- Match the steps of a path pattern, last step first. -/
def pathMatch (env : Env) : Nat → List Expr → NodeRef → M Bool
  | 0, _, _ => pure false
  | f + 1, steps, n =>
    match steps with
    | [] => pure true
    | [s] => headMatch env f s n
    | (.seq [u]) :: rest => pathMatch env f (u :: rest) n
    | (.bin .union a b) :: rest => do
        -- `x/(a|b)` is `x/a | x/b`
        if !rest.isEmpty then
          if ← pathMatch env f (a :: rest) n then pure true else pathMatch env f (b :: rest) n
        else patMatch env f (.bin .union a b) (.node n)
    | (.step ax t preds) :: rest =>
      if ax == .descendant || ax == .descendantOrSelf then do
        -- the context of the step is an ancestor (or self) that matches
        -- the rest of the pattern, and from it the step selects `n`
        let r := env.nrec n
        if r.kind == .attribute || r.kind == .namespace then return false
        let cands := if ax == .descendantOrSelf then n :: env.ancestors n else env.ancestors n
        for a in cands do
          if ← pathMatch env f rest a then
            let res ← eval 100000 (env.focus (.node a) 1 1) (.step ax t preds)
            if res.any (fun i => match i with | .node m => m == n | _ => false) then return true
        pure false
      else pathMatchStep env f (.step ax t preds) rest n
    | s :: rest => pathMatchStep env f s rest n

/-- Match the last step `s` against `n`, then the rest against its
    parent (or, after `//`, an ancestor). -/
def pathMatchStep (env : Env) : Nat → Expr → List Expr → NodeRef → M Bool
  | 0, _, _, _ => pure false
  | f + 1, s, rest, n => do
      if !(← headMatch env f s n) then return false
      match env.parentOf n with
      | none => pure false
      | some p =>
        match rest with
        | d :: rest' =>
          if isDos d then
            -- `//`: some ancestor-or-self of the parent matches the rest
            let cands := p :: env.ancestors p
            for a in cands do
              if ← pathMatch env f rest' a then return true
            pure false
          else pathMatch env f rest p
        | [] => pure true

/-- Match one step (or the head of a rooted path) against `n`. -/
def headMatch (env : Env) : Nat → Expr → NodeRef → M Bool
  | 0, _, _ => pure false
  | f + 1, s, n =>
    match s with
    | .step ax t preds => stepMatches env ax t preds n
    | .seq [a] => headMatch env f a n
    | .root => pure ((env.nrec n).kind == .document)
    | .bin .union _ _ | .bin .intersect _ _ | .bin .except _ _ | .filter _ _ => patMatch env f s (.node n)
    | e => do
      -- a variable reference or a function call (id, key, doc, root,
      -- element-with-id): the node must be in its value, evaluated with
      -- the node as context
      let r ← eval 100000 (env.focus (.node n) 1 1) e
      pure (r.any (fun i => match i with | .node m => m == n | _ => false))
end

/-- Does an item match a 4.0 item pattern (§6.3.3 to §6.3.9)? An error
    in a predicate makes the pattern not match (§6.5). -/
def ipMatch (env : Env) : Nat → IPat → Item → Bool
  | 0, _, _ => false
  | f + 1, ip, it =>
    -- does a value match a sequence pattern (§6.3.5)?
    let seqOk (m : Option IPat) (o : Occ) (v : Seq) : Bool :=
      match m with
      | none => v.isEmpty
      | some q =>
        let n := v.length
        (match o with | .one => n == 1 | .opt => n ≤ 1 | .star => true | .plus => n ≥ 1) &&
        v.all (fun x => ipMatch env f q x)
    match ip with
    | .xnode e => (patMatch env 200 e it).toOption.getD false
    | .any => true
    | .types t => env.itemMatches it t
    | .mapP es open_ =>
      match it with
      | .map kvs =>
        es.all (fun (k, sp) => match kvs.find? (fun (ka, _) => atomicEqual ka k) with
          | none => false
          | some (_, v) => match sp with
            | none => true
            | some (m, o) => seqOk m o v) &&
        (open_ || kvs.all (fun (ka, _) => es.any (fun (k, _) => atomicEqual ka k)))
      | _ => false
    | .arrayP m o =>
      match it with
      | .arr ms => ms.all (seqOk m o)
      | _ => false
    | .jnodeP k m o =>
      match it with
      | .jnode .. =>
        (match k with
          | none => true
          | some ka => (jkeyOf it).any (atomicEqual · ka)) &&
        seqOk m o (jvalOf it)
      | _ => false
    | .filtered q preds =>
      ipMatch env f q it && preds.all (fun pr =>
        match eval 100000 (env.focus it 1 1) (.filter .ctx pr) with
        | .ok r => !r.isEmpty
        | .error _ => false)

/-- Pattern matching with errors masked (§6.5). -/
def Pattern.matches (p : Pattern) (env : Env) (it : Item) : Bool :=
  -- `current()` in a pattern is the item being matched (§20.4.1)
  -- and the current captured groups are empty in a pattern (§17.2.1)
  let env := { env with vars := (vCurrent, [it]) :: (vRegex, [.map []]) :: env.vars }
  match p.ip with
  | some (ip, _) => ipMatch env 200 ip it
  | none =>
  match patMatch env 200 p.e it with
  | .ok b => b
  | .error _ => false

/-! ## Template rules (§6.6, §6.8) -/

def modeHas (t : Tmpl) (mode : String) : Bool :=
  t.modes.contains mode || t.modes.contains "#all"

/-- A quick test that the last step of a template's pattern can match
    `it` (element and attribute names), before the full match. -/
def quickOk (env : Env) (t : Tmpl) (it : Item) : Bool :=
  match t.pat with
  | none => false
  | some p =>
    match it with
    | .node n =>
      let r := env.nrec n
      let last := match (exprFlat 1000 p.e).getLast? with
        | some (.step ax (.ncname nt _) ps) => some (Expr.step ax (.name nt) ps)
        | x => x
      match last with
      | some (.step .child (.name (.name q)) _) => r.kind == .element && r.name.loc == q.loc
      | some (.step .attribute (.name (.name q)) _) => r.kind == .attribute && r.name.loc == q.loc
      | some (.step .child (.name _) _) => r.kind == .element
      | some (.step .attribute (.name _) _) => r.kind == .attribute
      | some (.step .child (.kind .text) _) => r.kind == .text
      | some .root => r.kind == .document
      | _ => true
    | _ =>
      match p.e with
      | .step .. | .root | .slash .. => false
      | _ => true

def ruleBetter (a b : Tmpl) : Bool :=
  a.prec > b.prec || (a.prec == b.prec && (a.prio > b.prio || (a.prio == b.prio && a.order > b.order)))

/-- The best template rule for `it` in `mode`, among the rules that
    `ok` admits. -/
def findRule (S : Sheet) (env : Env) (mode : String) (it : Item) (ok : Tmpl → Bool := fun _ => true) :
    M (Option Tmpl) := do
  let mut best : Option Tmpl := none
  let mut tie := false
  for t in S.templates do
    if !modeHas t mode || !ok t || !quickOk env t it then continue
    let some p := t.pat | continue
    if !(p.matches env it) then continue
    match best with
    | none => best := some t; tie := false
    | some b =>
      if t.prec == b.prec && t.prio == b.prio && b.id != t.id then tie := true
      if ruleBetter t b then
        if !(t.prec == b.prec && t.prio == b.prio) then tie := false
        best := some t
  if tie && (S.mode mode).onMultiple == "fail" then
    err "XTDE0540" "several template rules match with the same precedence and priority"
  pure best

/-! ## Sorting (§13) -/

structure SortSpec where
  desc : Bool := false
  dataType : String := ""
  caseOrder : String := ""
  collation : String := ""
  /-- The collation of string comparisons. -/
  coll : Coll := .codepoint
deriving Inhabited

def cmpAtom (coll : Coll) (tz : Int) (x y : Atomic) : Ordering :=
  let nanX := (x.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
  let nanY := (y.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
  if nanX && nanY then .eq else if nanX then .lt else if nanY then .gt else
  let strLike (a : Atomic) := a.isStringLike || a.ty == .untyped
  if strLike x && strLike y && !coll.isCodepoint then coll.compare x.str y.str else
  match atomicCmp x y tz with
  | .ok (some c) => c
  | _ => compare x.str y.str

/-- Can two sort key values be compared (§13.1.2, XTDE1030)? -/
def sortComparable (tz : Int) (x y : Atomic) : Bool :=
  let nan (a : Atomic) := (a.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
  nan x || nan y || (match atomicCmp x y tz with
    | .ok (some _) => true
    | _ => false)

/-- Compare two sort key values; 4.0 (§13.1.2): a key value is a
    sequence, compared item by item, a shorter prefix first. -/
def cmpSeqKey (coll : Coll) (tz : Int) : List Atomic → List Atomic → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match cmpAtom coll tz x y with
    | .eq => cmpSeqKey coll tz xs ys
    | o => o

def cmpKey (sp : SortSpec) (tz : Int) (a b : List Atomic) : Ordering :=
  let o := cmpSeqKey sp.coll tz a b
  if sp.desc then o.swap else o

def cmpKeys (sps : List SortSpec) (tz : Int) : List (List Atomic) → List (List Atomic) → Ordering
  | a :: as, b :: bs =>
    match sps with
    | sp :: rest =>
      match cmpKey sp tz a b with
      | .eq => cmpKeys rest tz as bs
      | o => o
    | [] => .eq
  | _, _ => .eq

/-- Normalise a sort key value (§13.1.2). -/
def sortKeyAtom (dataType : String) (as : List Atomic) : M (List Atomic) := do
  as.mapM (fun a =>
    if dataType == "number" then
      match castAtomic (if a.ty == .untyped then Atomic.ofStr a.str else a) (.b .double) with
      | .ok d => pure d
      | .error _ => pure (Atomic.ofDbl (0.0 / 0.0))
    else if dataType == "text" then pure (Atomic.ofStr a.str)
    else pure (if a.ty == .untyped then Atomic.ofStr a.str else a))

/-! ## Grouping keys -/

/-- A string that is equal for two atomic values when they are equal
    under the grouping rules (§14.4: `eq`, with NaN equal to NaN, and
    untyped values compared as strings). -/
def groupKeyStr (a : Atomic) : String :=
  if a.ty == .untyped || a.isStringLike then "s:" ++ a.str
  else match a.num? with
    | some n => let f := n.toFloat
                if f.isNaN then "n:NaN" else "n:" ++ toString f
    | none => match a.v with
      | .bool b => "b:" ++ toString b
      | _ => "x:" ++ a.ty.name ++ ":" ++ a.str

/-! ## Built-in template rules (§6.10) -/

def _root_.L4Factoidal.XPath4.Env.kindOf (e : Env) (i : Item) : Option NKind :=
  match i with
  | .node n => some (e.nrec n).kind
  | _ => none

def _root_.L4Factoidal.XPath4.Env.childItems (e : Env) (n : NodeRef) : Seq := (e.axis .child n).map Item.node
def _root_.L4Factoidal.XPath4.Env.attrItems (e : Env) (n : NodeRef) : Seq := (e.axis .attribute n).map Item.node

/-- The namespace bindings of an element to copy with it (§11.9.1). -/
def _root_.L4Factoidal.XPath4.Env.elemDecls (e : Env) (n : NodeRef) : List (String × String) :=
  ((e.nrec n).inscope.foldl (fun acc (p, u) => if acc.any (·.1 == p) then acc else acc ++ [(p, u)]) []).filter
    (fun (p, _) => p != "xml")

/-! ## Numbering (§12) -/

/-- Split an `xsl:number` format into its prefix, the alphanumeric
    format tokens with the separators before them, and the suffix. -/
def numberFormatParts (fmt : String) : String × List (String × String) × String := Id.run do
  let isAl (c : Char) := c.isAlphanum || c.toNat > 127 && !(c.toNat ≥ 0x2000 && c.toNat ≤ 0x206F)
  let cs := fmt.toList
  let mut toks : Array (Bool × String) := #[]
  for c in cs do
    let a := isAl c
    match toks.back? with
    | some (b, s) => if a == b then toks := toks.pop.push (b, s.push c) else toks := toks.push (a, String.singleton c)
    | none => toks := toks.push (a, String.singleton c)
  let tl := toks.toList
  let (pre, tl1) := match tl with
    | (false, s) :: r => (s, r)
    | r => ("", r)
  let (suf, tl2) := match tl1.reverse with
    | (false, s) :: r => if r.isEmpty then ("", tl1) else (s, r.reverse)
    | _ => ("", tl1)
  let mut out : List (String × String) := []
  let mut sep := ""
  for (a, s) in tl2 do
    if a then out := out ++ [(sep, s)]; sep := ""
    else sep := s
  if out.isEmpty then out := [("", "1")]
  return (pre, out, suf)

def groupDigits (s : String) (sep : String) (size : Nat) : String :=
  if size == 0 || sep == "" || !(s.toList.all Char.isDigit) then s else
  let cs := s.toList.reverse
  let rec go : List Char → Nat → List Char → List Char
    | [], _, acc => acc
    | c :: r, k, acc => go r (k + 1) (if k > 0 && k % size == 0 then c :: (sep.toList.reverse ++ acc) else c :: acc)
  String.ofList (go cs 0 [])


def lookupVar (vs : List (QN × Seq)) (q : QN) : Option Seq :=
  (vs.find? (fun (v, _) => v == q)).map (·.2)

/-! ## Regular expressions (§17) -/

/-- A segment of the input of `xsl:analyze-string`: matching or not, its
    string, and (for a matching segment) its captured groups, group zero
    first (§17.2.1). -/
structure ASPart where
  isMatch : Bool
  str : String
  groups : List (Atomic × Seq) := []

/-- The matching segment `sg` of `input` as a part: its string, and its
    captured groups with group zero first. -/
def matchPart (input : List Nat) (re : Re4) (sg : Seg) : ASPart :=
  let whole := cpsStr (Regex.slice input sg.start sg.stop)
  let g0 : Atomic × Seq := (Atomic.ofInt 0, [.map [(Atomic.ofStr "value", sStr whole),
    (Atomic.ofStr "position", sInt (sg.start + 1)), (Atomic.ofStr "nr", sInt 0), (Atomic.ofStr "name", [])]])
  { isMatch := true, str := whole, groups := g0 :: groupRecords input re sg.caps }

/-- The parts from offset `cur`: each matching segment, after the
    non-matching segment before it, and the rest of the input. -/
def partsFrom (input : List Nat) (re : Re4) : Nat → List Seg → List ASPart
  | cur, [] =>
    if input.length > cur then [{ isMatch := false, str := cpsStr (Regex.slice input cur input.length) }] else []
  | cur, sg :: rest =>
    (if sg.start > cur then [{ isMatch := false, str := cpsStr (Regex.slice input cur sg.start) }] else []) ++
    matchPart input re sg :: partsFrom input re (max cur sg.stop) rest

/-- The segments that `xsl:analyze-string` processes (§17.1): the
    matching segments of `fn:matching-segments` (`XPath4.segments`), with
    the non-matching segments between them. -/
def analyzeParts (s : String) (re : Re4) : List ASPart :=
  let input := s.toList.map Char.toNat
  partsFrom input re 0 (segments re.r input)

/-- The numbering sequences of single characters that `xsl:number`
    knows beyond `fn:format-integer` (§12.4: implementation-defined
    sequences): name, the character for zero if Unicode has one, and the
    ranges of consecutive code points (first number, last number, code
    point of the first). -/
def numberingSequences : List (String × Option Nat × List (Nat × Nat × Nat)) := [
  ("CIRCLED DIGIT ONE", some 0x24EA, [(1, 20, 0x2460), (21, 35, 0x3251), (36, 50, 0x32B1)]),
  ("PARENTHESIZED DIGIT ONE", none, [(1, 20, 0x2474)]),
  ("DIGIT ONE FULL STOP", some 0x1F100, [(1, 20, 0x2488)]),
  ("DINGBAT NEGATIVE CIRCLED DIGIT ONE", some 0x24FF, [(1, 10, 0x2776), (11, 20, 0x24EB)]),
  ("DINGBAT CIRCLED SANS-SERIF DIGIT ONE", some 0x1F10B, [(1, 10, 0x2780)]),
  ("DINGBAT NEGATIVE CIRCLED SANS-SERIF DIGIT ONE", some 0x1F10C, [(1, 10, 0x278A)]),
  ("DOUBLE CIRCLED DIGIT ONE", none, [(1, 10, 0x24F5)]),
  ("DIGIT ONE COMMA", some 0x1F101, [(1, 9, 0x1F102)]),
  ("PARENTHESIZED IDEOGRAPH ONE", none, [(1, 10, 0x3220)]),
  ("CIRCLED IDEOGRAPH ONE", none, [(1, 10, 0x3280)]),
  ("SINHALA ARCHAIC DIGIT ONE", none, [(1, 10, 0x111E1)]),
  ("RUMI DIGIT ONE", none, [(1, 10, 0x10E60)]),
  ("COPTIC EPACT DIGIT ONE", none, [(1, 10, 0x102E1)]),
  ("BRAHMI NUMBER ONE", none, [(1, 10, 0x11052)]),
  ("AEGEAN NUMBER ONE", none, [(1, 10, 0x10107)]),
  ("MENDE KIKAKUI DIGIT ONE", none, [(1, 9, 0x1E8C7)]),
  ("COUNTING ROD UNIT DIGIT ONE", none, [(1, 9, 0x1D360)])]

/-- A number in a sequence of `numberingSequences` whose first character
    is `tok`; `none` if `tok` starts no such sequence. A number outside
    the sequence is written in decimal digits (§12.4). -/
def seqNumber (tok : String) (x : Int) : Option String :=
  match tok.toList with
  | [c] =>
    (numberingSequences.find? (fun (_, _, rs) => rs.head?.any (fun (lo, _, cp) => lo == 1 && cp == c.toNat))).map
      (fun (_, zero, rs) =>
        let n := x.toNat
        if x == 0 then match zero with
          | some z => String.singleton (Char.ofNat z)
          | none => "0"
        else match rs.find? (fun (lo, hi, _) => lo ≤ n && n ≤ hi) with
          | some (lo, _, cp) => String.singleton (Char.ofNat (cp + (n - lo)))
          | none => toString x)
  | _ => none

/-- One number of `xsl:number` in the format token `tok` (§12.4): the
    F&O 4.0 function `fn:format-integer`, with `;o` for an ordinal. -/
def formatOne (env : Env) (x : Int) (tok : String) (ordS lng : Option String) : M String := do
  let pic := match ordS with
    | some o => if o == "" || o == "no" then tok else tok ++ ";o"
    | none => tok
  if x < 0 then pure "NaN" else
  if let some t := (if ordS.isNone then seqNumber tok x else none) then pure t else do
    let r ← callFn 100000 env { uri := nsFN, loc := "format-integer" }
      [sInt x, sStr pic, match lng with | some l => sStr l | none => []]
    pure (match r with | [.atom a] => a.str | _ => toString x)

/-- The text of `xsl:number` (§12.4): the format string split into a
    prefix, format tokens with their separators, and a suffix; each
    number formatted by `formatOne`, then grouped. -/
def numberText (env : Env) (nums : List Int) (fs : String) (gs gz ordS lng : Option String) : M String := do
  let (pre, toks, suf) := numberFormatParts fs
  let mut out := pre
  let mut i := 0
  for x in nums do
    let (sep, tok) := toks.getD i (toks.getLast?.getD (".", "1"))
    let sep := if i == 0 then "" else (if i < toks.length then (if sep == "" then "." else sep) else (match toks.reverse with
      | (s, _) :: _ => if s == "" then "." else s
      | [] => "."))
    let fmtd ← formatOne env x tok ordS lng
    let fmtd := match gs, gz with
      | some g, some z => groupDigits fmtd g ((z.toNat?).getD 0)
      | _, _ => fmtd
    out := out ++ sep ++ fmtd
    i := i + 1
  pure (out ++ suf)

/-! ## Helpers of the instructions -/

/-- Not "deemed empty" (§8.5.1). -/
def nodeNonEmpty (env : Env) (nd : NodeRef) : Bool :=
  let r := env.nrec nd
  match r.kind with
  | .element | .document => !r.children.isEmpty
  | .text | .comment | .pi | .attribute => r.value != ""
  | _ => true

def isNCName (x : String) : Bool :=
  match x.toList with
  | c :: cs => isNameStart c && cs.all (fun d => isNameCh d && d != ':')
  | [] => false

def Ctx.bindAll (cx : Ctx) (vs : List (QN × Seq)) : Ctx :=
  vs.foldl (fun c (q, v) => c.bind q v) cx

/-- The local name of an error code given as an EQName or QName (the
    error codes of `XPath4.Err` carry no namespace). -/
def errLocal (c : String) : String :=
  let c := c.trimAscii.toString
  if c.startsWith "Q{" then
    match (c.drop 2).toString.splitOn "}" with
    | [u, l] => if u == nsERR then l else "Q{" ++ u ++ "}" ++ l
    | _ => c
  else match c.splitOn ":" with
    | [_, l] => l
    | _ => c

/-- The error code of `xsl:message` and `xsl:assert`: the given code
    when it is an EQName or a lexical QName, else the default (§23.1). -/
def validCode (c dflt : String) : String :=
  -- a code from a value template carries the namespaces after a NUL
  let (c, ns) : String × Option (List (String × String)) := match c.splitOn "\x00" with
    | [a, b] => (a, some ((b.splitOn "\x01").filterMap (fun (kv : String) => match kv.splitOn "=" with
        | p :: rest => some (p, String.intercalate "=" rest)
        | [] => none)))
    | _ => (c, none)
  let c := c.trimAscii.toString
  if c.startsWith "Q{" && c.contains '}' then errLocal c
  else match c.splitOn ":", ns with
    | [l], some _ => if isNCName l then "Q{}" ++ l else dflt
    | [l], none => if isNCName l then l else dflt
    | [p, l], some ns =>
      if !(isNCName p && isNCName l) then dflt else
      match ns.lookup p with
      | some u => if u == nsERR then l else "Q{" ++ u ++ "}" ++ l
      | none => dflt
    | [p, l], none => if isNCName p && isNCName l then errLocal c else dflt
    | _, _ => dflt

/-- The expanded name of `xsl:element` or `xsl:attribute` (§11.2.2,
    §11.3): from the lexical name, the namespace attribute, and the
    namespace bindings of the instruction. -/
def resolveName (name : String) (ns : Option Avt) (scope : List (String × String)) (isElem : Bool)
    (cx : Ctx) (badName undeclared : String) : XM QN := do
  let (p, l) ← match name.splitOn ":" with
    | [l] => pure ("", l)
    | [p, l] => pure (p, l)
    | _ => xerr badName ("invalid name '" ++ name ++ "'")
  if !isNCName l || (p != "" && !isNCName p) then
    if name.startsWith "Q{" && name.contains '}' then
      match (name.drop 2).toString.splitOn "}" with
      | [u, l2] => return { uri := u, loc := l2 }
      | _ => pure ()
    xerr badName ("invalid name '" ++ name ++ "'")
  match ns with
  | some a =>
      let u ← avtStr cx a
      if !isElem && u == "" then return { uri := "", loc := l }
      let p := if !isElem && p == "" && u != "" then "" else p
      pure { uri := u, loc := l, pfx := if p == "xmlns" then "" else p }
  | none =>
      if p == "" then
        if isElem then pure { uri := (scope.lookup "").getD "", loc := l }
        else pure { uri := "", loc := l }
      else if p == "xml" then pure { uri := nsXML, loc := l, pfx := p }
      else match scope.lookup p with
        | some u => pure { uri := u, loc := l, pfx := p }
        | none => xerr undeclared ("undeclared namespace prefix '" ++ p ++ "'")

/-- The evaluated attributes of `xsl:sort`s. -/
def sortSpecs (cx : Ctx) (sorts : List SortK) : XM (List SortSpec) :=
  sorts.mapM (fun k => match k with
    | .mk _ _ order lang dt co coll st => do
      let o ← optAvtStr cx order
      -- the value of lang must be a language code (XTDE0030)
      if let some lg ← optAvtStr cx lang then
        if !(lg == "" || lg.toList.all (fun ch => ch.isAlphanum || ch == '-')) then
          xerr "XTDE0030" ("invalid language '" ++ lg ++ "' in xsl:sort")
      if let some sv ← optAvtStr cx st then
        if !(["yes", "no", "true", "false", "1", "0"].contains sv.trimAscii.toString) then
          xerr "XTDE0030" ("invalid stable value '" ++ sv ++ "' in xsl:sort")
      let d ← optAvtStr cx dt
      let c ← optAvtStr cx co
      let cl ← optAvtStr cx coll
      match o with
      | some v => if v != "ascending" && v != "descending" then xerr "XTDE0030" ("invalid sort order '" ++ v ++ "'")
      | none => pure ()
      -- the collation: the attribute, else the default collation; with
      -- case-order and no collation, the UCA with that case order
      let curi := cl.getD cx.env.defaultCollation
      let coll ← match collationOf cx.env.baseUri curi with
        | .ok k => pure k
        | .error _ => xerr "XTDE1035" ("unknown collation " ++ curi ++ " in xsl:sort")
      let coll := match cl, c with
        | none, some "upper-first" => Coll.uca { upperFirst := true }
        | none, some "lower-first" => Coll.uca {}
        | _, _ => coll
      pure { desc := o == some "descending", dataType := d.getD "", caseOrder := c.getD "",
             collation := cl.getD "", coll })

/-- The groups of `xsl:for-each-group` (§14): (key, items), in order of
    first appearance. -/
def makeGroups (cx : Ctx) (s : Seq) (kind : GroupKind) (key : Option Expr) (pat : Option Pattern)
    (composite : Bool) (coll : Coll := .codepoint) : XM (List (Seq × Seq)) := do
  let env := cx.env
  -- string keys are equal when their collation keys are equal
  let groupKeyStr (a : Atomic) : String :=
    if (a.ty == .untyped || a.isStringLike) && !coll.isCodepoint then
      "s:" ++ String.intercalate "," ((coll.key a.str).map toString)
    else groupKeyStr a
  let sz := s.length
  match kind with
  | .by =>
    let some ke := key | xerr "XTSE1080" "group-by needs an expression"
    let mut keys : Array (String × Seq) := #[]
    let mut idx : Std.HashMap String Nat := {}
    let mut members : Array (Array Item) := #[]
    let mut k := 1
    for it in s do
      let as ← liftX (env.atomize (← evalX (cx.focus it k sz) ke))
      -- values compared with `eq` across timezones (dates and times)
      -- take the key string of an equal key already seen
      let canon (a : Atomic) : String :=
        match a.v with
        | .x (.dt _ _) =>
          match keys.toList.find? (fun (_, kv) => match kv with
              | [.atom b] => (match atomicCmp a b env.tz with | .ok (some .eq) => true | _ => false)
              | _ => false) with
          | some (k0, _) => k0
          | none => groupKeyStr a
        | _ => groupKeyStr a
      let ks : List (String × Seq) := if composite
        then [(String.intercalate "\x00" (as.map groupKeyStr), as.map Item.atom)]
        else as.map (fun a => (canon a, [Item.atom a]))
      let mut seen : List String := []
      for (ks0, kv) in ks do
        if seen.contains ks0 then continue
        seen := ks0 :: seen
        match idx.get? ks0 with
        | some g => members := members.set! g (members[g]!.push it)
        | none =>
          idx := idx.insert ks0 keys.size
          keys := keys.push (ks0, kv)
          members := members.push #[it]
      k := k + 1
    pure ((keys.toList.zip members.toList).map (fun ((_, kv), m) => (kv, m.toList)))
  | .adjacent =>
    let some ke := key | xerr "XTSE1080" "group-adjacent needs an expression"
    let mut out : Array (String × Seq × Array Item) := #[]
    let mut k := 1
    for it in s do
      let as ← liftX (env.atomize (← evalX (cx.focus it k sz) ke))
      let (ks0, kv) ← if composite then pure (String.intercalate "\x00" (as.map groupKeyStr), as.map Item.atom)
        else match as with
          | [a] => pure (groupKeyStr a, [Item.atom a])
          | _ => xerr "XTTE1100" "a group-adjacent key must be a single atomic value"
      match out.back? with
      | some (k0, kv0, g) =>
          if k0 == ks0 then out := out.pop.push (k0, kv0, g.push it)
          else out := out.push (ks0, kv, #[it])
      | none => out := out.push (ks0, kv, #[it])
      k := k + 1
    pure (out.toList.map (fun (_, kv, g) => (kv, g.toList)))
  | .startingWith | .endingWith =>
    let some p := pat | xerr "XTSE1080" "a grouping pattern is needed"
    let mut out : Array (Array Item) := #[]
    let mut openG := false
    for it in s do
      let hit := p.matches env it
      if kind == .startingWith then
        if hit || out.isEmpty then out := out.push #[it]
        else out := out.pop.push (out.back!.push it)
      else
        if !openG then out := out.push #[it] else out := out.pop.push (out.back!.push it)
        openG := !hit
    pure (out.toList.map (fun g => ([], g.toList)))
  | .splitWhen | .mergeWhen =>
    let some ke := key | xerr "XTSE1080" "split-when needs an expression"
    let mut out : Array (Array Item) := #[]
    let mut prev : Option Item := none
    let mut k := 1
    for it in s do
      match prev with
      | none => out := out.push #[it]
      | some pv =>
        let g := out.back!.toList
        let gcx := ((cx.focus it k sz).bind { uri := "", loc := "group" } g).bind { uri := "", loc := "next" } [it]
        let gcx := gcx.bind { uri := "", loc := "prev" } [pv]
        let b ← evalBool gcx ke
        let split := if kind == .splitWhen then b else !b
        if split then out := out.push #[it] else out := out.pop.push (out.back!.push it)
      prev := some it
      k := k + 1
    pure (out.toList.map (fun g => ([], g.toList)))

/-- The default `count` pattern of `xsl:number` (§12.2): nodes of the
    same kind and name as `n`. -/
def sameKindName (env : Env) (n m : NodeRef) : Bool :=
  let a := env.nrec n
  let b := env.nrec m
  a.kind == b.kind && (a.kind == .text || a.kind == .comment || a.kind == .document ||
    (a.name.uri == b.name.uri && a.name.loc == b.name.loc))

/-- The place numbers of `xsl:number` without `value` (§12.2). -/
def numberNodes (env : Env) (n : NodeRef) (level : String) (cnt frm : Option Pattern) : List Nat :=
  let counts (m : NodeRef) : Bool := match cnt with
    | some p => p.matches env (.node m)
    | none => sameKindName env n m
  let froms (m : NodeRef) : Bool := match frm with
    | some p => p.matches env (.node m)
    | none => false
  let ancs := n :: env.ancestors n
  -- ancestors-or-self up to (not beyond) the first that matches `from`
  let upTo := (ancs.takeWhile (fun a => !froms a))
  let upTo := if frm.isSome then upTo else ancs
  let sibNum (a : NodeRef) : Nat :=
    ((env.axis .precedingSibling a).filter counts).length + 1
  match level with
  | "multiple" =>
      (upTo.filter counts).reverse.map sibNum
  | "any" =>
      -- the nodes before n (preceding and ancestors) and n itself, after
      -- the last node that matches `from`
      let before := (env.axis .preceding n) ++ env.ancestors n
      let before := before.mergeSort (fun a b => a.idx ≥ b.idx)
      let rec takeTill : List NodeRef → List NodeRef → List NodeRef
        | [], acc => acc
        | x :: r, acc => if froms x then acc else takeTill r (x :: acc)
      let region := takeTill before []
      let c := (region.filter counts).length + (if counts n then 1 else 0)
      if c == 0 then [] else [c]
  | _ =>
      match upTo.find? counts with
      | some a => [sibNum a]
      | none => []

mutual

/-- Evaluate a sequence constructor. -/
def run : Nat → Sheet → Ctx → List Instr → XM (List Out)
  | 0, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, is => do
    let mut cx := cx
    let mut out : Array (Option (List Out)) := #[]
    let mut pending : List (Nat × Bool × Ctx × Instr) := []
    for ins in is do
      if (← get).iterSignal.isSome then break
      match ins with
      | .var q ty sel body =>
          let v ← bindValue n S cx sel body ty ("$" ++ q.show) "XTTE0570"
          cx := cx.bind q v
      | .onEmpty _ _ => pending := pending ++ [(out.size, true, cx, ins)]; out := out.push none
      | .onNonEmpty _ _ => pending := pending ++ [(out.size, false, cx, ins)]; out := out.push none
      | _ => out := out.push (some (← run1 n S cx ins))
    if pending.isEmpty then
      return (out.toList.filterMap id).flatten
    -- §8.5: xsl:on-empty / xsl:on-non-empty depend on the other results
    let others := (out.toList.filterMap id).flatten
    let empty := others.all (fun o => match o with
      | .text "" => true
      | .doc [] _ => true
      | .item (.atom a) => a.str == "" && a.isStringLike
      | _ => false)
    let mut res : Array (List Out) := out.toList.map (·.getD []) |>.toArray
    for (pos, isEmpty, pcx, pins) in pending do
      match pins with
      | .onEmpty sel body | .onNonEmpty sel body =>
          if isEmpty == empty then
            let v ← match sel with
              | some e => do pure (Out.ofSeq (← evalX pcx e))
              | none => run n S pcx body
            res := res.set! pos v
      | _ => pure ()
    return res.toList.flatten

/-- The value of a variable, parameter or with-param (§9.3). -/
def bindValue : Nat → Sheet → Ctx → Option Expr → List Instr → Option IType → String → String → XM Seq
  | 0, _, _, _, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, sel, body, ty, what, code => do
    let v ← match sel with
      | some e => evalX cx e
      | none =>
        if body.isEmpty then
          pure (if ty.isSome then [] else sStr "")
        else
          let os ← run n S { cx with tempOut := true } body
          match ty with
          | none => do
              let id ← freshId
              pure [← liftX (materialize cx.env id (.doc os ""))]
          | some _ => materializeAll cx.env os
    match ty with
    | some t => liftX (typeErrAs code (cx.env.coerce t v what))
    | none => pure v

def run1 : Nat → Sheet → Ctx → Instr → XM (List Out)
  | 0, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, ins => do
    let env := cx.env
    match ins with
    | .lit s => pure [.text s]
    | .tvt parts =>
        let mut s := ""
        for p in parts do
          match p with
          | .lit t => s := s ++ t
          | .expr e => s := s ++ (← atomStr cx (← evalX cx e))
        pure [.text s]
    | .valueOf sel sep body first =>
        match sel with
        | some e =>
            let v ← evalX cx e
            let v := if first then v.take 1 else v
            let sp ← match sep with | some a => avtStr cx a | none => pure " "
            -- constructing simple content (§5.7.2): zero-length text
            -- nodes are removed and adjacent text nodes merged
            if first then
              let as ← liftX (env.atomize v)
              pure [.text (String.intercalate sp (as.map Atomic.str))]
            else pure [.text (← simpleContent env (Out.ofSeq v) sp)]
        | none =>
            let os ← run n S cx body
            let sp ← match sep with | some a => avtStr cx a | none => pure ""
            pure [.text (← simpleContent env os sp)]
    | .seq sel body ty =>
        let os ← match sel with
          | some e => do pure (Out.ofSeq (← evalX cx e))
          | none => run n S cx body
        match ty with
        | none => pure os
        | some t =>
            let v ← materializeAll env os
            pure (Out.ofSeq (← liftX (env.coerce t v "xsl:sequence result")))
    | .lre q decls ats useSets body =>
        let alias (u : String) : Option (String × String) :=
          (S.nsAliases.find? (fun (su, _, _) => su == u)).map (fun (_, p, r) => (p, r))
        let q := match alias q.uri with
          | some (p, r) => { q with uri := r, pfx := p }
          | none => q
        let decls := decls.filterMap (fun (p, u) =>
          if S.nsAliases.any (fun (_, _, r) => r == u) && !(alias u).isSome then
            -- a result namespace of an alias is copied only through the alias
            some (p, u)
          else match alias u with
            | some (p', r) => some (if p == "" then (p', r) else (p', r))
            | none => some (p, u))
        let mut content : Array Out := #[]
        for o in ← attrSetOuts n S cx useSets do content := content.push o
        for (aq, v) in ats do
          let aq := match alias aq.uri with
            | some (p, r) => if aq.uri == "" then aq else { aq with uri := r, pfx := p }
            | none => aq
          content := content.push (.attr aq (← avtStr cx v))
        for o in ← run n S cx body do content := content.push o
        pure [.elem q decls content.toList]
    | .elem nm ns scope useSets body =>
        let name ← avtStr cx nm
        let name := name.trimAscii.toString
        let q ← resolveName name ns scope true cx "XTDE0820" "XTDE0830"
        let mut content : Array Out := #[]
        for o in ← attrSetOuts n S cx useSets do content := content.push o
        for o in ← run n S cx body do content := content.push o
        pure [.elem q [] content.toList]
    | .attr nm ns scope sel sep body =>
        let name := (← avtStr cx nm).trimAscii.toString
        let q ← resolveName name ns scope false cx "XTDE0850" "XTDE0860"
        if q.uri == "" && q.loc == "xmlns" then xerr "XTDE0855" "an attribute cannot be named xmlns"
        if q.uri == "http://www.w3.org/2000/xmlns/" then xerr "XTDE0865" "an attribute cannot be in the xmlns namespace"
        let v ← match sel with
          | some e => do
              let sp ← match sep with | some a => avtStr cx a | none => pure " "
              let s ← evalX cx e
              let s := if cx.backCompat then s.take 1 else s
              let as ← liftX (env.atomize s)
              pure (String.intercalate sp (as.map Atomic.str))
          | none => do
              let sp ← match sep with | some a => avtStr cx a | none => pure ""
              simpleContent env (← run n S cx body) sp
        pure [.attr q v]
    | .comment sel body =>
        let v ← contentString n S cx sel body
        -- §11.8: a space after a hyphen that would end or double one
        let v := (v.replace "--" "- -").replace "--" "- -"
        let v := if v.endsWith "-" then v ++ " " else v
        pure [.comment v]
    | .pi nm sel body =>
        let name := (← avtStr cx nm).trimAscii.toString
        if !isNCName name || name.toLower == "xml" then
          xerr "XTDE0890" ("invalid processing-instruction name '" ++ name ++ "'")
        let v ← contentString n S cx sel body
        let v := (v.replace "?>" "? >").dropWhile Char.isWhitespace |>.toString
        pure [.pi name v]
    | .nsI nm sel body =>
        let p := (← avtStr cx nm).trimAscii.toString
        if p != "" && !isNCName p then xerr "XTDE0920" ("invalid namespace prefix '" ++ p ++ "'")
        if p == "xmlns" then xerr "XTDE0920" "the prefix xmlns cannot be declared"
        let u ← contentString n S cx sel body
        if u == "" then xerr "XTDE0930" "a namespace node cannot have an empty URI"
        if u == "http://www.w3.org/2000/xmlns/" then xerr "XTDE0905" "the xmlns namespace cannot be bound"
        if (p == "xml") != (u == nsXML) then xerr "XTDE0925" "the xml prefix and namespace go together"
        pure [.nsN p u]
    | .docI body => pure [.doc (← run n S cx body) ""]
    | .applyT sel mode sorts params sep =>
        let s ← match sel with
          | some e => evalX cx e
          | none => match env.ctx with
            | some [.node c] => pure (env.childItems c)
            | some [_] => xerr "XTTE0510" "xsl:apply-templates with no select needs a node as context item"
            | _ => xerr "XPDY0002" "xsl:apply-templates with no select needs a context item"
        let s ← if sorts.isEmpty then pure s else sortSeq n S cx s sorts
        let m := if mode == "#current" then cx.mode else mode
        let (ps, tps) ← evalParams n S cx params
        let sp ← optAvtStr cx sep
        applyT n S cx s m ps (tps ++ cx.tunnel.filter (fun (q, _) => !tps.any (·.1 == q))) sp
    | .callT name params =>
        let cands := S.templates.toList.filter (fun t => t.name == some name)
        let best := cands.foldl (fun (b : Option Tmpl) t => match b with
          | none => some t
          | some x => if t.prec > x.prec then some t else some x) none
        match best with
        | none => xerr "XTSE0650" ("no template named " ++ name.show)
        | some t =>
          let (ps, tps) ← evalParams n S cx params
          let tun := tps ++ cx.tunnel.filter (fun (q, _) => !tps.any (·.1 == q))
          for p in params do
            if !p.tunnel && !t.params.any (fun tp => tp.name == p.name && !tp.tunnel) && !cx.backCompat then
              xerr "XTSE0680" ("template " ++ name.show ++ " has no parameter $" ++ p.name.show)
          let cx' := if t.ctxAbsent then cx.noFocus else cx
          invoke n S cx' t ps tun
    | .applyImports params | .nextMatch params =>
        match cx.rule, env.ctx with
        | some r, some [it] =>
          let isNext := match ins with | .nextMatch _ => true | _ => false
          let ok : Tmpl → Bool := if isNext
            then fun t => t.id != r.id && ruleBetter r t
            else fun t => t.prec < r.prec
          let (ps, tps) ← evalParams n S cx params
          let tun := tps ++ cx.tunnel.filter (fun (q, _) => !tps.any (·.1 == q))
          match ← liftX (findRule S env cx.mode it ok) with
          | some t => invoke n S cx t ps tun
          | none => builtin n S cx it cx.mode ps tun
        | none, _ => xerr "XTDE0560" "no current template rule"
        | _, _ => xerr "XTDE0560" "no current template rule"
    | .forEach sel sorts body sep =>
        let s ← evalX cx sel
        let s ← if sorts.isEmpty then pure s else sortSeq n S cx s sorts
        let sz := s.length
        let sp ← optAvtStr cx sep
        let mut out : Array Out := #[]
        let mut k := 1
        for it in s do
          if k > 1 then if let some t := sp then out := out.push (.text t)
          for o in ← run n S ({ cx.focus it k sz with rule := none }) body do out := out.push o
          k := k + 1
        pure out.toList
    | .forEachGroup sel kind key pat composite collA sorts body =>
        let s ← evalX cx sel
        -- the collation of string keys (§14.4; XTDE1110 if unknown)
        let curi := (← optAvtStr cx collA).getD cx.env.defaultCollation
        let coll ← match collationOf cx.env.baseUri curi with
          | .ok k => pure k
          | .error _ => xerr "XTDE1110" ("unknown collation " ++ curi ++ " in xsl:for-each-group")
        let groups ← makeGroups cx s kind key pat composite coll
        -- sort the groups: the sort keys see the group as current-group
        let groups ← if sorts.isEmpty then pure groups else do
          let mut keyed : Array (List (List Atomic) × (Seq × Seq)) := #[]
          let specs ← sortSpecs cx sorts
          let gsz := groups.length
          let mut gi := 1
          for (k, g) in groups do
            let gcx := ((cx.focus (g.headD default) gi gsz).bind vGroup g).bind vGroupKey
              (if kind == .by || kind == .adjacent then k else noGroupKey)
            keyed := keyed.push ((← sortKeysOf n S gcx sorts specs), (k, g))
            gi := gi + 1
          let tz := env.tz
          pure ((keyed.toList.mergeSort (fun a b => cmpKeys specs tz a.1 b.1 != .gt)).map (·.2))
        let gsz := groups.length
        let mut out : Array Out := #[]
        let mut gi := 1
        -- with group-starting-with, group-ending-with, split-when and
        -- merge-when there is no grouping key (XTDE1071)
        let keyed := kind == .by || kind == .adjacent
        for (k, g) in groups do
          let gcx := ((cx.focus (g.headD default) gi gsz).bind vGroup g).bind vGroupKey (if keyed then k else noGroupKey)
          for o in ← run n S { gcx with rule := none } body do out := out.push o
          gi := gi + 1
        pure out.toList
    | .ifI test th el body =>
        if ← evalBool cx test then
          match th with
          | some e => do pure (Out.ofSeq (← evalX cx e))
          | none => run n S cx body
        else match el with
          | some e => do pure (Out.ofSeq (← evalX cx e))
          | none => pure []
    | .choose whens other =>
        for (t, b) in whens do
          if ← evalBool cx t then return ← run n S cx b
        match other with
        | some b => run n S cx b
        | none => pure []
    | .switch sel whens other =>
        let v ← liftX (env.atomize (← evalX cx sel))
        let v ← match v with
          | [a] => pure (some a)
          | [] => pure none
          | _ => xerr "XPTY0004" "the select value of xsl:switch must be at most one atomic value"
        for (t, b) in whens do
          let ws ← liftX (env.atomize (← evalX cx t))
          let hit := ws.any (fun w => match v with
            | some a => deepAtomEq a w
            | none => false)
          if hit then return ← run n S cx b
        match other with
        | some b => run n S cx b
        | none => pure []
    | .var _ _ _ _ => pure []
    | .copy sel copyNs _ useSets body =>
        let it? ← match sel with
          | some e => do
              let s ← evalX cx e
              match s with
              | [] => pure none
              | [i] => pure (some i)
              | _ => xerr "XTTE3180" "the select of xsl:copy must give at most one item"
          | none => match env.ctx with
            | some [i] => pure (some i)
            | _ => xerr "XTTE0945" "xsl:copy needs a context item"
        match it? with
        | none => pure []
        | some it =>
          let cx' := match sel with
            | some _ => cx.focus it 1 1
            | none => cx
          match it with
          | .node nd =>
            let r := env.nrec nd
            match r.kind with
            | .element =>
                let mut content : Array Out := #[]
                for o in ← attrSetOuts n S cx' useSets do content := content.push o
                for o in ← run n S cx' body do content := content.push o
                pure [.elem r.name (if copyNs then env.elemDecls nd else []) content.toList]
            | .document => pure [.doc (← run n S cx' body) (env.doc nd).uri]
            | .text => pure [.text r.value]
            | .attribute => pure [.attr r.name r.value]
            | .comment => pure [.comment r.value]
            | .pi => pure [.pi r.name.loc r.value]
            | .namespace => pure [.nsN r.name.loc r.value]
          | other => pure [.item other]
    | .copyOf sel copyNs =>
        let s ← evalX cx sel
        let mut out : Array Out := #[]
        for it in s do
          match it with
          | .node nd =>
            if !copyNs && (env.nrec nd).kind == .element then
              let id ← freshId
              out := out.push (.item (← liftX (copyAsTree env id nd false)))
            else out := out.push (.item it)
          | _ => out := out.push (.item it)
        pure out.toList
    | .message sel body term code =>
        -- the message: the select value followed by the content (§23.1)
        let t := (← avtStr cx term).trimAscii.toString
        let content : XM (String × List Item) := do
          let os1 ← match sel with
            | some e => do pure (Out.ofSeq (← evalX cx e))
            | none => pure []
          let os := os1 ++ (← run n S cx body)
          let txt ← simpleContent env os ""
          let id ← freshId
          let mdoc ← match materialize env id (.doc os "") with
            | .ok d => pure [d]
            | .error _ => pure []
          pure (txt, mdoc)
        -- a dynamic error in the content does not make the transformation
        -- fail; the message then reports the error (§23.1)
        let st0 ← get
        let (txt, mdoc) ← match content.run st0 with
          | .ok (r, st1) => do set st1; pure r
          | .error e =>
            if parseBool t == some true then throw e
            else pure ("error " ++ e.code ++ ": " ++ e.msg, [])
        modify (fun s => { s with msgs := s.msgs.push txt, msgDocs := s.msgDocs ++ mdoc.toArray })
        match parseBool t with
        | some true =>
            let c ← match code with
              | some a => avtStr cx a
              | none => pure "XTMM9000"
            xerr (validCode c "XTMM9000") txt
        | some false => pure []
        | none => xerr "XTDE0030" ("invalid terminate value '" ++ t ++ "'")
    | .assertI test sel body code =>
        if ← evalBool cx test then pure []
        else
          let os ← match sel with
            | some e => do pure (Out.ofSeq (← evalX cx e))
            | none => run n S cx body
          let txt ← simpleContent env os ""
          let c ← match code with
            | some a => avtStr cx a
            | none => pure "XTMM9001"
          xerr (validCode c "XTMM9001") txt
    | .number value sel level cnt frm fmt lang ord startAt gsep gsize =>
        let nums ← match value with
          | some e => do
              let as ← liftX (env.atomize (← evalX cx e))
              as.mapM (fun a => do
                let d := orElseM (castAtomic (if a.ty == .untyped then Atomic.ofStr a.str else a) (.b .double)) (Atomic.ofDbl (0.0/0.0))
                let f := (d.num?.map Num.toFloat).getD (0.0/0.0)
                if f.isNaN || f.isInf || f < -0.5 then
                  if cx.backCompat then pure (-1 : Int) else
                  xerr "XTDE0980" ("xsl:number value " ++ a.str ++ " is not a positive number")
                else pure (Int.ofNat (Float.round (if f < 0 then 0 else f)).toUInt64.toNat))
          | none => do
              let nd ← match sel with
                | some e => do
                    match ← evalX cx e with
                    | [.node x] => pure x
                    | _ => xerr "XTTE1000" "the select of xsl:number must give one node"
                | none => match env.ctx with
                  | some [.node x] => pure x
                  | _ => xerr "XTTE0990" "xsl:number needs a node as context item"
              let nums := numberNodes env nd level cnt frm
              pure (nums.map Int.ofNat)
        let start ← match startAt with
          | some a => do
              let t ← avtStr cx a
              pure ((tokens t).map (fun x => (x.toInt?).getD 1))
          | none => pure [1]
        let nums := nums.zipIdx.map (fun (x, i) => if x < 0 then x else x + (start.getD i (start.getLast?.getD 1)) - 1)
        let fs ← avtStr cx fmt
        let gs ← optAvtStr cx gsep
        let gz ← optAvtStr cx gsize
        let ordS ← optAvtStr cx ord
        let lng ← optAvtStr cx lang
        pure [.text (← liftX (numberText env nums fs gs gz ordS lng))]
    | .iterate sel params onComp body =>
        let s ← evalX cx sel
        -- initial parameter values
        let mut pv : List (QN × Seq) := []
        for p in params do
          let v ← bindValue n S (cx.bindAll pv) p.sel p.body p.ty ("$" ++ p.name.show) "XTTE0590"
          pv := pv ++ [(p.name, v)]
        let sz := s.length
        let mut out : Array Out := #[]
        let mut k := 1
        let mut broke := false
        let saved := (← get).iterSignal
        for it in s do
          modify (fun st => { st with iterSignal := none })
          let icx := (cx.focus it k sz).bindAll pv
          let os ← run n S { icx with rule := none } body
          for o in os do out := out.push o
          match (← get).iterSignal with
          | some (true, _) => broke := true; break
          | some (false, nv) =>
              pv := pv.map (fun (q, v) => match nv.find? (·.1 == q) with
                | some (_, v') => (q, v')
                | none => (q, v))
          | none => pure ()
          k := k + 1
        modify (fun st => { st with iterSignal := saved })
        if !broke then
          match onComp with
          | some (sel?, b) =>
              let ccx := (cx.noFocus).bindAll pv
              match sel? with
              | some e => for i in ← evalX ccx e do out := out.push (.item i)
              | none => for o in ← run n S ccx b do out := out.push o
          | none => pure ()
        pure out.toList
    | .breakI sel body =>
        let os ← match sel with
          | some e => do pure (Out.ofSeq (← evalX cx e))
          | none => run n S cx body
        modify (fun st => { st with iterSignal := some (true, []) })
        pure os
    | .nextIteration params =>
        let (ps, _) ← evalParams n S cx params
        modify (fun st => { st with iterSignal := some (false, ps) })
        pure []
    | .tryI sel body catches =>
        let st0 ← get
        let attempt : XM (List Out) := do
          let os ← match sel with
            | some e => do pure (Out.ofSeq (← evalX cx e))
            | none => run n S cx body
          -- dynamic errors inside the try must be raised here: the
          -- result is made into items now
          let _ ← materializeAll cx.env (os.filter (fun o => match o with | .item _ => false | _ => true))
          pure os
        match attempt.run st0 with
        | .ok (os, st1) => set st1; pure os
        | .error e =>
          set st0
          let code := e.code
          let (eu, el) := if code.startsWith "Q{" then
              match (code.drop 2).toString.splitOn "}" with
              | [u, l] => (u, l)
              | _ => (nsERR, code)
            else if e.uri == "#none" then ("", code)
            else if e.uri != "" then (e.uri, code)
            else (nsERR, code)
          let hit := catches.find? (fun (errs, _, _) => errs.any (fun t =>
            t == "*" || t == "*:" ++ el || t == "Q{" ++ eu ++ "}*" || t == "Q{" ++ eu ++ "}" ++ el))
          match hit with
          | none => throw e
          | some (_, csel, cbody) =>
            let ecx := ((((cx.bind { uri := nsERR, loc := "code" } [.atom (Atomic.ofQN { uri := eu, loc := el, pfx := "err" })]).bind
              { uri := nsERR, loc := "description" } (sStr e.msg)).bind
              { uri := nsERR, loc := "value" } []).bind
              { uri := nsERR, loc := "module" } []).bind
              { uri := nsERR, loc := "line-number" } []
            let ecx := (ecx.bind { uri := nsERR, loc := "column-number" } []).bind { uri := nsERR, loc := "additional" } []
            let ecx := ecx.bind { uri := nsERR, loc := "map" } [.map [(Atomic.ofStr "code", [.atom (Atomic.ofQN { uri := eu, loc := el, pfx := "err" })]),
              (Atomic.ofStr "description", sStr e.msg)]]
            match csel with
            | some e2 => do pure (Out.ofSeq (← evalX ecx e2))
            | none => run n S ecx cbody
    | .analyzeString sel rx fl ms ns =>
        -- the input is coerced to xs:string; () is "" (§17.1)
        let s ← match ← liftX (env.atomize (← evalX cx sel)) with
          | [] => pure ""
          | [a] =>
            if a.isStringLike || a.ty == .untyped then pure a.str
            else xerr "XPTY0004" ("xsl:analyze-string needs a string, not xs:" ++ a.ty.name)
          | _ => xerr "XPTY0004" "xsl:analyze-string needs a single string"
        let pat ← avtStr cx rx
        let flags ← avtStr cx fl
        -- invalid flags are XTDE1145, an invalid pattern XTDE1140 (§17.1)
        let badFlags := match compileRe4 pat flags with
          | .error er => er.code == "FORX0001"
          | .ok _ => false
        if badFlags then xerr "XTDE1145" ("invalid regular expression flags '" ++ flags ++ "'")
        let re ← orErr (compileRe4 pat flags) "XTDE1140" ("invalid regular expression '" ++ pat ++ "'")
        -- the disjoint matching segments of F&O 4.0 (fn:matching-segments)
        -- with the non-matching segments between them
        let parts := analyzeParts s re
        let sz := parts.length
        let mut out : Array Out := #[]
        let mut k := 1
        for p in parts do
          let rcx := (cx.focus (.atom (Atomic.ofStr p.str)) k sz).bind vRegex [.map p.groups]
          let b := if p.isMatch then ms else ns
          match b with
          | some body => for o in ← run n S { rcx with rule := none } body do out := out.push o
          | none => pure ()
          k := k + 1
        pure out.toList
    | .mapI sel body dups =>
        let v ← match sel with
          | some e => evalX cx e
          | none => do materializeAll env (← run n S cx body)
        let dupF ← match dups with
          | some e => do pure (some (← evalX cx e))
          | none => pure none
        let mut acc : MB := {}
        for it in v do
          -- a JNode whose value is a map stands for that map (4.0)
          let it := match it with
            | .jnode _ _ [m@(.map _)] _ => m
            | other => other
          match it with
          | .map kvs =>
            for (k, x) in kvs do
              match acc.get? k with
              | some old =>
                -- 4.0 duplicates: a function of the old and new values (a
                -- function of one argument gets the old value only), or
                -- one of the map:merge policies (§21.1.2)
                match dupF with
                | some [.atom pol] =>
                  match pol.str with
                  | "use-first" | "use-any" => pure ()
                  | "use-last" => acc := acc.set k x
                  | "combine" => acc := acc.set k (old ++ x)
                  | "reject" => xerr "XTDE3365" ("duplicate key " ++ k.str ++ " in xsl:map")
                  | other => xerr "XTDE3366" ("invalid duplicates value '" ++ other ++ "'")
                | some [f] =>
                  let args := if f.fnArity == some 1 then [old] else [old, x]
                  acc := acc.set k (← liftX (apply 100000 env f args))
                | _ => xerr "XTDE3365" ("duplicate key " ++ k.str ++ " in xsl:map")
              | none => acc := acc.set k x
          | _ => xerr "XTTE3375" "the content of xsl:map must be maps"
        pure [.item (.map acc.toList)]
    | .mapEntry key sel body =>
        let ks ← liftX (env.atomize (← evalX cx key))
        let k ← match ks with
          | [k] => pure k
          | _ => xerr "XTTE3375" "the key of xsl:map-entry must be a single atomic value"
        let v ← match sel with
          | some e => evalX cx e
          | none => do materializeAll env (← run n S cx body)
        pure [.item (.map [(k, v)])]
    | .arrayI fe sel body =>
        let unwrap (s : Seq) : List Seq := s.map (fun it => match it with
          | .map [(k, v)] => if deepAtomEq k memberKey then v else [it]
          | _ => [it])
        match fe with
        | none =>
            let s ← match sel with
              | some e => evalX cx e
              | none => do materializeAll env (← run n S cx body)
            pure [.item (.arr (unwrap s))]
        | some fe =>
            let fs ← evalX cx fe
            let sz := fs.length
            let mut ms : Array Seq := #[]
            let mut k := 1
            for it in fs do
              let icx := cx.focus it k sz
              let s ← match sel with
                | some e => evalX icx e
                | none => do materializeAll env (← run n S icx body)
              match s with
              | [.map [(key, v)]] => ms := ms.push (if deepAtomEq key memberKey then v else s)
              | _ => ms := ms.push s
              k := k + 1
            pure [.item (.arr ms.toList)]
    | .arrayMember sel body =>
        let s ← match sel with
          | some e => evalX cx e
          | none => do materializeAll env (← run n S cx body)
        pure [.item (.map [(memberKey, s)])]
    | .evaluate xp ctxE wp nsE ty params scope baseUri =>
        let src ← atomStr cx (← evalX cx xp)
        -- with namespace-context, the namespaces of that node, and its
        -- default namespace for unprefixed element names (§20.1.1)
        let (ns, dflt) ← match nsE with
          | some e => do
              match ← evalX cx e with
              | [.node nd] =>
                let sc := effScope (env.nrec nd).inscope
                pure (sc.filter (·.1 != ""), (sc.lookup "").getD "")
              | _ => xerr "XTTE3170" "namespace-context must be a single node"
          | none => pure (scope, "")
        let e ← match parseXPath src ns with
          | .ok e => pure (if dflt == "" then e else exprDefault dflt 100000 e)
          | .error er => xerr "XTDE3160" ("xsl:evaluate: " ++ er.code ++ " " ++ er.msg)
        let mut vars : List (QN × Seq) := []
        match wp with
        | some w =>
            match ← evalX cx w with
            | [.map kvs] =>
              for (k, v) in kvs do
                match k.v with
                | .qn q => vars := (q, v) :: vars
                | _ => xerr "XTTE3165" "the keys of with-params must be QNames"
            | [] => pure ()
            | _ => xerr "XTTE3165" "with-params must be a map"
        | none => pure ()
        let (ps, _) ← evalParams n S cx params
        vars := ps ++ vars
        let ctxV ← match ctxE with
          | some c => do
              match ← evalX cx c with
              | [] => pure none
              | [i] => pure (some [i])
              | _ => xerr "XTTE3210" "context-item must be a single item"
          | none => pure none
        let evars := vars.reverse ++ env.vars.filter (fun (q, _) => q.uri == "#xsl")
        -- current() in the target expression is the context item of the
        -- xsl:evaluate instruction
        let evars := match env.ctx with
          | some c => (vCurrent, c) :: evars
          | none => evars
        let one := if ctxV.isSome then 1 else 0
        let ebase := if baseUri == "" then env.baseUri else baseUri
        let env' : Env := { env with vars := evars, ctx := ctxV, pos := one, size := one, ns, baseUri := ebase }
        let r ← match eval 100000 env' e with
          | .ok v => pure v
          | .error er =>
            if er.code.startsWith "XPST" then xerr "XTDE3160" ("xsl:evaluate: " ++ er.code ++ " " ++ er.msg)
            else throw er
        let r ← match ty with
          | some t => liftX (env.coerce t r "xsl:evaluate result")
          | none => pure r
        pure (Out.ofSeq r)
    | .resultDoc href fmt ser body =>
        if cx.tempOut then xerr "XTDE1480" "xsl:result-document is not allowed in temporary output state"
        let h ← match href with
          | some a => avtStr cx a
          | none => pure ""
        let f ← match fmt with
          | some a => do
              let s ← avtStr cx a
              let q ← liftX (lexQName env.ns s false "XTDE1460")
              pure q.eqn
          | none => pure ""
        let mut sp : List (String × String) := []
        for (k, a) in ser do sp := sp ++ [(k, ← avtStr cx a)]
        let os ← run n S cx body
        let id ← freshId
        let meth := match sp.lookup "method" with
          | some m => m
          | none => ((S.outputs.lookup f).bind (·.lookup "method")).getD ""
        let buildTree := match sp.lookup "build-tree" with
          | some b => parseBool b != some false
          | none => meth != "json" && meth != "adaptive"
        let v ← if !buildTree then materializeAll env os else match os with
          | [] => pure []
          | _ => do pure [← liftX (materialize env id (.doc os ""))]
        let st ← get
        if st.results.any (fun (x, _, _, _) => x == h) then
          xerr "XTDE1490" ("two result documents with the URI '" ++ h ++ "'")
        set { st with results := st.results.push (h, v, f, sp) }
        pure []
    | .wherePopulated body =>
        let os ← run n S cx body
        pure (os.filter (fun o => match o with
          | .elem _ _ cs => cs.any (fun c => match c with | .attr .. | .nsN .. => false | _ => true)
          | .doc cs _ => !cs.isEmpty
          | .text "" => false
          | .item (.node nd) => nodeNonEmpty env nd
          | _ => true))
    | .onEmpty _ _ | .onNonEmpty _ _ => pure []
    | .performSort sel sorts body =>
        let s ← match sel with
          | some e => evalX cx e
          | none => do materializeAll env (← run n S cx body)
        pure (Out.ofSeq (← sortSeq n S cx s sorts))
    | .merge srcs action =>
        let mut rows : Array (List (List Atomic) × String × Item) := #[]
        let mut specs : List SortSpec := []
        for src in srcs do
          match src with
          | .mk name fei fes sel sortBefore keys =>
            let anchors : Seq ← match fei, fes with
              | some e, _ => evalX cx e
              | none, some e => do
                  let uris ← liftX (env.atomize (← evalX cx e))
                  let mut ds : Array Item := #[]
                  for u in uris do
                    for d in ← liftX (callFn 100000 env { uri := nsFN, loc := "doc" } [sStr u.str]) do ds := ds.push d
                  pure ds.toList
              | none, none => pure (match env.ctx with | some [i] => [i] | _ => [])
            let anchors := if fei.isNone && fes.isNone && anchors.isEmpty then [default] else anchors
            let ks ← sortSpecs cx keys
            specs := ks
            for a in anchors do
              let acx := if fei.isNone && fes.isNone && env.ctx.isNone then cx else cx.focus a 1 1
              let items ← evalX acx sel
              let items ← if sortBefore then sortSeq n S acx items keys else pure items
              let sz := items.length
              let mut k := 1
              for it in items do
                let kv ← sortKeysOf n S (acx.focus it k sz) keys ks
                rows := rows.push (kv, name, it)
                k := k + 1
        let tz := env.tz
        let sorted := rows.toList.mergeSort (fun a b => cmpKeys specs tz a.1 b.1 != .gt)
        -- group rows with equal keys
        let mut groups : Array (List (List Atomic) × Array (String × Item)) := #[]
        for (kv, nm, it) in sorted do
          match groups.back? with
          | some (k0, g) =>
              if cmpKeys (specs.map (fun s => { s with desc := false })) tz k0 kv == .eq then
                groups := groups.pop.push (k0, g.push (nm, it))
              else groups := groups.push (kv, #[(nm, it)])
          | none => groups := groups.push (kv, #[(nm, it)])
        let mut out : Array Out := #[]
        let gsz := groups.size
        let mut gi := 1
        for (kv, g) in groups.toList do
          let items := g.toList.map (·.2)
          let named : Seq := g.toList.map (fun (nm, it) => .arr [[.atom (Atomic.ofStr nm)], [it]])
          let keyV : Seq := kv.flatten.map Item.atom
          let gcx := ((cx.focus (items.headD default) gi gsz).bind vMergeGroup named).bind vMergeKey keyV
          let gcx := gcx.bind vGroup items
          for o in ← run n S { gcx with rule := none } action do out := out.push o
          gi := gi + 1
        pure out.toList
    | .sourceDoc href body =>
        let h ← avtStr cx href
        let d ← liftX (callFn 100000 env { uri := nsFN, loc := "doc" } [sStr h])
        match d with
        | [i] => run n S (cx.focus i 1 1) body
        | _ => xerr "FODC0002" ("cannot read " ++ h)
    | .unknown q fbs code =>
        match fbs with
        | [] => xerr code ("instruction " ++ q.show ++ " is not available and has no xsl:fallback")
        | _ => do
            let mut out : Array Out := #[]
            for b in fbs do
              for o in ← run n S cx b do out := out.push o
            pure out.toList
    | .staticErr code msg => xerr code msg
    | .withColl u body => run n S { cx with env := { cx.env with defaultCollation := u } } body
    | .withCompat on body => run n S { cx with backCompat := on } body
    | .extCall q ats fbs =>
        let cands := S.templates.toList.filter (fun t => t.name == some q)
        match cands.foldl (fun (b : Option Tmpl) t => match b with
            | none => some t
            | some x => if t.prec > x.prec then some t else some x) none with
        | none =>
          match fbs with
          | [] => xerr "XTDE1450" ("instruction " ++ q.show ++ " is not available and has no xsl:fallback")
          | _ => do
              let mut out : Array Out := #[]
              for b in fbs do
                for o in ← run n S cx b do out := out.push o
              pure out.toList
        | some t =>
          let mut ps : List (QN × Seq) := []
          for (aq, avt?, ex?) in ats do
            let some p := t.params.find? (fun p => p.name == aq && !p.tunnel)
              | xerr "XTSE0680" ("template " ++ q.show ++ " has no parameter " ++ aq.show)
            let v ← match p.ty with
              | some (.atomic (.b .boolean)) =>
                  match avt? with
                  | some a => do
                      let sv := (← avtStr cx a).trimAscii.toString
                      match parseBool sv with
                      | some b => pure (sBool b)
                      | none => xerr "XTDE0030" ("invalid boolean '" ++ sv ++ "' for " ++ aq.show)
                  | none => xerr "XTSE0350" ("invalid value template for " ++ aq.show)
              | some (.atomic _) =>
                  match avt? with
                  | some a => do pure [.atom (Atomic.untypedOf (← avtStr cx a))]
                  | none => xerr "XTSE0350" ("invalid value template for " ++ aq.show)
              | _ =>
                  match ex? with
                  | some e => evalX cx e
                  | none => xerr "XPST0003" ("invalid expression for " ++ aq.show)
            ps := ps ++ [(aq, v)]
          let cx' := if t.ctxAbsent then cx.noFocus else cx
          invoke n S cx' t ps cx.tunnel

/-- The string content of `xsl:comment`, `xsl:processing-instruction`
    and `xsl:namespace` (§5.7.2). -/
def contentString : Nat → Sheet → Ctx → Option Expr → List Instr → XM String
  | 0, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, sel, body => do
    match sel with
    | some e =>
        let s ← evalX cx e
        let as ← liftX (cx.env.atomize s)
        pure (String.intercalate " " (as.map Atomic.str))
    | none => simpleContent cx.env (← run n S cx body) ""

/-- Evaluate `xsl:with-param`s: the ordinary and the tunnel ones. -/
def evalParams : Nat → Sheet → Ctx → List WParam → XM (List (QN × Seq) × List (QN × Seq))
  | 0, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, ps => do
    let mut a : List (QN × Seq) := []
    let mut t : List (QN × Seq) := []
    for p in ps do
      let v ← bindValue n S cx p.sel p.body p.ty ("$" ++ p.name.show) "XTTE0590"
      if a.any (·.1 == p.name) || t.any (·.1 == p.name) then
        xerr "XTSE0670" ("two xsl:with-param elements named $" ++ p.name.show)
      if p.tunnel then t := t ++ [(p.name, v)] else a := a ++ [(p.name, v)]
    pure (a, t)

/-- The attributes of the named attribute sets (§10.2). -/
def attrSetOuts : Nat → Sheet → Ctx → List QN → XM (List Out)
  | 0, _, _, _ => xerr "XTDE0640" "attribute sets refer to each other in a cycle"
  | n + 1, S, cx, names => do
    let mut out : Array Out := #[]
    for nm in names do
      let sets := S.attrSets.filter (fun s => s.name == nm)
      if sets.isEmpty then xerr "XTSE0710" ("no attribute set named " ++ nm.show)
      for s in sets do
        for o in ← attrSetOuts n S cx s.useSets do out := out.push o
        for o in ← run n S { cx.noFocus with env := { cx.env with vars := cx.env.vars } } s.body do
          out := out.push o
    pure out.toList

/-- Apply templates to each item of `s` (§6.6). -/
def applyT : Nat → Sheet → Ctx → Seq → String → List (QN × Seq) → List (QN × Seq) → Option String → XM (List Out)
  | 0, _, _, _, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, s, mode, ps, tun, sep => do
    let sz := s.length
    let mut out : Array Out := #[]
    let mut k := 1
    for it in s do
      if k > 1 then if let some t := sep then out := out.push (.text t)
      let icx := { cx.focus it k sz with mode }
      match ← liftX (findRule S icx.env mode it) with
      | some t => for o in ← invoke n S icx t ps tun do out := out.push o
      | none => for o in ← builtin n S icx it mode ps tun do out := out.push o
      k := k + 1
    pure out.toList

/-- Invoke a template with the given parameters (§9.2, §10.1.6). -/
def invoke : Nat → Sheet → Ctx → Tmpl → List (QN × Seq) → List (QN × Seq) → XM (List Out)
  | 0, _, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, t, ps, tun => do
    -- an abstract template (§3.4.5.2) fails before its parameters are bound
    if let [.staticErr "XTDE3052" msg] := t.body then xerr "XTDE3052" msg
    -- the template body sees the global variables and its parameters,
    -- not the caller's local variables
    let globals := cx.env.vars.dropWhile (fun (q, _) => !(q == xv "globals"))
    -- the current captured groups are kept through template calls (§17.2.1)
    let globals := match lookupVar cx.env.vars vRegex with
      | some g => (vRegex, g) :: globals
      | none => globals
    let mut tcx : Ctx := { cx with env := { cx.env with vars := globals }, rule := if t.pat.isSome then some t else cx.rule, tunnel := tun, inFn := false }
    if t.pat.isNone then tcx := { tcx with rule := cx.rule }
    for p in t.params do
      let given := if p.tunnel then tun.find? (·.1 == p.name) else ps.find? (·.1 == p.name)
      let v ← match given with
        | some (_, v) =>
            match p.ty with
            | some ty => orErr (cx.env.coerce ty v ("$" ++ p.name.show)) "XTTE0590" ("the value of $" ++ p.name.show ++ " does not match its type")
            | none => pure v
        | none =>
            if p.required then xerr "XTDE0700" ("no value for the required parameter $" ++ p.name.show)
            else bindValue n S tcx p.sel p.body p.ty ("$" ++ p.name.show) "XTTE0590"
      tcx := tcx.bind p.name v
    if let some cty := t.ctxAs then
      match cx.env.ctx with
      | some c => if !(cx.env.seqMatches c cty) then xerr "XTTE0590" "the context item does not match the template's xsl:context-item type"
      | none => pure ()
    let os ← run n S tcx t.body
    match t.ty with
    | none => pure os
    | some ty =>
        let v ← materializeAll cx.env os
        pure (Out.ofSeq (← orErr (cx.env.coerce ty v "template result") "XTTE0505" "the result of the template does not match its declared type"))

/-- The built-in template rule of a mode (§6.10). -/
def builtin : Nat → Sheet → Ctx → Item → String → List (QN × Seq) → List (QN × Seq) → XM (List Out)
  | 0, _, _, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, it, mode, ps, tun => do
    let env := cx.env
    let md := S.mode mode
    let kids : Seq := match it with | .node nd => env.childItems nd | _ => []
    let ats : Seq := match it with | .node nd => env.attrItems nd | _ => []
    match md.onNoMatch with
    | .fail => xerr "XTDE0555" ("no template rule matches in mode " ++ mode)
    | .textOnlyCopy =>
      match it with
      | .node nd =>
        match (env.nrec nd).kind with
        | .document | .element => applyT n S cx kids mode ps tun none
        | .text | .attribute => pure [.text (env.nodeString nd)]
        | _ => pure []
      | .atom a => pure [.text a.str]
      | .arr ms => applyT n S cx ms.flatten mode ps tun none
      | _ => pure []
    | .deepCopy => pure [.item it]
    | .shallowCopy =>
      match it with
      | .node nd =>
        let r := env.nrec nd
        match r.kind with
        | .document => pure [.doc (← applyT n S cx kids mode ps tun none) (env.doc nd).uri]
        | .element =>
            let content := (← applyT n S cx ats mode ps tun none) ++ (← applyT n S cx kids mode ps tun none)
            pure [.elem r.name (if md.copyNs then env.elemDecls nd else []) content]
        | _ => pure [.item it]
      | .arr ms => applyT n S cx ms.flatten mode ps tun none
      | _ => pure [.item it]
    | .deepSkip =>
      match it with
      | .node nd => if (env.nrec nd).kind == .document then applyT n S cx kids mode ps tun none else pure []
      | _ => pure []
    | .shallowSkip =>
      match it with
      | .node nd =>
        match (env.nrec nd).kind with
        | .document => applyT n S cx kids mode ps tun none
        | .element => do pure ((← applyT n S cx ats mode ps tun none) ++ (← applyT n S cx kids mode ps tun none))
        | _ => pure []
      | .arr ms => applyT n S cx ms.flatten mode ps tun none
      | _ => pure []

/-- The keys of each item for `xsl:sort` (computed once per item). -/
def sortKeysOf : Nat → Sheet → Ctx → List SortK → List SortSpec → XM (List (List Atomic))
  | 0, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, sorts, specs => do
    let mut out : Array (List Atomic) := #[]
    for (k, sp) in sorts.zip specs do
      match k with
      | .mk sel body .. =>
        let v ← match sel with
          | some e => evalX cx e
          | none =>
            if body.isEmpty then pure (match cx.env.ctx with | some s => s | none => [])
            else do
              let os ← run n S cx body
              pure [.atom (Atomic.ofStr (← simpleContent cx.env os ""))]
        let as ← liftX (cx.env.atomize v)
        let as := if cx.backCompat then as.take 1 else as
        out := out.push (← liftX (sortKeyAtom sp.dataType as))
    pure out.toList

/-- Sort a sequence (§13). -/
def sortSeq : Nat → Sheet → Ctx → Seq → List SortK → XM Seq
  | 0, _, _, _, _ => xerr "FOER0000" "XSLT evaluation too deep (fuel exhausted)"
  | n + 1, S, cx, s, sorts => do
    let specs ← sortSpecs cx sorts
    let sz := s.length
    let mut keyed : Array (List (List Atomic) × Item) := #[]
    let mut k := 1
    for it in s do
      keyed := keyed.push ((← sortKeysOf n S { cx.focus it k sz with rule := none } sorts specs), it)
      k := k + 1
    let tz := cx.env.tz
    -- the values of one sort key must be comparable (XTDE1030)
    -- (4.0: a key value is a sequence; items at one position compare)
    for j in [0:specs.length] do
      let seqs := keyed.toList.map (fun (ks, _) => (ks[j]?.getD []))
      let width := seqs.foldl (fun a q => max a q.length) 0
      for p in [0:width] do
        let vals := seqs.filterMap (·[p]?)
        if let some v0 := vals.head? then
          if vals.any (fun v => !sortComparable tz v0 v) then
            xerr "XTDE1030" "the values of a sort key cannot be compared"
    pure ((keyed.toList.mergeSort (fun a b => cmpKeys specs tz a.1 b.1 != .gt)).map (·.2))

end

end L4Factoidal.XSLT4
