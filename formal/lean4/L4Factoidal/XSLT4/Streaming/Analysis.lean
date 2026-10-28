/-
L4Factoidal.XSLT4.Streaming.Analysis — the streamability analysis of
XSLT Streaming 4.0.

Spec: XSLT Streaming 4.0 editor's draft
(https://qt4cg.org/specifications/xslt-streaming-40/Overview.html, read
2026-10-28). Section numbers below cite it.

Every construct gets a posture (§3.8: grounded, climbing, striding,
crawling, roaming), a sweep (§3.9: motionless, consuming, free-ranging)
and a U-type (§3.5). Most constructs use the general streamability rules
(§3.10, `general`); the others have their own cases (§12). A construct
that is declared streamable (§3.1: a template rule of a mode with
`streamable="yes"`, `xsl:source-document`, `xsl:function` with a
`streamability` category, `xsl:accumulator`, `xsl:attribute-set`,
`xsl:merge-source`) and is not guaranteed streamable gives the static
error XTSE3430.

The analysis reads the stylesheet modules (the node tables that
`XSLT4.Compile` reads), not the compiled `Sheet`, because the compiled
form drops the `streamable` attributes. It does no evaluation, except of
`use-when` (through `XSLT4.staticBool`).

Approximations, each named here:
* static types are U-types without cardinality; the cardinality rules of
  §12.8.7 (pipeline) are not applied (a pipeline over streamed nodes is
  roaming);
* schema-aware analysis (§3.5.4) is not done: there are no schema types;
* `xsl:fallback` of a known instruction is ignored, as §12.6.17 says for
  a processor that does not perform fallback;
* shadow attributes and static variables are not expanded.
-/
import L4Factoidal.XSLT4.Compile
import L4Factoidal.XSLT4.Streaming.Usage

namespace L4Factoidal.XSLT4.Streaming

open L4Factoidal.XPath4
open L4Factoidal.XSLT4

/-! ## Posture, sweep and operand usage (§3.3, §3.8, §3.9) -/

inductive Posture where
  | grounded | climbing | striding | crawling | roaming
deriving DecidableEq, Repr, Inhabited

inductive Sweep where
  | motionless | consuming | freeRanging
deriving DecidableEq, Repr, Inhabited

def Sweep.rank : Sweep → Nat
  | .motionless => 0 | .consuming => 1 | .freeRanging => 2

/-- The wider of two sweeps (motionless < consuming < free-ranging). -/
def Sweep.wider (a b : Sweep) : Sweep := if a.rank ≥ b.rank then a else b

inductive Usage where
  | absorption | inspection | transmission | navigation
deriving DecidableEq, Repr, Inhabited

/-! ## U-types (§3.5), as bit sets

The fundamental item types are grouped: the seven node kinds, the
numeric types (`xs:decimal`, `xs:double`, `xs:float`), the other atomic
types, function items (with maps and arrays) and JNodes. The analysis
only asks whether a U-type meets these groups. -/

abbrev UT := Nat

namespace UT
def doc : UT := 1
def elem : UT := 2
def attr : UT := 4
def text : UT := 8
def comment : UT := 16
def pi : UT := 32
def ns : UT := 64
def num : UT := 128
def atom : UT := 256
def fn : UT := 512
def jnode : UT := 1024
def all : UT := 2047
def nodes : UT := 127
def empty : UT := 0
def atomic : UT := 384
/-- The kinds that the child axis can give. -/
def children : UT := 58
def meets (a b : UT) : Bool := a &&& b != 0
/-- Can an item of this U-type have children (§3.10: the intersection
    with `U{element(), document-node()}`)? -/
def withChildren (a : UT) : Bool := meets a 3
/-- Is `a` a subtype of the numeric types (and not empty)? -/
def numericOnly (a : UT) : Bool := a != 0 && a &&& (all - num) == 0
end UT

def utOfAtomic (a : AType) : UT :=
  if a.derives (.b .decimal) || a.derives (.b .double) || a.derives (.b .float) then UT.num
  else match a with
    | .b .anyAtomicType => UT.atomic
    | _ => UT.atom

/-- The U-type of a sequence type (§3.5, "the mapping from SequenceTypes
    to U-types"). -/
def utOf : Nat → IType → UT
  | 0, _ => UT.all
  | f + 1, t =>
    match t with
    | .item => UT.all
    | .anyNode | .xnode => UT.nodes
    | .jnodeT .. => UT.jnode
    | .atomic a => utOfAtomic a
    | .elem _ => UT.elem
    | .attr _ => UT.attr
    | .text => UT.text
    | .comment => UT.comment
    | .nsNode => UT.ns
    | .pi _ => UT.pi
    | .doc _ => UT.doc
    | .anyFn | .fnT .. | .anyMap | .mapT .. | .anyArr | .arrT _ | .record .. => UT.fn
    | .choice ts => ts.foldl (fun u x => u ||| utOf f x) 0
    | .enum _ => UT.atom
    | .seq x _ => utOf f x
    | .empty => 0

/-- The type-determined usage of a required type (§3.3.1): function
    types give inspection, atomic types absorption, others navigation. -/
def tdUsage : Nat → IType → Usage
  | 0, _ => .navigation
  | f + 1, t =>
    match t with
    | .seq x _ => tdUsage f x
    | .anyFn | .fnT .. | .anyMap | .mapT .. | .anyArr | .arrT _ | .record .. => .inspection
    | .atomic _ | .enum _ => .absorption
    | .choice ts =>
      if !ts.isEmpty && ts.all (fun x => tdUsage f x == .absorption) then .absorption
      else .navigation
    | _ => .navigation

def tdUsageOpt : Option IType → Usage
  | none => .navigation
  | some t => tdUsage 50 t

/-- Does the type permit more than one item (`*` or `+`, or no type)? -/
def manyItems : Nat → Option IType → Bool
  | _, none => true
  | 0, _ => true
  | f + 1, some t =>
    match t with
    | .seq _ .star | .seq _ .plus => true
    | .seq x _ => manyItems f (some x)
    | _ => false

/-! ## Results and the general rules (§3.10) -/

/-- The posture, sweep and U-type of a construct. -/
structure SR where
  p : Posture := .grounded
  s : Sweep := .motionless
  t : UT := UT.all
deriving Inhabited, Repr

/-- Grounded and motionless. -/
def SR.gm (t : UT := UT.all) : SR := { t }

/-- Roaming and free-ranging. -/
def SR.roam (t : UT := UT.all) : SR := { p := .roaming, s := .freeRanging, t }

/-- §3.9: a roaming posture or a free-ranging sweep makes the construct
    roaming and free-ranging. -/
def SR.norm (r : SR) : SR :=
  if r.p == .roaming || r.s == .freeRanging then SR.roam r.t else r

/-- Is the construct grounded and motionless? -/
def SR.isGM (r : SR) : Bool := r.p == .grounded && r.s == .motionless

/-- An operand of a construct: its result, its operand usage, whether it
    is a higher-order operand (§3.2) and its choice operand group (§3.8.1). -/
structure Opd where
  r : SR
  u : Usage
  ho : Bool := false
  grp : Option Nat := none
deriving Inhabited

/-- The adjusted sweep of an operand (§3.10, rule 1b). -/
def Opd.adj (o : Opd) : Sweep :=
  if o.r.s == .freeRanging || o.r.p == .roaming then .freeRanging
  else if o.r.p == .grounded then o.r.s
  else
    let u := if o.u == .absorption && !UT.withChildren o.r.t then Usage.inspection else o.u
    match u with
    | .absorption => if o.r.p == .climbing then .freeRanging else .consuming
    | .inspection | .transmission => o.r.s
    | .navigation => .freeRanging

/-- Is the operand potentially consuming (§3.10)? -/
def Opd.potCons (o : Opd) : Bool :=
  o.adj == .consuming || (o.u == .transmission && o.r.p != .grounded)

/-- The combined posture of a choice operand group (§3.8.1). -/
def combinedPosture (ps : List Posture) : Posture :=
  if ps.contains .roaming then .roaming
  else if ps.all (· == .grounded) then .grounded
  else if ps.all (fun p => p == .climbing || p == .grounded) then .climbing
  else if ps.all (fun p => p == .striding || p == .grounded) then .striding
  else if ps.all (fun p => p == .crawling || p == .striding || p == .grounded) then .crawling
  else .roaming

/-- The general streamability rules (§3.10, rule 2). `single` marks a
    call of a built-in function whose result has at most one item (the
    crawling-to-striding rule). -/
def general (t : UT) (ops : List Opd) (single : Bool := false) : SR :=
  if ops.isEmpty then SR.gm t
  else if ops.any (fun o => o.adj == .freeRanging) then SR.roam t
  else
    match ops.filter Opd.potCons with
    | [] => SR.gm t
    | [o] =>
      if o.ho then SR.roam t
      else if o.u == .absorption || o.u == .inspection then { p := .grounded, s := .consuming, t }
      else if o.r.p == .crawling && single then { p := .striding, s := o.adj, t }
      else { p := o.r.p, s := o.adj, t }
    | o :: rest =>
      let pc := o :: rest
      if o.grp.isSome && pc.all (·.grp == o.grp) then
        let grp := ops.filter (·.grp == o.grp)
        let cp := combinedPosture (grp.map (fun x => x.r.p))
        let cs := grp.foldl (fun acc x => acc.wider x.adj) Sweep.motionless
        SR.norm { p := cp, s := cs, t := t }
      else if pc.all (fun x => x.adj == .motionless && x.r.p == o.r.p) then
        { p := o.r.p, s := .motionless, t }
      else SR.roam t

/-- The type-adjusted posture and sweep with respect to a required type
    (§3.3.1). -/
def typeAdjusted (r : SR) (ty : Option IType) : SR :=
  general r.t [{ r, u := tdUsageOpt ty }]

/-! ## The static context of the analysis -/

/-- A stylesheet function: name, parameter types, result type,
    streamability category (§8.1). -/
structure FnInfo where
  name : QN
  params : List (Option IType) := []
  ret : Option IType := none
  cat : String := "unclassified"
deriving Inhabited

/-- A named template: `xsl:context-item` use and type, parameters. -/
structure TInfo where
  name : QN
  ctxUse : String := "optional"
  ctxAs : Option IType := none
  params : List (QN × Option IType) := []
deriving Inhabited

/-- What the analysis knows of the whole stylesheet. -/
structure Info where
  fns : List FnInfo := []
  tmpls : List TInfo := []
  /-- Mode keys (`#unnamed` or `Q{uri}local`) declared `streamable="yes"`. -/
  smodes : List String := []
  /-- Attribute sets (`Q{uri}local`) declared `streamable="yes"`. -/
  ssets : List String := []
  /-- Global variables and parameters with their U-types. -/
  globals : List (QN × UT) := []
deriving Inhabited

structure Ctx where
  /-- The context posture (§3.8.2) and the context item type. -/
  post : Posture := .roaming
  ct : UT := UT.all
  /-- Local variables in scope, with their U-types. -/
  vars : List (QN × UT) := []
  /-- The streaming parameter of the function being analyzed, and the
      posture and sweep of a reference to it (§8.1). -/
  sparam : Option (QN × SR) := none
  /-- The select expression of the `xsl:for-each-group` whose body is
      the focus-setting container (§12.9.4). -/
  feg : Option SR := none
  /-- The context posture of the outermost containing expression, and
      whether a higher-order operand lies on the path to it (§12.9.3). -/
  outer : Posture := .roaming
  ho : Bool := false
  inPattern : Bool := false
  /-- §12.9.1, `accumulator-after`: `none` when the focus is not the
      focus of a containing sequence constructor; `some b` when it is,
      `b` telling whether a preceding sibling (of an enclosing node) in
      a sequence constructor is consuming. -/
  accAfter : Option Bool := none
  /-- In an `xsl:accumulator-rule`: `some true` for phase `start`,
      `some false` for phase `end`. -/
  accPhase : Option Bool := none
  inFork : Bool := false
  info : Info := {}
deriving Inhabited

def Ctx.varType (cx : Ctx) (q : QN) : UT :=
  match cx.vars.find? (·.1 == q) with
  | some (_, t) => t
  | none => match cx.info.globals.find? (·.1 == q) with
    | some (_, t) => t
    | none => UT.all

/-- The context for an operand with a new focus: the predicate of a step
    or filter, the right operand of `/` or `!`. -/
def Ctx.focus (cx : Ctx) (p : Posture) (t : UT) (ho : Bool := true) : Ctx :=
  { cx with post := p, ct := t, feg := none, accAfter := none, ho := cx.ho || ho }

/-! ## Axis steps (§12.8.10) -/

/-- The node kinds an axis can reach from a context item of type `ct`. -/
def axisKinds (ax : Axis) (ct : UT) : UT :=
  match ax with
  | .attribute => if UT.meets ct UT.elem then UT.attr else 0
  | .namespace => if UT.meets ct UT.elem then UT.ns else 0
  | .child | .descendant => if UT.withChildren ct then UT.children else 0
  | .self => ct &&& UT.nodes
  | .descendantOrSelf => (ct &&& UT.nodes) ||| (if UT.withChildren ct then UT.children else 0)
  | .parent | .ancestor => if UT.meets ct (UT.nodes - UT.doc) then UT.elem ||| UT.doc else 0
  | .ancestorOrSelf => (ct &&& UT.nodes) ||| UT.elem ||| UT.doc
  | .followingSibling | .precedingSibling | .following | .preceding
  | .followingOrSelf | .followingSiblingOrSelf | .precedingOrSelf | .precedingSiblingOrSelf =>
    UT.children ||| (ct &&& UT.nodes)
  | .item => UT.all

def testType : Nat → Axis → NodeTest → UT
  | 0, _, _ => UT.nodes
  | f + 1, ax, t =>
    match t with
    | .name _ | .ncname .. =>
      if ax == .attribute then UT.attr else if ax == .namespace then UT.ns else UT.elem
    | .kind k => utOf 20 k
    | .union ts => ts.foldl (fun u x => u ||| testType f ax x) 0

/-- The U-type of an axis step. -/
def stepType (ax : Axis) (t : NodeTest) (ct : UT) : UT :=
  testType 20 ax t &&& axisKinds ax ct

/-- The table of §12.8.10: the posture and sweep of a step without
    (non-motionless) predicates, from the context posture and the axis. -/
def stepTable (cp : Posture) (ax : Axis) (selectsElems : Bool) : Posture × Sweep :=
  match cp, ax with
  | .grounded, _ => (.grounded, .motionless)
  | .climbing, .self | .climbing, .parent | .climbing, .ancestorOrSelf | .climbing, .ancestor =>
    (.climbing, .motionless)
  | .climbing, .attribute | .climbing, .namespace => (.striding, .motionless)
  | .striding, .parent | .striding, .ancestorOrSelf | .striding, .ancestor => (.climbing, .motionless)
  | .striding, .self | .striding, .attribute | .striding, .namespace => (.striding, .motionless)
  | .striding, .child => (.striding, .consuming)
  | .striding, .descendant | .striding, .descendantOrSelf =>
    if selectsElems then (.crawling, .consuming) else (.striding, .consuming)
  | .crawling, .parent | .crawling, .ancestorOrSelf | .crawling, .ancestor => (.climbing, .motionless)
  | .crawling, .attribute | .crawling, .namespace => (.striding, .motionless)
  | .crawling, .self => if selectsElems then (.crawling, .motionless) else (.striding, .motionless)
  | _, _ => (.roaming, .freeRanging)

/-! ## Static properties of expressions -/

def fnQ (q : QN) (l : String) : Bool := q.uri == nsFN && q.loc == l

/-- Functions whose call with `k` arguments takes the context item as
    an implicit last argument. -/
def ctxDefaulted (q : QN) (k : Nat) : Bool :=
  q.uri == nsFN && (
    (k == 0 && ["name", "local-name", "namespace-uri", "string", "data", "number",
      "string-length", "normalize-space", "root", "base-uri", "document-uri", "node-name",
      "nilled", "has-children", "path", "generate-id", "copy-of", "snapshot"].contains q.loc) ||
    (k == 1 && ["lang", "id", "idref", "element-with-id"].contains q.loc))

/-- Focus-dependent built-in functions (for named function references). -/
def focusDependentRef (q : QN) (k : Nat) : Bool :=
  ctxDefaulted q k || (q.uri == nsFN && (q.loc == "position" || q.loc == "last" ||
    q.loc == "current" || q.loc == "current-group" || q.loc == "current-grouping-key"))

/-- Does the expression depend on the focus of its own container (not
    counting nested predicates, right operands of `/` and `!`, and
    inline functions, which have their own)? §12.8.10, §12.8.11. -/
def focusFree : Nat → Expr → Bool
  | 0, _ => false
  | f + 1, e =>
    match e with
    | .ctx | .root | .step .. | .dstep .. | .ulookup _ => false
    | .call q args _ =>
      !(ctxDefaulted q args.length || fnQ q "position" || fnQ q "last") &&
        args.all (fun a => match a with | some x => focusFree f x | none => true)
    | .lit _ | .var _ | .fref .. | .inline .. => true
    | .seq es | .arrS es | .tmpl es => es.all (focusFree f)
    | .slash a _ | .smap a _ | .filter a _ | .pipe a _ => focusFree f a
    | .bin _ a b => focusFree f a && focusFree f b
    | .neg a | .plus a | .arrC a | .instOf a _ | .treat a _ | .cast a _ _ | .castable a _ _ =>
      focusFree f a
    | .ifE c t x => focusFree f c && focusFree f t && focusFree f x
    | .letE _ _ a b => focusFree f a && focusFree f b
    | .forE _ _ _ _ _ a b | .quant _ _ _ a b => focusFree f a && focusFree f b
    | .lookup a k => focusFree f a && (match k with | some x => focusFree f x | none => true)
    | .dyn g args => focusFree f g && args.all (fun a => match a with | some x => focusFree f x | none => true)
    | .mapArrow a g args => focusFree f a && focusFree f g &&
        args.all (fun a => match a with | some x => focusFree f x | none => true)
    | .mapC es => es.all (fun (a, b) => focusFree f a && focusFree f b)
    | .ext .. => false

/-- Is the expression known to give at most one item (§12.8.10: "the
    maximum cardinality of P is 1")? A syntactic approximation. -/
def singleton : Nat → Expr → Bool
  | 0, _ => false
  | f + 1, e =>
    match e with
    | .lit _ | .var _ => true
    | .bin op _ _ => !(op == .to || op == .union || op == .intersect || op == .except || op == .otherwise)
    | .neg _ | .plus _ | .cast _ _ _ | .castable .. | .instOf .. => true
    | .seq [a] => singleton f a
    | .call q _ _ => q.uri == nsFN && ["count", "sum", "avg", "max", "min", "number",
        "string-length", "round", "floor", "ceiling", "abs", "head", "exactly-one",
        "zero-or-one", "last", "position"].contains q.loc
    | .filter a _ => singleton f a
    | .ifE _ t x => singleton f t && singleton f x
    | _ => false

/-- Does the expression call `position`, `last` or `function-lookup`
    outside nested predicates (§12.10, non-positional predicates)? -/
def callsPositional : Nat → Expr → Bool
  | 0, _ => true
  | f + 1, e =>
    match e with
    | .call q args _ =>
      (q.uri == nsFN && (q.loc == "position" || q.loc == "last" || q.loc == "function-lookup")) ||
        args.any (fun a => match a with | some x => callsPositional f x | none => false)
    | .fref q _ => q.uri == nsFN && (q.loc == "position" || q.loc == "last" || q.loc == "function-lookup")
    | .step .. | .dstep .. | .lit _ | .var _ | .ctx | .root => false
    | .filter a _ => callsPositional f a
    | .seq es | .arrS es | .tmpl es => es.any (callsPositional f)
    | .slash a b | .smap a b | .pipe a b | .bin _ a b | .letE _ _ a b
    | .forE _ _ _ _ _ a b | .quant _ _ _ a b => callsPositional f a || callsPositional f b
    | .neg a | .plus a | .arrC a | .instOf a _ | .treat a _ | .cast a _ _ | .castable a _ _ =>
      callsPositional f a
    | .ifE c t x => callsPositional f c || callsPositional f t || callsPositional f x
    | .inline _ _ b _ => callsPositional f b
    | .lookup a k => callsPositional f a || (match k with | some x => callsPositional f x | none => false)
    | .ulookup k => match k with | some x => callsPositional f x | none => false
    | .dyn g args | .mapArrow _ g args => callsPositional f g ||
        args.any (fun a => match a with | some x => callsPositional f x | none => false)
    | .mapC es => es.any (fun (a, b) => callsPositional f a || callsPositional f b)
    | .ext .. => true

/-- Does the expression contain a reference to variable `q`? -/
def mentions : Nat → QN → Expr → Bool
  | 0, _, _ => true
  | f + 1, q, e =>
    match e with
    | .var v => v == q
    | .lit _ | .ctx | .root | .fref .. => false
    | .step _ _ ps => ps.any (mentions f q)
    | .dstep _ x ps => mentions f q x || ps.any (mentions f q)
    | .filter a b | .slash a b | .smap a b | .pipe a b | .bin _ a b | .letE _ _ a b
    | .forE _ _ _ _ _ a b | .quant _ _ _ a b => mentions f q a || mentions f q b
    | .seq es | .arrS es | .tmpl es | .ext _ es _ _ _ => es.any (mentions f q)
    | .neg a | .plus a | .arrC a | .instOf a _ | .treat a _ | .cast a _ _ | .castable a _ _ =>
      mentions f q a
    | .ifE c t x => mentions f q c || mentions f q t || mentions f q x
    | .inline _ _ b _ => mentions f q b
    | .call _ args kw => args.any (fun a => match a with | some x => mentions f q x | none => false) ||
        kw.any (fun (_, a) => match a with | some x => mentions f q x | none => false)
    | .lookup a k => mentions f q a || (match k with | some x => mentions f q x | none => false)
    | .ulookup k => match k with | some x => mentions f q x | none => false
    | .dyn g args | .mapArrow _ g args => mentions f q g ||
        args.any (fun a => match a with | some x => mentions f q x | none => false)
    | .mapC es => es.any (fun (a, b) => mentions f q a || mentions f q b)

/-- The U-type of the result of a built-in function, from the U-types
    of its arguments (a coarse table). -/
def fnRetType (q : QN) (argTs : List UT) : UT :=
  let first := argTs.headD UT.all
  if q.uri == nsMATH then UT.num
  else if q.uri == nsXS then
    match atypeOfName? q.loc with
    | some a => utOfAtomic a
    | none => UT.atomic
  else if q.uri == nsMAP || q.uri == nsARR then UT.all
  else if q.uri != nsFN then UT.all
  else match q.loc with
    | "count" | "sum" | "avg" | "max" | "min" | "number" | "string-length" | "position"
    | "last" | "round" | "floor" | "ceiling" | "abs" | "round-half-to-even" | "index-of"
    | "string-to-codepoints" | "compare" | "year-from-date" | "month-from-date"
    | "day-from-date" | "year-from-dateTime" | "month-from-dateTime" | "day-from-dateTime"
    | "hours-from-dateTime" | "minutes-from-dateTime" | "seconds-from-dateTime" => UT.num
    | "head" | "tail" | "remove" | "subsequence" | "reverse" | "unordered" | "exactly-one"
    | "zero-or-one" | "one-or-more" | "trace" | "copy-of" | "snapshot"
    | "distinct-ordered-nodes" | "outermost" | "innermost" | "filter" | "sort" | "foot"
    | "trunk" | "slice" | "items-at" => first
    | "insert-before" => first ||| (argTs.getD 2 0)
    | "root" => UT.doc ||| UT.elem
    | "doc" | "document" | "collection" | "parse-xml" | "parse-xml-fragment" | "parse-html" => UT.doc
    | "id" | "element-with-id" => UT.elem
    | "idref" => UT.attr
    | "data" => UT.atomic
    | "key" | "current" | "accumulator-before" | "accumulator-after" | "current-group"
    | "current-merge-group" => UT.all
    | "current-grouping-key" | "current-merge-key" => UT.atomic
    | "for-each" | "fold-left" | "fold-right" | "for-each-pair" | "apply" => UT.all
    | _ => UT.atom

/-- The usage string of a built-in function (§12.9), if it is in the
    table. -/
def builtinUsages (q : QN) : Option String :=
  let p := if q.uri == nsFN then "fn" else if q.uri == nsMAP then "map"
    else if q.uri == nsARR then "array" else if q.uri == nsMATH then "math" else ""
  (builtinUsageTable.find? (fun (a, b, _) => a == p && b == q.loc)).map (·.2.2)

def usageOfChar : Char → Usage
  | 'A' => .absorption | 'I' => .inspection | 'T' => .transmission | _ => .navigation

/-- The usage of argument `k` (0-based); a variadic function repeats its
    last usage. -/
def argUsage (us : String) (k : Nat) : Usage :=
  let cs := us.toList
  match cs[k]? with
  | some c => usageOfChar c
  | none => match cs.getLast? with
    | some c => usageOfChar c
    | none => .navigation

/-- The parameter types of an inline function argument, for the
    type-determined usages of §12.9.10, §12.9.13, §12.9.14. -/
def inlineParamTypes : Option Expr → Option (List IType)
  | some (.inline ps _ _ _) => some (ps.map (·.2))
  | _ => none

/-! ## Expressions (§12.8, §12.9) -/

/-- Is the type a document test that contains an element test
    (§12.8.5, §12.8.6)? -/
def docElemTest : IType → Bool
  | .doc (some _) => true
  | .seq (.doc (some _)) _ => true
  | _ => false

/-- The U-type that a pattern can match. -/
def patType : Nat → Expr → UT
  | 0, _ => UT.all
  | f + 1, e =>
    match e with
    | .bin .union a b => patType f a ||| patType f b
    | .bin .intersect a _ | .bin .except a _ => patType f a
    | .seq [a] => patType f a
    | .root => UT.doc
    | .instOf .ctx t => utOf 20 t
    | .filter a _ => patType f a
    | .step ax t _ =>
      let k := testType 20 ax t
      if ax == .attribute then UT.attr &&& k
      else if ax == .namespace then UT.ns &&& k
      else if ax == .self || ax == .descendantOrSelf then k
      else k &&& UT.children
    | .slash _ b => patType f b
    | _ => UT.all

/-- A union, intersect or except expression (§12.8.4). -/
def unionSR (a b : SR) : SR :=
  let t := a.t ||| b.t
  if a.s == .freeRanging || b.s == .freeRanging then SR.roam t
  else if a.isGM then { b with t }
  else if b.isGM then { a with t }
  else if a.p == .climbing && b.p == .climbing then { p := .climbing, s := a.s.wider b.s, t }
  else if (a.p == .striding || a.p == .crawling) && (b.p == .striding || b.p == .crawling) then
    { p := .crawling, s := a.s.wider b.s, t }
  else SR.roam t

mutual

/-- The posture, sweep and U-type of an XPath expression. -/
def ex : Nat → Ctx → Expr → SR
  | 0, _, _ => SR.roam
  | f + 1, cx, e => (exStep f cx e).norm

def exStep : Nat → Ctx → Expr → SR
  | 0, _, _ => SR.roam
  | f + 1, cx, e =>
    let opd (cx' : Ctx) (x : Expr) (u : Usage) (ho := false) (grp : Option Nat := none) : Opd :=
      { r := ex f cx' x, u, ho, grp }
    match e with
    | .lit a => SR.gm (if a.isNumeric then UT.num else UT.atom)
    | .seq [] => SR.gm 0
    | .seq [x] => ex f cx x
    | .seq es =>
      let os := es.map (fun x => opd cx x .transmission)
      general (os.foldl (fun u o => u ||| o.r.t) 0) os
    | .var q =>
      match cx.sparam with
      | some (p, r) => if p == q then r else SR.gm (cx.varType q)
      | none => SR.gm (cx.varType q)
    | .ctx => { p := cx.post, s := .motionless, t := cx.ct }
    | .root => rootOf f cx { p := cx.post, s := .motionless, t := cx.ct }
    | .slash (.slash a (.step .descendantOrSelf (.kind .anyNode) [])) (.step .child t preds) =>
      -- `E//X` with a child step `X` whose predicates are not positional
      -- selects what `E/descendant::X` selects (XPath 4.0 §4.6.7, the note
      -- on `//`); the analysis reads it in that form, as streaming
      -- processors do (§3.1 permits a more liberal analysis)
      let pcx := cx.focus .crawling (stepType .child t UT.all)
      if preds.all (fun pr => !callsPositional 200 pr && !UT.meets (ex f pcx pr).t UT.num) then
        ex f cx (.slash a (.step .descendant t preds))
      else
        let ra := ex f cx (.slash a (.step .descendantOrSelf (.kind .anyNode) []))
        let rb := ex f (cx.focus ra.p ra.t) (.step .child t preds)
        if rb.p == .roaming && isScanning f cx e then
          { p := if UT.meets rb.t UT.elem then .crawling else .striding,
            s := if ra.s == .freeRanging then .freeRanging else .consuming, t := rb.t }
        else { p := rb.p, s := ra.s.wider rb.s, t := rb.t }
    | .slash a (.slash b c) =>
      -- `/` is associative; the rules of §12.8.9 read `a/b/c` as `(a/b)/c`
      match exprFlat 200 (.slash a (.slash b c)) with
      | x :: xs => ex f cx (xs.foldl Expr.slash x)
      | [] => SR.roam
    | .slash a b =>
      let ra := ex f cx a
      let rb := ex f (cx.focus ra.p ra.t) b
      let s := ra.s.wider rb.s
      if rb.p == .roaming && isScanning f cx e then
        { p := if UT.meets rb.t UT.elem then .crawling else .striding,
          s := if ra.s == .freeRanging then .freeRanging else .consuming, t := rb.t }
      else { p := rb.p, s, t := rb.t }
    | .step ax t preds => stepSR f cx ax t preds
    | .dstep ax x preds =>
      let r := stepSR f cx ax (.name .any) preds
      general r.t [{ r, u := .transmission }, opd cx x .absorption]
    | .filter b p =>
      let rb := ex f cx b
      if rb.p == .crawling && UT.numericOnly (ex f (cx.focus rb.p rb.t) p).t &&
          singleton 20 p && focusFree 50 p then
        { p := .striding, s := rb.s, t := rb.t }
      else
        let rp := ex f (cx.focus rb.p rb.t) p
        if rp.s == .motionless && rp.p != .roaming then rb else SR.roam rb.t
    | .call q args kw =>
      let args := if ctxDefaulted q args.length then args ++ [some Expr.ctx] else args
      let args := args ++ kw.map (·.2)
      callSR f cx q args
    | .dyn g args =>
      let fo := opd cx g .inspection
      let tys := inlineParamTypes (some g)
      let os := args.zipIdx.filterMap (fun (a, k) => a.map (fun x =>
        opd cx x (match tys with
          | some ts => tdUsageOpt ts[k]?
          | none => .navigation)))
      general UT.all (fo :: os)
    | .fref q k =>
      if focusDependentRef q k && cx.post != .grounded then SR.roam UT.fn else SR.gm UT.fn
    | .inline _ _ body _ =>
      match cx.sparam with
      | some (p, _) => if mentions 200 p body then SR.roam UT.fn else SR.gm UT.fn
      | none => SR.gm UT.fn
    | .mapC es =>
      let rs := es.map (fun (k, v) => general UT.fn [opd cx k .absorption, opd cx v .navigation])
      if rs.any (fun r => r.p == .roaming || r.s == .freeRanging) then SR.roam UT.fn
      else { p := .grounded, s := rs.foldl (fun s r => s.wider r.s) .motionless, t := UT.fn }
    | .arrS es => general UT.fn (es.map (fun x => opd cx x .navigation))
    | .arrC x => general UT.fn [opd cx x .navigation]
    | .lookup x k =>
      general UT.all ([opd cx x .inspection] ++ (match k with
        | some kk => [opd cx kk .absorption]
        | none => []))
    | .ulookup k =>
      general UT.all ([opd cx .ctx .inspection] ++ (match k with
        | some kk => [opd cx kk .absorption]
        | none => []))
    | .bin op a b =>
      match op with
      | .or | .and => general UT.atom [opd cx a .inspection, opd cx b .inspection]
      | .is | .isNot | .precedes | .follows | .precedesOrIs | .followsOrIs =>
        general UT.atom [opd cx a .inspection, opd cx b .inspection]
      | .union | .intersect | .except => unionSR (ex f cx a) (ex f cx b)
      | .otherwise =>
        let oa := opd cx a .transmission
        let ob := opd cx b .transmission
        general (oa.r.t ||| ob.r.t) [oa, ob]
      | .geq | .gne | .glt | .gle | .ggt | .gge | .veq | .vne | .vlt | .vle | .vgt | .vge
      | .concat => general UT.atom [opd cx a .absorption, opd cx b .absorption]
      | _ => general UT.atomic [opd cx a .absorption, opd cx b .absorption]
    | .neg a | .plus a => general UT.atomic [opd cx a .absorption]
    | .ifE c t x =>
      let ot := opd cx t .transmission (grp := some 0)
      let ox := opd cx x .transmission (grp := some 0)
      general (ot.r.t ||| ox.r.t) [opd cx c .inspection, ot, ox]
    | .forE _ v _ posv _ src body =>
      let rs := ex f cx src
      if rs.p != .grounded then SR.roam
      else
        let cx' := { cx with vars := (v, rs.t) :: (match posv with
          | some pv => [(pv, UT.num)] | none => []) ++ cx.vars, ho := true }
        let ob := opd cx' body .transmission (ho := true)
        general ob.r.t [{ r := rs, u := .navigation }, ob]
    | .letE v _ a body =>
      let oa := opd cx a .navigation
      let cx' := { cx with vars := (v, oa.r.t) :: cx.vars }
      let ob := opd cx' body .transmission
      general ob.r.t [oa, ob]
    | .quant _ v _ src sat =>
      let os := opd cx src .navigation
      let cx' := { cx with vars := (v, os.r.t) :: cx.vars, ho := true }
      general UT.atom [os, opd cx' sat .inspection (ho := true)]
    | .instOf a t =>
      general UT.atom [opd cx a (if docElemTest t then .absorption else .inspection)]
    | .treat a t =>
      if docElemTest t then SR.roam else
      let oa := opd cx a .transmission
      general oa.r.t [oa]
    | .cast a t _ => general (utOf 20 t) [opd cx a .absorption]
    | .castable a _ _ => general UT.atom [opd cx a .absorption]
    | .smap a b =>
      let ra := ex f cx a
      let rb := ex f (cx.focus ra.p ra.t) b
      { p := rb.p, s := ra.s.wider rb.s, t := rb.t }
    | .pipe a b =>
      let ra := ex f cx a
      if ra.p == .grounded then
        let rb := ex f (cx.focus .grounded ra.t) b
        SR.norm { p := .grounded, s := ra.s.wider rb.s, t := rb.t }
      else SR.roam
    | .mapArrow a g args =>
      let tys := inlineParamTypes (some g)
      let oa := opd cx a (match tys with
        | some (t :: _) => tdUsage 50 t
        | _ => .navigation)
      let os := args.filterMap (fun x => x.map (fun y => opd cx y .navigation))
      general UT.all (oa :: opd cx g .inspection :: os)
    | .tmpl parts => general UT.atom (parts.map (fun x => opd cx x .absorption))
    | .ext .. => SR.roam

/-- `root(X)` (§12.9.21): `X` itself when `X` is a striding document
    node, otherwise `head(X/ancestor-or-self::node())`. -/
def rootOf : Nat → Ctx → SR → SR
  | 0, _, _ => SR.roam
  | _ + 1, _, r =>
    if r.t == UT.doc && r.p == .striding then r
    else if r.p == .grounded then { r with t := UT.doc ||| UT.elem }
    else
      let (p, s) := stepTable r.p .ancestorOrSelf true
      let s := r.s.wider s
      -- `head` of a climbing or striding sequence keeps its posture
      ({ p, s, t := UT.doc ||| UT.elem } : SR).norm

/-- An axis step with its predicates (§12.8.10). -/
def stepSR : Nat → Ctx → Axis → NodeTest → List Expr → SR
  | 0, _, _, _, _ => SR.roam
  | f + 1, cx, ax, t, preds =>
    let ty := stepType ax t cx.ct
    if cx.post == .grounded then SR.gm (testType 20 ax t &&& (if cx.ct == 0 then UT.nodes else axisKinds ax cx.ct))
    else if cx.post == .roaming then SR.roam ty
    else if ty == 0 then SR.gm 0
    else
      let selElems := UT.meets ty UT.elem
      let (p0, s0) := stepTable cx.post ax selElems
      let pcx := cx.focus p0 ty
      if cx.post == .striding && (ax == .descendant || ax == .descendantOrSelf) &&
          preds.any (fun pr => UT.numericOnly (ex f pcx pr).t && singleton 20 pr && focusFree 50 pr) then
        { p := .striding, s := .consuming, t := ty }
      else if preds.any (fun pr => (ex f pcx pr).s != .motionless || (ex f pcx pr).p == .roaming) then
        SR.roam ty
      else ({ p := p0, s := s0, t := ty } : SR).norm

/-- Is `e` a scanning expression (§12.8.9): the form of a motionless
    pattern? -/
def isScanning : Nat → Ctx → Expr → Bool
  | 0, _, _ => false
  | f + 1, cx, e => patternOk 200 false e && patMotionless f cx e

/-- Is the pattern motionless (§12.10)? -/
def patMotionless : Nat → Ctx → Expr → Bool
  | 0, _, _ => false
  | f + 1, cx, e =>
    match e with
    | .bin .union a b | .bin .intersect a b | .bin .except a b =>
      patMotionless f cx a && patMotionless f cx b
    | .seq [a] => patMotionless f cx a
    | .root | .ctx => true
    | .instOf .ctx _ => true
    | .filter a p => patMotionless f cx a && predMotionless f cx (patType 50 a) p
    | .step ax t ps => ps.all (predMotionless f cx (stepType ax t UT.all))
    | .slash a b => patMotionless f cx a && patMotionless f cx b
    | _ => false

/-- A top-level predicate of a motionless pattern: motionless with a
    striding context posture, and non-positional (§12.10). -/
def predMotionless : Nat → Ctx → UT → Expr → Bool
  | 0, _, _, _ => false
  | f + 1, cx, ct, p =>
    let r := ex f { cx with post := .striding, ct, inPattern := true, feg := none, accAfter := none } p
    r.s == .motionless && r.p != .roaming && !callsPositional 200 p && !UT.meets r.t UT.num &&
      (match cx.sparam with
       | some (q, _) => !mentions 200 q p
       | none => true)

/-- A static function call (§12.8.15, §12.9, §8.1). -/
def callSR : Nat → Ctx → QN → List (Option Expr) → SR
  | 0, _, _, _ => SR.roam
  | f + 1, cx, q, args =>
    let present := args.filterMap id
    let rs := present.map (ex f cx)
    let ret := fnRetType q (rs.map (·.t))
    let gen (us : List Usage) (single := false) : SR :=
      general ret (args.zipIdx.filterMap (fun (a, k) => a.map (fun x =>
        { r := ex f cx x, u := us.getD k (us.getLastD .navigation) }))) single
    -- partial application: a focus-dependent function with a streamed focus
    if args.any (·.isNone) && focusDependentRef q present.length && cx.post != .grounded then SR.roam
    else if q.uri == nsFN then
      match q.loc with
      | "last" =>
        if cx.post == .striding || cx.post == .crawling || cx.post == .roaming then SR.roam UT.num
        else SR.gm UT.num
      | "position" => SR.gm UT.num
      | "current" =>
        if cx.inPattern then { p := .climbing, s := .motionless, t := UT.nodes }
        else if cx.outer == .grounded then SR.gm
        else if cx.ho then { p := .climbing, s := .motionless, t := UT.nodes }
        else { p := cx.outer, s := .motionless, t := UT.all }
      | "current-group" => match cx.feg with
        | some r => r
        | none => SR.roam
      | "current-grouping-key" | "current-merge-group" | "current-merge-key"
      | "current-merge-key-array" => SR.gm ret
      | "accumulator-before" =>
        if rs.all (·.s == .motionless) then SR.gm else SR.roam
      | "accumulator-after" =>
        if !rs.all (·.s == .motionless) then SR.roam
        else if cx.post == .grounded then SR.gm
        else if !UT.withChildren cx.ct then SR.gm
        else match cx.accPhase with
          | some true => SR.roam
          | some false => SR.gm
          | none => match cx.accAfter with
            | none => SR.roam
            | some true => SR.gm
            | some false => { p := .grounded, s := .consuming, t := UT.all }
      | "distinct-ordered-nodes" => match rs with
        | [r] => r
        | _ => gen [.transmission]
      | "fold-left" =>
        let u := match inlineParamTypes (args.getD 2 none) with
          | some [_, t] => tdUsage 50 t
          | _ => .navigation
        gen [u, .absorption, .inspection]
      | "for-each" | "filter" =>
        let u := match inlineParamTypes (args.getD 1 none) with
          | some (t :: _) => tdUsage 50 t
          | _ => .navigation
        gen [u, .inspection]
      | "for-each-pair" =>
        let (u1, u2) := match inlineParamTypes (args.getD 2 none) with
          | some [t1, t2] => (tdUsage 50 t1, tdUsage 50 t2)
          | _ => (.navigation, .navigation)
        gen [u1, u2, .inspection]
      | "fold-right" => gen [.navigation, .absorption, .inspection]
      | "innermost" | "reverse" => gen [.navigation]
      | "outermost" =>
        let r := gen [.transmission]
        if r.p == .crawling then { r with p := .striding } else r
      | "root" => match rs with
        | [r] => rootOf f cx r
        | _ => rootOf f cx { p := cx.post, s := .motionless, t := cx.ct }
      | "foot" | "trunk" => match rs with
        | [r] => if r.p == .grounded || r.p == .climbing then r else SR.roam r.t
        | _ => SR.roam
      | "function-lookup" => gen [.absorption, .absorption]
      | _ =>
        match builtinUsages q with
        | some us =>
          let single := q.loc == "head" || q.loc == "exactly-one" || q.loc == "zero-or-one"
          general ret (args.zipIdx.filterMap (fun (a, k) => a.map (fun x =>
            { r := ex f cx x, u := argUsage us k }))) single
        | none => gen []
    else if q.uri == nsXS then gen [.absorption]
    else if q.uri == nsMAP || q.uri == nsARR || q.uri == nsMATH then
      match builtinUsages q with
      | some us => general ret (args.zipIdx.filterMap (fun (a, k) => a.map (fun x =>
          { r := ex f cx x, u := argUsage us k })))
      | none => gen []
    else
      match cx.info.fns.find? (fun fi => fi.name == q && fi.params.length == args.length) with
      | some fi => userCall f cx fi args
      | none => gen []

/-- A call of a stylesheet function, by its streamability category
    (§8.1.1 to §8.1.7). -/
def userCall : Nat → Ctx → FnInfo → List (Option Expr) → SR
  | 0, _, _, _ => SR.roam
  | f + 1, cx, fi, args =>
    let ret := match fi.ret with | some t => utOf 20 t | none => UT.all
    let rest : List Opd := (args.drop 1).zipIdx.filterMap (fun (a, k) => a.map (fun x =>
      { r := ex f cx x, u := tdUsageOpt (fi.params.getD (k + 1) none) }))
    let firstR : Option SR := match args.head? with
      | some (some x) => some (ex f cx x)
      | _ => none
    let withFirst (u : Usage) : List Opd := match firstR with
      | some r => { r, u } :: rest
      | none => rest
    let descent (crawl : Bool) : SR :=
      let t0 := fi.params.headD none
      let r0 := match firstR with
        | some r => typeAdjusted r t0
        | none => SR.gm
      -- the type-adjusted posture is computed above with the declared
      -- type of the streaming parameter; a node-typed parameter keeps it
      let r0 := match firstR with
        | some r => if tdUsageOpt t0 == Usage.navigation then r else r0
        | none => r0
      if r0.p != .striding && r0.p != .grounded then SR.roam ret else
      let c := general ret rest
      if c.p != .grounded then SR.roam ret
      else if (r0.s == .consuming && c.s == .consuming) || r0.s == .freeRanging || c.s == .freeRanging then SR.roam ret
      else if r0.p == .grounded then { p := .grounded, s := r0.s.wider c.s, t := ret }
      else
        let t0u := match t0 with | some t => utOf 20 t | none => UT.all
        let a := match firstR with | some r => r.t | none => UT.all
        let s := if !UT.withChildren t0u || !UT.withChildren a then r0.s else .consuming
        { p := if crawl then .crawling else r0.p, s := s.wider c.s, t := ret }
    match fi.cat with
    | "absorbing" =>
      match firstR with
      | some r => if r.p == .crawling then SR.roam ret else general ret (withFirst .absorption)
      | none => general ret rest
    | "inspection" => general ret (withFirst .inspection)
    | "filter" => general ret (withFirst .transmission)
    | "shallow-descent" => descent false
    | "deep-descent" => descent true
    | "ascent" =>
      let r := general ret (withFirst .transmission)
      if r.p == .roaming || r.s == .freeRanging || r.s != .motionless then SR.roam ret
      else if r.p == .grounded then SR.gm ret
      else if !UT.meets ret UT.nodes then SR.gm ret
      else { p := .climbing, s := .motionless, t := ret }
    | _ =>
      general ret (args.zipIdx.filterMap (fun (a, k) => a.map (fun x =>
        { r := ex f cx x, u := tdUsageOpt (fi.params.getD k none) })))

end

end L4Factoidal.XSLT4.Streaming
