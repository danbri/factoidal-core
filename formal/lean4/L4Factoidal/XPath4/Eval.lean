/-
L4Factoidal.XPath4.Eval — the XPath 4.0 evaluator (XPath 4.0 §3, §4).

`eval`, `apply` and `callFn` are one mutual definition, total by a
FUEL argument that decreases on every nested evaluation; exhausting it
is the dynamic error `FOER0000` ("evaluation too deep"), never a
silent result.

Implemented: every expression form of `XPath4.Syntax` — paths and the
seventeen axes, predicates (reverse-axis positions), filter, `for`
(item, member, key/value, positional), `let`, `some`/`every`, `if`
(both forms), the operators (general, value and node comparisons,
arithmetic on numbers and durations/dates, range, union/intersect/
except, `||`, `otherwise`), `!`, `->`, `=>`, `=!>`, lookup `?`, map and
array constructors, inline and focus functions, named function
references, partial application, dynamic calls, keyword arguments,
`instance of`, `treat as`, `cast as`, `castable as`, string templates.
Static calls are coerced to the F&O 4.0 signature first (§3.4.3).
-/
import L4Factoidal.XPath4.Ext

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## Operator helpers (non-recursive) -/

def isMergeMarker : Expr → Bool
  | .call q [] [] => q.uri == "#merge"
  | _ => false

def isTmplMarker (q : QN) : Bool := q.uri == "#tmpl"

def mkDur (ty : Builtin) (months : Int) (secs : Dec) : Atomic :=
  ⟨.b ty, .x (.dur { months, seconds := Dec.norm secs })⟩

/-- Arithmetic on two atomic values (§3.5.1 and the F&O 4.0 §9 tables
    for durations, dates and times). -/
def arith0 (tz : Int) (op : ArOp) (a b : Atomic) : M Atomic := do
  let a0 ← if a.ty == .untyped then castAtomic a (.b .double) else pure a
  let b0 ← if b.ty == .untyped then castAtomic b (.b .double) else pure b
  -- commute `number * duration` and `duration + date`
  let swap := match a0.v, b0.v, op with
    | _, .x (.dur _), .mul => a0.isNumeric
    | .x (.dur _), .x (.dt _ _), .add => true
    | _, _, _ => false
  let a := if swap then b0 else a0
  let b := if swap then a0 else b0
  match a.num?, b.num? with
  | some x, some y => pure (← numArith op x y).atomic
  | _, _ =>
  let isYM (x : Atomic) := x.is .yearMonthDuration
  let isDT (x : Atomic) := x.is .dayTimeDuration
  match a.v, b.v, op with
  | .x (.dur x), .x (.dur y), .add =>
      if isYM a && isYM b then pure (mkDur .yearMonthDuration (x.months + y.months) Dec.zero)
      else if isDT a && isDT b then pure (mkDur .dayTimeDuration 0 (Dec.add x.seconds y.seconds))
      else err "XPTY0004" "cannot add these durations"
  | .x (.dur x), .x (.dur y), .sub =>
      if isYM a && isYM b then pure (mkDur .yearMonthDuration (x.months - y.months) Dec.zero)
      else if isDT a && isDT b then pure (mkDur .dayTimeDuration 0 (Dec.sub x.seconds y.seconds))
      else err "XPTY0004" "cannot subtract these durations"
  | .x (.dur x), .x (.dur y), .div =>
      if isYM a && isYM b then
        match Fn.Numeric.decDiv? 18 (Dec.ofInt x.months) (Dec.ofInt y.months) with
        | some d => pure (Atomic.ofDec d) | none => err "FOAR0001" "division by zero duration"
      else if isDT a && isDT b then
        match Fn.Numeric.decDiv? 18 x.seconds y.seconds with
        | some d => pure (Atomic.ofDec d) | none => err "FOAR0001" "division by zero duration"
      else err "XPTY0004" "cannot divide these durations"
  | .x (.dur x), _, .mul | .x (.dur x), _, .div =>
    match b.num? with
    | some n =>
      let f := n.toFloat
      if f.isNaN then err "FOCA0005" "NaN in duration arithmetic" else
      if f.isInf && op == .mul then err "FODT0002" "duration overflow" else
      if op == .div && f == 0 then err "FODT0002" "duration overflow" else
      let factor : Dec ← if op == .mul then pure n.toDec
        else if f.isInf then pure Dec.zero
        else match Fn.Numeric.decDiv? 18 (Dec.ofInt 1) n.toDec with
          | some d => pure d | none => err "FOAR0001"
      let factorExact (v : Dec) : Dec :=
        if op == .mul then Fn.Numeric.decMul v n.toDec
        else (Fn.Numeric.decDiv? 18 v n.toDec).getD Dec.zero
      if isYM a then
        pure (mkDur .yearMonthDuration (Fn.Numeric.decRound (factorExact (Dec.ofInt x.months))) Dec.zero)
      else if isDT a then
        let _ := factor
        pure (mkDur .dayTimeDuration 0 (factorExact x.seconds))
      else if x.months == 0 then
        pure (mkDur .duration 0 (factorExact x.seconds))
      else if decIsZero x.seconds then
        pure (mkDur .duration (Fn.Numeric.decRound (factorExact (Dec.ofInt x.months))) Dec.zero)
      -- XPath 4.0 / F&O 4.0 §8.4.4: an xs:duration with both parts is
      -- scaled part by part, the month count rounded
      else pure (mkDur .duration (Fn.Numeric.decRound (factorExact (Dec.ofInt x.months))) (factorExact x.seconds))
    | none => err "XPTY0004" "invalid duration arithmetic"
  | .x (.dt k1 x), .x (.dt k2 y), .sub =>
      if k1 == k2 && (k1 == .dateTime || k1 == .date || k1 == .time) then
        let d := Fn.DateTime.subtractValues tz x y
        pure (mkDur .dayTimeDuration 0 d.seconds)
      else err "XPTY0004" "cannot subtract these values"
  | .x (.dt k x), .x (.dur d), .add | .x (.dt k x), .x (.dur d), .sub =>
      let d' : DurValue := if op == .sub then { months := -d.months, seconds := Dec.neg d.seconds } else d
      if k == .time && !isDT b then err "XPTY0004" "time arithmetic needs xs:dayTimeDuration"
      else if (k == .dateTime || k == .date || k == .time) && (isYM b || isDT b) then
        let r := Fn.DateTime.plusDuration x d'
        pure ⟨a.ty, .x (.dt k (dtProject k r))⟩
      else err "XPTY0004" "invalid date/duration arithmetic"
  | _, _, _ => err "XPTY0004" ("invalid arithmetic on xs:" ++ a.ty.name ++ " and xs:" ++ b.ty.name)

/-- Arithmetic with the date and duration limits (`checkLimits`): an
    overflowing result of date arithmetic is FODT0001, of duration
    arithmetic FODT0002. -/
def arith (tz : Int) (op : ArOp) (a b : Atomic) : M Atomic := do
  let r ← arith0 tz op a b
  match r.v with
  | .x (.dur d) =>
    if durWithinLimits d then pure r
    else if (match a.v, b.v with | .x (.dt ..), _ | _, .x (.dt ..) => true | _, _ => false) then
      err "FODT0001" "date/time arithmetic overflows"
    else err "FODT0002" "duration arithmetic overflows"
  | _ => checkLimits r

/-- Value comparison of two atomic values (§3.7.2). -/
def valueCmp (tz : Int) (op : BOp) (a b : Atomic) : M Bool := do
  let a := if a.ty == .untyped then Atomic.ofStr a.str else a
  let b := if b.ty == .untyped then Atomic.ofStr b.str else b
  let c ← atomicCmp a b tz
  match op with
  | .veq | .geq => pure (c == some .eq)
  | .vne | .gne => pure (c != some .eq)
  | _ =>
    if !(a.ty.ordered && b.ty.ordered) then
      err "XPTY0004" ("xs:" ++ a.ty.name ++ " values have no order")
    else match op with
    | .vlt | .glt => pure (c == some .lt)
    | .vle | .gle => pure (c == some .lt || c == some .eq)
    | .vgt | .ggt => pure (c == some .gt)
    | .vge | .gge => pure (c == some .gt || c == some .eq)
    | _ => pure false

/-- General comparison of one pair, with the untyped conversions of
    §3.7.1. -/
def generalPair (tz : Int) (op : BOp) (a b : Atomic) (ns : String → Option String) : M Bool := do
  let conv (x y : Atomic) : M Atomic :=
    if x.ty == .untyped then
      if y.ty == .untyped || y.isStringLike then pure (Atomic.ofStr x.str)
      -- XPath 4.0 §4.10.2: to the primitive type of the numeric
      -- operand, or if that fails to xs:double
      else if y.isNumeric then
        match y.ty with
        | .b bt => match castAtomic x (.b (bt.primitive.getD bt)) with
          | .ok v => pure v
          | .error _ => castAtomic x (.b .double)
        | _ => castAtomic x (.b .double)
      else match y.ty with
        | .b bt => castAtomic x (.b (match bt.primitive with | some p => if derivedFrom bt .dayTimeDuration then .dayTimeDuration else if derivedFrom bt .yearMonthDuration then .yearMonthDuration else p | none => bt)) ns
        | .untyped => pure (Atomic.ofStr x.str)
    else pure x
  let a' ← conv a b
  let b' ← conv b a
  valueCmp tz op a' b'

def BOp.isGeneral : BOp → Bool
  | .geq | .gne | .glt | .gle | .ggt | .gge => true | _ => false
def BOp.isValue : BOp → Bool
  | .veq | .vne | .vlt | .vle | .vgt | .vge => true | _ => false
def BOp.isNodeCmp : BOp → Bool
  | .is | .isNot | .precedes | .follows | .precedesOrIs | .followsOrIs => true | _ => false
def BOp.arOp? : BOp → Option ArOp
  | .add => some .add | .sub => some .sub | .mul => some .mul | .div => some .div
  | .idiv => some .idiv | .mod => some .mod | _ => none

def maxRange : Int := 20000000

/-- Whether an item type is a valid cast target (XPath 4.0 §4.19.2). -/
def isCastTarget : IType → Bool
  | .atomic _ | .choice _ | .enum _ | .arrT _ | .mapT _ _ | .record _ _ | .anyArr | .anyMap => true
  | _ => false

mutual
/-- `cast as` (XPath 4.0 §4.19.2): generalized atomic types, and array,
    map and record types (§4.19.2.5 to §4.19.2.7). -/
def castToF (e : Env) : Nat → Seq → IType → Bool → M Seq
  | 0, _, _, _ => err "FOER0000" "cast nested too deeply"
  | f + 1, s, t, opt => do
  match t with
  | .anyArr | .anyMap => return ← e.coerce (if opt then .seq t .opt else t) s "cast target"
  | .arrT m =>
    match ← e.coerce (if opt then .seq .anyArr .opt else .anyArr) s "cast target" with
    | [] => return []
    | [.arr ms] => return [.arr (← ms.mapM (fun x => e.castSeqF f x m))]
    | _ => err "XPTY0004" "cast to an array type needs an array"
  | .mapT kt vt =>
    match ← e.coerce (if opt then .seq .anyMap .opt else .anyMap) s "cast target" with
    | [] => return []
    | [.map kvs] =>
      let mut out : List (Atomic × Seq) := []
      for (k, v) in kvs do
        let k1 ← if e.itemMatches (.atom k) kt then pure k
          else match ← castToF e f [.atom k] kt false with
            | [.atom k1] => pure k1
            | _ => err "XPTY0004" "a map key must cast to an atomic value"
        if out.any (fun (k2, _) => atomicEqual k1 k2) then err "XQDY0137" "the cast gives two equal keys"
        out := out ++ [(k1, ← e.castSeqF f v vt)]
      return [.map out]
    | _ => err "XPTY0004" "cast to a map type needs a map"
  | .record fs ext =>
    if fs.isEmpty && ext then return ← e.coerce (if opt then .seq .anyMap .opt else .anyMap) s "cast target"
    match ← e.coerce (if opt then .seq .anyMap .opt else .anyMap) s "cast target" with
    | [] => return []
    | [.map kvs] =>
      let mut out : List (Atomic × Seq) := []
      for (name, _, ft) in fs do
        match kvs.find? (fun (k, _) => k.isStringLike && k.str == name) with
        | some (_, v) => out := out ++ [(Atomic.ofStr name, ← e.castSeqF f v ft)]
        | none =>
          if e.seqMatches [] ft then out := out ++ [(Atomic.ofStr name, [])]
          else err "XPTY0004" ("the map has no entry " ++ name ++ " for the record type")
      return [.map out]
    | _ => err "XPTY0004" "cast to a record type needs a map"
  | .jnodeT .. | .xnode => err "XPST0080" "cast target is not an atomic, array or map type"
  | _ => pure ()
  let as ← e.atomize s
  match as with
  | [] => if opt then pure [] else err "XPTY0004" "empty sequence cannot be cast"
  | [a] =>
    match t with
    | .atomic aty =>
        if aty == .b .anyAtomicType || aty == .b .notation then err "XPST0080" "cast to an abstract type"
        else if (aty == .b .qname) && !(a.isStringLike || a.is .qname) then
          err "XPTY0004" "cannot cast to xs:QName"
        else pure (single (← castAtomic a aty e.nsResolve))
    | .choice ts =>
        -- a value of a member type is kept (XPath 4.0 §4.19.2.3)
        if ts.any (fun t => e.itemMatches (.atom a) t) then return single a
        let mut res : Option Atomic := none
        for t in ts do
          match t with
          | .atomic aty =>
            match castAtomic a aty e.nsResolve with
            | .ok v => res := some v; break
            | .error _ => pure ()
          | _ => pure ()
        match res with
        | some v => pure (single v)
        | none => err "FORG0001" "value cannot be cast to any member of the choice type"
    | .enum vs =>
        if vs.contains a.str then pure (sStr a.str) else err "FORG0001" "value not in enumeration"
    | _ => err "XPST0051" "cast target is not an atomic type"
  | _ => err "XPTY0004" "more than one item cannot be cast"

/-- Casting a sequence to a sequence type (XPath 4.0 §4.19.2.4). -/
def Env.castSeqF (e : Env) : Nat → Seq → IType → M Seq
  | 0, _, _ => err "FOER0000" "cast nested too deeply"
  | f + 1, s, st => do
    match st with
    | .empty => if s.isEmpty then pure [] else err "XPTY0004" "the value must be empty"
    | _ =>
      let (t, occ) := splitST st
      let mut out : Array Item := #[]
      for j in s do
        if e.itemMatches j t then out := out.push j
        else if isCastTarget t then out := out ++ (← castToF e f [j] t false).toArray
        else err "XPTY0004" "an item does not match the required type and cannot be cast to it"
      if !occOk occ out.size then err "XPTY0004" "the cast value does not have the required number of items"
      pure out.toList
end

def castTo (e : Env) (s : Seq) (t : IType) (opt : Bool) : M Seq := castToF e 64 s t opt

/-- The root of the tree containing `n`. -/
def Env.treeRoot (e : Env) (n : NodeRef) : NodeRef :=
  match (e.ancestors n).getLast? with | some r => r | none => n

/-! ## The evaluator -/

def fuelErr {α} : M α := err "FOER0000" "evaluation too deep (fuel exhausted)"

def Env.lookupVar (e : Env) (q : QN) : M Seq :=
  match e.vars.find? (fun (v, _) => v == q) with
  | some (_, s) => pure s
  | none => err "XPST0008" ("undeclared variable $" ++ q.show)

def Env.bind (e : Env) (q : QN) (s : Seq) : Env := { e with vars := (q, s) :: e.vars }

def Env.focus (e : Env) (i : Item) (p sz : Nat) : Env := { e with ctx := some [i], pos := p, size := sz }

def Env.ctxNode (e : Env) : M NodeRef :=
  match e.ctx with
  | none => err "XPDY0002" "the context item is absent"
  | some [.node n] => pure n
  | some [_] => err "XPTY0020" "the context item is not a node"
  | some _ => err "XPTY0020" "the context value is not a single node"

/-- A navigational expression (XPath 4.0 §4.7.3): one that keeps the
    focus as the right operand of `/` on a JNode; any other right operand
    is a selector of children by key (the selector interpretation). -/
def isNavF : Nat → Expr → Bool
  | 0, _ => false
  | f + 1, ex =>
    match ex with
    | .ctx | .root | .step .. | .dstep .. => true
    | .slash a b => isNavF f a && isNavF f b
    | .bin op a b =>
        (op == .union || op == .intersect || op == .except || op == .otherwise) &&
        isNavF f a && isNavF f b
    | .seq es => !es.isEmpty && es.all (isNavF f)
    | .filter a _ => isNavF f a
    | .forE _ _ _ _ _ _ body => isNavF f body
    | .letE _ _ _ body => isNavF f body
    | .ifE _ t e => isNavF f t && (isNavF f e || (match e with | .seq [] => true | _ => false))
    | _ => false

def isNavigational (e : Expr) : Bool := isNavF 1000 e

/-- The context value of an axis step as GNodes: maps and arrays become
    root JNodes (the implicit `fn:jtree`); any other item is an error. -/
def Env.stepOrigins (e : Env) : M (List Item) :=
  match e.ctx with
  | none => err "XPDY0002" "the context item is absent"
  | some s =>
    let s := (s.zip (List.range s.length)).map (fun (i, k) => jwrap (k + 1).toUInt64 i)
    if s.all Item.isGNode then pure s
    else match s with
      | [_] => err "XPTY0004" "the context item is not a node"
      | _ => err "XPTY0004" "the context value is not a sequence of nodes"

def isNumericLit : Expr → Option Int
  | .lit ⟨_, .int i⟩ => some i
  | _ => none

mutual

def eval : Nat → Env → Expr → M Seq
  | 0, _, _ => fuelErr
  | n + 1, env, ex =>
  match ex with
  | .lit a => pure [.atom a]
  | .seq es => do
      let mut out : Array Item := #[]
      for x in es do
        for i in ← eval n env x do out := out.push i
      pure out.toList
  | .var q => env.lookupVar q
  | .ctx => match env.ctx with
      | some s => pure s
      | none => err "XPDY0002" "the context value is absent"
  | .root => do
      match env.ctx with
      | some [j@(.jnode ..)] => return [jrootOf j]
      | some [i@(.map _)] | some [i@(.arr _)] => return [jwrap 1 i]
      -- a leading `/` needs a node: `treat as node()` (XPath 4.0 §4.7.1)
      | some [.node _] | none => pure ()
      | some _ => err "XPTY0004" "the context value of a leading / is not a node"
      let c ← env.ctxNode
      let r := env.treeRoot c
      if (env.nrec r).kind != .document then err "XPDY0050" "the root of the tree is not a document node"
      pure [.node r]
  | .slash a b => do
      let left ← eval n env a
      match nodesOf left with
      | some ns =>
        let ns := sortNodes ns
        let sz := ns.length
        let mut out : Array Item := #[]
        let mut idx := 1
        for nd in ns do
          for i in ← eval n (env.focus (.node nd) idx sz) b do out := out.push i
          idx := idx + 1
        let res := out.toList
        match nodesOf res with
        | some rs => pure ((sortNodes rs).map Item.node)
        | none =>
          if res.all Item.isGNode then pure (sortGNodes res)
          else if res.any Item.isGNode then err "XPTY0018" "a path step returned both nodes and non-nodes" else pure res
      | none =>
        -- XPath 4.0 §4.7.3: maps and arrays become root JNodes; a JNode
        -- with a non-navigational right operand selects children by key
        let s1 := (left.zip (List.range left.length)).map (fun (i, k) => jwrap (k + 1).toUInt64 i)
        if !(s1.all Item.isGNode) then err "XPTY0004" "the left operand of '/' must be nodes"
        let ns := sortGNodes s1
        let sz := ns.length
        let nav := isNavigational b
        let mut keys : Option (List Atomic) := none
        let mut out : Array Item := #[]
        let mut idx := 1
        for nd in ns do
          if nd.isJNode && !nav then
            let ks ← match keys with
              | some ks => pure ks
              | none => do
                let ks ← env.atomize (← eval n { env with ctx := none, pos := 0, size := 0 } b)
                pure ks
            keys := some ks
            for i in jselect nd ks do out := out.push i
          else
            for i in ← eval n (env.focus nd idx sz) b do out := out.push i
          idx := idx + 1
        let res := out.toList
        if res.all Item.isGNode then pure (sortGNodes res)
        else if res.any Item.isGNode then err "XPTY0018" "a path step returned both nodes and non-nodes"
        else pure res
  | .step ax t preds => do
      match env.ctx with
      | some [.node c] =>
        if ax == .item then err "XPTY0004" "the item axis is defined only for JNodes"
        let ns := (env.axis ax c).filter (fun m => env.testMatches ax m t)
        let mut cur : Seq := ns.map Item.node
        for p in preds do
          cur ← filterSeq n env cur p
        match nodesOf cur with
        | some rs => pure ((sortNodes rs).map Item.node)
        | none => pure cur
      | _ =>
        let os ← env.stepOrigins
        let mut out : Array Item := #[]
        for o in os do
          let cands ← match o with
            | .node c =>
              if ax == .item then err "XPTY0004" "the item axis is defined only for JNodes"
              pure (((env.axis ax c).filter (fun m => env.testMatches ax m t)).map Item.node)
            | j =>
              if ax == .attribute || ax == .namespace then
                err "XPTY0004" "the attribute and namespace axes are not defined for JNodes"
              pure ((jaxis ax j).filter (fun m => env.jtestMatches m t))
          let mut cur : Seq := cands
          for p in preds do
            cur ← filterSeq n env cur p
          for i in cur do out := out.push i
        pure (sortGNodes out.toList)
  | .dstep ax ke preds => do
      -- the dynamic node test (XPath 4.0 §4.7.5.3, §4.7.5.4): the key
      -- expression is evaluated with an absent focus
      let ks ← env.atomize (← eval n { env with ctx := none, pos := 0, size := 0 } ke)
      let os ← env.stepOrigins
      let mut out : Array Item := #[]
      for o in os do
        let cands ← match o with
          | .node c =>
            if ax == .item then err "XPTY0004" "the item axis is defined only for JNodes"
            pure (((env.axis ax c).filter (fun m =>
              env.testMatches ax m (.name .any) &&
              (let q := (env.nrec m).name
               ks.any (fun a => atomicEqual a (Atomic.ofQN q) || atomicEqual a (Atomic.ofStr q.loc))))).map Item.node)
          | j =>
            if ax == .attribute || ax == .namespace then
              err "XPTY0004" "the attribute and namespace axes are not defined for JNodes"
            pure ((jaxis ax j).filter (jkeyIn ks))
        let mut cur : Seq := cands
        for p in preds do
          cur ← filterSeq n env cur p
        for i in cur do out := out.push i
      pure (sortGNodes out.toList)
  | .filter a p => do
      if let some r ← rangeShortcut n env (.filter a p) then return r
      match a, isNumericLit p with
      | .seq es, some k =>
        -- `(e1, e2, ...)[k]`: evaluate only as far as item k
        let mut acc : Array Item := #[]
        for x in es do
          if acc.size ≥ k.toNat then break
          for i in ← eval n env x do acc := acc.push i
        pure (if k ≥ 1 && k.toNat ≤ acc.size then [acc.getD (k.toNat - 1) default] else [])
      | _, _ =>
        let s ← eval n env a
        filterSeq n env s p
  | .call q args kw => do
      if q.uri == nsFN && kw.isEmpty && (q.loc == "count" || q.loc == "head" || q.loc == "starts-with-subsequence" || q.loc == "ends-with-subsequence") then
        if let some r ← rangeShortcut n env (.call q args kw) then return r
      if isTmplMarker q then
        let s ← match args with | [some x] => eval n env x | _ => pure []
        let as ← env.atomize s
        pure (sStr (String.intercalate " " (as.map Atomic.str)))
      else if q.uri == nsXS then
        if q.loc == "NOTATION" || q.loc == "anyAtomicType" || q.loc == "anySimpleType" then
          err "XPST0017" ("no constructor function xs:" ++ q.loc)
        else
        -- the parameter of a constructor function is `$value` (F&O 4.0 §21.1)
        let args ← match args, kw with
          | _, [] => pure args
          | [], [("value", v)] => pure [v]
          | _, _ => err "XPST0017" ("constructor function xs:" ++ q.loc ++ " has one parameter, $value")
        match (if args.isEmpty then [some Expr.ctx] else args) with
        | [some x] =>
            let s ← eval n env x
            if s.length > 1 then err "XPTY0004" "constructor function argument has more than one item"
            match xsCtorType? q.loc with
            | some t => castTo env s t true
            | none => err "XPST0017" ("unknown constructor function xs:" ++ q.loc)
        | [none] => pure [.fn (.papp (.fn (.builtin q 1)) [none])]
        | _ => err "XPST0017" ("constructor function xs:" ++ q.loc ++ " takes one argument")
      else
      let total := args.length + kw.length
      -- fn:concat is sequence-variadic (F&O 4.0 §5.4.1): any arity
      let sig? := if q.uri == nsFN && q.loc == "concat" then some (default : Sig) else findSig q total
      match sig? with
      | none =>
          if (findSigAny q).isSome then err "XPST0017" ("wrong number of arguments for " ++ q.show)
          else err "XPST0017" ("unknown function " ++ q.show)
      | some sig =>
        if q.uri == nsFN && q.loc == "concat" then
          let args ← match args, kw with
            | _, [] => pure args
            | [], [("values", a)] => pure [a]
            | _, _ => err "XPST0017" "fn:concat has one parameter, $values"
          if args.any Option.isNone then
            pure [.fn (.papp (.fn (.builtin q args.length)) (← evalArgs n env args))]
          else
            let vs ← evalArgs n env args
            callFn n env q (vs.map (·.getD []))
        else
        -- place keyword arguments
        let mut slots : Array (Option (Option Expr)) := (sig.ps.map (fun _ => none)).toArray
        for (a, i) in args.zip (List.range args.length) do
          slots := slots.set! i (some a)
        for (k, a) in kw do
          match sig.ps.findIdx? (·.name == k) with
          | some i =>
            if (slots.getD i none).isSome then err "XPST0017" ("duplicate argument " ++ k)
            slots := slots.set! i (some a)
          | none => err "XPST0017" ("no parameter named " ++ k)
        -- placeholders make a partial application
        if slots.toList.any (fun s => match s with | some none => true | _ => false) then
          let mut fixed : List (Option Seq) := []
          let mut arity := 0
          for (sl, p) in slots.toList.zip sig.ps do
            match sl with
            | some none => fixed := fixed ++ [none]; arity := arity + 1
            | some (some x) => fixed := fixed ++ [some (← eval n env x)]
            | none =>
              match p.dflt with
              | some d => fixed := fixed ++ [some (← eval n env d)]
              | none => err "XPST0017" ("missing argument " ++ p.name)
          pure [.fn (.papp (.fn (.builtin q fixed.length)) fixed)]
        else
          let mut vals : List Seq := []
          let mut lastGiven := 0
          for (sl, i) in slots.toList.zip (List.range slots.size) do
            if sl.isSome then lastGiven := i + 1
          let _ := lastGiven
          for (sl, p) in slots.toList.zip sig.ps do
            match sl with
            | some (some x) => vals := vals ++ [← eval n env x]
            | _ =>
              match p.dflt with
              | some d => vals := vals ++ [← eval n env d]
              | none => err "XPST0017" ("missing argument " ++ p.name)
          callFn n env q vals
  | .dyn f args => do
      let fs ← eval n env f
      let fs := env.unwrapJ 64 .anyFn fs
      match fs with
      | [fi] =>
          if !fi.isFn then err "XPTY0004" "dynamic call of a value that is not a function"
          if args.any Option.isNone then
            -- the argument count must be the arity (XPath 4.0 §4.5.4)
            if let some k := fi.fnArity then
              if k != args.length then err "XPTY0004" "partial application with the wrong number of arguments"
            pure [.fn (.papp fi (← evalArgs n env args))]
          else
            let vs ← evalArgs n env args
            apply n env fi (vs.map (·.getD []))
      | _ =>
        -- XPath 4.0 (PR 1975): a sequence of function items is called item by
        -- item and the results are concatenated; the empty sequence gives ()
        if !fs.all Item.isFn then err "XPTY0004" "dynamic call of a value that is not a function"
        if args.any Option.isNone then
          let fixed ← evalArgs n env args
          pure (fs.map (fun fi => .fn (.papp fi fixed)))
        else
          let vs ← evalArgs n env args
          let mut out : Seq := []
          for fi in fs do
            out := out ++ (← apply n env fi (vs.map (·.getD [])))
          pure out
  | .fref q k => do
      if q.uri == nsXS then
        if k == 1 && (xsCtorType? q.loc).isSome then pure [.fn (.builtin q 1)]
        -- arity 0: the argument defaults to the focus at the reference
        else if k == 0 && (xsCtorType? q.loc).isSome then
          match env.ctx with
          | some c => pure [.fn (.papp (.fn (.builtin q 1)) [some c])]
          | none => pure [.fn (.builtin q 0)]
        else err "XPST0017" ("unknown function " ++ q.show ++ "#" ++ toString k)
      else if q.uri == nsFN && q.loc == "concat" then pure [.fn (.builtin q k)]
      -- fn:position#0 and fn:last#0 capture the focus (F&O 4.0 §1.5.2)
      else if q.uri == nsFN && k == 0 && (q.loc == "position" || q.loc == "last") && env.ctx.isSome then
        pure [focusFn q.loc env.pos env.size]
      else match findSig q k with
        | some sig =>
          -- a reference to a context-dependent function whose omitted
          -- argument defaults to `.` captures the focus (F&O 4.0 §1.5.2)
          match env.ctx, (sig.ps.drop k).head? with
          | some c, some p =>
            if dfltUsesFocus p.dflt then
              pure [.fn (.papp (.fn (.builtin q (k + 1))) (List.replicate k none ++ [some c]))]
            else pure [.fn (.builtin q k)]
          | _, _ => pure [.fn (.builtin q k)]
        | none => err "XPST0017" ("unknown function " ++ q.show ++ "#" ++ toString k)
  | .inline ps ret body focus => pure [.fn (.inline ps ret body focus env.vars)]
  | .mapC es => do
      let mut acc : MB := {}
      for (k, v) in es do
        if isMergeMarker v then
          let ms ← eval n env k
          for m in ms do
            match m with
            | .map kvs =>
              for (kk, vv) in kvs do
                if (acc.get? kk).isSome then err "XQDY0137" "duplicate key in map constructor"
                acc := acc.set kk vv
            | _ => err "XPTY0004" "map constructor entry is not a map"
        else
          let ks ← env.atomize (← eval n env k)
          match ks with
          | [kk] =>
            if (acc.get? kk).isSome then err "XQDY0137" ("duplicate key " ++ kk.str ++ " in map constructor")
            acc := acc.set kk (← eval n env v)
          | _ => err "XPTY0004" "a map key must be a single atomic value"
      pure [.map acc.toList]
  | .arrS es => do
      let mut ms : Array Seq := #[]
      for x in es do ms := ms.push (← eval n env x)
      pure [.arr ms.toList]
  | .arrC x => do
      let s ← eval n env x
      pure [.arr (s.map (fun i => [i]))]
  | .lookup a k => do
      let s ← eval n env a
      let mut out : Array Item := #[]
      for i in s do
        for r in ← lookupIn n env i k do out := out.push r
      pure out.toList
  | .ulookup k => do
      match env.ctx with
      | some [i] => lookupIn n env i k
      | some _ => err "XPTY0004" "unary lookup needs a single context item"
      | none => err "XPDY0002" "the context item is absent"
  | .bin op a b => do
      if op.isGeneral then
        if let some r ← rangeShortcut n env (.bin op a b) then return r
      evalBin n env op a b
  | .neg a => do
      match ← env.atomizeOpt (← eval n env a) with
      | none => pure []
      | some x =>
        let x ← if x.ty == .untyped then castAtomic x (.b .double) else pure x
        match x.num? with
        | some v => pure (single (numNeg v).atomic)
        | none => err "XPTY0004" "unary minus on a non-numeric value"
  | .plus a => do
      match ← env.atomizeOpt (← eval n env a) with
      | none => pure []
      | some x =>
        let x ← if x.ty == .untyped then castAtomic x (.b .double) else pure x
        match x.num? with
        | some v => pure (single v.atomic)
        | none => err "XPTY0004" "unary plus on a non-numeric value"
  | .ifE c t e => do
      if ← ebv (← eval n env c) then eval n env t else eval n env e
  | .forE kind v v2 posv vt src body => do
      let s ← eval n env src
      let items : List (Seq × Option Seq) ← match kind with
        | .item => pure (s.map (fun i => ([i], none)))
        -- a sequence of arrays or maps is iterated in turn (XPath 4.0
        -- §4.13.2, PR 2715)
        | .member => s.flatMapM (fun i => match i with
            | .arr ms => pure (ms.map (fun m => (m, none)))
            | _ => err "XPTY0004" "for member requires arrays")
        | .entry => s.flatMapM (fun i => match i with
            | .map kvs => pure (kvs.map (fun (k, vv) => ([.atom k], some vv)))
            | _ => err "XPTY0004" "for key/value requires maps")
      let mut out : Array Item := #[]
      let mut idx := 1
      for (x, y) in items do
        let x ← env.coerce vt x ("$" ++ v.show)
        let mut env' := env.bind v x
        match v2, y with
        | some q2, some yv => env' := env'.bind q2 yv
        | _, _ => pure ()
        match posv with
        | some pv => env' := env'.bind pv (sInt idx)
        | none => pure ()
        for r in ← eval n env' body do out := out.push r
        idx := idx + 1
      pure out.toList
  | .letE v vt x body => do
      let s ← eval n env x
      let s ← env.coerce vt s ("$" ++ v.show)
      eval n (env.bind v s) body
  | .quant every v vt src sat => do
      let s ← eval n env src
      let mut res := every
      for i in s do
        let x ← env.coerce vt [i] ("$" ++ v.show)
        let b ← ebv (← eval n (env.bind v x) sat)
        if every && !b then res := false; break
        if !every && b then res := true; break
      pure (sBool res)
  | .instOf a t => do
      let s ← eval n env a
      pure (sBool (env.seqMatches s t))
  | .treat a t => do
      let s ← eval n env a
      if env.seqMatches s t then pure s else err "XPDY0050" "treat as: value does not match the type"
  | .cast a t opt => do castTo env (← eval n env a) t opt
  | .castable a t opt => do
      let s ← eval n env a
      match t with
      | .atomic aty =>
        if aty == .b .anyAtomicType || aty == .b .notation then err "XPST0080" "castable to an abstract type"
      | .jnodeT .. | .xnode => err "XPST0080" "castable target is not an atomic, array or map type"
      | .anyArr | .anyMap | .arrT _ | .mapT _ _ | .record _ _ =>
        return sBool (match castTo env s t opt with | .ok _ => true | .error _ => false)
      | t => if !isCastTarget t then err "XPST0051" "castable target is not an atomic, array, map or record type"
      match env.atomize s with
      | .error e => if e.code == "FOTY0013" then throw e else pure (sBool false)
      | .ok _ =>
        match castTo env s t opt with
        | .ok _ => pure (sBool true)
        | .error _ => pure (sBool false)
  | .smap a b => do
      let s ← eval n env a
      let sz := s.length
      let mut out : Array Item := #[]
      let mut idx := 1
      for i in s do
        for r in ← eval n (env.focus i idx sz) b do out := out.push r
        idx := idx + 1
      pure out.toList
  | .pipe a b => do
      let s ← eval n env a
      eval n { env with ctx := some s, pos := 1, size := 1 } b
  | .mapArrow a f args => do
      let s ← eval n env a
      let fs ← eval n env f
      match fs with
      | [fi] =>
        let rest ← evalArgs n env args
        let mut out : Array Item := #[]
        for i in s do
          -- a placeholder makes a partial application for each item
          if rest.any Option.isNone then out := out.push (.fn (.papp fi (some [i] :: rest)))
          else
          for r in ← apply n env fi ([i] :: rest.map (·.getD [])) do out := out.push r
        pure out.toList
      | _ => err "XPTY0004" "=!> target must be a single function"
  | .tmpl parts => do
      let mut out := ""
      for p in parts do
        let s ← eval n env p
        for x in ← env.atomize s do out := out ++ x.str
      pure (sStr out)

def evalArgs : Nat → Env → List (Option Expr) → M (List (Option Seq))
  | 0, _, _ => fuelErr
  | n + 1, env, args => args.mapM (fun a => match a with
      | some x => do pure (some (← eval n env x))
      | none => pure none)

/-- Apply predicate `p` to `s` (§4.3.1): a numeric value selects by
    position, anything else by effective boolean value. -/
def filterSeq : Nat → Env → Seq → Expr → M Seq
  | 0, _, _, _ => fuelErr
  | n + 1, env, s, p =>
    match isNumericLit p with
    | some k => pure (if k ≥ 1 && k.toNat ≤ s.length then [s.getD (k.toNat - 1) default] else [])
    | none => do
      let sz := s.length
      let mut out : Array Item := #[]
      let mut idx := 1
      for i in s do
        let r ← eval n (env.focus i idx sz) p
        let isNum (x : Item) : Bool := match x with | .atom a => a.isNumeric | _ => false
        let keep ← match r with
          | [.atom a] => match a.num? with
            | some num => pure (match numCmp num (.i idx) with | some .eq => true | _ => false)
            | none => ebv r
          | _ =>
            -- XPath 4.0: a sequence of numbers selects those positions
            if r.length > 1 && r.all isNum then
              pure (r.any (fun x => match x with
                | .atom a => match a.num? with
                  | some num => (match numCmp num (.i idx) with | some .eq => true | _ => false)
                  | none => false
                | _ => false))
            else ebv r
        if keep then out := out.push i
        idx := idx + 1
      pure out.toList

def lookupIn : Nat → Env → Item → Option Expr → M Seq
  | 0, _, _, _ => fuelErr
  | n + 1, env, i, k =>
    match i with
    | .map kvs => do
      match k with
      | none => pure (kvs.flatMap (·.2))
      | some kx => do
        let ks ← env.atomize (← eval n env kx)
        let mut out : Array Item := #[]
        for key in ks do
          match mapGet kvs key with
          | some v => for x in v do out := out.push x
          | none => pure ()
        pure out.toList
    | .arr ms => do
      match k with
      | none => pure ms.flatten
      | some kx => do
        let ks ← env.atomize (← eval n env kx)
        let mut out : Array Item := #[]
        for key in ks do
          let key ← if key.ty == .untyped then castAtomic key (.b .integer) else pure key
          match key.v with
          | .int j => for x in ← arrIdx ms j do out := out.push x
          | _ => err "XPTY0004" "array lookup key must be an integer"
        pure out.toList
    | .jnode _ _ v _ => do
      -- XPath 4.0 §4.13.3: the ·jvalue· of a JNode is looked up
      let mut out : Array Item := #[]
      for x in v do
        match x with
        | .map _ | .arr _ => for r in ← lookupIn n env x k do out := out.push r
        | _ => err "XPTY0004" "lookup on a JNode whose value is not a map or array"
      pure out.toList
    | _ => err "XPTY0004" "lookup on a value that is not a map or array"

def evalBin : Nat → Env → BOp → Expr → Expr → M Seq
  | 0, _, _, _, _ => fuelErr
  | n + 1, env, op, a, b =>
    match op with
    | .or => do
        if ← ebv (← eval n env a) then pure (sBool true) else pure (sBool (← ebv (← eval n env b)))
    | .and => do
        if !(← ebv (← eval n env a)) then pure (sBool false) else pure (sBool (← ebv (← eval n env b)))
    | .otherwise => do
        let s ← eval n env a
        if s.isEmpty then eval n env b else pure s
    | .concat => do
        let x ← env.atomizeOpt (← eval n env a)
        let y ← env.atomizeOpt (← eval n env b)
        pure (sStr ((x.map Atomic.str).getD "" ++ (y.map Atomic.str).getD ""))
    | .to => do
        let x ← env.atomizeOpt (← eval n env a)
        let y ← env.atomizeOpt (← eval n env b)
        match x, y with
        | some x, some y =>
          let x ← coerceAtom [.b .integer] x
          let y ← coerceAtom [.b .integer] y
          match x.v, y.v with
          | .int lo, .int hi =>
            if hi < lo then pure []
            else if hi - lo > maxRange then err "FOAR0002" "range too large for this implementation"
            else pure ((List.range (hi - lo + 1).toNat).map (fun (k : Nat) => .atom (Atomic.ofInt (lo + (k : Int)))))
          | _, _ => err "XPTY0004" "range bounds must be integers"
        | _, _ => pure []
    | .union | .intersect | .except => do
        let x ← eval n env a
        let y ← eval n env b
        match nodesOf x, nodesOf y with
        | some xs, some ys =>
          let r := match op with
            | .union => xs ++ ys
            | .intersect => xs.filter (fun m => ys.contains m)
            | _ => xs.filter (fun m => !ys.contains m)
          pure ((sortNodes r).map Item.node)
        | _, _ =>
          match gnodesOf x, gnodesOf y with
          | some xs, some ys =>
            let r := match op with
              | .union => xs ++ ys
              | .intersect => xs.filter (fun m => ys.any (gnodeEq m))
              | _ => xs.filter (fun m => !ys.any (gnodeEq m))
            pure (sortGNodes r)
          | _, _ => err "XPTY0004" "union/intersect/except operands must be nodes"
    | _ =>
      if op.isGeneral then do
        let xs ← env.atomize (← eval n env a)
        let ys ← env.atomize (← eval n env b)
        let mut res := false
        for x in xs do
          for y in ys do
            if ← generalPair env.tz op x y env.nsResolve then res := true; break
          if res then break
        pure (sBool res)
      else if op.isValue then do
        let x ← env.atomizeOpt (← eval n env a)
        let y ← env.atomizeOpt (← eval n env b)
        match x, y with
        | some x, some y => pure (sBool (← valueCmp env.tz op x y))
        | _, _ => pure []
      else if op.isNodeCmp then do
        let x ← eval n env a
        let y ← eval n env b
        match x, y with
        | [], _ => pure []
        | _, [] => pure []
        | [.node p], [.node q] =>
          pure (sBool (match op with
            | .is => p == q | .isNot => p != q
            | .precedes => nodeLt p q | .follows => nodeLt q p
            | .precedesOrIs => p == q || nodeLt p q
            | _ => p == q || nodeLt q p))
        | [p], [q] =>
          if !(p.isGNode && q.isGNode) then err "XPTY0004" "node comparison operands must be single nodes"
          else pure (sBool (match op with
            | .is => gnodeEq p q | .isNot => !gnodeEq p q
            | .precedes => gnodeLt p q | .follows => gnodeLt q p
            | .precedesOrIs => gnodeEq p q || gnodeLt p q
            | _ => gnodeEq p q || gnodeLt q p))
        | _, _ => err "XPTY0004" "node comparison operands must be single nodes"
      else match op.arOp? with
        | some ar => do
          let x ← env.atomizeOpt (← eval n env a)
          let y ← env.atomizeOpt (← eval n env b)
          match x, y with
          | some x, some y => pure (single (← arith env.tz ar x y))
          | _, _ => pure []
        | none => err "XPST0003" "unknown operator"

/-- Apply a function item to argument values. -/
def apply : Nat → Env → Item → List Seq → M Seq
  | 0, _, _, _ => fuelErr
  | n + 1, env, f, args =>
    match f with
    | .map kvs => do
        if args.length != 1 then err "XPTY0004" "a map takes one argument"
        match ← env.atomizeOpt (args.headD []) with
        | some k => pure ((mapGet kvs k).getD [])
        | none => err "XPTY0004" "map key must be a single atomic value"
    | .arr ms => do
        if args.length != 1 then err "XPTY0004" "an array takes one argument"
        match ← env.atomizeOpt (args.headD []) with
        | some k =>
          let k ← if k.ty == .untyped then castAtomic k (.b .integer) else pure k
          match k.v with
          | .int j => arrIdx ms j
          | _ => err "XPTY0004" "array index must be an integer"
        | none => err "XPTY0004" "array index must be a single integer"
    | .fn (.builtin q k) => do
        if args.length != k then err "XPTY0004" ("function " ++ q.show ++ " expects " ++ toString k ++ " arguments")
        if q.uri == nsXS then
          if k == 0 then err "XPDY0002" "the context value is absent"
          match xsCtorType? q.loc with
          | some t => castTo env (args.headD []) t true
          | none => err "XPST0017" ("unknown constructor function " ++ q.show)
        else if q.uri == nsFN && q.loc == "concat" then callFn n env q args
        else
        match findSig q k with
        | some sig =>
          -- defaults for parameters beyond the arity
          let mut vals := args
          for p in sig.ps.drop k do
            match p.dflt with
            | some d => vals := vals ++ [← eval n { env with ctx := none } d]
            | none => pure ()
          callFn n env q vals
        | none => err "XPST0017" ("unknown function " ++ q.show)
    | .fn (.inline ps ret body focus cl) => do
        if focus then
          if args.length != 1 then err "XPTY0004" "a focus function takes one argument"
          let a := args.headD []
          let env' := { env with vars := cl, ctx := some a, pos := 1, size := 1 }
          eval n env' body
        else
          if args.length != ps.length then
            err "XPTY0004" ("inline function expects " ++ toString ps.length ++ " arguments, got " ++ toString args.length)
          let mut vars := cl
          for ((v, t), a) in ps.zip args do
            vars := (v, ← env.coerce t a ("$" ++ v.show)) :: vars
          let env' := { env with vars, ctx := none, pos := 0, size := 0 }
          let r ← eval n env' body
          env.coerce ret r "function result"
    | .fn (.papp g fixed) => do
        let mut rest := args
        let mut full : List Seq := []
        for fx in fixed do
          match fx with
          | some v => full := full ++ [v]
          | none =>
            match rest with
            | a :: r => full := full ++ [a]; rest := r
            | [] => err "XPTY0004" "too few arguments for a partial application"
        if !rest.isEmpty then err "XPTY0004" "too many arguments for a partial application"
        apply n env g full
    | _ => err "XPTY0004" "not a function item"

/-- Call a built-in function by name, with the full argument list:
    coerce to the signature, then run the implementation. -/
def callFn : Nat → Env → QN → List Seq → M Seq
  | 0, _, _, _ => fuelErr
  | n + 1, env, q, args => do
    let args ← if q.uri == nsFN && q.loc == "concat" then
        args.mapM (fun a => do pure (seqOfAtoms (← env.atomize a)))
      else match findSig q args.length with
        | some sig => (args.zip sig.ps).mapM (fun (a, p) => env.coerce p.ty a ("$" ++ p.name ++ " of " ++ q.show))
        | none => pure args
    match libLookupAll q with
    | some impl => do
      let r ← impl { call := fun f as => apply n env f as } env args
      -- date results stay within the limits (`checkLimits`)
      match r with
      | [.atom a@⟨_, .x (.dt ..)⟩] => pure [.atom (← checkLimits a)]
      | _ => pure r
    | none => err "XPST0017" ("function " ++ q.show ++ " is not implemented")

/-- A range expression `a to b` (possibly parenthesised, possibly under
    `fn:reverse`) whose bounds are integers and whose length is above
    `maxRange`: `(lo, hi, reversed)`. Such a range is not materialized;
    `rangeShortcut` answers the expressions over it that need only its
    bounds (XPath 4.0 §4.8.1: the value is the same). -/
def largeRangeOf? : Nat → Env → Expr → M (Option (Int × Int × Bool))
  | 0, _, _ => pure none
  | n + 1, env, e =>
    match e with
    | .seq [x] => largeRangeOf? n env x
    | .bin .to a b => do
        let x ← env.atomizeOpt (← eval n env a)
        let y ← env.atomizeOpt (← eval n env b)
        match x, y with
        | some x, some y =>
          let x ← coerceAtom [.b .integer] x
          let y ← coerceAtom [.b .integer] y
          match x.v, y.v with
          | .int lo, .int hi => pure (if hi - lo > maxRange then some (lo, hi, false) else none)
          | _, _ => pure none
        | _, _ => pure none
    | .call q [some x] [] =>
        if q.uri == nsFN && q.loc == "reverse" then do
          pure ((← largeRangeOf? n env x).map (fun (lo, hi, r) => (lo, hi, !r)))
        else pure none
    | _ => pure none

/-- The `k`-th item (1-based) of a range. -/
def rangeAt (lo hi : Int) (rev : Bool) (k : Int) : Seq :=
  if k < 1 || k > hi - lo + 1 then [] else sInt (if rev then hi - k + 1 else lo + k - 1)

/-- The items of a range from position `i` (1-based), `len` of them. -/
def rangeSlice (lo hi : Int) (rev : Bool) (i len : Nat) : Seq :=
  (List.range len).filterMap (fun (j : Nat) => match rangeAt lo hi rev (i + j) with
    | [x] => some x
    | _ => none)

/-- Expressions over a large range that need only its bounds: `count`,
    a numeric predicate, a general comparison with one integer,
    `starts-with-subsequence`, `ends-with-subsequence`, and
    `head(drop-while(...))`. `none`: evaluate as usual. -/
def rangeShortcut : Nat → Env → Expr → M (Option Seq)
  | 0, _, _ => pure none
  | n + 1, env, e =>
    match e with
    | .call q [some x] [] =>
      if q.uri != nsFN then pure none
      else if q.loc == "count" then do
        match ← largeRangeOf? n env x with
        | some (lo, hi, _) => pure (some (sInt (hi - lo + 1)))
        | none => pure none
      else if q.loc == "head" then do
        match x with
        | .call q2 [some r, some f] [] =>
          if q2.uri == nsFN && q2.loc == "drop-while" then
            match ← largeRangeOf? n env r with
            | some (lo, hi, rev) =>
              let fs ← eval n env f
              let some fi := fs.head? | pure none
              let size := (hi - lo + 1).toNat
              let mut res : Seq := []
              for j in [0:size] do
                let v := rangeAt lo hi rev (j + 1)
                let keep ← ebv (← apply n env fi (if fi.fnArity == some 1 then [v] else [v, sInt (j + 1)]))
                if !keep then res := v; break
              pure (some res)
            | none => pure none
          else pure none
        | _ => pure none
      else pure none
    | .call q (some r :: some s :: rest) [] =>
      if q.uri == nsFN && (q.loc == "starts-with-subsequence" || q.loc == "ends-with-subsequence") then do
        match ← largeRangeOf? n env r with
        | some (lo, hi, rev) =>
          let sv ← eval n env s
          let size := (hi - lo + 1).toNat
          let k := min sv.length size
          let part := if q.loc == "starts-with-subsequence" then rangeSlice lo hi rev 1 k
            else rangeSlice lo hi rev (size - k + 1) k
          let restV ← rest.mapM (fun a => match a with | some y => eval n env y | none => pure [])
          pure (some (← callFn n env q (part :: sv :: restV)))
        | none => pure none
      else pure none
    | .filter r p =>
      match isNumericLit p with
      | some k => do
        match ← largeRangeOf? n env r with
        | some (lo, hi, rev) => pure (some (rangeAt lo hi rev k))
        | none => pure none
      | none => pure none
    | .bin op a b =>
      if !op.isGeneral then pure none else do
      -- one side a large range, the other one integer
      let (rangeSide, other, flipped) ← match ← largeRangeOf? n env a with
        | some rg => pure (some rg, b, true)
        | none => pure ((← largeRangeOf? n env b), a, false)
      match rangeSide with
      | none => pure none
      | some (lo, hi, _) =>
        match ← env.atomize (← eval n env other) with
        | [⟨_, .int x⟩] =>
          -- `x op v` for some v in lo..hi (the operands in source order)
          let op' := if flipped then (match op with
            | .glt => .ggt | .gle => .gge | .ggt => .glt | .gge => .gle | o => o) else op
          let r := match op' with
            | .geq => lo ≤ x && x ≤ hi
            | .gne => hi > lo || x != lo
            | .glt => x < hi
            | .gle => x ≤ hi
            | .ggt => x > lo
            | .gge => x ≥ lo
            | _ => false
          pure (some (sBool r))
        | _ => pure none
    | _ => pure none

end

/-- Evaluate an XPath 4.0 expression string. -/
def evalString (src : String) (env : Env := {}) : M Seq := do
  let e ← parseXPath src env.ns
  eval 100000 env e

def showSeq (s : Seq) : String :=
  String.intercalate " " (s.map (fun i => match i with
    | .atom a => a.str
    | .node _ => "<node>"
    | .map _ => "map{...}"
    | .arr _ => "[...]"
    | .fn _ => "function"
    | .jnode .. => "<jnode>"))

def evalShow (src : String) : String :=
  match evalString src with
  | .ok s => showSeq s
  | .error e => "error " ++ e.code ++ ": " ++ e.msg

#guard evalShow "1 + 2 * 3" == "7"
#guard evalShow "for $x in 1 to 3 return $x * 2" == "2 4 6"
#guard evalShow "map { 'a' : 1, 'b' : 2 }?b" == "2"
#guard evalShow "[1, 2, 3]?2" == "2"
#guard evalShow "fold-left(1 to 5, 0, function($a, $b) { $a + $b })" == "15"
#guard evalShow "(3, 1, 2) => sort()" == "1 2 3"
#guard evalShow "'abc' || 'def'" == "abcdef"
#guard evalShow "1 div 0" == "error FOAR0001: division by zero"
#guard evalShow "substring('motor car', 6)" == " car"
#guard evalShow "let $f := concat('a', ?, 'c') return $f('b')" == "abc"
#guard evalShow "xs:double('1e3') instance of xs:double" == "true"
#guard evalShow "() otherwise 5" == "5"
#guard evalShow "`x{1+1}y`" == "x2y"

end L4Factoidal.XPath4
