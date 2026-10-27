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
import L4Factoidal.XPath4.Lib

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
def arith (tz : Int) (op : ArOp) (a b : Atomic) : M Atomic := do
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
      if op == .div && f == 0 && n.rank < 2 then err "FOAR0001" "division of a duration by zero" else
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
      else err "XPTY0004" "cannot multiply an xs:duration with both month and second parts"
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
      else if y.isNumeric then castAtomic x (.b .double)
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

/-- `cast as` to an item type. -/
def castTo (e : Env) (s : Seq) (t : IType) (opt : Bool) : M Seq := do
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
      let c ← env.ctxNode
      let r := env.treeRoot c
      if (env.nrec r).kind != .document then err "XPDY0050" "the root of the tree is not a document node"
      pure [.node r]
  | .slash a b => do
      let left ← eval n env a
      match nodesOf left with
      | none => err "XPTY0004" "the left operand of '/' must be nodes"
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
        | none => if res.any Item.isNode then err "XPTY0018" "a path step returned both nodes and non-nodes" else pure res
  | .step ax t preds => do
      let c ← env.ctxNode
      let ns := (env.axis ax c).filter (fun m => env.testMatches ax m t)
      let mut cur : Seq := ns.map Item.node
      for p in preds do
        cur ← filterSeq n env cur p
      match nodesOf cur with
      | some rs => pure ((sortNodes rs).map Item.node)
      | none => pure cur
  | .filter a p => do
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
      if isTmplMarker q then
        let s ← match args with | [some x] => eval n env x | _ => pure []
        let as ← env.atomize s
        pure (sStr (String.intercalate " " (as.map Atomic.str)))
      else if q.uri == nsXS then
        if q.loc == "NOTATION" || q.loc == "anyAtomicType" || q.loc == "anySimpleType" then
          err "XPST0017" ("no constructor function xs:" ++ q.loc)
        else
        match (if args.isEmpty then [some Expr.ctx] else args) with
        | [some x] =>
            let s ← eval n env x
            if s.length > 1 then err "XPTY0004" "constructor function argument has more than one item"
            match atypeOfName? q.loc with
            | some t => castTo env s (.atomic t) true
            | none => if q.loc == "numeric" then castTo env s (.choice [.atomic (.b .double)]) true
                      else err "XPST0017" ("unknown constructor function xs:" ++ q.loc)
        | [none] => pure [.fn (.papp (.fn (.builtin q 1)) [none])]
        | _ => err "XPST0017" ("constructor function xs:" ++ q.loc ++ " takes one argument")
      else
      let total := args.length + kw.length
      let sig? := if q.uri == nsFN && q.loc == "concat" then
          (if total ≥ 2 then some (default : Sig) else none) else findSig q total
      match sig? with
      | none =>
          if (findSigAny q).isSome then err "XPST0017" ("wrong number of arguments for " ++ q.show)
          else err "XPST0017" ("unknown function " ++ q.show)
      | some sig =>
        if q.uri == nsFN && q.loc == "concat" then
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
      match fs with
      | [fi] =>
          if !fi.isFn then err "XPTY0004" "dynamic call of a value that is not a function"
          if args.any Option.isNone then
            pure [.fn (.papp fi (← evalArgs n env args))]
          else
            let vs ← evalArgs n env args
            apply n env fi (vs.map (·.getD []))
      | _ => err "XPTY0004" "dynamic call requires exactly one function item"
  | .fref q k => do
      if q.uri == nsXS then
        if k == 1 && ((atypeOfName? q.loc).isSome || q.loc == "numeric") && q.loc != "NOTATION" && q.loc != "anyAtomicType" then pure [.fn (.builtin q 1)]
        else err "XPST0017" ("unknown function " ++ q.show ++ "#" ++ toString k)
      else if q.uri == nsFN && q.loc == "concat" && k ≥ 2 then pure [.fn (.builtin q k)]
      else match findSig q k with
        | some _ => pure [.fn (.builtin q k)]
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
  | .bin op a b => evalBin n env op a b
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
        | .member => match s with
            | [.arr ms] => pure (ms.map (fun m => (m, none)))
            | _ => err "XPTY0004" "for member requires a single array"
        | .entry => match s with
            | [.map kvs] => pure (kvs.map (fun (k, vv) => ([.atom k], some vv)))
            | _ => err "XPTY0004" "for key/value requires a single map"
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
      | _ => pure ()
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
          match atypeOfName? q.loc with
          | some t => castTo env (args.headD []) (.atomic t) true
          | none => castTo env (args.headD []) (.choice [.atomic (.b .double)]) true
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
    match libLookup q with
    | some impl => impl { call := fun f as => apply n env f as } env args
    | none => err "XPST0017" ("function " ++ q.show ++ " is not implemented")

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
    | .fn _ => "function"))

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
