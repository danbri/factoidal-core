import L4Factoidal.JS.Value
import L4Factoidal.JS.Parser

/-!
# L4Factoidal.JS.Interp — the evaluator

A definitional interpreter: one Lean function per group of ECMA-262 runtime
semantics (`Evaluation` of §13 and §14, `[[Call]]` and `[[Construct]]` of §10.2,
the abstract operations of §7), over the heap of `Value.lean`, in the monad
`M = EStateM Abrupt Heap`. A thrown JavaScript value is `Abrupt.throw`; `return`,
`break` and `continue` are statement completions (`Compl`).

Every function of the mutual block takes a fuel argument and passes a smaller
one to each recursive call, so the block is total by structural recursion: each
nested evaluation and each loop iteration uses one unit. The fuel is not the
budget of a script: `Heap.steps` counts loop iterations and calls and stops a
script that runs too long (`Abrupt.halt`), and `Heap.maxDepth` turns deep
recursion into a `RangeError`, as engines do.
-/

namespace L4Factoidal.JS

/-! ## Heap primitives -/

def alloc (o : Obj) : M Nat := modifyGet fun h => (h.objs.size, { h with objs := h.objs.push o })
def getObj (id : Nat) : M Obj := do pure ((← get).obj id)
def modifyObj (id : Nat) (f : Obj → Obj) : M Unit :=
  modify fun h => { h with objs := h.objs.modify id f }
def realm : M Realm := do pure (← get).realm

def newEnv (parent : Option Nat) : M Nat :=
  modifyGet fun h => (h.envs.size, { h with envs := h.envs.push { parent } })

def declare (env : Nat) (name : String) (b : Binding) : M Unit :=
  modify fun h => { h with envs := h.envs.modify env fun e => { e with vars := e.vars.insert name b } }

def getBinding (env : Nat) (name : String) : M (Option Binding) := do
  pure (((← get).envs.getD env default).vars.get? name)

def tick : M Unit := do
  let h ← get
  if h.steps == 0 then throw (.halt "step budget exhausted")
  set { h with steps := h.steps - 1 }

/-- Set or add an own data property with all attributes true (CreateDataProperty). -/
def Obj.putOwn (o : Obj) (key : String) (p : PropV) : Obj :=
  match o.kind, arrayIndex? key, p with
  | .array es, some i, .data v _ _ _ =>
    if i < es.size then { o with kind := .array (es.set! i v) }
    else if i == es.size then { o with kind := .array (es.push v) }
    else if i < es.size + 100000 then
      { o with kind := .array ((es ++ Array.replicate (i - es.size) Value.undef).push v) }
    else
      { o with props := o.props.insert key p, keys := if o.props.contains key then o.keys else o.keys.push key }
  | _, _, _ =>
    { o with props := o.props.insert key p, keys := if o.props.contains key then o.keys else o.keys.push key }

def defineOwn (id : Nat) (key : String) (p : PropV) : M Unit := modifyObj id (·.putOwn key p)

def setHidden (id : Nat) (key : String) (v : Value) : M Unit :=
  defineOwn id key (.data v true false true)

def deleteOwn (id : Nat) (key : String) : M Unit :=
  modifyObj id fun o =>
    match o.kind, arrayIndex? key with
    | .array es, some i =>
      if i + 1 == es.size then { o with kind := .array es.pop }
      else if i < es.size then { o with kind := .array (es.set! i .undef) }
      else o
    | _, _ => { o with props := o.props.erase key, keys := o.keys.filter (· != key) }

def mkError (k : ErrKind) (msg : String) : M Value := do
  let r ← realm
  let id ← alloc { proto := .obj (r.errorProtos.getD k.idx r.objectProto), kind := .error }
  setHidden id "message" (.str msg)
  pure (.obj id)

def throwErr {α} (k : ErrKind) (msg : String) : M α := do
  throw (.throw (← mkError k msg))

def newObject : M Nat := do alloc { proto := .obj (← realm).objectProto }

def newArray (es : Array Value) : M Value := do
  pure (.obj (← alloc { proto := .obj (← realm).arrayProto, kind := .array es }))

def isCallable (v : Value) : M Bool := do
  match v with
  | .obj id => pure (← getObj id).kind.callable
  | _ => pure false

def typeOf (v : Value) : M String := do
  match v with
  | .undef => pure "undefined"
  | .null => pure "object"
  | .bool _ => pure "boolean"
  | .num _ => pure "number"
  | .str _ => pure "string"
  | .obj id => pure (typeOfKind (← getObj id).kind)

/-- A function object for a native, with `name` and `length`. -/
def mkNative (id : Native) (name : String) (len : Nat) : M Value := do
  let r ← realm
  let o ← alloc { proto := .obj r.functionProto, kind := .native id }
  defineOwn o "length" (.data (.num (Float.ofNat len)) false false true)
  defineOwn o "name" (.data (.str name) false false true)
  pure (.obj o)

def method (target : Nat) (name : String) (id : Native) (len : Nat) : M Unit := do
  setHidden target name (← mkNative id name len)

/-- OrdinaryFunctionCreate and MakeConstructor (§10.2.3, §10.2.5). -/
def makeClosure (ctx : Ctx) (f : FunDef) (nameHint : String := "") : M Value := do
  let r ← realm
  -- a named function expression sees its own name (§15.2.5)
  let env ← match f.name with
    | some n => if f.arrow then pure ctx.env else do
        let e ← newEnv (some ctx.env); pure e
    | none => pure ctx.env
  let id ← alloc { proto := .obj r.functionProto, kind := .closure f env ctx.thisV }
  if env != ctx.env then
    if let some n := f.name then declare env n { v := .obj id, mutable := false }
  defineOwn id "length" (.data (.num (Float.ofNat f.params.length)) false false true)
  defineOwn id "name" (.data (.str (f.name.getD nameHint)) false false true)
  if !f.arrow then
    let p ← newObject
    setHidden p "constructor" (.obj id)
    defineOwn id "prototype" (.data (.obj p) true false false)
  pure (.obj id)

/-- The `[[Get]]` of a property found on the chain, without accessors. -/
def ownValue (id : Nat) (key : String) : M Value := do
  match (← get).findProp id key 1000 with
  | some (.data v ..) => pure v
  | _ => pure .undef

def protoOf (v : Value) : M Value := do
  let r ← realm
  match v with
  | .obj id => pure (← getObj id).proto
  | .str _ => pure (.obj r.stringProto)
  | .num _ => pure (.obj r.numberProto)
  | .bool _ => pure (.obj r.booleanProto)
  | _ => pure .null

def keyOfNum (x : Float) : String := numToString x

/-- Enumerable string keys of an object and its prototypes (§14.7.5.9 EnumerateObjectProperties). -/
def enumKeys (v : Value) : M (Array String) := do
  let h ← get
  let rec go : Nat → Value → Array String → Array String → Array String
    | 0, _, _, acc => acc
    | fuel + 1, .obj id, seen, acc =>
      let o := h.obj id
      let ks := o.ownKeys
      let acc := ks.foldl (fun a k =>
        if seen.contains k then a
        else match o.getOwn k with
          | some p => if p.enumerable then a.push k else a
          | none => a) acc
      go fuel o.proto (seen ++ ks) acc
    | _ + 1, _, _, acc => acc
  match v with
  | .obj _ => pure (go 1000 v #[] #[])
  | .str s => pure ((List.range s.length).toArray.map toString)
  | _ => pure #[]

def numV (x : Float) : Value := .num x
def intV (i : Int) : Value := .num (Float.ofInt i)

def argD (args : Array Value) (i : Nat) : Value := args.getD i .undef

/-- The `this` string of String.prototype methods (§22.1.3: RequireObjectCoercible). -/
def thisPrim (v : Value) : M Value := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .prim p => pure p
    | _ => pure v
  | _ => pure v

/-- Clamp a relative index (§23.1.3.30 slice, start/end). -/
def relIndex (x : Float) (len : Nat) : Nat :=
  let r := toIntegerOrInf x
  if r < 0 then
    let k := len.toFloat + r
    if k < 0 then 0 else k.toUInt64.toNat
  else if r > len.toFloat then len else r.toUInt64.toNat

def charsOf (s : String) : Array Char := s.toList.toArray

def substr (s : String) (i j : Nat) : String := String.ofList ((charsOf s).extract i j).toList

def indexOfFrom (s pat : String) (from_ : Nat) : Option Nat :=
  let cs := charsOf s; let ps := charsOf pat
  if ps.size == 0 then (if from_ ≤ cs.size then some from_ else some cs.size) else
  let rec go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if i + ps.size > cs.size then none
      else if (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then some i
      else go fuel (i + 1)
  go (cs.size + 1) from_

def lastIndexOfStr (s pat : String) : Option Nat :=
  let cs := charsOf s; let ps := charsOf pat
  if ps.size > cs.size then none else
  let rec go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then some i
      else if i == 0 then none else go fuel (i - 1)
  go (cs.size + 1) (cs.size - ps.size)

def splitOn (s sep : String) : Array String :=
  if sep.isEmpty then (charsOf s).map String.singleton
  else (s.splitOn sep).toArray

/-- `parseInt` (§19.2.5). -/
def parseIntStr (s : String) (radix : Int) : Float :=
  let cs := (trimJs s).toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let (r, cs) :=
    if radix == 0 || radix == 16 then
      match cs with
      | '0' :: 'x' :: rest | '0' :: 'X' :: rest => ((16 : Int), rest)
      | _ => ((if radix == 0 then 10 else radix), cs)
    else (radix, cs)
  if r < 2 || r > 36 then nan else
  let dv (c : Char) : Option Nat :=
    let d := if c.isDigit then some (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 55) else none
    d.bind fun d => if d < r.toNat then some d else none
  let ds := cs.takeWhile fun c => (dv c).isSome
  if ds.isEmpty then nan else
  let v := ds.foldl (fun a c => a * r.toNat + (dv c).getD 0) 0
  let f := if r == 10 then floatOfNat v else floatOfNat v
  if neg then -f else f

/-- `parseFloat` (§19.2.4): the longest prefix that is a StrDecimalLiteral. -/
def parseFloatStr (s : String) : Float :=
  let t := trimJs s
  let cs := t.toList
  let body := match cs with | '-' :: r => r | '+' :: r => r | r => r
  let neg := cs.head? == some '-'
  if String.ofList (body.take 8) == "Infinity" then (if neg then -inf else inf) else
  -- longest prefix accepted by strToNumber
  let n := cs.length
  let rec go : Nat → Float
    | 0 => nan
    | k + 1 =>
      let pre := String.ofList (cs.take (k + 1))
      let last := pre.back
      let f := if last == 'e' || last == 'E' || last == '+' || last == '-' then nan else strToNumber pre
      if f.isNaN then go k else f
  go n

/-! ## The evaluator -/

set_option maxHeartbeats 2000000 in
mutual

/-- `[[Get]]` on any value (§7.3.2 GetV). -/
def getV : Nat → Value → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, key => do
    match v with
    | .obj id =>
      match (← get).findProp id key 1000 with
      | none => pure .undef
      | some (.data x ..) => pure x
      | some (.acc g _ _ _) => if g.isObj then callV n g v #[] else pure .undef
    | .str s =>
      if key == "length" then pure (.num (Float.ofNat (utf16Length s)))
      else match arrayIndex? key with
        | some i => match s.toList[i]? with
          | some c => pure (.str (String.singleton c))
          | none => getProto n (← realm).stringProto key v
        | none => getProto n (← realm).stringProto key v
    | .num _ => getProto n (← realm).numberProto key v
    | .bool _ => getProto n (← realm).booleanProto key v
    | .undef => throwErr .type s!"Cannot read properties of undefined (reading '{key}')"
    | .null => throwErr .type s!"Cannot read properties of null (reading '{key}')"

def getProto : Nat → Nat → String → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, proto, key, recv => do
    match (← get).findProp proto key 1000 with
    | none => pure .undef
    | some (.data x ..) => pure x
    | some (.acc g _ _ _) => if g.isObj then callV n g recv #[] else pure .undef

/-- `[[Set]]` (§10.1.9 OrdinarySet), with the Array `length` (§10.4.2.4). -/
def putV : Nat → Value → String → Value → Bool → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, target, key, val, strict => do
    match target with
    | .obj id =>
      let o ← getObj id
      match o.kind, key with
      | .array es, "length" =>
        let len ← toNum n val
        if len < 0 || !isIntegral len || len ≥ 4294967296.0 then throwErr .range "Invalid array length"
        let l := len.toUInt64.toNat
        let es' := if l ≤ es.size then es.extract 0 l else es ++ Array.replicate (l - es.size) .undef
        modifyObj id fun o => { o with kind := .array es' }
        return
      | _, _ => pure ()
      match o.getOwn key with
      | some (.data _ w e c) =>
        if w then
          match o.kind with
          | .prim (.str _) => if strict then throwErr .type s!"Cannot assign to read only property '{key}'"
          | _ => defineOwn id key (.data val true e c)
        else if strict then throwErr .type s!"Cannot assign to read only property '{key}' of object"
      | some (.acc _ s _ _) =>
        if s.isObj then let _ ← callV n s target #[val]
        else if strict then throwErr .type s!"Cannot set property {key} which has only a getter"
      | none =>
        let inherited ← match o.proto with
          | .obj p => pure ((← get).findProp p key 1000)
          | _ => pure none
        match inherited with
        | some (.acc _ s _ _) =>
          if s.isObj then let _ ← callV n s target #[val]
          else if strict then throwErr .type s!"Cannot set property {key} which has only a getter"
        | some (.data _ false _ _) =>
          if strict then throwErr .type s!"Cannot assign to read only property '{key}' of object"
        | _ =>
          if o.extensible then defineOwn id key (.data val true true true)
          else if strict then throwErr .type s!"Cannot add property {key}, object is not extensible"
    | .undef | .null => throwErr .type s!"Cannot set properties of {if target.isObj then "" else "undefined or null"} (setting '{key}')"
    | _ => if strict then throwErr .type s!"Cannot create property '{key}' on a primitive" else pure ()

/-- ToPrimitive (§7.1.1) with OrdinaryToPrimitive (§7.1.1.1). -/
def toPrim : Nat → Value → Bool → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, preferString => do
    match v with
    | .obj _ =>
      let order := if preferString then ["toString", "valueOf"] else ["valueOf", "toString"]
      tryMethods n v order
    | _ => pure v

def tryMethods : Nat → Value → List String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => throwErr .type "Cannot convert object to primitive value"
  | n + 1, v, m :: ms => do
    let f ← getV n v m
    if ← isCallable f then
      let r ← callV n f v #[]
      if !r.isObj then return r
    tryMethods n v ms

/-- ToNumber (§7.1.4). -/
def toNum : Nat → Value → M Float
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .undef => pure nan
    | .null => pure 0
    | .bool b => pure (if b then 1 else 0)
    | .num x => pure x
    | .str s => pure (strToNumber s)
    | .obj _ => toNum n (← toPrim n v false)

/-- ToString (§7.1.17). -/
def toStr : Nat → Value → M String
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .undef => pure "undefined"
    | .null => pure "null"
    | .bool b => pure (if b then "true" else "false")
    | .num x => pure (numToString x)
    | .str s => pure s
    | .obj _ => toStr n (← toPrim n v true)

/-- ToPropertyKey (§7.1.19). -/
def toKey : Nat → Value → M String
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .str s => pure s
    | .num x => pure (keyOfNum x)
    | _ => toStr n v

/-- ToObject (§7.1.18). -/
def toObj : Nat → Value → M Nat
  | 0, _ => throw (.halt "fuel")
  | _ + 1, v => do
    let r ← realm
    match v with
    | .obj id => pure id
    | .undef | .null => throwErr .type "Cannot convert undefined or null to object"
    | .str _ => alloc { proto := .obj r.stringProto, kind := .prim v }
    | .num _ => alloc { proto := .obj r.numberProto, kind := .prim v }
    | .bool _ => alloc { proto := .obj r.booleanProto, kind := .prim v }

/-- IsLooselyEqual (§7.2.14). -/
def looseEq : Nat → Value → Value → M Bool
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, a, b => do
    match a, b with
    | .undef, .null | .null, .undef => pure true
    | .num _, .str s => pure (strictEq a (.num (strToNumber s)))
    | .str s, .num _ => pure (strictEq (.num (strToNumber s)) b)
    | .bool x, _ => looseEq n (.num (if x then 1 else 0)) b
    | _, .bool y => looseEq n a (.num (if y then 1 else 0))
    | .obj _, .num _ | .obj _, .str _ => looseEq n (← toPrim n a false) b
    | .num _, .obj _ | .str _, .obj _ => looseEq n a (← toPrim n b false)
    | _, _ => pure (strictEq a b)

/-- IsLessThan (§7.2.13): `none` is undefined (a NaN operand). -/
def lessThan : Nat → Value → Value → Bool → M (Option Bool)
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, a, b, leftFirst => do
    let (pa, pb) ← if leftFirst then do
        let x ← toPrim n a false; let y ← toPrim n b false; pure (x, y)
      else do
        let y ← toPrim n b false; let x ← toPrim n a false; pure (x, y)
    match pa, pb with
    | .str x, .str y => pure (some (decide (x < y)))
    | _, _ =>
      let x ← toNum n pa
      let y ← toNum n pb
      if x.isNaN || y.isNaN then pure none else pure (some (x < y))

/-- OrdinaryHasInstance (§7.3.21). -/
def instOf : Nat → Value → Value → M Bool
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, c => do
    match c with
    | .obj cid =>
      let co ← getObj cid
      if !co.kind.callable then throwErr .type "Right-hand side of 'instanceof' is not callable"
      match co.kind with
      | .bound t _ _ => instOf n v t
      | _ =>
        let p ← getV n c "prototype"
        match p with
        | .obj pid =>
          match v with
          | .obj _ =>
            let h ← get
            let rec walk : Nat → Value → Bool
              | 0, _ => false
              | k + 1, .obj o => match (h.obj o).proto with
                | .obj q => q == pid || walk k (.obj q)
                | _ => false
              | _ + 1, _ => false
            pure (walk 10000 v)
          | _ => pure false
        | _ => throwErr .type "Function has non-object prototype in instanceof check"
    | _ => throwErr .type "Right-hand side of 'instanceof' is not an object"

/-- The binary operators (§13.15.3 ApplyStringOrNumericBinaryOperator and §13.10, §13.11). -/
def binop : Nat → BinOp → Value → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, op, a, b => do
    match op with
    | .add =>
      match a, b with
      | .num x, .num y => pure (.num (x + y))
      | .str x, .str y => pure (.str (x ++ y))
      | _, _ =>
        let pa ← toPrim n a false
        let pb ← toPrim n b false
        match pa, pb with
        | .str _, _ | _, .str _ => pure (.str ((← toStr n pa) ++ (← toStr n pb)))
        | _, _ => pure (.num ((← toNum n pa) + (← toNum n pb)))
    | .sub => pure (.num ((← toNum n a) - (← toNum n b)))
    | .mul => pure (.num ((← toNum n a) * (← toNum n b)))
    | .div => pure (.num ((← toNum n a) / (← toNum n b)))
    | .mod => pure (.num (jsMod (← toNum n a) (← toNum n b)))
    | .exp => pure (.num (jsPow (← toNum n a) (← toNum n b)))
    | .shl =>
      let x := toInt32 (← toNum n a); let s := toUint32 (← toNum n b) % 32
      pure (intV (toInt32 (Float.ofInt (x * 2 ^ s))))
    | .sar =>
      let x := toInt32 (← toNum n a); let s := toUint32 (← toNum n b) % 32
      pure (intV (x / 2 ^ s))
    | .shr =>
      let x := toUint32 (← toNum n a); let s := toUint32 (← toNum n b) % 32
      pure (.num (floatOfNat (x / 2 ^ s)))
    | .band | .bor | .bxor =>
      let x := toUint32 (← toNum n a)
      let y := toUint32 (← toNum n b)
      let r := match op with
        | .band => x &&& y | .bor => x ||| y | _ => x ^^^ y
      pure (intV (toInt32 (floatOfNat r)))
    | .lt => pure (.bool ((← lessThan n a b true) == some true))
    | .gt => pure (.bool ((← lessThan n b a false) == some true))
    | .le => pure (.bool ((← lessThan n b a false) == some false))
    | .ge => pure (.bool ((← lessThan n a b true) == some false))
    | .eq => pure (.bool (← looseEq n a b))
    | .ne => pure (.bool !(← looseEq n a b))
    | .seq => pure (.bool (strictEq a b))
    | .sne => pure (.bool !(strictEq a b))
    | .instanceof => pure (.bool (← instOf n a b))
    | .inOp =>
      match b with
      | .obj id =>
        let k ← toKey n a
        pure (.bool ((← get).findProp id k 1000).isSome)
      | _ => throwErr .type "Cannot use 'in' operator to search for a key in a non-object"

/-- `[[Call]]` (§10.2.1, §10.3.1, §10.4.1.1). -/
def callV : Nat → Value → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, f, thisV, args => do
    match f with
    | .obj id =>
      match (← getObj id).kind with
      | .closure fd env lexThis => callClosure n fd env lexThis thisV args
      | .native nid => callNative n nid thisV args none
      | .bound t bt bargs => callV n t bt (bargs ++ args)
      | _ => throwErr .type "not a function"
    | _ => throwErr .type "not a function"

/-- PrepareForOrdinaryCall, OrdinaryCallBindThis, FunctionDeclarationInstantiation
(§10.2.1.1, §10.2.1.2, §10.2.11), then the body. -/
def callClosure : Nat → FunDef → Nat → Value → Value → Array Value → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, fd, env, lexThis, thisV, args => do
    tick
    let h ← get
    if h.depth ≥ h.maxDepth then throwErr .range "Maximum call stack size exceeded"
    set { h with depth := h.depth + 1 }
    let fenv ← newEnv (some env)
    let r ← realm
    let thisV := if fd.arrow then lexThis
      else if fd.strict then thisV
      else match thisV with
        | .undef | .null => .obj r.globalObj
        | v => v
    let rec bindParams : List String → Nat → M Unit
      | [], _ => pure ()
      | p :: ps, i => do declare fenv p { v := args.getD i .undef }; bindParams ps (i + 1)
    bindParams fd.params 0
    if fd.usesArgs && !fd.params.contains "arguments" then
      let a ← alloc { proto := .obj r.objectProto, kind := .args }
      for i in [0:args.size] do defineOwn a (toString i) (.data args[i]! true true true)
      setHidden a "length" (.num (Float.ofNat args.size))
      declare fenv "arguments" { v := .obj a }
    for v in fd.vars do
      if !((← getBinding fenv v).isSome) then declare fenv v { v := .undef }
    let ctx : Ctx := { env := fenv, thisV, strict := fd.strict }
    let c ← evalBody n ctx fd.body
    modify fun h => { h with depth := h.depth - 1 }
    match c with
    | .ret v => pure v
    | _ => pure .undef

/-- `[[Construct]]` (§10.2.2). -/
def construct : Nat → Value → Array Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, f, args => do
    match f with
    | .obj id =>
      match (← getObj id).kind with
      | .closure fd env lexThis =>
        if fd.arrow then throwErr .type "not a constructor"
        let p ← getV n f "prototype"
        let r ← realm
        let o ← alloc { proto := if p.isObj then p else .obj r.objectProto }
        let res ← callClosure n fd env lexThis (.obj o) args
        pure (if res.isObj then res else .obj o)
      | .native nid => callNative n nid .undef args (some f)
      | .bound t _ bargs => construct n t (bargs ++ args)
      | _ => throwErr .type "not a constructor"
    | _ => throwErr .type "not a constructor"

/-- The block body of a function or script, after its declarations are bound. -/
def evalBody : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let ctx ← enterBlock n ctx ss
    evalStmts n ctx ss

/-- BlockDeclarationInstantiation (§14.2.3): a new environment when the block
declares `let`, `const` or functions; functions are created here (hoisting). -/
def enterBlock : Nat → Ctx → List Stmt → M Ctx
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let needs := ss.any fun s => match s with
      | .decl .letK _ | .decl .constK _ | .funDecl .. => true
      | _ => false
    if !needs then return ctx
    let env ← newEnv (some ctx.env)
    let ctx' := { ctx with env }
    declareLexical n ctx' ss
    return ctx'

def declareLexical : Nat → Ctx → List Stmt → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure ()
  | n + 1, ctx, s :: ss => do
    match s with
    | .decl .letK ds | .decl .constK ds =>
      let mutable := match s with | .decl .letK _ => true | _ => false
      for d in ds do
        match d with
        | .mk x _ => declare ctx.env x { v := .undef, mutable, init := false }
    | .funDecl name f =>
      let c ← makeClosure ctx f
      declare ctx.env name { v := c }
    | _ => pure ()
    declareLexical n ctx ss

def evalStmts : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure .normal
  | n + 1, ctx, s :: ss => do
    let c ← evalStmt n ctx [] s
    match c with
    | .normal => evalStmts n ctx ss
    | _ => pure c

def evalBlock : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let ctx ← enterBlock n ctx ss
    evalStmts n ctx ss

/-- InitializeReferencedBinding / PutValue for a name (§9.1.1.1.5, §6.2.5.6). -/
def assignName : Nat → Ctx → String → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x, v => do
    let h ← get
    match h.findEnv x 100000 (some ctx.env) with
    | some e =>
      match (h.envs.getD e default).vars.get? x with
      | some b =>
        if !b.init then throwErr .reference s!"Cannot access '{x}' before initialization"
        if !b.mutable then
          if b.v.isObj && ctx.strict == false && false then pure ()
          else throwErr .type "Assignment to constant variable."
        declare e x { b with v }
      | none => pure ()
    | none =>
      let g := h.realm.globalObj
      if (h.findProp g x 1000).isSome || !ctx.strict then putV n (.obj g) x v ctx.strict
      else throwErr .reference s!"{x} is not defined"

def lookup : Nat → Ctx → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x => do
    let h ← get
    match h.findEnv x 100000 (some ctx.env) with
    | some e =>
      match (h.envs.getD e default).vars.get? x with
      | some b =>
        if b.init then pure b.v else throwErr .reference s!"Cannot access '{x}' before initialization"
      | none => pure .undef
    | none =>
      let g := h.realm.globalObj
      if (h.findProp g x 1000).isSome then getV n (.obj g) x
      else throwErr .reference s!"{x} is not defined"

/-- PutValue on an assignment target, after its parts are evaluated. -/
def putTarget : Nat → Ctx → Expr → Option Value → Option String → Value → M Unit
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, target, base, key, v => do
    match target, base, key with
    | .ident x, _, _ => assignName n ctx x v
    | _, some b, some k => putV n b k v ctx.strict
    | _, _, _ => throwErr .syntax "Invalid assignment target"

/-- Evaluate the base and key of a target (the Reference of §6.2.5). -/
def evalRef : Nat → Ctx → Expr → M (Option Value × Option String)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e => do
    match e with
    | .member o k => pure (some (← evalExpr n ctx o), some k)
    | .index o k =>
      let b ← evalExpr n ctx o
      let kv ← evalExpr n ctx k
      if let .undef := b then throwErr .type "Cannot read properties of undefined"
      if let .null := b then throwErr .type "Cannot read properties of null"
      pure (some b, some (← toKey n kv))
    | _ => pure (none, none)

def getRef : Nat → Ctx → Expr → Option Value → Option String → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e, base, key => do
    match e, base, key with
    | .ident x, _, _ => lookup n ctx x
    | _, some b, some k => getV n b k
    | _, _, _ => evalExpr n ctx e

def evalArgs : Nat → Ctx → List Expr → Array Value → M (Array Value)
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], acc => pure acc
  | n + 1, ctx, a :: as, acc => do
    let v ← evalExpr n ctx a
    evalArgs n ctx as (acc.push v)

def evalProps : Nat → Ctx → Nat → List PropDef → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, [] => pure ()
  | n + 1, ctx, id, p :: ps => do
    let keyOf (k : PropKey) : M String := match k with
      | .lit s => pure s
      | .computed e => do toKey n (← evalExpr n ctx e)
    match p with
    | .init k e =>
      let key ← keyOf k
      let v ← match e with
        | .func f => if f.name.isNone then makeClosure ctx f key else evalExpr n ctx e
        | _ => evalExpr n ctx e
      defineOwn id key (.data v true true true)
    | .getter k f =>
      let key ← keyOf k
      let g ← makeClosure ctx f ("get " ++ key)
      let old := (← getObj id).props.get? key
      let s := match old with | some (.acc _ s _ _) => s | _ => .undef
      defineOwn id key (.acc g s true true)
    | .setter k f =>
      let key ← keyOf k
      let s ← makeClosure ctx f ("set " ++ key)
      let old := (← getObj id).props.get? key
      let g := match old with | some (.acc g _ _ _) => g | _ => .undef
      defineOwn id key (.acc g s true true)
    evalProps n ctx id ps

/-- Evaluation of expressions (§13). -/
def evalExpr : Nat → Ctx → Expr → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e => do
    match e with
    | .num x => pure (.num x)
    | .str s => pure (.str s)
    | .bool b => pure (.bool b)
    | .null => pure .null
    | .ident x => lookup n ctx x
    | .this => pure ctx.thisV
    | .array es => newArray (← evalArgs n ctx es #[])
    | .object ps =>
      let id ← newObject
      evalProps n ctx id ps
      pure (.obj id)
    | .func f => makeClosure ctx f
    | .unary op a =>
      match op, a with
      | .typeof, .ident x =>
        let h ← get
        if (h.findEnv x 100000 (some ctx.env)).isNone && (h.findProp h.realm.globalObj x 1000).isNone then
          pure (.str "undefined")
        else pure (.str (← typeOf (← lookup n ctx x)))
      | .delete, t =>
        match t with
        | .member _ _ | .index _ _ =>
          let (b, k) ← evalRef n ctx t
          match b, k with
          | some (.obj id), some key =>
            let o ← getObj id
            match o.getOwn key with
            | none => pure (.bool true)
            | some p =>
              let arrayLen := match o.kind with | .array _ => key == "length" | _ => false
              if p.configurable && !arrayLen then deleteOwn id key; pure (.bool true)
              else if ctx.strict then throwErr .type s!"Cannot delete property '{key}'"
              else pure (.bool false)
          | some (.str _), some key =>
            if key == "length" || (arrayIndex? key).isSome then
              if ctx.strict then throwErr .type s!"Cannot delete property '{key}'" else pure (.bool false)
            else pure (.bool true)
          | some _, _ => pure (.bool true)
          | none, _ => pure (.bool true)
        | .ident x =>
          let h ← get
          match h.findEnv x 100000 (some ctx.env) with
          | some _ => pure (.bool false)
          | none =>
            let g := h.realm.globalObj
            match (h.obj g).getOwn x with
            | some p => if p.configurable then deleteOwn g x; pure (.bool true) else pure (.bool false)
            | none => pure (.bool true)
        | _ => let _ ← evalExpr n ctx t; pure (.bool true)
      | _, _ =>
        let v ← evalExpr n ctx a
        match op with
        | .neg => pure (.num (-(← toNum n v)))
        | .plus => pure (.num (← toNum n v))
        | .not => pure (.bool !(toBool v))
        | .bnot => pure (intV (-(toInt32 (← toNum n v)) - 1))
        | .typeof => pure (.str (← typeOf v))
        | .void => pure .undef
        | .delete => pure (.bool true)
    | .binary op a b =>
      let x ← evalExpr n ctx a
      let y ← evalExpr n ctx b
      match op, x, y with
      | .add, .num p, .num q => pure (.num (p + q))
      | .sub, .num p, .num q => pure (.num (p - q))
      | .lt, .num p, .num q => pure (.bool (p < q))
      | .seq, _, _ => pure (.bool (strictEq x y))
      | _, _, _ => binop n op x y
    | .logical op a b =>
      let x ← evalExpr n ctx a
      match op with
      | .and => if toBool x then evalExpr n ctx b else pure x
      | .or => if toBool x then pure x else evalExpr n ctx b
      | .coalesce => match x with
        | .undef | .null => evalExpr n ctx b
        | _ => pure x
    | .assign none target rhs =>
      let (b, k) ← evalRef n ctx target
      let v ← match target, rhs with
        | .ident x, .func f => if f.name.isNone then makeClosure ctx f x else evalExpr n ctx rhs
        | _, _ => evalExpr n ctx rhs
      putTarget n ctx target b k v
      pure v
    | .assign (some op) target rhs =>
      let (b, k) ← evalRef n ctx target
      let old ← getRef n ctx target b k
      let r ← evalExpr n ctx rhs
      let v ← binop n op old r
      putTarget n ctx target b k v
      pure v
    | .logAssign op target rhs =>
      let (b, k) ← evalRef n ctx target
      let old ← getRef n ctx target b k
      let go ← match op with
        | .and => pure (toBool old)
        | .or => pure !(toBool old)
        | .coalesce => pure (match old with | .undef | .null => true | _ => false)
      if !go then return old
      let v ← evalExpr n ctx rhs
      putTarget n ctx target b k v
      pure v
    | .update pre inc target =>
      let (b, k) ← evalRef n ctx target
      let old ← toNum n (← getRef n ctx target b k)
      let nv := if inc then old + 1 else old - 1
      putTarget n ctx target b k (.num nv)
      pure (.num (if pre then nv else old))
    | .cond c t f => if toBool (← evalExpr n ctx c) then evalExpr n ctx t else evalExpr n ctx f
    | .seq a b => let _ ← evalExpr n ctx a; evalExpr n ctx b
    | .call callee args =>
      let (f, thisV) ← match callee with
        | .member o k =>
          let b ← evalExpr n ctx o
          pure (← getV n b k, b)
        | .index o k =>
          let b ← evalExpr n ctx o
          let key ← toKey n (← evalExpr n ctx k)
          pure (← getV n b key, b)
        | _ => pure (← evalExpr n ctx callee, Value.undef)
      let argv ← evalArgs n ctx args #[]
      if !(← isCallable f) then
        let what := match callee with
          | .ident x => x | .member _ k => k | _ => "expression"
        throwErr .type s!"{what} is not a function"
      callV n f thisV argv
    | .new callee args =>
      let f ← evalExpr n ctx callee
      let argv ← evalArgs n ctx args #[]
      construct n f argv
    | .member o k => getV n (← evalExpr n ctx o) k
    | .index o k =>
      let b ← evalExpr n ctx o
      let kv ← evalExpr n ctx k
      match b, kv with
      | .obj id, .num x =>
        match (← getObj id).kind with
        | .array es =>
          if x ≥ 0 && x < Float.ofNat es.size && x.floor == x then pure (es.getD x.toUInt64.toNat .undef)
          else getV n b (← toKey n kv)
        | _ => getV n b (← toKey n kv)
      | .undef, _ => throwErr .type "Cannot read properties of undefined"
      | .null, _ => throwErr .type "Cannot read properties of null"
      | _, _ => getV n b (← toKey n kv)

/-- What a loop does with the completion of its body (LoopContinues, §14.7.1.2). -/
def loopNext (labels : List String) : Compl → Option Compl
  | .normal => none
  | .cont none => none
  | .cont (some l) => if labels.contains l then none else some (.cont (some l))
  | .brk none => some .normal
  | .brk (some l) => if labels.contains l then some .normal else some (.brk (some l))
  | .ret v => some (.ret v)

def whileLoop : Nat → Ctx → List String → Expr → Stmt → M Compl
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, c, body => do
    tick
    if !(toBool (← evalExpr n ctx c)) then return .normal
    let r ← evalStmt n ctx [] body
    match loopNext labels r with
    | some out => pure out
    | none => whileLoop n ctx labels c body

def doLoop : Nat → Ctx → List String → Stmt → Expr → M Compl
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, body, c => do
    tick
    let r ← evalStmt n ctx [] body
    match loopNext labels r with
    | some out => pure out
    | none =>
      if !(toBool (← evalExpr n ctx c)) then return .normal
      doLoop n ctx labels body c

/-- ForBodyEvaluation (§14.7.4.3) with CreatePerIterationEnvironment for `let`. -/
def forLoop : Nat → Ctx → List String → List String → Option Expr → Option Expr → Stmt → Bool → M Compl
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, perIter, test, update, body, first => do
    tick
    let ctx ← if perIter.isEmpty then pure ctx else copyEnv n ctx perIter
    if !first then
      if let some u := update then let _ ← evalExpr n ctx u
    if let some t := test then
      if !(toBool (← evalExpr n ctx t)) then return .normal
    let r ← evalStmt n ctx [] body
    match loopNext labels r with
    | some out => pure out
    | none => forLoop n ctx labels perIter test update body false

def copyEnv : Nat → Ctx → List String → M Ctx
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, ctx, names => do
    let h ← get
    let old := h.envs.getD ctx.env default
    let e ← newEnv old.parent
    for x in names do
      if let some b := old.vars.get? x then declare e x b
    pure { ctx with env := e }

def forInLoop : Nat → Ctx → List String → Option DeclKind → Expr → Value → List String → Stmt → M Compl
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, _, _, _, [], _ => pure .normal
  | n + 1, ctx, labels, kind, target, obj, k :: ks, body => do
    tick
    -- a key deleted during the loop is not visited
    let present ← match obj with
      | .obj id => pure ((← get).findProp id k 1000).isSome
      | _ => pure true
    if !present then return ← forInLoop n ctx labels kind target obj ks body
    let ctx' ← match kind, target with
      | some .letK, .ident x | some .constK, .ident x => do
        let e ← newEnv (some ctx.env)
        declare e x { v := .str k, mutable := kind == some .letK }
        pure { ctx with env := e }
      | _, _ => do
        let (b, key) ← evalRef n ctx target
        putTarget n ctx target b key (.str k)
        pure ctx
    let r ← evalStmt n ctx' [] body
    match loopNext labels r with
    | some out => pure out
    | none => forInLoop n ctx labels kind target obj ks body

/-- CaseBlockEvaluation (§14.12.4). -/
def switchFind : Nat → Ctx → Value → List Case → Nat → M (Option Nat)
  | 0, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, [], _ => pure none
  | n + 1, ctx, d, (.mk t _) :: cs, i => do
    match t with
    | some e =>
      let v ← evalExpr n ctx e
      if strictEq d v then pure (some i) else switchFind n ctx d cs (i + 1)
    | none => switchFind n ctx d cs (i + 1)

def runCases : Nat → Ctx → List Case → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure .normal
  | n + 1, ctx, (.mk _ body) :: cs => do
    let r ← evalStmts n ctx body
    match r with
    | .normal => runCases n ctx cs
    | _ => pure r

def evalDecls : Nat → Ctx → DeclKind → List Decl → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, [] => pure ()
  | n + 1, ctx, kind, (.mk x init) :: ds => do
    match kind with
    | .var =>
      if let some e := init then
        let v ← match e with
          | .func f => if f.name.isNone then makeClosure ctx f x else evalExpr n ctx e
          | _ => evalExpr n ctx e
        assignName n ctx x v
    | _ =>
      let v ← match init with
        | some (.func f) => if f.name.isNone then makeClosure ctx f x else evalExpr n ctx (.func f)
        | some e => evalExpr n ctx e
        | none => pure .undef
      declare ctx.env x { v, mutable := kind == .letK }
    evalDecls n ctx kind ds

/-- Evaluation of statements (§14). `labels` is the label set of a loop. -/
def evalStmt : Nat → Ctx → List String → Stmt → M Compl
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, s => do
    match s with
    | .expr e => let _ ← evalExpr n ctx e; pure .normal
    | .decl k ds => evalDecls n ctx k ds; pure .normal
    | .funDecl .. => pure .normal
    | .ret none => pure (.ret .undef)
    | .ret (some e) => pure (.ret (← evalExpr n ctx e))
    | .ifS c t f =>
      if toBool (← evalExpr n ctx c) then evalStmt n ctx [] t
      else match f with
        | some f => evalStmt n ctx [] f
        | none => pure .normal
    | .whileS c body => whileLoop n ctx labels c body
    | .doWhile body c => doLoop n ctx labels body c
    | .forS init test update body =>
      match init with
      | some (.decl .var ds) =>
        evalDecls n ctx .var ds
        forLoop n ctx labels [] test update body true
      | some (.decl k ds) =>
        let env ← newEnv (some ctx.env)
        let ctx' := { ctx with env }
        for d in ds do
          match d with
          | .mk x _ => declare env x { v := .undef, mutable := k == .letK, init := false }
        evalDecls n ctx' k ds
        let names := ds.map fun d => match d with | .mk x _ => x
        forLoop n ctx' labels (if k == .letK then names else []) test update body true
      | some (.expr e) =>
        let _ ← evalExpr n ctx e
        forLoop n ctx labels [] test update body true
      | none => forLoop n ctx labels [] test update body true
    | .forIn kind target obj body =>
      let o ← evalExpr n ctx obj
      let keys ← enumKeys o
      forInLoop n ctx labels kind target o keys.toList body
    | .block ss => evalBlock n ctx ss
    | .throwS e => throw (.throw (← evalExpr n ctx e))
    | .tryS body param handler fin =>
      let r ← tryCatch (do let c ← evalBlock n ctx body; pure (Except.ok c))
        (fun a => pure (Except.error a))
      let r ← match r, handler with
        | .error (.throw v), some hs =>
          tryCatch (do
            let env ← newEnv (some ctx.env)
            if let some p := param then declare env p { v }
            let c ← evalBlock n { ctx with env } hs
            pure (Except.ok c))
            (fun a => pure (Except.error a))
        | r, _ => pure r
      match fin with
      | none => match r with
        | .ok c => pure c
        | .error a => throw a
      | some fs =>
        match r with
        | .error (.halt w) => throw (.halt w)
        | _ =>
          let fc ← evalBlock n ctx fs
          match fc with
          | .normal => match r with
            | .ok c => pure c
            | .error a => throw a
          | _ => pure fc
    | .brk l => pure (.brk l)
    | .cont l => pure (.cont l)
    | .labeled l body =>
      let r ← evalStmt n ctx (l :: labels) body
      match r with
      | .brk (some l') => if l' == l then pure .normal else pure r
      | _ => pure r
    | .switchS d cases =>
      let dv ← evalExpr n ctx d
      let allBody := cases.flatMap fun c => match c with | .mk _ b => b
      let ctx' ← enterBlock n ctx allBody
      let idx ← match ← switchFind n ctx' dv cases 0 with
        | some i => pure (some i)
        | none => pure (cases.findIdx? fun c => match c with | .mk t _ => t.isNone)
      match idx with
      | none => pure .normal
      | some i =>
        let r ← runCases n ctx' (cases.drop i)
        match r with
        | .brk none => pure .normal
        | .brk (some l) => if labels.contains l then pure .normal else pure r
        | _ => pure r
    | .empty => pure .normal

/-- Built-in functions. `newTarget` is set for `new`. -/
def callNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args, newTarget => do
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    match id with
    | .print =>
      let parts ← args.toList.mapM (toStr n)
      modify fun h => { h with out := h.out.push (" ".intercalate parts) }
      pure .undef
    | .isNaN => pure (.bool (← toNum n a0).isNaN)
    | .isFinite => pure (.bool (← toNum n a0).isFinite)
    | .parseInt =>
      let s ← toStr n a0
      let rx ← toNum n a1
      pure (.num (parseIntStr s (toInt32 rx)))
    | .parseFloat => pure (.num (parseFloatStr (← toStr n a0)))
    | .objectCtor =>
      match a0 with
      | .undef | .null => pure (.obj (← newObject))
      | v => pure (.obj (← toObj n v))
    | .objectKeys =>
      let id ← toObj n a0
      let o ← getObj id
      let ks := o.ownKeys.filter fun k => match o.getOwn k with
        | some p => p.enumerable | none => false
      newArray (ks.map .str)
    | .objectGetOwnPropertyNames =>
      let id ← toObj n a0
      newArray ((← getObj id).ownKeys.map .str)
    | .objectGetPrototypeOf =>
      let id ← toObj n a0
      pure (← getObj id).proto
    | .objectSetPrototypeOf =>
      match a0, a1 with
      | .obj id, .obj _ | .obj id, .null => modifyObj id (fun o => { o with proto := a1 }); pure a0
      | _, _ => pure a0
    | .objectCreate =>
      match a0 with
      | .obj _ | .null =>
        let id ← alloc { proto := a0 }
        if let .obj ps := a1 then
          for k in (← getObj ps).ownKeys do
            let d ← getV n a1 k
            defineFromDescriptor n id k d
        pure (.obj id)
      | _ => throwErr .type "Object prototype may only be an Object or null"
    | .objectDefineProperty =>
      match a0 with
      | .obj id =>
        let k ← toKey n a1
        defineFromDescriptor n id k (argD args 2)
        pure a0
      | _ => throwErr .type "Object.defineProperty called on non-object"
    | .objectGetOwnPropertyDescriptor =>
      let id ← toObj n a0
      let k ← toKey n a1
      match (← getObj id).getOwn k with
      | none => pure .undef
      | some p =>
        let d ← newObject
        match p with
        | .data v w e c =>
          defineOwn d "value" (.data v true true true)
          defineOwn d "writable" (.data (.bool w) true true true)
          defineOwn d "enumerable" (.data (.bool e) true true true)
          defineOwn d "configurable" (.data (.bool c) true true true)
        | .acc g s e c =>
          defineOwn d "get" (.data g true true true)
          defineOwn d "set" (.data s true true true)
          defineOwn d "enumerable" (.data (.bool e) true true true)
          defineOwn d "configurable" (.data (.bool c) true true true)
        pure (.obj d)
    | .objectIs => pure (.bool (sameValue a0 a1))
    | .objectFreeze =>
      match a0 with
      | .obj id =>
        let o ← getObj id
        let o := match o.kind with
          | .array es =>
            let o := { o with kind := .ordinary }
            let o := (List.range es.size).foldl (fun (o : Obj) i => o.putOwn (toString i) (.data es[i]! true true true)) o
            o.putOwn "length" (.data (.num (Float.ofNat es.size)) false false false)
          | _ => o
        let props := o.props.fold (fun (m : Std.HashMap String PropV) k p => m.insert k (match p with
          | .data v _ e _ => .data v false e false
          | .acc g s e _ => .acc g s e false)) {}
        modifyObj id fun _ => { o with props, extensible := false }
        pure a0
      | _ => pure a0
    | .objectIsFrozen =>
      match a0 with
      | .obj id =>
        let o ← getObj id
        let all := o.ownKeys.all fun k => match o.getOwn k with
          | some (.data _ w _ c) => !w && !c
          | some (.acc _ _ _ c) => !c
          | none => true
        pure (.bool (!o.extensible && all))
      | _ => pure (.bool true)
    | .objectPreventExtensions =>
      if let .obj id := a0 then modifyObj id fun o => { o with extensible := false }
      pure a0
    | .objectIsExtensible =>
      match a0 with
      | .obj id => pure (.bool (← getObj id).extensible)
      | _ => pure (.bool false)
    | .objectProtoHasOwnProperty =>
      let k ← toKey n a0
      let id ← toObj n thisV
      pure (.bool ((← getObj id).getOwn k).isSome)
    | .objectProtoPropertyIsEnumerable =>
      let k ← toKey n a0
      let id ← toObj n thisV
      pure (.bool (match (← getObj id).getOwn k with | some p => p.enumerable | none => false))
    | .objectProtoIsPrototypeOf =>
      match a0 with
      | .obj _ =>
        let me ← toObj n thisV
        let h ← get
        let rec walk : Nat → Value → Bool
          | 0, _ => false
          | k + 1, .obj o => match (h.obj o).proto with
            | .obj q => q == me || walk k (.obj q)
            | _ => false
          | _ + 1, _ => false
        pure (.bool (walk 10000 a0))
      | _ => pure (.bool false)
    | .objectProtoToString =>
      match thisV with
      | .undef => pure (.str "[object Undefined]")
      | .null => pure (.str "[object Null]")
      | _ =>
        let id ← toObj n thisV
        let tag := match (← getObj id).kind with
          | .array _ => "Array"
          | .closure .. | .native _ | .bound .. => "Function"
          | .error => "Error"
          | .args => "Arguments"
          | .prim (.bool _) => "Boolean"
          | .prim (.num _) => "Number"
          | .prim (.str _) => "String"
          | _ => "Object"
        pure (.str s!"[object {tag}]")
    | .objectProtoToLocaleString => callV n (← getV n thisV "toString") thisV #[]
    | .objectProtoValueOf => pure (.obj (← toObj n thisV))
    | .functionCtor => throwErr .eval "The Function constructor is not supported"
    | .functionProto => pure .undef
    | .functionProtoCall =>
      if !(← isCallable thisV) then throwErr .type "Function.prototype.call called on non-function"
      callV n thisV a0 (args.extract 1 args.size)
    | .functionProtoApply =>
      if !(← isCallable thisV) then throwErr .type "Function.prototype.apply called on non-function"
      let argv ← match a1 with
        | .undef | .null => pure #[]
        | .obj _ =>
          let len ← toNum n (← getV n a1 "length")
          let k := (toIntegerOrInf len).toUInt64.toNat
          (List.range k).toArray.mapM fun i => getV n a1 (toString i)
        | _ => throwErr .type "CreateListFromArrayLike called on non-object"
      callV n thisV a0 argv
    | .functionProtoBind =>
      if !(← isCallable thisV) then throwErr .type "Bind must be called on a function"
      let o ← alloc { proto := .obj r.functionProto, kind := .bound thisV a0 (args.extract 1 args.size) }
      let nm ← getV n thisV "name"
      let nm := match nm with | .str s => s | _ => ""
      defineOwn o "name" (.data (.str ("bound " ++ nm)) false false true)
      let len ← getV n thisV "length"
      let l := match len with | .num x => x | _ => 0
      let l := l - Float.ofNat (args.size - 1 |>.min args.size)
      defineOwn o "length" (.data (.num (if l < 0 then 0 else l)) false false true)
      pure (.obj o)
    | .functionProtoToString =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .closure f .. => pure (.str s!"function {f.name.getD ""}() {"{"} [code] }")
        | .native _ | .bound .. => pure (.str "function () { [native code] }")
        | _ => throwErr .type "Function.prototype.toString requires that 'this' be a Function"
      | _ => throwErr .type "Function.prototype.toString requires that 'this' be a Function"
    | .arrayCtor =>
      if args.size == 1 then
        match a0 with
        | .num x =>
          if x < 0 || !isIntegral x || x ≥ 4294967296.0 then throwErr .range "Invalid array length"
          newArray (Array.replicate x.toUInt64.toNat .undef)
        | v => newArray #[v]
      else newArray args
    | .arrayIsArray =>
      match a0 with
      | .obj id => match (← getObj id).kind with
        | .array _ => pure (.bool true)
        | _ => pure (.bool false)
      | _ => pure (.bool false)
    | .arrayPush =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          modifyObj id fun o => { o with kind := .array (es ++ args) }
          pure (.num (Float.ofNat (es.size + args.size)))
        | _ => genericPush n thisV args
      | _ => genericPush n thisV args
    | .arrayPop =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          if es.isEmpty then pure .undef else
          modifyObj id fun o => { o with kind := .array es.pop }
          pure es.back!
        | _ => pure .undef
      | _ => pure .undef
    | .arrayShift =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          if es.isEmpty then pure .undef else
          modifyObj id fun o => { o with kind := .array (es.extract 1 es.size) }
          pure es[0]!
        | _ => pure .undef
      | _ => pure .undef
    | .arrayUnshift =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          modifyObj id fun o => { o with kind := .array (args ++ es) }
          pure (.num (Float.ofNat (es.size + args.size)))
        | _ => pure .undef
      | _ => pure .undef
    | .arraySlice =>
      let es ← elemsOf n thisV
      let s := relIndex (← toNum n a0) es.size
      let e := match a1 with | .undef => es.size | _ => 0
      let e ← if e == 0 && !(match a1 with | .undef => true | _ => false) then
          do pure (relIndex (← toNum n a1) es.size) else pure es.size
      newArray (if s < e then es.extract s e else #[])
    | .arraySplice =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          let s := relIndex (← toNum n a0) es.size
          let dc ← if args.size < 2 then pure (es.size - s) else do
            let d := toIntegerOrInf (← toNum n a1)
            pure (if d < 0 then 0 else (min d.toUInt64.toNat (es.size - s)))
          let removed := es.extract s (s + dc)
          let es' := es.extract 0 s ++ args.extract 2 args.size ++ es.extract (s + dc) es.size
          modifyObj id fun o => { o with kind := .array es' }
          newArray removed
        | _ => newArray #[]
      | _ => newArray #[]
    | .arrayJoin | .arrayToString =>
      let es ← elemsOf n thisV
      let sep ← if id == .arrayJoin then (match a0 with | .undef => pure "," | v => toStr n v) else pure ","
      let parts ← es.toList.mapM fun v => match v with
        | .undef | .null => pure ""
        | v => toStr n v
      pure (.str (sep.intercalate parts))
    | .arrayIndexOf | .arrayIncludes =>
      let es ← elemsOf n thisV
      let start := relIndex (← toNum n a1) es.size
      let found := (List.range es.size).find? fun i => i ≥ start &&
        (if id == .arrayIncludes then sameValueZero es[i]! a0 else strictEq es[i]! a0)
      if id == .arrayIncludes then pure (.bool found.isSome)
      else pure (.num (match found with | some i => Float.ofNat i | none => -1))
    | .arrayLastIndexOf =>
      let es ← elemsOf n thisV
      let found := (List.range es.size).reverse.find? fun i => strictEq es[i]! a0
      pure (.num (match found with | some i => Float.ofNat i | none => -1))
    | .arrayConcat =>
      let es ← elemsOf n thisV
      let mut acc := es
      for a in args do
        match a with
        | .obj aid => match (← getObj aid).kind with
          | .array more => acc := acc ++ more
          | _ => acc := acc.push a
        | _ => acc := acc.push a
      newArray acc
    | .arrayReverse =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es => modifyObj id (fun o => { o with kind := .array es.reverse }); pure thisV
        | _ => pure thisV
      | _ => pure thisV
    | .arrayFill =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          let s := relIndex (← toNum n a1) es.size
          let e ← match argD args 2 with
            | .undef => pure es.size
            | v => do pure (relIndex (← toNum n v) es.size)
          let es' := es.mapIdx fun i v => if s ≤ i && i < e then a0 else v
          modifyObj id fun o => { o with kind := .array es' }
          pure thisV
        | _ => pure thisV
      | _ => pure thisV
    | .arrayMap | .arrayForEach | .arrayFilter | .arraySome | .arrayEvery | .arrayFind
    | .arrayFindIndex =>
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      let es ← elemsOf n thisV
      iterArray n id a0 a1 thisV es 0 #[]
    | .arrayReduce =>
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      let es ← elemsOf n thisV
      if args.size < 2 && es.isEmpty then throwErr .type "Reduce of empty array with no initial value"
      let (acc, start) := if args.size ≥ 2 then (a1, 0) else (es[0]!, 1)
      reduceArray n a0 thisV es start acc
    | .arraySort =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          let sorted ← mergeSort n a0 es.toList
          modifyObj id fun o => { o with kind := .array sorted.toArray }
          pure thisV
        | _ => pure thisV
      | _ => pure thisV
    | .stringCtor =>
      let s ← if args.isEmpty then pure "" else toStr n a0
      match newTarget with
      | some _ => pure (.obj (← alloc { proto := .obj r.stringProto, kind := .prim (.str s) }))
      | none => pure (.str s)
    | .stringFromCharCode =>
      let cs ← args.toList.mapM fun a => do pure (charOfCode ((toUint32 (← toNum n a)) % 65536))
      pure (.str (String.ofList cs))
    | .stringToString =>
      match ← thisPrim thisV with
      | .str s => pure (.str s)
      | _ => throwErr .type "String.prototype.toString requires that 'this' be a String"
    | .numberCtor =>
      let x ← if args.isEmpty then pure 0 else toNum n a0
      match newTarget with
      | some _ => pure (.obj (← alloc { proto := .obj r.numberProto, kind := .prim (.num x) }))
      | none => pure (.num x)
    | .numberValueOf | .numberToString | .numberToFixed =>
      let x ← match ← thisPrim thisV with
        | .num x => pure x
        | _ => throwErr .type "Number.prototype method requires that 'this' be a Number"
      match id with
      | .numberValueOf => pure (.num x)
      | .numberToString =>
        let radix ← match a0 with | .undef => pure 10 | v => do pure (toIntegerOrInf (← toNum n v))
        if radix < 2 || radix > 36 then throwErr .range "toString() radix must be between 2 and 36"
        if radix == 10 || !isIntegral x then pure (.str (numToString x))
        else
          let i := truncInt x
          let ds := Nat.toDigits radix.toUInt64.toNat i.natAbs
          pure (.str ((if i < 0 then "-" else "") ++ String.ofList ds))
      | _ =>
        let d := toIntegerOrInf (← toNum n a0)
        if d < 0 || d > 100 then throwErr .range "toFixed() digits argument must be between 0 and 100"
        if x.abs ≥ 1e21 || x.isNaN then pure (.str (numToString x)) else
        let k := d.toUInt64.toNat
        let scaled := x.abs * Float.ofNat (10 ^ k)
        let m := (scaled + 0.5).floor
        let ms := toString (truncInt m)
        let ms := if ms.length ≤ k then String.ofList (List.replicate (k + 1 - ms.length) '0') ++ ms else ms
        let body := if k == 0 then ms
          else String.ofList (ms.toList.take (ms.length - k)) ++ "." ++ String.ofList (ms.toList.drop (ms.length - k))
        pure (.str ((if x < 0 && m != 0 then "-" else "") ++ body))
    | .numberIsInteger => pure (.bool (match a0 with | .num x => isIntegral x | _ => false))
    | .booleanCtor =>
      let b := toBool a0
      match newTarget with
      | some _ => pure (.obj (← alloc { proto := .obj r.booleanProto, kind := .prim (.bool b) }))
      | none => pure (.bool b)
    | .booleanToString | .booleanValueOf =>
      match ← thisPrim thisV with
      | .bool b => pure (if id == .booleanValueOf then .bool b else .str (if b then "true" else "false"))
      | _ => throwErr .type "Boolean.prototype method requires that 'this' be a Boolean"
    | .errorCtor k =>
      let proto ← match newTarget with
        | some nt => do
          let p ← getV n nt "prototype"
          pure (if p.isObj then p else .obj (r.errorProtos.getD k r.objectProto))
        | none => pure (.obj (r.errorProtos.getD k r.objectProto))
      let o ← alloc { proto, kind := .error }
      match a0 with
      | .undef => pure ()
      | v => setHidden o "message" (.str (← toStr n v))
      pure (.obj o)
    | .errorToString =>
      if !thisV.isObj then throwErr .type "Error.prototype.toString called on non-object"
      let nm ← getV n thisV "name"
      let nm ← match nm with | .undef => pure "Error" | v => toStr n v
      let msg ← getV n thisV "message"
      let msg ← match msg with | .undef => pure "" | v => toStr n v
      pure (.str (if nm.isEmpty then msg else if msg.isEmpty then nm else nm ++ ": " ++ msg))
    | .throwTypeError => throwErr .type "'caller', 'callee', and 'arguments' properties may not be accessed"
    | .jsonStringify => jsonStr n a0 0
    | _ =>
      -- string methods and Math
      stringOrMath n id thisV args

def genericPush : Nat → Value → Array Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, thisV, args => do
    let len ← toNum n (← getV n thisV "length")
    let l := (toIntegerOrInf len).toUInt64.toNat
    for i in [0:args.size] do putV n thisV (toString (l + i)) args[i]! true
    putV n thisV "length" (.num (Float.ofNat (l + args.size))) true
    pure (.num (Float.ofNat (l + args.size)))

/-- The elements of an array, or of an array-like object (`length` and indices). -/
def elemsOf : Nat → Value → M (Array Value)
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .obj id => match (← getObj id).kind with
      | .array es => pure es
      | _ =>
        let len ← toNum n (← getV n v "length")
        let k := (toIntegerOrInf len).toUInt64.toNat
        (List.range (min k 10000000)).toArray.mapM fun i => getV n v (toString i)
    | .str s => pure ((charsOf s).map fun c => .str (String.singleton c))
    | .undef | .null => throwErr .type "Array.prototype method called on null or undefined"
    | _ => pure #[]

def iterArray : Nat → Native → Value → Value → Value → Array Value → Nat → Array Value → M Value
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, f, thisArg, arr, es, i, acc => do
    if h : i < es.size then
      let x := es[i]
      let r ← callV n f thisArg #[x, .num (Float.ofNat i), arr]
      match id with
      | .arrayMap => iterArray n id f thisArg arr es (i + 1) (acc.push r)
      | .arrayFilter => iterArray n id f thisArg arr es (i + 1) (if toBool r then acc.push x else acc)
      | .arraySome => if toBool r then pure (.bool true) else iterArray n id f thisArg arr es (i + 1) acc
      | .arrayEvery => if toBool r then iterArray n id f thisArg arr es (i + 1) acc else pure (.bool false)
      | .arrayFind => if toBool r then pure x else iterArray n id f thisArg arr es (i + 1) acc
      | .arrayFindIndex => if toBool r then pure (.num (Float.ofNat i)) else iterArray n id f thisArg arr es (i + 1) acc
      | _ => iterArray n id f thisArg arr es (i + 1) acc
    else
      match id with
      | .arrayMap | .arrayFilter => newArray acc
      | .arraySome => pure (.bool false)
      | .arrayEvery => pure (.bool true)
      | .arrayFindIndex => pure (.num (-1))
      | _ => pure .undef

def reduceArray : Nat → Value → Value → Array Value → Nat → Value → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, f, arr, es, i, acc => do
    if h : i < es.size then
      let acc ← callV n f .undef #[acc, es[i], .num (Float.ofNat i), arr]
      reduceArray n f arr es (i + 1) acc
    else pure acc

/-- SortCompare (§23.1.3.30.2): `true` when `a` goes after `b`. -/
def sortGt : Nat → Value → Value → Value → M Bool
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, cmp, a, b => do
    match a, b with
    | .undef, .undef => pure false
    | .undef, _ => pure true
    | _, .undef => pure false
    | _, _ =>
      match cmp with
      | .undef =>
        let x ← toStr n a; let y ← toStr n b
        pure (decide (y < x))
      | _ =>
        let r ← toNum n (← callV n cmp .undef #[a, b])
        pure (r > 0)

def mergeSort : Nat → Value → List Value → M (List Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, cmp, xs => do
    if xs.length ≤ 1 then return xs
    let k := xs.length / 2
    let l ← mergeSort n cmp (xs.take k)
    let r ← mergeSort n cmp (xs.drop k)
    merge n cmp l r #[]

def merge : Nat → Value → List Value → List Value → Array Value → M (List Value)
  | 0, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], r, acc => pure (acc.toList ++ r)
  | _ + 1, _, l, [], acc => pure (acc.toList ++ l)
  | n + 1, cmp, a :: as, b :: bs, acc => do
    if ← sortGt n cmp a b then merge n cmp (a :: as) bs (acc.push b)
    else merge n cmp as (b :: bs) (acc.push a)

/-- PropertyDescriptor from an object (§6.2.6.5 ToPropertyDescriptor), defined
with ValidateAndApplyPropertyDescriptor's defaults for a new property. -/
def defineFromDescriptor : Nat → Nat → String → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, k, d => do
    if !d.isObj then throwErr .type "Property description must be an object"
    let has (f : String) : M Bool := do
      match d with
      | .obj did => pure ((← get).findProp did f 1000).isSome
      | _ => pure false
    let old := (← getObj id).getOwn k
    if let some p := old then
      if !p.configurable then
        -- only a writable data property may change its value
        match p with
        | .data _ true e c =>
          if ← has "value" then defineOwn id k (.data (← getV n d "value") true e c)
          if ← has "writable" then
            if !(toBool (← getV n d "writable")) then
              let v := match (← getObj id).getOwn k with | some (.data v ..) => v | _ => .undef
              defineOwn id k (.data v false e c)
          return
        | _ => throwErr .type s!"Cannot redefine property: {k}"
    let e ← if ← has "enumerable" then do pure (toBool (← getV n d "enumerable"))
      else pure (match old with | some p => p.enumerable | none => false)
    let c ← if ← has "configurable" then do pure (toBool (← getV n d "configurable"))
      else pure (match old with | some p => p.configurable | none => false)
    if (← has "get") || (← has "set") then
      let g ← getV n d "get"
      let s ← getV n d "set"
      if !(g.isObj || match g with | .undef => true | _ => false) then throwErr .type "Getter must be a function"
      let (og, os) := match old with | some (.acc g s _ _) => (g, s) | _ => (.undef, .undef)
      defineOwn id k (.acc (if ← has "get" then g else og) (if ← has "set" then s else os) e c)
    else
      let w ← if ← has "writable" then do pure (toBool (← getV n d "writable"))
        else pure (match old with | some (.data _ w _ _) => w | _ => false)
      let v ← if ← has "value" then getV n d "value"
        else pure (match old with | some (.data v ..) => v | _ => .undef)
      match (← getObj id).kind, k with
      | .array _, "length" => putV n (.obj id) k v true
      | _, _ =>
        let o ← getObj id
        match o.kind, arrayIndex? k with
        | .array es, some i =>
          if w && e && c then defineOwn id k (.data v true true true)
          else
            -- leave the fast form: keep the elements as ordinary properties
            let o' := (List.range es.size).foldl (fun o j => { o with
                props := o.props.insert (toString j) (.data es[j]! true true true),
                keys := o.keys.push (toString j) }) { o with kind := .ordinary }
            modifyObj id fun _ => o'
            defineOwn id k (.data v w e c)
            let _ := i
        | _, _ => defineOwn id k (.data v w e c)

/-- JSON.stringify (§25.5.2) without `replacer` and `space`. -/
def jsonStr : Nat → Value → Nat → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, depth => do
    if depth > 1000 then throwErr .range "Maximum call stack size exceeded"
    let quote (s : String) : String :=
      "\"" ++ s.foldl (fun acc c => acc ++ match c with
        | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
        | '\x08' => "\\b" | '\x0c' => "\\f"
        | c => if c.toNat < 32 then "\\u" ++ String.ofList ((Nat.toDigits 16 c.toNat).leftpad 4 '0') else String.singleton c) "" ++ "\""
    let v ← match v with
      | .obj _ =>
        let tj ← getV n v "toJSON"
        if ← isCallable tj then callV n tj v #[] else pure v
      | _ => pure v
    match v with
    | .undef => pure .undef
    | .null => pure (.str "null")
    | .bool b => pure (.str (if b then "true" else "false"))
    | .num x => pure (.str (if x.isFinite then numToString x else "null"))
    | .str s => pure (.str (quote s))
    | .obj id =>
      let o ← getObj id
      match o.kind with
      | .closure .. | .native _ | .bound .. => pure .undef
      | .prim p => jsonStr n p depth
      | .array es =>
        let parts ← es.toList.mapM fun e => do
          match ← jsonStr n e (depth + 1) with
          | .str s => pure s
          | _ => pure "null"
        pure (.str ("[" ++ ",".intercalate parts ++ "]"))
      | _ =>
        let ks := o.ownKeys.filter fun k => match o.getOwn k with | some p => p.enumerable | none => false
        let parts ← ks.toList.filterMapM fun k => do
          match ← jsonStr n (← getV n v k) (depth + 1) with
          | .str s => pure (some (quote k ++ ":" ++ s))
          | _ => pure none
        pure (.str ("{" ++ ",".intercalate parts ++ "}"))

def stringOrMath : Nat → Native → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args => do
    let a0 := argD args 0
    let a1 := argD args 1
    let num1 (f : Float → Float) : M Value := do pure (.num (f (← toNum n a0)))
    match id with
    | .mathFloor => num1 Float.floor
    | .mathCeil => num1 Float.ceil
    | .mathAbs => num1 Float.abs
    | .mathSqrt => num1 Float.sqrt
    | .mathSin => num1 Float.sin
    | .mathCos => num1 Float.cos
    | .mathTan => num1 Float.tan
    | .mathAtan => num1 Float.atan
    | .mathLog => num1 Float.log
    | .mathExp => num1 Float.exp
    | .mathTrunc => num1 fun x => if x.isFinite then (if x < 0 then -((-x).floor) else x.floor) else x
    | .mathSign => num1 fun x => if x.isNaN then x else if x > 0 then 1 else if x < 0 then -1 else x
    | .mathRound => num1 fun x =>
        if !x.isFinite || x == 0 then x
        else if x < 0 && x ≥ -0.5 then -0.0
        else (x + 0.5).floor
    | .mathAtan2 => pure (.num (Float.atan2 (← toNum n a0) (← toNum n a1)))
    | .mathPow => pure (.num (jsPow (← toNum n a0) (← toNum n a1)))
    | .mathMax | .mathMin =>
      let xs ← args.toList.mapM (toNum n)
      let isMax := id == .mathMax
      let r := xs.foldl (fun acc x =>
        if acc.isNaN || x.isNaN then nan
        else if isMax then (if x > acc || (x == acc && isNegZero acc && !isNegZero x) then x else acc)
        else (if x < acc || (x == acc && isNegZero x) then x else acc))
        (if isMax then -inf else inf)
      pure (.num r)
    | .mathRandom =>
      let h ← get
      let x := h.rng
      let x := x ^^^ (x <<< 13); let x := x ^^^ (x >>> 7); let x := x ^^^ (x <<< 17)
      set { h with rng := x }
      pure (.num ((x >>> 11).toFloat / 9007199254740992.0))
    | _ =>
      -- String.prototype methods: this is coerced to a string (RequireObjectCoercible)
      let tp ← thisPrim thisV
      match tp with
      | .undef | .null => throwErr .type "String.prototype method called on null or undefined"
      | _ => pure ()
      let s ← toStr n tp
      let cs := charsOf s
      match id with
      | .stringCharAt =>
        let i := toIntegerOrInf (← toNum n a0)
        pure (.str (if i < 0 || i ≥ Float.ofNat cs.size then "" else String.singleton cs[i.toUInt64.toNat]!))
      | .stringCharCodeAt =>
        let i := toIntegerOrInf (← toNum n a0)
        pure (.num (if i < 0 || i ≥ Float.ofNat cs.size then nan else Float.ofNat cs[i.toUInt64.toNat]!.toNat))
      | .stringIndexOf =>
        let p ← toStr n a0
        let st := relIndex (toIntegerOrInf (← toNum n a1)) cs.size
        let st := if (toIntegerOrInf (← toNum n a1)) < 0 then 0 else st
        pure (.num (match indexOfFrom s p st with | some i => Float.ofNat i | none => -1))
      | .stringLastIndexOf =>
        let p ← toStr n a0
        pure (.num (match lastIndexOfStr s p with | some i => Float.ofNat i | none => -1))
      | .stringIncludes =>
        let p ← toStr n a0
        pure (.bool (indexOfFrom s p 0).isSome)
      | .stringStartsWith =>
        let p ← toStr n a0
        pure (.bool (s.startsWith p))
      | .stringEndsWith =>
        let p ← toStr n a0
        pure (.bool (s.endsWith p))
      | .stringSlice =>
        let st := relIndex (← toNum n a0) cs.size
        let en ← match a1 with | .undef => pure cs.size | v => do pure (relIndex (← toNum n v) cs.size)
        pure (.str (if st < en then substr s st en else ""))
      | .stringSubstring =>
        let clamp (x : Float) : Nat :=
          let x := toIntegerOrInf x
          if x < 0 then 0 else if x > Float.ofNat cs.size then cs.size else x.toUInt64.toNat
        let st := clamp (← toNum n a0)
        let en ← match a1 with | .undef => pure cs.size | v => do pure (clamp (← toNum n v))
        pure (.str (substr s (min st en) (max st en)))
      | .stringSubstr =>
        let st := relIndex (← toNum n a0) cs.size
        let len ← match a1 with
          | .undef => pure (cs.size - st)
          | v => do
            let l := toIntegerOrInf (← toNum n v)
            pure (if l < 0 then 0 else min l.toUInt64.toNat (cs.size - st))
        pure (.str (substr s st (st + len)))
      | .stringToUpperCase => pure (.str s.toUpper)
      | .stringToLowerCase => pure (.str s.toLower)
      | .stringTrim => pure (.str (trimJs s))
      | .stringRepeat =>
        let c := toIntegerOrInf (← toNum n a0)
        if c < 0 || c.isInf then throwErr .range "Invalid count value"
        pure (.str (String.join (List.replicate c.toUInt64.toNat s)))
      | .stringConcat =>
        let parts ← args.toList.mapM (toStr n)
        pure (.str (s ++ String.join parts))
      | .stringSplit =>
        match a0 with
        | .undef => newArray #[.str s]
        | v =>
          let sep ← toStr n v
          let parts := splitOn s sep
          let lim ← match a1 with
            | .undef => pure parts.size
            | l => do pure (toUint32 (← toNum n l))
          newArray ((parts.extract 0 lim).map .str)
      | _ => throwErr .type "not a function"

end

/-! ## The realm: global object and intrinsics (§9.3, §19) -/

def ctorWith (name : String) (id : Native) (len : Nat) (proto : Nat) : M Value := do
  let c ← mkNative id name len
  if let .obj cid := c then
    defineOwn cid "prototype" (.data (.obj proto) false false false)
  setHidden proto "constructor" c
  pure c

def initRealm : M Unit := do
  let objectProto ← alloc {}
  let functionProto ← alloc { proto := .obj objectProto, kind := .native .functionProto }
  let mk (k : Kind := .ordinary) : M Nat := alloc { proto := .obj objectProto, kind := k }
  let arrayProto ← mk (.array #[])
  let stringProto ← mk (.prim (.str ""))
  let numberProto ← mk (.prim (.num 0))
  let booleanProto ← mk (.prim (.bool false))
  let errorProto ← mk
  let mut errorProtos := #[errorProto]
  for _ in [1:7] do
    let p ← alloc { proto := .obj errorProto }
    errorProtos := errorProtos.push p
  let gl ← mk
  let rl : Realm := Realm.mk gl objectProto functionProto arrayProto stringProto numberProto
    booleanProto errorProtos 0
  modify fun h => { h with realm := rl }
  let g := gl
  let thrower ← mkNative .throwTypeError "" 0
  if let .obj t := thrower then
    modifyObj t fun o => { o with extensible := false }
    modify fun h => { h with realm := { h.realm with throwTypeError := t } }
  defineOwn functionProto "length" (.data (.num 0) false false true)
  defineOwn functionProto "name" (.data (.str "") false false true)
  setHidden g "globalThis" (.obj g)
  defineOwn g "undefined" (.data .undef false false false)
  defineOwn g "NaN" (.data (.num nan) false false false)
  defineOwn g "Infinity" (.data (.num inf) false false false)
  method g "print" .print 1
  method g "isNaN" .isNaN 1
  method g "isFinite" .isFinite 1
  method g "parseInt" .parseInt 2
  method g "parseFloat" .parseFloat 1
  -- Object
  let objectC ← ctorWith "Object" .objectCtor 1 objectProto
  setHidden g "Object" objectC
  if let .obj oc := objectC then
    method oc "keys" .objectKeys 1
    method oc "getPrototypeOf" .objectGetPrototypeOf 1
    method oc "setPrototypeOf" .objectSetPrototypeOf 2
    method oc "create" .objectCreate 2
    method oc "defineProperty" .objectDefineProperty 3
    method oc "getOwnPropertyNames" .objectGetOwnPropertyNames 1
    method oc "getOwnPropertyDescriptor" .objectGetOwnPropertyDescriptor 2
    method oc "is" .objectIs 2
    method oc "freeze" .objectFreeze 1
    method oc "isFrozen" .objectIsFrozen 1
    method oc "preventExtensions" .objectPreventExtensions 1
    method oc "isExtensible" .objectIsExtensible 1
  method objectProto "hasOwnProperty" .objectProtoHasOwnProperty 1
  method objectProto "toString" .objectProtoToString 0
  method objectProto "toLocaleString" .objectProtoToLocaleString 0
  method objectProto "valueOf" .objectProtoValueOf 0
  method objectProto "isPrototypeOf" .objectProtoIsPrototypeOf 1
  method objectProto "propertyIsEnumerable" .objectProtoPropertyIsEnumerable 1
  -- Function
  setHidden g "Function" (← ctorWith "Function" .functionCtor 1 functionProto)
  method functionProto "call" .functionProtoCall 1
  method functionProto "apply" .functionProtoApply 2
  method functionProto "bind" .functionProtoBind 1
  method functionProto "toString" .functionProtoToString 0
  -- Array
  let arrayC ← ctorWith "Array" .arrayCtor 1 arrayProto
  setHidden g "Array" arrayC
  if let .obj ac := arrayC then method ac "isArray" .arrayIsArray 1
  for (nm, f, l) in [("push", Native.arrayPush, 1), ("pop", .arrayPop, 0), ("shift", .arrayShift, 0),
      ("unshift", .arrayUnshift, 1), ("slice", .arraySlice, 2), ("splice", .arraySplice, 2),
      ("join", .arrayJoin, 1), ("toString", .arrayToString, 0), ("indexOf", .arrayIndexOf, 1),
      ("lastIndexOf", .arrayLastIndexOf, 1), ("map", .arrayMap, 1), ("forEach", .arrayForEach, 1),
      ("filter", .arrayFilter, 1), ("reduce", .arrayReduce, 1), ("concat", .arrayConcat, 1),
      ("reverse", .arrayReverse, 0), ("sort", .arraySort, 1), ("some", .arraySome, 1),
      ("every", .arrayEvery, 1), ("includes", .arrayIncludes, 1), ("find", .arrayFind, 1),
      ("findIndex", .arrayFindIndex, 1), ("fill", .arrayFill, 1)] do
    method arrayProto nm f l
  -- String
  let stringC ← ctorWith "String" .stringCtor 1 stringProto
  setHidden g "String" stringC
  if let .obj sc := stringC then method sc "fromCharCode" .stringFromCharCode 1
  for (nm, f, l) in [("charAt", Native.stringCharAt, 1), ("charCodeAt", .stringCharCodeAt, 1),
      ("indexOf", .stringIndexOf, 1), ("lastIndexOf", .stringLastIndexOf, 1),
      ("slice", .stringSlice, 2), ("substring", .stringSubstring, 2), ("substr", .stringSubstr, 2),
      ("toUpperCase", .stringToUpperCase, 0), ("toLowerCase", .stringToLowerCase, 0),
      ("trim", .stringTrim, 0), ("split", .stringSplit, 2), ("concat", .stringConcat, 1),
      ("toString", .stringToString, 0), ("valueOf", .stringToString, 0),
      ("includes", .stringIncludes, 1), ("startsWith", .stringStartsWith, 1),
      ("endsWith", .stringEndsWith, 1), ("repeat", .stringRepeat, 1)] do
    method stringProto nm f l
  -- Number, Boolean
  let numberC ← ctorWith "Number" .numberCtor 1 numberProto
  setHidden g "Number" numberC
  if let .obj nc := numberC then
    defineOwn nc "MAX_SAFE_INTEGER" (.data (.num 9007199254740991.0) false false false)
    defineOwn nc "MIN_SAFE_INTEGER" (.data (.num (-9007199254740991.0)) false false false)
    defineOwn nc "MAX_VALUE" (.data (.num (Float.ofBits 0x7FEFFFFFFFFFFFFF)) false false false)
    defineOwn nc "MIN_VALUE" (.data (.num (Float.ofBits 1)) false false false)
    defineOwn nc "EPSILON" (.data (.num (Float.ofBits 0x3CB0000000000000)) false false false)
    defineOwn nc "NaN" (.data (.num nan) false false false)
    defineOwn nc "POSITIVE_INFINITY" (.data (.num inf) false false false)
    defineOwn nc "NEGATIVE_INFINITY" (.data (.num (-inf)) false false false)
    method nc "isInteger" .numberIsInteger 1
  method numberProto "toString" .numberToString 1
  method numberProto "valueOf" .numberValueOf 0
  method numberProto "toFixed" .numberToFixed 1
  setHidden g "Boolean" (← ctorWith "Boolean" .booleanCtor 1 booleanProto)
  method booleanProto "toString" .booleanToString 0
  method booleanProto "valueOf" .booleanValueOf 0
  -- Errors
  for i in [0:7] do
    let p := errorProtos[i]!
    let c ← ctorWith (errorNames[i]!) (.errorCtor i) 1 p
    if i > 0 then
      if let .obj cid := c then
        if let .obj e0 ← ownValue g "Error" then modifyObj cid fun o => { o with proto := .obj e0 }
    setHidden g (errorNames[i]!) c
    setHidden p "name" (.str (errorNames[i]!))
    setHidden p "message" (.str "")
  method errorProto "toString" .errorToString 0
  -- Math
  let math ← mk
  setHidden g "Math" (.obj math)
  for (nm, f, l) in [("floor", Native.mathFloor, 1), ("ceil", .mathCeil, 1), ("abs", .mathAbs, 1),
      ("max", .mathMax, 2), ("min", .mathMin, 2), ("pow", .mathPow, 2), ("sqrt", .mathSqrt, 1),
      ("round", .mathRound, 1), ("random", .mathRandom, 0), ("sin", .mathSin, 1),
      ("cos", .mathCos, 1), ("tan", .mathTan, 1), ("atan", .mathAtan, 1), ("atan2", .mathAtan2, 2),
      ("log", .mathLog, 1), ("exp", .mathExp, 1), ("trunc", .mathTrunc, 1), ("sign", .mathSign, 1)] do
    method math nm f l
  defineOwn math "PI" (.data (.num 3.141592653589793) false false false)
  defineOwn math "E" (.data (.num 2.718281828459045) false false false)
  defineOwn math "LN2" (.data (.num 0.6931471805599453) false false false)
  defineOwn math "LN10" (.data (.num 2.302585092994046) false false false)
  defineOwn math "SQRT2" (.data (.num 1.4142135623730951) false false false)
  -- JSON, console
  let json ← mk
  setHidden g "JSON" (.obj json)
  method json "stringify" .jsonStringify 3
  let console ← mk
  setHidden g "console" (.obj console)
  method console "log" .print 0

/-- A fresh realm. -/
def freshHeap : Heap :=
  match initRealm.run {} with
  | .ok _ h => h
  | .error _ h => h

/-- Fuel for one script: far more than any nesting or loop the step budget allows. -/
def defaultFuel : Nat := 1 <<< 40

/-- GlobalDeclarationInstantiation (§16.1.7), then the statements. -/
def runScriptM (s : Script) : M Unit := do
  let h ← get
  let g := h.realm.globalObj
  let ctx : Ctx := { env := 0, thisV := .obj g, strict := s.strict }
  for v in s.vars do
    if ((h.obj g).getOwn v).isNone then defineOwn g v (.data .undef true true false)
  -- top-level functions are properties of the global object
  for st in s.body do
    if let .funDecl name f := st then
      defineOwn g name (.data (← makeClosure ctx f) true true false)
  -- top-level let/const are bindings of the global environment record
  for st in s.body do
    match st with
    | .decl .letK ds | .decl .constK ds =>
      for d in ds do
        match d with
        | .mk x _ =>
          if ((← getBinding 0 x)).isSome then throwErr .syntax s!"Identifier '{x}' has already been declared"
          declare 0 x { v := .undef, mutable := (match st with | .decl .letK _ => true | _ => false), init := false }
    | _ => pure ()
  let _ ← evalStmts defaultFuel ctx s.body
  pure ()

/-- The result of running a script. -/
inductive Outcome where
  | ok
  | threw (v : Value) (msg : String)
  | syntaxError (msg : String)
  | halted (why : String)
  deriving Inhabited

/-- Describe a thrown value the way an uncaught error is reported. -/
def describeThrown (h : Heap) (v : Value) : String :=
  match (toStr 100 v).run h with
  | .ok s _ => s
  | .error _ _ => "(an exception whose string conversion threw)"

def runScript (h : Heap) (src : String) (strict : Bool := false) : Outcome × Heap :=
  match parseScript src strict with
  | .error e => (.syntaxError e, h)
  | .ok s =>
    match (runScriptM s).run h with
    | .ok _ h' => (.ok, h')
    | .error (.throw v) h' => (.threw v (describeThrown h' v), h')
    | .error (.halt w) h' => (.halted w, h')

/-- Run a script in a fresh realm; the printed lines and the outcome. -/
def run (src : String) : Outcome × Array String :=
  let (o, h) := runScript freshHeap src
  (o, h.out)

end L4Factoidal.JS
