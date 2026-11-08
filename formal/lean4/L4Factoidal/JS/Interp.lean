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

def isConstructor (v : Value) : M Bool := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .closure f .. => pure (f.kind != .arrow && f.kind != .method && !f.gen)
    | .native nid => pure (match nid with
        | .objectCtor | .functionCtor | .arrayCtor | .stringCtor | .numberCtor | .booleanCtor
        | .errorCtor _ | .symbolCtor => true
        | _ => false)
    | .bound .. => pure true
    | _ => pure false
  | _ => pure false

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
  | .sym _ => pure "symbol"
  | .big _ => pure "bigint"
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
def makeClosure (ctx : Ctx) (f : FunDef) (nameHint : String := "") (home : Value := .undef) : M Value := do
  let r ← realm
  -- a named function expression sees its own name (§15.2.5)
  let env ← match f.name with
    | some n => if f.arrow then pure ctx.env else do
        let e ← newEnv (some ctx.env); pure e
    | none => pure ctx.env
  let home := if f.arrow then ctx.home else home
  let id ← alloc { proto := .obj r.functionProto, kind := .closure f env ctx.thisV ctx.newTarget home #[] }
  if env != ctx.env then
    if let some n := f.name then declare env n { v := .obj id, mutable := false }
  defineOwn id "length" (.data (.num (Float.ofNat f.expectedArgs)) false false true)
  defineOwn id "name" (.data (.str (f.name.getD nameHint)) false false true)
  if f.gen then
    let p ← alloc { proto := .obj r.generatorProto }
    defineOwn id "prototype" (.data (.obj p) true false false)
  else if f.kind == .normal then
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

/-- The `name` of a function stored under a property key (§10.2.9 SetFunctionName). -/
def nameOfKey (key : String) : M String := do
  match symOfKey? key with
  | some id =>
    let d := (← get).syms.getD id ""
    pure (if d.isEmpty && id ≥ wellKnown.size then "" else "[" ++ d ++ "]")
  | none => pure key



/-- Enumerable string keys of an object and its prototypes (§14.7.5.9 EnumerateObjectProperties). -/
def enumKeys (v : Value) : M (Array String) := do
  let h ← get
  let rec go : Nat → Value → Array String → Array String → Array String
    | 0, _, _, acc => acc
    | fuel + 1, .obj id, seen, acc =>
      let o := h.obj id
      let ks := o.ownStrKeys
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

/-! ## BigInt (§6.1.6.2) -/

/-- Two's complement bit operations on integers, through naturals of a width that
holds both operands. -/
def bigBits (f : Nat → Nat → Nat) (x y : Int) : Int :=
  let k := Nat.max (Nat.log2 x.natAbs) (Nat.log2 y.natAbs) + 2
  let m : Nat := 2 ^ k
  let enc (i : Int) : Nat := (i % (m : Int)).toNat
  let r := f (enc x) (enc y) % m
  if r ≥ m / 2 then (r : Int) - m else r

/-- Compare an integer with a finite double exactly: `lt`, `eq` or `gt`. -/
def cmpIntFloat (i : Int) (x : Float) : Ordering :=
  let (neg, num, den) := parts x
  let xn : Int := if neg then -(num : Int) else num
  compare (i * den) xn

/-- StringToBigInt (§7.1.14): `none` when the text is not an integer literal. -/
def strToBigInt (s0 : String) : Option Int :=
  let s := trimJs s0
  if s.isEmpty then some 0 else
  let cs := s.toList
  let radix (b : Nat) (ds : List Char) : Option Int :=
    if ds.isEmpty then none else
    ds.foldlM (fun (a : Nat) c => (hexVal c).bind fun d => if d < b then some (a * b + d) else none) 0
      |>.map (fun v => (v : Int))
  match cs with
  | '0' :: 'x' :: r | '0' :: 'X' :: r => radix 16 r
  | '0' :: 'o' :: r | '0' :: 'O' :: r => radix 8 r
  | '0' :: 'b' :: r | '0' :: 'B' :: r => radix 2 r
  | '-' :: r => (if r.all Char.isDigit && !r.isEmpty then radix 10 r else none).map (- ·)
  | '+' :: r => if r.all Char.isDigit then radix 10 r else none
  | r => if r.all Char.isDigit then radix 10 r else none

def bigOp (op : BinOp) (x y : Int) : M Value := do
  match op with
  | .sub => pure (.big (x - y))
  | .mul => pure (.big (x * y))
  | .div => if y == 0 then throwErr .range "Division by zero" else pure (.big (x.tdiv y))
  | .mod => if y == 0 then throwErr .range "Division by zero" else pure (.big (x.tmod y))
  | .exp =>
    if y < 0 then throwErr .range "Exponent must be non-negative"
    else if y > 100000 && x.natAbs > 1 then throwErr .range "Maximum BigInt size exceeded"
    else pure (.big (x ^ y.toNat))
  | .shl =>
    if y > 1000000 then throwErr .range "Maximum BigInt size exceeded"
    else pure (.big (if y ≥ 0 then x * 2 ^ y.toNat else x.fdiv (2 ^ (-y).toNat)))
  | .sar =>
    if y < -1000000 then throwErr .range "Maximum BigInt size exceeded"
    else pure (.big (if y ≥ 0 then x.fdiv (2 ^ y.toNat) else x * 2 ^ (-y).toNat))
  | .shr => throwErr .type "BigInts have no unsigned right shift, use >> instead"
  | .band => pure (.big (bigBits (· &&& ·) x y))
  | .bor => pure (.big (bigBits (· ||| ·) x y))
  | .bxor => pure (.big (bigBits (· ^^^ ·) x y))
  | _ => pure (.big 0)

/-! ## The evaluator -/

/-- The prototype of the running method's `[[HomeObject]]` (§13.3.7, `super`). -/
def homeProto (ctx : Ctx) : M Value := do
  match ctx.home with
  | .obj h => pure (← getObj h).proto
  | _ => throwErr .syntax "'super' keyword unexpected here"


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
    | .sym _ => getProto n (← realm).symbolProto key v
    | .big _ => getProto n (← realm).bigintProto key v
    | .undef => throwErr .type s!"Cannot read properties of undefined (reading '{key}')"
    | .null => throwErr .type s!"Cannot read properties of null (reading '{key}')"
termination_by structural n _ _ => n

def getProto : Nat → Nat → String → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, proto, key, recv => do
    match (← get).findProp proto key 1000 with
    | none => pure .undef
    | some (.data x ..) => pure x
    | some (.acc g _ _ _) => if g.isObj then callV n g recv #[] else pure .undef
termination_by structural n _ _ _ => n

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
termination_by structural n _ _ _ _ => n

/-- ToPrimitive (§7.1.1) with OrdinaryToPrimitive (§7.1.1.1). -/
def toPrim : Nat → Value → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, hint => do
    match v with
    | .obj _ =>
      let ex ← getV n v (symKey symToPrimitive)
      match ex with
      | .undef | .null =>
        let order := if hint == "string" then ["toString", "valueOf"] else ["valueOf", "toString"]
        tryMethods n v order
      | f =>
        if !(← isCallable f) then throwErr .type "Symbol.toPrimitive is not a function"
        let r ← callV n f v #[.str hint]
        if r.isObj then throwErr .type "Cannot convert object to primitive value"
        pure r
    | _ => pure v
termination_by structural n _ _ => n

def tryMethods : Nat → Value → List String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => throwErr .type "Cannot convert object to primitive value"
  | n + 1, v, m :: ms => do
    let f ← getV n v m
    if ← isCallable f then
      let r ← callV n f v #[]
      if !r.isObj then return r
    tryMethods n v ms
termination_by structural n _ _ => n

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
    | .sym _ => throwErr .type "Cannot convert a Symbol value to a number"
    | .big _ => throwErr .type "Cannot convert a BigInt value to a number"
    | .obj _ => toNum n (← toPrim n v "number")
termination_by structural n _ => n

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
    | .sym _ => throwErr .type "Cannot convert a Symbol value to a string"
    | .big i => pure (toString i)
    | .obj _ => toStr n (← toPrim n v "string")
termination_by structural n _ => n

/-- ToPropertyKey (§7.1.19). -/
def toKey : Nat → Value → M String
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .str s => pure s
    | .num x => pure (keyOfNum x)
    | .sym id => pure (symKey id)
    | .obj _ => toKey n (← toPrim n v "string")
    | _ => toStr n v
termination_by structural n _ => n

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
    | .sym _ => alloc { proto := .obj r.symbolProto, kind := .prim v }
    | .big _ => alloc { proto := .obj r.bigintProto, kind := .prim v }
termination_by structural n _ => n

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
    | .obj _, .num _ | .obj _, .str _ => looseEq n (← toPrim n a "default") b
    | .num _, .obj _ | .str _, .obj _ => looseEq n a (← toPrim n b "default")
    | .big x, .num y | .num y, .big x =>
      pure (y.isFinite && cmpIntFloat x y == .eq)
    | .big x, .str t | .str t, .big x => pure (strToBigInt t == some x)
    | .obj _, .big _ => looseEq n (← toPrim n a "default") b
    | .big _, .obj _ => looseEq n a (← toPrim n b "default")
    | .obj _, .sym _ => looseEq n (← toPrim n a "default") b
    | .sym _, .obj _ => looseEq n a (← toPrim n b "default")
    | _, _ => pure (strictEq a b)
termination_by structural n _ _ => n

/-- IsLessThan (§7.2.13): `none` is undefined (a NaN operand). -/
def lessThan : Nat → Value → Value → Bool → M (Option Bool)
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, a, b, leftFirst => do
    let (pa, pb) ← if leftFirst then do
        let x ← toPrim n a "number"; let y ← toPrim n b "number"; pure (x, y)
      else do
        let y ← toPrim n b "number"; let x ← toPrim n a "number"; pure (x, y)
    match pa, pb with
    | .str x, .str y => pure (some (decide (x < y)))
    | .big x, .big y => pure (some (decide (x < y)))
    | .big x, .str t => pure ((strToBigInt t).map fun y => decide (x < y))
    | .str t, .big y => pure ((strToBigInt t).map fun x => decide (x < y))
    | .big x, _ =>
      let y ← toNum n pb
      if y.isNaN then pure none else if y.isInf then pure (some (y > 0))
      else pure (some (cmpIntFloat x y == .lt))
    | _, .big y =>
      let x ← toNum n pa
      if x.isNaN then pure none else if x.isInf then pure (some (x < 0))
      else pure (some (cmpIntFloat y x == .gt))
    | _, _ =>
      let x ← toNum n pa
      let y ← toNum n pb
      if x.isNaN || y.isNaN then pure none else pure (some (x < y))
termination_by structural n _ _ _ => n

/-- OrdinaryHasInstance (§7.3.21). -/
def instOf : Nat → Value → Value → M Bool
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, c => do
    match c with
    | .obj cid =>
      let co ← getObj cid
      let hi ← getV n c (symKey symHasInstance)
      match hi with
      | .undef | .null => pure ()
      | f => return toBool (← callV n f c #[v])
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
termination_by structural n _ _ => n

/-- The binary operators (§13.15.3 ApplyStringOrNumericBinaryOperator and §13.10, §13.11). -/
def binop : Nat → BinOp → Value → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, op, a, b => do
    let numeric := match op with
      | .sub | .mul | .div | .mod | .exp | .shl | .sar | .shr | .band | .bor | .bxor => true
      | _ => false
    -- ToNumeric (§7.1.3) of the left operand completes before the right one starts
    let (a, b) ← if numeric && (a.isObj || b.isObj) then do
        let x ← toPrim n a "number"
        let x ← match x with
          | .big _ => pure x
          | _ => do pure (Value.num (← toNum n x))
        let y ← toPrim n b "number"
        let y ← match y with
          | .big _ => pure y
          | _ => do pure (Value.num (← toNum n y))
        pure (x, y)
      else pure (a, b)
    match a, b with
    | .big x, .big y =>
      if numeric then return ← bigOp op x y
    | .big _, _ | _, .big _ =>
      if numeric then throwErr .type "Cannot mix BigInt and other types, use explicit conversions"
    | _, _ => pure ()
    match op with
    | .add =>
      match a, b with
      | .num x, .num y => pure (.num (x + y))
      | .str x, .str y => pure (.str (x ++ y))
      | _, _ =>
        let pa ← toPrim n a "default"
        let pb ← toPrim n b "default"
        match pa, pb with
        | .str _, _ | _, .str _ => pure (.str ((← toStr n pa) ++ (← toStr n pb)))
        | .big x, .big y => pure (.big (x + y))
        | .big _, _ | _, .big _ => throwErr .type "Cannot mix BigInt and other types, use explicit conversions"
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
termination_by structural n _ _ _ => n

/-- `[[Call]]` (§10.2.1, §10.3.1, §10.4.1.1). -/
def callV : Nat → Value → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, f, thisV, args => do
    match f with
    | .obj id =>
      match (← getObj id).kind with
      | .closure fd env capThis capNT home _ =>
        match fd.kind with
        | .ctor _ => throwErr .type "Class constructor cannot be invoked without 'new'"
        | _ => callClosure n fd env capThis capNT home f thisV .undef args
      | .native nid => callNative n nid thisV args none
      | .bound t bt bargs => callV n t bt (bargs ++ args)
      | _ => throwErr .type "not a function"
    | _ => throwErr .type "not a function"
termination_by structural n _ _ _ => n

/-- PrepareForOrdinaryCall, OrdinaryCallBindThis, FunctionDeclarationInstantiation
(§10.2.1.1, §10.2.1.2, §10.2.11), then the body. -/
def callClosure : Nat → FunDef → Nat → Value → Value → Value → Value → Value → Value → Array Value → M Value
  | 0, _, _, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, fd, env, capThis, capNT, home, fnObj, thisV, newTarget, args => do
    tick
    let h ← get
    if h.depth ≥ h.maxDepth then throwErr .range "Maximum call stack size exceeded"
    set { h with depth := h.depth + 1 }
    let fenv ← newEnv (some env)
    let r ← realm
    let thisV ← if fd.arrow then pure capThis
      else if fd.strict then pure thisV
      else match thisV with
        | .undef | .null => pure (.obj r.globalObj)
        | .obj _ => pure thisV
        | v => do pure (.obj (← toObj n v))
    let nt := if fd.arrow then capNT else newTarget
    let fo := if fd.arrow then Value.undef else fnObj
    let ctx : Ctx := { env := fenv, thisV := thisV, strict := fd.strict, newTarget := nt, home := home, fnObj := fo }
    if fd.usesArgs then
      let a ← alloc { proto := .obj r.objectProto, kind := .args }
      for i in [0:args.size] do defineOwn a (toString i) (.data args[i]! true true true)
      setHidden a "length" (.num (Float.ofNat args.size))
      setHidden a (symKey symIterator) (← ownValue r.arrayProto "values")
      if fd.strict then
        let t := Value.obj r.throwTypeError
        defineOwn a "callee" (.acc t t false false)
      else setHidden a "callee" fnObj
      declare fenv "arguments" { v := .obj a }
    bindParams n ctx fd.params args 0
    if let some rp := fd.rest then
      bindPat n ctx rp (← newArray (args.extract fd.params.length args.size)) (.declare fenv true)
    for v in fd.vars do
      if !((← getBinding fenv v).isSome) then declare fenv v { v := .undef }
    if fd.kind == .ctor false then initFields n ctx fnObj thisV
    if fd.gen then
      -- a generator function returns its generator, suspended at the start (§27.5.3.1)
      let p ← getV n fnObj "prototype"
      let ctx' ← enterBlock n ctx fd.body
      let g ← alloc { proto := if p.isObj then p else .obj r.generatorProto,
                      kind := .gen [.block ctx' fd.body] 0 }
      modify fun h => { h with depth := h.depth - 1 }
      return .obj g
    let c ← evalBody n ctx fd.body
    modify fun h => { h with depth := h.depth - 1 }
    match c with
    | .ret v => pure v
    | _ => pure .undef
termination_by structural n _ _ _ _ _ _ _ _ _ => n

def bindParams : Nat → Ctx → List PatElem → Array Value → Nat → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], _, _ => pure ()
  | n + 1, ctx, (.mk p d) :: ps, args, i => do
    let v := args.getD i .undef
    let v ← match v, d with
      | .undef, some e => evalNamed n ctx e p
      | _, _ => pure v
    match p with
    | .id x => declare ctx.env x { v }
    | _ => bindPat n ctx p v (.declare ctx.env true)
    bindParams n ctx ps args (i + 1)
termination_by structural n _ _ _ _ => n

/-- Evaluate an initialiser; an anonymous function takes the binding's name
(§8.4.5 NamedEvaluation). -/
def evalNamed : Nat → Ctx → Expr → Pat → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e, p => do
    match e, p with
    | .func f, .id x => if f.name.isNone then makeClosure ctx f x else evalExpr n ctx e
    | .classE c, .id x => match c with
      | .mk none h k ms => evalClass n ctx (.mk none h k ms) x
      | _ => evalExpr n ctx e
    | _, _ => evalExpr n ctx e
termination_by structural n _ _ _ => n

/-- InitializeInstanceElements (§7.3.34): the class's fields on a new object. -/
def initFields : Nat → Ctx → Value → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, _, fnObj, thisV => do
    match fnObj with
    | .obj fid =>
      match (← getObj fid).kind with
      | .closure _ _ _ _ _ fields =>
        for (k, init) in fields do
          let v ← callV n init thisV #[]
          match thisV with
          | .obj tid =>
            match (← getObj tid).getOwn k with
            | some p => if !p.configurable then throwErr .type s!"Cannot redefine property: {k}"
            | none => pure ()
            defineOwn tid k (.data v true true true)
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()
termination_by structural n _ _ _ => n

/-- `[[Construct]]` (§10.2.2). -/
def construct : Nat → Value → Array Value → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, f, args, newTarget => do
    match f with
    | .obj id =>
      match (← getObj id).kind with
      | .closure fd env capThis capNT home _ =>
        match fd.kind with
        | .arrow | .method => throwErr .type "not a constructor"
        | _ =>
          let p ← getV n newTarget "prototype"
          let r ← realm
          let o ← alloc { proto := if p.isObj then p else .obj r.objectProto }
          let res ← callClosure n fd env capThis capNT home f (.obj o) newTarget args
          match fd.kind, res with
          | _, .obj _ => pure res
          | .ctor true, .undef => pure (.obj o)
          | .ctor true, _ => throwErr .type "Derived constructors may only return object or undefined"
          | _, _ => pure (.obj o)
      | .native nid => callNative n nid .undef args (some newTarget)
      | .bound t _ bargs => construct n t (bargs ++ args) (if strictEq newTarget f then t else newTarget)
      | _ => throwErr .type "not a constructor"
    | _ => throwErr .type "not a constructor"
termination_by structural n _ _ _ => n

/-- The block body of a function or script, after its declarations are bound. -/
def evalBody : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let ctx ← enterBlock n ctx ss
    evalStmts n ctx ss
termination_by structural n _ _ => n

/-- BlockDeclarationInstantiation (§14.2.3): a new environment when the block
declares `let`, `const` or functions; functions are created here (hoisting). -/
def enterBlock : Nat → Ctx → List Stmt → M Ctx
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let needs := ss.any fun s => match s with
      | .decl .letK _ | .decl .constK _ | .funDecl .. | .classDecl .. => true
      | _ => false
    if !needs then return ctx
    let env ← newEnv (some ctx.env)
    let ctx' := { ctx with env }
    declareLexical n ctx' ss
    return ctx'
termination_by structural n _ _ => n

def declareLexical : Nat → Ctx → List Stmt → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure ()
  | n + 1, ctx, s :: ss => do
    match s with
    | .decl .letK ds | .decl .constK ds =>
      let mutable := match s with | .decl .letK _ => true | _ => false
      for d in ds do
        for x in d.names do declare ctx.env x { v := .undef, mutable, init := false }
    | .classDecl name _ => declare ctx.env name { v := .undef, mutable := true, init := false }
    | .funDecl name f =>
      let c ← makeClosure ctx f
      declare ctx.env name { v := c }
    | _ => pure ()
    declareLexical n ctx ss
termination_by structural n _ _ => n

def evalStmts : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure .normal
  | n + 1, ctx, s :: ss => do
    let c ← evalStmt n ctx [] s
    match c with
    | .normal => evalStmts n ctx ss
    | _ => pure c
termination_by structural n _ _ => n

def evalBlock : Nat → Ctx → List Stmt → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, ss => do
    let ctx ← enterBlock n ctx ss
    evalStmts n ctx ss
termination_by structural n _ _ => n

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
      | none =>
        match (h.envs.getD e default).withObj with
        | some o => putV n (.obj o) x v ctx.strict
        | none => pure ()
    | none =>
      let g := h.realm.globalObj
      if (h.findProp g x 1000).isSome || !ctx.strict then putV n (.obj g) x v ctx.strict
      else throwErr .reference s!"{x} is not defined"
termination_by structural n _ _ _ => n

def lookup : Nat → Ctx → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x => do
    let h ← get
    match h.findEnv x 100000 (some ctx.env) with
    | some e =>
      match (h.envs.getD e default).vars.get? x with
      | some b =>
        if b.init then pure b.v else throwErr .reference s!"Cannot access '{x}' before initialization"
      | none =>
        match (h.envs.getD e default).withObj with
        | some o => getV n (.obj o) x
        | none => pure .undef
    | none =>
      let g := h.realm.globalObj
      if (h.findProp g x 1000).isSome then getV n (.obj g) x
      else throwErr .reference s!"{x} is not defined"
termination_by structural n _ _ => n

/-- PutValue on an assignment target, after its parts are evaluated. -/
def putTarget : Nat → Ctx → Expr → Option Value → Option String → Value → M Unit
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, target, base, key, v => do
    match target, base, key with
    | .ident x, _, _ => assignName n ctx x v
    | _, some b, some k => putV n b k v ctx.strict
    | _, _, _ => throwErr .syntax "Invalid assignment target"
termination_by structural n _ _ _ _ _ => n

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
termination_by structural n _ _ => n

def getRef : Nat → Ctx → Expr → Option Value → Option String → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e, base, key => do
    match e, base, key with
    | .ident x, _, _ => lookup n ctx x
    | _, some b, some k => getV n b k
    | _, _, _ => evalExpr n ctx e
termination_by structural n _ _ _ _ => n

def evalArgs : Nat → Ctx → List Expr → Array Value → M (Array Value)
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], acc => pure acc
  | n + 1, ctx, a :: as, acc => do
    match a with
    | .spread e =>
      let it ← getIterator n (← evalExpr n ctx e)
      let vs ← iterToArray n it #[]
      evalArgs n ctx as (acc ++ vs)
    | .ident "" => evalArgs n ctx as (acc.push .undef)
    | _ =>
      let v ← evalExpr n ctx a
      evalArgs n ctx as (acc.push v)
termination_by structural n _ _ _ => n

def evalProps : Nat → Ctx → Nat → List PropDef → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, [] => pure ()
  | n + 1, ctx, id, p :: ps => do
    let keyOf (k : PropKey) : M String := match k with
      | .lit s => pure s
      | .computed e => do toKey n (← evalExpr n ctx e)
    match p with
    | .spread e =>
      let src ← evalExpr n ctx e
      copyDataProps n id src []
    | .init k e =>
      let key ← keyOf k
      let v ← match e with
        | .func f => if f.name.isNone then makeClosure ctx f (← nameOfKey key) (.obj id) else evalExpr n ctx e
        | .classE (.mk none h c ms) => evalClass n ctx (.mk none h c ms) (← nameOfKey key)
        | _ => evalExpr n ctx e
      if key == "__proto__" && (match k with | .lit _ => true | _ => false) &&
          (match e with | .func _ => false | _ => true) then
        match v with
        | .obj _ | .null => modifyObj id fun o => { o with proto := v }
        | _ => pure ()
      else defineOwn id key (.data v true true true)
    | .getter k f =>
      let key ← keyOf k
      let g ← makeClosure ctx f ("get " ++ (← nameOfKey key)) (.obj id)
      let old := (← getObj id).props.get? key
      let s := match old with | some (.acc _ s _ _) => s | _ => .undef
      defineOwn id key (.acc g s true true)
    | .setter k f =>
      let key ← keyOf k
      let s ← makeClosure ctx f ("set " ++ (← nameOfKey key)) (.obj id)
      let old := (← getObj id).props.get? key
      let g := match old with | some (.acc g _ _ _) => g | _ => .undef
      defineOwn id key (.acc g s true true)
    evalProps n ctx id ps
termination_by structural n _ _ _ => n

/-- Evaluation of expressions (§13). -/
def evalExpr : Nat → Ctx → Expr → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e => do
    match e with
    | .num x => pure (.num x)
    | .bigint v => pure (.big v)
    | .str s => pure (.str s)
    | .bool b => pure (.bool b)
    | .null => pure .null
    | .ident x => lookup n ctx x
    | .this => pure ctx.thisV
    | .array es => newArray (← evalArgs n ctx es #[])
    | .spread _ => throwErr .syntax "unexpected spread"
    | .template cooked subs =>
      let parts ← evalArgs n ctx subs #[]
      let mut out := cooked.headD ""
      let mut i := 0
      for v in parts do
        let str ← match v with
          | .sym _ => throwErr .type "Cannot convert a Symbol value to a string"
          | _ => toStr n v
        out := out ++ str ++ cooked.getD (i + 1) ""
        i := i + 1
      pure (.str out)
    | .tagged tag cooked raw subs =>
      let (f, thisV) ← match tag with
        | .member o k => do let b ← evalExpr n ctx o; pure (← getV n b k, b)
        | _ => do pure (← evalExpr n ctx tag, Value.undef)
      let strs ← newArray (cooked.toArray.map .str)
      let raws ← newArray (raw.toArray.map .str)
      if let .obj sid := strs then
        defineOwn sid "raw" (.data raws false false false)
      let _ ← callNative n .objectFreeze .undef #[raws] none
      let _ ← callNative n .objectFreeze .undef #[strs] none
      let argv ← evalArgs n ctx subs #[strs]
      if !(← isCallable f) then throwErr .type "tag is not a function"
      callV n f thisV argv
    | .assignPat p rhs =>
      let v ← evalExpr n ctx rhs
      bindPat n ctx p v .assign
      pure v
    | .classE c => evalClass n ctx c ""
    | .newTarget => pure ctx.newTarget
    | .yieldE .. => throwErr .syntax "yield in this position is not supported"
    | .superMember k =>
      let proto ← homeProto ctx
      getSuper n proto k ctx.thisV
    | .superIndex k =>
      let key ← toKey n (← evalExpr n ctx k)
      let proto ← homeProto ctx
      getSuper n proto key ctx.thisV
    | .superCall args =>
      let argv ← evalArgs n ctx args #[]
      superCall n ctx argv
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
        | .neg => match ← toPrim n v "number" with
          | .big i => pure (.big (-i))
          | p => pure (.num (-(← toNum n p)))
        | .plus => pure (.num (← toNum n v))
        | .not => pure (.bool !(toBool v))
        | .bnot => match ← toPrim n v "number" with
          | .big i => pure (.big (-i - 1))
          | p => pure (intV (-(toInt32 (← toNum n p)) - 1))
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
      match ← toPrim n (← getRef n ctx target b k) "number" with
      | .big i =>
        let nv := if inc then i + 1 else i - 1
        putTarget n ctx target b k (.big nv)
        pure (.big (if pre then nv else i))
      | p =>
        let old ← toNum n p
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
        | .superMember k =>
          let proto ← homeProto ctx
          pure (← getSuper n proto k ctx.thisV, ctx.thisV)
        | .ident x =>
          let h ← get
          let thisV := match h.findEnv x 100000 (some ctx.env) with
            | some e => match (h.envs.getD e default).withObj with
              | some o => if ((h.envs.getD e default).vars.contains x) then Value.undef else .obj o
              | none => .undef
            | none => .undef
          pure (← lookup n ctx x, thisV)
        | _ => pure (← evalExpr n ctx callee, Value.undef)
      let argv ← evalArgs n ctx args #[]
      -- a direct eval (§19.2.1.1, PerformEval with direct = true)
      if let .ident "eval" := callee then
        if let .obj fid := f then
          if fid == (← realm).evalFn then
            return ← directEval n ctx (argD argv 0)
      if !(← isCallable f) then
        let what := match callee with
          | .ident x => x | .member _ k => k | _ => "expression"
        throwErr .type s!"{what} is not a function"
      callV n f thisV argv
    | .new callee args =>
      let f ← evalExpr n ctx callee
      let argv ← evalArgs n ctx args #[]
      if !(← isConstructor f) then
        let what := match callee with
          | .ident x => x | .member _ k => k | _ => "expression"
        throwErr .type s!"{what} is not a constructor"
      construct n f argv f
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
termination_by structural n _ _ => n

def whileLoop : Nat → Ctx → List String → Expr → Stmt → M Compl
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, c, body => do
    tick
    if !(toBool (← evalExpr n ctx c)) then return .normal
    let r ← evalStmt n ctx [] body
    match loopNext labels r with
    | some out => pure out
    | none => whileLoop n ctx labels c body
termination_by structural n _ _ _ _ => n

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
termination_by structural n _ _ _ _ => n

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
termination_by structural n _ _ _ _ _ _ _ => n

def copyEnv : Nat → Ctx → List String → M Ctx
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, ctx, names => do
    let h ← get
    let old := h.envs.getD ctx.env default
    let e ← newEnv old.parent
    for x in names do
      if let some b := old.vars.get? x then declare e x b
    pure { ctx with env := e }
termination_by structural n _ _ => n

def forInLoop : Nat → Ctx → List String → Option DeclKind → Pat → Value → List String → Stmt → M Compl
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, _, _, _, [], _ => pure .normal
  | n + 1, ctx, labels, kind, target, obj, k :: ks, body => do
    tick
    -- a key deleted during the loop is not visited
    let present ← match obj with
      | .obj id => pure ((← get).findProp id k 1000).isSome
      | _ => pure true
    if !present then return ← forInLoop n ctx labels kind target obj ks body
    let ctx' ← bindIter n ctx kind target (.str k)
    let r ← evalStmt n ctx' [] body
    match loopNext labels r with
    | some out => pure out
    | none => forInLoop n ctx labels kind target obj ks body
termination_by structural n _ _ _ _ _ _ _ => n

/-- ForIn/OfBodyEvaluation (§14.7.5.7): bind the next value, in a new environment
for `let` and `const`. -/
def bindIter : Nat → Ctx → Option DeclKind → Pat → Value → M Ctx
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, kind, target, v => do
    match kind with
    | some .letK | some .constK =>
      let e ← newEnv (some ctx.env)
      for x in target.names do declare e x { v := .undef, mutable := true, init := false }
      let ctx' := { ctx with env := e }
      bindPat n ctx' target v (.declare e (kind == some .letK))
      pure ctx'
    | some .var => bindPat n ctx target v .var; pure ctx
    | none => bindPat n ctx target v .assign; pure ctx
termination_by structural n _ _ _ _ => n

/-- for-of (§14.7.5.7 with iterationKind iterate): IteratorClose on every exit
that is not the end of the iterator. -/
def forOfLoop : Nat → Ctx → List String → Option DeclKind → Pat → Value → Stmt → M Compl
  | 0, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, kind, target, it, body => do
    tick
    match ← iterStep n it with
    | none => pure .normal
    | some v =>
      let r ← tryCatch (do
          let ctx' ← bindIter n ctx kind target v
          let c ← evalStmt n ctx' [] body
          pure (Except.ok c))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw e) =>
        let _ ← tryCatch (iterClose n it) (fun _ => pure ())
        throw (.throw e)
      | .error a => throw a
      | .ok c =>
        match loopNext labels c with
        | some out => iterClose n it; pure out
        | none => forOfLoop n ctx labels kind target it body
termination_by structural n _ _ _ _ _ _ => n

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
termination_by structural n _ _ _ _ => n

def runCases : Nat → Ctx → List Case → M Compl
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, _, [] => pure .normal
  | n + 1, ctx, (.mk _ body) :: cs => do
    let r ← evalStmts n ctx body
    match r with
    | .normal => runCases n ctx cs
    | _ => pure r
termination_by structural n _ _ => n

def evalDecls : Nat → Ctx → DeclKind → List Decl → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, [] => pure ()
  | n + 1, ctx, kind, (.mk p init) :: ds => do
    match kind with
    | .var =>
      if let some e := init then
        let v ← evalNamed n ctx e p
        bindPat n ctx p v .var
    | _ =>
      let v ← match init with
        | some e => evalNamed n ctx e p
        | none => pure .undef
      bindPat n ctx p v (.declare ctx.env (kind == .letK))
    evalDecls n ctx kind ds
termination_by structural n _ _ _ => n

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
          for x in d.names do declare env x { v := .undef, mutable := k == .letK, init := false }
        evalDecls n ctx' k ds
        let names := ds.flatMap Decl.names
        forLoop n ctx' labels (if k == .letK then names else []) test update body true
      | some (.expr e) =>
        let _ ← evalExpr n ctx e
        forLoop n ctx labels [] test update body true
      | none => forLoop n ctx labels [] test update body true
    | .forIn kind target obj body =>
      let o ← evalExpr n ctx obj
      let keys ← enumKeys o
      forInLoop n ctx labels kind target o keys.toList body
    | .forOf kind target obj body =>
      let o ← evalExpr n ctx obj
      let it ← getIterator n o
      forOfLoop n ctx labels kind target it body
    | .withS o body =>
      let id ← toObj n (← evalExpr n ctx o)
      let env ← modifyGet fun h => (h.envs.size, { h with envs := h.envs.push { parent := some ctx.env, withObj := some id } })
      evalStmt n { ctx with env } [] body
    | .classDecl name c =>
      let v ← evalClass n ctx c name
      declare ctx.env name { v }
      pure .normal
    | .block ss => evalBlock n ctx ss
    | .throwS e => throw (.throw (← evalExpr n ctx e))
    | .tryS body param handler fin =>
      let r ← tryCatch (do let c ← evalBlock n ctx body; pure (Except.ok c))
        (fun a => pure (Except.error a))
      let r ← match r, handler with
        | .error (.throw v), some hs =>
          tryCatch (do
            let env ← newEnv (some ctx.env)
            if let some p := param then
              for x in p.names do declare env x { v := .undef, init := false }
              bindPat n { ctx with env } p v (.declare env true)
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
termination_by structural n _ _ _ => n

/-- BindingInitialization and DestructuringAssignmentEvaluation (§8.6.2,
§13.15.5). -/
def bindPat : Nat → Ctx → Pat → Value → BindMode → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, p, v, mode => do
    match p with
    | .id x =>
      match mode with
      | .declare env mutable => declare env x { v, mutable }
      | _ => assignName n ctx x v
    | .target e =>
      let (b, k) ← evalRef n ctx e
      putTarget n ctx e b k v
    | .obj props rest =>
      match v with
      | .undef | .null => throwErr .type "Cannot destructure 'undefined' or 'null'"
      | _ => pure ()
      let used ← bindProps n ctx props v mode []
      if let some r := rest then
        let o ← newObject
        copyDataProps n o v used
        bindPat n ctx r (.obj o) mode
    | .arr elems rest =>
      let it ← getIterator n v
      let r ← tryCatch (do
          let done ← bindElems n ctx elems it mode false
          let done ← match rest with
            | some rp =>
              if done then
                bindPat n ctx rp (← newArray #[]) mode
                pure true
              else
                let vs ← iterToArray n it #[]
                bindPat n ctx rp (← newArray vs) mode
                pure true
            | none => pure done
          pure (Except.ok done))
        (fun a => pure (Except.error a))
      match r with
      | .ok done => if !done then iterClose n it
      | .error (.throw e) =>
        let _ ← tryCatch (iterClose n it) (fun _ => pure ())
        throw (.throw e)
      | .error a => throw a
termination_by structural n _ _ _ _ => n

def bindProps : Nat → Ctx → List PatProp → Value → BindMode → List String → M (List String)
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], _, _, used => pure used
  | n + 1, ctx, (.mk k p d) :: ps, v, mode, used => do
    let key ← match k with
      | .lit s => pure s
      | .computed e => do toKey n (← evalExpr n ctx e)
    let x ← getV n v key
    let x ← match x, d with
      | .undef, some e => evalNamed n ctx e p
      | _, _ => pure x
    bindPat n ctx p x mode
    bindProps n ctx ps v mode (key :: used)
termination_by structural n _ _ _ _ _ => n

/-- The elements of an array pattern; answers whether the iterator is done. -/
def bindElems : Nat → Ctx → List (Option PatElem) → Value → BindMode → Bool → M Bool
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], _, _, done => pure done
  | n + 1, ctx, e :: es, it, mode, done => do
    let (x, done) ← if done then pure (Value.undef, true) else do
      match ← iterStep n it with
      | some x => pure (x, false)
      | none => pure (Value.undef, true)
    match e with
    | none => bindElems n ctx es it mode done
    | some (.mk p d) =>
      let x ← match x, d with
        | .undef, some e => evalNamed n ctx e p
        | _, _ => pure x
      bindPat n ctx p x mode
      bindElems n ctx es it mode done
termination_by structural n _ _ _ _ _ => n

/-- CopyDataProperties (§7.3.25): own enumerable properties, except `excluded`. -/
def copyDataProps : Nat → Nat → Value → List String → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, target, src, excluded => do
    match src with
    | .undef | .null => pure ()
    | _ =>
      let sid ← toObj n src
      let o ← getObj sid
      for k in o.ownKeys do
        if !excluded.contains k then
          match (← getObj sid).getOwn k with
          | some p =>
            if p.enumerable then
              let v ← getV n (.obj sid) k
              defineOwn target k (.data v true true true)
          | none => pure ()
termination_by structural n _ _ _ => n

/-- GetIterator (§7.4.2) with the sync kind. -/
def getIterator : Nat → Value → M Value
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    let m ← match v with
      | .undef | .null => throwErr .type "object is not iterable"
      | _ => getV n v (symKey symIterator)
    if !(← isCallable m) then throwErr .type "object is not iterable"
    let it ← callV n m v #[]
    if !it.isObj then throwErr .type "Result of the Symbol.iterator method is not an object"
    pure it
termination_by structural n _ => n

/-- IteratorStepValue (§7.4.10): `none` when done. -/
def iterStep : Nat → Value → M (Option Value)
  | 0, _ => throw (.halt "fuel")
  | n + 1, it => do
    let next ← getV n it "next"
    let r ← callV n next it #[]
    if !r.isObj then throwErr .type "Iterator result is not an object"
    if toBool (← getV n r "done") then pure none
    else pure (some (← getV n r "value"))
termination_by structural n _ => n

/-- IteratorClose (§7.4.11) after a normal or break completion. -/
def iterClose : Nat → Value → M Unit
  | 0, _ => throw (.halt "fuel")
  | n + 1, it => do
    let ret ← getV n it "return"
    match ret with
    | .undef | .null => pure ()
    | f =>
      let r ← callV n f it #[]
      if !r.isObj then throwErr .type "Iterator result is not an object"
termination_by structural n _ => n

def iterToArray : Nat → Value → Array Value → M (Array Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, it, acc => do
    tick
    match ← iterStep n it with
    | some v => iterToArray n it (acc.push v)
    | none => pure acc
termination_by structural n _ _ => n

/-- `super.k`: [[Get]] on the home object's prototype with `this` as receiver. -/
def getSuper : Nat → Value → String → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, proto, k, thisV => do
    match proto with
    | .obj pid => getProto n pid k thisV
    | _ => throwErr .type s!"Cannot read properties of null (reading '{k}')"
termination_by structural n _ _ _ => n

/-- `super(...)` (§13.3.7.1): run the parent constructor on this object. -/
def superCall : Nat → Ctx → Array Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, args => do
    let parent ← match ctx.fnObj with
      | .obj fid => pure (← getObj fid).proto
      | _ => throwErr .syntax "'super' keyword unexpected here"
    match parent with
    | .obj pid =>
      match (← getObj pid).kind with
      | .closure fd env capThis capNT home _ =>
        if fd.arrow || fd.kind == .method then throwErr .type "Super constructor is not a constructor"
        let r ← callClosure n fd env capThis capNT home parent ctx.thisV ctx.newTarget args
        if let .obj _ := r then
          if !(strictEq r ctx.thisV) then
            -- a parent that returns another object: copy it into this one
            if let .obj tid := ctx.thisV then
              if let .obj rid := r then
                let ro ← getObj rid
                modifyObj tid fun o => { o with kind := ro.kind, props := ro.props, keys := ro.keys }
      | .native _ | .bound .. =>
        let r ← construct n parent args ctx.newTarget
        if let .obj tid := ctx.thisV then
          if let .obj rid := r then
            let ro ← getObj rid
            let merge (o : Obj) : Obj :=
              let props := ro.props.fold (fun m k p => m.insert k p) o.props
              let keys := o.keys ++ ro.keys.filter (!o.keys.contains ·)
              { o with kind := ro.kind, props := props, keys := keys }
            modifyObj tid merge
      | _ => throwErr .type "Super constructor is not a constructor"
    | _ => throwErr .type "Super constructor null of anonymous class is not a constructor"
    initFields n ctx ctx.fnObj ctx.thisV
    pure ctx.thisV
termination_by structural n _ _ => n

/-- ClassDefinitionEvaluation (§15.7.14). `nameHint` names an anonymous class. -/
def evalClass : Nat → Ctx → ClassDef → String → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, .mk name heritage ctor members, nameHint => do
    let r ← realm
    let cenv ← newEnv (some ctx.env)
    if let some x := name then declare cenv x { v := .undef, mutable := false, init := false }
    let cctx : Ctx := { ctx with env := cenv, strict := true }
    let (protoParent, ctorParent) ← match heritage with
      | none => pure (Value.obj r.objectProto, Value.obj r.functionProto)
      | some h =>
        let sc ← evalExpr n cctx h
        match sc with
        | .null => pure (Value.null, Value.obj r.functionProto)
        | _ =>
          if !(← isConstructor sc) then throwErr .type "Class extends value is not a constructor or null"
          let pp ← getV n sc "prototype"
          match pp with
          | .obj _ | .null => pure (pp, sc)
          | _ => throwErr .type "Class extends value does not have valid prototype property"
    let proto ← alloc { proto := protoParent }
    let derived := heritage.isSome
    let fd := match ctor with
      | some f => f
      | none =>
        if derived then
          FunDef.mk none [] (some (.id "args")) [.expr (.superCall [.spread (.ident "args")])] [] false true (.ctor true) false
        else FunDef.mk none [] none [] [] false true (.ctor false) false
    let cname := name.getD nameHint
    let fid ← alloc { proto := ctorParent, kind := .closure fd cenv .undef .undef (.obj proto) #[] }
    defineOwn fid "length" (.data (.num (Float.ofNat fd.expectedArgs)) false false true)
    defineOwn fid "name" (.data (.str cname) false false true)
    defineOwn fid "prototype" (.data (.obj proto) false false false)
    setHidden proto "constructor" (.obj fid)
    let fields ← defineMembers n cctx fid proto members #[]
    modifyObj fid fun o => match o.kind with
      | .closure f e t nt h _ => { o with kind := .closure f e t nt h fields }
      | k => { o with kind := k }
    if let some x := name then declare cenv x { v := .obj fid, mutable := false }
    pure (.obj fid)
termination_by structural n _ _ _ => n

/-- ClassElementEvaluation for each member; answers the instance fields. -/
def defineMembers : Nat → Ctx → Nat → Nat → List Member → Array (String × Value) → M (Array (String × Value))
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, _, _, [], acc => pure acc
  | n + 1, ctx, fid, proto, (.mk static kind k f) :: ms, acc => do
    let target := if static then fid else proto
    let key ← match k with
      | .lit s => pure s
      | .computed e => do toKey n (← evalExpr n { ctx with thisV := .obj fid } e)
    if static && key == "prototype" && kind != .field then
      throwErr .type "Classes may not have a static property named 'prototype'"
    let nm ← nameOfKey key
    match kind with
    | .method =>
      let m ← makeClosure ctx f nm (.obj target)
      setHidden target key m
      defineMembers n ctx fid proto ms acc
    | .getter =>
      let g ← makeClosure ctx f ("get " ++ nm) (.obj target)
      let s := match (← getObj target).props.get? key with | some (.acc _ s _ _) => s | _ => .undef
      defineOwn target key (.acc g s false true)
      defineMembers n ctx fid proto ms acc
    | .setter =>
      let s ← makeClosure ctx f ("set " ++ nm) (.obj target)
      let g := match (← getObj target).props.get? key with | some (.acc g _ _ _) => g | _ => .undef
      defineOwn target key (.acc g s false true)
      defineMembers n ctx fid proto ms acc
    | .field =>
      let init ← makeClosure ctx f nm (.obj target)
      if static then
        let v ← callV n init (.obj fid) #[]
        defineOwn fid key (.data v true true true)
        defineMembers n ctx fid proto ms acc
      else defineMembers n ctx fid proto ms (acc.push (key, init))
termination_by structural n _ _ _ _ _ => n

/-- PerformEval (§19.2.1.1) for a direct call: the code sees the caller's scope. -/
def directEval : Nat → Ctx → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, src => do
    match src with
    | .str code =>
      match parseScript code ctx.strict with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok sc =>
        let env ← newEnv (some ctx.env)
        let ectx := { ctx with env, strict := sc.strict }
        -- var declarations of sloppy eval code go to the caller's variable scope
        for x in sc.vars do
          if sc.strict then declare env x { v := .undef }
          else if ((← get).findEnv x 100000 (some ctx.env)).isNone then
            if ctx.env == 0 then
              let g := (← realm).globalObj
              if ((← getObj g).getOwn x).isNone then defineOwn g x (.data .undef true true true)
            else declare ctx.env x { v := .undef }
        let ectx ← enterBlock n ectx sc.body
        evalCompletion n ectx sc.body .undef
    | v => pure v
termination_by structural n _ _ => n

/-- Statements with their completion value (§8.2, UpdateEmpty), as eval needs. -/
def evalCompletion : Nat → Ctx → List Stmt → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], v => pure v
  | n + 1, ctx, s :: rest, v => do
    match s with
    | .expr e => let x ← evalExpr n ctx e; evalCompletion n ctx rest x
    | _ =>
      match ← evalStmt n ctx [] s with
      | .normal => evalCompletion n ctx rest v
      | _ => pure v
termination_by structural n _ _ _ => n

/-- Run a generator's frames until it yields, returns or throws (§27.5.3.3
GeneratorResume). `input` is what the caller sent: a value for `next`, a
completion for `throw` and `return`. Answers the yielded value and the frames to
keep, or the return value. -/
def genRun : Nat → List GFrame → GInput → M GOut
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, frames, input => do
    tick
    match input with
    | .throwV v => genUnwind n frames (.throw v)
    | .retV v => genUnwind n frames (.ret v)
    | .send v =>
    match frames with
    | [] => pure (.done .undef)
    | f :: rest =>
      match f with
      | .resume ctx target =>
        let r ← tryCatch (do
            if let some (p, m) := target then bindPat n ctx p v m
            pure none)
          (fun a => pure (some a))
        match r with
        | some (.throw e) => genUnwind n rest (.throw e)
        | some a => throw a
        | none => genRun n rest (.send .undef)
      | .delegate ctx it target =>
        let r ← tryCatch (do
            let next ← getV n it "next"
            let res ← callV n next it #[v]
            if !res.isObj then throwErr .type "Iterator result is not an object"
            pure (Except.ok res))
          (fun a => pure (Except.error a))
        match r with
        | .error (.throw e) => genUnwind n rest (.throw e)
        | .error a => throw a
        | .ok res =>
          if toBool (← getV n res "done") then
            let x ← getV n res "value"
            genRun n (.resume ctx target :: rest) (.send x)
          else pure (.yielded (← getV n res "value") (f :: rest))
      | .pending c =>
        -- the finally block ended normally: go on with the completion it held
        genUnwind n rest c
      | .block _ [] => genRun n rest (.send .undef)
      | .block ctx (s :: ss) =>
        if !s.hasYield then
          let r ← tryCatch (do let c ← evalStmt n ctx [] s; pure (Except.ok c))
            (fun a => pure (Except.error a))
          match r with
          | .error (.throw e) => genUnwind n (.block ctx ss :: rest) (.throw e)
          | .error a => throw a
          | .ok .normal => genRun n (.block ctx ss :: rest) (.send .undef)
          | .ok (.ret x) => genUnwind n (.block ctx ss :: rest) (.ret x)
          | .ok (.brk l) => genUnwind n (.block ctx ss :: rest) (.brk l)
          | .ok (.cont l) => genUnwind n (.block ctx ss :: rest) (.cont l)
        else genEnter n ctx [] s (.block ctx ss :: rest)
      | .loopW ctx labels c body =>
        let t ← genEval n ctx c
        match t with
        | .error e => genUnwind n rest (.throw e)
        | .ok t =>
          if toBool t then genRun n (.block ctx [body] :: f :: rest) (.send .undef)
          else genRun n rest (.send .undef)
      | .loopDo ctx labels body c =>
        let t ← genEval n ctx c
        match t with
        | .error e => genUnwind n rest (.throw e)
        | .ok t =>
          if toBool t then genRun n (.block ctx [body] :: f :: rest) (.send .undef)
          else genRun n rest (.send .undef)
      | .loopFor ctx labels perIter test update body first =>
        let ctx ← if perIter.isEmpty then pure ctx else copyEnv n ctx perIter
        let r ← tryCatch (do
            if !first then
              if let some u := update then let _ ← evalExpr n ctx u
            match test with
            | some t => pure (Except.ok (toBool (← evalExpr n ctx t)))
            | none => pure (Except.ok true))
          (fun a => pure (Except.error a))
        match r with
        | .error (.throw e) => genUnwind n rest (.throw e)
        | .error a => throw a
        | .ok false => genRun n rest (.send .undef)
        | .ok true =>
          genRun n (.block ctx [body] :: .loopFor ctx labels perIter test update body false :: rest) (.send .undef)
      | .loopOf ctx labels kind target it body =>
        let r ← tryCatch (do pure (Except.ok (← iterStep n it))) (fun a => pure (Except.error a))
        match r with
        | .error (.throw e) => genUnwind n rest (.throw e)
        | .error a => throw a
        | .ok none => genRun n rest (.send .undef)
        | .ok (some x) =>
          let r ← tryCatch (do pure (Except.ok (← bindIter n ctx kind target x)))
            (fun a => pure (Except.error a))
          match r with
          | .error (.throw e) =>
            let _ ← tryCatch (iterClose n it) (fun _ => pure ())
            genUnwind n rest (.throw e)
          | .error a => throw a
          | .ok ctx' => genRun n (.block ctx' [body] :: f :: rest) (.send .undef)
      | .tryF ctx _ _ (some fs) _ =>
        let ctx' ← enterBlock n ctx fs
        genRun n (.block ctx' fs :: rest) (.send .undef)
      | .tryF .. => genRun n rest (.send .undef)
termination_by structural n _ _ => n

/-- Evaluate a `yield`-free expression, catching a thrown value. -/
def genEval : Nat → Ctx → Expr → M (Except Value Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e => do
    let r ← tryCatch (do pure (Except.ok (← evalExpr n ctx e))) (fun a => pure (Except.error a))
    match r with
    | .ok v => pure (.ok v)
    | .error (.throw v) => pure (.error v)
    | .error a => throw a
termination_by structural n _ _ => n

/-- Start a statement that holds a `yield`, on top of `rest`. -/
def genEnter : Nat → Ctx → List String → Stmt → List GFrame → M GOut
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, labels, s, rest => do
    let yieldAt (arg : Option Expr) (delegate : Bool) (target : Option (Pat × BindMode)) : M GOut := do
      let v ← match arg with
        | some e => genEval n ctx e
        | none => pure (.ok .undef)
      match v with
      | .error e => genUnwind n rest (.throw e)
      | .ok v =>
        if delegate then
          let r ← tryCatch (do pure (Except.ok (← getIterator n v))) (fun a => pure (Except.error a))
          match r with
          | .error (.throw e) => genUnwind n rest (.throw e)
          | .error a => throw a
          | .ok it => genRun n (.delegate ctx it target :: rest) (.send .undef)
        else pure (.yielded v (.resume ctx target :: rest))
    match s with
    | .expr (.yieldE d arg) => yieldAt arg d none
    | .expr (.assign none t (.yieldE d arg)) =>
      match t with
      | .ident x => yieldAt arg d (some (.id x, .assign))
      | .member .. | .index .. => yieldAt arg d (some (.target t, .assign))
      | _ => genUnsupported n rest
    | .decl k [Decl.mk p (some (.yieldE d arg))] =>
      let m : BindMode := match k with
        | .var => .var
        | .letK => .declare ctx.env true
        | .constK => .declare ctx.env false
      yieldAt arg d (some (p, m))
    | .ret (some (.yieldE d arg)) =>
      -- `return yield x`: the value sent back is the return value
      let _ := d
      let v ← match arg with
        | some e => genEval n ctx e
        | none => pure (.ok .undef)
      match v with
      | .error e => genUnwind n rest (.throw e)
      | .ok v => pure (.yielded v (.resume ctx (some (.id "%ret", .declare ctx.env true)) ::
          .block ctx [.ret (some (.ident "%ret"))] :: rest))
    | .block ss =>
      let ctx' ← enterBlock n ctx ss
      genRun n (.block ctx' ss :: rest) (.send .undef)
    | .ifS c t e =>
      if c.hasYield then genUnsupported n rest else
      match ← genEval n ctx c with
      | .error x => genUnwind n rest (.throw x)
      | .ok v =>
        if toBool v then genRun n (.block ctx [t] :: rest) (.send .undef)
        else match e with
          | some e => genRun n (.block ctx [e] :: rest) (.send .undef)
          | none => genRun n rest (.send .undef)
    | .whileS c body =>
      if c.hasYield then genUnsupported n rest
      else genRun n (.loopW ctx labels c body :: rest) (.send .undef)
    | .doWhile body c =>
      if c.hasYield then genUnsupported n rest
      else genRun n (.block ctx [body] :: .loopDo ctx labels body c :: rest) (.send .undef)
    | .forS init test update body =>
      let ok := !(test.any Expr.hasYield) && !(update.any Expr.hasYield) &&
        (match init with | some (.expr e) => !e.hasYield | some (.decl _ ds) => !(ds.any Decl.hasYield) | none => true)
      if !ok then genUnsupported n rest else
      let r ← tryCatch (do
          match init with
          | some (.decl .var ds) => evalDecls n ctx .var ds; pure (Except.ok (ctx, ([] : List String)))
          | some (.decl k ds) =>
            let env ← newEnv (some ctx.env)
            let ctx' := { ctx with env }
            for d in ds do
              for x in d.names do declare env x { v := .undef, mutable := k == .letK, init := false }
            evalDecls n ctx' k ds
            pure (Except.ok (ctx', if k == .letK then ds.flatMap Decl.names else []))
          | some (.expr e) => let _ ← evalExpr n ctx e; pure (Except.ok (ctx, []))
          | none => pure (Except.ok (ctx, [])))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw x) => genUnwind n rest (.throw x)
      | .error a => throw a
      | .ok (ctx', perIter) => genRun n (.loopFor ctx' labels perIter test update body true :: rest) (.send .undef)
    | .forOf kind target obj body =>
      if obj.hasYield then genUnsupported n rest else
      let r ← tryCatch (do pure (Except.ok (← getIterator n (← evalExpr n ctx obj))))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw x) => genUnwind n rest (.throw x)
      | .error a => throw a
      | .ok it => genRun n (.loopOf ctx labels kind target it body :: rest) (.send .undef)
    | .tryS body param handler fin =>
      let ctx' ← enterBlock n ctx body
      genRun n (.block ctx' body :: .tryF ctx param handler fin 0 :: rest) (.send .undef)
    | .labeled l body => genEnter n ctx (l :: labels) body rest
    | _ => genUnsupported n rest
termination_by structural n _ _ _ _ => n

def genUnsupported : Nat → List GFrame → M GOut
  | 0, _ => throw (.halt "fuel")
  | n + 1, rest => do
    genUnwind n rest (.throw (← mkError .syntax "yield in this position is not supported"))
termination_by structural n _ => n

/-- Unwind the frames with an abrupt completion: loops take their `break` and
`continue`, `try` takes a throw, `finally` runs, `for`-`of` closes its iterator. -/
def genUnwind : Nat → List GFrame → GCompl → M GOut
  | 0, _, _ => throw (.halt "fuel")
  | _ + 1, [], c =>
    match c with
    | .ret v => pure (.done v)
    | .throw v => throw (.throw v)
    | _ => pure (.done .undef)
  | n + 1, f :: rest, c => do
    match f, c with
    | .loopW _ labels _ _, .brk l | .loopDo _ labels _ _, .brk l | .loopFor _ labels _ _ _ _ _, .brk l =>
      if l.isNone || labels.contains (l.getD "") then genRun n rest (.send .undef)
      else genUnwind n rest c
    | .loopW _ labels _ _, .cont l | .loopDo _ labels _ _, .cont l | .loopFor _ labels _ _ _ _ _, .cont l =>
      if l.isNone || labels.contains (l.getD "") then genRun n (f :: rest) (.send .undef)
      else genUnwind n rest c
    | .loopOf _ labels _ _ it _, .brk l =>
      if l.isNone || labels.contains (l.getD "") then
        iterClose n it; genRun n rest (.send .undef)
      else iterClose n it; genUnwind n rest c
    | .loopOf _ labels _ _ it _, .cont l =>
      if l.isNone || labels.contains (l.getD "") then genRun n (f :: rest) (.send .undef)
      else iterClose n it; genUnwind n rest c
    | .loopOf _ _ _ _ it _, .ret _ => iterClose n it; genUnwind n rest c
    | .loopOf _ _ _ _ it _, .throw _ =>
      let _ ← tryCatch (iterClose n it) (fun _ => pure ())
      genUnwind n rest c
    | .delegate _ it _, .throw v =>
      let th ← getV n it "throw"
      match th with
      | .undef | .null =>
        let _ ← tryCatch (iterClose n it) (fun _ => pure ())
        genUnwind n rest (.throw (← mkError .type "The iterator does not provide a 'throw' method"))
      | _ =>
        let res ← callV n th it #[v]
        if !res.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n res "done") then genRun n rest (.send (← getV n res "value"))
        else pure (.yielded (← getV n res "value") (f :: rest))
    | .delegate _ it _, .ret v =>
      let rt ← getV n it "return"
      match rt with
      | .undef | .null => genUnwind n rest c
      | _ =>
        let res ← callV n rt it #[v]
        if !res.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n res "done") then genUnwind n rest (.ret (← getV n res "value"))
        else pure (.yielded (← getV n res "value") (f :: rest))
    | .tryF ctx param (some hs) fin 0, .throw v =>
      let env ← newEnv (some ctx.env)
      let ctx' := { ctx with env }
      let r ← tryCatch (do
          if let some p := param then
            for x in p.names do declare env x { v := .undef, init := false }
            bindPat n ctx' p v (.declare env true)
          pure none)
        (fun a => pure (some a))
      match r with
      | some (.throw e) => genUnwind n (.tryF ctx param none fin 1 :: rest) (.throw e)
      | some a => throw a
      | none =>
        let ctx'' ← enterBlock n ctx' hs
        genRun n (.block ctx'' hs :: .tryF ctx param (some hs) fin 1 :: rest) (.send .undef)
    | .tryF ctx _ _ (some fs) _, _ =>
      let ctx' ← enterBlock n ctx fs
      genRun n (.block ctx' fs :: .pending c :: rest) (.send .undef)
    | _, _ => genUnwind n rest c
termination_by structural n _ _ => n

/-- Built-in functions. `newTarget` is set for `new`. -/
def callNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args, newTarget => do
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    let id_ := id
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
      let ks := o.ownStrKeys.filter fun k => match o.getOwn k with
        | some p => p.enumerable | none => false
      newArray (ks.map .str)
    | .objectGetOwnPropertyNames =>
      let id ← toObj n a0
      newArray ((← getObj id).ownStrKeys.map .str)
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
        let custom ← getV n (.obj id) (symKey symToStringTag)
        let builtin := match (← getObj id).kind with
          | .array _ => "Array"
          | .closure .. | .native _ | .bound .. => "Function"
          | .error => "Error"
          | .args => "Arguments"
          | .prim (.bool _) => "Boolean"
          | .prim (.num _) => "Number"
          | .prim (.str _) => "String"
          | _ => "Object"
        let tag := match custom with | .str t => t | _ => builtin
        pure (.str s!"[object {tag}]")
    | .objectProtoToLocaleString => callV n (← getV n thisV "toString") thisV #[]
    | .objectProtoValueOf => pure (.obj (← toObj n thisV))
    | .functionCtor =>
      let strs ← args.toList.mapM (toStr n)
      let (ps, body) := match strs.reverse with
        | [] => ([], "")
        | b :: rest => (rest.reverse, b)
      let src := "(function anonymous(" ++ ",".intercalate ps ++ "\n) {\n" ++ body ++ "\n})"
      match parseScript src false with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok { body := [.expr e], .. } =>
        evalExpr n { env := 0, thisV := .obj r.globalObj, strict := false } e
      | .ok _ => throwErr .syntax "invalid function body"
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
      let s ← match a0, newTarget with
        | .sym id, none => pure ("Symbol(" ++ (← get).syms.getD id "" ++ ")")
        | _, _ => if args.isEmpty then pure "" else toStr n a0
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
    | .eval =>
      match a0 with
      | .str _ => directEval n { env := 0, thisV := .obj r.globalObj, strict := false } a0
      | v => pure v
    | .symbolCtor =>
      if newTarget.isSome then throwErr .type "Symbol is not a constructor"
      let d ← match a0 with | .undef => pure "" | v => toStr n v
      let id ← modifyGet fun h => (h.syms.size, { h with syms := h.syms.push d })
      pure (.sym id)
    | .symbolToString | .symbolDescription | .symbolValueOf =>
      let v ← thisPrim thisV
      match v with
      | .sym id =>
        let d := (← get).syms.getD id ""
        match id_ with
        | .symbolToString => pure (.str ("Symbol(" ++ d ++ ")"))
        | .symbolDescription => pure (.str d)
        | _ => pure v
      | _ => throwErr .type "Symbol.prototype method requires that 'this' be a Symbol"
    | .objectGetOwnPropertySymbols =>
      let id ← toObj n a0
      let ks := (← getObj id).ownKeys.filter isSymKey
      newArray (ks.filterMap fun k => (symOfKey? k).map .sym)
    | .objectAssign =>
      let tid ← toObj n a0
      for src in args.extract 1 args.size do
        match src with
        | .undef | .null => pure ()
        | _ =>
          let sid ← toObj n src
          for k in (← getObj sid).ownKeys do
            match (← getObj sid).getOwn k with
            | some p => if p.enumerable then putV n (.obj tid) k (← getV n (.obj sid) k) true
            | none => pure ()
      pure (.obj tid)
    | .objectEntries | .objectValues =>
      let id ← toObj n a0
      let o ← getObj id
      let ks := o.ownStrKeys.filter fun k => match o.getOwn k with | some p => p.enumerable | none => false
      let vs ← ks.mapM fun k => do
        let v ← getV n (.obj id) k
        if id_ == .objectEntries then newArray #[.str k, v] else pure v
      newArray vs
    | .arrayValues | .arrayKeys | .arrayEntries =>
      let o ← toObj n thisV
      let mode := match id_ with | .arrayKeys => 1 | .arrayEntries => 2 | _ => 0
      pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter (.obj o) 0 mode }))
    | .stringIterator =>
      match thisV with
      | .undef | .null => throwErr .type "String.prototype[Symbol.iterator] called on null or undefined"
      | _ =>
        let s ← toStr n thisV
        pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter (.str s) 0 3 }))
    | .iterNext =>
      let id ← match thisV with
        | .obj id => pure id
        | _ => throwErr .type "next method called on incompatible receiver"
      match (← getObj id).kind with
      | .iter target idx mode =>
        let result (v : Value) (done : Bool) : M Value := do
          let o ← newObject
          defineOwn o "value" (.data v true true true)
          defineOwn o "done" (.data (.bool done) true true true)
          pure (.obj o)
        match target with
        | .undef => result .undef true
        | .str s =>
          let cs := charsOf s
          if idx < cs.size then
            modifyObj id fun o => { o with kind := .iter target (idx + 1) mode }
            result (.str (String.singleton cs[idx]!)) false
          else
            modifyObj id fun o => { o with kind := .iter .undef idx mode }
            result .undef true
        | _ =>
          let len ← match target with
            | .obj tid => match (← getObj tid).kind with
              | .array es => pure es.size
              | _ => do pure (toIntegerOrInf (← toNum n (← getV n target "length"))).toUInt64.toNat
            | _ => pure 0
          if idx < len then
            modifyObj id fun o => { o with kind := .iter target (idx + 1) mode }
            match mode with
            | 1 => result (.num (Float.ofNat idx)) false
            | 2 =>
              let v ← getV n target (toString idx)
              result (← newArray #[.num (Float.ofNat idx), v]) false
            | _ => result (← getV n target (toString idx)) false
          else
            modifyObj id fun o => { o with kind := .iter .undef idx mode }
            result .undef true
      | _ => throwErr .type "next method called on incompatible receiver"
    | .iterSelf => pure thisV
    | .arrayFrom =>
      let mapFn := a1
      let usingIter ← match a0 with
        | .undef | .null => throwErr .type "Array.from requires an array-like or iterable"
        | _ => getV n a0 (symKey symIterator)
      let vs ← match usingIter with
        | .undef | .null => elemsOf n a0
        | _ => do iterToArray n (← getIterator n a0) #[]
      let vs ← match mapFn with
        | .undef => pure vs
        | f => (List.range vs.size).toArray.mapM fun i => callV n f (argD args 2) #[vs[i]!, .num (Float.ofNat i)]
      newArray vs
    | .arrayOf => newArray args
    | .dateNow => pure (.num 0)
    | .bigintCtor =>
      if newTarget.isSome then throwErr .type "BigInt is not a constructor"
      match ← toPrim n a0 "number" with
      | .num x =>
        if !isIntegral x then throwErr .range s!"The number {numToString x} cannot be converted to a BigInt because it is not an integer"
        pure (.big (truncInt x))
      | .str t => match strToBigInt t with
        | some i => pure (.big i)
        | none => throwErr .syntax s!"Cannot convert {t} to a BigInt"
      | .bool b => pure (.big (if b then 1 else 0))
      | .big i => pure (.big i)
      | _ => throwErr .type "Cannot convert value to a BigInt"
    | .bigintToString | .bigintValueOf =>
      match ← thisPrim thisV with
      | .big i =>
        if id_ == .bigintValueOf then pure (.big i) else
        let radix ← match a0 with | .undef => pure 10 | v => do pure (toIntegerOrInf (← toNum n v))
        if radix < 2 || radix > 36 then throwErr .range "toString() radix must be between 2 and 36"
        let ds := Nat.toDigits radix.toUInt64.toNat i.natAbs
        pure (.str ((if i < 0 then "-" else "") ++ String.ofList ds))
      | _ => throwErr .type "BigInt.prototype method requires that 'this' be a BigInt"
    | .genNext | .genReturn | .genThrow =>
      let gid ← match thisV with
        | .obj g => pure g
        | _ => throwErr .type "next method called on incompatible receiver"
      match (← getObj gid).kind with
      | .gen frames st =>
        let result (v : Value) (done : Bool) : M Value := do
          let o ← newObject
          defineOwn o "value" (.data v true true true)
          defineOwn o "done" (.data (.bool done) true true true)
          pure (.obj o)
        if st == 2 then throwErr .type "Generator is already running"
        let setG (fs : List GFrame) (s : Nat) : M Unit :=
          modifyObj gid fun o => { o with kind := .gen fs s }
        if st == 3 || (st == 0 && id_ != .genNext) then
          setG [] 3
          match id_ with
          | .genNext => result .undef true
          | .genReturn => result a0 true
          | _ => throw (.throw a0)
        else
          setG frames 2
          let input := match id_ with
            | .genNext => GInput.send a0
            | .genReturn => .retV a0
            | _ => .throwV a0
          let r ← tryCatch (do pure (Except.ok (← genRun n frames input)))
            (fun a => pure (Except.error a))
          match r with
          | .error a => setG [] 3; throw a
          | .ok (.yielded v fs) => setG fs 1; result v false
          | .ok (.done v) => setG [] 3; result v true
      | _ => throwErr .type "next method called on incompatible receiver"
    | _ =>
      -- string methods and Math
      stringOrMath n id thisV args
termination_by structural n _ _ _ _ => n

def genericPush : Nat → Value → Array Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, thisV, args => do
    let len ← toNum n (← getV n thisV "length")
    let l := (toIntegerOrInf len).toUInt64.toNat
    for i in [0:args.size] do putV n thisV (toString (l + i)) args[i]! true
    putV n thisV "length" (.num (Float.ofNat (l + args.size))) true
    pure (.num (Float.ofNat (l + args.size)))
termination_by structural n _ _ => n

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
termination_by structural n _ => n

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
termination_by structural n _ _ _ _ _ _ _ => n

def reduceArray : Nat → Value → Value → Array Value → Nat → Value → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, f, arr, es, i, acc => do
    if h : i < es.size then
      let acc ← callV n f .undef #[acc, es[i], .num (Float.ofNat i), arr]
      reduceArray n f arr es (i + 1) acc
    else pure acc
termination_by structural n _ _ _ _ _ => n

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
termination_by structural n _ _ _ => n

def mergeSort : Nat → Value → List Value → M (List Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, cmp, xs => do
    if xs.length ≤ 1 then return xs
    let k := xs.length / 2
    let l ← mergeSort n cmp (xs.take k)
    let r ← mergeSort n cmp (xs.drop k)
    merge n cmp l r #[]
termination_by structural n _ _ => n

def merge : Nat → Value → List Value → List Value → Array Value → M (List Value)
  | 0, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], r, acc => pure (acc.toList ++ r)
  | _ + 1, _, l, [], acc => pure (acc.toList ++ l)
  | n + 1, cmp, a :: as, b :: bs, acc => do
    if ← sortGt n cmp a b then merge n cmp (a :: as) bs (acc.push b)
    else merge n cmp as (b :: bs) (acc.push a)
termination_by structural n _ _ _ _ => n

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
termination_by structural n _ _ _ => n

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
    | .sym _ => pure .undef
    | .big _ => throwErr .type "Do not know how to serialize a BigInt"
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
        let ks := o.ownStrKeys.filter fun k => match o.getOwn k with | some p => p.enumerable | none => false
        let parts ← ks.toList.filterMapM fun k => do
          match ← jsonStr n (← getV n v k) (depth + 1) with
          | .str s => pure (some (quote k ++ ":" ++ s))
          | _ => pure none
        pure (.str ("{" ++ ",".intercalate parts ++ "}"))
termination_by structural n _ _ => n

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
termination_by structural n _ _ _ => n

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
  let symbolProto ← mk
  let iterProto ← mk
  let arrayIterProto ← alloc { proto := .obj iterProto }
  let rl : Realm :=
    { globalObj := gl, objectProto := objectProto, functionProto := functionProto,
      arrayProto := arrayProto, stringProto := stringProto, numberProto := numberProto,
      booleanProto := booleanProto, errorProtos := errorProtos, symbolProto := symbolProto,
      iterProto := iterProto, arrayIterProto := arrayIterProto }
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
  -- eval, Symbol, iterators, Date.now
  let ev ← mkNative .eval "eval" 1
  setHidden g "eval" ev
  if let .obj e := ev then modify fun h => { h with realm := { h.realm with evalFn := e } }
  let symC ← ctorWith "Symbol" .symbolCtor 0 symbolProto
  setHidden g "Symbol" symC
  if let .obj sc := symC then
    for i in [0:wellKnown.size] do
      defineOwn sc (wellKnown[i]!) (.data (.sym i) false false false)
  method symbolProto "toString" .symbolToString 0
  method symbolProto "valueOf" .symbolValueOf 0
  defineOwn symbolProto "description" (.acc (← mkNative .symbolDescription "get description" 0) .undef false true)
  defineOwn symbolProto (symKey symToStringTag) (.data (.str "Symbol") false false true)
  setHidden iterProto (symKey symIterator) (← mkNative .iterSelf "[Symbol.iterator]" 0)
  method arrayIterProto "next" .iterNext 0
  let genProto ← alloc { proto := .obj iterProto }
  modify fun h => { h with realm := { h.realm with generatorProto := genProto } }
  method genProto "next" .genNext 1
  method genProto "return" .genReturn 1
  method genProto "throw" .genThrow 1
  defineOwn genProto (symKey symToStringTag) (.data (.str "Generator") false false true)
  defineOwn arrayIterProto (symKey symToStringTag) (.data (.str "Array Iterator") false false true)
  let values ← mkNative .arrayValues "values" 0
  setHidden arrayProto "values" values
  setHidden arrayProto (symKey symIterator) values
  method arrayProto "keys" .arrayKeys 0
  method arrayProto "entries" .arrayEntries 0
  setHidden stringProto (symKey symIterator) (← mkNative .stringIterator "[Symbol.iterator]" 0)
  if let .obj ac := arrayC then
    method ac "from" .arrayFrom 1
    method ac "of" .arrayOf 0
  if let .obj oc := objectC then
    method oc "getOwnPropertySymbols" .objectGetOwnPropertySymbols 1
    method oc "assign" .objectAssign 2
    method oc "entries" .objectEntries 1
    method oc "values" .objectValues 1
  let bigintProto ← mk
  modify fun h => { h with realm := { h.realm with bigintProto := bigintProto } }
  setHidden g "BigInt" (← ctorWith "BigInt" .bigintCtor 1 bigintProto)
  method bigintProto "toString" .bigintToString 0
  method bigintProto "valueOf" .bigintValueOf 0
  defineOwn bigintProto (symKey symToStringTag) (.data (.str "BigInt") false false true)
  let date ← mk
  setHidden g "Date" (.obj date)
  method date "now" .dateNow 0

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
        for x in d.names do
          if ((← getBinding 0 x)).isSome then throwErr .syntax s!"Identifier '{x}' has already been declared"
          declare 0 x { v := .undef, mutable := (match st with | .decl .letK _ => true | _ => false), init := false }
    | .classDecl x _ =>
      if ((← getBinding 0 x)).isSome then throwErr .syntax s!"Identifier '{x}' has already been declared"
      declare 0 x { v := .undef, init := false }
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
