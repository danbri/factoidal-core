import L4Factoidal.JS.Value
import L4Factoidal.JS.Clone
import L4Factoidal.JS.Parser
import L4Factoidal.JS.Resolve
import L4Factoidal.JS.Date
import L4Factoidal.JS.NumFmt
import L4Factoidal.JSON.Parser
import L4Factoidal.JS.JsonText
import L4Factoidal.WHATWG.URLPattern
import L4Factoidal.Prim.Float16

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

set_option maxHeartbeats 8000000

namespace L4Factoidal.JS

variable {H : Type}
-- The evaluator's monad over the heap of host `H` (`JSM H`).
set_option hygiene false in
local notation "M" => JSM H

/-! ## Heap primitives -/

@[inline] def alloc (o : Obj) : M Nat := modifyGet fun h => (h.objs.size, { h with objs := h.objs.push o })
@[inline] def getObj (id : Nat) : M Obj := do pure ((← get).obj id)
@[inline] def modifyObj (id : Nat) (f : Obj → Obj) : M Unit :=
  -- the object array is taken out of the heap first, and `Array.modify` moves the object
  -- out of the array for `f`: both are changed in place when nothing else holds them
  modify fun h =>
    let objs := h.objs
    let h := { h with objs := #[] }
    { h with objs := objs.modify id f }

/-- Object `id` and the array with a placeholder in its place. Not inlined: the compiler
must not move the write of the placeholder after the uses of the object, or the object
would still be shared with the array while it changes (and its elements copied). -/
@[noinline] def takeAt (objs : Array Obj) (id : Nat) : Obj × Array Obj :=
  objs.swapAt! id default

/-- Change object `id` with `f`, which also answers a value. The object is moved out of the
heap while `f` runs, so `f` holds the only reference and a change to its elements does not
copy them (an Array push is amortised constant time, not a copy of the array). -/
def updateObj {α} [Inhabited α] (id : Nat) (f : Obj → α × Obj) : M α :=
  modifyGet fun h =>
    let objs := h.objs
    let h := { h with objs := #[] }
    if id < objs.size then
      let (o, objs) := takeAt objs id
      let (a, o) := f o
      (a, { h with objs := objs.set! id o })
    else (default, { h with objs })

/-- The elements of an Array object, taken out of it: the object is left with no elements
(`Kind.ordinary`) so the elements are the only reference. -/
def Obj.takeArray (o : Obj) : Option (Array Value) × Obj :=
  match o.kind with
  | .array es => let o := { o with kind := .ordinary }; (some es, o)
  | _ => (none, o)
/-- Write element `i` of the Array object `id`, in place, when the object is an Array and `i`
is below its length (no attribute can stand in the way there: elements are always writable,
`Obj.getOwn`); `false` otherwise (the caller takes the general path). -/
def setElem (id i : Nat) (v : Value) : M Bool :=
  updateObj id fun o =>
    match o.kind with
    | .array es =>
      if h : i < es.size then
        let o := { o with kind := .ordinary }
        (true, { o with kind := .array (es.set i v) })
      else (false, o)
    | _ => (false, o)

/-- Overwrite an own writable data property of a non-exotic object, in place; `false` when
the property is absent or not plain (the caller takes the general path). -/
def setOwnData (id : Nat) (key : String) (v : Value) : M Bool :=
  updateObj id fun o =>
    match o.kind with
    | .array _ | .proxy .. | .typed .. | .prim _ => (false, o)
    | _ =>
      match o.props.get? key with
      | some (.data _ true e c) =>
        (true, { o with props := o.props.insert key (.data v true e c) })
      | _ => (false, o)

@[inline] def realm : M Realm := do pure (← get).realm

/-- Put an environment record in a free slot of the environment array. -/
@[inline] def pushEnv (en : Env) : M Nat :=
  modifyGet fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    match h.envFree.back? with
    | some e => (e, { h with envFree := h.envFree.pop, envs := envs.set! e en })
    | none => (envs.size, { h with envs := envs.push en })

@[inline] def newEnv (parent : Nat) : M Nat := pushEnv { parent }

/-- Environment `e` is not reachable any more: drop its contents and reuse its slot. -/
@[inline] def releaseEnv (e : Nat) : M Unit :=
  modify fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    { h with envs := envs.set! e default, envFree := h.envFree.push e }

/-- Change an environment in place: the array and the record are taken out while `f` runs. -/
@[inline] def modifyEnv (e : Nat) (f : Env → Env) : M Unit :=
  modify fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    { h with envs := envs.modify e f }

@[inline] def declare (env : Nat) (name : String) (b : Binding) : M Unit :=
  modifyEnv env (·.put name b)

def getBinding (env : Nat) (name : String) : M (Option Binding) := do
  pure (((← get).envs.getD env default).get? name)

/-- Check every resolved name against the plain lookup (`JS/Tests.lean` sets it through
`verifyLocalsDefault`; off in the engine). -/
def verifyLocals : Bool := false

/-- Set a slot, in place. -/
@[inline] def setSlot (e i : Nat) (v : Value) : M Unit :=
  modifyEnv e fun en => { en with vals := en.vals.set! i v }

/-- The slots of a call with plain parameters: the arguments array, cut to the parameters and
filled with `undefined` to the size of the layout. -/
def fillSlots (args : Array Value) (nParams size : Nat) : Array Value :=
  let a := if args.size > nParams then args.shrink nParams else args
  if a.size == size then a else
  (List.range (size - a.size)).foldl (fun a _ => a.push .undef) a

/-- What a script is stopped with when its heap is full (`HeapOf.full`). -/
def heapFullMsg : String := "memory limit: the script's heap is full"

/-- One step. Every 1024th step also looks at the size of the heap (`HeapOf.full`), so a loop
that makes objects stops at `maxObjs` and not when the machine is out of memory. -/
@[inline] def tick : M Unit := do
  let h ← get
  if h.steps == 0 then throw (.halt "step budget exhausted")
  if h.steps % 1024 == 0 && h.full then throw (.halt heapFullMsg)
  set { h with steps := h.steps - 1 }

/-- The step of a function call. It looks at the size of the heap every time: a run of few
steps (an event handler, a timer callback) starts with a call, so on a full heap no run gets
further than its first call, however short the runs are. -/
@[inline] def tickCall : M Unit := do
  let h ← get
  if h.steps == 0 then throw (.halt "step budget exhausted")
  if h.full then throw (.halt heapFullMsg)
  set { h with steps := h.steps - 1 }

/-- Take `k` steps at once: the work of a built-in that loops inside Lean (over a string,
an array or a buffer) is counted, so a script stops at its budget however it spends it. -/
def charge (k : Nat) : M Unit := do
  if k == 0 then return
  let h ← get
  let k := k.toUInt64
  if h.steps < k then
    set { h with steps := 0 }
    throw (.halt "step budget exhausted")
  if h.full then throw (.halt heapFullMsg)
  set { h with steps := h.steps - k }

/-- The longest string `repeat` and `padStart` make: 256 MiB of UTF-8. -/
def maxStringBytes : Nat := 268435456

/-- The most elements `new Array(n)` and an assignment to an array's `length` make at once:
2^25 (256 MiB of values). Arrays are dense here (an array of `n` elements holds `n` values), so
`a.length = 4294967295` would ask for 32 GiB: the engine's process was killed for it (Test262
`harness/propertyhelper-verifywritable-array-length`, 2026-11-14). Past the limit the script gets
a RangeError; ECMA-262 allows the length (a sparse array). The growth also takes steps. -/
def maxDenseArray : Nat := 33554432

/-- Strings shorter than this many bytes are not kept by `cachedChars`: decoding one costs
less than a step. -/
def cachedCharsMin : Nat := 256

/-- The UTF-16 units of `s` as characters, kept for the last string of `cachedCharsMin` bytes
or more: repeated matches on one string (`exec` in a loop, `replace` with a global regexp) do
not decode it each time. -/
def cachedChars (s : String) : M (Array Char) := do
  -- A short string is decoded each time and leaves the kept string in place: a tokeniser that
  -- tests one character between two sticky matches on its long input (WPT's webidl2.js) does
  -- not decode the input again for every token.
  if s.utf8ByteSize < cachedCharsMin then return Str.unitChars s
  match (← get).reCache with
  | some (t, cs) => if t == s then return cs else pure ()
  | none => pure ()
  let cs := Str.unitChars s
  modify fun h => { h with reCache := some (s, cs) }
  return cs

/-- The steps a value's size is worth to a built-in that walks it: a step for every 64
bytes of a string, 64 elements of an array, or 4096 bytes of an ArrayBuffer or typed
array (copied or compared at memory speed). -/
def sizeCost (v : Value) : M Nat := do
  match v with
  | .str s => pure (s.utf8ByteSize / 64)
  | .obj id => match (← getObj id).kind with
    | .array es => pure (es.size / 64)
    | .buffer b => pure (b.size / 4096)
    | .typed _ _ _ len => pure (len / 4096)
    | _ => pure 0
  | _ => pure 0

/-- `charAt` and `charCodeAt` on a string that is not ASCII, when it is the string whose units
`cachedChars` holds: they index those units, and the only walk is the comparison with the cached
string (memory speed, a step for each 4096 bytes). A loop over a string's units (the WPT
`wasm/core` harness turns each module's bytes into an ArrayBuffer this way) is then linear, where
it was a walk of the string per unit (a 20 KB module took the 5 M steps of a run). -/
def cachedReceiverCost (id : Native) (thisV : Value) : M (Option Nat) := do
  match thisV with
  | .str s =>
    if !(id == .stringCharAt || id == .stringCharCodeAt) then return none
    match (← get).reCache with
    | some (t, _) => pure (if t == s then some (s.utf8ByteSize / 4096) else none)
    | none => pure none
  | _ => pure none

/-- The built-ins that do not walk their receiver: String methods on an ASCII string index it
in constant time (`Str.unitAt?`) or copy only their result (and take steps for that), and
`startsWith` and `endsWith` read only the units they compare (`unitsAt`; the search string's
size is counted as an argument); an Array's `push`, `pop` and `at`. -/
def indexesReceiver (id : Native) (thisV : Value) : Bool :=
  match thisV with
  | .str s =>
    Str.isAscii s && match id with
      | .stringCharAt | .stringCharCodeAt | .stringAt | .stringCodePointAt | .stringSlice
      | .stringSubstring | .stringSubstr | .stringStartsWith | .stringEndsWith => true
      | _ => false
  -- an Array's push, pop and at change or read one end in place (`updateObj`)
  | .obj _ => match id with
    | .arrayPush | .arrayPop | .arrayAt => true
    | _ => false
  | _ => false

/-- `RegExp.prototype.exec` and `test` on the string whose code units `cachedChars` holds: they
do not walk it again and take steps for the distance matched (`regexExec`), so the size of
the subject is not charged again on each call. -/
def subjectCached (id : Native) (args : Array Value) : M Bool := do
  match id, (args[0]? : Option Value) with
  | .regexpExec, some (Value.str s) | .regexpTest, some (Value.str s) =>
    match (← get).reCache with
    | some (t, _) => pure (t == s)
    | none => pure false
  | _, _ => pure false

/-- Set or add an own data property with all attributes true (CreateDataProperty). -/
def Obj.putOwn (o : Obj) (key : String) (p : PropV) : Obj :=
  match o.kind, arrayIndex? key, p with
  | .array _, some i, .data v _ _ _ =>
    -- the elements leave the object first, so `set!` and `push` change them in place
    let (es, o) := o.takeArray
    let es := es.getD #[]
    if i < es.size then { o with kind := .array (es.set! i v) }
    else if i == es.size then { o with kind := .array (es.push v) }
    else if i < es.size + 100000 then
      { o with kind := .array ((es ++ Array.replicate (i - es.size) Value.undef).push v) }
    else
      let known := o.props.contains key
      { o with kind := .array es, props := o.props.insert key p,
               keys := if known then o.keys else o.keys.push key }
  | _, _, _ =>
    -- `known` is computed first: `insert` must hold the only reference to the table
    let known := o.props.contains key
    { o with props := o.props.insert key p, keys := if known then o.keys else o.keys.push key }

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
    | _, _ =>
      -- the key stays in `keys` for now (`Obj.liveKeys`); `keys` is rebuilt when mostly stale
      let o := { o with props := o.props.erase key }
      if o.keys.size > 2 * o.props.size + 16 then { o with keys := o.liveKeys } else o

def mkError (k : ErrKind) (msg : String) : M Value := do
  let r ← realm
  let id ← alloc { proto := .obj (r.errorProtos.getD k.idx r.objectProto), kind := .error }
  setHidden id "message" (.str msg)
  pure (.obj id)

def throwErr {α} (k : ErrKind) (msg : String) : M α := do
  throw (.throw (← mkError k msg))

/-- `s` repeated `n` times, by doubling: about log₂ n appends and no list of `n` parts
(`"a".repeat(2 ** 28)` as a list of parts took gigabytes before the string was made). -/
def repeatStr (s : String) (n : Nat) : String :=
  let rec go : Nat → Nat → String → String → String
    | 0, _, _, acc => acc
    | fuel + 1, k, cur, acc =>
      if k == 0 then acc
      else go fuel (k / 2) (if k / 2 == 0 then cur else cur ++ cur) (if k % 2 == 1 then acc ++ cur else acc)
  go 64 n s ""

/-- A string of `bytes` bytes may be made: at most `maxStringBytes`, else a RangeError
("Invalid string length", as engines answer for a string past their limit). Every place that
makes a string from parts asks first, so no script makes the engine allocate past it:
`s += s` in a loop, `join`, `concat`, a template, `replace` with `$&` (Test262
`staging/sm/String/replace-math` asks for 2^36 units and took the process with it). -/
@[inline] def checkStrLen (bytes : Nat) : M Unit :=
  if bytes > maxStringBytes then throwErr .range "Invalid string length" else pure ()

def newObject : M Nat := do alloc { proto := .obj (← realm).objectProto }

def newArray (es : Array Value) : M Value := do
  pure (.obj (← alloc { proto := .obj (← realm).arrayProto, kind := .array es }))

/-- Whether an object of this kind has a [[Construct]] method of its own (IsConstructor,
§7.2.4, for the kinds that are not a Proxy). -/
def Kind.constructs : Kind → Bool
  | .closure f .. => f.kind != .arrow && f.kind != .method && !f.gen && !f.async
  | .native nid => match nid with
    | .objectCtor | .functionCtor | .arrayCtor | .stringCtor | .numberCtor | .booleanCtor
    | .errorCtor _ | .symbolCtor | .promiseCtor | .mapCtor _ | .regexpCtor | .proxyCtor
    | .bufferCtor | .typedCtor _ | .dateCtor | .dataViewCtor => true
    | (.x .sharedCtor) | (.x .typedArrayCtor) | (.x .iteratorCtor) | (.x .aggregateErrorCtor) => true
    | (.x .weakRefCtor) | (.x .finRegCtor) | (.x (.dynFunction _)) => true
    | _ => false
  | .bound .. => true
  | _ => false

/-- IsConstructor (§7.2.4). A Proxy is a constructor when its target is (ProxyCreate,
§10.5.15 step 7b); a Proxy whose target is a Proxy is not followed (it answers false). -/
def isConstructor (v : Value) : M Bool := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .proxy (.obj t) _ => pure (← getObj t).kind.constructs
    | k => pure k.constructs
  | _ => pure false

@[inline] def isCallable (v : Value) : M Bool := do
  match v with
  | .obj id => pure (← getObj id).kind.callable
  | _ => pure false

def typeOf (v : Value) : M String := do
  match v with
  | .hole | .fl => pure "undefined"
  | .undef => pure "undefined"
  | .null => pure "object"
  | .bool _ => pure "boolean"
  | .num _ => pure "number"
  | .str _ => pure "string"
  | .sym _ => pure "symbol"
  | .big _ => pure "bigint"
  | .obj id => pure (typeOfKind (← getObj id).kind)

/-- The source text CreateDynamicFunction (§20.2.1.1.1 steps 13 to 16) parses: `kw` is
`function`, `function*`, `async function` or `async function*`. -/
def dynFunctionSource (kw : String) (ps : List String) (body : String) : String :=
  "(" ++ kw ++ " anonymous(" ++ ",".intercalate ps ++ "\n) {\n" ++ body ++ "\n})"

/-- A function object for a native, with `name` and `length`. -/
def mkNative (id : Native) (name : String) (len : Nat) : M Value := do
  let r ← realm
  let o ← alloc { proto := .obj r.functionProto, kind := .native id }
  defineOwn o "length" (.data (.num (Float.ofNat len)) false false true)
  defineOwn o "name" (.data (.str name) false false true)
  pure (.obj o)

def method (target : Nat) (name : String) (id : Native) (len : Nat) : M Unit := do
  setHidden target name (← mkNative id name len)

/-- OrdinaryFunctionCreate and MakeConstructor (§10.2.3, §10.2.5). `decl`: the closure of a
function declaration. Its name is a binding of the scope that has the declaration (§10.2.11,
§16.1.7), so it gets no scope of its own for the name: `function f() { f = 1 }` changes that
binding. -/
def makeClosure (ctx : Ctx) (f : FunDef) (nameHint : String := "") (home : Value := .undef)
    (decl : Bool := false) : M Value := do
  let r ← realm
  -- a named function expression sees its own name (§15.2.5)
  let env ← match f.name with
    | some _ => if f.arrow || decl then pure ctx.env else do
        let e ← newEnv ctx.env; pure e
    | none => pure ctx.env
  let home := if f.arrow then ctx.home else home
  -- the [[Prototype]] of the function: %GeneratorFunction.prototype%, %AsyncGeneratorFunction.prototype%,
  -- %AsyncFunction.prototype% or %Function.prototype% (§10.2.3 step 1, from the callers' choice)
  let id ← alloc { proto := .obj (r.closureProto f.gen f.async), kind := .closure f env ctx.thisV ctx.newTarget home #[] }
  if env != ctx.env then
    if let some n := f.name then declare env n { v := .obj id, mutable := false }
  defineOwn id "length" (.data (.num (Float.ofNat f.expectedArgs)) false false true)
  defineOwn id "name" (.data (.str (f.name.getD nameHint)) false false true)
  if f.gen then
    let p ← alloc { proto := .obj (if f.async then r.asyncGenProto else r.generatorProto) }
    defineOwn id "prototype" (.data (.obj p) true false false)
  else if f.kind == .normal && !f.async then
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

/-- The next live entry of a collection at or after `i`. -/
def collNext (es : Array (Option (Value × Value))) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, f + 1 => if i ≥ es.size then none else match es[i]! with
    | some _ => some i
    | none => collNext es (i + 1) f

/-- The index of a live entry whose key is SameValueZero to `k`. -/
def collFind (idx : Std.HashMap VKey Nat) (k : Value) : Option Nat := idx.get? (VKey.of k)

/-- Map.prototype.set and Set.prototype.add on the object itself (so the entries are
changed in place). -/
def collPut (key v : Value) (o : Obj) : Obj :=
  match o.kind with
  | .coll k es idx =>
    -- the object lets go of the tables first, so `set!`, `push` and `insert` work in place
    let o := { o with kind := .ordinary }
    match idx.get? (VKey.of key) with
    | some i => { o with kind := .coll k (es.set! i (some (key, v))) idx }
    | none =>
      let at_ := es.size  -- `es` is used up by `push`
      { o with kind := .coll k (es.push (some (key, v))) (idx.insert (VKey.of key) at_) }
  | _ => o

def collDel (key : Value) (o : Obj) : Obj :=
  match o.kind with
  | .coll k es idx =>
    match idx.get? (VKey.of key) with
    | some i =>
      let o := { o with kind := .ordinary }
      { o with kind := .coll k (es.set! i none) (idx.erase (VKey.of key)) }
    | none => o
  | _ => o

def collClear (o : Obj) : Obj :=
  match o.kind with
  | .coll k es _ => { o with kind := .coll k (es.map fun _ => none) {} }
  | _ => o

/-- The key of the global object's internal slot for the host's named properties
(`namedGlobal`): a private-name key (`privKey`), so no reflection lists it. -/
def namedGetterKey : String := privKey "WindowNamedProperties"

/-- A property key as a value: a Symbol for a Symbol key, else the string. -/
def keyValue (k : String) : Value :=
  match symOfKey? k with | some i => .sym i | none => .str (keyStr k)

/-- The String value of a key that is not a Symbol's (a name in a listing of keys). -/
@[inline] def keyStrV (k : String) : Value := .str (keyStr k)

/-- The integer part of a number, 0 for NaN and the infinities (the start of ToInt8 to
ToUint32, §7.1.6 to §7.1.11). -/
def toInt32Wide (x : Float) : Int :=
  if x.isNaN || x.isInf then 0 else truncInt x

/-- Read element `i` of a typed array whose buffer holds `bytes` (§10.4.5.15 TypedArrayGetElement). -/
def typedRead (ty : Nat) (bytes : ByteArray) (at_ : Nat) : Value :=
  let b := fun (k : Nat) => (bytes.get! (at_ + k)).toNat
  let u := fun (w : Nat) => (List.range w).foldl (fun a k => a + b k * 2 ^ (8 * k)) 0
  match ty with
  | 0 => let x := u 1; .num (Float.ofInt (if x ≥ 128 then (x : Int) - 256 else x))
  | 1 | 2 => .num (Float.ofNat (u 1))
  | 3 => let x := u 2; .num (Float.ofInt (if x ≥ 32768 then (x : Int) - 65536 else x))
  | 4 => .num (Float.ofNat (u 2))
  | 5 => let x := u 4; .num (Float.ofInt (if x ≥ 2147483648 then (x : Int) - 4294967296 else x))
  | 6 => .num (Float.ofNat (u 4))
  | 7 => .num (Float32.ofBits (u 4).toUInt32).toFloat
  | 9 => let x := u 8; .big (if x ≥ 2 ^ 63 then (x : Int) - 2 ^ 64 else x)
  | 10 => .big (u 8)
  | 11 => .num (L4Factoidal.Prim.Float16.toFloat (u 2).toUInt16)
  | _ => .num (Float.ofBits (u 8).toUInt64)

/-- ToUint8Clamp (§7.1.12): round half to even, clamped to 0..255. -/
def clampByte (x : Float) : Nat :=
  if x.isNaN || x ≤ 0 then 0 else if x ≥ 255 then 255 else
  let f := x.floor
  let r := x - f
  let g := if r < 0.5 then f else if r > 0.5 then f + 1 else if f.toUInt64.toNat % 2 == 0 then f else f + 1
  g.toUInt64.toNat

/-- The bytes of a number stored as element type `ty` (§25.1.3.17 NumericToRawBytes). -/
def typedBytes (ty : Nat) (x : Float) : ByteArray :=
  let le := fun (v : Nat) (w : Nat) => ByteArray.mk ((List.range w).toArray.map fun k => (v / 2 ^ (8 * k) % 256).toUInt8)
  let int := fun (w : Nat) => le (Int.toNat (toInt32Wide x % (2 ^ (8 * w) : Int))) w
  match ty with
  | 2 => le (clampByte x) 1
  | 0 | 1 => int 1
  | 3 | 4 => int 2
  | 5 | 6 => int 4
  | 7 => le x.toFloat32.toBits.toNat 4
  | 11 => le (L4Factoidal.Prim.Float16.ofFloat x).toNat 2
  | _ => le x.toBits.toNat 8

/-- Direct reads for Uint8Array and Uint8ClampedArray. -/
def typedReadByteFast (ty : Nat) (bytes : ByteArray) (at_ : Nat) : Value :=
  match ty with
  | 1 | 2 => .num (Float.ofNat (bytes.get! at_).toNat)
  | _ => typedRead ty bytes at_

/-- **Kind: refinement.** Says the direct byte read preserves every result of
`typedRead`, for all type tags, buffers and offsets. Does not say the reference
implements all of ECMA-262 or that this is faster. -/
@[csimp] theorem typedRead_eq_byteFast : typedRead = typedReadByteFast := by
  funext ty bytes at_
  match ty with
  | 0 | _ + 3 => rfl
  | 1 | 2 =>
    simp only [typedRead, typedReadByteFast, List.range_one, List.foldl_cons,
      List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]

/-- Direct singleton buffers for the three byte-sized numeric element types. -/
def typedBytesByteFast (ty : Nat) (x : Float) : ByteArray :=
  match ty with
  | 0 | 1 => ByteArray.mk #[(Int.toNat (toInt32Wide x % 256) % 256).toUInt8]
  | 2 => ByteArray.mk #[(clampByte x % 256).toUInt8]
  | _ => typedBytes ty x

/-- **Kind: refinement.** Says direct byte writes produce exactly the reference
bytes for every type tag and Float. Does not say anything about speed. -/
@[csimp] theorem typedBytes_eq_byteFast : typedBytes = typedBytesByteFast := by
  funext ty x
  match ty with
  | _ + 3 => rfl
  | 0 | 1 | 2 =>
    simp only [typedBytes, typedBytesByteFast, List.range_one, Array.map_singleton, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      show (2 : Int) ^ (8 * 1) = 256 from by decide]

#print axioms typedRead_eq_byteFast
#print axioms typedBytes_eq_byteFast

/-- The `name` of a function stored under a property key (§10.2.9 SetFunctionName). -/
def nameOfKey (key : String) : M String := do
  match symOfKey? key with
  | some id =>
    let d := (← get).syms.getD id ""
    pure (if d.isEmpty && id ≥ wellKnown.size then "" else "[" ++ d ++ "]")
  | none => pure (if isPrivKey key then "#" ++ (key.drop 1).toString else keyStr key)



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
  | .str s => pure ((List.range (Str.jsLength s)).toArray.map toString)
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

/-- The code units of a string, one character each (`Str.unitChars`): every string method
indexes this, so indices are UTF-16 code unit indices (§6.1.4). -/
def charsOf (s : String) : Array Char := Str.unitChars s

/-- Code units `i` to `j` (exclusive) of a string. -/
def substr (s : String) (i j : Nat) : String := Str.sliceUnits s i j

/-- Whether the ASCII string `pat` occurs in the ASCII string `s` at byte `i` (`k` of its
bytes are checked). -/
def asciiMatchAt (s pat : String) (i : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, k =>
    if k ≥ pat.utf8ByteSize then true
    else if String.Pos.Raw.get s ⟨i + k⟩ != String.Pos.Raw.get pat ⟨k⟩ then false
    else asciiMatchAt s pat i fuel (k + 1)

/-- `indexOf` on ASCII strings: no decoding, and the search stops at the first match. -/
def asciiIndexOf (s pat : String) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i + pat.utf8ByteSize > s.utf8ByteSize then none
    else if asciiMatchAt s pat i pat.utf8ByteSize 0 then some i
    else asciiIndexOf s pat fuel (i + 1)

def indexOfFrom (s pat : String) (from_ : Nat) : Option Nat :=
  if Str.isAscii s && Str.isAscii pat then
    if pat.isEmpty then (if from_ ≤ s.utf8ByteSize then some from_ else some s.utf8ByteSize)
    else asciiIndexOf s pat (s.utf8ByteSize + 1) from_
  else
  let cs := charsOf s; let ps := charsOf pat
  if ps.size == 0 then (if from_ ≤ cs.size then some from_ else some cs.size) else
  let first := ps[0]!
  let rec go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if i + ps.size > cs.size then none
      else if cs[i]! == first && (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then some i
      else go fuel (i + 1)
  go (cs.size + 1) from_

def lastIndexOfStr (s pat : String) : Option Nat :=
  let cs := charsOf s; let ps := charsOf pat
  if ps.size > cs.size then none else
  let rec go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if (cs[i]! == ps[0]!) && (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then some i
      else if i == 0 then none else go fuel (i - 1)
  go (cs.size + 1) (cs.size - ps.size)

/-- `lastIndexOf` from a position (§22.1.3.11 steps 9 to 12): the last unit index at or
before `start` where `pat` occurs. `start` past the last possible index is that index. -/
def lastIndexOfFrom (s pat : String) (start : Nat) : Option Nat :=
  let cs := charsOf s; let ps := charsOf pat
  if ps.size > cs.size then none else
  let rec go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, i =>
      if (ps.size == 0 || cs[i]! == ps[0]!) && (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!)
      then some i
      else if i == 0 then none else go fuel (i - 1)
  go (cs.size + 1) (min start (cs.size - ps.size))

/-- A position argument as a unit index in `0 … len` (ToIntegerOrInfinity, then the clamp of
`startsWith` step 7, `endsWith` step 7 and `includes` step 9). `undefined` is NaN, so 0. -/
def clampPos (x : Float) (len : Nat) : Nat :=
  if toIntegerOrInf x ≤ 0 then 0
  else if toIntegerOrInf x ≥ len.toFloat then len
  else min (toIntegerOrInf x).toUInt64.toNat len

/-- Whether the code units of `p` are the units of `s` from unit `pos` (the comparison of
`startsWith`, §22.1.3.24 steps 9 to 11, and of `endsWith`, §22.1.3.7 steps 10 to 12). On an
ASCII `s` only the units compared are read. -/
def unitsAt (s p : String) (pos : Nat) : Bool :=
  pos + Str.jsLength p ≤ Str.jsLength s && substr s pos (pos + Str.jsLength p) == p

/-- Bound (kind: safety of an index). Says: a position from `clampPos` is at most the
length it was clamped to, whatever the number. Does not say: that it is the integer part of
the number (that rests on `Float`, which Lean does not reason about). -/
theorem clampPos_le (x : Float) (len : Nat) : clampPos x len ≤ len := by
  unfold clampPos
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.le_refl _
    · exact Nat.min_le_right _ _

/-- Bound (kind: safety of an index). Says: where `unitsAt` answers true, the search string
lies inside the subject: `pos + |p| ≤ |s|` in code units. Does not say: that the units are
equal (that is the second conjunct of the definition, by `Str.sliceUnits`). -/
theorem unitsAt_bound (s p : String) (pos : Nat) (h : unitsAt s p pos = true) :
    pos + Str.jsLength p ≤ Str.jsLength s := by
  unfold unitsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

def splitOn (s sep : String) : Array String :=
  if sep.isEmpty then (charsOf s).map String.singleton
  else if Str.isBmp s && Str.isBmp sep then (s.splitOn sep).toArray
  else
    -- a separator may match half of a surrogate pair: split on the code units
    let n := Str.jsLength sep
    let rec go : Nat → Nat → Array String → Array String
      | 0, last, acc => acc.push (substr s last (Str.jsLength s))
      | f + 1, last, acc => match indexOfFrom s sep last with
        | some p => go f (p + n) (acc.push (substr s last p))
        | none => acc.push (substr s last (Str.jsLength s))
    go (Str.jsLength s + 1) 0 #[]

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

def newPromise : M Nat := do
  let r ← realm
  alloc { proto := .obj r.promiseProto, kind := .promise 0 .undef #[] false }

def enqueue (f : Value) (args : Array Value) : M Unit :=
  modify fun h => { h with jobs := h.jobs.push (f, args) }

/-- A function object for a native, without `name` and `length` (internal use). -/
def nativeFn (id : Native) : M Value := do
  let r ← realm
  pure (.obj (← alloc { proto := .obj r.functionProto, kind := .native id }))

/-- Array.prototype.flat's FlattenIntoArray (§23.1.3.13.1) on dense arrays. -/
def flattenArr (d : Nat) (vs : Array Value) : Nat → M (Array Value)
  | 0 => pure vs
  | f + 1 => do
    let mut out := #[]
    for v in vs do
      match v with
      | .obj vid =>
        match (← getObj vid).kind with
        | .array inner => if d > 0 then out := out ++ (← flattenArr (d - 1) inner f) else out := out.push v
        | _ => out := out.push v
      | _ => out := out.push v
    pure out

/-- The start of each match of `pat` in `s`, left to right, without overlap. -/
def allPositions (s pat : String) (from_ : Nat) (fuel : Nat) : List Nat :=
  go from_ fuel #[]
where
  go (from_ : Nat) : Nat → Array Nat → List Nat
    | 0, acc => acc.toList
    | f + 1, acc => match indexOfFrom s pat from_ with
      | some p => go (p + (if pat.isEmpty then 1 else Str.jsLength pat)) f (acc.push p)
      | none => acc.toList

/-! ## Lifting `yield` and `await` out of expressions

The generator machine suspends only at statement level. A `yield` (or an `await`,
which the parser reads as a `yield` in an async function) inside an expression is
moved before its statement when it is evaluated unconditionally: `f(await p)`
becomes `let %y0 = await p; f(%y0)`. The callee and operands to its left are then
evaluated after the suspension, not before: a known difference from §13.3.6 when
they have side effects. `yield` inside `&&`, `||`, `??`, `?:`, functions and classes
stays, and the machine refuses that statement. -/

/-- Lifting: the next temporary, and the statements that must run first. -/
abbrev Lift := StateM (Nat × Array Stmt)

def liftName (k : Nat) : String := "%y" ++ toString k

/-- A literal: its evaluation cannot be observed, and it is not worth a temporary. -/
def isLiteral : Expr → Bool
  | .num _ | .str _ | .bool _ | .null | .bigint _ | .lit _ => true
  | .member (.ident "") _ => true  -- the private name of `#x in o` (`privIn`)
  | _ => false

def liftPush (st : Stmt) : Lift Unit := modify fun s => (s.1, s.2.push st)

/-- A fresh temporary, declared by the statements that run first, holding `e`. -/
def liftTemp (e : Expr) : Lift Expr := do
  let (k, acc) ← get
  let x := liftName k
  set (k + 1, acc.push (Stmt.decl .letK [Decl.mk (.id x) (some e)]))
  pure (.ident x)

mutual
/-- Move each `yield` out of `e`, in order, into statements before it. Operands evaluated
before a `yield` move too (into temporaries), so they still come first; a `yield` on one
branch of `?:`, `&&`, `||` or `??` runs only when its branch does (an `if` statement). -/
def liftE : Nat → Expr → Lift Expr
  | 0, e => pure e
  | n + 1, e => do
    match e with
    | .yieldE d arg =>
      let arg ← match arg with
        | some a => do pure (some (← liftE n a))
        | none => pure none
      let (k, acc) ← get
      let x := liftName k
      set (k + 1, acc.push (Stmt.decl .letK [Decl.mk (.id x) (some (.yieldE d arg))]))
      pure (.ident x)
    | .unary op a => pure (.unary op (← liftE n a))
    | .binary op a b => do
      let a ← liftE n a
      let a ← if b.hasYield && !isLiteral a then liftTemp a else pure a
      let b ← liftE n b
      pure (.binary op a b)
    | .logical op a b =>
      if !b.hasYield then
        pure (.logical op (← liftE n a) b)
      else
        -- `a && b`: b's statements run only when a is true (for `||` false, for `??` nullish)
        let (k, acc) ← get
        let t := liftName k
        set (k + 1, acc)
        let a ← liftE n a
        let (b', pre) ← liftBranch n b
        let test : Expr := match op with
          | .and => .ident t
          | .or => .unary .not (.ident t)
          | .coalesce => .binary .seq (.binary .eq (.ident t) .null) (.bool true)
        let body := Stmt.block (pre ++ [.expr (.assign none (.ident t) b')])
        liftPush (.decl .letK [Decl.mk (.id t) (some a)])
        liftPush (.ifS test body none)
        pure (.ident t)
    | .cond c a b =>
      if !a.hasYield && !b.hasYield then
        pure (.cond (← liftE n c) a b)
      else
        let c ← liftE n c
        let (k, acc) ← get
        let t := liftName k
        set (k + 1, acc)
        let (a', preA) ← liftBranch n a
        let (b', preB) ← liftBranch n b
        liftPush (.decl .letK [Decl.mk (.id t) none])
        liftPush (.ifS c (.block (preA ++ [.expr (.assign none (.ident t) a')]))
          (some (.block (preB ++ [.expr (.assign none (.ident t) b')]))))
        pure (.ident t)
    | .call f args => do let f ← liftE n f; pure (.call f (← liftL n args))
    | .new f args => do let f ← liftE n f; pure (.new f (← liftL n args))
    | .member o k => pure (.member (← liftE n o) k)
    | .index o k => do
      let o ← liftE n o
      let o ← if k.hasYield && !isLiteral o then liftTemp o else pure o
      pure (.index o (← liftE n k))
    | .array es => pure (.array (← liftL n es))
    | .template c subs => pure (.template c (← liftL n subs))
    | .spread a => pure (.spread (← liftE n a))
    | .seq a b => do
      let a ← liftE n a
      if b.hasYield then
        liftPush (.expr a)
        liftE n b
      else pure (.seq a (← liftE n b))
    | .assign op t v => do
      let t ← match t with
        | .member o k => do pure (Expr.member (← liftE n o) k)
        | _ => pure t
      pure (.assign op t (← liftE n v))
    | .object ps => pure (.object (← liftP n ps))
    | _ => pure e
termination_by structural n _ => n

/-- Lift `e` into statements of its own (one branch of a conditional). -/
def liftBranch : Nat → Expr → Lift (Expr × List Stmt)
  | 0, e => pure (e, [])
  | n + 1, e => do
    let (k, acc) ← get
    set (k, (#[] : Array Stmt))
    let e' ← liftE n e
    let (k', pre) ← get
    set (k', acc)
    pure (e', pre.toList)
termination_by structural n _ => n

def liftL : Nat → List Expr → Lift (List Expr)
  | 0, es => pure es
  | _ + 1, [] => pure []
  | n + 1, e :: es => do
    let e ← liftE n e
    -- an argument before a `yield` is evaluated first
    let e ← match e with
      | .spread _ => pure e
      | _ => if es.any Expr.hasYield && !isLiteral e then liftTemp e else pure e
    pure (e :: (← liftL n es))
termination_by structural n _ => n

def liftP : Nat → List PropDef → Lift (List PropDef)
  | 0, ps => pure ps
  | _ + 1, [] => pure []
  | n + 1, p :: ps => do
    let p ← match p with
      | .init (.lit k) v => do pure (PropDef.init (.lit k) (← liftE n v))
      | .spread v => do pure (PropDef.spread (← liftE n v))
      | _ => pure p
    pure (p :: (← liftP n ps))
termination_by structural n _ => n
end

/-- A statement with its lifted `yield`s before it, or `none` when nothing moved. -/
def liftStmt (seed : Nat) (s : Stmt) : Option (List Stmt) :=
  let run (e : Expr) : Expr × Array Stmt :=
    let (e', (_, acc)) := (liftE 10000 e).run (seed, #[])
    (e', acc)
  let wrap (e : Expr) (mk : Expr → Stmt) : Option (List Stmt) :=
    match e with
    | .yieldE d (some a) =>
      -- the statement's own `yield` stays (`genEnter` takes it); the yields in its operand
      -- (`yield await x`, `await (yield x)`, `return` of a `yield` in an async generator) go first
      if a.hasYield then
        let (a', acc) := run a
        if acc.isEmpty then none else some (acc.toList ++ [mk (.yieldE d (some a'))])
      else none
    | .yieldE _ none => none
    | _ =>
      let (e', acc) := run e
      if acc.isEmpty then none else some (acc.toList ++ [mk e'])
  match s with
  | .expr e => wrap e .expr
  | .ret (some e) => wrap e (fun x => .ret (some x))
  | .throwS e => wrap e .throwS
  | .decl k [Decl.mk p (some e)] => wrap e (fun x => .decl k [Decl.mk p (some x)])
  | .ifS c t f =>
    -- the test may itself be a `yield` (`if (await x)`), which `genEnter` does not take apart
    let (c', acc) := run c
    if acc.isEmpty then none else some (acc.toList ++ [.ifS c' t f])
  | _ => none

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


/-- The signal that ends an optional chain at a nullish base (§13.3.9.1): never seen by
script code, since every `optBase` is inside its `chain`. -/
def shortSignal : String := "%optional-chain"

/-- RegExpCreate (§22.2.3.2): a new RegExp object, or a `SyntaxError`. -/
def newRegExp (src flags : String) : M Value := do
  match Re.compile src flags with
  | .error e => throwErr .syntax (if e.startsWith "SyntaxError: " then (e.drop 13).toString else e)
  | .ok re =>
    let id ← alloc { proto := .obj (← realm).regexpProto, kind := .regexp re src flags }
    defineOwn id "lastIndex" (.data (.num 0) true false false)
    pure (.obj id)

def regexpOf (v : Value) : M (Re.Compiled × String × String) := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .regexp re s f => pure (re, s, f)
    | _ => throwErr .type "RegExp method called on incompatible receiver"
  | _ => throwErr .type "RegExp method called on incompatible receiver"

def isRegExpV (v : Value) : M Bool := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .regexp .. => pure true
    | _ => pure false
  | _ => pure false

/-- A JSON text's value as a JavaScript value (§25.5.1 JSON.parse, no reviver). -/
def jsonToValue : Nat → L4Factoidal.JSON.Json → M Value
  | 0, _ => throwErr .range "JSON nesting too deep"
  | fuel + 1, j => do
    match j with
    | .null => pure .null
    | .bool b => pure (.bool b)
    | .string s => pure (.str s)
    | .number t => pure (.num (strToNumber t))
    | .array xs => newArray (← xs.toArray.mapM (jsonToValue fuel))
    | .object kvs =>
      let o ← newObject
      for (k, v) in kvs do defineOwn o (strKey k) (.data (← jsonToValue fuel v) true true true)
      pure (.obj o)

def bufferBytes (o : Obj) : ByteArray :=
  match o.kind with | .buffer b => b | _ => ByteArray.empty

def elemSize (ty : Nat) : Nat := (typedNames[ty]?.map (·.2)).getD 1

/-- A new ArrayBuffer with these bytes. -/
def newBuffer (bytes : ByteArray) : M Value := do
  -- `byteLength` is an accessor of ArrayBuffer.prototype (§25.1.6.2)
  let id ← alloc { proto := .obj (← realm).bufferProto, kind := .buffer bytes }
  pure (.obj id)

/-- A new typed array of type `ty` over the ArrayBuffer object `buf`. -/
def newTyped (ty buf off len : Nat) : M Value := do
  let r ← realm
  -- `length`, `byteLength`, `byteOffset` and `buffer` are accessors of
  -- %TypedArray%.prototype (§23.2.3)
  let id ← alloc { proto := .obj (r.typedProtos.getD ty r.objectProto), kind := .typed ty buf off len }
  pure (.obj id)

/-- The 8 bytes of a BigInt stored as `BigInt64` or `BigUint64` (§25.1.3.17: modulo 2^64). -/
def bigBytes (i : Int) : ByteArray :=
  let u := (i.emod (2 ^ 64)).toNat
  ByteArray.mk ((List.range 8).toArray.map fun k => (u / 2 ^ (8 * k) % 256).toUInt8)

/-- Write a value (a Number, or a BigInt for the BigInt types) into element `i` of a typed
array. -/
def typedWriteV (ty buf off i : Nat) (v : Value) : M Unit :=
  let bs := match v with
    | .big b => bigBytes b
    | .num x => typedBytes ty x
    | _ => typedBytes ty nan
  modifyObj buf fun bo => match bo.kind with
    | .buffer bytes =>
      let at_ := off + i * elemSize ty
      if at_ + bs.size ≤ bytes.size then
        let bo := { bo with kind := .buffer ByteArray.empty }
        { bo with kind := .buffer (bs.copySlice 0 bytes at_ bs.size) }
      else bo
    | _ => bo

/-- The hidden slots of an ArrayBuffer: its maximum length (resizable), whether it is
detached, whether it is a SharedArrayBuffer. -/
def bufMaxKey : String := privKey "%ArrayBufferMaxByteLength"
def bufDetachedKey : String := privKey "%ArrayBufferDetached"
def bufSharedKey : String := privKey "%ArrayBufferShared"

def hiddenNum (o : Obj) (k : String) : Option Nat :=
  match o.props.get? k with
  | some (.data (.num x) ..) => some x.toUInt64.toNat
  | _ => none

/-- The hidden slot of an immutable prototype exotic object (§10.4.7): Object.prototype. -/
def immutableProtoKey : String := privKey "%ImmutablePrototype"

def hiddenFlag (o : Obj) (k : String) : Bool :=
  match o.props.get? k with
  | some (.data (.bool b) ..) => b
  | _ => false

/-- [[SetPrototypeOf]] (§10.1.2, §10.4.7.2) of an object, or of a Proxy's target (the trap is
not called): `protoChangeAllowed` decides, over the chain of `v` as OrdinarySetPrototypeOf
walks it. -/
def setProtoOf (id : Nat) (v : Value) : M Bool := do
  let id ← match (← getObj id).kind with
    | .proxy (.obj t) _ => pure t
    | _ => pure id
  let o ← getObj id
  let mut chain : List Nat := []
  let mut p := v
  for _ in [0:(← get).objs.size + 1] do
    match p with
    | .obj pid =>
      let po ← getObj pid
      match po.kind with
      | .proxy .. => break
      | _ =>
        chain := pid :: chain
        if pid == id then break
        p := po.proto
    | _ => break
  if !protoChangeAllowed id o.proto v o.extensible (hiddenFlag o immutableProtoKey) chain then return false
  modifyObj id (fun o => { o with proto := v })
  return true

/-- IsDetachedBuffer (§25.1.3.4). -/
def isDetached (o : Obj) : Bool := hiddenFlag o bufDetachedKey

/-- IsTypedArrayOutOfBounds (§10.4.5.11) of a view with a fixed length: the buffer is
detached, or the view's bytes run past its end. -/
def typedOob (detached : Bool) (off len elem size : Nat) : Bool :=
  detached || off + len * elem > size

/-- The element count of a typed array as its buffer now is (§10.4.5.12
TypedArrayLength): 0 when the buffer is detached or too small for the view. -/
def liveLen (ty buf off len : Nat) : M Nat := do
  let bo ← getObj buf
  pure (if typedOob (isDetached bo) off len (elemSize ty) (bufferBytes bo).size then 0 else len)

/-- The %TypedArray%.prototype methods that validate the typed array and then take the steps
of the Array.prototype method of the same name (`NativeX.typedGeneric`): name, length. -/
def typedGenericNames : Array (String × Nat) :=
  #[("forEach", 1), ("join", 1), ("indexOf", 1), ("includes", 1), ("every", 1), ("some", 1), ("reduce", 1),
    ("find", 1), ("findIndex", 1), ("values", 0), ("keys", 0), ("entries", 0)]

/-- Where %TypedArray%.prototype keeps the Array.prototype function a generic method uses. -/
def typedGenericKey (nm : String) : String := privKey ("%Array." ++ nm)

/-- Does an Array iteration method skip the indices that HasProperty says are absent
(§23.1.3)? `find` and `findIndex` read every index; forEach, map, filter, some, every and the
others do not. -/
def arrayProbes : Native → Bool
  | .arrayFind | .arrayFindIndex => false
  | _ => true

/-- ValidateTypedArray's test (§23.2.4.4): is the view inside its buffer, and the buffer not
detached? -/
def typedInBounds (ty buf off len : Nat) : M Bool := do
  let bo ← getObj buf
  pure !(typedOob (isDetached bo) off len (elemSize ty) (bufferBytes bo).size)

/-- The hidden slots of an iterator helper (§27.1.2.1): the underlying iterator and its
`next`, the kind (`Native.iterLazy`, 5 the wrapper of `Iterator.from`), the callback or
limit, the count, the inner iterator of `flatMap`, done and running. -/
def helperIt : String := privKey "%HelperIterated"
def helperNextKey : String := privKey "%HelperNext"
def helperKind : String := privKey "%HelperKind"
def helperFn : String := privKey "%HelperFn"
def helperCount : String := privKey "%HelperCount"
def helperInner : String := privKey "%HelperInner"
def helperDone : String := privKey "%HelperDone"
def helperRunning : String := privKey "%HelperRunning"

/-- The hidden slot of a Date object (`[[DateValue]]` is its `.prim (.num t)`). -/
def dateKey : String := privKey "%DateValue"

/-- The record of a `yield*` in an async generator (§15.5.5 with generatorKind async), held
where a sync `yield*` holds its iterator (`GFrame.delegate`): an object with these hidden
slots. The phase: 0 at a `yield` (or before the first `next`), 1 the result of `next` or
`throw` is awaited, 2 the result of `return`, 3 the result of `return` when the iterator has
no `throw` (a TypeError follows), 4 the value of a `return` when it has no `return`. -/
def delegIterKey : String := privKey "%DelegateIterator"
def delegNextKey : String := privKey "%DelegateNext"
def delegPhaseKey : String := privKey "%DelegatePhase"

/-- The iterator, its `next` and the phase of an async delegate record; `none` for the
iterator of a sync `yield*`. -/
def asyncDelegate? (it : Value) : M (Option (Value × Value × Nat)) := do
  match it with
  | .obj id =>
    let o ← getObj id
    match o.props.get? delegIterKey, o.props.get? delegNextKey, o.props.get? delegPhaseKey with
    | some (.data iter ..), some (.data next ..), some (.data (.num ph) ..) =>
      pure (some (iter, next, ph.toUInt64.toNat))
    | _, _, _ => pure none
  | _ => pure none

def setDelegatePhase (it : Value) (ph : Nat) : M Unit :=
  match it with
  | .obj id => setHidden id delegPhaseKey (.num (Float.ofNat ph))
  | _ => pure ()

/-- The GlobalSymbolRegistry (§20.4.2.2): a hidden object of the global object, its
properties the registered keys. The hidden slots of a WeakRef (its target) and of a
FinalizationRegistry (its cleanup callback, and the array of unregister tokens). -/
def symbolRegistryKey : String := privKey "%SymbolRegistry"
def weakRefTargetKey : String := privKey "%WeakRefTarget"
def finRegCallbackKey : String := privKey "%CleanupCallback"
def finRegTokensKey : String := privKey "%UnregisterTokens"

/-- The hidden slots of an async-from-sync iterator (§27.1.6.3 `[[SyncIteratorRecord]]`): the
sync iterator and its `next`; and the global object's hidden property that holds
%AsyncFromSyncIteratorPrototype%. -/
def syncIterKey : String := privKey "%SyncIterator"
def syncNextKey : String := privKey "%SyncNext"
def asyncFromSyncProtoKey : String := privKey "%AsyncFromSyncIteratorPrototype"

/-- The time value of a Date object. -/
def thisDate? (v : Value) : M (Option Float) := do
  match v with
  | .obj oid =>
    let o ← getObj oid
    match o.kind with
    | .prim (.num t) => pure (if hiddenFlag o dateKey then some t else none)
    | _ => pure none
  | _ => pure none

/-- The time of year, month, and optional date, hours, minutes, seconds, ms (Numbers), as
the Date constructor and Date.UTC take them: a year 0 to 99 is 1900 to 1999. -/
def dateOfParts (xs : Array Float) : Float :=
  let y := xs.getD 0 (0.0 / 0.0)
  let yi := toIntegerOrInf y
  let yr := if !y.isNaN && 0 ≤ yi && yi ≤ 99 then 1900 + yi else y
  Date.makeDate (Date.makeDay yr (xs.getD 1 0) (xs.getD 2 1))
    (Date.makeTime (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0) (xs.getD 6 0))

/-- The methods of Date.prototype (`Native.dateMethod`): name, number, length. Local time
is UTC, so `getHours` and `getUTCHours` are one method. -/
def dateMethodNames : List (String × Nat × Nat) :=
  [("getDate", 0, 0), ("getDay", 1, 0), ("getFullYear", 2, 0), ("getHours", 3, 0), ("getMilliseconds", 4, 0),
   ("getMinutes", 5, 0), ("getMonth", 6, 0), ("getSeconds", 7, 0), ("getTimezoneOffset", 8, 0), ("getYear", 9, 0),
   ("getUTCDate", 0, 0), ("getUTCDay", 1, 0), ("getUTCFullYear", 2, 0), ("getUTCHours", 3, 0),
   ("getUTCMilliseconds", 4, 0), ("getUTCMinutes", 5, 0), ("getUTCMonth", 6, 0), ("getUTCSeconds", 7, 0),
   ("setDate", 20, 1), ("setFullYear", 21, 3), ("setHours", 22, 4), ("setMilliseconds", 23, 1),
   ("setMinutes", 24, 3), ("setMonth", 25, 2), ("setSeconds", 26, 2), ("setTime", 27, 1), ("setYear", 28, 1),
   ("setUTCDate", 20, 1), ("setUTCFullYear", 21, 3), ("setUTCHours", 22, 4), ("setUTCMilliseconds", 23, 1),
   ("setUTCMinutes", 24, 3), ("setUTCMonth", 25, 2), ("setUTCSeconds", 26, 2),
   ("toDateString", 30, 0), ("toISOString", 31, 0), ("toJSON", 32, 1), ("toLocaleDateString", 33, 0),
   ("toLocaleString", 34, 0), ("toLocaleTimeString", 35, 0), ("toString", 36, 0), ("toTimeString", 37, 0),
   ("toUTCString", 38, 0)]

/-- Write a number into element `i` of a typed array. -/
def typedWrite (ty buf off i : Nat) (x : Float) : M Unit :=
  let bs := typedBytes ty x
  modifyObj buf fun bo => match bo.kind with
    | .buffer bytes => { bo with kind := .buffer (bs.copySlice 0 bytes (off + i * elemSize ty) bs.size) }
    | _ => bo

/-- The number of `HeapOf.hostCall` that answers the clock: ns as a number. -/
def hostClockId : Nat := 1000000

/-- The value of a host's answer; writes into an argument's ArrayBuffer and detaching it
happen here. -/
def hostAnswer (args : Array Value) : HostAns → M Value
  | .val v => pure v
  | .ints xs => newArray (xs.map fun i => .num (Float.ofInt i))
  | .err m => throwErr .type m
  | .bytes b => newBuffer b
  | .detach i => do
    if let some (.obj id) := args[i]? then
      if let .buffer _ := (← getObj id).kind then
        modifyObj id fun bo => { bo with kind := .buffer ByteArray.empty }
        -- IsDetachedBuffer reads this slot; `byteLength` (an accessor) then answers 0
        defineOwn id bufDetachedKey (.data (.bool true) true false false)
    pure .undef
  | .writes i ws ans => do
    if let some (.obj id) := args[i]? then
      modifyObj id fun bo => match bo.kind with
        | .buffer bytes =>
          -- Take the bytes out first, so the writes change them in place.
          let bo := { bo with kind := .buffer ByteArray.empty }
          { bo with kind := .buffer (ws.foldl (fun acc (o, c) =>
              if o + c.size ≤ acc.size then c.copySlice 0 acc o c.size else acc) bytes) }
        | _ => bo
    hostAnswer args ans

/-- Call a native of the host (`Native.host k`). The host's state is taken out of the heap
for the call, so the host changes it in place. -/
def callHost (k : Nat) (args : Array Value) : M Value := do
  let (st, call, left) ← modifyGet fun h => ((h.host, h.hostCall, h.steps.toNat), { h with host := none })
  -- An ArrayBuffer or a typed array reaches the host as its bytes.
  let hargs ← args.mapM fun a => do
    match a with
    | .obj id => match (← getObj id).kind with
      | .buffer b => pure (HostArg.bytes b)
      | .typed ty b off len => pure (.bytes ((bufferBytes (← getObj b)).extract off (off + len * elemSize ty)))
      | _ => pure (.val a)
    | _ => pure (.val a)
  match st with
  | none => throwErr .type "this realm has no host"
  | some st =>
    let (st, ans) := call st k hargs left
    modify fun h => { h with host := some st }
    hostAnswer args ans


/-- The host's clock in ns (0 with no host). -/
def hostNowNs : M Float := do
  if (← get).host.isNone then return 0
  match ← callHost hostClockId #[] with
  | .num x => pure x
  | _ => pure 0

/-- GetSubstitution (§22.1.3.19.1): `$$`, `$&`, `` $` ``, `$'`, `$n`, `$nn`, `$<name>`. -/
def substitution (rep : String) (matched : String) (pos : Nat) (cs : Array Char)
    (caps : Array (Option String)) (names : Array (String × Nat)) : Option String := Id.run do
  let r := rep.toList.toArray
  let tailAt := pos + Str.jsLength matched
  let mut out := ""
  let mut i := 0
  for _ in [0:r.size + 1] do
    if i ≥ r.size then break
    -- `none`: the result is past `maxStringBytes` (each `$&` or `$1` adds a whole match)
    if out.utf8ByteSize > maxStringBytes then return none
    let c := r[i]!
    if c != '$' || i + 1 ≥ r.size then out := out.push c; i := i + 1; continue
    let d := r[i+1]!
    if d == '$' then out := out.push '$'; i := i + 2
    else if d == '&' then out := out ++ matched; i := i + 2
    else if d == '`' then out := out ++ Str.ofUnitChars (cs.extract 0 pos); i := i + 2
    else if d == '\'' then out := out ++ Str.ofUnitChars (cs.extract tailAt cs.size); i := i + 2
    else if d.isDigit then
      let one := d.toNat - 48
      let two := if i + 2 < r.size && r[i+2]!.isDigit then some (one * 10 + (r[i+2]!.toNat - 48)) else none
      match two with
      | some t => if t ≥ 1 && t ≤ caps.size then out := out ++ (caps[t-1]!).getD ""; i := i + 3; continue
                  else pure ()
      | none => pure ()
      if one ≥ 1 && one ≤ caps.size then out := out ++ (caps[one-1]!).getD ""; i := i + 2
      else out := out.push '$'; i := i + 1
    else if d == '<' && !names.isEmpty then
      match (List.range (r.size - i)).find? (fun k => r[i + 2 + k]? == some '>') with
      | some k =>
        let name := String.ofList (r.extract (i + 2) (i + 2 + k)).toList
        match names.find? (·.1 == name) with
        | some (_, g) => out := out ++ (caps[g-1]?.join).getD ""
        | none => pure ()
        i := i + 3 + k
      | none => out := out.push '$'; i := i + 1
    else out := out.push '$'; i := i + 1
  return (if out.utf8ByteSize > maxStringBytes then none else some (Str.canonical out))

/-- QuoteJSONString (§25.5.2.3) for surrogates: a code unit of a surrogate that is not part
of a pair is written as `\\uXXXX`, in lower-case hexadecimal (well-formed JSON.stringify). -/
def jsonLone (s : String) : String :=
  if Str.isAscii s || s.all (fun c : Char => !Str.isLoneChar c) then s else Id.run do
    let us := (Str.units s).toArray
    let mut out := ""
    let mut i := 0
    for _ in [0:us.size] do
      if i ≥ us.size then break
      let u := us[i]!
      if Str.isHigh u && i + 1 < us.size && Str.isLow us[i+1]! then
        out := out ++ Str.ofUnits [u, us[i+1]!]; i := i + 2
      else if Str.isSurrogate u then
        out := out ++ "\\u" ++ String.ofList ((Nat.toDigits 16 u).leftpad 4 '0'); i := i + 1
      else out := out.push (Char.ofNat u); i := i + 1
    return out

set_option maxHeartbeats 4000000 in
/-! ## The register machine (`JS/Compile.lean`)

One loop interprets a compiled function; a call from compiled code to compiled code stays in
the loop (no native frame, no environment, no arguments array), so JavaScript recursion
between compiled functions is limited by `vmMaxDepth`, not by the host's stack. Registers
hold values; a number is kept unboxed in the parallel float registers, with `Value.fl` in
the value register. Everything other than plain number arithmetic and plain property access
goes through the same helpers as the evaluator. The registers are put back in the heap
(`vmStash`) before anything that can run JavaScript or fail, so a nested run finds them and an
exception does not lose them. -/

/-- A compiled function suspended at a call. -/
structure VFrame where
  code : Code
  pc : Nat
  bp : Nat
  env : Nat
  /-- The caller's register for the result. -/
  dst : Nat
  depth : Nat

/-- Compiled functions may nest this deep (they do not use the host's stack). -/
def vmMaxDepth : Nat := 20000

/-- The register machine is on. Off, every function runs in the evaluator (a differential test
and a way to compare). -/
def useVm : Bool := true

@[inline] def vmStash (regs : Array Value) (fregs : FloatArray) (top : Nat) : M Unit :=
  modify fun h => { h with vmRegs := regs, vmF := fregs, vmTop := top }

/-- Take the registers back out of the heap, for the caller to own. -/
@[inline] def vmTake : M (Array Value × FloatArray) :=
  modifyGet fun h => ((h.vmRegs, h.vmF), { h with vmRegs := #[], vmF := .empty })

/-- A register as a language value (boxing a number). -/
@[inline] def vmRd (regs : Array Value) (fregs : FloatArray) (i : Nat) : Value :=
  match regs[i]! with
  | .fl => .num (fregs.get! i)
  | v => v

/-- Grow the value registers to `n`. -/
def vmGrowRegs (regs : Array Value) (n : Nat) : Array Value :=
  if regs.size >= n then regs else
  let cap := Nat.max n (2 * regs.size + 64)
  go regs (cap - regs.size)
where go (r : Array Value) : Nat → Array Value
  | 0 => r
  | k + 1 => go (r.push .undef) k

/-- Grow the float registers to `n`. -/
def vmGrowF (fregs : FloatArray) (n : Nat) : FloatArray :=
  if fregs.size >= n then fregs else
  let cap := Nat.max n (2 * fregs.size + 64)
  go fregs (cap - fregs.size)
where go (r : FloatArray) : Nat → FloatArray
  | 0 => r
  | k + 1 => go (r.push 0) k

/-- Registers `lo` to `hi` are set to `undefined`. -/
def vmClear (regs : Array Value) (lo : Nat) : Nat → Array Value
  | 0 => regs
  | k + 1 => vmClear (regs.set! lo .undef) (lo + 1) k

/-- The `k` registers from `base`, as values. -/
def vmArgs (regs : Array Value) (fregs : FloatArray) (base : Nat) : Nat → Array Value → Array Value
  | 0, acc => acc
  | k + 1, acc => vmArgs regs fregs (base + 1) k (acc.push (vmRd regs fregs base))

/-- Write the first `n` arguments into registers from `base`, numbers unboxed. -/
def vmFill (regs : Array Value) (fregs : FloatArray) (base : Nat) (args : Array Value) :
    Nat → Nat → Array Value × FloatArray
  | 0, _ => (regs, fregs)
  | k + 1, i =>
    match args.getD i .undef with
    | .num x => vmFill (regs.set! (base + i) .fl) (fregs.set! (base + i) x) base args k (i + 1)
    | v => vmFill (regs.set! (base + i) v) fregs base args k (i + 1)

mutual

/-- `[[Get]]` on any value (§7.3.2 GetV). -/
def getV : Nat → Value → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, key => do
    match v with
    | .obj id =>
      match (← get).findProp id key 1000 with
      | none =>
        match (← getObj id).kind with
        | .proxy t hnd =>
          match ← proxyTrap n hnd "get" with
          | some f => callV n f hnd #[t, keyValue key, v]
          | none => getV n t key
        | .typed ty b off len =>
          match arrayIndex? key with
          | some i => if i < (← liveLen ty b off len) then pure (typedRead ty (bufferBytes (← getObj b)) (off + i * elemSize ty)) else pure .undef
          | none => pure .undef
        | _ =>
          if isPrivKey key then throwErr .type s!"Cannot read private member #{(key.drop 1).toString} from an object whose class did not declare it"
          -- a property the global object and its prototype chain do not have: the host's
          -- named properties (`namedGlobal`), asked for on this miss only
          if id == (← get).realm.globalObj && !isSymKey key then
            match ← namedGlobal n key with
            | some x => pure x
            | none => pure .undef
          else pure .undef
      | some (.data x ..) => pure x
      | some (.acc g _ _ _) => if g.isObj then callV n g v #[] else pure .undef
    | .str s =>
      if key == "length" then pure (.num (Float.ofNat ((← get).strLength s)))
      else match arrayIndex? key with
        | some i => match Str.unitStrAt? s i with
          | some c => pure (.str c)
          | none => getProto n (← realm).stringProto key v
        | none => getProto n (← realm).stringProto key v
    | .num _ => getProto n (← realm).numberProto key v
    | .bool _ => getProto n (← realm).booleanProto key v
    | .sym _ => getProto n (← realm).symbolProto key v
    | .big _ => getProto n (← realm).bigintProto key v
    | .hole | .fl => pure .undef
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

/-- A trap of a Proxy's handler (§10.5): the method, or none. A revoked proxy throws. -/
def proxyTrap : Nat → Value → String → M (Option Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, hnd, name => do
    match hnd with
    | .obj _ =>
      match ← getV n hnd name with
      | .undef | .null => pure none
      | f => pure (some f)
    | _ => throwErr .type s!"Cannot perform '{name}' on a proxy that has been revoked"
termination_by structural n _ _ => n

/-- `[[HasProperty]]` (§7.3.12 HasProperty), with Proxy and typed arrays. -/
def hasProp : Nat → Nat → String → M Bool
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, id, k => do
    match (← getObj id).kind with
    | .proxy t hnd =>
      match ← proxyTrap n hnd "has" with
      | some f => pure (toBool (← callV n f hnd #[t, keyValue k]))
      | none => match t with | .obj tid => hasProp n tid k | _ => pure false
    | .typed ty b off len =>
      match arrayIndex? k with
      | some i => pure (i < (← liveLen ty b off len))
      | none => pure ((← get).findProp id k 1000).isSome
    | _ => pure ((← get).findProp id k 1000).isSome
termination_by structural n _ _ => n

/-- `[[Get]]` with a receiver (Reflect.get, §28.1.6). -/
def getRecv : Nat → Nat → String → Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, key, recv => do
    match (← get).findProp id key 1000 with
    | some (.data x ..) => pure x
    | some (.acc g _ _ _) => if g.isObj then callV n g recv #[] else pure .undef
    | none => getV n (.obj id) key
termination_by structural n _ _ _ => n

/-- `[[OwnPropertyKeys]]` (§10.1.11), with Proxy (`ownKeys`) and typed arrays. -/
def ownKeysOf : Nat → Nat → M (Array String)
  | 0, _ => throw (.halt "fuel")
  | n + 1, id => do
    let o ← getObj id
    match o.kind with
    | .proxy t hnd =>
      match ← proxyTrap n hnd "ownKeys" with
      | some f => (← elemsOf n (← callV n f hnd #[t])).mapM (toKey n)
      | none => match t with | .obj tid => ownKeysOf n tid | _ => pure #[]
    | .typed ty b off len => pure ((List.range (← liveLen ty b off len)).toArray.map toString ++ o.ownKeys)
    | _ => pure o.ownKeys
termination_by structural n _ => n

/-- `[[GetOwnProperty]]` (§10.1.5), with Proxy (`getOwnPropertyDescriptor`) and typed arrays. -/
def ownDesc : Nat → Nat → String → M (Option PropV)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, id, k => do
    let o ← getObj id
    match o.kind with
    | .proxy t hnd =>
      match ← proxyTrap n hnd "getOwnPropertyDescriptor" with
      | some f =>
        let d ← callV n f hnd #[t, keyValue k]
        match d with
        | .obj _ =>
          let flag := fun (name : String) => do pure (toBool (← getV n d name))
          let g ← getV n d "get"
          let st ← getV n d "set"
          if g.isObj || st.isObj then pure (some (.acc g st (← flag "enumerable") (← flag "configurable")))
          else pure (some (.data (← getV n d "value") (← flag "writable") (← flag "enumerable") (← flag "configurable")))
        | _ => pure none
      | none => match t with | .obj tid => ownDesc n tid k | _ => pure none
    | .typed ty b off len =>
      match arrayIndex? k with
      | some i => if i < (← liveLen ty b off len) then pure (some (.data (typedRead ty (bufferBytes (← getObj b)) (off + i * elemSize ty)) true true true)) else pure none
      | none => pure (o.getOwn k)
    | _ => pure (o.getOwn k)
termination_by structural n _ _ => n

/-- `[[Set]]` (§10.1.9 OrdinarySet), with the Array `length` (§10.4.2.4). -/
def putV : Nat → Value → String → Value → Bool → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, target, key, val, strict => do
    match target with
    | .obj id =>
      -- an own writable data property of a non-exotic object is overwritten in place
      if ← setOwnData id key val then return
      let o ← getObj id
      match o.kind with
      | .proxy t hnd =>
        match ← proxyTrap n hnd "set" with
        | some f =>
          let ok ← callV n f hnd #[t, keyValue key, val, target]
          if !toBool ok && strict then throwErr .type s!"'set' on proxy: trap returned falsish for property '{key}'"
        | none => putV n t key val strict
        return
      | .typed ty b off len =>
        if let some i := arrayIndex? key then
          -- §10.4.5.16 TypedArraySetElement: the value is converted first
          let x ← typedConv n ty val
          if i < (← liveLen ty b off len) then typedWriteV ty b off i x
          return
      | _ => pure ()
      match o.kind, key with
      | .array es, "length" =>
        let len ← toNum n val
        if len < 0 || !isIntegral len || len ≥ twoPow32F then throwErr .range "Invalid array length"
        let l := len.toUInt64.toNat
        if l > es.size then
          if l > maxDenseArray then throwErr .range "Invalid array length"
          charge ((l - es.size) / 64)
        let es' := if l ≤ es.size then es.extract 0 l else es ++ Array.replicate (l - es.size) .undef
        modifyObj id fun o => { o with kind := .array es' }
        return
      | _, _ => pure ()
      if isPrivKey key && ((← get).findProp id key 1000).isNone then
        throwErr .type s!"Cannot write private member #{(key.drop 1).toString} to an object whose class did not declare it"
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
    | .hole | .fl | .undef => pure nan
    | .null => pure 0
    | .bool b => pure (if b then 1 else 0)
    | .num x => pure x
    | .str s => pure (strToNumber s)
    | .sym _ => throwErr .type "Cannot convert a Symbol value to a number"
    | .big _ => throwErr .type "Cannot convert a BigInt value to a number"
    | .obj _ => toNum n (← toPrim n v "number")
termination_by structural n _ => n

/-- ToBigInt (§7.1.13). -/
def toBigInt : Nat → Value → M Int
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match ← toPrim n v "number" with
    | .big i => pure i
    | .bool b => pure (if b then 1 else 0)
    | .str t => match strToBigInt t with
      | some i => pure i
      | none => throwErr .syntax s!"Cannot convert {t} to a BigInt"
    | .num _ => throwErr .type "Cannot convert a Number to a BigInt"
    | .sym _ => throwErr .type "Cannot convert a Symbol value to a BigInt"
    | _ => throwErr .type "Cannot convert undefined or null to a BigInt"
termination_by structural n _ => n

/-- The value stored into a typed array of type `ty`: ToBigInt for the BigInt types,
else ToNumber (§10.4.5.16). -/
def typedConv : Nat → Nat → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ty, v => do
    if typedIsBig ty then pure (.big (← toBigInt n v)) else pure (.num (← toNum n v))
termination_by structural n _ _ => n

/-- ToString (§7.1.17). -/
def toStr : Nat → Value → M String
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .hole | .fl | .undef => pure "undefined"
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
    | .str s => pure (strKey s)
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
    | .hole | .fl | .undef | .null => throwErr .type "Cannot convert undefined or null to object"
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
              | k + 1, .obj o => match (h.obj o).kind, (h.obj o).proto with
                | .proxy t _, _ => walk k t
                | _, .obj q => q == pid || walk k (.obj q)
                | _, _ => false
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
      | .str x, .str y => checkStrLen (x.utf8ByteSize + y.utf8ByteSize); pure (.str (Str.jsAppend x y))
      | _, _ =>
        let pa ← toPrim n a "default"
        let pb ← toPrim n b "default"
        match pa, pb with
        | .str _, _ | _, .str _ =>
          let sa ← toStr n pa
          let sb ← toStr n pb
          checkStrLen (sa.utf8ByteSize + sb.utf8ByteSize)
          pure (.str (Str.jsAppend sa sb))
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
        pure (.bool (← hasProp n id k))
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
    tickCall
    let h ← get
    if h.depth ≥ h.maxDepth then throwErr .range "Maximum call stack size exceeded"
    let saved := h.depth
    set { h with depth := h.depth + 1 }
    -- The depth comes back on every exit, a throw included (a throw that a caller catches
    -- must not use up the call depth).
    -- the environment: the arguments are its first slots when the parameters are plain
    if useVm then
      if let some c := fd.info.code then
        return ← tryCatch (do
            if fd.kind == .ctor false then
              initFields n { env, thisV, strict := fd.strict, fnObj } fnObj thisV
            let v ← vmEnter n c env capThis thisV args
            modify fun h => { h with depth := h.depth - 1 }
            pure v)
          fun e => do
            modify fun h => { h with depth := saved }
            throw e
    let info := fd.info
    -- `args` is moved into the environment on the plain path (the array must have one owner:
    -- `fillSlots` then grows it in place)
    let (fenv, args) ← if info.plain then do
        let e ← pushEnv { names := info.layout, vals := fillSlots args info.nParams info.layout.size, parent := env,
                          index := info.index }
        pure (e, (#[] : Array Value))
      else do
        let e ← newEnv env
        pure (e, args)
    tryCatch (callBody n fd env capThis capNT home fnObj thisV newTarget args fenv info) fun e => do
      modify fun h => { h with depth := saved }
      if info.frameLocal then releaseEnv fenv
      throw e
termination_by structural n _ _ _ _ _ _ _ _ _ => n

/-- The rest of a call, after the environment is made (`callClosure`). -/
def callBody : Nat → FunDef → Nat → Value → Value → Value → Value → Value → Value → Array Value → Nat → FunInfo → M Value
  | 0, _, _, _, _, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, fd, env, capThis, capNT, home, fnObj, thisV, newTarget, args, fenv, info => do
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
    if !info.plain then
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
    if fd.gen && fd.async then
      let p ← getV n fnObj "prototype"
      let ctx' ← enterBlock n ctx fd.body
      let g ← alloc { proto := if p.isObj then p else .obj r.asyncGenProto, kind := .agen [.block ctx' fd.body] 0 #[] }
      modify fun h => { h with depth := h.depth - 1 }
      return .obj g
    if fd.gen then
      -- a generator function returns its generator, suspended at the start (§27.5.3.1)
      let p ← getV n fnObj "prototype"
      let ctx' ← enterBlock n ctx fd.body
      let g ← alloc { proto := if p.isObj then p else .obj r.generatorProto,
                      kind := .gen [.block ctx' fd.body] 0 }
      modify fun h => { h with depth := h.depth - 1 }
      return .obj g
    if fd.async then
      -- an async function runs until its first await and returns its promise (§27.7.5.1)
      let pid ← newPromise
      let ctx' ← enterBlock n ctx fd.body
      let co ← alloc { kind := .coro [.block ctx' fd.body] pid }
      asyncStep n co (.send .undef)
      modify fun h => { h with depth := h.depth - 1 }
      return .obj pid
    -- a body that is one `return e`: no statement machinery, no completion record
    match fd.body with
    | [.ret (some e)] =>
      let v ← evalExpr n ctx e
      modify fun h => { h with depth := h.depth - 1 }
      if info.frameLocal then releaseEnv fenv
      pure v
    | _ =>
      let c ← evalBody n ctx fd.body
      modify fun h => { h with depth := h.depth - 1 }
      if info.frameLocal then releaseEnv fenv
      match c with
      | .ret v => pure v
      | _ => pure .undef
termination_by structural n _ _ _ _ _ _ _ _ _ _ _ => n

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
      | .proxy t hnd =>
        -- [[Construct]] of a Proxy (§10.5.13): the `construct` trap with the target, the
        -- arguments as an array and the new target, and its answer must be an object; with
        -- no trap, the target constructs
        match ← proxyTrap n hnd "construct" with
        | some trap =>
          let argArray ← newArray args
          let r ← callV n trap hnd #[t, argArray, newTarget]
          if !r.isObj then throwErr .type "proxy [[Construct]] must return an object"
          pure r
        | none => construct n t args newTarget
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
    let env ← newEnv ctx.env
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
      let c ← makeClosure ctx f (decl := true)
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

/-- Environment `e` is the scope of the own name `x` of a function expression (§15.2.5; made by
`makeClosure`): one binding, whose value is the closure that has `e` as its environment. That
binding is immutable and not strict (CreateImmutableBinding(name, false)): an assignment to it
from code that is not strict does nothing, and from strict code it throws a TypeError
(§9.1.1.1.5 SetMutableBinding). A `const` binding throws for both. -/
def fnNameScope (h : HeapOf H) (e : Nat) (x : String) : Bool :=
  let env := h.envs.getD e default
  if env.names.size != 1 || env.names[0]! != x then false else
  match env.vals.getD 0 .undef with
  | .obj id =>
    match (h.obj id).kind with
    | .closure f fenv .. => fenv == e && f.name == some x
    | _ => false
  | _ => false

/-- InitializeReferencedBinding / PutValue for a name (§9.1.1.1.5, §6.2.5.6). -/
def assignName : Nat → Ctx → String → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x, v => do
    let h ← get
    match h.findEnv x 100000 ctx.env with
    | some e =>
      match (h.envs.getD e default).get? x with
      | some b =>
        if !b.init then throwErr .reference s!"Cannot access '{x}' before initialization"
        if !b.mutable then
          if !ctx.strict && fnNameScope h e x then return
          throwErr .type "Assignment to constant variable."
        declare e x { b with v }
      | none =>
        match (h.envs.getD e default).withObj with
        | some o => putV n (.obj o) x v ctx.strict
        | none => pure ()
    | none =>
      let g := h.realm.globalObj
      if !ctx.strict || (h.findProp g x 1000).isSome then putV n (.obj g) x v ctx.strict
      else throwErr .reference s!"{x} is not defined"
termination_by structural n _ _ _ => n

/-- Read a resolved name: slot `idx`, `hops` environments up, when that slot has the name
(`JS/Resolve.lean`); otherwise the plain lookup. -/
def lookupLocal : Nat → Ctx → String → Nat → Nat → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x, hops, idx => do
    let h ← get
    let env := h.envs.getD (h.envUp hops ctx.env) default
    match env.names[idx]?, env.vals[idx]? with
    | some y, some v =>
      if y == x then
        match v with
        | .hole => throwErr .reference s!"Cannot access '{x}' before initialization"
        | _ =>
          if verifyLocals then
            let w ← lookup n ctx x
            if !sameValue v w then throw (.halt s!"verifyLocals: {x} {hops} {idx}")
          pure v
      else lookup n ctx x
    | _, _ => lookup n ctx x
termination_by structural n _ _ _ _ => n

/-- Slot `idx` (`hops` up) lets go of the string `p`, if it holds that string: the only
other reference is the caller's, so an append works in place (`s += x` is linear). -/
def dropSlotStr (ctx : Ctx) (hops idx : Nat) (p : String) : M Unit := do
  let h ← get
  let e := h.envUp hops ctx.env
  match (h.envs.getD e default).vals[idx]? with
  | some (.str y) => if y == p then setSlot e idx .undef
  | _ => pure ()

/-- The binding of the name `x` lets go of the string `p`, if it holds it (a name not
resolved to a slot: top-level code, a `with`): as `dropSlotStr`. -/
def dropNameStr (ctx : Ctx) (x : String) (p : String) : M Unit := do
  let h ← get
  match h.findEnv x 100000 ctx.env with
  | some e =>
    let env := h.envs.getD e default
    if env.withObj.isSome then pure () else
    let i := env.slotN x
    match env.vals[i]? with
    | some (.str y) => if y == p then setSlot e i .undef
    | _ => pure ()
  | none =>
    let g := h.realm.globalObj
    match (h.obj g).props.get? x with
    | some (.data (.str y) true _ _) =>
      if y == p then let _ ← setOwnData g x .undef
    | _ => pure ()

/-- Assign a resolved name; the plain assignment when the hint does not hold. -/
def assignLocal : Nat → Ctx → String → Nat → Nat → Value → M Unit
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x, hops, idx, v => do
    let h ← get
    let e := h.envUp hops ctx.env
    let env := h.envs.getD e default
    match env.names[idx]?, env.vals[idx]? with
    | some y, some old =>
      if y == x then
        if let .hole := old then throwErr .reference s!"Cannot access '{x}' before initialization"
        if !env.mutableAt idx then
          if !ctx.strict && fnNameScope h e x then return
          throwErr .type "Assignment to constant variable."
        if verifyLocals then
          -- the plain path must find the same binding
          if (h.findEnv x 100000 ctx.env) != some e then throw (.halt s!"verifyLocals: {x} {hops} {idx}")
        setSlot e idx v
      else assignName n ctx x v
    | _, _ => assignName n ctx x v
termination_by structural n _ _ _ _ _ => n

/-- The value of a leaf expression that reads no outside state beyond the heap and has no
effects: a literal, a resolved name that holds, `this`. `Value.hole` for anything else (the
caller evaluates the expression the full way, which also reports an uninitialised binding). -/
@[inline] def leafV (h : HeapOf H) (ctx : Ctx) (e : Expr) : Value :=
  match e with
  | .lit v => v
  | .local x hops idx =>
    if verifyLocals then .hole else  -- every read goes through `lookupLocal`, which checks it
    let env := h.envs.getD (h.envUp hops ctx.env) default
    match env.names[idx]?, env.vals[idx]? with
    | some y, some v => if y == x then v else .hole
    | _, _ => .hole
  | .this => ctx.thisV
  | _ => .hole

/-- The value of a name that has no binding and that the global object and its prototype
chain do not have, from the host: the global object's internal slot `namedGetterKey` holds a
function of the name (for a page, the named properties of the Window object, HTML §7.3.3,
decided by `DOM.Named`), and `undefined` from it means "no such name". A realm whose global
has no such slot (a script outside a page, a worker) answers `none` without a call, and a
name that resolves never comes here: this is the path that otherwise throws a ReferenceError
or answers `undefined`. -/
def namedGlobal : Nat → String → M (Option Value)
  | 0, _ => throw (.halt "fuel")
  | n + 1, x => do
    let h ← get
    match h.findProp h.realm.globalObj namedGetterKey 1 with
    | some (.data f ..) =>
      if !f.isObj then return none
      match ← callV n f .undef #[.str x] with
      | .undef => pure none
      | v => pure (some v)
    | _ => pure none
termination_by structural n _ => n

def lookup : Nat → Ctx → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, x => do
    let h ← get
    match h.findEnv x 100000 ctx.env with
    | some e =>
      match (h.envs.getD e default).get? x with
      | some b =>
        if b.init then pure b.v else throwErr .reference s!"Cannot access '{x}' before initialization"
      | none =>
        match (h.envs.getD e default).withObj with
        | some o => getV n (.obj o) x
        | none => pure .undef
    | none =>
      let g := h.realm.globalObj
      match h.findProp g x 1000 with
      | some (.data v ..) => pure v
      | some _ => getV n (.obj g) x
      | none =>
        match ← namedGlobal n x with
        | some v => pure v
        | none => throwErr .reference s!"{x} is not defined"
termination_by structural n _ _ => n

/-- PutValue on an assignment target, after its parts are evaluated. -/
def putTarget : Nat → Ctx → Expr → Option Value → Option String → Value → M Unit
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, target, base, key, v => do
    match target, base, key with
    | .ident x, _, _ => assignName n ctx x v
    | .local x h i, _, _ => assignLocal n ctx x h i v
    | _, some b, some k => putV n b k v ctx.strict
    -- a call as a target (code that is not strict): PutValue of a value that is not a Reference
    | .call .., _, _ => throwErr .reference "Invalid left-hand side in assignment"
    | _, _, _ => throwErr .syntax "Invalid assignment target"
termination_by structural n _ _ _ _ _ => n

/-- Evaluate the base and key of a target (the Reference of §6.2.5). -/
def evalRef : Nat → Ctx → Expr → M (Option Value × Option String)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, ctx, e => do
    match e with
    | .member o k => pure (some (← evalExpr n ctx o), some k)
    -- a super reference as a target (§13.3.7, §6.2.5.6 PutValue): the base is `this`, the
    -- receiver of the [[Set]]. A setter of the parent is found from `this` too, unless the
    -- object or its class overrides it (then that one runs: a known difference).
    | .superMember k => do
      let _ ← homeProto ctx
      pure (some ctx.thisV, some k)
    | .superIndex k => do
      let _ ← homeProto ctx
      pure (some ctx.thisV, some (← toKey n (← evalExpr n ctx k)))
    -- a call as a target (code that is not strict): it is evaluated; it is not a Reference
    | .call .. => do
      let _ ← evalExpr n ctx e
      pure (none, none)
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
    | .local x h i, _, _ => lookupLocal n ctx x h i
    -- a super reference (§13.3.7): [[Get]] on the home object's prototype, receiver `this`
    | .superMember _, _, some k | .superIndex _, _, some k => do getSuper n (← homeProto ctx) k ctx.thisV
    | _, some b, some k => getV n b k
    -- a call as a target was evaluated by `evalRef`; `putTarget` throws next
    | .call .., none, none => pure .undef
    | _, _, _ => evalExpr n ctx e
termination_by structural n _ _ _ _ => n

def evalArgs : Nat → Ctx → List Expr → Array Value → M (Array Value)
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, _, [], acc => pure acc
  | n + 1, ctx, a :: as, acc => do
    match leafV (← get) ctx a with
    | .hole => evalArg n ctx a as acc
    | v => evalArgs n ctx as (acc.push v)
termination_by structural n _ _ _ => n

def evalArg : Nat → Ctx → Expr → List Expr → Array Value → M (Array Value)
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, a, as, acc => do
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
    | .regex p f => newRegExp p f
    | .chain e =>
      tryCatch (evalExpr n ctx e) fun a => match a with
        | .halt w => if w == shortSignal then pure .undef else throw a
        | a => throw a
    | .optBase e =>
      let v ← evalExpr n ctx e
      match v with
      | .undef | .null => throw (.halt shortSignal)
      | _ => pure v
    | .optCallee e => evalExpr n ctx e
    | .bool b => pure (.bool b)
    | .null => pure .null
    | .ident x => lookup n ctx x
    | .local x h i => lookupLocal n ctx x h i
    | .lit v => pure v
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
        checkStrLen (out.utf8ByteSize + str.utf8ByteSize)
        out := Str.jsAppend (Str.jsAppend out str) (cooked.getD (i + 1) "")
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
        if (h.findEnv x 100000 ctx.env).isNone && (h.findProp h.realm.globalObj x 1000).isNone then
          match ← namedGlobal n x with
          | some v => pure (.str (← typeOf v))
          | none => pure (.str "undefined")
        else pure (.str (← typeOf (← lookup n ctx x)))
      | .delete, t =>
        match t with
        | .member _ _ | .index _ _ =>
          let (b, k) ← evalRef n ctx t
          match b, k with
          | some (.obj id), some key =>
            let o ← getObj id
            if let .proxy pt hnd := o.kind then
              match ← proxyTrap n hnd "deleteProperty" with
              | some f =>
                let ok := toBool (← callV n f hnd #[pt, keyValue key])
                if !ok && ctx.strict then throwErr .type s!"'deleteProperty' on proxy: trap returned falsish for property '{key}'"
                return .bool ok
              | none =>
                match pt with
                | .obj tid => deleteOwn tid key; return .bool true
                | _ => return .bool true
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
          match h.findEnv x 100000 ctx.env with
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
    | .binary .inOp (.member (.ident "") k) b =>
      -- `#x in o` (§13.10.1, `privIn`): the private name's key itself
      match ← evalExpr n ctx b with
      | .obj id => pure (.bool (← hasProp n id k))
      | _ => throwErr .type "Cannot use 'in' operator to search for a key in a non-object"
    | .binary op a b =>
      let x ← (match leafV (← get) ctx a with | .hole => evalExpr n ctx a | v => pure v)
      let y ← (match leafV (← get) ctx b with | .hole => evalExpr n ctx b | v => pure v)
      -- the constant values `.bool true`, `.bool false` are not allocated (`if`, not `.bool (p < q)`)
      match op, x, y with
      | .add, .num p, .num q => pure (.num (p + q))
      | .sub, .num p, .num q => pure (.num (p - q))
      | .mul, .num p, .num q => pure (.num (p * q))
      | .div, .num p, .num q => pure (.num (p / q))
      | .lt, .num p, .num q => if p < q then pure (.bool true) else pure (.bool false)
      | .gt, .num p, .num q => if p > q then pure (.bool true) else pure (.bool false)
      | .le, .num p, .num q => if p ≤ q then pure (.bool true) else pure (.bool false)
      | .ge, .num p, .num q => if p ≥ q then pure (.bool true) else pure (.bool false)
      | .seq, _, _ => if strictEq x y then pure (.bool true) else pure (.bool false)
      | .sne, _, _ => if strictEq x y then pure (.bool false) else pure (.bool true)
      | _, _, _ => binop n op x y
    | .logical op a b =>
      let x ← evalExpr n ctx a
      match op with
      | .and => if toBool x then evalExpr n ctx b else pure x
      | .or => if toBool x then pure x else evalExpr n ctx b
      | .coalesce => match x with
        | .undef | .null => evalExpr n ctx b
        | _ => pure x
    | .assign none (.index o k) rhs =>
      -- `a[i] = v`: an element of an Array is written in place, with no key string
      let b ← evalExpr n ctx o
      let kv ← evalExpr n ctx k
      if let .undef := b then throwErr .type "Cannot read properties of undefined"
      if let .null := b then throwErr .type "Cannot read properties of null"
      match b, kv with
      | .obj id, .num x =>
        let v ← evalExpr n ctx rhs
        let isIdx := x ≥ 0 && x < maxIndexF && x.floor == x
        let done ← if isIdx then setElem id x.toUInt64.toNat v else pure false
        if !done then putV n b (keyOfNum x) v ctx.strict
        pure v
      | _, _ =>
        let key ← toKey n kv
        let v ← evalExpr n ctx rhs
        putV n b key v ctx.strict
        pure v
    | .assign none (.member o k) rhs =>
      let b ← (match leafV (← get) ctx o with | .hole => evalExpr n ctx o | v => pure v)
      let v ← (match leafV (← get) ctx rhs with | .hole => evalExpr n ctx rhs | v => pure v)
      putV n b k v ctx.strict
      pure v
    | .assign (some .add) (.local x h i) rhs =>
      let old ← lookupLocal n ctx x h i
      let r ← (match leafV (← get) ctx rhs with | .hole => evalExpr n ctx rhs | v => pure v)
      -- a string held by this binding alone is appended to in place: the slot lets go first
      let v ← match old, r with
        | .num p, .num q => pure (.num (p + q))
        | .str p, .str q => checkStrLen (p.utf8ByteSize + q.utf8ByteSize); dropSlotStr ctx h i p; pure (.str (Str.jsAppend p q))
        | .str p, .num q => dropSlotStr ctx h i p; pure (.str (Str.jsAppend p (numToString q)))
        | _, _ => binop n .add old r
      assignLocal n ctx x h i v
      pure v
    | .assign (some .add) (.ident x) rhs =>
      let old ← lookup n ctx x
      let r ← (match leafV (← get) ctx rhs with | .hole => evalExpr n ctx rhs | v => pure v)
      let v ← match old, r with
        | .num p, .num q => pure (.num (p + q))
        | .str p, .str q => checkStrLen (p.utf8ByteSize + q.utf8ByteSize); dropNameStr ctx x p; pure (.str (Str.jsAppend p q))
        | .str p, .num q => dropNameStr ctx x p; pure (.str (Str.jsAppend p (numToString q)))
        | _, _ => binop n .add old r
      assignName n ctx x v
      pure v
    | .assign (some op) (.local x h i) rhs =>
      let old ← lookupLocal n ctx x h i
      let r ← (match leafV (← get) ctx rhs with | .hole => evalExpr n ctx rhs | v => pure v)
      let v ← match op, old, r with
        | .add, .num p, .num q => pure (.num (p + q))
        | .sub, .num p, .num q => pure (.num (p - q))
        | _, _, _ => binop n op old r
      assignLocal n ctx x h i v
      pure v
    | .assign none target rhs =>
      let (b, k) ← evalRef n ctx target
      let v ← match target, rhs with
        | .ident x, .func f | .local x _ _, .func f =>
          if f.name.isNone then makeClosure ctx f x else evalExpr n ctx rhs
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
    | .update pre inc (.local x h i) =>
      match ← lookupLocal n ctx x h i with
      | .num old =>
        let nv := if inc then old + 1 else old - 1
        assignLocal n ctx x h i (.num nv)
        pure (.num (if pre then nv else old))
      | p =>
        match ← toPrim n p "number" with
        | .big big =>
          let nv := if inc then big + 1 else big - 1
          assignLocal n ctx x h i (.big nv)
          pure (.big (if pre then nv else big))
        | p =>
          let old ← toNum n p
          let nv := if inc then old + 1 else old - 1
          assignLocal n ctx x h i (.num nv)
          pure (.num (if pre then nv else old))
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
    | .cond c t f =>
      let cv ← (match leafV (← get) ctx c with | .hole => evalExpr n ctx c | v => pure v)
      if toBool cv then evalExpr n ctx t else evalExpr n ctx f
    | .seq a b => let _ ← evalExpr n ctx a; evalExpr n ctx b
    | .call callee args =>
      let (f, thisV) ← match callee with
        | .optCallee inner =>
          let (f, t) ← match inner with
            | .member o k => do let b ← evalExpr n ctx o; pure (← getV n b k, b)
            | .index o k => do
              let b ← evalExpr n ctx o
              let key ← toKey n (← evalExpr n ctx k)
              pure (← getV n b key, b)
            | _ => do pure (← evalExpr n ctx inner, Value.undef)
          match f with
          | .undef | .null => throw (.halt shortSignal)
          | _ => pure (f, t)
        | .member o k =>
          let b ← (match leafV (← get) ctx o with | .hole => evalExpr n ctx o | v => pure v)
          let f ← (match (← get).fastGetV b k with | .hole => getV n b k | v => pure v)
          pure (f, b)
        | .index o k =>
          let b ← evalExpr n ctx o
          let key ← toKey n (← evalExpr n ctx k)
          pure (← getV n b key, b)
        | .superMember k =>
          let proto ← homeProto ctx
          pure (← getSuper n proto k ctx.thisV, ctx.thisV)
        | .local x h i => pure (← lookupLocal n ctx x h i, Value.undef)
        | .ident x =>
          let h ← get
          let thisV := match h.findEnv x 100000 ctx.env with
            | some e => match (h.envs.getD e default).withObj with
              | some o => if (h.envs.getD e default).has x then Value.undef else .obj o
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
          | .ident x | .local x .. => x | .member _ k => k | _ => "expression"
        throwErr .type s!"{what} is not a function"
      callV n f thisV argv
    | .new callee args =>
      let f ← evalExpr n ctx callee
      let argv ← evalArgs n ctx args #[]
      if !(← isConstructor f) then
        let what := match callee with
          | .ident x | .local x .. => x | .member _ k => k | _ => "expression"
        throwErr .type s!"{what} is not a constructor"
      construct n f argv f
    | .member o k =>
      let b ← (match leafV (← get) ctx o with | .hole => evalExpr n ctx o | v => pure v)
      match (← get).fastGetV b k with
      | .hole => getV n b k
      | v => pure v
    | .index o k =>
      let b ← (match leafV (← get) ctx o with | .hole => evalExpr n ctx o | v => pure v)
      let kv ← (match leafV (← get) ctx k with | .hole => evalExpr n ctx k | v => pure v)
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
    let old := (← get).envs.getD ctx.env default
    -- all the names of the record are the loop's (the record is the loop's alone): a copy
    let e ← pushEnv (if names.isEmpty then { parent := old.parent } else old)
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
    let ctx' ← bindIter n ctx kind target (keyStrV k)
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
      let e ← newEnv ctx.env
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
    | .ret (some e) =>
      let v ← (match leafV (← get) ctx e with | .hole => evalExpr n ctx e | v => pure v)
      pure (.ret v)
    | .ifS c t f =>
      let cv ← (match leafV (← get) ctx c with | .hole => evalExpr n ctx c | v => pure v)
      if toBool cv then evalStmt n ctx [] t
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
        let env ← newEnv ctx.env
        let ctx' := { ctx with env }
        for d in ds do
          for x in d.names do declare env x { v := .undef, mutable := k == .letK, init := false }
        evalDecls n ctx' k ds
        let names := ds.flatMap Decl.names
        forLoop n ctx' labels (if k == .letK then names else []) test update body true
      | some (.letOnce ds) =>
        let env ← newEnv ctx.env
        let ctx' := { ctx with env }
        for d in ds do
          for x in d.names do declare env x { v := .undef, mutable := true, init := false }
        evalDecls n ctx' .letK ds
        forLoop n ctx' labels [] test update body true
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
      let env ← pushEnv { parent := ctx.env, withObj := some id }
      evalStmt n { ctx with env } [] body
    | .classDecl name c =>
      let v ← evalClass n ctx c name
      declare ctx.env name { v }
      pure .normal
    | .compiled c s =>
      if useVm then
        let _ ← vmEnter n c ctx.env ctx.thisV ctx.thisV #[]
        pure .normal
      else evalStmt n ctx labels s
    | .block ss => evalBlock n ctx ss
    | .blockF ss =>
      -- no closure holds this block's environment: its slot is reused on a normal end
      -- (after a throw it stays allocated, which is only memory)
      let ctx' ← enterBlock n ctx ss
      let c ← evalStmts n ctx' ss
      if ctx'.env != ctx.env then releaseEnv ctx'.env
      pure c
    | .throwS e => throw (.throw (← evalExpr n ctx e))
    | .tryS body param handler fin =>
      let r ← tryCatch (do let c ← evalBlock n ctx body; pure (Except.ok c))
        (fun a => pure (Except.error a))
      let r ← match r, handler with
        | .error (.throw v), some hs =>
          tryCatch (do
            let env ← newEnv ctx.env
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
      if l == annexBLabel then
        -- Annex B.3.3.1: when a block's function declaration is evaluated, the `var`
        -- binding of its name gets the function (the value the block's binding has now).
        -- The parser puts this statement after such a declaration; the `var` binding is the
        -- nearest one above the block's environment, or the global object's property.
        match body with
        | .expr (.ident x) | .expr (.local x _ _) =>
          let v ← evalExpr n ctx (match body with | .expr e => e | _ => .null)
          let parent := ((← get).envs.getD ctx.env default).parent
          assignName n { ctx with env := parent, strict := false } x v
        | _ => pure ()
        return .normal
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
    let cenv ← newEnv ctx.env
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
          FunDef.mk none [] (some (.id "args")) [.expr (.superCall [.spread (.ident "args")])] [] false true (.ctor true) false false {}
        else FunDef.mk none [] none [] [] false true (.ctor false) false false {}
    let cname := name.getD nameHint
    let fid ← alloc { proto := ctorParent, kind := .closure fd cenv .undef .undef (.obj proto) #[] }
    defineOwn fid "length" (.data (.num (Float.ofNat fd.expectedArgs)) false false true)
    defineOwn fid "name" (.data (.str cname) false false true)
    defineOwn fid "prototype" (.data (.obj proto) false false false)
    setHidden proto "constructor" (.obj fid)
    -- the class binding is initialised before static fields and blocks run (§15.7.14)
    let statics := members.filter fun m => match m with
      | .mk true .field .. | .mk true .staticBlock .. => true
      | _ => false
    let others := members.filter fun m => match m with
      | .mk true .field .. | .mk true .staticBlock .. => false
      | _ => true
    let fields ← defineMembers n cctx fid proto others #[]
    modifyObj fid fun o => match o.kind with
      | .closure f e t nt h _ => { o with kind := .closure f e t nt h fields }
      | k => { o with kind := k }
    if let some x := name then declare cenv x { v := .obj fid, mutable := false }
    let _ ← defineMembers n cctx fid proto statics #[]
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
    | .staticBlock =>
      let init ← makeClosure ctx f "" (.obj fid)
      let _ ← callV n init (.obj fid) #[]
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
      match (parseScript code ctx.strict (evalCode := true)).map Resolve.script with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok sc =>
        let env ← newEnv ctx.env
        let ectx := { ctx with env, strict := sc.strict }
        -- var declarations of sloppy eval code go to the caller's variable scope
        for x in sc.vars do
          if sc.strict then declare env x { v := .undef }
          else if ((← get).findEnv x 100000 ctx.env).isNone then
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
        match ← asyncDelegate? it with
        | some (iter, nextM, ph) =>
          -- `yield*` in an async generator: `v` is what `next(v)` sent (phase 0) or the
          -- awaited result of the inner iterator's method (phases 1 to 4)
          -- the answer: 0 await this, 1 the delegation ended with this value, 2 yield this,
          -- 3 return this
          let r ← tryCatch (do
              if ph == 0 then
                let res ← callV n nextM iter #[v]
                setDelegatePhase it 1
                pure (Except.ok ((0 : Nat), res))
              else
                setDelegatePhase it 0
                if ph == 4 then pure (Except.ok (3, v))
                else
                  if !v.isObj then throwErr .type "Iterator result is not an object"
                  if ph == 3 then throwErr .type "The iterator does not provide a 'throw' method"
                  let done := toBool (← getV n v "done")
                  let x ← getV n v "value"
                  pure (Except.ok (if !done then 2 else if ph == 2 then 3 else 1, x)))
            (fun a => pure (Except.error a))
          match r with
          | .error (.throw e) => genUnwind n rest (.throw e)
          | .error a => throw a
          | .ok (0, res) => pure (.awaited res (f :: rest))
          | .ok (1, x) => genRun n (.resume ctx target :: rest) (.send x)
          | .ok (2, x) => pure (.yielded x (f :: rest))
          | .ok (_, x) => genUnwind n rest (.ret x)
        | none =>
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
      if let some (.call (.ident "%await") [e]) := arg then
        return ← match ← genEval n ctx e with
          | .error x => genUnwind n rest (.throw x)
          | .ok v =>
            if delegate then do
              -- `yield*` in an async generator: GetIterator(v, async), then the record
              let r ← tryCatch (do
                  let iter ← callNative n (.x (.forAwait 0)) .undef #[v] none
                  let nextM ← getV n iter "next"
                  let rec ← alloc { proto := .null }
                  setHidden rec delegIterKey iter
                  setHidden rec delegNextKey nextM
                  setHidden rec delegPhaseKey (.num 0)
                  pure (Except.ok (Value.obj rec)))
                (fun a => pure (Except.error a))
              match r with
              | .error (.throw x) => genUnwind n rest (.throw x)
              | .error a => throw a
              | .ok rec => genRun n (.delegate ctx rec target :: rest) (.send .undef)
            else pure (.awaited v (.resume ctx target :: rest))
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
    -- a `yield` whose operand holds a `yield` (`yield await x`, `await (yield x)`): the inner
    -- ones are lifted first (`liftStmt`)
    let nested : Bool := match s with
      | .expr (.yieldE _ (some a)) | .expr (.assign none _ (.yieldE _ (some a)))
      | .decl _ [Decl.mk _ (some (.yieldE _ (some a)))] | .ret (some (.yieldE _ (some a))) => a.hasYield
      | _ => false
    if nested then return ← genLift n ctx s rest
    match s with
    | .expr (.yieldE d arg) => yieldAt arg d none
    | .expr (.assign none t (.yieldE d arg)) =>
      match t with
      | .ident x => yieldAt arg d (some (.id x, .assign))
      | .member .. | .index .. => yieldAt arg d (some (.target t, .assign))
      | _ => genLift n ctx s rest
    | .decl k [Decl.mk p (some (.yieldE d arg))] =>
      let m : BindMode := match k with
        | .var => .var
        | .letK => .declare ctx.env true
        | .constK => .declare ctx.env false
      yieldAt arg d (some (p, m))
    | .ret (some (.yieldE d arg)) =>
      -- `return yield x`: the value sent back is the return value. `return await x` in an
      -- async generator (the `%await` form) is an await, not a yield.
      let _ := d
      let (arg, isAwait) := match arg with
        | some (.call (.ident "%await") [e]) => (some e, true)
        | a => (a, false)
      let v ← match arg with
        | some e => genEval n ctx e
        | none => pure (.ok .undef)
      match v with
      | .error e => genUnwind n rest (.throw e)
      | .ok v =>
        let fs := .resume ctx (some (.id "%ret", .declare ctx.env true)) ::
          .block ctx [.ret (some (.ident "%ret"))] :: rest
        pure (if isAwait then .awaited v fs else .yielded v fs)
    | .block ss | .blockF ss =>
      let ctx' ← enterBlock n ctx ss
      genRun n (.block ctx' ss :: rest) (.send .undef)
    | .ifS c t e =>
      if c.hasYield then genLift n ctx s rest else
      match ← genEval n ctx c with
      | .error x => genUnwind n rest (.throw x)
      | .ok v =>
        if toBool v then genRun n (.block ctx [t] :: rest) (.send .undef)
        else match e with
          | some e => genRun n (.block ctx [e] :: rest) (.send .undef)
          | none => genRun n rest (.send .undef)
    | .whileS c body =>
      if c.hasYield then
        -- `while (c) b` is `while (true) { if (!c) break; b }`: `c`'s yields are then lifted
        genEnter n ctx labels (.whileS (.bool true)
          (.block [.ifS (.unary .not c) (.brk none) none, body])) rest
      else genRun n (.loopW ctx labels c body :: rest) (.send .undef)
    | .doWhile body c =>
      if c.hasYield then
        -- a flag makes the test run after the body, also after `continue`
        let f := s!"%dw{(← get).envs.size}"
        let loop : Stmt := .whileS (.bool true) (.block [
          .ifS (.ident f) (.ifS (.unary .not c) (.brk none) none) none,
          .expr (.assign none (.ident f) (.bool true)), body])
        genRun n (.block ctx [.decl .letK [Decl.mk (.id f) (some (.bool false))],
          labels.foldr .labeled loop] :: rest) (.send .undef)
      else genRun n (.block ctx [body] :: .loopDo ctx labels body c :: rest) (.send .undef)
    | .forS init test update body =>
      let initYields := match init with
        | some (.expr e) => e.hasYield
        | some (.decl _ ds) | some (.letOnce ds) => ds.any Decl.hasYield
        | none => false
      if initYields then
        match init with
        | some (.expr e) =>
          genRun n (.block ctx [.expr e, labels.foldr .labeled (.forS none test update body)] :: rest) (.send .undef)
        | some (.decl .var ds) =>
          genRun n (.block ctx [.decl .var ds, labels.foldr .labeled (.forS none test update body)] :: rest) (.send .undef)
        | _ => genUnsupported n rest
      else if test.any Expr.hasYield || update.any Expr.hasYield then
        -- the test and update move into the body, after a flag for the first pass, so
        -- `continue` still runs the update
        let f := s!"%fy{(← get).envs.size}"
        let upd : List Stmt := match update with
          | some u => [.ifS (.ident f) (.expr u) none]
          | none => []
        let tst : List Stmt := match test with
          | some t => [.ifS (.unary .not t) (.brk none) none]
          | none => []
        let loop : Stmt := .forS init none none
          (.block (upd ++ [.expr (.assign none (.ident f) (.bool true))] ++ tst ++ [body]))
        genRun n (.block ctx [.decl .letK [Decl.mk (.id f) (some (.bool false))],
          labels.foldr .labeled loop] :: rest) (.send .undef)
      else
      let r ← tryCatch (do
          match init with
          | some (.decl .var ds) => evalDecls n ctx .var ds; pure (Except.ok (ctx, ([] : List String)))
          | some (.decl k ds) =>
            let env ← newEnv ctx.env
            let ctx' := { ctx with env }
            for d in ds do
              for x in d.names do declare env x { v := .undef, mutable := k == .letK, init := false }
            evalDecls n ctx' k ds
            pure (Except.ok (ctx', if k == .letK then ds.flatMap Decl.names else []))
          | some (.letOnce ds) =>
            let env ← newEnv ctx.env
            let ctx' := { ctx with env }
            for d in ds do
              for x in d.names do declare env x { v := .undef, mutable := true, init := false }
            evalDecls n ctx' .letK ds
            pure (Except.ok (ctx', []))
          | some (.expr e) => let _ ← evalExpr n ctx e; pure (Except.ok (ctx, []))
          | none => pure (Except.ok (ctx, [])))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw x) => genUnwind n rest (.throw x)
      | .error a => throw a
      | .ok (ctx', perIter) => genRun n (.loopFor ctx' labels perIter test update body true :: rest) (.send .undef)
    | .forOf kind target obj body =>
      if obj.hasYield then
        -- the iterable's yields first, in a temporary
        let t := s!"%it{(← get).envs.size}"
        genRun n (.block ctx [.decl .letK [Decl.mk (.id t) (some obj)],
          labels.foldr .labeled (.forOf kind target (.ident t) body)] :: rest) (.send .undef)
      else
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
    | .switchS d cs =>
      -- a `switch` with a `yield` or `await` in it: the same statements without `switch`
      match switchStmts (← get).envs.size labels d cs with
      | some s' => genEnter n ctx [] s' rest
      | none => genUnsupported n rest
    | _ => genLift n ctx s rest
termination_by structural n _ _ _ _ => n

def genUnsupported : Nat → List GFrame → M GOut
  | 0, _ => throw (.halt "fuel")
  | n + 1, rest => do
    genUnwind n rest (.throw (← mkError .syntax "yield in this position is not supported"))
termination_by structural n _ => n

/-- A statement whose `yield`s are inside expressions: lift them, or refuse. -/
def genLift : Nat → Ctx → Stmt → List GFrame → M GOut
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, ctx, s, rest => do
    match liftStmt (← get).envs.size s with
    | some ss => genRun n (.block ctx ss :: rest) (.send .undef)
    | none => genUnsupported n rest
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
      if let some (iter, _, ph) := ← asyncDelegate? it then
        -- `yield*` in an async generator. Phase 0: `throw(v)` came to the `yield`; the inner
        -- `throw` is called and awaited, or the iterator is closed and a TypeError follows.
        -- Other phases: the awaited promise was rejected.
        if ph != 0 then
          setDelegatePhase it 0
          return ← genUnwind n rest c
        let r ← tryCatch (do
            let th ← getV n iter "throw"
            match th with
            | .undef | .null =>
              let rt ← getV n iter "return"
              match rt with
              | .undef | .null => throwErr .type "The iterator does not provide a 'throw' method"
              | _ =>
                let res ← callV n rt iter #[]
                setDelegatePhase it 3
                pure (Except.ok res)
            | _ =>
              let res ← callV n th iter #[v]
              setDelegatePhase it 1
              pure (Except.ok res))
          (fun a => pure (Except.error a))
        return ← match r with
          | .error (.throw e) => genUnwind n rest (.throw e)
          | .error a => throw a
          | .ok res => pure (.awaited res (f :: rest))
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
      if let some (iter, _, ph) := ← asyncDelegate? it then
        -- `return(v)` came to the `yield` of an async `yield*`: the inner `return` is called
        -- and awaited; with none, `v` is awaited and returned
        if ph != 0 then
          setDelegatePhase it 0
          return ← genUnwind n rest c
        let r ← tryCatch (do
            let rt ← getV n iter "return"
            match rt with
            | .undef | .null =>
              setDelegatePhase it 4
              pure (Except.ok v)
            | _ =>
              let res ← callV n rt iter #[v]
              setDelegatePhase it 2
              pure (Except.ok res))
          (fun a => pure (Except.error a))
        return ← match r with
          | .error (.throw e) => genUnwind n rest (.throw e)
          | .error a => throw a
          | .ok res => pure (.awaited res (f :: rest))
      let rt ← getV n it "return"
      match rt with
      | .undef | .null => genUnwind n rest c
      | _ =>
        let res ← callV n rt it #[v]
        if !res.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n res "done") then genUnwind n rest (.ret (← getV n res "value"))
        else pure (.yielded (← getV n res "value") (f :: rest))
    | .tryF ctx param (some hs) fin 0, .throw v =>
      let env ← newEnv ctx.env
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

/-- Run an async function's frames to its next await or its end (§27.7.5.3 Await). -/
def asyncStep : Nat → Nat → GInput → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, co, input => do
    match (← getObj co).kind with
    | .coro frames pid =>
      let r ← tryCatch (do pure (Except.ok (← genRun n frames input))) (fun a => pure (Except.error a))
      match r with
      | .error (.throw e) => modifyObj co (fun o => { o with kind := .coro [] pid }); rejectPromise n pid e
      | .error a => throw a
      | .ok (.done v) => modifyObj co (fun o => { o with kind := .coro [] pid }); resolvePromise n pid v
      | .ok (.yielded v fs) | .ok (.awaited v fs) =>
        modifyObj co fun o => { o with kind := .coro fs pid }
        let p ← promiseResolve n v
        let r ← realm
        let onF ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .asyncResume) .undef #[.obj co, .num 0] }
        let onR ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .asyncResume) .undef #[.obj co, .num 1] }
        performThen n p (.obj onF) (.obj onR) .undef
    | _ => pure ()
termination_by structural n _ _ => n

/-- PromiseResolve (§27.2.4.7.1) with the intrinsic Promise. -/
def promiseResolve : Nat → Value → M Nat
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .obj id =>
      match (← getObj id).kind with
      | .promise .. =>
        let c ← getV n v "constructor"
        if strictEq c (.obj (← realm).promiseCtor) then return id
        let p ← newPromise
        resolvePromise n p v
        pure p
      | _ =>
        let p ← newPromise
        resolvePromise n p v
        pure p
    | _ =>
      let p ← newPromise
      resolvePromise n p v
      pure p
termination_by structural n _ => n

/-- Promise Resolve Functions (§27.2.1.3.2), without the AlreadyResolved check. -/
def resolvePromise : Nat → Nat → Value → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, pid, x => do
    match x with
    | .obj xid =>
      if xid == pid then
        return ← rejectPromise n pid (← mkError .type "Chaining cycle detected for promise")
      let r ← tryCatch (do pure (Except.ok (← getV n x "then"))) (fun a => pure (Except.error a))
      match r with
      | .error (.throw e) => rejectPromise n pid e
      | .error a => throw a
      | .ok th =>
        if ← isCallable th then
          enqueue (← nativeFn .promiseThenableJob) #[.obj pid, x, th]
        else settlePromise n pid 1 x
    | _ => settlePromise n pid 1 x
termination_by structural n _ _ => n

def rejectPromise : Nat → Nat → Value → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, pid, e => settlePromise n pid 2 e
termination_by structural n _ _ => n

/-- FulfillPromise / RejectPromise (§27.2.1.4, §27.2.1.7): reactions become jobs. -/
def settlePromise : Nat → Nat → Nat → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, pid, st, v => do
    match (← getObj pid).kind with
    | .promise 0 _ reactions _ =>
      modifyObj pid fun o => { o with kind := .promise st v #[] true }
      let job ← nativeFn .promiseReactionJob
      for (onF, onR, derived) in reactions do
        enqueue job #[if st == 1 then onF else onR, derived, v, .bool (st == 2)]
    | _ => pure ()
termination_by structural n _ _ _ => n

/-- PerformPromiseThen (§27.2.5.4.1). -/
def performThen : Nat → Nat → Value → Value → Value → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | _ + 1, pid, onF, onR, derived => do
    match (← getObj pid).kind with
    | .promise 0 v rs l => modifyObj pid fun o => { o with kind := .promise 0 v (rs.push (onF, onR, derived)) l }
    | .promise st v _ _ =>
      enqueue (← nativeFn .promiseReactionJob) #[if st == 1 then onF else onR, derived, v, .bool (st == 2)]
    | _ => pure ()
termination_by structural n _ _ _ _ => n

/-- Run the queued jobs, oldest first, until none is left (a microtask checkpoint). -/
def runJobs : Nat → M Unit
  | 0 => throw (.halt "fuel")
  | n + 1 => do
    let h ← get
    if h.jobHead ≥ h.jobs.size then
      set { h with jobs := #[], jobHead := 0 }
      return
    let (f, args) := h.jobs[h.jobHead]!
    -- the jobs already run leave the queue once they are half of it: a chain of jobs that
    -- each queue the next (a loop of awaits) does not keep every job it ever ran
    let h := if h.jobHead ≥ 4096 && 2 * (h.jobHead + 1) ≥ h.jobs.size then
        { h with jobs := h.jobs.extract (h.jobHead + 1) h.jobs.size, jobHead := 0, jobsRun := h.jobsRun + 1 }
      else { h with jobHead := h.jobHead + 1, jobsRun := h.jobsRun + 1 }
    set h
    tick
    let r ← tryCatch (do let _ ← callV n f .undef args; pure none) (fun a => pure (some a))
    match r with
    | some (.halt w) => throw (.halt w)
    | _ => runJobs n
termination_by structural n => n

/-- An iterator result object (§7.4.14 CreateIteratorResultObject). -/
def iterResult : Nat → Value → Bool → M Value
  | _, v, done => do
    let o ← newObject
    defineOwn o "value" (.data v true true true)
    defineOwn o "done" (.data (.bool done) true true true)
    pure (.obj o)
termination_by structural n _ _ => n

/-- Serve the request queue of an async generator (§27.6.3.7 AsyncGeneratorDrainQueue). -/
def agenDrain : Nat → Nat → M Unit
  | 0, _ => throw (.halt "fuel")
  | n + 1, gid => do
    match (← getObj gid).kind with
    | .agen frames st queue =>
      if st == 2 || queue.isEmpty then return
      let (input, pid) := queue.getD 0 (GInput.send .undef, 0)
      let pop : M Unit := modifyObj gid fun o => match o.kind with
        | .agen fs s q => { o with kind := .agen fs s (q.extract 1 q.size) }
        | k => { o with kind := k }
      let finished := st == 3 || (st == 0 && (match input with | .send _ => false | _ => true))
      if finished then
        match input with
        | .retV v =>
          -- AsyncGeneratorAwaitReturn (§27.6.3.9): the value is awaited while the request
          -- stays at the head of the queue; then the result, or the rejection (modes 4, 5)
          modifyObj gid fun o => { o with kind := .agen [] 2 ((match o.kind with | .agen _ _ q => q | _ => #[])) }
          agenAwait n gid v 4 5
        | _ =>
          modifyObj gid fun o => { o with kind := .agen [] 3 ((match o.kind with | .agen _ _ q => q | _ => #[])) }
          pop
          match input with
          | .throwV e => rejectPromise n pid e
          | _ => resolvePromise n pid (← iterResult n .undef true)
          agenDrain n gid
      else
        modifyObj gid fun o => { o with kind := .agen frames 2 ((match o.kind with | .agen _ _ q => q | _ => #[])) }
        match input with
        | .retV v =>
          -- a return completion at a `yield` (§27.6.3.8 AsyncGeneratorYield, step 12): the
          -- value is awaited first; a rejection is thrown into the generator (modes 3, 1)
          agenAwait n gid v 3 1
        | _ => agenRun n gid frames input
    | _ => pure ()
termination_by structural n _ => n

/-- Await `v` for async generator `gid` (§27.7.5.3 Await): `agenResume` runs with mode `onF`
and the value when it is fulfilled, with mode `onR` and the reason when it is rejected. What
PromiseResolve throws (a poisoned `constructor`) is a rejection. -/
def agenAwait : Nat → Nat → Value → Nat → Nat → M Unit
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, gid, v, onF, onR => do
    let p ← tryCatch (promiseResolve n v) (fun a => match a with
      | .throw e => do
        let p ← newPromise
        rejectPromise n p e
        pure p
      | a => throw a)
    let rr ← realm
    let f ← nativeFn .agenResume
    let onF ← alloc { proto := .obj rr.functionProto, kind := .bound f .undef #[.obj gid, .num (Float.ofNat onF)] }
    let onR ← alloc { proto := .obj rr.functionProto, kind := .bound f .undef #[.obj gid, .num (Float.ofNat onR)] }
    performThen n p (.obj onF) (.obj onR) .undef
termination_by structural n _ _ _ _ => n

/-- Run an async generator from a resumption, for the request at the head of its queue. -/
def agenRun : Nat → Nat → List GFrame → GInput → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, gid, frames, input => do
    let r ← tryCatch (do pure (Except.ok (← genRun n frames input))) (fun a => pure (Except.error a))
    let q := match (← getObj gid).kind with | .agen _ _ q => q | _ => #[]
    let pid := (q.getD 0 (GInput.send .undef, 0)).2
    let set (fs : List GFrame) (s : Nat) (q : Array (GInput × Nat)) : M Unit :=
      modifyObj gid fun o => { o with kind := .agen fs s q }
    match r with
    | .error (.throw e) => set [] 3 (q.extract 1 q.size); rejectPromise n pid e; agenDrain n gid
    | .error a => throw a
    | .ok (.done v) => set [] 3 (q.extract 1 q.size); resolvePromise n pid (← iterResult n v true); agenDrain n gid
    | .ok (.yielded v fs) =>
      -- `yield v` awaits `v` (§27.6.3.8 AsyncGeneratorYield: `yield` is `yield await`); a
      -- value that `yield*` passes on from its iterator is not awaited again (§15.5.5)
      let raw ← match fs with
        | .delegate _ it _ :: _ => do pure (← asyncDelegate? it).isSome
        | _ => pure false
      if raw then
        set fs 1 (q.extract 1 q.size); resolvePromise n pid (← iterResult n v false); agenDrain n gid
      else
        set fs 2 q
        agenAwait n gid v 2 1
    | .ok (.awaited v fs) =>
      set fs 2 q
      agenAwait n gid v 0 1
termination_by structural n _ _ _ => n

/-- Built-in functions. `newTarget` is set for `new`. -/
def callNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args, newTarget => do
    -- A built-in's loops are over its receiver and arguments: one step per call is not
    -- enough when it walks them, so the call takes steps for their size (`sizeCost`). The
    -- String methods that index an ASCII receiver in constant time (`charAt`, `charCodeAt`,
    -- `at`, `codePointAt`) or copy only their result (`slice`, `substring`, `substr`, which
    -- take steps for the result) do not walk it, and take no steps for it.
    let recvCost ← if indexesReceiver id thisV then pure 0 else
      match ← cachedReceiverCost id thisV with
      | some c => pure c
      | none => sizeCost thisV
    let argsCost ← if (← subjectCached id args) then pure 0
      else args.foldlM (fun acc a => do pure (acc + (← sizeCost a))) 0
    charge (recvCost + args.size / 64 + argsCost)
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    let id_ := id
    match id with
    | .print =>
      let parts ← args.toList.mapM (toStr n)
      modify fun h => { h with out := h.out.push (Str.toHost (" ".intercalate parts)) }
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
      match o.kind with
      | .proxy .. | .typed .. =>
        let ks := (← ownKeysOf n id).filter (fun k => !isSymKey k && !isPrivKey k)
        let ks ← ks.filterM fun k => do pure (match ← ownDesc n id k with | some p => p.enumerable | none => false)
        newArray (ks.map keyStrV)
      | _ =>
        let ks := o.ownStrKeys.filter fun k => match o.getOwn k with
          | some p => p.enumerable | none => false
        newArray (ks.map keyStrV)
    | .objectGetOwnPropertyNames =>
      let id ← toObj n a0
      newArray ((← ownKeysOf n id).filter (fun k => !isSymKey k && !isPrivKey k) |>.map keyStrV)
    | .objectGetPrototypeOf =>
      -- [[GetPrototypeOf]] (§10.1.1, §10.5.1)
      let id ← toObj n a0
      let o ← getObj id
      match o.kind with
      | .proxy t hnd =>
        let .obj _ := t | throwErr .type "Cannot perform 'getPrototypeOf' on a proxy that has been revoked"
        match ← proxyTrap n hnd "getPrototypeOf" with
        | none => callNative n .objectGetPrototypeOf .undef #[t] none
        | some f =>
          let p ← callV n f hnd #[t]
          if !(p.isObj || p matches .null) then
            throwErr .type "'getPrototypeOf' on proxy: the trap returned neither an object nor null"
          if !toBool (← callNative n .objectIsExtensible .undef #[t] none) then
            if !sameValue p (← callNative n .objectGetPrototypeOf .undef #[t] none) then
              throwErr .type "'getPrototypeOf' on proxy: the target is not extensible and has another prototype"
          pure p
      | _ => pure o.proto
    | .objectSetPrototypeOf =>
      -- §20.1.2.23
      match a0 with
      | .undef | .null => throwErr .type "Object.setPrototypeOf called on null or undefined"
      | _ =>
        match a1 with
        | .obj _ | .null =>
          match a0 with
          | .obj _ =>
            if toBool (← callNative n (.reflect 2) .undef #[a0, a1] none) then pure a0
            else throwErr .type "Object.setPrototypeOf: the prototype of this object cannot be changed"
          | _ => pure a0
        | _ => throwErr .type "Object prototype may only be an Object or null" 
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
      match ← ownDesc n id k with
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
        let props := o.props.mapValues (fun p => (match p with
          | .data v _ e _ => .data v false e false
          | .acc g s e _ => .acc g s e false))
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
      match a0 with
      | .obj _ =>
        if !toBool (← callNative n (.reflect 12) .undef #[a0] none) then
          throwErr .type "Object.preventExtensions: the object refused"
        pure a0
      | _ => pure a0
    | .objectIsExtensible =>
      -- [[IsExtensible]] (§10.1.3, §10.5.3): a Proxy asks its trap, whose answer must be the target's
      match a0 with
      | .obj id0 =>
        let mut cur := id0
        for _ in [0:64] do
          match (← getObj cur).kind with
          | .proxy t hnd =>
            let .obj tid := t | throwErr .type "Cannot perform 'isExtensible' on a proxy that has been revoked"
            match ← proxyTrap n hnd "isExtensible" with
            | some f =>
              let b := toBool (← callV n f hnd #[t])
              if b != toBool (← callNative n .objectIsExtensible .undef #[t] none) then
                throwErr .type "'isExtensible' on proxy: the trap's answer is not the target's"
              return .bool b
            | none => cur := tid
          | _ => return .bool (← getObj cur).extensible
        pure (.bool false)
      | _ => pure (.bool false)
    | .objectProtoHasOwnProperty =>
      let k ← toKey n a0
      let id ← toObj n thisV
      pure (.bool (← ownDesc n id k).isSome)
    | .objectProtoPropertyIsEnumerable =>
      let k ← toKey n a0
      let id ← toObj n thisV
      pure (.bool (match ← ownDesc n id k with | some p => p.enumerable | none => false))
    -- Annex B.2.2.2 and B.2.2.3: __defineGetter__ (P, getter), __defineSetter__ (P, setter):
    -- DefinePropertyOrThrow(O, key, { [[Get]] or [[Set]]: f, [[Enumerable]]: true, [[Configurable]]: true })
    | .objectProtoDefineGetter | .objectProtoDefineSetter =>
      let o ← toObj n thisV
      if !(← isCallable a1) then
        throwErr .type (if id matches .objectProtoDefineGetter then "Object.prototype.__defineGetter__: Expecting function"
          else "Object.prototype.__defineSetter__: Expecting function")
      let k ← toKey n a0
      let d ← newObject
      defineOwn d (if id matches .objectProtoDefineGetter then "get" else "set") (.data a1 true true true)
      defineOwn d "enumerable" (.data (.bool true) true true true)
      defineOwn d "configurable" (.data (.bool true) true true true)
      defineFromDescriptor n o k (.obj d)
      pure .undef
    -- Annex B.2.2.4 and B.2.2.5: __lookupGetter__ (P), __lookupSetter__ (P): the getter or setter
    -- of the first object on the prototype chain that has P as its own property
    | .objectProtoLookupGetter | .objectProtoLookupSetter =>
      let o ← toObj n thisV
      let k ← toKey n a0
      let wantGet := id matches .objectProtoLookupGetter
      let mut cur := o
      let mut res : Value := .undef
      for _ in [0:10000] do
        match ← ownDesc n cur k with
        | some (.acc g s _ _) => res := (if wantGet then g else s); break
        | some _ => break
        | none =>
          match (← getObj cur).proto with
          | .obj q => cur := q
          | _ => break
      pure res
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
      let src := dynFunctionSource "function" ps body
      match (parseScript src false).map Resolve.script with
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
          if x < 0 || !isIntegral x || x ≥ twoPow32F then throwErr .range "Invalid array length"
          if x.toUInt64.toNat > maxDenseArray then throwErr .range "Invalid array length"
          charge (x.toUInt64.toNat / 64)
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
      | .obj id =>
        let r ← updateObj id fun o =>
          match o.takeArray with
          | (some es, o) => let es := es ++ args; (some es.size, { o with kind := .array es })
          | (none, o) => (none, o)
        match r with
        | some k => pure (.num (Float.ofNat k))
        | none => genericPush n thisV args
      | _ => genericPush n thisV args
    | .arrayPop =>
      match thisV with
      | .obj id =>
        updateObj id fun o =>
          match o.takeArray with
          | (some es, o) => (es.back?.getD .undef, { o with kind := .array es.pop })
          | (none, o) => (.undef, o)
      | _ => pure .undef
    | .arrayShift =>
      match thisV with
      | .obj id =>
        updateObj id fun o =>
          match o.takeArray with
          | (some es, o) =>
            match es[0]? with
            | some v => (v, { o with kind := .array (es.eraseIdxIfInBounds 0) })
            | none => (.undef, { o with kind := .array es })
          | (none, o) => (.undef, o)
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
      checkStrLen (parts.foldl (fun acc t => acc + t.utf8ByteSize + sep.utf8ByteSize) 0)
      pure (.str (Str.canonical (sep.intercalate parts)))
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
      -- §23.1.3: ToObject(this), LengthOfArrayLike, then the callback's check
      let oid ← toObj n thisV
      let len ← arrayLikeLength n (.obj oid)
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      iterArray n id a0 a1 (.obj oid) len 0 #[]
    | .arrayReduce =>
      -- §23.1.3.24: the first present element is the start when there is no initial value
      let oid ← toObj n thisV
      let len ← arrayLikeLength n (.obj oid)
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      if args.size ≥ 2 then reduceArray n a0 (.obj oid) len 0 a1
      else
        let mut k := 0
        let mut first : Option Value := none
        for _ in [0:len] do
          if first.isSome then break
          first ← elemAt n oid k true
          k := k + 1
        match first with
        | some acc => reduceArray n a0 (.obj oid) len k acc
        | none => throwErr .type "Reduce of empty array with no initial value"
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
      let us ← args.toList.mapM fun a => do pure ((toUint32 (← toNum n a)) % 65536)
      pure (.str (Str.ofCodeUnits us))
    | .stringToString =>
      match ← thisPrim thisV with
      | .str s => pure (.str s)
      | _ => throwErr .type "String.prototype.toString requires that 'this' be a String"
    | .numberCtor =>
      -- §21.1.1.1: ToNumeric, and a BigInt becomes the Number of its value.
      let x ← if args.isEmpty then pure 0 else match ← toPrim n a0 "number" with
        | .big i => pure (Float.ofInt i)
        | p => toNum n p
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
        if x.abs ≥ 1e21 || !x.isFinite then pure (.str (numToString x)) else
        -- exact digits (JS/NumFmt.lean)
        let (neg, num, den) := NumFmt.ofFloat x
        pure (.str (NumFmt.fixed neg num den d.toUInt64.toNat))
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
        if id_ == .objectEntries then newArray #[keyStrV k, v] else pure v
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
            -- a surrogate pair is one code point (§22.1.5.1 %StringIteratorPrototype%.next)
            let pair := idx + 1 < cs.size && Str.isHigh (Str.charUnit cs[idx]!) && Str.isLow (Str.charUnit cs[idx + 1]!)
            let w := if pair then 2 else 1
            modifyObj id fun o => { o with kind := .iter target (idx + w) mode }
            result (.str (Str.ofUnitChars (cs.extract idx (idx + w)))) false
          else
            modifyObj id fun o => { o with kind := .iter .undef idx mode }
            result .undef true
        | _ =>
          if let .obj tid := target then
            if let .coll _ es _ := (← getObj tid).kind then
              match collNext es idx es.size with
              | none =>
                modifyObj id fun o => { o with kind := .iter .undef idx mode }
                return ← result .undef true
              | some i =>
                modifyObj id fun o => { o with kind := .iter target (i + 1) mode }
                let (k, v) := (es[i]!).getD (.undef, .undef)
                return ← match mode with
                  | 5 => result k false
                  | 6 => result v false
                  | _ => do result (← newArray #[k, v]) false
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
    | .dateNow => pure (.num ((← hostNowNs) / 1000000).floor)
    | .promiseCtor =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Promise constructor cannot be invoked without 'new'"
      if !(← isCallable a0) then throwErr .type "Promise resolver is not a function"
      let pid ← newPromise
      let pp ← getV n nt "prototype"
      if pp.isObj then modifyObj pid fun o => { o with proto := pp }
      let res ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseResolveFn) .undef #[.obj pid] }
      let rej ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseRejectFn) .undef #[.obj pid] }
      let x ← tryCatch (do let _ ← callV n a0 .undef #[.obj res, .obj rej]; pure none) (fun a => pure (some a))
      match x with
      | some (.throw e) => let _ ← callV n (.obj rej) .undef #[e]
      | some a => throw a
      | none => pure ()
      pure (.obj pid)
    | .promiseResolveFn | .promiseRejectFn =>
      match a0 with
      | .obj pid =>
        match (← getObj pid).kind with
        | .promise st v rs false =>
          modifyObj pid fun o => { o with kind := .promise st v rs true }
          if id_ == .promiseResolveFn then resolvePromise n pid a1 else rejectPromise n pid a1
        | _ => pure ()
        pure .undef
      | _ => pure .undef
    | .promiseThen =>
      let pid ← match thisV with
        | .obj p => match (← getObj p).kind with
          | .promise .. => pure p
          | _ => throwErr .type "Promise.prototype.then called on an incompatible receiver"
        | _ => throwErr .type "Promise.prototype.then called on an incompatible receiver"
      let d ← newPromise
      let onF := if ← isCallable a0 then a0 else .undef
      let onR := if ← isCallable a1 then a1 else .undef
      performThen n pid onF onR (.obj d)
      pure (.obj d)
    | .promiseCatch =>
      let th ← getV n thisV "then"
      if !(← isCallable th) then throwErr .type "then is not a function"
      callV n th thisV #[.undef, a0]
    | .promiseFinally =>
      let th ← getV n thisV "then"
      if !(← isCallable th) then throwErr .type "then is not a function"
      if !(← isCallable a0) then return ← callV n th thisV #[a0, a0]
      let f ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseFinallyF) .undef #[a0] }
      let g ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseFinallyR) .undef #[a0] }
      callV n th thisV #[.obj f, .obj g]
    | .promiseFinallyF | .promiseFinallyR =>
      let res ← callV n a0 .undef #[]
      let p ← promiseResolve n res
      let kf ← nativeFn (if id_ == .promiseFinallyF then .promiseValueThunk else .promiseThrower)
      let k ← alloc { proto := .obj r.functionProto, kind := .bound kf .undef #[a1] }
      let d ← newPromise
      performThen n p (.obj k) .undef (.obj d)
      pure (.obj d)
    | .promiseValueThunk => pure a0
    | .promiseThrower => throw (.throw a0)
    | .promiseResolveStatic => pure (.obj (← promiseResolve n a0))
    | .promiseRejectStatic =>
      let p ← newPromise
      rejectPromise n p a0
      pure (.obj p)
    | .promiseReactionJob =>
      -- args: handler, derived promise, argument, rejected?
      let handler := a0
      let derived := a1
      let arg := argD args 2
      let rejected := toBool (argD args 3)
      if ← isCallable handler then
        let x ← tryCatch (do pure (Except.ok (← callV n handler .undef #[arg]))) (fun a => pure (Except.error a))
        match derived, x with
        | .obj d, .ok v => resolvePromise n d v
        | .obj d, .error (.throw e) => rejectPromise n d e
        | _, .error (.halt w) => throw (.halt w)
        | _, _ => pure ()
      else
        match derived with
        | .obj d => if rejected then rejectPromise n d arg else resolvePromise n d arg
        | _ => pure ()
      pure .undef
    | .promiseThenableJob =>
      match a0 with
      | .obj pid =>
        -- CreateResolvingFunctions (§27.2.1.3): a new pair with its own [[AlreadyResolved]]
        -- record. The promise's own flag is already set when its resolve function was called
        -- with the thenable, so a pair that read that flag could never settle the promise
        -- (`new Promise(r => r(otherPromise))` stayed pending for ever, before 2026-11-14).
        let record ← alloc { proto := .null }
        let res ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x (.promiseThenableFn false))) .undef #[.obj pid, .obj record] }
        let rej ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x (.promiseThenableFn true))) .undef #[.obj pid, .obj record] }
        let x ← tryCatch (do let _ ← callV n (argD args 2) a1 #[.obj res, .obj rej]; pure none) (fun a => pure (some a))
        match x with
        | some (.throw e) => let _ ← callV n (.obj rej) .undef #[e]
        | some a => throw a
        | none => pure ()
        pure .undef
      | _ => pure .undef
    | .promiseAll =>
      let res ← newPromise
      let x ← tryCatch (do
          let it ← getIterator n a0
          let items ← iterToArray n it #[]
          let vals ← newArray (Array.replicate items.size .undef)
          let counter ← newObject
          setHidden counter "n" (.num (Float.ofNat items.size + 1))
          for i in [0:items.size] do
            let p ← promiseResolve n items[i]!
            let elF ← nativeFn .promiseAllElement
            let elArgs : Array Value := #[.obj res, vals, .obj counter, .num (Float.ofNat i)]
            let el ← alloc { proto := .obj r.functionProto, kind := .bound elF .undef elArgs }
            let rj ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseRejectFn) .undef #[.obj res] }
            performThen n p (.obj el) (.obj rj) .undef
          let _ ← callNative n .promiseAllElement .undef #[.obj res, vals, .obj counter, .num (-1), .undef] none
          pure none)
        (fun a => pure (some a))
      match x with
      | some (.throw e) => rejectPromise n res e
      | some a => throw a
      | none => pure ()
      pure (.obj res)
    | (.x (.promiseCombinator k)) =>
      let res ← newPromise
      let x ← tryCatch (do
          let it ← getIterator n a0
          let items ← iterToArray n it #[]
          let vals ← newArray (Array.replicate items.size .undef)
          let counter ← newObject
          setHidden counter "n" (.num (Float.ofNat items.size + 1))
          for i in [0:items.size] do
            let p ← promiseResolve n items[i]!
            if k == 0 then
              let rs ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseResolveFn) .undef #[.obj res] }
              let rj ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseRejectFn) .undef #[.obj res] }
              performThen n p (.obj rs) (.obj rj) .undef
            else
              let elArgs : Array Value := #[.obj res, vals, .obj counter, .num (Float.ofNat i)]
              let onF ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn ((.x (.promiseSettleElement 0)))) .undef elArgs }
              let onR ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn ((.x (.promiseSettleElement 1)))) .undef elArgs }
              performThen n p (.obj onF) (.obj onR) .undef
          if k != 0 then
            let _ ← callNative n .promiseAllElement .undef #[.obj res, vals, .obj counter, .num (-1), .undef] none
          pure none)
        (fun a => pure (some a))
      match x with
      | some (.throw e) => rejectPromise n res e
      | some a => throw a
      | none => pure ()
      pure (.obj res)
    | (.x (.promiseSettleElement rejected)) =>
      -- args: result promise, values, counter, index, value: the value becomes
      -- { status, value } or { status, reason } (§27.2.4.2.2, §27.2.4.2.3)
      let o ← newObject
      defineOwn o "status" (.data (.str (if rejected == 1 then "rejected" else "fulfilled")) true true true)
      defineOwn o (if rejected == 1 then "reason" else "value") (.data (argD args 4) true true true)
      callNative n .promiseAllElement .undef #[a0, a1, argD args 2, argD args 3, .obj o] none
    | .promiseAllElement =>
      -- args: result promise, values, counter, index, value
      let idx := match argD args 3 with | .num i => i | _ => -1
      if idx ≥ 0 then putV n a1 (numToString idx) (argD args 4) true
      let c := argD args 2
      let k ← toNum n (← getV n c "n")
      putV n c "n" (.num (k - 1)) true
      if k - 1 == 0 then
        match a0 with
        | .obj p => resolvePromise n p a1
        | _ => pure ()
      pure .undef
    | .agenNext | .agenReturn | .agenThrow =>
      let pid ← newPromise
      match thisV with
      | .obj gid =>
        match (← getObj gid).kind with
        | .agen fs st q =>
          let input := match id_ with
            | .agenNext => GInput.send a0
            | .agenReturn => .retV a0
            | _ => .throwV a0
          modifyObj gid fun o => { o with kind := .agen fs st (q.push (input, pid)) }
          agenDrain n gid
        | _ => rejectPromise n pid (← mkError .type "not an async generator")
      | _ => rejectPromise n pid (← mkError .type "not an async generator")
      pure (.obj pid)
    | .agenResume =>
      -- bound arguments: the generator and the mode. 0, 1: an `await` in the body ended
      -- (fulfilled, rejected). 2: the operand of a `yield`, awaited: the request at the head
      -- gets it. 3: the value of `return(v)` at a `yield`, awaited. 4, 5: the value of a
      -- `return(v)` to a generator that is not running its body (fulfilled, rejected).
      match a0 with
      | .obj gid =>
        match (← getObj gid).kind with
        | .agen fs _ q =>
          let mode := match a1 with | .num m => m.toUInt64.toNat | _ => 0
          let v := argD args 2
          let pid := (q.getD 0 (GInput.send .undef, 0)).2
          let finish (st : Nat) : M Unit :=
            modifyObj gid fun o => { o with kind := .agen (if st == 3 then [] else fs) st (q.extract 1 q.size) }
          match mode with
          | 0 => agenRun n gid fs (.send v)
          | 1 => agenRun n gid fs (.throwV v)
          | 2 => finish 1; resolvePromise n pid (← iterResult n v false); agenDrain n gid
          | 3 => agenRun n gid fs (.retV v)
          | 4 => finish 3; resolvePromise n pid (← iterResult n v true); agenDrain n gid
          | _ => finish 3; rejectPromise n pid v; agenDrain n gid
        | _ => pure ()
        pure .undef
      | _ => pure .undef
    | .mapCtor k =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Constructor requires 'new'"
      let pp ← getV n nt "prototype"
      let o ← alloc { proto := pp, kind := .coll k #[] {} }
      match a0 with
      | .undef | .null => pure ()
      | it =>
        let adder ← getV n (.obj o) (if k == 0 || k == 2 then "set" else "add")
        if !(← isCallable adder) then throwErr .type "adder is not a function"
        let items ← iterToArray n (← getIterator n it) #[]
        for item in items do
          if k == 0 || k == 2 then
            if !item.isObj then throwErr .type "Iterator value is not an entry object"
            let key ← getV n item "0"
            let v ← getV n item "1"
            let _ ← callV n adder (.obj o) #[key, v]
          else let _ ← callV n adder (.obj o) #[item]
      pure (.obj o)
    | .mapGet | .mapSet | .mapHas | .mapDelete | .mapClear | .mapSize | .mapForEach | .setAdd
    | .mapIter _ =>
      let (cid, ck) ← match thisV with
        | .obj c => match (← getObj c).kind with
          | .coll k _ _ => pure (c, k)
          | _ => throwErr .type "method called on incompatible receiver"
        | _ => throwErr .type "method called on incompatible receiver"
      let weak := ck ≥ 2
      let key := match a0 with
        | .num x => if x == 0 then Value.num 0 else a0
        | _ => a0
      match id_ with
      | .mapGet =>
        match (← getObj cid).kind with
        | .coll _ es idx => pure (match collFind idx key with | some i => ((es[i]!).map (·.2)).getD .undef | none => .undef)
        | _ => pure .undef
      | .mapHas =>
        match (← getObj cid).kind with
        | .coll _ _ idx => pure (.bool (collFind idx key).isSome)
        | _ => pure (.bool false)
      | .mapSet | .setAdd =>
        if weak && !key.isObj then throwErr .type "Invalid value used as weak collection key"
        let v := if id_ == .setAdd then key else a1
        modifyObj cid (collPut key v)
        pure thisV
      | .mapDelete =>
        let had ← match (← getObj cid).kind with
          | .coll _ _ idx => pure (collFind idx key).isSome
          | _ => pure false
        if had then modifyObj cid (collDel key)
        pure (.bool had)
      | .mapClear => modifyObj cid collClear; pure .undef
      | .mapSize =>
        match (← getObj cid).kind with
        | .coll _ _ idx => pure (.num (Float.ofNat idx.size))
        | _ => pure (.num 0)
      | .mapForEach =>
        if !(← isCallable a0) then throwErr .type "callback is not a function"
        let mut i := 0
        for _ in [0:1000000] do
          let es ← match (← getObj cid).kind with | .coll _ es _ => pure es | _ => pure #[]
          match collNext es i es.size with
          | none => break
          | some j =>
            let (k, v) := (es[j]!).getD (.undef, .undef)
            let _ ← callV n a0 a1 #[v, k, thisV]
            i := j + 1
        pure .undef
      | .mapIter mode =>
        pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter thisV 0 mode }))
      | _ => pure .undef
    | .reflect op =>
      let needObj : M Unit := if !a0.isObj then throwErr .type "Reflect method called on a non-object" else pure ()
      match op with
      | 0 => needObj; newArray ((← ownKeysOf n (← toObj n a0)).filter (!isPrivKey ·) |>.map keyValue)
      | 1 => needObj; callNative n .objectGetPrototypeOf .undef args none
      | 2 => needObj
             match a0, a1 with
             | .obj id0, .obj _ | .obj id0, .null =>
               -- [[SetPrototypeOf]] (§10.1.2, §10.5.2): a Proxy asks its trap
               let mut cur := id0
               for _ in [0:64] do
                 match (← getObj cur).kind with
                 | .proxy t hnd =>
                   let .obj tid := t | throwErr .type "Cannot perform 'setPrototypeOf' on a proxy that has been revoked"
                   match ← proxyTrap n hnd "setPrototypeOf" with
                   | some f =>
                     if !toBool (← callV n f hnd #[t, a1]) then return .bool false
                     if !toBool (← callNative n .objectIsExtensible .undef #[t] none) then
                       if !sameValue a1 (← callNative n .objectGetPrototypeOf .undef #[t] none) then
                         throwErr .type "'setPrototypeOf' on proxy: the target is not extensible and has another prototype"
                     return .bool true
                   | none => cur := tid
                 | _ => return .bool (← setProtoOf cur a1)
               pure (.bool false)
             | _, _ => throwErr .type "Object prototype may only be an Object or null"
      | 3 => needObj; let k ← toKey n a1; pure (.bool (← hasProp n (← toObj n a0) k))
      | 4 => needObj; if args.size > 2 then getRecv n (← toObj n a0) (← toKey n a1) (argD args 2) else getV n a0 (← toKey n a1)
      | 5 =>
        needObj
        let recv := if args.size > 3 then argD args 3 else a0
        if !sameValue recv a0 then
          -- Reflect.set with a receiver that is not the target (§10.1.9.2
          -- OrdinarySetWithOwnDescriptor): a setter found on the target's chain is called with
          -- the receiver as `this`; a data property is made or changed on the receiver.
          let key ← toKey n a1
          let val := argD args 2
          let tid ← toObj n a0
          match (← getObj tid).kind with
          | .proxy t hnd =>
            match ← proxyTrap n hnd "set" with
            | some f => return .bool (toBool (← callV n f hnd #[t, keyValue key, val, recv]))
            | none => return ← callNative n (.reflect 5) .undef #[t, a1, val, recv] none
          | _ => pure ()
          match (← get).findProp tid key 1000 with
          | some (.acc _ st _ _) =>
            if st.isObj then
              let _ ← callV n st recv #[val]
              return .bool true
            else return .bool false
          | some (.data _ false _ _) => return .bool false
          | _ =>
            match recv with
            | .obj rid =>
              let existing ← ownDesc n rid key
              match existing with
              | some (.acc ..) | some (.data _ false _ _) => return .bool false
              | _ => pure ()
              -- the receiver's [[DefineOwnProperty]]: a Proxy passes it to its `defineProperty`
              -- trap, or to its target when it has none
              let mut cur := rid
              for _ in [0:64] do
                match (← getObj cur).kind with
                | .proxy t hnd =>
                  match ← proxyTrap n hnd "defineProperty" with
                  | some f =>
                    let d ← newObject
                    defineOwn d "value" (.data val true true true)
                    if existing.isNone then
                      defineOwn d "writable" (.data (.bool true) true true true)
                      defineOwn d "enumerable" (.data (.bool true) true true true)
                      defineOwn d "configurable" (.data (.bool true) true true true)
                    return .bool (toBool (← callV n f hnd #[t, keyValue key, .obj d]))
                  | none =>
                    match t with
                    | .obj tid => cur := tid
                    | _ => return .bool false
                | _ => break
              let ro ← getObj cur
              match ro.getOwn key with
              | some (.data _ true e c) => defineOwn cur key (.data val true e c); return .bool true
              | some _ => return .bool false
              | none =>
                if ro.extensible then defineOwn cur key (.data val true true true); return .bool true
                else return .bool false
            | _ => return .bool false
        let ok ← tryCatch (do putV n a0 (← toKey n a1) (argD args 2) true; pure true) (fun e => match e with
          | .throw _ => pure false
          | a => throw a)
        pure (.bool ok)
      | 6 =>
        -- §28.1.3: the key, the descriptor (its TypeErrors), then [[DefineOwnProperty]]
        let .obj tid := a0 | throwErr .type "Reflect.defineProperty called on a non-object"
        let k ← toKey n a1
        let desc ← toPropDesc n (argD args 2)
        pure (.bool (← defineOwnProp n tid k desc))
      | 7 =>
        needObj
        let id ← toObj n a0
        let k ← toKey n a1
        match (← getObj id).getOwn k with
        | none => pure (.bool true)
        | some p => if p.configurable then deleteOwn id k; pure (.bool true) else pure (.bool false)
      | 8 =>
        if !(← isCallable a0) then throwErr .type "Reflect.apply target is not callable"
        let argv ← elemsOf n (argD args 2)
        callV n a0 a1 argv
      | 9 =>
        if !(← isConstructor a0) then throwErr .type "Reflect.construct target is not a constructor"
        if args.size > 2 && !(← isConstructor (argD args 2)) then throwErr .type "Reflect.construct newTarget is not a constructor"
        let argv ← elemsOf n a1
        construct n a0 argv (if args.size > 2 then argD args 2 else a0)
      | 10 => needObj; callNative n .objectGetOwnPropertyDescriptor .undef args none
      | 11 => needObj; callNative n .objectIsExtensible .undef args none
      | _ =>
        -- [[PreventExtensions]] (§10.1.4, §10.5.4)
        needObj
        let .obj id0 := a0 | pure (.bool false)
        let mut cur := id0
        for _ in [0:64] do
          match (← getObj cur).kind with
          | .proxy t hnd =>
            let .obj tid := t | throwErr .type "Cannot perform 'preventExtensions' on a proxy that has been revoked"
            match ← proxyTrap n hnd "preventExtensions" with
            | some f =>
              let b := toBool (← callV n f hnd #[t])
              if b && toBool (← callNative n .objectIsExtensible .undef #[t] none) then
                throwErr .type "'preventExtensions' on proxy: the trap returned true but the target is extensible"
              return .bool b
            | none => cur := tid
          | _ =>
            modifyObj cur fun o => { o with extensible := false }
            return .bool true
        pure (.bool false)
    | .objectDefineProperties =>
      match a0 with
      | .obj id =>
        let pid ← toObj n a1
        for k in (← getObj pid).ownKeys do
          match (← getObj pid).getOwn k with
          | some p => if p.enumerable then defineFromDescriptor n id k (← getV n (.obj pid) k)
          | none => pure ()
        pure a0
      | _ => throwErr .type "Object.defineProperties called on non-object"
    | .objectSeal =>
      match a0 with
      | .obj id =>
        let o ← getObj id
        let props := o.props.mapValues (fun p => (match p with
          | .data v w e _ => .data v w e false
          | .acc g s e _ => .acc g s e false))
        modifyObj id fun o => { o with props, extensible := false }
        pure a0
      | _ => pure a0
    | .objectIsSealed =>
      match a0 with
      | .obj id =>
        let o ← getObj id
        pure (.bool (!o.extensible && o.ownKeys.all fun k => match o.getOwn k with
          | some p => !p.configurable | none => true))
      | _ => pure (.bool true)
    | .objectGetOwnPropertyDescriptors =>
      let id ← toObj n a0
      let res ← newObject
      for k in (← getObj id).ownKeys do
        let d ← callNative n .objectGetOwnPropertyDescriptor .undef #[.obj id, keyValue k] none
        defineOwn res k (.data d true true true)
      pure (.obj res)
    | .objectFromEntries =>
      let res ← newObject
      let items ← iterToArray n (← getIterator n a0) #[]
      for item in items do
        let k ← toKey n (← getV n item "0")
        defineOwn res k (.data (← getV n item "1") true true true)
      pure (.obj res)
    | .arrayFlat | .arrayFlatMap =>
      let es ← elemsOf n thisV
      let es ← if id_ == .arrayFlatMap then do
          if !(← isCallable a0) then throwErr .type "flatMap mapper is not callable"
          (List.range es.size).toArray.mapM fun i => callV n a0 a1 #[es[i]!, .num (Float.ofNat i), thisV]
        else pure es
      let depth := if id_ == .arrayFlatMap then 1 else match a0 with
        | .undef => 1
        | .num d => if d.isNaN || d < 1 then 0 else (if d > 1000 then 1000 else d.toUInt64.toNat)
        | _ => 1
      newArray (← flattenArr depth es (depth + 1))
    | .stringAt =>
      -- §22.1.3.1: one code unit, found in constant time for ASCII (`Str.unitStrAt?`)
      let s ← toStr n (← thisPrim thisV)
      let len := Str.jsLength s
      let k := toIntegerOrInf (← toNum n a0)
      let i := if k < 0 then Float.ofNat len + k else k
      if i < 0 || i ≥ Float.ofNat len then pure .undef
      else pure ((Str.unitStrAt? s i.toUInt64.toNat).map Value.str |>.getD .undef)
    | .arrayAt =>
      let es ← elemsOf n thisV
      let k := toIntegerOrInf (← toNum n a0)
      let i := if k < 0 then Float.ofNat es.size + k else k
      if i < 0 || i ≥ Float.ofNat es.size then pure .undef else pure es[i.toUInt64.toNat]!
    | .arrayFindLast | .arrayFindLastIndex =>
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      let es ← elemsOf n thisV
      let mut found : Option Nat := none
      for j in [0:es.size] do
        let i := es.size - 1 - j
        if found.isNone then
          if toBool (← callV n a0 a1 #[es[i]!, .num (Float.ofNat i), thisV]) then found := some i
      match found with
      | some i => pure (if id_ == .arrayFindLast then es[i]! else .num (Float.ofNat i))
      | none => pure (if id_ == .arrayFindLast then .undef else .num (-1))
    | .stringPadStart | .stringPadEnd =>
      let s ← toStr n (← thisPrim thisV)
      let len := toIntegerOrInf (← toNum n a0)
      let fill ← match a1 with | .undef => pure " " | v => toStr n v
      let cur := Str.jsLength s
      if len ≤ Float.ofNat cur || fill.isEmpty then pure (.str s) else
      let need := len.toUInt64.toNat - cur
      if need > maxStringBytes then throwErr .range "Invalid string length"
      charge (need / 64)
      let reps := repeatStr fill (need / Str.jsLength fill + 1)
      let pad := substr reps 0 need
      pure (.str (if id_ == .stringPadStart then Str.jsAppend pad s else Str.jsAppend s pad))
    | .stringCodePointAt =>
      let s ← toStr n (← thisPrim thisV)
      let i := toIntegerOrInf (← toNum n a0)
      if i < 0 then pure .undef else
      -- §11.1.4 CodePointAt: a high surrogate followed by a low one is their code point
      let k := i.toUInt64.toNat
      match Str.unitAt? s k with
      | none => pure .undef
      | some u =>
        match (if Str.isHigh u then Str.unitAt? s (k + 1) else none) with
        | some l => pure (.num (Float.ofNat (if Str.isLow l then 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00) else u)))
        | none => pure (.num (Float.ofNat u))
    | .stringTrimStart | .stringTrimEnd =>
      match ← thisPrim thisV with
      | .undef | .null => throwErr .type "String.prototype.trimStart/trimEnd called on null or undefined"
      | _ => pure ()
      let s ← toStr n (← thisPrim thisV)
      let cs := s.toList
      pure (.str (if id_ == .stringTrimStart then String.ofList (cs.dropWhile isStrWs)
        else String.ofList (cs.reverse.dropWhile isStrWs).reverse))
    | .stringReplace | .stringReplaceAll =>
      if ← isRegExpV a0 then return ← extraNative n id_ thisV args newTarget
      let s ← toStr n (← thisPrim thisV)
      let pat ← toStr n a0
      let fnRepl ← isCallable a1
      let replStr ← if fnRepl then pure "" else toStr n a1
      let positions : List Nat :=
        if id_ == .stringReplaceAll then
          allPositions s pat 0 (Str.jsLength s + 2)
        else match indexOfFrom s pat 0 with | some p => [p] | none => []
      let mut out := ""
      let mut last := 0
      -- each `$&` of the replacement adds the search string: asked before it is made
      let whole := (replStr.splitOn "$&").length - 1
      if !fnRepl then checkStrLen (replStr.utf8ByteSize + whole * pat.utf8ByteSize)
      for p in positions do
        out := out ++ substr s last p
        let r ← if fnRepl then toStr n (← callV n a1 .undef #[.str pat, .num (Float.ofNat p), .str s])
          else pure ((replStr.replace "$&" pat).replace "$$" "$")
        checkStrLen (out.utf8ByteSize + r.utf8ByteSize)
        out := out ++ r
        last := p + Str.jsLength pat
      pure (.str (Str.canonical (out ++ substr s last (Str.jsLength s))))
    | .stringFromCodePoint =>
      let cs ← args.toList.mapM fun a => do
        let x ← toNum n a
        if !isIntegral x || x < 0 || x > 1114111 then throwErr .range s!"Invalid code point {numToString x}"
        pure (Str.ofCodePoint x.toUInt64.toNat)
      pure (.str (Str.canonical (String.join cs)))
    | .numberIsFinite => pure (.bool (match a0 with | .num x => x.isFinite | _ => false))
    | .numberIsNaN => pure (.bool (match a0 with | .num x => x.isNaN | _ => false))
    | .numberIsSafeInteger => pure (.bool (match a0 with | .num x => isIntegral x && x.abs ≤ maxSafeF | _ => false))
    | .math1 op =>
      let x ← toNum n a0
      pure (.num (match op with
        | 0 => Float.cbrt x | 1 => Float.log2 x | 2 => Float.log10 x | 3 => Float.sinh x
        | 4 => Float.cosh x | 5 => Float.tanh x | 6 => Float.asin x | 7 => Float.acos x
        | 8 => Float.asinh x | 9 => Float.acosh x | 10 => Float.atanh x
        | 11 => Float.exp x - 1 | 12 => Float.log (1 + x)
        | 14 => L4Factoidal.Prim.Float16.round x
        | _ => x.toFloat32.toFloat))
    | .mathHypot =>
      let xs ← args.toList.mapM (toNum n)
      if xs.any Float.isInf then pure (.num inf)
      else pure (.num (Float.sqrt (xs.foldl (fun a x => a + x * x) 0)))
    | .mathImul =>
      let a := toInt32 (← toNum n a0); let b := toInt32 (← toNum n a1)
      pure (intV (toInt32 (Float.ofInt (a * b % 4294967296))))
    | .mathClz32 =>
      let x := toUint32 (← toNum n a0)
      pure (.num (Float.ofNat (if x == 0 then 32 else 31 - Nat.log2 x)))
    | .asyncResume =>
      match a0 with
      | .obj co =>
        let input := if (match a1 with | .num m => m == 1 | _ => false) then GInput.throwV (argD args 2)
          else .send (argD args 2)
        asyncStep n co input
        pure .undef
      | _ => pure .undef
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
    | .bigintAsN signed =>
      -- ToIndex (§7.1.22).
      let bf := toIntegerOrInf (← toNum n a0)
      if bf < 0 || bf > 9007199254740991 then throwErr .range "Invalid value: not (convertible to) a safe integer"
      let bits := bf.toUInt64.toNat
      if bits > 1000000 then throwErr .range "Maximum BigInt size exceeded"
      -- ToBigInt (§7.1.13): a Number is a TypeError.
      let x ← match ← toPrim n a1 "number" with
        | .big i => pure i
        | .bool b => pure (if b then 1 else 0)
        | .str t => match strToBigInt t with
          | some i => pure i
          | none => throwErr .syntax s!"Cannot convert {t} to a BigInt"
        | .num _ => throwErr .type "Cannot convert a Number to a BigInt"
        | _ => throwErr .type "Cannot convert value to a BigInt"
      let m : Int := 2 ^ bits
      let r := x.emod m
      pure (.big (if signed && bits > 0 && r ≥ 2 ^ (bits - 1) then r - m else r))
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
          | .ok (.awaited _ _) => setG [] 3; throwErr .syntax "await outside an async function"
          | .ok (.done v) => setG [] 3; result v true
      | _ => throwErr .type "next method called on incompatible receiver"
    | .stringSplit =>
      if ← isRegExpV a0 then extraNative n id thisV args newTarget else stringOrMath n id thisV args
    | .regexpCtor | .regexpExec | .regexpTest | .regexpToString | .regexpGetter _ | .stringMatch
    | .stringMatchAll | .stringSearch | .proxyCtor | .jsonParse | .bufferCtor | .bufferSlice
    | .bufferIsView | .typedCtor _ | .typedSet | .typedSubarray | .typedFill | .dateCtor
    | .dataViewCtor | .dataViewGet _ | .dataViewSet _
    | .dateGetTime | .perfNow | .host _ | .uriFn _ =>
      extraNative n id thisV args newTarget
    | .x _ =>
      moreNative n id thisV args newTarget
    | _ =>
      -- string methods and Math
      stringOrMath n id thisV args
termination_by structural n _ _ _ _ => n


/-- A global name read through the cache: the value, or `Value.hole` when the general path
must look (not a plain writable data property, or a lexical binding may shadow it). -/
def vmGlobalHit (h : HeapOf H) (env : Nat) (x : String) (site : Nat) : Value :=
  match h.findEnv x 100000 env with
  | some _ => .hole
  | none =>
    let g := h.obj h.realm.globalObj
    let slot := h.globalCache[site]!
    match g.props.ks[slot]?, g.props.vs[slot]? with
    | some k, some (.data v ..) => if k == x then v else .hole
    | _, _ => .hole

/-- Assign a global name through the cache: only when no lexical binding shadows it and the
cached slot holds this name as a plain writable data property; `false` otherwise. -/
def vmGlobalSet (env : Nat) (x : String) (site : Nat) (v : Value) : M Bool := do
  let h ← get
  if (h.findEnv x 100000 env).isSome then return false
  let gid := h.realm.globalObj
  let slot := h.globalCache[site]!
  let g := h.obj gid
  match g.props.ks[slot]?, g.props.vs[slot]? with
  | some k, some (.data _ true e c) =>
    if k == x then
      updateObj gid fun o =>
        (true, { o with props := { o.props with vs := o.props.vs.set! slot (.data v true e c) } })
    else pure false
  | _, _ => pure false

/-- Assign a variable `hops` above the closure environment, when the slot holds that name
and the binding is initialised and mutable; `false` otherwise. -/
def vmSetUp (env hops idx : Nat) (x : String) (v : Value) : M Bool := do
  let h ← get
  let e := h.envUp hops env
  let en := h.envs.getD e default
  match en.names[idx]?, en.vals[idx]? with
  | some y, some old =>
    if y == x && en.mutableAt idx then
      match old with
      | .hole => pure false
      | _ => setSlot e idx v; pure true
    else pure false
  | _, _ => pure false

/-- The slow path of a global name: the lookup, and the cache learns the slot. -/
def vmGlobalMiss : Nat → Nat → String → Nat → Bool → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, env, x, site, strict => do
    let v ← lookup n { env, thisV := .undef, strict } x
    let h ← get
    if (h.findEnv x 100000 env).isNone then
      match (h.obj h.realm.globalObj).props.slot? x with
      | some slot => set { h with globalCache := h.globalCache.setIfInBounds site slot }
      | none => pure ()
    pure v
termination_by structural n _ _ _ _ => n

/-- The unary operators, as the evaluator does them. -/
def vmUnary : Nat → UnOp → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, op, v => do
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
termination_by structural n _ _ => n

/-- `b[kv]`, as the evaluator's `.index` arm does it. -/
def vmGetIndex : Nat → Value → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, b, kv => do
    match b, kv with
    | .obj id, .num x =>
      match (← getObj id).kind with
      | .array es =>
        if x ≥ 0 && x < Float.ofNat es.size && x.floor == x then pure (es.getD x.toUInt64.toNat .undef)
        else getV n b (← toKey n kv)
      | _ => getV n b (← toKey n kv)
    | _, _ =>
      if let .undef := b then throwErr .type "Cannot read properties of undefined"
      if let .null := b then throwErr .type "Cannot read properties of null"
      getV n b (← toKey n kv)
termination_by structural n _ _ => n

/-- Run a compiled function: registers `bp` up. -/
def vmLoop : Nat → Code → Nat → Nat → Nat → List VFrame → Array Value → FloatArray → M Value
  | 0, _, _, _, _, _, regs, fregs => do vmStash regs fregs 0; throw (.halt "fuel")
  | n + 1, code, pc, bp, env, fr, regs, fregs => do
    match code.instrs[pc]! with
    | .move dst src =>
      match regs[bp + src]! with
      | .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + src)))
      | v => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) v) fregs
    | .loadF dst x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
    | .loadV dst v => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) v) fregs
    | .setHole r => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + r) .hole) fregs
    | .checkInit r x =>
      match regs[bp + r]! with
      | .hole =>
        vmStash regs fregs (bp + code.nregs)
        throwErr .reference s!"Cannot access '{x}' before initialization"
      | _ => vmLoop n code (pc + 1) bp env fr regs fregs
    | .add dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) + fregs.get! (bp + b)))
      -- `s += t` on strings (`dst` = `a`): the register lets go of the string before the
      -- append, so the append is in place when nothing else holds the string, and a loop of
      -- appends is linear (as `dropSlotStr` in the evaluator)
      | .str x, .str y =>
        checkStrLen (x.utf8ByteSize + y.utf8ByteSize)
        let regs := if dst == a then regs.set! (bp + a) .undef else regs
        vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.str (Str.jsAppend x y))) fregs
      | .str x, .fl =>
        let y := numToString (fregs.get! (bp + b))
        let regs := if dst == a then regs.set! (bp + a) .undef else regs
        vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.str (Str.jsAppend x y))) fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .add x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .sub dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) - fregs.get! (bp + b)))
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .sub x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .mul dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) * fregs.get! (bp + b)))
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .mul x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .div dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) / fregs.get! (bp + b)))
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .div x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .lt dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) < fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .lt x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .gt dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) > fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .gt x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .le dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .le x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .ge dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .ge x y
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .addK dst a k =>
      match regs[bp + a]! with
      | .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) + k))
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .add x (.num k)
        let (regs, fregs) ← vmTake
        match v with
        | .num r => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) r)
        | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .subK dst a k =>
      match regs[bp + a]! with
      | .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) - k))
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .sub x (.num k)
        let (regs, fregs) ← vmTake
        match v with
        | .num r => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) r)
        | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .mulK dst a k =>
      match regs[bp + a]! with
      | .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) * k))
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .mul x (.num k)
        let (regs, fregs) ← vmTake
        match v with
        | .num r => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) r)
        | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .jnltK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) < k then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .lt x (.num k)
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jngtK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) > k then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .gt x (.num k)
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jnleK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) ≤ k then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .le x (.num k)
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jngeK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) ≥ k then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .ge x (.num k)
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .seq dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) == fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | _, _ =>
        let r := strictEq (vmRd regs fregs (bp + a)) (vmRd regs fregs (bp + b))
        vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (if r then .bool true else .bool false)) fregs
    | .sne dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) == fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
      | _, _ =>
        let r := strictEq (vmRd regs fregs (bp + a)) (vmRd regs fregs (bp + b))
        vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (if r then .bool false else .bool true)) fregs
    | .binop op dst a b =>
      let x := vmRd regs fregs (bp + a)
      let y := vmRd regs fregs (bp + b)
      vmStash regs fregs (bp + code.nregs)
      let v ← binop n op x y
      let (regs, fregs) ← vmTake
      match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .inc nw old src up =>
      match regs[bp + src]! with
      | .fl =>
        let x := fregs.get! (bp + src)
        let d := if up then x + 1 else x - 1
        vmLoop n code (pc + 1) bp env fr (regs.set! (bp + old) .fl |>.set! (bp + nw) .fl) (fregs.set! (bp + old) x |>.set! (bp + nw) d)
      | _ =>
        let v := vmRd regs fregs (bp + src)
        vmStash regs fregs (bp + code.nregs)
        let (o, nv) ← match ← toPrim n v "number" with
          | .big i => pure (Value.big i, Value.big (if up then i + 1 else i - 1))
          | p =>
            let x ← toNum n p
            pure (Value.num x, Value.num (if up then x + 1 else x - 1))
        let (regs, fregs) ← vmTake
        let regs := regs.set! (bp + old) o
        match (nv) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + nw) .fl) (fregs.set! (bp + nw) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + nw) wv) fregs
    | .unop op dst a =>
      match op, regs[bp + a]! with
      | .neg, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (-(fregs.get! (bp + a))))
      | .plus, .fl => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a)))
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        vmStash regs fregs (bp + code.nregs)
        let v ← vmUnary n op x
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .not dst a =>
      match regs[bp + a]! with
      | .fl =>
        let x := fregs.get! (bp + a)
        if x == 0 || x.isNaN then vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool true)) fregs
        else vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.bool false)) fregs
      | v => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (if toBool v then .bool false else .bool true)) fregs
    | .jmp t => vmLoop n code t bp env fr regs fregs
    | .jf a t =>
      match regs[bp + a]! with
      | .fl =>
        let x := fregs.get! (bp + a)
        if x == 0 || x.isNaN then vmLoop n code t bp env fr regs fregs else vmLoop n code (pc + 1) bp env fr regs fregs
      | v => if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jt a t =>
      match regs[bp + a]! with
      | .fl =>
        let x := fregs.get! (bp + a)
        if x == 0 || x.isNaN then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
      | v => if toBool v then vmLoop n code t bp env fr regs fregs else vmLoop n code (pc + 1) bp env fr regs fregs
    | .jnull a t =>
      match regs[bp + a]! with
      | .undef | .null => vmLoop n code t bp env fr regs fregs
      | _ => vmLoop n code (pc + 1) bp env fr regs fregs
    | .jnotnull a t =>
      match regs[bp + a]! with
      | .undef | .null => vmLoop n code (pc + 1) bp env fr regs fregs
      | _ => vmLoop n code t bp env fr regs fregs
    | .jnlt a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) < fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .lt x y
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jngt a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) > fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .gt x y
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jnle a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .le x y
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .jnge a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then vmLoop n code (pc + 1) bp env fr regs fregs
        else vmLoop n code t bp env fr regs fregs
      | _, _ =>
        let x := vmRd regs fregs (bp + a)
        let y := vmRd regs fregs (bp + b)
        vmStash regs fregs (bp + code.nregs)
        let v ← binop n .ge x y
        let (regs, fregs) ← vmTake
        if toBool v then vmLoop n code (pc + 1) bp env fr regs fregs else vmLoop n code t bp env fr regs fregs
    | .tick =>
      tick
      vmLoop n code (pc + 1) bp env fr regs fregs
    | .getGlobal dst x site =>
      let h ← get
      match vmGlobalHit h env x site with
      | .num xf => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) xf)
      | .hole =>
        vmStash regs fregs (bp + code.nregs)
        let v ← vmGlobalMiss n env x site code.strict
        let (regs, fregs) ← vmTake
        match v with
        | .num xf => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) xf)
        | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
      | v => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) v) fregs
    | .setGlobal src x site =>
      let v := vmRd regs fregs (bp + src)
      if ← vmGlobalSet env x site v then
        vmLoop n code (pc + 1) bp env fr regs fregs
      else
        vmStash regs fregs (bp + code.nregs)
        assignName n { env, thisV := .undef, strict := code.strict } x v
        let h ← get
        if (h.findEnv x 100000 env).isNone then
          match (h.obj h.realm.globalObj).props.slot? x with
          | some slot => set { h with globalCache := h.globalCache.setIfInBounds site slot }
          | none => pure ()
        let (regs, fregs) ← vmTake
        vmLoop n code (pc + 1) bp env fr regs fregs
    | .typeofGlobal dst x =>
      vmStash regs fregs (bp + code.nregs)
      let h ← get
      let v ← if (h.findEnv x 100000 env).isNone && (h.findProp h.realm.globalObj x 1000).isNone then
          match ← namedGlobal n x with
          | some nv => pure (Value.str (← typeOf nv))
          | none => pure (Value.str "undefined")
        else pure (.str (← typeOf (← lookup n { env, thisV := .undef, strict := code.strict } x)))
      let (regs, fregs) ← vmTake
      match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .getUp dst hops idx x =>
      let h ← get
      let e := h.envUp hops env
      let en := h.envs.getD e default
      match en.names[idx]?, en.vals[idx]? with
      | some y, some v =>
        if y == x then
          match v with
          | .hole =>
            vmStash regs fregs (bp + code.nregs)
            throwErr .reference s!"Cannot access '{x}' before initialization"
          | _ => match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
        else
          vmStash regs fregs (bp + code.nregs)
          let v ← lookup n { env, thisV := .undef, strict := code.strict } x
          let (regs, fregs) ← vmTake
          match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
      | _, _ =>
        vmStash regs fregs (bp + code.nregs)
        let v ← lookup n { env, thisV := .undef, strict := code.strict } x
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .setUp src hops idx x =>
      let v := vmRd regs fregs (bp + src)
      if ← vmSetUp env hops idx x v then
        vmLoop n code (pc + 1) bp env fr regs fregs
      else
        vmStash regs fregs (bp + code.nregs)
        assignName n { env, thisV := .undef, strict := code.strict } x v
        let (regs, fregs) ← vmTake
        vmLoop n code (pc + 1) bp env fr regs fregs
    | .getMember dst o k =>
      let b := vmRd regs fregs (bp + o)
      match (← get).fastGetV b k with
      | .hole =>
        vmStash regs fregs (bp + code.nregs)
        let v ← getV n b k
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
      | v => match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .setMember o k src =>
      let b := vmRd regs fregs (bp + o)
      let v := vmRd regs fregs (bp + src)
      vmStash regs fregs (bp + code.nregs)
      putV n b k v code.strict
      let (regs, fregs) ← vmTake
      vmLoop n code (pc + 1) bp env fr regs fregs
    | .getIndex dst o i =>
      let b := vmRd regs fregs (bp + o)
      match b, regs[bp + i]! with
      | .obj id, .fl =>
        let x := fregs.get! (bp + i)
        match (← get).obj id |>.kind with
        | .array es =>
          if x ≥ 0 && x < Float.ofNat es.size && x.floor == x then
            match ((es.getD x.toUInt64.toNat .undef)) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
          else
            vmStash regs fregs (bp + code.nregs)
            let v ← getV n b (keyOfNum x)
            let (regs, fregs) ← vmTake
            match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
        | _ =>
          vmStash regs fregs (bp + code.nregs)
          let v ← getV n b (keyOfNum x)
          let (regs, fregs) ← vmTake
          match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
      | _, _ =>
        let kv := vmRd regs fregs (bp + i)
        vmStash regs fregs (bp + code.nregs)
        let v ← vmGetIndex n b kv
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .setIndex o i src =>
      let b := vmRd regs fregs (bp + o)
      let kv := vmRd regs fregs (bp + i)
      let v := vmRd regs fregs (bp + src)
      vmStash regs fregs (bp + code.nregs)
      if let .undef := b then throwErr .type "Cannot read properties of undefined"
      if let .null := b then throwErr .type "Cannot read properties of null"
      match b, kv with
      | .obj id, .num x =>
        let isIdx := x ≥ 0 && x < maxIndexF && x.floor == x
        let done ← if isIdx then setElem id x.toUInt64.toNat v else pure false
        if !done then putV n b (keyOfNum x) v code.strict
      | _, _ =>
        let key ← toKey n kv
        putV n b key v code.strict
      let (regs, fregs) ← vmTake
      vmLoop n code (pc + 1) bp env fr regs fregs
    | .call dst f thisR base k what =>
      let fv := vmRd regs fregs (bp + f)
      let thisV := if thisR == noReg then Value.undef else vmRd regs fregs (bp + thisR)
      let h ← get
      let callee := match fv with
        | .obj id => match (h.obj id).kind with
          | .closure fd cenv capThis _ _ _ => match fd.info.code with
            | some c => some (c, cenv, capThis)
            | none => none
          | _ => none
        | _ => none
      -- a primitive `this` for a sloppy function needs an object made: the general path
      let primThis := match thisV with | .undef | .null | .obj _ => false | _ => true
      let callee := match callee with
        | some (c, cenv, capThis) => if primThis && !c.isArrow && !c.strict then none else some (c, cenv, capThis)
        | none => none
      match callee with
      | some (c, cenv, capThis) =>
        tickCall
        let depth := (match fr with | f0 :: _ => f0.depth + 1 | [] => 1)
        if depth > vmMaxDepth then
          vmStash regs fregs (bp + code.nregs)
          throwErr .range "Maximum call stack size exceeded"
        let bp' := bp + base
        let need := bp' + c.nregs + 1
        let regs := vmGrowRegs regs need
        let fregs := vmGrowF fregs need
        -- missing arguments are undefined, extra ones are not read; the rest of the frame is cleared
        let regs := vmClear regs (bp' + Nat.min k c.nparams) (c.nvars - Nat.min k c.nparams)
        let thisC ← if c.isArrow then pure capThis
          else if c.strict then pure thisV
          else match thisV with
            | .undef | .null => pure (.obj (← realm).globalObj)
            | _ => pure thisV
        let regs := match c.thisReg with
          | some r => regs.set! (bp' + r) thisC
          | none => regs
        let frame : VFrame := { code, pc := pc + 1, bp, env, dst, depth }
        vmLoop n c 0 bp' cenv (frame :: fr) regs fregs
      | none =>
        let args := vmArgs regs fregs (bp + base) k (Array.emptyWithCapacity k)
        vmStash regs fregs (bp + code.nregs)
        if !(← isCallable fv) then throwErr .type s!"{what} is not a function"
        let v ← callV n fv thisV args
        let (regs, fregs) ← vmTake
        match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .new dst f base k what =>
      let fv := vmRd regs fregs (bp + f)
      let args := vmArgs regs fregs (bp + base) k (Array.emptyWithCapacity k)
      vmStash regs fregs (bp + code.nregs)
      if !(← isConstructor fv) then throwErr .type s!"{what} is not a constructor"
      let v ← construct n fv args fv
      let (regs, fregs) ← vmTake
      match (v) with
          | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
    | .ret a =>
      let v := if a == noReg then Value.undef else vmRd regs fregs (bp + a)
      match fr with
      | [] =>
        vmStash regs fregs bp
        pure v
      | f0 :: rest =>
        match v with
        | .num x => vmLoop n f0.code f0.pc f0.bp f0.env rest (regs.set! (f0.bp + f0.dst) .fl) (fregs.set! (f0.bp + f0.dst) x)
        | _ => vmLoop n f0.code f0.pc f0.bp f0.env rest (regs.set! (f0.bp + f0.dst) v) fregs
    | .arr dst base k =>
      let es := vmArgs regs fregs (bp + base) k (Array.emptyWithCapacity k)
      let a ← newArray es
      vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) a) fregs
    | .obj dst =>
      let id ← newObject
      vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) (.obj id)) fregs
    | .defProp o k src =>
      let v := vmRd regs fregs (bp + src)
      match regs[bp + o]! with
      | .obj id => defineOwn id k (.data v true true true); vmLoop n code (pc + 1) bp env fr regs fregs
      | _ => vmLoop n code (pc + 1) bp env fr regs fregs
    | .throw a =>
      let v := vmRd regs fregs (bp + a)
      vmStash regs fregs (bp + code.nregs)
      throw (.throw v)
termination_by structural n _ _ _ _ _ _ _ => n

/-- Enter a compiled function from the evaluator. -/
def vmEnter : Nat → Code → Nat → Value → Value → Array Value → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, c, env, capThis, thisV, args => do
    let thisC ← if c.isArrow then pure capThis
      else if c.strict then pure thisV
      else match thisV with
        | .undef | .null => pure (.obj (← realm).globalObj)
        | .obj _ => pure thisV
        | v => do pure (.obj (← toObj n v))
    let base := (← get).vmTop
    let (regs, fregs) ← vmTake
    let need := base + c.nregs + 1
    let regs := vmGrowRegs regs need
    let fregs := vmGrowF fregs need
    let k := Nat.min args.size c.nparams
    let (regs, fregs) := vmFill regs fregs base args k 0
    let regs := vmClear regs (base + k) (c.nvars - k)
    let regs := match c.thisReg with
      | some r => regs.set! (base + r) thisC
      | none => regs
    tryCatch (do
        let v ← vmLoop n c 0 base env [] regs fregs
        modify fun h => { h with vmTop := base }
        pure v)
      fun e => do
        modify fun h => { h with vmTop := base }
        throw e
termination_by structural n _ _ _ _ _ => n


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
        charge (min k 10000000 / 64)
        (List.range (min k 10000000)).toArray.mapM fun i => getV n v (toString i)
    | .str s => pure ((charsOf s).map fun c => .str (String.singleton c))
    | .undef | .null => throwErr .type "Array.prototype method called on null or undefined"
    | _ => pure #[]
termination_by structural n _ => n

/-- Element `i` of the object `oid` as the Array iteration methods read it (§23.1.3): `none`
when `probe` asks HasProperty first and the object has no such element (a hole), else its
[[Get]]. An Array's own element is read directly; anything else (an array-like, a hole, an
index past a shrunk array) through HasProperty and [[Get]], so getters and the prototype
chain are seen at the step the Standard reads them. -/
def elemAt : Nat → Nat → Nat → Bool → M (Option Value)
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, oid, i, probe => do
    if let .array es := (← getObj oid).kind then
      if h : i < es.size then
        match es[i] with
        | .hole => pure ()
        | v => return some v
    let k := toString i
    if probe && !(← hasProp n oid k) then return none
    pure (some (← getV n (.obj oid) k))
termination_by structural n _ _ _ => n

def iterArray : Nat → Native → Value → Value → Value → Nat → Nat → Array Value → M Value
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, f, thisArg, arr, len, i, acc => do
    if i < len then
      let oid := match arr with | .obj o => o | _ => 0
      -- find and findIndex read every index; the others skip what HasProperty says is absent
      match ← elemAt n oid i (arrayProbes id) with
      -- map's result keeps the index (as undefined: an Array here has no holes)
      | none => iterArray n id f thisArg arr len (i + 1) (if id == .arrayMap then acc.push .undef else acc)
      | some x =>
      let r ← callV n f thisArg #[x, .num (Float.ofNat i), arr]
      match id with
      | .arrayMap => iterArray n id f thisArg arr len (i + 1) (acc.push r)
      | .arrayFilter => iterArray n id f thisArg arr len (i + 1) (if toBool r then acc.push x else acc)
      | .arraySome => if toBool r then pure (.bool true) else iterArray n id f thisArg arr len (i + 1) acc
      | .arrayEvery => if toBool r then iterArray n id f thisArg arr len (i + 1) acc else pure (.bool false)
      | .arrayFind => if toBool r then pure x else iterArray n id f thisArg arr len (i + 1) acc
      | .arrayFindIndex => if toBool r then pure (.num (Float.ofNat i)) else iterArray n id f thisArg arr len (i + 1) acc
      | _ => iterArray n id f thisArg arr len (i + 1) acc
    else
      match id with
      | .arrayMap | .arrayFilter => newArray acc
      | .arraySome => pure (.bool false)
      | .arrayEvery => pure (.bool true)
      | .arrayFindIndex => pure (.num (-1))
      | _ => pure .undef
termination_by structural n _ _ _ _ _ _ _ => n

def reduceArray : Nat → Value → Value → Nat → Nat → Value → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, f, arr, len, i, acc => do
    if i < len then
      let oid := match arr with | .obj o => o | _ => 0
      match ← elemAt n oid i true with
      | none => reduceArray n f arr len (i + 1) acc
      | some x =>
        let acc ← callV n f .undef #[acc, x, .num (Float.ofNat i), arr]
        reduceArray n f arr len (i + 1) acc
    else pure acc
termination_by structural n _ _ _ _ _ => n

/-- LengthOfArrayLike (§7.3.18): ToLength of the object's `length`. -/
def arrayLikeLength : Nat → Value → M Nat
  | 0, _ => throw (.halt "fuel")
  | n + 1, o => do
    match o with
    | .obj id =>
      if let .array es := (← getObj id).kind then return es.size
    | _ => pure ()
    let f := toIntegerOrInf (← toNum n (← getV n o "length"))
    pure (if f ≤ 0 then 0 else if f > 9007199254740991 then 9007199254740991 else f.toUInt64.toNat)
termination_by structural n _ => n

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

/-- ToPropertyDescriptor (§6.2.6.5): the fields of `d` that are present, read in its order,
with its TypeErrors. -/
def toPropDesc : Nat → Value → M Desc
  | 0, _ => throw (.halt "fuel")
  | n + 1, d => do
    if !d.isObj then throwErr .type "Property description must be an object"
    let field (f : String) : M (Option Value) := do
      match d with
      | .obj did => if ← hasProp n did f then pure (some (← getV n d f)) else pure none
      | _ => pure none
    let en ← field "enumerable"
    let cf ← field "configurable"
    let vl ← field "value"
    let wr ← field "writable"
    let gt ← field "get"
    let st ← field "set"
    if let some g := gt then
      if !(← isCallable g) && !(match g with | .undef => true | _ => false) then throwErr .type "Getter must be a function"
    if let some f := st then
      if !(← isCallable f) && !(match f with | .undef => true | _ => false) then throwErr .type "Setter must be a function"
    if (gt.isSome || st.isSome) && (vl.isSome || wr.isSome) then
      throwErr .type "Invalid property descriptor. Cannot both specify accessors and a value or writable attribute"
    pure { value := vl, writable := wr.map toBool, get := gt, set := st,
           enumerable := en.map toBool, configurable := cf.map toBool }
termination_by structural n _ => n

/-- [[DefineOwnProperty]] (§10.1.6, §10.5.6): whether the property was defined as asked. An
ordinary object asks `Desc.allowedOn` (ValidateAndApplyPropertyDescriptor, §10.1.6.3); a Proxy
calls its `defineProperty` trap (or passes the request to its target) and `proxyDefineOk`
checks the trap's true against the target. -/
def defineOwnProp : Nat → Nat → String → Desc → M Bool
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, k, desc => do
    if let .proxy t hnd := (← getObj id).kind then
      let .obj tid := t | throwErr .type s!"Cannot perform 'defineProperty' on a proxy that has been revoked"
      match ← proxyTrap n hnd "defineProperty" with
      | none => return ← defineOwnProp n tid k desc
      | some f =>
        -- FromPropertyDescriptor (§6.2.6.4)
        let dobj ← newObject
        if let some v := desc.value then defineOwn dobj "value" (.data v true true true)
        if let some w := desc.writable then defineOwn dobj "writable" (.data (.bool w) true true true)
        if let some g := desc.get then defineOwn dobj "get" (.data g true true true)
        if let some x := desc.set then defineOwn dobj "set" (.data x true true true)
        if let some e := desc.enumerable then defineOwn dobj "enumerable" (.data (.bool e) true true true)
        if let some c := desc.configurable then defineOwn dobj "configurable" (.data (.bool c) true true true)
        if !toBool (← callV n f hnd #[t, keyValue k, .obj dobj]) then return false
        let td ← ownDesc n tid k
        if !proxyDefineOk (← getObj tid).extensible desc td then
          throwErr .type s!"'defineProperty' on proxy: the trap's answer for '{k}' does not agree with the target"
        return true
    let o0 ← getObj id
    let old := o0.getOwn k
    match old with
    | some p => if !desc.allowedOn p then return false
    | none => if !o0.extensible then return false
    let e := desc.enumerable.getD (match old with | some p => p.enumerable | none => false)
    let c := desc.configurable.getD (match old with | some p => p.configurable | none => false)
    let gt := desc.get
    let st := desc.set
    let vl := desc.value
    if gt.isSome || st.isSome then
      let (og, os) := match old with | some (.acc g s _ _) => (g, s) | _ => (.undef, .undef)
      defineOwn id k (.acc (gt.getD og) (st.getD os) e c)
    else if let (some (.acc g s _ _), true) := (old, vl.isNone && desc.writable.isNone) then
      -- a descriptor with neither kind's fields keeps the accessor
      defineOwn id k (.acc g s e c)
    else
      let w := desc.writable.getD (match old with | some (.data _ w _ _) => w | _ => false)
      let v := vl.getD (match old with | some (.data v ..) => v | _ => .undef)
      match (← getObj id).kind, k with
      | .array _, "length" => putV n (.obj id) k v true
      | _, _ =>
        let o ← getObj id
        match o.kind, arrayIndex? k with
        | .array es, some i =>
          if w && e && c then defineOwn id k (.data v true true true)
          else
            -- leave the fast form: keep the elements, and the length, as ordinary properties
            let o' := (List.range es.size).foldl (fun o j => { o with
                props := o.props.insert (toString j) (.data es[j]! true true true),
                keys := o.keys.push (toString j) }) { o with kind := .ordinary }
            modifyObj id fun _ => o'.putOwn "length" (.data (.num (Float.ofNat es.size)) true false false)
            defineOwn id k (.data v w e c)
            let _ := i
        | _, _ => defineOwn id k (.data v w e c)
    return true
termination_by structural n _ _ _ => n

/-- DefinePropertyOrThrow (§7.3.8) with the descriptor object `d` (Object.defineProperty,
Object.defineProperties, Object.create). -/
def defineFromDescriptor : Nat → Nat → String → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, k, d => do
    let desc ← toPropDesc n d
    if !(← defineOwnProp n id k desc) then
      if (← getObj id).getOwn k |>.isSome then throwErr .type s!"Cannot redefine property: {k}"
      else throwErr .type s!"Cannot define property {k}, object is not extensible"
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
        | c => if c.toNat < 32 then "\\u" ++ String.ofList ((Nat.toDigits 16 c.toNat).leftpad 4 '0') else String.singleton c) ""
        |> jsonLone |> (· ++ "\"")
    let v ← match v with
      | .obj _ =>
        let tj ← getV n v "toJSON"
        if ← isCallable tj then callV n tj v #[] else pure v
      | _ => pure v
    match v with
    | .hole | .fl | .undef => pure .undef
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
          | .str s => pure (some (quote (keyStr k) ++ ":" ++ s))
          | _ => pure none
        pure (.str ("{" ++ ",".intercalate parts ++ "}"))
termination_by structural n _ _ => n

/-- RegExpBuiltinExec (§22.2.7.2) on a RegExp value: the captures, with `lastIndex` read
and written for a global or sticky one. -/
def regexExec : Nat → Value → String → M (Option (Array (Option (Nat × Nat))))
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, rv, s => do
    let (re, _, _) ← regexpOf rv
    let cs ← cachedChars s
    let g := re.flags.global || re.flags.sticky
    let li ← if g then do pure (toIntegerOrInf (← toNum n (← getV n rv "lastIndex"))) else pure 0
    let start := if li ≤ 0 then 0 else li.toUInt64.toNat
    if g && li > Float.ofNat cs.size then
      putV n rv "lastIndex" (.num 0) true
      return none
    -- The matcher's own fuel bounds one match (Re.matchFuel); the steps count it, so a
    -- loop of matches over a long string stops at the budget.
    match Re.exec re cs start with
    | none =>
      -- a sticky match is tried at `start` only (`Re.exec`): the rest of the subject is not
      -- walked, and takes no steps
      charge (if re.flags.sticky then 1 else (cs.size - start) / 64 + 1)
      if g then putV n rv "lastIndex" (.num 0) true
      pure none
    | some caps =>
      let e := match caps[0]? with | some (some (_, b)) => b | _ => start
      charge ((e - start) / 64 + 1)
      if g then
        putV n rv "lastIndex" (.num (Float.ofNat e)) true
      pure (some caps)
termination_by structural n _ _ => n

/-- The array of a match (§22.2.7.2 steps 20 to 34): the strings, `index`, `input`,
`groups`. -/
def matchArray : Nat → Re.Compiled → String → Array (Option (Nat × Nat)) → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | _ + 1, re, s, caps => do
    let cs ← cachedChars s
    let ascii := Str.isAscii s
    let vals := caps.map fun c => match c with
      | some (a, b) => Value.str (if ascii then Str.sliceUnits s a b else Str.ofUnitChars (cs.extract a b))
      | none => .undef
    let arr ← newArray vals
    let .obj aid := arr | pure arr
    let start := match caps[0]? with | some (some (a, _)) => a | _ => 0
    defineOwn aid "index" (.data (.num (Float.ofNat start)) true true true)
    defineOwn aid "input" (.data (.str s) true true true)
    let groups ← if re.names.isEmpty then pure Value.undef else do
      let o ← alloc { proto := .null }
      for (nm, k) in re.names do defineOwn o nm (.data (vals.getD k .undef) true true true)
      pure (.obj o)
    defineOwn aid "groups" (.data groups true true true)
    pure arr
termination_by structural n _ _ _ => n

/-- RegExp, the String methods with a RegExp, Proxy, JSON.parse, ArrayBuffer, the typed
arrays, Date, `performance.now` and the host's natives. -/
def extraNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args, newTarget => do
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    let needNew : String → M Unit := fun nm =>
      if newTarget.isNone then throwErr .type s!"Constructor {nm} requires 'new'" else pure ()
    match id with
    | .regexpCtor =>
      let (src, fl0) ← match a0 with
        | .obj oid => match (← getObj oid).kind with
          | .regexp _ src f => pure (src, f)
          | _ => do pure (← toStr n a0, "")
        | .undef => pure ("", "")
        | _ => do pure (← toStr n a0, "")
      if newTarget.isNone && a1 matches .undef then
        if ← isRegExpV a0 then return a0
      let fl ← match a1 with | .undef => pure fl0 | v => toStr n v
      newRegExp (if src.isEmpty then "(?:)" else src) fl
    | .regexpExec =>
      let s ← toStr n a0
      match ← regexExec n thisV s with
      | none => pure .null
      | some caps => matchArray n (← regexpOf thisV).1 s caps
    | .regexpTest =>
      let s ← toStr n a0
      pure (.bool (← regexExec n thisV s).isSome)
    | .regexpToString =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .regexp _ src f => pure (.str ("/" ++ src ++ "/" ++ f))
        | _ => pure (.str ("/" ++ (← toStr n (← getV n thisV "source")) ++ "/" ++ (← toStr n (← getV n thisV "flags"))))
      | _ => throwErr .type "RegExp.prototype.toString called on a non-object"
    | .regexpGetter which =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .regexp re src f =>
          pure (match which with
            | 0 => .str src
            -- §22.2.6.4 get flags: in the order "dgimsuvy"
            | 1 => .str (String.ofList ("dgimsuvy".toList.filter fun c => f.contains c))
            | 2 => .bool re.flags.global | 3 => .bool re.flags.icase
            | 4 => .bool re.flags.multiline | 5 => .bool re.flags.sticky | 6 => .bool re.flags.unicode
            | _ => .bool re.flags.dotAll)
        | _ => pure (if which == 0 then .str "(?:)" else if which == 1 then .str "" else .undef)
      | _ => throwErr .type "RegExp getter called on a non-object"
    | .stringMatch | .stringMatchAll | .stringSearch =>
      let s ← toStr n (← thisPrim thisV)
      let rx ← if ← isRegExpV a0 then pure a0 else match a0 with
        | .undef => newRegExp "(?:)" (if id == .stringMatchAll then "g" else "")
        | _ => do newRegExp (← toStr n a0) (if id == .stringMatchAll then "g" else "")
      let (re, src, fl) ← regexpOf rx
      if id == .stringSearch then
        return match Re.exec { re with flags := { re.flags with global := false, sticky := re.flags.sticky } } (charsOf s) 0 with
          | some caps => match caps[0]? with | some (some (a, _)) => .num (Float.ofNat a) | _ => .num (-1)
          | none => .num (-1)
      if id == .stringMatch && !re.flags.global then
        return ← match ← regexExec n rx s with
          | none => pure .null
          | some caps => matchArray n re s caps
      if id == .stringMatchAll && !re.flags.global then throwErr .type "String.prototype.matchAll called with a non-global RegExp argument"
      -- All matches, on a copy for matchAll (§22.2.6.9 step 6), from lastIndex 0.
      let rx ← if id == .stringMatchAll then newRegExp src fl else pure rx
      putV n rx "lastIndex" (.num 0) true
      let cs := charsOf s
      let mut out : Array Value := #[]
      for _ in [0:cs.size + 2] do
        match ← regexExec n rx s with
        | none => break
        | some caps =>
          let (a, b) := match caps[0]? with | some (some p) => p | _ => (0, 0)
          out := out.push (← if id == .stringMatch then pure (.str (Str.ofUnitChars (cs.extract a b))) else matchArray n re s caps)
          if a == b then putV n rx "lastIndex" (.num (Float.ofNat (b + 1))) true
      if id == .stringMatch then
        return ← (if out.isEmpty then pure .null else newArray out)
      let arr ← newArray out
      pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter arr 0 0 }))
    | .stringReplace | .stringReplaceAll =>
      let s ← toStr n (← thisPrim thisV)
      let cs := charsOf s
      let (re, _, _) ← regexpOf a0
      if id == .stringReplaceAll && !re.flags.global then
        throwErr .type "replaceAll must be called with a global RegExp"
      let fnRepl ← isCallable a1
      let replStr ← if fnRepl then pure "" else toStr n a1
      if re.flags.global then putV n a0 "lastIndex" (.num 0) true
      let mut found : Array (Array (Option (Nat × Nat))) := #[]
      for _ in [0:cs.size + 2] do
        match ← regexExec n a0 s with
        | none => break
        | some caps =>
          found := found.push caps
          if !re.flags.global then break
          match caps[0]? with
          | some (some (a, b)) => if a == b then putV n a0 "lastIndex" (.num (Float.ofNat (b + 1))) true
          | _ => pure ()
      let mut out := ""
      let mut last := 0
      for caps in found do
        let (a, b) := match caps[0]? with | some (some p) => p | _ => (0, 0)
        if a < last then continue
        let matched := Str.ofUnitChars (cs.extract a b)
        let capStrs : Array (Option String) := (caps.extract 1 caps.size).map fun c =>
          c.map fun (x, y) => Str.ofUnitChars (cs.extract x y)
        let rep ← if fnRepl then do
            let capVals := capStrs.map fun c => match c with | some t => Value.str t | none => .undef
            let groups ← if re.names.isEmpty then pure #[] else do
              let o ← alloc { proto := .null }
              for (nm, k) in re.names do defineOwn o nm (.data (capVals.getD (k - 1) .undef) true true true)
              pure #[Value.obj o]
            toStr n (← callV n a1 .undef (#[.str matched] ++ capVals ++ #[.num (Float.ofNat a), .str s] ++ groups))
          else match substitution replStr matched a cs capStrs re.names with
            | some t => pure t
            | none => throwErr .range "Invalid string length"
        checkStrLen (out.utf8ByteSize + rep.utf8ByteSize)
        out := out ++ Str.ofUnitChars (cs.extract last a) ++ rep
        last := b
      pure (.str (out ++ Str.ofUnitChars (cs.extract last cs.size)))
    | .stringSplit =>
      let s ← toStr n (← thisPrim thisV)
      let cs := charsOf s
      let (re, _, _) ← regexpOf a0
      let lim ← match a1 with
        | .undef => pure 4294967295
        | l => do pure (toUint32 (← toNum n l))
      if lim == 0 then return ← newArray #[]
      let sticky := { re with flags := { re.flags with sticky := true, global := false } }
      if cs.isEmpty then
        return ← newArray (if (Re.exec sticky cs 0).isSome then #[] else #[.str s])
      let mut out : Array Value := #[]
      let mut p := 0
      let mut q := 0
      for _ in [0:cs.size + 1] do
        if q ≥ cs.size then break
        charge (cs.size / 64 + 1)
        match Re.exec sticky cs q with
        | none => q := q + 1
        | some caps =>
          let e := match caps[0]? with | some (some (_, b)) => min b cs.size | _ => q
          if e == p then q := q + 1
          else
            out := out.push (.str (Str.ofUnitChars (cs.extract p q)))
            if out.size == lim then return ← newArray out
            for c in caps.extract 1 caps.size do
              out := out.push (match c with | some (x, y) => .str (Str.ofUnitChars (cs.extract x y)) | none => .undef)
              if out.size == lim then return ← newArray out
            p := e
            q := p
      out := out.push (.str (Str.ofUnitChars (cs.extract p cs.size)))
      newArray out
    | .proxyCtor =>
      needNew "Proxy"
      if !a0.isObj || !a1.isObj then throwErr .type "Cannot create proxy with a non-object as target or handler"
      pure (.obj (← alloc { proto := .null, kind := .proxy a0 a1, extensible := true }))
    | .jsonParse =>
      let s ← toStr n a0
      -- §25.5.1 reads code units: a lone surrogate escape (`"\uD800"`, which RFC 8259's
      -- strict parser refuses) is a string of that unit (`jsonParseText`: the strict parse
      -- first, the escaped reading only when it fails; `jsonParseText_strict`).
      match jsonParseText s with
      | .ok (j, _) => jsonToValue 100000 j
      | .error e => throwErr .syntax s!"Unexpected token in JSON at position {e.pos}"
    | .bufferCtor =>
      needNew "ArrayBuffer"
      let len := toIntegerOrInf (← toNum n a0)
      if len < 0 || len > 268435456 then throwErr .range "Invalid array buffer length"
      -- §25.1.4.1: the `maxByteLength` option makes a resizable buffer
      let max ← match a1 with
        | .obj _ => do
          match ← getV n a1 "maxByteLength" with
          | .undef => pure none
          | v =>
            let m := toIntegerOrInf (← toNum n v)
            if m < 0 || m > 268435456 then throwErr .range "Invalid array buffer max length"
            pure (some m)
        | _ => pure none
      if let some m := max then
        if len > m then throwErr .range "byteLength exceeds maxByteLength"
      let buf ← newBuffer (ByteArray.mk (Array.replicate len.toUInt64.toNat 0))
      if let (.obj bid, some m) := (buf, max) then
        defineOwn bid bufMaxKey (.data (.num m) true false false)
      -- the prototype is the new target's (OrdinaryCreateFromConstructor)
      if let (.obj bid, some nt) := (buf, newTarget) then
        let p ← getV n nt "prototype"
        if p.isObj then modifyObj bid fun o => { o with proto := p }
      pure buf
    | .bufferSlice =>
      let bytes ← match thisV with
        | .obj oid => match (← getObj oid).kind with
          | .buffer b => pure b
          | _ => throwErr .type "ArrayBuffer.prototype.slice called on incompatible receiver"
        | _ => throwErr .type "ArrayBuffer.prototype.slice called on incompatible receiver"
      if let .obj oid := thisV then
        if isDetached (← getObj oid) then throwErr .type "ArrayBuffer.prototype.slice called on a detached ArrayBuffer"
      let a := relIndex (toIntegerOrInf (← toNum n a0)) bytes.size
      let b ← match a1 with
        | .undef => pure bytes.size
        | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) bytes.size)
      newBuffer (bytes.extract a (max a b))
    | .bufferIsView =>
      match a0 with
      | .obj oid => match (← getObj oid).kind with
        | .typed .. | .dataView .. => pure (.bool true)
        | _ => pure (.bool false)
      | _ => pure (.bool false)
    | .typedCtor ty =>
      needNew ((typedNames[ty]?.map (·.1)).getD "TypedArray")
      let es := elemSize ty
      let fromList (xs : Array Value) : M Value := do
        let buf ← newBuffer (ByteArray.mk (Array.replicate (xs.size * es) 0))
        let .obj bid := buf | pure buf
        for i in [0:xs.size] do typedWriteV ty bid 0 i (← typedConv n ty xs[i]!)
        newTyped ty bid 0 xs.size
      match a0 with
      | .obj oid =>
        match (← getObj oid).kind with
        | .buffer bytes =>
          if isDetached (← getObj oid) then throwErr .type "Cannot construct a typed array on a detached ArrayBuffer"
          let off := (toIntegerOrInf (← toNum n a1)).toUInt64.toNat
          if off % es != 0 then throwErr .range s!"start offset of {(typedNames[ty]?.map (·.1)).getD ""} should be a multiple of {es}"
          let len ← match argD args 2 with
            | .undef =>
              if bytes.size < off || (bytes.size - off) % es != 0 then throwErr .range "byte length should be a multiple of the element size"
              pure ((bytes.size - off) / es)
            | v => do pure (toIntegerOrInf (← toNum n v)).toUInt64.toNat
          if off + len * es > bytes.size then throwErr .range "Invalid typed array length"
          newTyped ty oid off len
        | .typed sty sb soff slen =>
          let bytes := bufferBytes (← getObj sb)
          let slen ← liveLen sty sb soff slen
          -- §23.2.5.1.2 InitializeTypedArrayFromTypedArray: BigInts and Numbers do not mix
          if typedIsBig sty != typedIsBig ty then throwErr .type "Content types of the typed arrays differ"
          fromList ((List.range slen).toArray.map fun i => typedRead sty bytes (soff + i * elemSize sty))
        | _ =>
          let itf ← getV n a0 (symKey symIterator)
          if itf.isObj then fromList (← iterToArray n (← getIterator n a0) #[])
          else fromList (← elemsOf n a0)
      | .undef => fromList #[]
      | v =>
        let len := toIntegerOrInf (← toNum n v)
        if len < 0 || len > 268435456 then throwErr .range "Invalid typed array length"
        let buf ← newBuffer (ByteArray.mk (Array.replicate (len.toUInt64.toNat * es) 0))
        let .obj bid := buf | pure buf
        newTyped ty bid 0 len.toUInt64.toNat
    | .dataViewCtor =>
      needNew "DataView"
      let bid ← match a0 with
        | .obj oid => match (← getObj oid).kind with
          | .buffer _ => pure oid
          | _ => throwErr .type "First argument to DataView constructor must be an ArrayBuffer"
        | _ => throwErr .type "First argument to DataView constructor must be an ArrayBuffer"
      let size := (bufferBytes (← getObj bid)).size
      -- ToIndex (§7.1.22) of the offset and of the length.
      let off := toIntegerOrInf (← toNum n a1)
      if off < 0 || off > 9007199254740991 then throwErr .range "Start offset is outside the bounds of the buffer"
      let off := off.toUInt64.toNat
      if off > size then throwErr .range "Start offset is outside the bounds of the buffer"
      let len ← match argD args 2 with
        | .undef => pure (size - off)
        | v => do
          let l := toIntegerOrInf (← toNum n v)
          if l < 0 || l > 9007199254740991 then throwErr .range "Invalid DataView length"
          pure l.toUInt64.toNat
      if off + len > size then throwErr .range "Invalid DataView length"
      let id ← alloc { proto := .obj (← realm).dataViewProto, kind := .dataView bid off len }
      defineOwn id "byteLength" (.data (.num (Float.ofNat len)) false false true)
      defineOwn id "byteOffset" (.data (.num (Float.ofNat off)) false false true)
      defineOwn id "buffer" (.data (.obj bid) false false true)
      pure (.obj id)
    | .dataViewGet ty | .dataViewSet ty =>
      -- GetViewValue and SetViewValue (§25.3.1.5, §25.3.1.6).
      let (b, voff, vlen) ← match thisV with
        | .obj oid => match (← getObj oid).kind with
          | .dataView b off len => pure (b, off, len)
          | _ => throwErr .type "not a DataView"
        | _ => throwErr .type "not a DataView"
      let idx := toIntegerOrInf (← toNum n a0)
      if idx < 0 || idx > 9007199254740991 then throwErr .range "Offset is outside the bounds of the DataView"
      let idx := idx.toUInt64.toNat
      let size := elemSize ty
      let isSet := match id with | .dataViewSet _ => true | _ => false
      -- set: the value is converted before the offset is checked.
      let bits : Option ByteArray ← if !isSet then pure none else
        if typedIsBig ty then do
          let i ← match ← toPrim n a1 "number" with
            | .big i => pure i
            | .bool bb => pure (if bb then 1 else 0)
            | .str t => match strToBigInt t with
              | some i => pure i
              | none => throwErr .syntax s!"Cannot convert {t} to a BigInt"
            | _ => throwErr .type "Cannot convert value to a BigInt"
          let u := (i.emod (2 ^ 64)).toNat
          pure (some (ByteArray.mk ((List.range 8).toArray.map fun k => (u / 2 ^ (8 * k) % 256).toUInt8)))
        else do pure (some (typedBytes ty (← toNum n a1)))
      let little := toBool (argD args (if isSet then 2 else 1))
      if idx + size > vlen then throwErr .range "Offset is outside the bounds of the DataView"
      let at_ := voff + idx
      match bits with
      | some le =>
        let bs := if little then le else ByteArray.mk le.data.reverse
        modifyObj b fun bo => match bo.kind with
          | .buffer bytes =>
            let bo := { bo with kind := .buffer ByteArray.empty }
            { bo with kind := .buffer (if at_ + size ≤ bytes.size then bs.copySlice 0 bytes at_ size else bytes) }
          | _ => bo
        pure .undef
      | none =>
        let bytes := bufferBytes (← getObj b)
        if at_ + size > bytes.size then throwErr .type "Cannot perform DataView get on a detached ArrayBuffer"
        let raw := bytes.extract at_ (at_ + size)
        let le := if little then raw else ByteArray.mk raw.data.reverse
        if typedIsBig ty then
          let u := (List.range 8).foldl (fun a k => a + (le.get! k).toNat * 2 ^ (8 * k)) 0
          pure (.big (if ty == 9 && u ≥ 2 ^ 63 then (u : Int) - 2 ^ 64 else u))
        else pure (typedRead ty le 0)
    | .typedSet | .typedSubarray | .typedFill =>
      let (ty, b, off, len) ← match thisV with
        | .obj oid => match (← getObj oid).kind with
          | .typed ty b off len => pure (ty, b, off, len)
          | _ => throwErr .type "not a typed array"
        | _ => throwErr .type "not a typed array"
      match id with
      | .typedSet =>
        let at_ := toIntegerOrInf (← toNum n a1)
        if at_ < 0 then throwErr .range "offset is out of bounds"
        if !(← typedInBounds ty b off len) then throwErr .type "set: the typed array is detached or out of bounds"
        let at_ := at_.toUInt64.toNat
        let len ← liveLen ty b off len
        let xs ← elemsOf n a0
        if at_ + xs.size > len then throwErr .range "offset is out of bounds"
        for i in [0:xs.size] do typedWriteV ty b off (at_ + i) (← typedConv n ty xs[i]!)
        pure .undef
      | .typedSubarray =>
        -- the new view on the same buffer: TypedArraySpeciesCreate refuses a detached one
        if isDetached (← getObj b) then throwErr .type "subarray: the buffer is detached"
        let len ← liveLen ty b off len
        let a := relIndex (toIntegerOrInf (← toNum n a0)) len
        let e ← match a1 with
          | .undef => pure len
          | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) len)
        newTyped ty b (off + a * elemSize ty) (if e > a then e - a else 0)
      | _ =>
        -- §23.2.3.9 %TypedArray%.prototype.fill: ValidateTypedArray, the value, then the
        -- indices, then detachment
        if !(← typedInBounds ty b off len) then throwErr .type "fill: the typed array is detached or out of bounds"
        let x ← typedConv n ty a0
        let len0 ← liveLen ty b off len
        let a ← match a1 with | .undef => pure 0 | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) len0)
        let e ← match argD args 2 with | .undef => pure len0 | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) len0)
        let len ← liveLen ty b off len
        if len == 0 && len0 > 0 then throwErr .type "Cannot fill a typed array whose buffer is detached"
        for i in [a:min e len] do typedWriteV ty b off i x
        pure thisV
    | .dateCtor =>
      -- §21.4.2.1 Date (local time is UTC here: JS/Date.lean)
      let now := Date.timeClip ((← hostNowNs) / 1000000).floor
      let some nt := newTarget | return .str (Date.toStr now)
      let t ← if args.size == 0 then pure now
        else if args.size == 1 then do
          match ← thisDate? a0 with
          | some t => pure t
          | none =>
            let v ← toPrim n a0 "default"
            match v with
            | .str s => pure (Date.parse s)
            | v => pure (Date.timeClip (← toNum n v))
        else do
          let mut xs : Array Float := #[]
          for i in [0:min 7 args.size] do xs := xs.push (← toNum n args[i]!)
          pure (Date.timeClip (dateOfParts xs))
      let p ← getV n nt "prototype"
      let id ← alloc { proto := if p.isObj then p else .obj r.dateProto, kind := .prim (.num t) }
      defineOwn id dateKey (.data (.bool true) true false false)
      pure (.obj id)
    | .dateGetTime =>
      match ← thisDate? thisV with
      | some t => pure (.num t)
      | none => throwErr .type "this is not a Date object."
    | .perfNow => pure (.num ((← hostNowNs) / 1000000))
    | .uriFn which =>
      let s ← toStr n a0
      let hex := fun (v : Nat) (w : Nat) =>
        String.ofList ((List.range w).reverse.map fun k => "0123456789ABCDEF".toList[(v / 16 ^ k) % 16]!)
      let hexVal := fun (cs : List Char) => cs.foldl (fun (acc : Option Nat) c =>
        acc.bind fun a => if c.isDigit then some (a * 16 + (c.toNat - 48))
          else if 'a' ≤ c && c ≤ 'f' then some (a * 16 + (c.toNat - 87))
          else if 'A' ≤ c && c ≤ 'F' then some (a * 16 + (c.toNat - 55)) else none) (some 0)
      match which with
      | 0 | 4 =>
        -- encodeURIComponent: the unreserved marks stay, every other code point is its
        -- UTF-8 bytes as %XX; a lone surrogate is a URIError (§19.2.6.5 Encode).
        -- encodeURI (4): the reserved characters and `#` stay too (§19.2.6.3).
        if !Str.isWellFormed s then throwErr .uri "URI malformed"
        let marks := (if which == 4 then "-_.!~*'();/?:@&=+$,#" else "-_.!~*'()").toList
        let keep := fun (c : Char) => c.isAlphanum && c.toNat < 128 || marks.contains c
        pure (.str (String.join ((Str.toHost s).toList.map fun c =>
          if keep c then String.singleton c
          else String.join ((String.singleton c).toUTF8.toList.map fun b => "%" ++ hex b.toNat 2))))
      | 1 | 5 =>
        -- decodeURIComponent: %XX sequences are UTF-8; anything malformed is a URIError.
        -- a run of %XX is UTF-8 text (host text: `Str.ofHost`); other characters stay.
        -- decodeURI (5): the escape of a reserved character or of `#` stays as it is written
        -- (§19.2.6.1, §19.2.6.6 Decode with the preserved set).
        let preserve : List Char := if which == 5 then ";/?:@&=+$,#".toList else []
        let cs := s.toList.toArray
        let mut out := ""
        let mut pend := ByteArray.empty
        let mut i := 0
        for _ in [0:cs.size + 1] do
          let c := cs.getD i ' '
          let isEsc := i < cs.size && c == '%'
          let esc := if isEsc && i + 2 < cs.size then hexVal [cs[i+1]!, cs[i+2]!] else none
          if isEsc && esc.isNone then throwErr .uri "URI malformed"
          let kept := match esc with
            | some v => v < 128 && preserve.contains (Char.ofNat v)
            | none => false
          match esc, kept with
          | some v, false => pend := pend.push v.toUInt8; i := i + 3
          | _, _ =>
            if pend.size > 0 then
              match String.fromUTF8? pend with
              | some r => out := out ++ Str.ofHost r
              | none => throwErr .uri "URI malformed"
              pend := ByteArray.empty
            if i ≥ cs.size then break
            if kept then
              out := ((out.push c).push (cs.getD (i + 1) ' ')).push (cs.getD (i + 2) ' '); i := i + 3
            else
              out := out.push c; i := i + 1
        pure (.str (Str.canonical out))
      | 2 =>
        -- escape (§B.2.1.1): code units, as %XX or %uXXXX.
        let keep := fun (c : Char) => c.isAlphanum && c.toNat < 128 || "@*_+-./".toList.contains c
        let unit := fun (u : Nat) => if u < 256 then "%" ++ hex u 2 else "%u" ++ hex u 4
        pure (.str (String.join ((Str.units s).map fun u =>
          if u < 128 && keep (Char.ofNat u) then String.singleton (Char.ofNat u) else unit u)))
      | _ =>
        -- unescape (§B.2.1.2): %XX and %uXXXX are code units (the other characters' units
        -- are taken as they are)
        let cs := (Str.units s).toArray.map Str.unitChar
        let mut units : Array Nat := #[]
        let mut i := 0
        for _ in [0:cs.size] do
          if i ≥ cs.size then break
          let c := cs[i]!
          if c == '%' && i + 5 < cs.size + 0 && cs[i+1]! == 'u' then
            match hexVal [cs[i+2]!, cs[i+3]!, cs[i+4]!, cs[i+5]!] with
            | some v => units := units.push v; i := i + 6
            | none => units := units.push (Str.charUnit c); i := i + 1
          else if c == '%' && i + 2 < cs.size then
            match hexVal [cs[i+1]!, cs[i+2]!] with
            | some v => units := units.push v; i := i + 3
            | none => units := units.push (Str.charUnit c); i := i + 1
          else
            units := units.push (Str.charUnit c); i := i + 1
        -- the units as a string: a lone surrogate stays one (§6.1.4, `Str`)
        pure (.str (Str.ofUnitsFast units.toList))
    | .host k => callHost k args
    | _ => throwErr .type "not a function"
termination_by structural n _ _ _ _ => n

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
      match id with
      | .stringCharAt =>
        let i := toIntegerOrInf (← toNum n a0)
        if i < 0 then pure (.str "") else
        if Str.isAscii s then pure (.str ((Str.unitStrAt? s i.toUInt64.toNat).getD "")) else
        -- not ASCII: the units of `cachedChars` (`cachedReceiverCost`)
        pure (.str (((← cachedChars s)[i.toUInt64.toNat]?.map String.singleton).getD ""))
      | .stringCharCodeAt =>
        let i := toIntegerOrInf (← toNum n a0)
        if i < 0 then pure (.num nan) else
        let u ← if Str.isAscii s then pure (Str.unitAt? s i.toUInt64.toNat)
          else do pure ((← cachedChars s)[i.toUInt64.toNat]?.map Str.charUnit)
        pure (.num (match u with | some u => Float.ofNat u | none => nan))
      | _ =>
        -- the unit count only: `charsOf` is made by the methods that walk the string
        let len := Str.jsLength s
        match id with
        | .stringIndexOf =>
          let p ← toStr n a0
          let st := relIndex (toIntegerOrInf (← toNum n a1)) len
          let st := if (toIntegerOrInf (← toNum n a1)) < 0 then 0 else st
          pure (.num (match indexOfFrom s p st with | some i => Float.ofNat i | none => -1))
        | .stringLastIndexOf =>
          let p ← toStr n a0
          -- §22.1.3.11: a position that is NaN (so `undefined`) is +∞
          let np ← toNum n a1
          let start := if np.isNaN then len else clampPos np len
          pure (.num (match lastIndexOfFrom s p start with | some i => Float.ofNat i | none => -1))
        | .stringIncludes =>
          let p ← toStr n a0
          pure (.bool (indexOfFrom s p (clampPos (← toNum n a1) len)).isSome)
        | .stringStartsWith =>
          let p ← toStr n a0
          pure (.bool (unitsAt s p (clampPos (← toNum n a1) len)))
        | .stringEndsWith =>
          let p ← toStr n a0
          let e ← match a1 with | .undef => pure len | v => do pure (clampPos (← toNum n v) len)
          let m := Str.jsLength p
          pure (.bool (m ≤ e && unitsAt s p (e - m)))
        | .stringSlice =>
          let st := relIndex (← toNum n a0) len
          let en ← match a1 with | .undef => pure len | v => do pure (relIndex (← toNum n v) len)
          charge ((en - st) / 64)
          pure (.str (if st < en then substr s st en else ""))
        | .stringSubstring =>
          let clamp (x : Float) : Nat :=
            let x := toIntegerOrInf x
            if x < 0 then 0 else if x > Float.ofNat len then len else x.toUInt64.toNat
          let st := clamp (← toNum n a0)
          let en ← match a1 with | .undef => pure len | v => do pure (clamp (← toNum n v))
          charge ((max st en - min st en) / 64)
          pure (.str (substr s (min st en) (max st en)))
        | .stringSubstr =>
          let st := relIndex (← toNum n a0) len
          let len ← match a1 with
            | .undef => pure (len - st)
            | v => do
              let l := toIntegerOrInf (← toNum n v)
              pure (if l < 0 then 0 else min l.toUInt64.toNat (len - st))
          charge (len / 64)
          pure (.str (substr s st (st + len)))
        | .stringToUpperCase => pure (.str s.toUpper)
        | .stringToLowerCase => pure (.str s.toLower)
        | .stringTrim => pure (.str (trimJs s))
        | .stringRepeat =>
          let c := toIntegerOrInf (← toNum n a0)
          if c < 0 || c.isInf then throwErr .range "Invalid count value"
          let bytes := c.toUInt64.toNat * s.utf8ByteSize
          if bytes > maxStringBytes then throwErr .range "Invalid string length"
          charge (bytes / 64)
          pure (.str (Str.canonical (repeatStr s c.toUInt64.toNat)))
        | .stringConcat =>
          let parts ← args.toList.mapM (toStr n)
          checkStrLen (parts.foldl (fun acc t => acc + t.utf8ByteSize) s.utf8ByteSize)
          pure (.str (Str.canonical (s ++ String.join parts)))
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

/-- ArrayBuffer `resize` and `transfer` and its accessors, SharedArrayBuffer, %TypedArray%
(the constructor, `from`, `of`, the accessors and the methods that answer typed arrays),
Atomics without waiting, and `String.prototype.isWellFormed`/`toWellFormed`. -/
def moreNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args, newTarget => do
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    let thisBuf (shared : Bool) (what : String) : M (Nat × Obj) := do
      match thisV with
      | .obj oid =>
        let o ← getObj oid
        match o.kind with
        | .buffer _ =>
          if hiddenFlag o bufSharedKey == shared then pure (oid, o)
          else throwErr .type s!"{what} called on incompatible receiver"
        | _ => throwErr .type s!"{what} called on incompatible receiver"
      | _ => throwErr .type s!"{what} called on incompatible receiver"
    let thisTyped (what : String) : M (Nat × Nat × Nat × Nat) := do
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .typed ty b off len => pure (ty, b, off, len)
        | _ => throwErr .type s!"{what}: this is not a typed array"
      | _ => throwErr .type s!"{what}: this is not a typed array"
    -- ValidateTypedArray (§23.2.4.4): a typed array whose view is inside a live buffer
    let validTyped (what : String) : M (Nat × Nat × Nat × Nat) := do
      let (ty, b, off, len) ← thisTyped what
      if !(← typedInBounds ty b off len) then
        throwErr .type s!"{what}: the typed array is detached or out of bounds"
      pure (ty, b, off, len)
    -- a new typed array of type `ty` holding these (already converted) values
    let fresh (ty : Nat) (xs : Array Value) : M Value := do
      let buf ← newBuffer (ByteArray.mk (Array.replicate (xs.size * elemSize ty) 0))
      let .obj bid := buf | pure buf
      for i in [0:xs.size] do typedWriteV ty bid 0 i xs[i]!
      newTyped ty bid 0 xs.size
    let valuesOf (ty b off len : Nat) : M (Array Value) := do
      let len ← liveLen ty b off len
      let bytes := bufferBytes (← getObj b)
      pure ((List.range len).toArray.map fun i => typedRead ty bytes (off + i * elemSize ty))
    let maxOption : M (Option Float) := do
      match a1 with
      | .obj _ => match ← getV n a1 "maxByteLength" with
        | .undef => pure none
        | v => do
          let m := toIntegerOrInf (← toNum n v)
          if m < 0 || m > 268435456 then throwErr .range "Invalid array buffer max length"
          pure (some m)
      | _ => pure none
    let resized (bytes : ByteArray) (l : Nat) : ByteArray :=
      if l ≤ bytes.size then bytes.extract 0 l else bytes ++ ByteArray.mk (Array.replicate (l - bytes.size) 0)
    match id with
    | (.x (.bufferGetter which)) =>
      let (_, o) ← thisBuf false "ArrayBuffer.prototype accessor"
      let size := if isDetached o then 0 else (bufferBytes o).size
      match which with
      | 0 => pure (.num (Float.ofNat size))
      | 1 => pure (.num (Float.ofNat (if isDetached o then 0 else (hiddenNum o bufMaxKey).getD size)))
      | 2 => pure (.bool (hiddenNum o bufMaxKey).isSome)
      | _ => pure (.bool (isDetached o))
    | (.x .bufferResize) =>
      let (oid, o) ← thisBuf false "ArrayBuffer.prototype.resize"
      let some m := hiddenNum o bufMaxKey | throwErr .type "ArrayBuffer.prototype.resize called on a fixed-length ArrayBuffer"
      let l := toIntegerOrInf (← toNum n a0)
      if isDetached (← getObj oid) then throwErr .type "ArrayBuffer.prototype.resize called on a detached ArrayBuffer"
      if l < 0 || l > Float.ofNat m then throwErr .range "Invalid length for ArrayBuffer.prototype.resize"
      modifyObj oid fun bo => match bo.kind with
        | .buffer bytes =>
          let bo := { bo with kind := .buffer ByteArray.empty }
          { bo with kind := .buffer (resized bytes l.toUInt64.toNat) }
        | _ => bo
      pure .undef
    | (.x (.bufferTransfer fixed)) =>
      -- §25.1.6.9 ArrayBufferCopyAndDetach
      let (oid, o) ← thisBuf false "ArrayBuffer.prototype.transfer"
      let bytes := bufferBytes o
      let l ← match a0 with
        | .undef => pure bytes.size
        | v => do
          let l := toIntegerOrInf (← toNum n v)
          if l < 0 || l > 268435456 then throwErr .range "Invalid array buffer length"
          pure l.toUInt64.toNat
      if isDetached (← getObj oid) then throwErr .type "Cannot transfer a detached ArrayBuffer"
      let max := if fixed then none else hiddenNum o bufMaxKey
      if let some m := max then
        if l > m then throwErr .range "Invalid length for ArrayBuffer.prototype.transfer"
      let nb ← newBuffer (resized bytes l)
      if let (.obj nid, some m) := (nb, max) then
        defineOwn nid bufMaxKey (.data (.num (Float.ofNat m)) true false false)
      modifyObj oid fun bo => { bo with kind := .buffer ByteArray.empty }
      defineOwn oid bufDetachedKey (.data (.bool true) true false false)
      pure nb
    | (.x .sharedCtor) =>
      let some nt := newTarget | throwErr .type "Constructor SharedArrayBuffer requires 'new'"
      let len := toIntegerOrInf (← toNum n a0)
      if len < 0 || len > 268435456 then throwErr .range "Invalid array buffer length"
      let max ← maxOption
      if let some m := max then
        if len > m then throwErr .range "byteLength exceeds maxByteLength"
      let p ← getV n nt "prototype"
      let sid ← alloc { proto := if p.isObj then p else .obj r.sharedBufferProto,
                        kind := .buffer (ByteArray.mk (Array.replicate len.toUInt64.toNat 0)) }
      defineOwn sid bufSharedKey (.data (.bool true) true false false)
      if let some m := max then defineOwn sid bufMaxKey (.data (.num m) true false false)
      pure (.obj sid)
    | (.x (.sharedGetter which)) =>
      let (_, o) ← thisBuf true "SharedArrayBuffer.prototype accessor"
      let size := (bufferBytes o).size
      match which with
      | 0 => pure (.num (Float.ofNat size))
      | 1 => pure (.num (Float.ofNat ((hiddenNum o bufMaxKey).getD size)))
      | _ => pure (.bool (hiddenNum o bufMaxKey).isSome)
    | (.x .sharedGrow) =>
      let (oid, o) ← thisBuf true "SharedArrayBuffer.prototype.grow"
      let some m := hiddenNum o bufMaxKey | throwErr .type "SharedArrayBuffer.prototype.grow called on a fixed-length SharedArrayBuffer"
      let l := toIntegerOrInf (← toNum n a0)
      let size := (bufferBytes o).size
      if l < Float.ofNat size || l > Float.ofNat m then throwErr .range "Invalid length for SharedArrayBuffer.prototype.grow"
      modifyObj oid fun bo => match bo.kind with
        | .buffer bytes =>
          let bo := { bo with kind := .buffer ByteArray.empty }
          { bo with kind := .buffer (resized bytes l.toUInt64.toNat) }
        | _ => bo
      pure .undef
    | (.x .sharedSlice) =>
      let (_, o) ← thisBuf true "SharedArrayBuffer.prototype.slice"
      let bytes := bufferBytes o
      let a := relIndex (toIntegerOrInf (← toNum n a0)) bytes.size
      let b ← match a1 with
        | .undef => pure bytes.size
        | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) bytes.size)
      let sid ← alloc { proto := .obj r.sharedBufferProto, kind := .buffer (bytes.extract a (max a b)) }
      defineOwn sid bufSharedKey (.data (.bool true) true false false)
      pure (.obj sid)
    | (.x .typedArrayCtor) => throwErr .type "Abstract class TypedArray not directly constructable"
    | (.x .typedOf) | (.x .typedFrom) =>
      -- §23.2.2.1 %TypedArray%.from, §23.2.2.2 %TypedArray%.of: `this` makes the array
      if !(← isConstructor thisV) then throwErr .type "TypedArray.from/of: this is not a constructor"
      let items ← if id == (.x .typedOf) then pure args else do
        let mapFn := a1
        let mapping := match mapFn with | .undef => false | _ => true
        if mapping && !(← isCallable mapFn) then throwErr .type "TypedArray.from: the map function is not callable"
        let usingIter ← match a0 with
          | .undef | .null => pure Value.undef
          | _ => getV n a0 (symKey symIterator)
        let vs ← match usingIter with
          | .undef | .null => do elemsOf n (.obj (← toObj n a0))
          | f => do
            if !(← isCallable f) then throwErr .type "TypedArray.from: @@iterator is not callable"
            iterToArray n (← getIterator n a0) #[]
        if mapping then
          let mut out := #[]
          for i in [0:vs.size] do out := out.push (← callV n mapFn (argD args 2) #[vs[i]!, .num (Float.ofNat i)])
          pure out
        else pure vs
      let ta ← construct n thisV #[.num (Float.ofNat items.size)] thisV
      match ta with
      | .obj tid => match (← getObj tid).kind with
        | .typed ty b off len =>
          if (← liveLen ty b off len) < items.size then throwErr .type "TypedArray.from/of: the new typed array is too short"
        | _ => throwErr .type "TypedArray.from/of: the constructor did not make a typed array"
      | _ => throwErr .type "TypedArray.from/of: the constructor did not make a typed array"
      for i in [0:items.size] do putV n ta (toString i) items[i]! true
      pure ta
    | (.x (.typedGetter which)) =>
      let info : Option (Nat × Nat × Nat × Nat) ← match thisV with
        | .obj oid => do
          match (← getObj oid).kind with
          | .typed ty b off len => pure (some (ty, b, off, len))
          | _ => pure none
        | _ => pure none
      let some (ty, b, off, len) := info
        | if which == 4 then pure .undef else throwErr .type "TypedArray accessor called on incompatible receiver"
      let live ← liveLen ty b off len
      let gone := live == 0 && len > 0 || isDetached (← getObj b)
      match which with
      | 0 => pure (.obj b)
      | 1 => pure (.num (Float.ofNat (live * elemSize ty)))
      | 2 => pure (.num (Float.ofNat (if gone then 0 else off)))
      | 3 => pure (.num (Float.ofNat live))
      | _ => pure (.str ((typedNames[ty]?.map (·.1)).getD ""))
    | (.x (.typedGeneric k)) =>
      -- the %TypedArray%.prototype methods whose steps are Array.prototype's after
      -- ValidateTypedArray: that function, kept hidden on %TypedArray%.prototype
      let nm := typedGenericNames.getD k ("", 0)
      let _ ← validTyped s!"%TypedArray%.prototype.{nm.1}"
      let tp ← match (← getObj r.typedArrayCtor).getOwn "prototype" with
        | some (.data (.obj p) ..) => pure p
        | _ => throwErr .type "no %TypedArray%.prototype"
      match (← getObj tp).getOwn (typedGenericKey nm.1) with
      | some (.data f ..) => callV n f thisV args
      | _ => throwErr .type s!"%TypedArray%.prototype.{nm.1} is missing"
    | (.x (.typedMethod which)) =>
      let (ty, b, off, len) ← validTyped "TypedArray method"
      let xs ← valuesOf ty b off len
      let size := xs.size
      let writeAll (vs : Array Value) : M Unit := do
        let live ← liveLen ty b off len
        for i in [0:min vs.size live] do typedWriteV ty b off i vs[i]!
      -- §23.2.3.29 SortCompare: numeric order, -0 before +0, NaN last; or the comparator
      let numLe (x y : Value) : Bool := match x, y with
        | .num p, .num q => if p.isNaN then q.isNaN else if q.isNaN then true
          else p < q || (p == q && (isNegZero p || !isNegZero q))
        | .big p, .big q => p ≤ q
        | _, _ => true
      let sorted (cmp : Value) : M (Array Value) := do
        match cmp with
        | .undef => pure (xs.toList.mergeSort numLe).toArray
        | _ =>
          if !(← isCallable cmp) then throwErr .type "The comparison function must be callable"
          pure (← mergeSort n cmp xs.toList).toArray
      let callback (f : Value) : M Unit := do
        if !(← isCallable f) then throwErr .type "callback is not a function"
      match which with
      | 0 =>
        -- copyWithin (§23.2.3.6): the elements move as the bytes would
        let to := relIndex (toIntegerOrInf (← toNum n a0)) size
        let from_ := relIndex (toIntegerOrInf (← toNum n a1)) size
        let fin ← match argD args 2 with
          | .undef => pure size
          | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) size)
        let live ← liveLen ty b off len
        if live == 0 && size > 0 then throwErr .type "Cannot copy within a detached typed array"
        let count := min (fin - from_) (min (size - to) (live - min live from_))
        let mut ys := xs
        for i in [0:count] do
          if from_ + i < xs.size && to + i < ys.size then ys := ys.set! (to + i) xs[from_ + i]!
        writeAll ys
        pure thisV
      | 1 => writeAll xs.reverse; pure thisV
      | 2 =>
        let st := relIndex (toIntegerOrInf (← toNum n a0)) size
        let en ← match a1 with
          | .undef => pure size
          | v => do pure (relIndex (toIntegerOrInf (← toNum n v)) size)
        let vs ← valuesOf ty b off len
        fresh ty (vs.extract st (max st en))
      | 3 => writeAll (← sorted a0); pure thisV
      | 4 =>
        let k := toIntegerOrInf (← toNum n a0)
        let i := if k < 0 then Float.ofNat size + k else k
        if i < 0 || i ≥ Float.ofNat size then pure .undef else pure xs[i.toUInt64.toNat]!
      | 5 =>
        -- lastIndexOf (§23.2.3.20): strict equality, from the end
        let start ← if args.size > 1 then do
            let k := toIntegerOrInf (← toNum n a1)
            pure (if k < 0 then Float.ofNat size + k else k)
          else pure (Float.ofNat size - 1)
        if start < 0 then return .num (-1)
        let st := min (size - 1) start.toUInt64.toNat
        let live ← liveLen ty b off len
        let found := (List.range (st + 1)).reverse.find? fun i => i < live && strictEq xs[i]! a0
        pure (.num (match found with | some i => Float.ofNat i | none => -1))
      | 6 =>
        callback a0
        let mut kept := #[]
        for i in [0:size] do
          if toBool (← callV n a0 a1 #[xs[i]!, .num (Float.ofNat i), thisV]) then kept := kept.push xs[i]!
        fresh ty kept
      | 7 =>
        callback a0
        let mut out := #[]
        for i in [0:size] do
          out := out.push (← typedConv n ty (← callV n a0 a1 #[xs[i]!, .num (Float.ofNat i), thisV]))
        fresh ty out
      | 8 => fresh ty xs.reverse
      | 9 =>
        match a0 with
        | .undef => pure ()
        | f => callback f
        fresh ty (← sorted a0)
      | 10 =>
        -- with (§23.2.3.36): the index is checked against the length after the value converts
        let k := toIntegerOrInf (← toNum n a0)
        let i := if k < 0 then Float.ofNat size + k else k
        let v ← typedConv n ty a1
        let live ← liveLen ty b off len
        if i < 0 || i ≥ Float.ofNat live then throwErr .range "Invalid typed array index"
        fresh ty (xs.set! i.toUInt64.toNat v)
      | 11 | 12 =>
        callback a0
        let mut found : Option Nat := none
        for j in [0:size] do
          let i := size - 1 - j
          if found.isNone then
            if toBool (← callV n a0 a1 #[xs[i]!, .num (Float.ofNat i), thisV]) then found := some i
        match found with
        | some i => pure (if which == 11 then xs[i]! else .num (Float.ofNat i))
        | none => pure (if which == 11 then .undef else .num (-1))
      | _ =>
        -- reduceRight (§23.2.3.24)
        callback a0
        if size == 0 && args.size < 2 then throwErr .type "Reduce of empty array with no initial value"
        let mut acc := if args.size ≥ 2 then a1 else xs[size - 1]!
        let last := if args.size ≥ 2 then size else size - 1
        for j in [0:last] do
          let i := last - 1 - j
          acc ← callV n a0 .undef #[acc, xs[i]!, .num (Float.ofNat i), thisV]
        pure acc
    | (.x (.atomics op)) =>
      if op == 4 then
        let k := toIntegerOrInf (← toNum n a0)
        return .bool (k == 1 || k == 2 || k == 4 || k == 8)
      -- ValidateIntegerTypedArray (§25.4.3.1), ValidateAtomicAccess (§25.4.3.2)
      let (ty, b, off, len) ← match a0 with
        | .obj oid => match (← getObj oid).kind with
          | .typed ty b off len => pure (ty, b, off, len)
          | _ => throwErr .type "Atomics operation on an object that is not a typed array"
        | _ => throwErr .type "Atomics operation on a value that is not a typed array"
      let okTy := if op == 10 then ty == 5 || ty == 9 else [0, 1, 3, 4, 5, 6, 9, 10].contains ty
      if !okTy then throwErr .type "Atomics operation on a typed array of the wrong element type"
      if isDetached (← getObj b) then throwErr .type "Atomics operation on a detached ArrayBuffer"
      let idx := toIntegerOrInf (← toNum n a1)
      if idx < 0 || idx > 9007199254740991 then throwErr .range "Invalid atomic access index"
      if idx ≥ Float.ofNat (← liveLen ty b off len) then throwErr .range "Invalid atomic access index"
      let i := idx.toUInt64.toNat
      let at_ := off + i * elemSize ty
      let read : M Value := do pure (typedRead ty (bufferBytes (← getObj b)) at_)
      if op == 10 then
        -- notify: no agent waits here
        let _ ← toNum n (argD args 2)
        return .num 0
      if op == 5 then return ← read
      let v ← typedConv n ty (argD args 2)
      if op == 7 then
        let v := match v with | .num x => .num (let k := toIntegerOrInf x; if k == 0 then 0 else k) | v => v
        typedWriteV ty b off i v
        return v
      let asInt : Value → Int := fun x => match x with
        | .big i => i
        | .num x => toInt32Wide x
        | _ => 0
      let mk : Int → Value := fun i => if typedIsBig ty then .big i else .num (Float.ofInt i)
      let raw : Value → ByteArray := fun x => match x with
        | .big i => bigBytes i
        | .num x => typedBytes ty x
        | _ => ByteArray.empty
      let old ← read
      let o := asInt old
      let x := asInt v
      let newV? : Option Value ← match op with
        | 0 => pure (some (mk (o + x)))
        | 1 => pure (some (mk (bigBits Nat.land o x)))
        | 2 => do
          let rep ← typedConv n ty (argD args 3)
          pure (if (raw v).data == (raw old).data then some rep else none)
        | 3 => pure (some v)
        | 6 => pure (some (mk (bigBits Nat.lor o x)))
        | 8 => pure (some (mk (o - x)))
        | _ => pure (some (mk (bigBits Nat.xor o x)))
      if let some nv := newV? then typedWriteV ty b off i nv
      pure old
    | (.x .iteratorCtor) =>
      -- §27.1.3.1 Iterator: abstract; a subclass may construct
      let some nt := newTarget | throwErr .type "Constructor Iterator requires 'new'"
      if strictEq nt (← getV n (.obj r.globalObj) "Iterator") then throwErr .type "Abstract class Iterator not directly constructable"
      let p ← getV n nt "prototype"
      pure (.obj (← alloc { proto := if p.isObj then p else .obj r.iterProto }))
    | (.x .iteratorConcat) =>
      -- §27.1.3.2.2 Iterator.concat: every argument an object with a callable @@iterator, checked
      -- first; the iterators are made one at a time as the result is read
      let mut items : Array Value := #[]
      for a in args do
        if !a.isObj then throwErr .type "Iterator.concat: an argument is not an object"
        let m ← getV n a (symKey symIterator)
        if !(← isCallable m) then throwErr .type "Iterator.concat: an argument is not iterable"
        items := (items.push a).push m
      let arr ← newArray items
      let h ← alloc { proto := .obj r.iterHelperProto }
      defineOwn h helperIt (.data arr true false false)
      defineOwn h helperNextKey (.data .undef true false false)
      defineOwn h helperKind (.data (.num 6) true false false)
      defineOwn h helperFn (.data .undef true false false)
      defineOwn h helperCount (.data (.num 0) true false false)
      defineOwn h helperInner (.data .undef true false false)
      pure (.obj h)
    | (.x .iteratorFrom) =>
      -- §27.1.3.2.1 Iterator.from: GetIteratorFlattenable, then wrap unless it inherits Iterator.prototype
      let it ← match a0 with
        | .str _ => getIterator n a0
        | .obj _ => do
          let m ← getV n a0 (symKey symIterator)
          match m with
          | .undef | .null => pure a0
          | f =>
            if !(← isCallable f) then throwErr .type "Iterator.from: @@iterator is not callable"
            let it ← callV n f a0 #[]
            if !it.isObj then throwErr .type "Iterator.from: the iterator is not an object"
            pure it
        | _ => throwErr .type "Iterator.from called on a non-object"
      let next ← getV n it "next"
      if ← instOf n it (← getV n (.obj r.globalObj) "Iterator") then return it
      let w ← alloc { proto := .obj r.wrapIterProto }
      defineOwn w helperIt (.data it true false false)
      defineOwn w helperNextKey (.data next true false false)
      defineOwn w helperKind (.data (.num 5) true false false)
      pure (.obj w)
    | (.x (.iterLazy k)) =>
      -- §27.1.4.{5,4,12,3,6}: GetIteratorDirect, the argument checked, a helper made
      if !thisV.isObj then throwErr .type "Iterator.prototype method called on a non-object"
      let lim ← if k == 2 || k == 3 then do
          let x ← toNum n a0
          if x.isNaN then
            iterClose n thisV
            throwErr .range "Iterator helper limit is NaN"
          let x := toIntegerOrInf x
          if x < 0 then
            iterClose n thisV
            throwErr .range "Iterator helper limit is negative"
          pure (Value.num x)
        else do
          if !(← isCallable a0) then
            iterClose n thisV
            throwErr .type "Iterator helper callback is not a function"
          pure a0
      let next ← getV n thisV "next"
      let h ← alloc { proto := .obj r.iterHelperProto }
      defineOwn h helperIt (.data thisV true false false)
      defineOwn h helperNextKey (.data next true false false)
      defineOwn h helperKind (.data (.num (Float.ofNat k)) true false false)
      defineOwn h helperFn (.data lim true false false)
      defineOwn h helperCount (.data (.num 0) true false false)
      defineOwn h helperInner (.data .undef true false false)
      pure (.obj h)
    | (.x (.iterEager k)) =>
      if !thisV.isObj then throwErr .type "Iterator.prototype method called on a non-object"
      if k != 1 && !(← isCallable a0) then
        iterClose n thisV
        throwErr .type "Iterator.prototype method: the callback is not a function"
      let next ← getV n thisV "next"
      let step : M (Option Value) := do
        let r ← callV n next thisV #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n r "done") then pure none else pure (some (← getV n r "value"))
      -- a callback that throws closes the iterator, then the error goes on (§7.4.12)
      let guarded (f : M Value) : M Value := tryCatch f fun e => do
        match e with
        | .throw _ =>
          tryCatch (iterClose n thisV) fun _ => pure ()
          throw e
        | _ => throw e
      let mut acc := if k == 0 then a1 else .undef
      let mut haveAcc := k != 0 || args.size ≥ 2
      let mut out : Array Value := #[]
      let mut i := 0
      for _ in [0:1000000000] do
        let some v ← step | break
        if k == 0 && !haveAcc then
          acc := v; haveAcc := true
        else if k == 0 then
          acc ← guarded (callV n a0 .undef #[acc, v, .num (Float.ofNat i)])
        else if k == 1 then out := out.push v
        else
          let res ← guarded (callV n a0 .undef #[v, .num (Float.ofNat i)])
          if k == 3 && toBool res then
            iterClose n thisV
            return .bool true
          if k == 4 && !toBool res then
            iterClose n thisV
            return .bool false
          if k == 5 && toBool res then
            iterClose n thisV
            return v
        i := i + 1
      match k with
      | 0 => if haveAcc then pure acc else throwErr .type "Reduce of empty iterator with no initial value"
      | 1 => newArray out
      | 3 => pure (.bool false)
      | 4 => pure (.bool true)
      | _ => pure .undef
    | (.x .helperNext) | (.x .helperReturn) =>
      let some (hid, o) ← (match thisV with
          | .obj i => do
            let o ← getObj i
            pure (if (o.props.get? helperKind).isSome then some (i, o) else none)
          | _ => pure none)
        | throwErr .type "Iterator helper method called on an incompatible receiver"
      let field (k : String) : Value := match o.props.get? k with | some (.data v ..) => v | _ => .undef
      let it := field helperIt
      let kind := match field helperKind with | .num x => x.toUInt64.toNat | _ => 0
      let setF (k : String) (v : Value) : M Unit := defineOwn hid k (.data v true false false)
      let result (v : Value) (done : Bool) : M Value := do
        let ro ← newObject
        defineOwn ro "value" (.data v true true true)
        defineOwn ro "done" (.data (.bool done) true true true)
        pure (.obj ro)
      if kind == 5 then
        -- %WrapForValidIteratorPrototype%: the wrapped iterator's own next and return
        if id == (.x .helperNext) then return ← callV n (field helperNextKey) it #[]
        let ret ← getV n it "return"
        match ret with
        | .undef | .null => return ← result .undef true
        | f => return ← callV n f it #[]
      if hiddenFlag o helperRunning then throwErr .type "Iterator helper is already running"
      if id == (.x .helperReturn) then
        if !(hiddenFlag o helperDone) then
          setF helperDone (.bool true)
          match field helperInner with
          | .obj _ => tryCatch (iterClose n (field helperInner)) fun _ => pure ()
          | _ => pure ()
          iterClose n it
        return ← result .undef true
      if hiddenFlag o helperDone then return ← result .undef true
      if kind == 6 then
        -- Iterator.concat's closure (§27.1.3.2.2): each iterable's iterator in turn, its
        -- values yielded again; `helperCount` the next iterable, `helperFn` the inner `next`
        let items ← elemsOf n it
        setF helperRunning (.bool true)
        let out ← tryCatch (do
          let mut answer : Option Value := none
          for _ in [0:1000000000] do
            let o ← getObj hid
            let inner := match o.props.get? helperInner with | some (.data v ..) => v | _ => .undef
            if inner.isObj then
              let nx := match o.props.get? helperFn with | some (.data v ..) => v | _ => .undef
              let r ← callV n nx inner #[]
              if !r.isObj then throwErr .type "Iterator result is not an object"
              if !toBool (← getV n r "done") then
                answer := some (← result (← getV n r "value") false)
                break
              setF helperInner .undef
            else
              let count := match o.props.get? helperCount with | some (.data (.num x) ..) => x.toUInt64.toNat | _ => 0
              if 2 * count + 1 ≥ items.size then
                setF helperDone (.bool true)
                answer := some (← result .undef true)
                break
              let iter ← callV n items[2 * count + 1]! items[2 * count]! #[]
              if !iter.isObj then throwErr .type "Iterator.concat: the iterator is not an object"
              setF helperCount (.num (Float.ofNat (count + 1)))
              setF helperFn (← getV n iter "next")
              setF helperInner iter
          pure answer) fun e => do
            setF helperRunning (.bool false)
            setF helperDone (.bool true)
            throw e
        setF helperRunning (.bool false)
        return ← match out with
          | some v => pure v
          | none => result .undef true
      let next := field helperNextKey
      let fn := field helperFn
      let stepOuter : M (Option Value) := do
        let r ← callV n next it #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n r "done") then pure none else pure (some (← getV n r "value"))
      let finish : M Value := do setF helperDone (.bool true); result .undef true
      let callFn (args : Array Value) : M Value :=
        tryCatch (callV n fn .undef args) fun e => do
          match e with
          | .throw _ =>
            setF helperDone (.bool true)
            tryCatch (iterClose n it) fun _ => pure ()
            throw e
          | _ => throw e
      setF helperRunning (.bool true)
      let out ← tryCatch (do
        let mut answer : Option Value := none
        for _ in [0:1000000000] do
          let o ← getObj hid
          let count := match o.props.get? helperCount with | some (.data (.num x) ..) => x.toUInt64.toNat | _ => 0
          let lim := match fn with | .num x => x | _ => 0
          if kind == 2 && Float.ofNat count ≥ lim then
            setF helperDone (.bool true)
            iterClose n it
            answer := some (← result .undef true); break
          if kind == 4 then
            match o.props.get? helperInner with
            | some (.data inner ..) =>
              if inner.isObj then
                let r ← callV n (← getV n inner "next") inner #[]
                if !r.isObj then throwErr .type "Iterator result is not an object"
                if !toBool (← getV n r "done") then
                  answer := some (← result (← getV n r "value") false); break
                setF helperInner .undef
            | _ => pure ()
          let some v ← stepOuter
            | answer := some (← finish)
              break
          setF helperCount (.num (Float.ofNat (count + 1)))
          match kind with
          | 0 => answer := some (← result (← callFn #[v, .num (Float.ofNat count)]) false); break
          | 1 =>
            if toBool (← callFn #[v, .num (Float.ofNat count)]) then
              answer := some (← result v false)
              break
          | 2 =>
            answer := some (← result v false)
            break
          | 3 =>
            if Float.ofNat count ≥ lim then
              answer := some (← result v false)
              break
          | _ =>
            -- flatMap: GetIteratorFlattenable(mapped, reject strings)
            let mapped ← callFn #[v, .num (Float.ofNat count)]
            if !mapped.isObj then
              setF helperDone (.bool true); iterClose n it
              throwErr .type "flatMap: the mapper did not return an object"
            let m ← getV n mapped (symKey symIterator)
            let inner ← match m with
              | .undef | .null => pure mapped
              | f => callV n f mapped #[]
            if !inner.isObj then throwErr .type "flatMap: the inner iterator is not an object"
            setF helperInner inner
        pure answer) fun e => do setF helperRunning (.bool false); throw e
      setF helperRunning (.bool false)
      match out with
      | some v => pure v
      | none => finish
    | (.x .numberToExponential) | (.x .numberToPrecision) =>
      let x ← match ← thisPrim thisV with
        | .num x => pure x
        | _ => throwErr .type "Number.prototype method requires that 'this' be a Number"
      if id == (.x .numberToPrecision) && (a0 matches .undef) then return .str (numToString x)
      let f := toIntegerOrInf (← toNum n a0)
      if !x.isFinite then return .str (numToString x)
      let (neg, num, den) := NumFmt.ofFloat x
      if id == (.x .numberToExponential) then
        if f < 0 || f > 100 then throwErr .range "toExponential() argument must be between 0 and 100"
        if a0 matches .undef then
          -- as many digits as Number::toString gives
          return .str (NumFmt.expo neg num den (if num == 0 then 0 else NumFmt.shortestFrac x))
        pure (.str (NumFmt.expo neg num den f.toUInt64.toNat))
      else
        if f < 1 || f > 100 then throwErr .range "toPrecision() argument must be between 1 and 100"
        pure (.str (NumFmt.precision neg num den f.toUInt64.toNat))
    -- ==== workers: the structured clone of HTML §2.7 over the heap (JS.Clone) ====
    | (.x .cloneSerialize) =>
      -- `n.serialize(value, transfer)`: the bytes as a new ArrayBuffer; the transferred
      -- ArrayBuffers detached (§2.7.5 step 5).
      let items ← match a1 with
        | .obj tid => do
          match (← getObj tid).kind with
          | .array es => pure es
          | _ => pure #[]
        | _ => pure #[]
      let mut ids : Array Nat := #[]
      for it in items do
        match it with
        | .obj i => ids := ids.push i
        | _ => throwErr .type "DataCloneError: Value in the transfer list is not an ArrayBuffer"
      match Clone.serialize (← get) a0 ids with
      | .error e => throwErr .type ("DataCloneError: " ++ e)
      | .ok (bytes, det) =>
        charge (bytes.size / 64)
        for d in det do
          modifyObj d fun bo => { bo with kind := .buffer ByteArray.empty }
          defineOwn d bufDetachedKey (.data (.bool true) true false false)
        newBuffer bytes
    | (.x .cloneDeserialize) =>
      let bytes ← match a0 with
        | .obj b => do pure (bufferBytes (← getObj b))
        | _ => pure ByteArray.empty
      charge (bytes.size / 64)
      -- the heap is taken out of the state, so its object array is changed in place
      let h ← modifyGet fun h => (h, { h with objs := #[] })
      let (v, h) := Clone.deserializeIn h bytes
      set h
      match v with
      | some v => pure v
      | none => throwErr .type "DataCloneError: the message could not be deserialized"
    | (.x .classicScript) =>
      -- GlobalDeclarationInstantiation (§16.1.7) and the statements, as `runScriptM` (which
      -- comes after this function), with no microtask checkpoint.
      let src ← toStr n a0
      match parseScript src false with
      | .error e => throwErr .syntax e
      | .ok sc =>
        let g := r.globalObj
        let ctx : Ctx := { env := 0, thisV := .obj g, strict := sc.strict }
        for v in sc.vars do
          if ((← getObj g).getOwn v).isNone then defineOwn g v (.data .undef true true false)
        for st in sc.body do
          if let .funDecl name f := st then
            defineOwn g name (.data (← makeClosure ctx f) true true false)
        for st in sc.body do
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
        let _ ← evalStmts n ctx sc.body
        pure .undef
    -- ==== end workers ====
    | (.x (.setMethod k)) =>
      -- the receiver: a Set (§24.2.4, RequireInternalSlot [[SetData]])
      let (sid, es) ← match thisV with
        | .obj i => do
          match (← getObj i).kind with
          | .coll 1 es _ => pure (i, es)
          | _ => throwErr .type "Set.prototype method called on an object that is not a Set"
        | _ => throwErr .type "Set.prototype method called on a value that is not a Set"
      -- GetSetRecord (§24.2.1.2)
      if !a0.isObj then throwErr .type "Set method: the argument is not an object"
      let rawSize ← getV n a0 "size"
      let numSize ← toNum n rawSize
      if numSize.isNaN then throwErr .type "Set method: the argument's size is not a number"
      let otherSize := toIntegerOrInf numSize
      if otherSize < 0 then throwErr .range "Set method: the argument's size is negative"
      let has ← getV n a0 "has"
      if !(← isCallable has) then throwErr .type "Set method: the argument's has is not a function"
      let keys ← getV n a0 "keys"
      if !(← isCallable keys) then throwErr .type "Set method: the argument's keys is not a function"
      let mine : Array Value := es.filterMap (·.map (·.1))
      let inThis (v : Value) : M Bool := do
        match (← getObj sid).kind with
        | .coll _ _ idx => pure (collFind idx v).isSome
        | _ => pure false
      let canon (v : Value) : Value := match v with | .num x => if x == 0 then .num 0 else v | _ => v
      let otherKeys : M (Value × Value) := do
        let it ← callV n keys a0 #[]
        if !it.isObj then throwErr .type "Set method: keys() did not return an object"
        pure (it, ← getV n it "next")
      let stepKeys (it next : Value) : M (Option Value) := do
        let r ← callV n next it #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← getV n r "done") then pure none else pure (some (canon (← getV n r "value")))
      let otherHas (v : Value) : M Bool := do pure (toBool (← callV n has a0 #[v]))
      let thisSize := Float.ofNat mine.size
      let mkSet (vs : Array Value) : M Value := do
        let mut o : Obj := { proto := (← getObj sid).proto, kind := .coll 1 #[] {} }
        for v in vs do o := collPut v v o
        -- %Set.prototype%, not the receiver's
        let sc ← getV n (.obj r.globalObj) "Set"
        let sp ← getV n sc "prototype"
        pure (.obj (← alloc { o with proto := if sp.isObj then sp else o.proto }))
      match k with
      | 0 | 3 =>
        let (it, next) ← otherKeys
        let mut out := mine
        let mut removed : Array Value := #[]
        for _ in [0:1000000000] do
          let some v ← stepKeys it next | break
          if k == 0 then out := out.push v
          else if (← inThis v) then removed := removed.push v
          else if !(out.any (sameValueZero · v)) then out := out.push v
        mkSet (if k == 3 then out.filter (fun x => !(removed.any (sameValueZero · x))) else out)
      | 1 | 2 =>
        if thisSize ≤ otherSize then
          let mut out := #[]
          for v in mine do
            let h ← otherHas v
            if (k == 1 && h) || (k == 2 && !h) then out := out.push v
          mkSet out
        else
          let (it, next) ← otherKeys
          let mut hit : Array Value := #[]
          for _ in [0:1000000000] do
            let some v ← stepKeys it next | break
            if (← inThis v) then hit := hit.push v
          if k == 1 then mkSet (mine.filter fun x => hit.any (sameValueZero · x))
          else mkSet (mine.filter fun x => !(hit.any (sameValueZero · x)))
      | 4 =>
        if thisSize > otherSize then return .bool false
        for v in mine do
          if !(← otherHas v) then return .bool false
        pure (.bool true)
      | 5 =>
        if thisSize < otherSize then return .bool false
        let (it, next) ← otherKeys
        for _ in [0:1000000000] do
          let some v ← stepKeys it next | break
          if !(← inThis v) then
            iterClose n it
            return .bool false
        pure (.bool true)
      | _ =>
        if thisSize ≤ otherSize then
          for v in mine do
            if (← otherHas v) then return .bool false
          pure (.bool true)
        else
          let (it, next) ← otherKeys
          for _ in [0:1000000000] do
            let some v ← stepKeys it next | break
            if (← inThis v) then
              iterClose n it
              return .bool false
          pure (.bool true)
    | (.x .proxyRevocable) =>
      if !a0.isObj || !a1.isObj then throwErr .type "Cannot create proxy with a non-object as target or handler"
      let p ← alloc { proto := .null, kind := .proxy a0 a1, extensible := true }
      let rv ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x .proxyRevoke)) .undef #[.obj p] }
      defineOwn rv "length" (.data (.num 0) false false true)
      defineOwn rv "name" (.data (.str "") false false true)
      let o ← newObject
      defineOwn o "proxy" (.data (.obj p) true true true)
      defineOwn o "revoke" (.data (.obj rv) true true true)
      pure (.obj o)
    | (.x .proxyRevoke) =>
      if let .obj p := a0 then
        modifyObj p fun o => match o.kind with
          | .proxy t _ => { o with kind := .proxy t .null }
          | _ => o
      pure .undef
    | (.x (.arrayMethod k)) =>
      -- generic over array-likes: ToObject(this), LengthOfArrayLike (§23.1.3)
      let oid ← toObj n thisV
      let o := Value.obj oid
      let lenF := toIntegerOrInf (← toNum n (← getV n o "length"))
      let len := if lenF ≤ 0 then 0 else if lenF > 9007199254740991 then 9007199254740991 else lenF.toUInt64.toNat
      let rel (v : Value) (dflt : Nat) : M Nat := do
        match v with
        | .undef => pure dflt
        | v => pure (relIndex (toIntegerOrInf (← toNum n v)) len)
      let valuesUpTo (m : Nat) : M (Array Value) := do
        let mut out := Array.emptyWithCapacity m
        for i in [0:m] do out := out.push (← getV n o (toString i))
        pure out
      match k with
      | 0 =>
        let to ← rel a0 0
        let from_ ← rel a1 0
        let fin ← rel (argD args 2) len
        let count := min (fin - from_) (len - to)
        if count > 10000000 then throwErr .range "copyWithin: too many elements"
        -- §23.1.3.4 steps 13-14: backwards when the ranges overlap that way
        let back := from_ < to && to < from_ + count
        for j in [0:count] do
          let i := if back then count - 1 - j else j
          let fk := toString (from_ + i)
          let tk := toString (to + i)
          if (← hasProp n oid fk) then putV n o tk (← getV n o fk) true
          else deleteOwn oid tk
        pure o
      | 1 =>
        if !(← isCallable a0) then throwErr .type "reduceRight: the callback is not a function"
        if len > 10000000 then throwErr .range "reduceRight: too many elements"
        let mut acc := a1
        let mut got : Bool := args.size ≥ 2
        for j in [0:len] do
          let i := len - 1 - j
          if (← hasProp n oid (toString i)) then
            let v ← getV n o (toString i)
            if got then acc ← callV n a0 .undef #[acc, v, .num (Float.ofNat i), o]
            else
              acc := v
              got := true
        if !got then throwErr .type "Reduce of empty array with no initial value"
        pure acc
      | 2 =>
        if len > 4294967295 then throwErr .range "Invalid array length"
        newArray (← valuesUpTo len).reverse
      | 3 =>
        match a0 with
        | .undef => pure ()
        | f => if !(← isCallable f) then throwErr .type "The comparison function must be either a function or undefined"
        if len > 4294967295 then throwErr .range "Invalid array length"
        newArray (← mergeSort n a0 (← valuesUpTo len).toList).toArray
      | 4 =>
        let st ← rel a0 0
        let skip ← if args.size == 0 then pure 0 else if args.size == 1 then pure (len - st) else do
          let d := toIntegerOrInf (← toNum n a1)
          pure (if d < 0 then 0 else min d.toUInt64.toNat (len - st))
        let items := args.extract (min 2 args.size) args.size
        let newLen := len + items.size - skip
        if Float.ofNat newLen > 9007199254740991 then throwErr .type "toSpliced: the length is too large"
        if newLen > 4294967295 then throwErr .range "Invalid array length"
        let mut out := Array.emptyWithCapacity newLen
        for i in [0:st] do out := out.push (← getV n o (toString i))
        out := out ++ items
        for i in [st + skip:len] do out := out.push (← getV n o (toString i))
        newArray out
      | _ =>
        let r := toIntegerOrInf (← toNum n a0)
        let i := if r ≥ 0 then r else Float.ofNat len + r
        if i ≥ Float.ofNat len || i < 0 then throwErr .range "Invalid index for Array.prototype.with"
        if len > 4294967295 then throwErr .range "Invalid array length"
        let vs ← valuesUpTo len
        newArray (vs.set! i.toUInt64.toNat a1)
    | (.x .objectHasOwn) =>
      let id ← toObj n a0
      let k ← toKey n a1
      pure (.bool (← ownDesc n id k).isSome)
    | (.x (.groupBy isMap)) =>
      -- GroupBy (§7.3.35): the items of an iterable, by key (property key or SameValueZero)
      if !(← isCallable a1) then throwErr .type "groupBy: the callback is not a function"
      let items ← iterToArray n (← getIterator n a0) #[]
      let mut keys : Array Value := #[]
      let mut groups : Array (Array Value) := #[]
      for i in [0:items.size] do
        let kv ← callV n a1 .undef #[items[i]!, .num (Float.ofNat i)]
        let key ← if isMap then pure (match kv with | .num x => if x == 0 then .num 0 else kv | _ => kv)
          else do pure (keyValue (← toKey n kv))
        match keys.findIdx? (sameValue · key) with
        | some j => groups := groups.modify j (·.push items[i]!)
        | none =>
          keys := keys.push key
          groups := groups.push #[items[i]!]
      if isMap then
        let mut o : Obj := { kind := .coll 0 #[] {} }
        for j in [0:keys.size] do o := collPut keys[j]! (← newArray groups[j]!) o
        let mc ← getV n (.obj r.globalObj) "Map"
        let mp ← getV n mc "prototype"
        pure (.obj (← alloc { o with proto := mp }))
      else
        let res ← alloc { proto := .null }
        for j in [0:keys.size] do
          defineOwn res (← toKey n keys[j]!) (.data (← newArray groups[j]!) true true true)
        pure (.obj res)
    | (.x .stringLocaleCompare) =>
      match ← thisPrim thisV with
      | .undef | .null => throwErr .type "String.prototype.localeCompare called on null or undefined"
      | _ => pure ()
      let s ← toStr n (← thisPrim thisV)
      let t ← toStr n a0
      let a := Str.units s
      let b := Str.units t
      pure (.num (if a == b then 0 else if decide (a < b) then -1 else 1))
    | (.x (.errorStack false)) =>
      -- get Error.prototype.stack (Error Stack Accessor proposal): a string for an object
      -- with [[ErrorData]]. The string lists the call frames, as in SpiderMonkey, JSC and
      -- QuickJS (not the V8 form, which starts with the message). This engine keeps no record
      -- of call sites, so the list is empty: "" (a script that tests `e.stack` sees none).
      match thisV with
      | .obj oid =>
        match (← getObj oid).kind with
        | .error => pure (.str "")
        | _ => pure .undef
      | _ => throwErr .type "Error.prototype.stack getter called on a non-object"
    | (.x (.errorStack true)) =>
      -- set Error.prototype.stack (v): SetterThatIgnoresPrototypeProperties(this,
      -- %Error.prototype%, "stack", v).
      let oid ← match thisV with
        | .obj oid => pure oid
        | _ => throwErr .type "Error.prototype.stack setter called on a non-object"
      match a0 with
      | .str _ => pure ()
      | _ => throwErr .type "Error.prototype.stack setter: the value is not a string"
      if oid == r.errorProtos.getD 0 r.objectProto then
        throwErr .type "Cannot set Error.prototype.stack on Error.prototype"
      match ← ownDesc n oid "stack" with
      | some _ => putV n thisV "stack" a0 true
      | none =>
        let o ← getObj oid
        match o.kind with
        | .proxy t hnd =>
          match ← proxyTrap n hnd "defineProperty" with
          | some f =>
            let d ← newObject
            defineOwn d "value" (.data a0 true true true)
            defineOwn d "writable" (.data (.bool true) true true true)
            defineOwn d "enumerable" (.data (.bool true) true true true)
            defineOwn d "configurable" (.data (.bool true) true true true)
            if !toBool (← callV n f hnd #[t, .str "stack", .obj d]) then
              throwErr .type "'defineProperty' on proxy: trap returned falsish for property 'stack'"
          | none =>
            match t with
            | .obj tid =>
              if !(← getObj tid).extensible then throwErr .type "Cannot define property stack, object is not extensible"
              defineOwn tid "stack" (.data a0 true true true)
            | _ => throwErr .type "Cannot perform 'defineProperty' on a proxy that has been revoked"
        | _ =>
          if !o.extensible then throwErr .type "Cannot define property stack, object is not extensible"
          defineOwn oid "stack" (.data a0 true true true)
      pure .undef
    | (.x .aggregateErrorCtor) =>
      let proto ← match newTarget with
        | some nt => do
          let p ← getV n nt "prototype"
          pure (if p.isObj then p else .obj r.aggregateErrorProto)
        | none => pure (.obj r.aggregateErrorProto)
      let o ← alloc { proto, kind := .error }
      match a1 with
      | .undef => pure ()
      | v => setHidden o "message" (.str (← toStr n v))
      -- InstallErrorCause (§20.5.8.1)
      if let .obj opts := argD args 2 then
        if ← hasProp n opts "cause" then setHidden o "cause" (← getV n (.obj opts) "cause")
      let errs ← iterToArray n (← getIterator n a0) #[]
      setHidden o "errors" (← newArray errs)
      pure (.obj o)
    | (.x .promiseAny) =>
      let res ← newPromise
      let x ← tryCatch (do
          let it ← getIterator n a0
          let items ← iterToArray n it #[]
          let errs ← newArray (Array.replicate items.size .undef)
          let counter ← newObject
          setHidden counter "n" (.num (Float.ofNat items.size + 1))
          for i in [0:items.size] do
            let p ← promiseResolve n items[i]!
            let rs ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn .promiseResolveFn) .undef #[.obj res] }
            let elArgs : Array Value := #[.obj res, errs, .obj counter, .num (Float.ofNat i)]
            let rj ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x .promiseAnyReject)) .undef elArgs }
            performThen n p (.obj rs) (.obj rj) .undef
          let _ ← callNative n (.x .promiseAnyReject) .undef #[.obj res, errs, .obj counter, .num (-1), .undef] none
          pure none)
        (fun a => pure (some a))
      match x with
      | some (.throw e) => rejectPromise n res e
      | some a => throw a
      | none => pure ()
      pure (.obj res)
    | (.x .promiseAnyReject) =>
      -- args: result promise, errors, counter, index, reason
      let idx := match argD args 3 with | .num i => i | _ => -1
      if idx ≥ 0 then putV n a1 (numToString idx) (argD args 4) true
      let c := argD args 2
      let k ← toNum n (← getV n c "n")
      putV n c "n" (.num (k - 1)) true
      if k - 1 == 0 then
        let e ← alloc { proto := .obj r.aggregateErrorProto, kind := .error }
        setHidden e "message" (.str "All promises were rejected")
        setHidden e "errors" (← newArray (← elemsOf n a1))
        match a0 with
        | .obj p => rejectPromise n p (.obj e)
        | _ => pure ()
      pure .undef
    | (.x .dateUTC) =>
      let mut xs : Array Float := #[]
      for i in [0:min 7 args.size] do xs := xs.push (← toNum n args[i]!)
      pure (.num (Date.timeClip (dateOfParts xs)))
    | (.x .dateParse) => pure (.num (Date.parse (← toStr n a0)))
    | (.x (.dateMethod k)) =>
      if k == 32 then
        -- toJSON (§21.4.4.37)
        let o ← toObj n thisV
        let tv ← toPrim n (.obj o) "number"
        if let .num x := tv then
          if !x.isFinite then return .null
        let f ← getV n (.obj o) "toISOString"
        if !(← isCallable f) then throwErr .type "toISOString is not a function"
        return ← callV n f (.obj o) #[]
      if k == 39 then
        -- @@toPrimitive (§21.4.4.45)
        if !thisV.isObj then throwErr .type "Date.prototype[Symbol.toPrimitive] called on a non-object"
        match a0 with
        | .str "string" | .str "default" => return ← tryMethods n thisV ["toString", "valueOf"]
        | .str "number" => return ← tryMethods n thisV ["valueOf", "toString"]
        | _ => throwErr .type "Invalid hint"
      let some t ← thisDate? thisV | throwErr .type "this is not a Date object."
      let oid := match thisV with | .obj i => i | _ => 0
      let p := Date.parts t
      if k < 20 then
        if t.isNaN then return .num t
        return .num (match k with
          | 0 => Float.ofNat p.date | 1 => Float.ofNat p.weekDay | 2 => Float.ofInt p.year
          | 3 => Float.ofNat p.hours | 4 => Float.ofNat p.ms | 5 => Float.ofNat p.minutes
          | 6 => Float.ofNat p.month | 7 => Float.ofNat p.seconds | 8 => 0
          | _ => Float.ofInt (p.year - 1900))
      if k < 30 then
        let set (v : Float) : M Value := do
          modifyObj oid fun o => { o with kind := .prim (.num v) }
          pure (.num v)
        if k == 27 then return ← set (Date.timeClip (← toNum n a0))
        if k == 28 then
          -- setYear (Annex B.2.3.2)
          let y ← toNum n a0
          if y.isNaN then return ← set y
          let yi := toIntegerOrInf y
          let yr := if 0 ≤ yi && yi ≤ 99 then 1900 + yi else y
          let t := if t.isNaN then 0 else t
          let q := Date.parts t
          return ← set (Date.timeClip (Date.makeDate (Date.makeDay yr (Float.ofNat q.month) (Float.ofNat q.date))
            (Float.ofInt ((Date.toInt t).emod Date.msPerDay))))
        -- the arguments replace parts from `first` on, at most `most` of them (§21.4.4.20 to §21.4.4.28)
        let (first, most) := match k with
          | 20 => (2, 1) | 21 => (0, 3) | 22 => (3, 4) | 23 => (6, 1) | 24 => (4, 3) | 25 => (1, 2) | _ => (5, 2)
        let mut given : Array Float := #[]
        for i in [0:min most (max 1 args.size)] do given := given.push (← toNum n (argD args i))
        if t.isNaN && k != 21 then return .num t
        let q := Date.parts (if t.isNaN then 0 else t)
        let mut cs : Array Float := #[Float.ofInt q.year, Float.ofNat q.month, Float.ofNat q.date, Float.ofNat q.hours,
          Float.ofNat q.minutes, Float.ofNat q.seconds, Float.ofNat q.ms]
        for i in [0:given.size] do cs := cs.set! (first + i) given[i]!
        return ← set (Date.timeClip (Date.makeDate (Date.makeDay cs[0]! cs[1]! cs[2]!)
          (Date.makeTime cs[3]! cs[4]! cs[5]! cs[6]!)))
      if t.isNaN then
        if k == 31 then throwErr .range "Invalid time value"
        return .str "Invalid Date"
      pure (.str (match k with
        | 30 | 33 => Date.dateString t
        | 31 => Date.isoString t
        | 35 | 37 => Date.timeString t
        | 38 => Date.utcString t
        | _ => Date.toStr t))
    | (.x .namedGetterSet) =>
      -- the host's function for the named properties of the global object (`namedGlobal`)
      defineOwn r.globalObj namedGetterKey (.data a0 false false false)
      pure .undef
    | (.x .symbolFor) | (.x .symbolKeyFor) =>
      let reg ← match (← getObj r.globalObj).props.get? symbolRegistryKey with
        | some (.data (.obj id) ..) => pure id
        | _ => do
          let id ← alloc { proto := .null }
          setHidden r.globalObj symbolRegistryKey (.obj id)
          pure id
      if id == (.x .symbolFor) then
        let key ← toStr n a0
        match (← getObj reg).props.get? (strKey key) with
        | some (.data v ..) => pure v
        | _ =>
          let sid ← modifyGet fun h => (h.syms.size, { h with syms := h.syms.push key })
          defineOwn reg (strKey key) (.data (.sym sid) true true true)
          pure (.sym sid)
      else
        match a0 with
        | .sym sid =>
          let o ← getObj reg
          pure (match o.keys.find? (fun k => match o.props.get? k with
              | some (.data (.sym j) ..) => j == sid | _ => false) with
            | some k => .str (keyStr k)
            | none => .undef)
        | _ => throwErr .type "Symbol.keyFor: the argument is not a symbol"
    | (.x .stringRaw) =>
      let cooked ← toObj n a0
      let raw ← toObj n (← getV n (.obj cooked) "raw")
      let len := toIntegerOrInf (← toNum n (← getV n (.obj raw) "length"))
      let count := if len ≤ 0 then 0 else len.toUInt64.toNat
      charge (count / 8)
      let mut out := ""
      for i in [0:count] do
        out := Str.jsAppend out (← toStr n (← getV n (.obj raw) (toString i)))
        if i + 1 < count && i + 1 < args.size then
          out := Str.jsAppend out (← toStr n (argD args (i + 1)))
      pure (.str out)
    | (.x .weakRefCtor) =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Constructor WeakRef requires 'new'"
      if !a0.isObj then throwErr .type "WeakRef: the target must be an object"
      let pp ← getV n nt "prototype"
      let proto ← if pp.isObj then pure pp else getV n (← getV n (.obj r.globalObj) "WeakRef") "prototype"
      let o ← alloc { proto }
      setHidden o weakRefTargetKey a0
      pure (.obj o)
    | (.x .weakRefDeref) =>
      match thisV with
      | .obj oid =>
        match (← getObj oid).props.get? weakRefTargetKey with
        | some (.data v ..) => pure v
        | _ => throwErr .type "WeakRef.prototype.deref called on an incompatible receiver"
      | _ => throwErr .type "WeakRef.prototype.deref called on an incompatible receiver"
    | (.x .finRegCtor) =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Constructor FinalizationRegistry requires 'new'"
      if !(← isCallable a0) then throwErr .type "FinalizationRegistry: the cleanup callback is not a function"
      let pp ← getV n nt "prototype"
      let proto ← if pp.isObj then pure pp else getV n (← getV n (.obj r.globalObj) "FinalizationRegistry") "prototype"
      let o ← alloc { proto }
      setHidden o finRegCallbackKey a0
      setHidden o finRegTokensKey (← newArray #[])
      pure (.obj o)
    | (.x (.finRegMethod k)) =>
      let (oid, tokens) ← match thisV with
        | .obj oid =>
          match (← getObj oid).props.get? finRegTokensKey with
          | some (.data (.obj t) ..) => pure (oid, t)
          | _ => throwErr .type "FinalizationRegistry method called on an incompatible receiver"
        | _ => throwErr .type "FinalizationRegistry method called on an incompatible receiver"
      let _ := oid
      let held ← match (← getObj tokens).kind with | .array es => pure es | _ => pure #[]
      if k == 0 then
        -- register(target, heldValue, unregisterToken)
        if !a0.isObj then throwErr .type "FinalizationRegistry.register: the target must be an object"
        if sameValue a0 a1 then throwErr .type "FinalizationRegistry.register: the target and the held value are the same"
        let tok := argD args 2
        match tok with
        | .undef => pure ()
        | .obj _ => modifyObj tokens fun o => { o with kind := .array (held.push tok) }
        | _ => throwErr .type "FinalizationRegistry.register: the unregister token must be an object"
        pure .undef
      else
        -- unregister(unregisterToken): were there cells with the token
        if !a0.isObj then throwErr .type "FinalizationRegistry.unregister: the token must be an object"
        let rest := held.filter fun v => !sameValue v a0
        modifyObj tokens fun o => { o with kind := .array rest }
        pure (.bool (rest.size < held.size))
    | (.x (.mapUpsert computed weak)) =>
      let ck : Nat ← match thisV with
        | .obj c => match (← getObj c).kind with
          | .coll k _ _ => pure k
          | _ => throwErr .type "method called on incompatible receiver"
        | _ => throwErr .type "method called on incompatible receiver"
      -- Map's method needs a Map (kind 0), WeakMap's a WeakMap (kind 2)
      if ck != (if weak then 2 else 0) then throwErr .type "method called on incompatible receiver"
      if computed && !(← isCallable a1) then throwErr .type "getOrInsertComputed: the callback is not a function"
      if weak && !a0.isObj then throwErr .type "Invalid value used as weak collection key"
      if toBool (← callNative n .mapHas thisV #[a0] none) then callNative n .mapGet thisV #[a0] none
      else
        let key := match a0 with | .num x => if x == 0 then Value.num 0 else a0 | _ => a0
        let v ← if computed then callV n a1 .undef #[key] else pure a1
        let _ ← callNative n .mapSet thisV #[a0, v] none
        pure v
    | (.x .streams) =>
      -- `n.streams(op, ...)` for the page's stream classes: the queue-with-sizes of a
      -- controller and the fill plan of a BYOB read are `WHATWG.Streams`
      let queueOf (v : Value) : M (Nat × L4Factoidal.WHATWG.Streams.SizedQueue Value) := do
        match v with
        | .obj id =>
          match (← getObj id).kind with
          | .queue q => pure (id, q)
          | _ => throwErr .type "streams: not a queue"
        | _ => throwErr .type "streams: not a queue"
      let natArg (i : Nat) : M Nat := do
        match argD args i with
        | .num x => pure (if x.isFinite && x > 0 then x.toUInt64.toNat else 0)
        | _ => pure 0
      match a0 with
      | .num op =>
        match op.toUInt64.toNat with
        | 0 => pure (.obj (← alloc { proto := .null, kind := .queue {} }))
        | 1 =>
          let (id, q) ← queueOf a1
          let size ← match argD args 3 with
            | .num s => pure s
            | _ => throwErr .range "The chunk size is not a finite, non-negative number"
          match q.enqueue (argD args 2) size with
          | some q' => modifyObj id (fun o => { o with kind := .queue q' }); pure .undef
          | none => throwErr .range "The chunk size is not a finite, non-negative number"
        | 2 =>
          let (id, q) ← queueOf a1
          -- the queue leaves the object first, so that `dequeue` changes its array in place
          modifyObj id (fun o => { o with kind := .ordinary })
          match q.dequeue with
          | some (v, q') => modifyObj id (fun o => { o with kind := .queue q' }); pure v
          | none => modifyObj id (fun o => { o with kind := .queue q }); pure .undef
        | 3 => let (_, q) ← queueOf a1; pure (q.peek.getD .undef)
        | 4 => let (id, _) ← queueOf a1; modifyObj id (fun o => { o with kind := .queue .reset }); pure .undef
        | 5 => let (_, q) ← queueOf a1; pure (.num q.total)
        | 6 => let (_, q) ← queueOf a1; pure (.num q.count.toFloat)
        | 7 =>
          match a1 with
          | .num h => if L4Factoidal.WHATWG.Streams.validHighWaterMark h then pure a1
                      else throwErr .range "The high water mark is negative or not a number"
          | _ => throwErr .range "The high water mark is negative or not a number"
        | 8 =>
          let p := L4Factoidal.WHATWG.Streams.fillPlan (← natArg 1) (← natArg 2) (← natArg 3) (← natArg 4) (← natArg 5)
          pure (.num (if p.ready then -(p.toCopy.toFloat) - 1 else p.toCopy.toFloat))
        | _ => throwErr .type "streams: unknown operation"
      | _ => throwErr .type "streams: unknown operation"
    | (.x (.protoAccessor false)) =>
      -- get Object.prototype.__proto__ (B.2.2.1.1)
      let id ← toObj n thisV
      callNative n .objectGetPrototypeOf .undef #[.obj id] none
    | (.x (.protoAccessor true)) =>
      -- set Object.prototype.__proto__ (B.2.2.1.2)
      match thisV with
      | .undef | .null => throwErr .type "Object.prototype.__proto__ called on null or undefined"
      | .obj id =>
        match a0 with
        | .obj _ | .null =>
          if toBool (← callNative n (.reflect 2) .undef #[.obj id, a0] none) then pure .undef
          else throwErr .type "Object.prototype.__proto__: the prototype of this object cannot be changed"
        | _ => pure .undef
      | _ => pure .undef
    | (.x .promiseWithResolvers) =>
      -- §27.2.4.8 Promise.withResolvers: NewPromiseCapability(this) (§27.2.1.5)
      if !(← isConstructor thisV) then throwErr .type "Promise.withResolvers: this is not a constructor"
      let cap ← alloc { proto := .null }
      let exec ← alloc { proto := .obj r.functionProto,
        kind := .bound (← nativeFn (.x .capabilityExecutor)) .undef #[.obj cap] }
      let p ← construct n thisV #[.obj exec] thisV
      let field (k : String) : M Value := do
        match (← getObj cap).getOwn k with
        | some (.data v ..) => pure v
        | _ => pure .undef
      let res ← field "resolve"
      let rej ← field "reject"
      if !(← isCallable res) || !(← isCallable rej) then
        throwErr .type "Promise.withResolvers: the constructor did not give callable resolving functions"
      let o ← newObject
      defineOwn o "promise" (.data p true true true)
      defineOwn o "resolve" (.data res true true true)
      defineOwn o "reject" (.data rej true true true)
      pure (.obj o)
    | (.x .capabilityExecutor) =>
      -- GetCapabilitiesExecutor (§27.2.1.5 step 4): the record, then resolve and reject
      match a0 with
      | .obj cap =>
        let o ← getObj cap
        let isSet (k : String) : Bool := match o.getOwn k with
          | some (.data .undef ..) | none => false
          | _ => true
        if isSet "resolve" || isSet "reject" then throwErr .type "Promise executor has already been invoked"
        defineOwn cap "resolve" (.data a1 true true true)
        defineOwn cap "reject" (.data (argD args 2) true true true)
        pure .undef
      | _ => pure .undef
    | (.x (.dynFunction k)) =>
      -- CreateDynamicFunction (§20.2.1.1.1) for the generator, async and async generator kinds
      let strs ← args.toList.mapM (toStr n)
      let (ps, body) := match strs.reverse with
        | [] => ([], "")
        | b :: rest => (rest.reverse, b)
      let kw := match k with | 1 => "function*" | 2 => "async function" | _ => "async function*"
      match (parseScript (dynFunctionSource kw ps body) false).map Resolve.script with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok { body := [.expr e], .. } =>
        evalExpr n { env := 0, thisV := .obj r.globalObj, strict := false } e
      | .ok _ => throwErr .syntax "invalid function body"
    | (.x .urlPattern) =>
      -- `n.urlPattern(op, ...)` for the page's URLPattern class: the Standard's algorithms are
      -- `WHATWG.URLPattern.create` and `exec`; this converts the arguments and builds the answer.
      let names := ["protocol", "username", "password", "hostname", "port", "pathname", "search", "hash"]
      -- a URLPatternInput (WebIDL): an object is a URLPatternInit, its members read in
      -- lexicographical order; anything else is a USVString
      let toInput (v : Value) : M L4Factoidal.WHATWG.URLPattern.Input := do
        match v with
        | .obj _ =>
          let member (k : String) : M (Option String) := do
            match ← getV n v k with
            | .undef => pure none
            | x => pure (some (Str.toHost (← toStr n x)))
          let baseURL ← member "baseURL"
          let hash ← member "hash"
          let hostname ← member "hostname"
          let password ← member "password"
          let pathname ← member "pathname"
          let port ← member "port"
          let protocol ← member "protocol"
          let search ← member "search"
          let username ← member "username"
          pure (.init { protocol, username, password, hostname, port, pathname, search, hash, baseURL })
        | .undef | .null => pure (.init {})
        | x => pure (.str (Str.toHost (← toStr n x)))
      let optStr (v : Value) : M (Option String) := do
        match v with
        | .undef => pure none
        | x => pure (some (Str.toHost (← toStr n x)))
      let a2 := argD args 2
      let a3 := argD args 3
      if (match a0 with | .num x => x == 0 | _ => false) then
        let input ← toInput a1
        let base ← optStr a2
        match L4Factoidal.WHATWG.URLPattern.create input base (toBool a3) with
        | .error msg => throwErr .type msg
        | .ok p =>
          let record ← newObject
          let comps := [p.protocol, p.username, p.password, p.hostname, p.port, p.pathname, p.search, p.hash]
          for (name, c) in names.zip comps do
            defineOwn record name (.data (.str (Str.ofHost c.pattern)) false true false)
            let re ← alloc { proto := .obj r.regexpProto, kind := .regexp c.regex "" "" }
            setHidden record (privKey ("re:" ++ name)) (.obj re)
            setHidden record (privKey ("names:" ++ name)) (← newArray (c.names.map fun s => Value.str (Str.ofHost s)))
          defineOwn record "hasRegExpGroups" (.data (.bool p.hasRegexpGroups) false true false)
          pure (.obj record)
      else
        let o ← match a1 with
          | .obj id => getObj id
          | _ => throwErr .type "URLPattern: not a pattern"
        let comp (name : String) : M L4Factoidal.WHATWG.URLPattern.Component := do
          match o.props.get? (privKey ("re:" ++ name)), o.props.get? (privKey ("names:" ++ name)) with
          | some (.data (.obj rid) ..), some (.data (.obj nid) ..) =>
            match (← getObj rid).kind, (← getObj nid).kind with
            | .regexp re _ _, .array ns =>
              pure { pattern := "", regex := re, names := ns.map fun v => match v with | .str s => Str.toHost s | _ => "" }
            | _, _ => throwErr .type "URLPattern: not a pattern"
          | _, _ => throwErr .type "URLPattern: not a pattern"
        let pat : L4Factoidal.WHATWG.URLPattern.Pattern :=
          { protocol := ← comp "protocol", username := ← comp "username", password := ← comp "password",
            hostname := ← comp "hostname", port := ← comp "port", pathname := ← comp "pathname",
            search := ← comp "search", hash := ← comp "hash" }
        let input ← toInput a2
        let base ← optStr a3
        match L4Factoidal.WHATWG.URLPattern.exec pat input base with
        | .error msg => throwErr .type msg
        | .ok none => pure .null
        | .ok (some res) =>
          let out ← newObject
          let inputs ← newArray (match a3 with | .undef => #[a2] | b => #[a2, b])
          defineOwn out "inputs" (.data inputs true true true)
          for (name, (v, groups)) in names.zip res.components.toList do
            let c ← newObject
            defineOwn c "input" (.data (.str (Str.ofHost v)) true true true)
            let g ← newObject
            for (k, gv) in groups do
              defineOwn g (strKey (Str.ofHost k))
                (.data (match gv with | some s => Value.str (Str.ofHost s) | none => .undef) true true true)
            defineOwn c "groups" (.data (.obj g) true true true)
            defineOwn out name (.data (.obj c) true true true)
          pure (.obj out)
    | (.x .dynImport) =>
      let pid ← newPromise
      let x ← tryCatch (do let _ ← toStr n a0; pure none) (fun a => pure (some a))
      match x with
      | some (.throw e) => rejectPromise n pid e
      | some a => throw a
      | none => rejectPromise n pid (← mkError .type "import() is not supported in this script")
      pure (.obj pid)
    | (.x (.promiseThenableFn reject)) =>
      -- bound arguments: the promise and the pair's [[AlreadyResolved]] record
      match a0, a1 with
      | .obj pid, .obj record =>
        if !(← getObj record).props.contains "done" then
          setHidden record "done" (.bool true)
          if reject then rejectPromise n pid (argD args 2) else resolvePromise n pid (argD args 2)
        pure .undef
      | _, _ => pure .undef
    | (.x (.forAwait 0)) =>
      -- GetIterator(obj, async) (§7.4.3): the @@asyncIterator method's iterator, or an
      -- async-from-sync iterator over the @@iterator method's (§27.1.6.1).
      let m ← match a0 with
        | .undef | .null => throwErr .type "object is not async iterable"
        | _ => getV n a0 (symKey 1)
      match m with
      | .undef | .null =>
        let sync ← getIterator n a0
        let nextM ← getV n sync "next"
        let w ← alloc { proto := (← ownValue r.globalObj asyncFromSyncProtoKey) }
        setHidden w syncIterKey sync
        setHidden w syncNextKey nextM
        pure (.obj w)
      | _ =>
        if !(← isCallable m) then throwErr .type "Symbol.asyncIterator is not a function"
        let it ← callV n m a0 #[]
        if !it.isObj then throwErr .type "Result of the Symbol.asyncIterator method is not an object"
        pure it
    | (.x (.forAwait 1)) =>
      if !(← isCallable a0) then throwErr .type "iterator method is not a function"
      callV n a0 a1 #[]
    | (.x (.forAwait _)) =>
      if !a0.isObj then throwErr .type "Iterator result is not an object"
      pure .undef
    | (.x (.asyncFromSync 3)) => iterResult n a0 false
    | (.x (.asyncFromSync 4)) => iterResult n a0 true
    | (.x (.asyncFromSync 5)) =>
      -- the value was a rejected promise: IteratorClose(sync, ThrowCompletion(reason)); what
      -- `return` throws is dropped (bound argument: the sync iterator)
      let _ ← tryCatch (iterClose n a0) (fun a => match a with | .halt w => throw (.halt w) | _ => pure ())
      throw (.throw a1)
    | (.x (.asyncFromSync k)) =>
      -- %AsyncFromSyncIteratorPrototype%.next, .return, .throw (§27.1.6.2): every abrupt
      -- completion rejects the promise that is returned (IfAbruptRejectPromise)
      let pid ← newPromise
      let slots : Option (Value × Value) ← match thisV with
        | .obj w =>
          let o ← getObj w
          match o.props.get? syncIterKey, o.props.get? syncNextKey with
          | some (.data sync ..), some (.data nextM ..) => pure (some (sync, nextM))
          | _, _ => pure none
        | _ => pure none
      match slots with
      | none => rejectPromise n pid (← mkError .type "not an async-from-sync iterator")
      | some (sync, nextM) =>
        let given : Array Value := if args.size > 0 then #[a0] else #[]
        let x ← tryCatch (do
            let res : Option Value ← match k with
              | 0 => do pure (some (← callV n nextM sync given))
              | 1 => do
                let m ← getV n sync "return"
                match m with
                | .undef | .null => resolvePromise n pid (← iterResult n a0 true); pure none
                | _ =>
                  if !(← isCallable m) then throwErr .type "return is not a function"
                  pure (some (← callV n m sync given))
              | _ => do
                let m ← getV n sync "throw"
                match m with
                | .undef | .null =>
                  -- no `throw`: the protocol is broken; close the sync iterator, then a TypeError
                  iterClose n sync
                  throwErr .type "The iterator does not provide a 'throw' method"
                | _ =>
                  if !(← isCallable m) then throwErr .type "throw is not a function"
                  pure (some (← callV n m sync given))
            match res with
            | none => pure ()
            | some res =>
              -- AsyncFromSyncIteratorContinuation (§27.1.6.4); closeOnRejection is false for `return`
              if !res.isObj then throwErr .type "Iterator result is not an object"
              let done := toBool (← getV n res "done")
              let value ← getV n res "value"
              let close := !done && k != 1
              let vw ← tryCatch (do pure (Except.ok (← promiseResolve n value))) (fun a => pure (Except.error a))
              let vp ← match vw with
                | .ok vp => pure vp
                | .error (.throw e) =>
                  if close then
                    let _ ← tryCatch (iterClose n sync) (fun a => match a with | .halt w => throw (.halt w) | _ => pure ())
                  throw (.throw e)
                | .error a => throw a
              let onF ← nativeFn (.x (.asyncFromSync (if done then 4 else 3)))
              let onR ← if close then do
                  let f ← nativeFn (.x (.asyncFromSync 5))
                  pure (Value.obj (← alloc { proto := .obj r.functionProto, kind := .bound f .undef #[sync] }))
                else pure Value.undef
              performThen n vp onF onR (.obj pid)
            pure none)
          (fun a => pure (some a))
        match x with
        | some (.throw e) => rejectPromise n pid e
        | some a => throw a
        | none => pure ()
      pure (.obj pid)
    | (.x .stringIsWellFormed) | (.x .stringToWellFormed) =>
      let tp ← thisPrim thisV
      match tp with
      | .undef | .null => throwErr .type "String.prototype method called on null or undefined"
      | _ => pure ()
      let s ← toStr n tp
      if id == (.x .stringIsWellFormed) then pure (.bool (Str.isWellFormed s)) else pure (.str (Str.toWellFormed s))
    | _ => throwErr .type "not a function"
termination_by structural n _ _ _ _ => n

end

/-! ## The realm: global object and intrinsics (§9.3, §19) -/

def ctorWith (name : String) (id : Native) (len : Nat) (proto : Nat) : M Value := do
  let c ← mkNative id name len
  if let .obj cid := c then
    defineOwn cid "prototype" (.data (.obj proto) false false false)
  setHidden proto "constructor" c
  pure c

/-- An accessor property with a getter only, not enumerable (as built-in accessors are). -/
def getter (target : Nat) (name : String) (id : Native) : M Unit := do
  defineOwn target name (.acc (← mkNative id ("get " ++ name) 0) .undef false true)

/-- The methods of %TypedArray%.prototype that answer typed arrays or need the element
type (`Native.typedMethod`): name, number, length. -/
def typedMethodNames : List (String × Nat × Nat) :=
  [("copyWithin", 0, 2), ("reverse", 1, 0), ("slice", 2, 2), ("sort", 3, 1), ("at", 4, 1),
   ("lastIndexOf", 5, 1), ("filter", 6, 1), ("map", 7, 1), ("toReversed", 8, 0), ("toSorted", 9, 1),
   ("with", 10, 2), ("findLast", 11, 1), ("findLastIndex", 12, 1), ("reduceRight", 13, 1)]

/-- The functions of Atomics (`Native.atomics`): name, number, length. -/
def atomicsNames : List (String × Nat × Nat) :=
  [("add", 0, 3), ("and", 1, 3), ("compareExchange", 2, 4), ("exchange", 3, 3), ("isLockFree", 4, 1),
   ("load", 5, 2), ("or", 6, 3), ("store", 7, 3), ("sub", 8, 3), ("xor", 9, 3), ("notify", 10, 3)]

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
    -- Object.prototype.__proto__ (B.2.2.1); Object.prototype is an immutable prototype exotic
    -- object (§20.1.3)
    defineOwn objectProto "__proto__" (.acc (← mkNative (.x (.protoAccessor false)) "get __proto__" 0)
      (← mkNative (.x (.protoAccessor true)) "set __proto__" 1) false true)
    setHidden objectProto immutableProtoKey (.bool true)
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
  method objectProto "__defineGetter__" .objectProtoDefineGetter 2
  method objectProto "__defineSetter__" .objectProtoDefineSetter 2
  method objectProto "__lookupGetter__" .objectProtoLookupGetter 1
  method objectProto "__lookupSetter__" .objectProtoLookupSetter 1
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
    defineOwn nc "MAX_SAFE_INTEGER" (.data (.num maxSafeF) false false false)
    defineOwn nc "MIN_SAFE_INTEGER" (.data (.num (-maxSafeF)) false false false)
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
  method numberProto "toExponential" (.x .numberToExponential) 1
  method numberProto "toPrecision" (.x .numberToPrecision) 1
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
  -- Error.prototype.stack (Error Stack Accessor proposal): an accessor, so an error costs
  -- nothing for it until a script reads it.
  defineOwn errorProto "stack" (.acc (← mkNative (.x (.errorStack false)) "get stack" 0)
    (← mkNative (.x (.errorStack true)) "set stack" 1) false true)
  -- AggregateError (§20.5.7)
  let aggProto ← alloc { proto := .obj errorProto }
  modify fun h => { h with realm := { h.realm with aggregateErrorProto := aggProto } }
  let aggC ← ctorWith "AggregateError" (.x .aggregateErrorCtor) 2 aggProto
  if let .obj cid := aggC then
    if let .obj e0 ← ownValue g "Error" then modifyObj cid fun o => { o with proto := .obj e0 }
  setHidden g "AggregateError" aggC
  setHidden aggProto "name" (.str "AggregateError")
  setHidden aggProto "message" (.str "")
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
  -- Map, Set, WeakMap, WeakSet
  for (k, nm) in [(0, "Map"), (1, "Set"), (2, "WeakMap"), (3, "WeakSet")] do
    let p ← mk
    setHidden g nm (← ctorWith nm (.mapCtor k) 0 p)
    defineOwn p (symKey symToStringTag) (.data (.str nm) false false true)
    let isMap := k == 0 || k == 2
    if isMap then
      method p "get" .mapGet 1
      method p "set" .mapSet 2
      method p "getOrInsert" (.x (.mapUpsert false (k == 2))) 2
      method p "getOrInsertComputed" (.x (.mapUpsert true (k == 2))) 2
    else method p "add" .setAdd 1
    if k == 1 then
      for (nm, j) in [("union", 0), ("intersection", 1), ("difference", 2), ("symmetricDifference", 3),
          ("isSubsetOf", 4), ("isSupersetOf", 5), ("isDisjointFrom", 6)] do
        method p nm ((.x (.setMethod j))) 1
    method p "has" .mapHas 1
    method p "delete" .mapDelete 1
    if k < 2 then
      method p "clear" .mapClear 0
      method p "forEach" .mapForEach 1
      defineOwn p "size" (.acc (← mkNative .mapSize "get size" 0) .undef false true)
      let entries ← mkNative (.mapIter 4) "entries" 0
      let values ← mkNative (.mapIter 6) "values" 0
      setHidden p "entries" entries
      setHidden p "values" values
      if isMap then
        method p "keys" (.mapIter 5) 0
        setHidden p (symKey symIterator) entries
      else
        setHidden p "keys" values
        setHidden p (symKey symIterator) values
  -- Reflect
  let reflect ← mk
  setHidden g "Reflect" (.obj reflect)
  for (nm, op, l) in [("ownKeys", 0, 1), ("getPrototypeOf", 1, 1), ("setPrototypeOf", 2, 2),
      ("has", 3, 2), ("get", 4, 2), ("set", 5, 3), ("defineProperty", 6, 3),
      ("deleteProperty", 7, 2), ("apply", 8, 3), ("construct", 9, 2),
      ("getOwnPropertyDescriptor", 10, 2), ("isExtensible", 11, 1), ("preventExtensions", 12, 1)] do
    method reflect nm (.reflect op) l
  if let .obj oc := objectC then
    method oc "defineProperties" .objectDefineProperties 2
    method oc "seal" .objectSeal 1
    method oc "isSealed" .objectIsSealed 1
    method oc "getOwnPropertyDescriptors" .objectGetOwnPropertyDescriptors 1
    method oc "fromEntries" .objectFromEntries 1
    method oc "hasOwn" (.x .objectHasOwn) 2
    method oc "groupBy" ((.x (.groupBy false))) 2
  for (nm, f, l) in [("flat", Native.arrayFlat, 0), ("flatMap", .arrayFlatMap, 1), ("at", .arrayAt, 1),
      ("findLast", .arrayFindLast, 1), ("findLastIndex", .arrayFindLastIndex, 1)] do
    method arrayProto nm f l
  for (nm, k, l) in [("copyWithin", 0, 2), ("reduceRight", 1, 1), ("toReversed", 2, 0), ("toSorted", 3, 1),
      ("toSpliced", 4, 2), ("with", 5, 2)] do
    method arrayProto nm ((.x (.arrayMethod k))) l
  for (nm, f, l) in [("padStart", Native.stringPadStart, 1), ("padEnd", .stringPadEnd, 1),
      ("at", .stringAt, 1), ("codePointAt", .stringCodePointAt, 1), ("trimStart", .stringTrimStart, 0),
      ("trimEnd", .stringTrimEnd, 0), ("replace", .stringReplace, 2), ("replaceAll", .stringReplaceAll, 2)] do
    method stringProto nm f l
  if let .obj sc := stringC then
    method sc "fromCodePoint" .stringFromCodePoint 1
    method sc "raw" (.x .stringRaw) 1
  method stringProto "localeCompare" (.x .stringLocaleCompare) 1
  -- Annex B.2.2.15, B.2.2.16: trimLeft and trimRight are trimStart and trimEnd
  for (alias, nm) in [("trimLeft", "trimStart"), ("trimRight", "trimEnd"), ("toLocaleUpperCase", "toUpperCase"),
      ("toLocaleLowerCase", "toLowerCase")] do
    if let some (.data f ..) := (← getObj stringProto).getOwn nm then setHidden stringProto alias f
  match ← getV 100 (.obj g) "Map" with
  | .obj mc => method mc "groupBy" ((.x (.groupBy true))) 2
  | _ => pure ()
  if let .obj nc := numberC then
    method nc "isFinite" .numberIsFinite 1
    method nc "isNaN" .numberIsNaN 1
    method nc "isSafeInteger" .numberIsSafeInteger 1
    setHidden nc "parseFloat" (← ownValue g "parseFloat")
    setHidden nc "parseInt" (← ownValue g "parseInt")
  for (nm, op) in [("cbrt", 0), ("log2", 1), ("log10", 2), ("sinh", 3), ("cosh", 4), ("tanh", 5),
      ("asin", 6), ("acos", 7), ("asinh", 8), ("acosh", 9), ("atanh", 10), ("expm1", 11),
      ("log1p", 12), ("fround", 13), ("f16round", 14)] do
    method math nm (.math1 op) 1
  method math "hypot" .mathHypot 2
  method math "imul" .mathImul 2
  method math "clz32" .mathClz32 1
  -- JSON, console
  let json ← mk
  setHidden g "JSON" (.obj json)
  method json "stringify" .jsonStringify 3
  method json "parse" .jsonParse 2
  let console ← mk
  setHidden g "console" (.obj console)
  method console "log" .print 0
  -- eval, Symbol, iterators, Date.now
  for (nm, k) in [("encodeURIComponent", 0), ("decodeURIComponent", 1), ("escape", 2), ("unescape", 3),
      ("encodeURI", 4), ("decodeURI", 5)] do
    setHidden g nm (← mkNative (.uriFn k) nm 1)
  let ev ← mkNative .eval "eval" 1
  setHidden g "eval" ev
  if let .obj e := ev then modify fun h => { h with realm := { h.realm with evalFn := e } }
  let symC ← ctorWith "Symbol" .symbolCtor 0 symbolProto
  setHidden g "Symbol" symC
  if let .obj sc := symC then
    for i in [0:wellKnown.size] do
      defineOwn sc (wellKnown[i]!) (.data (.sym i) false false false)
    method sc "for" (.x .symbolFor) 1
    method sc "keyFor" (.x .symbolKeyFor) 1
  -- WeakRef (§26.1) and FinalizationRegistry (§26.2)
  let weakRefProto ← mk
  setHidden g "WeakRef" (← ctorWith "WeakRef" (.x .weakRefCtor) 1 weakRefProto)
  method weakRefProto "deref" (.x .weakRefDeref) 0
  defineOwn weakRefProto (symKey symToStringTag) (.data (.str "WeakRef") false false true)
  let finRegProto ← mk
  setHidden g "FinalizationRegistry" (← ctorWith "FinalizationRegistry" (.x .finRegCtor) 1 finRegProto)
  method finRegProto "register" (.x (.finRegMethod 0)) 2
  method finRegProto "unregister" (.x (.finRegMethod 1)) 1
  defineOwn finRegProto (symKey symToStringTag) (.data (.str "FinalizationRegistry") false false true)
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
  let asyncIterProto ← mk
  setHidden asyncIterProto (symKey 1) (← mkNative .iterSelf "[Symbol.asyncIterator]" 0)
  -- %AsyncFromSyncIteratorPrototype% (§27.1.6.2) and the functions the statements of
  -- `for await` call (`forAwaitFn`): hidden properties of the global object
  let asyncFromSyncProto ← alloc { proto := .obj asyncIterProto }
  method asyncFromSyncProto "next" (.x (.asyncFromSync 0)) 1
  method asyncFromSyncProto "return" (.x (.asyncFromSync 1)) 1
  method asyncFromSyncProto "throw" (.x (.asyncFromSync 2)) 1
  setHidden g asyncFromSyncProtoKey (.obj asyncFromSyncProto)
  for k in [0:3] do
    setHidden g (forAwaitFn k) (← mkNative (.x (.forAwait k)) "" 1)
  setHidden g dynImportName (← mkNative (.x .dynImport) "" 1)
  let asyncGenProto ← alloc { proto := .obj asyncIterProto }
  modify fun h => { h with realm := { h.realm with asyncGenProto := asyncGenProto } }
  method asyncGenProto "next" .agenNext 1
  method asyncGenProto "return" .agenReturn 1
  method asyncGenProto "throw" .agenThrow 1
  defineOwn asyncGenProto (symKey symToStringTag) (.data (.str "AsyncGenerator") false false true)
  -- %GeneratorFunction%, %AsyncGeneratorFunction%, %AsyncFunction% and their prototypes
  -- (§27.3, §27.4, §27.7): not globals; reached as Object.getPrototypeOf(function* () {}) and
  -- its constructor
  let fnProtoId := (← realm).functionProto
  let genFnProto ← alloc { proto := .obj fnProtoId }
  let asyncGenFnProto ← alloc { proto := .obj fnProtoId }
  let asyncFnProto ← alloc { proto := .obj fnProtoId }
  let fnCtorV ← ownValue g "Function"
  for (fp, inst, tag, k) in [(genFnProto, genProto, "GeneratorFunction", 1),
      (asyncGenFnProto, asyncGenProto, "AsyncGeneratorFunction", 3), (asyncFnProto, 0, "AsyncFunction", 2)] do
    if inst != 0 then
      defineOwn fp "prototype" (.data (.obj inst) false false true)
      defineOwn inst "constructor" (.data (.obj fp) false false true)
    defineOwn fp (symKey symToStringTag) (.data (.str tag) false false true)
    let c ← mkNative (.x (.dynFunction k)) tag 1
    if let .obj cid := c then
      modifyObj cid (fun o => { o with proto := match fnCtorV with | .obj f => .obj f | _ => .obj fnProtoId })
      defineOwn cid "prototype" (.data (.obj fp) false false false)
    defineOwn fp "constructor" (.data c false false true)
  modify fun h => { h with realm := { h.realm with genFnProto := genFnProto, asyncGenFnProto := asyncGenFnProto, asyncFnProto := asyncFnProto } }
  let promiseProto ← mk
  let promiseC ← ctorWith "Promise" .promiseCtor 1 promiseProto
  setHidden g "Promise" promiseC
  if let .obj pc := promiseC then
    modify fun h => { h with realm := { h.realm with promiseProto := promiseProto, promiseCtor := pc } }
    method pc "resolve" .promiseResolveStatic 1
    method pc "reject" .promiseRejectStatic 1
    method pc "all" .promiseAll 1
    method pc "race" ((.x (.promiseCombinator 0))) 1
    method pc "allSettled" ((.x (.promiseCombinator 1))) 1
    method pc "any" (.x .promiseAny) 1
    method pc "withResolvers" (.x .promiseWithResolvers) 0
  method promiseProto "then" .promiseThen 2
  method promiseProto "catch" .promiseCatch 1
  method promiseProto "finally" .promiseFinally 1
  defineOwn promiseProto (symKey symToStringTag) (.data (.str "Promise") false false true)
  let bigintProto ← mk
  modify fun h => { h with realm := { h.realm with bigintProto := bigintProto } }
  let bigC ← ctorWith "BigInt" .bigintCtor 1 bigintProto
  setHidden g "BigInt" bigC
  if let .obj bc := bigC then
    method bc "asIntN" (.bigintAsN true) 2
    method bc "asUintN" (.bigintAsN false) 2
  method bigintProto "toString" .bigintToString 0
  method bigintProto "valueOf" .bigintValueOf 0
  defineOwn bigintProto (symKey symToStringTag) (.data (.str "BigInt") false false true)
  -- Date: a time value read from the host's clock; `Date.now()` and `getTime`.
  let dateProto ← mk
  modify fun h => { h with realm := { h.realm with dateProto } }
  let dateC ← ctorWith "Date" .dateCtor 7 dateProto
  setHidden g "Date" dateC
  if let .obj dc := dateC then method dc "now" .dateNow 0
  method dateProto "getTime" .dateGetTime 0
  method dateProto "valueOf" .dateGetTime 0
  for (nm, k, l) in dateMethodNames do method dateProto nm ((.x (.dateMethod k))) l
  setHidden dateProto "toGMTString" ((← getObj dateProto).getOwn "toUTCString" |>.map (fun p => match p with
    | .data v .. => v | _ => .undef) |>.getD .undef)
  defineOwn dateProto (symKey symToPrimitive) (.data (← mkNative ((.x (.dateMethod 39))) "[Symbol.toPrimitive]" 1) false false true)
  if let .obj dc := dateC then
    method dc "UTC" (.x .dateUTC) 7
    method dc "parse" (.x .dateParse) 1
  -- performance.now() (High Resolution Time §4.3): the host's clock in ms.
  let perf ← mk
  setHidden g "performance" (.obj perf)
  method perf "now" .perfNow 0
  -- RegExp (§22.2)
  let regexpProto ← mk
  modify fun h => { h with realm := { h.realm with regexpProto } }
  setHidden g "RegExp" (← ctorWith "RegExp" .regexpCtor 2 regexpProto)
  method regexpProto "exec" .regexpExec 1
  method regexpProto "test" .regexpTest 1
  method regexpProto "toString" .regexpToString 0
  for (nm, k) in [("source", 0), ("flags", 1), ("global", 2), ("ignoreCase", 3), ("multiline", 4),
      ("sticky", 5), ("unicode", 6), ("dotAll", 7)] do
    let getter ← mkNative (.regexpGetter k) ("get " ++ nm) 0
    defineOwn regexpProto nm (.acc getter .undef false true)
  let sp := (← realm).stringProto
  method sp "match" .stringMatch 1
  method sp "matchAll" .stringMatchAll 1
  method sp "search" .stringSearch 1
  -- Proxy (§28.2)
  let proxyC ← mkNative .proxyCtor "Proxy" 2
  setHidden g "Proxy" proxyC
  if let .obj pc := proxyC then method pc "revocable" (.x .proxyRevocable) 2
  -- ArrayBuffer (§25.1) and the typed arrays (§23.2)
  let bufferProto ← mk
  modify fun h => { h with realm := { h.realm with bufferProto } }
  let bufferC ← ctorWith "ArrayBuffer" .bufferCtor 1 bufferProto
  setHidden g "ArrayBuffer" bufferC
  if let .obj bc := bufferC then method bc "isView" .bufferIsView 1
  method bufferProto "slice" .bufferSlice 2
  let typedProto ← mk
  let ap := (← realm).arrayProto
  -- methods with Array.prototype's steps after ValidateTypedArray, as functions of their own
  -- (§23.2.3); @@iterator is the same function as values (§23.2.3.37)
  for i in [0:typedGenericNames.size] do
    let (nm, l) := typedGenericNames[i]!
    if let some (.data f ..) := (← getObj ap).getOwn nm then
      setHidden typedProto (typedGenericKey nm) f
      method typedProto nm (.x (.typedGeneric i)) l
  if let some p := (← getObj typedProto).getOwn "values" then
    defineOwn typedProto (symKey symIterator) p
  method typedProto "set" .typedSet 1
  method typedProto "subarray" .typedSubarray 2
  method typedProto "fill" .typedFill 1
  let mut typedProtos := #[]
  for i in [0:typedNames.size] do
    let (nm, size) := typedNames[i]!
    let p ← alloc { proto := .obj typedProto }
    defineOwn p "BYTES_PER_ELEMENT" (.data (.num (Float.ofNat size)) false false false)
    let c ← ctorWith nm (.typedCtor i) 3 p
    if let .obj cid := c then defineOwn cid "BYTES_PER_ELEMENT" (.data (.num (Float.ofNat size)) false false false)
    setHidden g nm c
    typedProtos := typedProtos.push p
  modify fun h => { h with realm := { h.realm with typedProtos } }
  -- DataView (§25.3)
  let dataViewProto ← mk
  modify fun h => { h with realm := { h.realm with dataViewProto } }
  setHidden g "DataView" (← ctorWith "DataView" .dataViewCtor 1 dataViewProto)
  defineOwn dataViewProto (symKey symToStringTag) (.data (.str "DataView") false false true)
  for (nm, ty) in [("Int8", 0), ("Uint8", 1), ("Int16", 3), ("Uint16", 4), ("Int32", 5), ("Uint32", 6),
      ("Float32", 7), ("Float64", 8), ("BigInt64", 9), ("BigUint64", 10), ("Float16", 11)] do
    method dataViewProto ("get" ++ nm) (.dataViewGet ty) 1
    method dataViewProto ("set" ++ nm) (.dataViewSet ty) 2
  defineOwn bufferProto (symKey symToStringTag) (.data (.str "ArrayBuffer") false false true)
  -- %TypedArray% (§23.2.1, §23.2.2): the constructor that every typed array constructor
  -- inherits, with `from` and `of`; its prototype holds the accessors and methods
  let taC ← mkNative (.x .typedArrayCtor) "TypedArray" 0
  if let .obj tc := taC then
    defineOwn tc "prototype" (.data (.obj typedProto) false false false)
    method tc "from" (.x .typedFrom) 1
    method tc "of" (.x .typedOf) 0
    modify fun h => { h with realm := { h.realm with typedArrayCtor := tc } }
    for p in typedProtos do
      if let some (.data (.obj c) ..) := (← getObj p).getOwn "constructor" then
        modifyObj c fun o => { o with proto := .obj tc }
  setHidden typedProto "constructor" taC
  for (nm, w) in [("buffer", 0), ("byteLength", 1), ("byteOffset", 2), ("length", 3)] do
    getter typedProto nm ((.x (.typedGetter w)))
  defineOwn typedProto (symKey symToStringTag)
    (.acc (← mkNative ((.x (.typedGetter 4))) "get [Symbol.toStringTag]" 0) .undef false true)
  for (nm, k, l) in typedMethodNames do method typedProto nm ((.x (.typedMethod k))) l
  -- ArrayBuffer (§25.1.6): accessors, `resize`, `transfer`
  for (nm, w) in [("byteLength", 0), ("maxByteLength", 1), ("resizable", 2), ("detached", 3)] do
    getter bufferProto nm ((.x (.bufferGetter w)))
  method bufferProto "resize" (.x .bufferResize) 1
  method bufferProto "transfer" ((.x (.bufferTransfer false))) 0
  method bufferProto "transferToFixedLength" ((.x (.bufferTransfer true))) 0
  -- SharedArrayBuffer (§25.2)
  let sharedProto ← mk
  modify fun h => { h with realm := { h.realm with sharedBufferProto := sharedProto } }
  setHidden g "SharedArrayBuffer" (← ctorWith "SharedArrayBuffer" (.x .sharedCtor) 1 sharedProto)
  for (nm, w) in [("byteLength", 0), ("maxByteLength", 1), ("growable", 2)] do
    getter sharedProto nm ((.x (.sharedGetter w)))
  method sharedProto "grow" (.x .sharedGrow) 1
  method sharedProto "slice" (.x .sharedSlice) 2
  defineOwn sharedProto (symKey symToStringTag) (.data (.str "SharedArrayBuffer") false false true)
  -- Atomics (§25.4), without `wait`
  let atomicsObj ← mk
  for (nm, k, l) in atomicsNames do method atomicsObj nm ((.x (.atomics k))) l
  defineOwn atomicsObj (symKey symToStringTag) (.data (.str "Atomics") false false true)
  setHidden g "Atomics" (.obj atomicsObj)
  -- Iterator (§27.1.3) and the iterator helpers (§27.1.4)
  let ip := (← realm).iterProto
  let iterC ← mkNative (.x .iteratorCtor) "Iterator" 0
  if let .obj ic := iterC then
    defineOwn ic "prototype" (.data (.obj ip) false false false)
    method ic "from" (.x .iteratorFrom) 1
    method ic "concat" (.x .iteratorConcat) 0
  setHidden g "Iterator" iterC
  setHidden ip "constructor" iterC
  for (nm, k) in [("map", 0), ("filter", 1), ("take", 2), ("drop", 3), ("flatMap", 4)] do
    method ip nm ((.x (.iterLazy k))) 1
  for (nm, k, l) in [("reduce", 0, 1), ("toArray", 1, 0), ("forEach", 2, 1), ("some", 3, 1), ("every", 4, 1), ("find", 5, 1)] do
    method ip nm ((.x (.iterEager k))) l
  if ((← getObj ip).getOwn (symKey symToStringTag)).isNone then
    setHidden ip (symKey symToStringTag) (.str "Iterator")
  let helperProto ← alloc { proto := .obj ip }
  method helperProto "next" (.x .helperNext) 0
  method helperProto "return" (.x .helperReturn) 0
  defineOwn helperProto (symKey symToStringTag) (.data (.str "Iterator Helper") false false true)
  let wrapProto ← alloc { proto := .obj ip }
  method wrapProto "next" (.x .helperNext) 0
  method wrapProto "return" (.x .helperReturn) 0
  modify fun h => { h with realm := { h.realm with iterHelperProto := helperProto, wrapIterProto := wrapProto } }
  -- String.prototype.isWellFormed and toWellFormed (§22.1.3.10, §22.1.3.32)
  let sp := (← realm).stringProto
  method sp "isWellFormed" (.x .stringIsWellFormed) 0
  method sp "toWellFormed" (.x .stringToWellFormed) 0

/-- A fresh realm. -/
def freshHeapOf (host : Option H) (hostCall : H → Nat → Array HostArg → Nat → H × HostAns) : HeapOf H :=
  match (initRealm : M Unit).run { host, hostCall } with
  | .ok _ h => h
  | .error _ h => h

/-- A fresh realm with no host. -/
def freshHeap : Heap := freshHeapOf none fun h _ _ _ => (h, .val .undef)

/-- Fuel for one script: far more than any nesting or loop the step budget allows (the
default budget `Heap.steps` is 10^9; `fuel_covers_steps` in `JS/Tests.lean`). It is the
largest Nat that is a scalar on a 32-bit target (2^31 - 1, `LEAN_MAX_SMALL_NAT` on wasm32):
each call and loop iteration subtracts one, and above it every subtraction allocates a big
number in the Foafnaut Wasm build (the first fib(24) turn there: about 580 ms with 2^40, 265 ms with
this). -/
def defaultFuel : Nat := 2147483647

/-- GlobalDeclarationInstantiation (§16.1.7), then the statements. -/
def runScriptM (s : Script) (checkpoint : Bool := true) : M Unit := do
  let h ← get
  let g := h.realm.globalObj
  let ctx : Ctx := { env := 0, thisV := .obj g, strict := s.strict }
  for v in s.vars do
    if ((h.obj g).getOwn v).isNone then defineOwn g v (.data .undef true true false)
  -- top-level functions are properties of the global object
  for st in s.body do
    if let .funDecl name f := st then
      defineOwn g name (.data (← makeClosure ctx f (decl := true)) true true false)
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
  if checkpoint then runJobs defaultFuel
  pure ()

/-- The result of running a script. -/
inductive Outcome where
  | ok
  | threw (v : Value) (msg : String)
  | syntaxError (msg : String)
  | halted (why : String)
  deriving Inhabited

/-- Describe a thrown value the way an uncaught error is reported. -/
def describeThrown (h : HeapOf H) (v : Value) : String :=
  match (toStr 100 v).run h with
  | .ok s _ => s
  | .error _ _ => "(an exception whose string conversion threw)"

def runScript (h : HeapOf H) (src : String) (strict : Bool := false) : Outcome × HeapOf H :=
  match (parseScript src strict).map Resolve.script with
  | .error e => (.syntaxError e, h)
  | .ok s =>
    match (runScriptM s : M Unit).run h with
    | .ok _ h' => (.ok, h')
    | .error (.throw v) h' => (.threw v (describeThrown h' v), h')
    | .error (.halt w) h' => (.halted w, h')

/-! ## The entry points of an embedding host

A page host (`WasmVM.Hosts.LeanJS`) runs its scripts with no microtask checkpoint after
them (`evalScript`), calls functions of the page (`callFunction`), and runs the
checkpoint when its event loop says (`checkpoint`). -/

/-- Run a classic script, with no microtask checkpoint after it. -/
def evalScript (h : HeapOf H) (src : String) : Outcome × HeapOf H :=
  match (parseScript src false).map Resolve.script with
  | .error e => (.syntaxError e, h)
  | .ok s =>
    match (runScriptM s false : M Unit).run h with
    | .ok _ h' => (.ok, h')
    | .error (.throw v) h' => (.threw v (describeThrown h' v), h')
    | .error (.halt w) h' => (.halted w, h')

/-- Call a function value; the outcome and the value it returned. -/
def callFunction (h : HeapOf H) (f thisV : Value) (args : Array Value) : (Outcome × Value) × HeapOf H :=
  match (callV defaultFuel f thisV args : M Value).run h with
  | .ok v h' => ((.ok, v), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), .undef), h')
  | .error (.halt w) h' => ((.halted w, .undef), h')

/-- `o[name](...args)`. -/
def callMethod (h : HeapOf H) (o : Value) (name : String) (args : Array Value) : (Outcome × Value) × HeapOf H :=
  match (do let f ← getV defaultFuel o name; callV defaultFuel f o args : M Value).run h with
  | .ok v h' => ((.ok, v), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), .undef), h')
  | .error (.halt w) h' => ((.halted w, .undef), h')

/-- The completion value of a script (an indirect `eval`, §19.2.1.1). -/
def evalValue (h : HeapOf H) (src : String) : (Outcome × Value) × HeapOf H :=
  callFunction h (.obj h.realm.evalFn) .undef #[.str src]

/-- An object whose methods are the host's natives: `names[k]` (name and length) is
`Native.host k`. Not enumerable, as built-in methods are. -/
def hostObject (h : HeapOf H) (names : Array (String × Nat)) : Value × HeapOf H :=
  let make : M Value := do
    let o ← newObject
    for k in [0:names.size] do
      let (nm, len) := names[k]!
      defineOwn o nm (.data (← mkNative (.host k) nm len) true false true)
    pure (.obj o)
  match make.run h with
  | .ok v h' => (v, h')
  | .error _ h' => (.undef, h')

/-- Add built-ins of the engine (not the host's) to an object, as `hostObject` makes the
host's: not enumerable. -/
def addNatives (h : HeapOf H) (o : Value) (names : Array (String × Native × Nat)) : HeapOf H :=
  match o with
  | .obj id =>
    let make : M Unit := do
      for (nm, nat, len) in names do defineOwn id nm (.data (← mkNative nat nm len) true false true)
    match make.run h with
    | .ok _ h' => h'
    | .error _ h' => h'
  | _ => h

/-- The microtask checkpoint: the jobs run until none is left (§9.5; HTML "perform a
microtask checkpoint"). A job that throws is dropped. The answer counts the jobs run. -/
def checkpoint (h : HeapOf H) : (Outcome × Nat) × HeapOf H :=
  let before := h.jobsRun
  match (runJobs defaultFuel : M Unit).run h with
  | .ok _ h' => ((.ok, h'.jobsRun - before), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), h'.jobsRun - before), h')
  | .error (.halt w) h' => ((.halted w, h'.jobsRun - before), h')

/-- Run a script in a fresh realm; the printed lines and the outcome. -/
def run (src : String) : Outcome × Array String :=
  let (o, h) := runScript freshHeap src
  (o, h.out)

end L4Factoidal.JS
