import L4Factoidal.JS.Value
import L4Factoidal.JS.Clone
import L4Factoidal.JS.Parser
import L4Factoidal.JS.Resolve
import L4Factoidal.JS.Date
import L4Factoidal.JS.NumFmt
import L4Factoidal.JS.Base64
import L4Factoidal.JSON.Parser
import L4Factoidal.JS.JsonText
import L4Factoidal.WHATWG.URLPattern
import L4Factoidal.Temporal.Parse
import L4Factoidal.Prim.Float16
import L4Factoidal.Unicode.Normalization

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
    let (h, objs) := h.noteObj objs id
    { h with objs := objs.modify id f }

/-- Object `id` and the array with a placeholder in its place. Not inlined: the compiler
must not move the write of the placeholder after the uses of the object, or the object
would still be shared with the array while it changes (and its elements copied). -/
@[noinline] def takeAt (objs : Array Obj) (id : Nat) : Obj × Array Obj :=
  objs.swapAt! id default

/-- Change object `id` with `f`, which also answers a value. The object is moved out of the
heap while `f` runs, so `f` holds the only reference and a change to its elements does not
copy them (an Array push is amortised constant time, not a copy of the array).

Specialised for `f` (`@[specialize]`): each caller passes a function written in place, and without
this every write of an element or a property made a closure for it, called it through a pointer
and took its answer from a pair. -/
@[specialize] def updateObj {α} [Inhabited α] (id : Nat) (f : Obj → α × Obj) : M α :=
  modifyGet fun h =>
    let objs := h.objs
    let h := { h with objs := #[] }
    let (h, objs) := h.noteObj objs id
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
      -- an absent element of a non-extensible array cannot be added back here
      if h : i < es.size then
        -- an absent element of a non-extensible array cannot be added back here
        if !o.extensible && es[i].isHole then (false, o) else
        let o := { o with kind := .ordinary }
        (true, { o with kind := .array (es.set i v h) })
      else (false, o)
    | _ => (false, o)

/-- Overwrite an own writable data property of a non-exotic object, in place; `false` when
the property is absent or not plain (the caller takes the general path). -/
def setOwnData (id : Nat) (key : String) (v : Value) : M Bool :=
  updateObj id fun o =>
    if key == "length" && o.isArray then (false, o) else
    match o.kind with
    | .array _ | .proxy .. | .typed .. | .prim _ => (false, o)
    | _ =>
      match o.props.get? key with
      | some (.data _ true e c) =>
        (true, { o with props := o.props.insert key (.data v true e c) })
      | _ => (false, o)

@[inline] def realm : M Realm := do pure (← get).realm

/-! ## Realms (§9.3)

A heap has one realm unless its host makes more (`ColdHeap.realms`): a test host's
`$262.createRealm`, as a browser makes one for each new global (a frame's window). Objects
of all realms live in the one heap; what a realm owns is its intrinsics (`Realm`) and its
global environment record, which is environment 0 while the realm runs. A call of a
function of another realm runs in that realm (`inRealm`): its intrinsics and its global
environment are swapped in for the call and back after it, a throw included. With one realm
none of this runs: `realms` is empty, and each check is that one test. -/

/-- Make realm `k` the running realm: the running realm's intrinsics and global environment
go to its entry of `realms`, realm `k`'s come out (its entry keeps no copy, so environment 0
has one owner and changes in place). Nothing happens when `k` runs already or is not a realm
of the heap. -/
def switchRealm (k : Nat) : M Unit := modify fun h =>
  if k == h.curRealm || k ≥ h.realms.size || h.curRealm ≥ h.realms.size then h else
  let saved : SavedRealm := { (h.realms[h.curRealm]!) with realm := h.realm, env0 := h.envs[0]! }
  let realms := h.realms.set! h.curRealm saved
  let next := realms[k]!
  let realms := realms.set! k { next with env0 := {} }
  let envs := h.envs
  let h := { h with envs := #[] }
  let (h, envs) := h.noteEnv envs 0
  { h with realms, realm := next.realm, envs := envs.set! 0 next.env0, curRealm := k }

/-- Run `act` in realm `k`, then go back to the realm that ran before, on a throw too. -/
@[inline] def inRealm {α} (k : Nat) (act : M α) : M α := do
  let back := (← get).curRealm
  switchRealm k
  let r ← tryCatch act (fun e => do switchRealm back; throw e)
  switchRealm back
  pure r

/-- The realm a function object belongs to (its [[Realm]]): realm 0 unless another realm
made it. -/
@[inline] def fnRealmIdx (h : HeapOf H) (id : Nat) : Nat := h.fnRealm.getD id 0

/-- Record that the running realm made function object `id` (nothing in realm 0). -/
@[inline] def tagFn (id : Nat) : M Unit :=
  modify fun h => if h.curRealm == 0 then h else { h with fnRealm := h.fnRealm.insert id h.curRealm }


/-- Put an environment record in a free slot of the environment array. -/
@[inline] def pushEnv (en : Env) : M Nat :=
  modifyGet fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    match h.envFree.back? with
    | some e =>
      let (h, envs) := h.noteEnv envs e
      (e, { h with envFree := h.envFree.pop, envs := envs.set! e en })
    | none => (envs.size, { h with envs := envs.push en })

@[inline] def newEnv (parent : Nat) : M Nat := pushEnv { parent }

/-- Environment `e` is not reachable any more: drop its contents and reuse its slot. -/
@[inline] def releaseEnv (e : Nat) : M Unit :=
  modify fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    let (h, envs) := h.noteEnv envs e
    { h with envs := envs.set! e default, envFree := h.envFree.push e }

/-- Change an environment in place: the array and the record are taken out while `f` runs. -/
@[inline] def modifyEnv (e : Nat) (f : Env → Env) : M Unit :=
  modify fun h =>
    let envs := h.envs
    let h := { h with envs := #[] }
    let (h, envs) := h.noteEnv envs e
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

/-- One step less in the budget. Not inlined: here the record is the function's own argument at its
last use, so the compiler updates it in place when nothing else holds it. Inlined into the
evaluator's large functions, the same update was compiled as a new record at every call (88 bytes;
`docs/bubblepopjs-heap.md`, section 1.4). -/
@[noinline] def HeapOf.decStep (h : HeapOf H) : HeapOf H := { h with steps := h.steps - 1 }

/-- `decStep` is the record update it stands for. -/
@[simp] theorem HeapOf.decStep_eq (h : HeapOf H) : h.decStep = { h with steps := h.steps - 1 } := rfl

/-- The step of a function call. It looks at the size of the heap every time: a run of few
steps (an event handler, a timer callback) starts with a call, so on a full heap no run gets
further than its first call, however short the runs are. -/
@[inline] def tickCall : M Unit := do
  let h ← get
  if h.steps == 0 then throw (.halt "step budget exhausted")
  if h.full then throw (.halt heapFullMsg)
  set h.decStep

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

/-- The most values `iterEach` takes from one iterator: past it the run halts. Each value also
takes a step (`tick`), so the step budget ends any run long before this. -/
def iterEachMax : Nat := 4294967296

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

/-- The [[ArrayLength]] of a length-tracking typed array (§10.4.5: `auto`, a view made on a
resizable buffer with no length): its length follows the buffer's (`typedLenOf`). No typed
array has this many elements (a buffer holds at most `maxBufferBytes`), so a fixed length is
never it. -/
-- noinline: one value made at start; inlined, the generated C read 2^53 from decimal text through
-- GMP at each `typedOob` and `typedLenOf` call (each Float64Array access; issue 1031).
@[noinline] def autoLen : Nat := 2 ^ 53

/-- The steps a value's size is worth to a built-in that walks it: a step for every 64
bytes of a string, 64 elements of an array, or 4096 bytes of an ArrayBuffer or typed
array (copied or compared at memory speed). -/
def sizeCost (v : Value) : M Nat := do
  match v with
  | .str s => pure (s.utf8ByteSize / 64)
  | .obj id => match (← getObj id).kind with
    | .array es => pure (es.size / 64)
    | .buffer b => pure (b.size / 4096)
    | .typed _ _ _ len => pure ((if len == autoLen then 0 else len) / 4096)
    | _ => pure 0
  | _ => pure 0

/-- `sizeCost` as a function of the heap (`sizeCost_eq`). -/
def sizeCostOf (h : HeapOf H) (v : Value) : Nat :=
  match v with
  | .str s => s.utf8ByteSize / 64
  | .obj id => match (h.obj id).kind with
    | .array es => es.size / 64
    | .buffer b => b.size / 4096
    | .typed _ _ _ len => (if len == autoLen then 0 else len) / 4096
    | _ => 0
  | _ => 0

theorem sizeCost_eq (v : Value) (h : HeapOf H) : sizeCost v h = .ok (sizeCostOf h v) h := by
  unfold sizeCost sizeCostOf
  cases v <;> try rfl
  rename_i id
  simp only [getObj, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  cases hk : (h.obj id).kind <;> simp only [hk] <;> rfl

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

/-- `cachedReceiverCost` as a function of the heap. -/
def cachedReceiverCostOf (h : HeapOf H) (id : Native) (thisV : Value) : Option Nat :=
  match thisV with
  | .str s =>
    if !(id == .stringCharAt || id == .stringCharCodeAt) then none
    else match h.reCache with
      | some (t, _) => if t == s then some (s.utf8ByteSize / 4096) else none
      | none => none
  | _ => none

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

/-- `subjectCached` as a function of the heap. -/
def subjectCachedOf (h : HeapOf H) (id : Native) (args : Array Value) : Bool :=
  match id, (args[0]? : Option Value) with
  | .regexpExec, some (Value.str s) | .regexpTest, some (Value.str s) =>
    match h.reCache with
    | some (t, _) => t == s
    | none => false
  | _, _ => false

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
      { o with kind := .array ((es ++ Array.replicate (i - es.size) Value.hole).push v) }
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
      -- the index becomes absent; the length stays (§10.4.2: deleting never changes it)
      if i < es.size then { o with kind := .array (es.set! i .hole) }
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

/-- The length of an Array stored as ordinary properties. -/
def Obj.generalArrayLen (o : Obj) : Option (Float × Bool) :=
  if !o.isArray then none else
  match o.kind, o.props.get? "length" with
  | .ordinary, some (.data (.num l) w _ _) => some (l, w)
  | _, _ => none

/-- ArraySetLength deletes indexed properties in descending order, and keeps
the failed index and everything below it when an index cannot be deleted. -/
def Obj.shrinkGeneralArray (o : Obj) (length : Nat) : Nat × Obj := Id.run do
  let keys := o.ownKeys
  let mut result := o
  for key in keys.reverse do
    if let some index := arrayIndex? key then
      if index < length then break
      if let some prop := result.props.get? key then
        if !prop.configurable then return (index + 1, result)
        result := { result with props := result.props.erase key }
  return (length, result)

/-- ECMA-262 §10.4.2.4 for Arrays stored as ordinary properties. Conversion
can run user code twice, so read the current length descriptor after both
conversions. No deletion in the subsequent scan invokes user code. -/
def setGeneralArrayLength (number : Value → M Float) (id : Nat) (request : Desc) : M Bool := do
  let length ← match request.value with
    | none => pure none
    | some value =>
      let n := toUint32 (← number value)
      let x ← number value
      if Float.ofNat n != x then throwErr .range "Invalid array length"
      pure (some n)
  let o ← getObj id
  let some (.data (.num old) writable enumerable configurable) := o.getOwn "length" | return false
  let prop := PropV.data (.num old) writable enumerable configurable
  let request := { request with value := length.map (fun n => .num (Float.ofNat n)) }
  if !request.allowedOn prop then return false
  let storeLength := fun (arr : Obj) (n : Float) =>
    arr.putOwn "length" (.data (.num n) (request.writable.getD writable) enumerable configurable)
  match length with
  | some n =>
    if Float.ofNat n < old then
      charge o.keys.size
      let (resultLen, result) := o.shrinkGeneralArray n
      modifyObj id fun _ => storeLength result (Float.ofNat resultLen)
      return resultLen == n
    else
      modifyObj id fun current => storeLength current (Float.ofNat n)
      return true
  | none =>
    modifyObj id fun current => storeLength current old
    return true

/-- GetFunctionRealm (§7.3.24): the realm of a function, through bound functions to their
target and through proxies to theirs (a revoked proxy is a TypeError); the running realm for
anything else. With one realm, the running realm. -/
def funRealm (v : Value) : M Realm := do
  let h ← get
  if h.realms.isEmpty then return h.realm
  let mut cur := v
  for _ in [0:4096] do
    match cur with
    | .obj id =>
      match (h.obj id).kind with
      | .bound t _ _ => cur := t
      | .proxy t hnd =>
        if let .null := hnd then throwErr .type "Cannot perform 'GetFunctionRealm' on a proxy that has been revoked"
        cur := t
      | .closure .. | .native _ =>
        let k := fnRealmIdx h id
        return (if k == h.curRealm then h.realm else (h.realms.getD k {}).realm)
      | _ => return h.realm
    | _ => return h.realm
  return h.realm

/-- `p` when it is an object, else the intrinsic `pick` of `nt`'s realm: the last steps of
GetPrototypeFromConstructor (§10.1.14) after `nt.prototype` was read. -/
def protoOr (p nt : Value) (pick : Realm → Nat) : M Value := do
  if p.isObj then pure p else pure (.obj (pick (← funRealm nt)))

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
    | (.x .suppressedErrorCtor) | (.x .disposableStackCtor) | (.x .asyncDisposableStackCtor) => true
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
    -- a bound function constructs when its target does (BoundFunctionCreate, §10.4.1.3)
    | .bound (.obj t) .. => do
      let rec go : Nat → Nat → M Bool
        | 0, _ => pure false
        | k + 1, t => do
          match (← getObj t).kind with
          | .bound (.obj t') .. => go k t'
          | .proxy (.obj t') _ => pure (← getObj t').kind.constructs
          | kd => pure kd.constructs
      go 1000 t
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
  tagFn o
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
  tagFn id
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

/-- `n` zero bytes (a new ArrayBuffer's data block, §25.1.3.1 CreateByteDataBlock), as
`ByteArray.mk (Array.replicate n 0)` writes it: an array of `n` boxed values, then a copy.
The compiled program runs `zeroBytesFast` (`zeroBytes_eq_fast`). -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Append `k` zero bytes. -/
def pushZeroBytes : Nat → ByteArray → ByteArray
  | 0, b => b
  | k + 1, b => pushZeroBytes k (b.push 0)

/-- `n` zero bytes pushed into one array of capacity `n`: no boxed array and no copy. The
Canvas 2D prelude makes an ArrayBuffer for each batch; the boxed form took 8 bytes of fresh
memory per byte, and the kernel's zeroing of it was 8 % of a frame (issue 1098). -/
def zeroBytesFast (n : Nat) : ByteArray := pushZeroBytes n (ByteArray.emptyWithCapacity n)

theorem push0_toList (b : ByteArray) : (b.push 0).data.toList = b.data.toList ++ [0] := by
  simp [ByteArray.push]

theorem pushZeroBytes_toList (k : Nat) (b : ByteArray) :
    (pushZeroBytes k b).data.toList = b.data.toList ++ List.replicate k 0 := by
  induction k generalizing b with
  | zero => simp [pushZeroBytes]
  | succ k ih =>
    simp only [pushZeroBytes, ih, push0_toList, List.append_assoc]
    rw [List.singleton_append, ← List.replicate_succ]

/-- **Kind: refinement.** Says the pushed zeros are the reference's `n` zero bytes. Does not
say anything about speed. -/
@[csimp] theorem zeroBytes_eq_fast : @zeroBytes = @zeroBytesFast := by
  funext n
  apply ByteArray.ext
  apply Array.ext'
  simp only [zeroBytesFast, pushZeroBytes_toList, zeroBytes, Array.toList_replicate]
  rfl

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

/-! ### Direct element access for the one-, two- and four-byte integer types

`typedRead` and `typedBytes` are the reference: little-endian sums and digits over `List.range w`
with powers of two. The compiled program runs `typedReadByteFast` and `typedBytesByteFast`
(`@[csimp]`, proved equal below): byte reads and constant multipliers, no list and no power.

A note for whoever extends the proofs: nothing here may ask Lean whether two terms with a product
by a large literal are equal by computation (`rfl`, `show`, `decide` on the whole sum, or a `simp`
that closes the goal by reflexivity before the two sides are the same text). `n * 16777216` with
`n` not a literal unfolds `Nat.mul` one successor at a time: a first draft of these theorems did
not finish in five minutes and passed 6 GB. The lemmas below only rewrite. -/

/-- The little-endian sum of two bytes, as the reference writes it and as two terms. -/
theorem leSum2 (b : Nat → Nat) :
    (List.range 2).foldl (fun a k => a + b k * 2 ^ (8 * k)) 0 = b 0 + b 1 * 256 := by
  have r : List.range 2 = [0, 1] := rfl
  have p0 : (2:Nat) ^ (8 * 0) = 1 := by decide
  have p1 : (2:Nat) ^ (8 * 1) = 256 := by decide
  rw [r, List.foldl_cons, List.foldl_cons, List.foldl_nil, p0, p1, Nat.mul_one, Nat.zero_add]

/-- The little-endian sum of four bytes. -/
theorem leSum4 (b : Nat → Nat) :
    (List.range 4).foldl (fun a k => a + b k * 2 ^ (8 * k)) 0
      = b 0 + b 1 * 256 + b 2 * 65536 + b 3 * 16777216 := by
  have r : List.range 4 = [0, 1, 2, 3] := rfl
  have p0 : (2:Nat) ^ (8 * 0) = 1 := by decide
  have p1 : (2:Nat) ^ (8 * 1) = 256 := by decide
  have p2 : (2:Nat) ^ (8 * 2) = 65536 := by decide
  have p3 : (2:Nat) ^ (8 * 3) = 16777216 := by decide
  rw [r, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    p0, p1, p2, p3, Nat.mul_one, Nat.zero_add]

/-- The two little-endian bytes of a number, as the reference writes them and as two terms. -/
theorem leBytes2 (v : Nat) :
    ByteArray.mk ((List.range 2).toArray.map fun k => (v / 2 ^ (8 * k) % 256).toUInt8)
      = ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8] := by
  have r : List.range 2 = [0, 1] := rfl
  have p0 : (2:Nat) ^ (8 * 0) = 1 := by decide
  have p1 : (2:Nat) ^ (8 * 1) = 256 := by decide
  rw [r, List.map_toArray, List.map_cons, List.map_cons, List.map_nil, p0, p1, Nat.div_one]

/-- The four little-endian bytes of a number. -/
theorem leBytes4 (v : Nat) :
    ByteArray.mk ((List.range 4).toArray.map fun k => (v / 2 ^ (8 * k) % 256).toUInt8)
      = ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8, (v / 65536 % 256).toUInt8,
          (v / 16777216 % 256).toUInt8] := by
  have r : List.range 4 = [0, 1, 2, 3] := rfl
  have p0 : (2:Nat) ^ (8 * 0) = 1 := by decide
  have p1 : (2:Nat) ^ (8 * 1) = 256 := by decide
  have p2 : (2:Nat) ^ (8 * 2) = 65536 := by decide
  have p3 : (2:Nat) ^ (8 * 3) = 16777216 := by decide
  rw [r, List.map_toArray, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    p0, p1, p2, p3, Nat.div_one]

/-- Direct reads for the unsigned one-byte types and the integer types of two and four bytes
(Int8 keeps the reference path). -/
def typedReadByteFast (ty : Nat) (bytes : ByteArray) (at_ : Nat) : Value :=
  match ty with
  | 1 | 2 => .num (Float.ofNat (bytes.get! at_).toNat)
  | 3 =>
    let x := (bytes.get! at_).toNat + (bytes.get! (at_ + 1)).toNat * 256
    .num (Float.ofInt (if x ≥ 32768 then (x : Int) - 65536 else x))
  | 4 => .num (Float.ofNat ((bytes.get! at_).toNat + (bytes.get! (at_ + 1)).toNat * 256))
  | 5 =>
    let x := (bytes.get! at_).toNat + (bytes.get! (at_ + 1)).toNat * 256
      + (bytes.get! (at_ + 2)).toNat * 65536 + (bytes.get! (at_ + 3)).toNat * 16777216
    .num (Float.ofInt (if x ≥ 2147483648 then (x : Int) - 4294967296 else x))
  | 6 => .num (Float.ofNat ((bytes.get! at_).toNat + (bytes.get! (at_ + 1)).toNat * 256
      + (bytes.get! (at_ + 2)).toNat * 65536 + (bytes.get! (at_ + 3)).toNat * 16777216))
  | _ => typedRead ty bytes at_

/-- **Kind: refinement.** Says the direct read preserves every result of
`typedRead`, for all type tags, buffers and offsets. Does not say the reference
implements all of ECMA-262 or that this is faster. -/
@[csimp] theorem typedRead_eq_byteFast : typedRead = typedReadByteFast := by
  funext ty bytes at_
  match ty with
  | 0 | _ + 7 => rfl
  | 1 | 2 =>
    simp only [typedRead, typedReadByteFast, List.range_one, List.foldl_cons,
      List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
  | 3 | 4 => simp only [typedRead, typedReadByteFast, leSum2, Nat.add_zero]
  | 5 | 6 => simp only [typedRead, typedReadByteFast, leSum4, Nat.add_zero]

/-- The eight bytes of a 64-bit word, least significant first. -/
def leBytesU64 (v : UInt64) : ByteArray :=
  ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
    (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]

/-- The four bytes of a 32-bit word, least significant first. -/
def leBytesU32 (v : UInt32) : ByteArray :=
  ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

/-- Byte `k` of a 64-bit word as the reference writes it (a quotient by a power of two) and as a shift. -/
theorem leByte64 (v : UInt64) (k : Nat) (hk : k < 8) :
    (v.toNat / 2 ^ (8 * k) % 256).toUInt8 = (v >>> (8 * k).toUInt64).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h1 : ((8 * k).toUInt64).toNat = 8 * k := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h1,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : 8 * k < 64)]; simp

theorem leByte32 (v : UInt32) (k : Nat) (hk : k < 4) :
    (v.toNat / 2 ^ (8 * k) % 256).toUInt8 = (v >>> (8 * k).toUInt32).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h1 : ((8 * k).toUInt32).toNat = 8 * k := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, h1,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : 8 * k < 32)]; simp

/-- **Kind: refinement.** The reference's eight little-endian digits of a 64-bit word are its
shifted bytes. -/
theorem leBytes8_eq (v : UInt64) :
    ByteArray.mk ((List.range 8).toArray.map fun k => (v.toNat / 2 ^ (8 * k) % 256).toUInt8) = leBytesU64 v := by
  have e : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [leBytesU64, e, List.map_toArray, List.map_cons, List.map_nil]
  rw [leByte64 v 0 (by omega), leByte64 v 1 (by omega), leByte64 v 2 (by omega), leByte64 v 3 (by omega),
    leByte64 v 4 (by omega), leByte64 v 5 (by omega), leByte64 v 6 (by omega), leByte64 v 7 (by omega)]
  simp only [Nat.mul_zero]
  rfl

/-- **Kind: refinement.** The same for four bytes of a 32-bit word. -/
theorem leBytes4_eq (v : UInt32) :
    ByteArray.mk ((List.range 4).toArray.map fun k => (v.toNat / 2 ^ (8 * k) % 256).toUInt8) = leBytesU32 v := by
  have e : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [leBytesU32, e, List.map_toArray, List.map_cons, List.map_nil]
  rw [leByte32 v 0 (by omega), leByte32 v 1 (by omega), leByte32 v 2 (by omega), leByte32 v 3 (by omega)]
  simp only [Nat.mul_zero]
  rfl

/-- Direct buffers for the integer element types of one, two and four bytes, and for Float32
and Float64. -/
def typedBytesByteFast (ty : Nat) (x : Float) : ByteArray :=
  match ty with
  | 0 | 1 => ByteArray.mk #[(Int.toNat (toInt32Wide x % 256) % 256).toUInt8]
  | 2 => ByteArray.mk #[(clampByte x % 256).toUInt8]
  | 3 | 4 =>
    let v := Int.toNat (toInt32Wide x % 65536)
    ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8]
  | 5 | 6 =>
    let v := Int.toNat (toInt32Wide x % 4294967296)
    ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8, (v / 65536 % 256).toUInt8,
      (v / 16777216 % 256).toUInt8]
  -- Float32 and Float64: the bits as shifted bytes, no division by a power of two (issue 1098:
  -- a Float64Array.set of a Canvas 2D batch spent most of its time in big-number powers).
  | 7 => leBytesU32 x.toFloat32.toBits
  | 11 => typedBytes ty x
  | _ => leBytesU64 x.toBits

/-- **Kind: refinement.** Says direct byte writes produce exactly the reference
bytes for every type tag and Float. Does not say anything about speed. -/
@[csimp] theorem typedBytes_eq_byteFast : typedBytes = typedBytesByteFast := by
  funext ty x
  match ty with
  | 7 => simp only [typedBytes, typedBytesByteFast]; exact leBytes4_eq _
  | 11 => rfl
  | 8 | 9 | 10 => simp only [typedBytes, typedBytesByteFast]; exact leBytes8_eq _
  | _ + 12 => simp only [typedBytes, typedBytesByteFast]; exact leBytes8_eq _
  | 0 | 1 | 2 =>
    simp only [typedBytes, typedBytesByteFast, List.range_one, Array.map_singleton, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      show (2 : Int) ^ (8 * 1) = 256 from by decide]
  | 3 | 4 =>
    simp only [typedBytes, typedBytesByteFast, leBytes2, show (2 : Int) ^ (8 * 2) = 65536 from by decide]
  | 5 | 6 =>
    simp only [typedBytes, typedBytesByteFast, leBytes4, show (2 : Int) ^ (8 * 4) = 4294967296 from by decide]
#print axioms typedRead_eq_byteFast
#print axioms typedBytes_eq_byteFast

/-- The source text of a private name from its key: `#x` for `privKey "x"` and for the key of
one class evaluation (`privRk`: the name, `#` and a number; an identifier has no `#`). -/
def privDisplay (key : String) : String :=
  "#" ++ ((key.drop 1).toString.takeWhile (· != '#'))

/-- The `name` of a function stored under a property key (§10.2.9 SetFunctionName). -/
def nameOfKey (key : String) : M String := do
  match symOfKey? key with
  | some id =>
    let d := (← get).syms.getD id ""
    pure (if d.isEmpty && id ≥ wellKnown.size then "" else "[" ++ d ++ "]")
  | none => pure (if isPrivKey key then privDisplay key else keyStr key)



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

/-- The substrings of the ordinary string split, after both arguments are converted.
A zero limit needs no separator search, including when the separator is undefined. -/
def splitPlain (s : String) (separator : Option String) (limit : Nat) : Array String :=
  if limit = 0 then #[] else
  match separator with
  | none => #[s]
  | some sep => (splitOn s sep).extract 0 limit

/-- Every ordinary split result contains at most the requested number of substrings. -/
theorem splitPlain_size_le (s : String) (separator : Option String) (limit : Nat) :
    (splitPlain s separator limit).size ≤ limit := by
  cases limit with
  | zero => simp [splitPlain]
  | succ n =>
    cases separator with
    | none => simp [splitPlain]
    | some sep => simpa [splitPlain] using Nat.min_le_left (n + 1) (splitOn s sep).size

#print axioms splitPlain_size_le

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

/-- Append `undefined` to an internal list kept as an array (the values of `Promise.all` and the
others, §27.2.4.1.2 step 8.e "Append undefined to values"): an own element made directly, so no
setter of `Array.prototype` runs. -/
def pushHole (arr : Value) : M Unit := do
  if let .obj id := arr then
    modifyObj id fun o => match o.kind with
      | .array es => { o with kind := .array (es.push .undef) }
      | _ => o

/-- A function object for a native, without `name` and `length` (internal use). -/
def nativeFn (id : Native) : M Value := do
  let r ← realm
  let o ← alloc { proto := .obj r.functionProto, kind := .native id }
  tagFn o
  pure (.obj o)

/-- The collection methods `Native.x (.collMethod kind op)` checks the receiver for. -/
def collOps : Array Native :=
  #[.mapGet, .mapSet, .mapHas, .mapDelete, .mapClear, .mapSize, .mapForEach, .setAdd,
    .mapIter 4, .mapIter 5, .mapIter 6]

/-- The HTML methods of String.prototype (Annex B.2.2): name, tag, attribute. -/
def htmlMethods : Array (String × String × String) :=
  #[("anchor", "a", "name"), ("big", "big", ""), ("blink", "blink", ""), ("bold", "b", ""),
    ("fixed", "tt", ""), ("fontcolor", "font", "color"), ("fontsize", "font", "size"),
    ("italics", "i", ""), ("link", "a", "href"), ("small", "small", ""), ("strike", "strike", ""),
    ("sub", "sub", ""), ("sup", "sup", "")]

/-- An anonymous built-in function (CreateBuiltinFunction, §10.3.4, with the name ""): the
native `id` with its bound arguments `bargs` first, and own `length` and `name` in that order
(the resolving functions of a promise, a capability's executor, the element functions). -/
def anonFn (id : Native) (bargs : Array Value) (len : Nat) : M Value := do
  let r ← realm
  let f ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn id) .undef bargs }
  defineOwn f "length" (.data (.num (Float.ofNat len)) false false true)
  defineOwn f "name" (.data (.str "") false false true)
  pure (.obj f)

/-- Array.prototype.flat's FlattenIntoArray (§23.1.3.13.1) on dense arrays. -/
def flattenArr (d : Nat) (vs : Array Value) : Nat → M (Array Value)
  | 0 => pure vs
  | f + 1 => do
    let mut out := #[]
    for v in vs do
      match v with
      | .hole => pure ()
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
      | some p =>
        -- an empty pattern matches at every index up to the length, once each
        if p > Str.jsLength s || p < from_ then acc.toList
        else go (p + (if pat.isEmpty then 1 else Str.jsLength pat)) f (acc.push p)
      | none => acc.toList

/-! ## Lifting `yield` and `await` out of expressions

The generator machine suspends only at statement level. A `yield` (or an `await`,
which the parser reads as a `yield` in an async function) inside an expression is
moved before its statement when it is evaluated unconditionally: `f(await p)`
becomes `let %y0 = await p; f(%y0)`. The callee and operands to its left are then
evaluated after the suspension, not before: a known difference from §13.3.6 when
they have side effects. A `yield` on one branch of `&&`, `||`, `??`, `?:` or a logical
assignment runs inside an `if`; one in a destructuring pattern is lowered to statements
(`dstrLower`). A `yield` inside an optional chain stays, and the machine refuses that
statement: https://github.com/danbri/factoidal-core/issues/1167. -/

/-- Lifting: the next temporary, and the statements that must run first. -/
abbrev Lift := StateM (Nat × Array Stmt)

def liftName (k : Nat) : String := "%y" ++ toString k

/-- A computed key of the member holds a `yield` (outside nested functions). -/
def Member.keyHasYield : Member → Bool
  | .mk _ _ (.computed e) _ => e.hasYield
  | _ => false

/-- The property definition holds a `yield` in its key or its value. -/
def PropDef.hasYield : PropDef → Bool
  | .init (.computed k) v => k.hasYield || v.hasYield
  | .init _ v => v.hasYield
  | .getter (.computed k) _ | .setter (.computed k) _ => k.hasYield
  | .spread e => e.hasYield
  | _ => false

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

/-! ### Destructuring assignment with a `yield` in its pattern

`[x = yield] = v`, `({a: o[yield]} = v)`: the pattern's own steps (§13.15.5.5
IteratorDestructuringAssignmentEvaluation, §13.15.5.6 KeyedDestructuringAssignmentEvaluation)
become statements, so the generator machine can stop at each `yield`: for each element the
target's operands, then IteratorStep, then the default, then PutValue. The iterator is closed
in a `finally` (§7.4.11): quietly after a throw, checked after a normal or `return`
completion. The internal calls `%dstr(op, ...)` (`dstrOp`) do GetIterator, the step, the
closes, RequireObjectCoercible and CopyDataProperties. -/

/-- An internal call of the lowering (a `%` name, which source text cannot write). -/
def dstrCall (op : String) (args : List Expr) : Expr := .call (.ident "%dstr") (.str op :: args)

/-- A temporary of the lowering. Its own prefix: a later lift pass of an expression in the
pattern (a default, a target) uses `%y` names in a block of its own, so it cannot hide these. -/
def dstrFresh : StateM Nat String := modifyGet fun k => ("%d" ++ toString k, k + 1)

def dstrLet (x : String) (e : Option Expr) : Stmt := .decl .letK [Decl.mk (.id x) e]

/-- The target of an element that is not a pattern: its operands into temporaries first
(DestructuringAssignmentTarget is evaluated before the value is taken). -/
def dstrTarget : Pat → StateM Nat (List Stmt × Option Expr)
  | .id x => pure ([], some (.ident x))
  | .target (.member o k) => do
    let x ← dstrFresh
    pure ([dstrLet x (some o)], some (.member (.ident x) k))
  | .target (.index o k) => do
    let x ← dstrFresh
    let y ← dstrFresh
    pure ([dstrLet x (some o), dstrLet y (some k)], some (.index (.ident x) (.ident y)))
  | .target e => pure ([], some e)
  | _ => pure ([], none)

/-- One IteratorStep into `v` (left `undefined` when the iterator is done). The record is done
before the call, so a throw of `next`, `done` or `value` does not close it. -/
def dstrStep (it dn : String) (into : String → Stmt) : StateM Nat Stmt := do
  let r ← dstrFresh
  pure (.ifS (.unary .not (.ident dn)) (.block [
    .expr (.assign none (.ident dn) (.bool true)),
    dstrLet r (some (dstrCall "next" [.ident it])),
    .ifS (.unary .not (.member (.ident r) "done"))
      (.block [into r, .expr (.assign none (.ident dn) (.bool false))]) none]) none)

mutual
/-- The default (when the value `v` is `undefined`) and the store into the target, or into a
nested pattern (lowered here when it has a `yield`). A name takes the default directly, so an
anonymous function is named after it. -/
def dstrStore : Nat → Option DeclKind → Pat → Option Expr → Option Expr → String → StateM Nat (List Stmt)
  | 0, _, _, _, _, _ => pure []
  | n + 1, bind, p, tgt, d, v => do
    let undef : Expr := .binary .seq (.ident v) (.unary .void (.num 0))
    -- a name of a `let` or `const` declaration is initialised here (`init`: the binding its
    -- scope made, in its TDZ until then; the steps may be inside the `try` of an array pattern)
    let putV (e : Expr) : Stmt := match p, bind with
      | .id x, some k => .expr (dstrCall "init" [.str x, e, .bool (k == .letK)])
      | _, _ => match tgt with
        | some t => .expr (.assign none t e)
        | none => .expr (.assignPat p e)
    let put ← match p with
      | .obj .. | .arr .. =>
        if p.hasYield then dstrLower n bind v p
        else pure [match bind with
          | some k => Stmt.decl k [Decl.mk p (some (.ident v))]
          | none => Stmt.expr (.assignPat p (.ident v))]
      | _ => pure [putV (.ident v)]
    match p, d with
    -- one statement, not a block: a block would be a scope of its own for the declaration
    | .id _, some e => pure [.ifS undef (putV e) (some (putV (.ident v)))]
    | _, some e => pure (.ifS undef (.expr (.assign none (.ident v) e)) none :: put)
    | _, none => pure put

def dstrElems : Nat → Option DeclKind → String → String → List (Option PatElem) → StateM Nat (List Stmt)
  | 0, _, _, _, _ => pure []
  | _ + 1, _, _, _, [] => pure []
  | n + 1, bind, it, dn, none :: es => do
    let st ← dstrStep it dn (fun _ => .empty)
    pure (st :: (← dstrElems n bind it dn es))
  | n + 1, bind, it, dn, some (.mk p d) :: es => do
    let (prep, tgt) ← dstrTarget p
    let v ← dstrFresh
    let st ← dstrStep it dn (fun r => .expr (.assign none (.ident v) (.member (.ident r) "value")))
    let store ← dstrStore n bind p tgt d v
    pure (prep ++ [dstrLet v none, st] ++ store ++ (← dstrElems n bind it dn es))

def dstrProps : Nat → Option DeclKind → String → List PatProp → StateM Nat (List Stmt × List Expr)
  | 0, _, _, _ => pure ([], [])
  | _ + 1, _, _, [] => pure ([], [])
  | n + 1, bind, src, .mk k p d :: ps => do
    let (keyPrep, key, get) ← match k with
      | .lit s => pure ([], Expr.str s, Expr.member (.ident src) s)
      | .computed e => do
        let x ← dstrFresh
        pure ([dstrLet x (some e)], Expr.ident x, Expr.index (.ident src) (.ident x))
    let (prep, tgt) ← dstrTarget p
    let v ← dstrFresh
    let store ← dstrStore n bind p tgt d v
    let (rest, keys) ← dstrProps n bind src ps
    pure (keyPrep ++ prep ++ [dstrLet v (some get)] ++ store ++ rest, key :: keys)

/-- The statements of `p = src` (`src` a temporary holding the value); with `bind`, the names
of the pattern are bound by declarations of that kind (`let [a = yield] = v`). -/
def dstrLower : Nat → Option DeclKind → String → Pat → StateM Nat (List Stmt)
  | 0, _, _, _ => pure []
  | n + 1, bind, src, .arr es rest => do
    let it ← dstrFresh
    let dn ← dstrFresh
    let ex ← dstrFresh
    let body ← dstrElems n bind it dn es
    let restS ← match rest with
      | none => pure []
      | some rp => do
        let (prep, tgt) ← dstrTarget rp
        let a ← dstrFresh
        let st ← dstrStep it dn (fun r => .expr (dstrCall "push" [.ident a, .member (.ident r) "value"]))
        let store ← dstrStore n bind rp tgt none a
        pure (prep ++ [dstrLet a (some (.array [])), .whileS (.unary .not (.ident dn)) st] ++ store)
    let quiet : Stmt := .ifS (.unary .not (.ident dn)) (.block [
      .expr (.assign none (.ident dn) (.bool true)), .expr (dstrCall "closeQuiet" [.ident it])]) none
    pure [dstrLet it (some (dstrCall "iter" [.ident src])), dstrLet dn (some (.bool false)),
      .tryS (body ++ restS) (some (.id ex)) (some [quiet, .throwS (.ident ex)])
        (some [.ifS (.unary .not (.ident dn)) (.expr (dstrCall "close" [.ident it])) none])]
  | n + 1, bind, src, .obj ps rest => do
    let (body, keys) ← dstrProps n bind src ps
    let restS ← match rest with
      | none => pure []
      | some rp => do
        let (prep, tgt) ← dstrTarget rp
        let a ← dstrFresh
        let store ← dstrStore n bind rp tgt none a
        pure (prep ++ [dstrLet a (some (dstrCall "rest" (.ident src :: keys)))] ++ store)
    pure (.expr (dstrCall "req" [.ident src]) :: body ++ restS)
  | n + 1, bind, src, p => do
    let (prep, tgt) ← dstrTarget p
    pure (prep ++ (← dstrStore n bind p tgt none src))
end

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
    -- `[a, b] = await e` (§13.15.5.2): the value's yields first; a pattern with yields of its
    -- own is lowered to statements (`dstrLower`)
    | .assignPat p v =>
      if !p.hasYield then pure (.assignPat p (← liftE n v)) else do
        -- the value into a temporary, then the pattern's steps as statements (`dstrLower`);
        -- the expression's value is the value assigned (§13.15.2)
        let v ← liftE n v
        let (k, acc) ← get
        let ((x, ss), k') := (do let x ← dstrFresh; pure (x, ← dstrLower 10000 none x p)).run k
        set (k', (acc.push (dstrLet x (some v))) ++ ss.toArray)
        pure (.ident x)
    | .update pre inc t => pure (.update pre inc (← liftE n t))
    | .superCall args => pure (.superCall (← liftL n args))
    | .superIndex k => pure (.superIndex (← liftE n k))
    | .tagged tag c r subs => do
      let tag ← liftE n tag
      pure (.tagged tag c r (← liftL n subs))
    | .logAssign op t v =>
      if !v.hasYield then
        pure (.logAssign op (← liftE n t) v)
      else
        -- `t ||= await v` (§13.15.2): the target is read once; the value and the store run
        -- only when the test asks for them, as for `logical`
        let t ← match t with
          | .member o k => do
            let o ← liftE n o
            pure (Expr.member (← if isLiteral o then pure o else liftTemp o) k)
          | .index o k => do
            let o ← liftE n o
            let o ← if isLiteral o then pure o else liftTemp o
            let k ← liftE n k
            pure (Expr.index o (← if isLiteral k then pure k else liftTemp k))
          | _ => pure t
        let (k, acc) ← get
        let x := liftName k
        set (k + 1, acc)
        let (v', pre) ← liftBranch n v
        let test : Expr := match op with
          | .and => .ident x
          | .or => .unary .not (.ident x)
          | .coalesce => .binary .seq (.binary .eq (.ident x) .null) (.bool true)
        liftPush (.decl .letK [Decl.mk (.id x) (some t)])
        liftPush (.ifS test (.block (pre ++ [.expr (.assign none (.ident x) (.assign none t v'))])) none)
        pure (.ident x)
    | .object ps => pure (.object (← liftP n ps))
    | .classE (.mk name h ctor ms) =>
      -- ClassDefinitionEvaluation (§15.7.14) evaluates the heritage, then the computed keys in
      -- order: their `yield`s go first, each key before them held in a temporary
      let h ← match h with
        | some x => do
          let x ← liftE n x
          let x ← if ms.any Member.keyHasYield && !isLiteral x then liftTemp x else pure x
          pure (some x)
        | none => pure none
      pure (.classE (.mk name h ctor (← liftMembers n ms)))
    | _ => pure e
termination_by structural n _ => n

/-- The computed keys of class members, lifted in order (`liftE`'s `classE`). -/
def liftMembers : Nat → List Member → Lift (List Member)
  | 0, ms => pure ms
  | _ + 1, [] => pure []
  | n + 1, m :: ms => do
    let m ← match m with
      | .mk st kind (.computed k) f => do
        let k ← liftE n k
        let k ← if ms.any Member.keyHasYield && !isLiteral k then liftTemp k else pure k
        pure (Member.mk st kind (.computed k) f)
      | _ => pure m
    pure (m :: (← liftMembers n ms))
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
    let later := ps.any PropDef.hasYield
    let p ← match p with
      | .init (.lit k) v => do pure (PropDef.init (.lit k) (← liftE n v))
      | .init (.computed k) v => do
        -- the key, then the value (§13.2.5.5): a key before a `yield` is held in a temporary
        let k ← liftE n k
        let k ← if (v.hasYield || later) && !isLiteral k then liftTemp k else pure k
        let v ← liftE n v
        let v ← if later && !isLiteral v then liftTemp v else pure v
        pure (PropDef.init (.computed k) v)
      | .getter (.computed k) f => do
        let k ← liftE n k
        pure (PropDef.getter (.computed (← if later && !isLiteral k then liftTemp k else pure k)) f)
      | .setter (.computed k) f => do
        let k ← liftE n k
        pure (PropDef.setter (.computed (← if later && !isLiteral k then liftTemp k else pure k)) f)
      | .spread v => do pure (PropDef.spread (← liftE n v))
      | _ => pure p
    pure (p :: (← liftP n ps))
termination_by structural n _ => n
end

/-- A `let`, `const` or `var` declaration whose pattern holds a `yield` (`let [a = yield] = v`):
the value into a temporary, then the pattern's steps (`dstrLower`); a `var` name is assigned,
a `let` or `const` name is initialised by a declaration at its step. -/
def liftDecl (seed : Nat) (k : DeclKind) (p : Pat) (e : Expr) : List Stmt :=
  let bind : Option DeclKind := match k with | .var => none | k => some k
  let ((x, ss), _) := (do let x ← dstrFresh; pure (x, ← dstrLower 10000 bind x p)).run seed
  dstrLet x (some e) :: ss

/-- A `for`-`in` or `for`-`of` whose target holds a `yield` (`for ([x = yield] of xs)`): each
value into a temporary of the loop, then the target as the body's first statement, a
destructuring assignment or declaration that `liftE` and `liftDecl` lower. A `let` or `const`
target is still a binding of each iteration (the body's block). -/
def forTargetTemp (k : Nat) (isOf : Bool) (kind : Option DeclKind) (target : Pat) (obj : Expr) (body : Stmt) : Stmt :=
  let t := s!"%ft{k}"
  let bind : Stmt := match kind, target with
    | some dk, _ => .decl dk [Decl.mk target (some (.ident t))]
    | none, .target e => .expr (.assign none e (.ident t))
    | none, .id x => .expr (.assign none (.ident x) (.ident t))
    | none, p => .expr (.assignPat p (.ident t))
  let body' : Stmt := .block [bind, body]
  if isOf then .forOf (some .letK) (.id t) obj body' else .forIn (some .letK) (.id t) obj body'

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
  | .classDecl x c =>
    match run (.classE c) with
    | (.classE c', acc) => if acc.isEmpty then none else some (acc.toList ++ [.classDecl x c'])
    | _ => none
  | .ret (some e) => wrap e (fun x => .ret (some x))
  | .throwS e => wrap e .throwS
  | .decl k [Decl.mk p (some e)] =>
    if p.hasYield then some (liftDecl seed k p e)
    else wrap e (fun x => .decl k [Decl.mk p (some x)])
  -- several declarators: one statement each, in order (each then runs or lifts on its own)
  | .decl k (d :: d' :: ds) => some ((d :: d' :: ds).map fun d => .decl k [d])
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

/-- The source text of a primitive JSON value (for a string, its quoted form; the parser
keeps no escapes). -/
def jsonSrcOf : L4Factoidal.JSON.Json → Option String
  | .null => some "null"
  | .bool b => some (if b then "true" else "false")
  | .number t => some t
  | .string s => some ("\"" ++ s.foldl (fun acc c => acc ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
      | c => String.singleton c) "" ++ "\"")
  | _ => none

/-- The primitives of a parsed JSON text and the places `jsonToValue` put them: (holder,
key, source text, value), for the reviver's context (proposal-json-parse-with-source). -/
def jsonSources : Nat → Nat → String → L4Factoidal.JSON.Json → Value → M (Array (Nat × String × String × Value))
  | 0, _, _, _, _ => pure #[]
  | fuel + 1, holder, key, j, v => do
    match jsonSrcOf j with
    | some t => pure #[(holder, key, t, v)]
    | none =>
      let .obj vid := v | pure #[]
      let o ← getObj vid
      match j, o.kind with
      | .array xs, .array es =>
        let mut out := #[]
        let mut i := 0
        for x in xs do
          if h : i < es.size then out := out ++ (← jsonSources fuel vid (toString i) x es[i])
          i := i + 1
        pure out
      | .object kvs, _ =>
        let mut out := #[]
        for (k, jv) in kvs do
          match o.getOwn (strKey k) with
          | some (.data cv ..) => out := out ++ (← jsonSources fuel vid (strKey k) jv cv)
          | _ => pure ()
        pure out
      | _, _ => pure #[]

def bufferBytes (o : Obj) : ByteArray :=
  match o.kind with | .buffer b => b | _ => ByteArray.empty

def elemSize (ty : Nat) : Nat := (typedNames[ty]?.map (·.2)).getD 1

/-- `elemSize` by a match: no read of the table and no `Option` for each element access. -/
def elemSizeFast (ty : Nat) : Nat :=
  match ty with
  | 3 | 4 | 11 => 2
  | 5 | 6 | 7 => 4
  | 8 | 9 | 10 => 8
  | _ => 1

/-- **Kind: refinement.** `elemSizeFast` is `elemSize` for every type tag (those past the table
included). -/
@[csimp] theorem elemSize_eq_fast : elemSize = elemSizeFast := by
  funext ty
  match ty with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rfl
  | n + 12 =>
    have h : typedNames[n + 12]? = none := Array.getElem?_eq_none (by show 12 ≤ n + 12; omega)
    unfold elemSize; rw [h]; rfl

#print axioms elemSize_eq_fast

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

/-- Write `bs` into buffer `buf` at byte `at_`, when it fits (`typedWriteV` for many elements
at once). -/
def typedWriteAll (buf at_ : Nat) (bs : ByteArray) : M Unit :=
  modifyObj buf fun bo => match bo.kind with
    | .buffer bytes =>
      if at_ + bs.size ≤ bytes.size then
        let bo := { bo with kind := .buffer ByteArray.empty }
        { bo with kind := .buffer (bs.copySlice 0 bytes at_ bs.size) }
      else bo
    | _ => bo

/-- The hidden slots of an ArrayBuffer: its maximum length (resizable), whether it is
detached, whether it is a SharedArrayBuffer. -/
def bufMaxKey : String := privKey "%ArrayBufferMaxByteLength"
/-- A DataView made without a length on a resizable buffer: its length follows the buffer's. -/
def dataViewAutoKey : String := privKey "%DataViewLengthTracking"
def bufDetachedKey : String := privKey "%ArrayBufferDetached"
def bufSharedKey : String := privKey "%ArrayBufferShared"

def hiddenNum (o : Obj) (k : String) : Option Nat :=
  match o.props.get? k with
  | some (.data (.num x) ..) => some x.toUInt64.toNat
  | _ => none

/-- The hidden slots of an `Iterator.zip` helper: the mode (0 shortest, 1 longest, 2 strict),
the padding (an Array), the keys of `zipKeyed` (an Array, or undefined), the open count. -/
def zipModeKey : String := privKey "%ZipMode"
def zipPadKey : String := privKey "%ZipPadding"
def zipKeysKey : String := privKey "%ZipKeys"
def zipOpenKey : String := privKey "%ZipOpen"

/-- The hidden slots of a DisposableStack: its resources (an Array of value, method pairs) and
whether it is disposed. -/
def dsStackKey : String := privKey "%DisposableResourceStack"
def dsStateKey : String := privKey "%DisposableState"
/-- The mark of an AsyncDisposableStack (beside its stack and state), and on
%DisposableStack.prototype% the place of %AsyncDisposableStack.prototype%. -/
def adsKey : String := privKey "%AsyncDisposableStack"
/-- A RegExp made by a subclass constructor: its [[LegacyFeaturesEnabled]] is false. -/
def regexpNoLegacyKey : String := privKey "%RegExpNoLegacy"
/-- The record of one DisposeResources run of disposeAsync: the error so far, needsAwait,
hasAwaited. -/
def adsErrKey : String := privKey "%AdsError"
def adsNeedKey : String := privKey "%AdsNeedsAwait"
def adsDoneKey : String := privKey "%AdsHasAwaited"

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
  detached || (if len == autoLen then off > size else off + len * elem > size)

/-- TypedArrayLength (§10.4.5.12) of a view at byte offset `off` with [[ArrayLength]] `len`
(`autoLen`: length-tracking) over a buffer of `size` bytes: 0 when it is out of bounds, else
the fixed length, or as many whole elements as fit after the offset. -/
def typedLenOf (detached : Bool) (off len elem size : Nat) : Nat :=
  if typedOob detached off len elem size then 0
  else if len == autoLen then (size - off) / elem else len

/-- The element count of a typed array as its buffer now is (§10.4.5.12
TypedArrayLength): 0 when the buffer is detached or too small for the view; for a
length-tracking view (`autoLen`), the elements that fit in the buffer now. -/
@[inline] def liveLen (ty buf off len : Nat) : M Nat := do
  let bo ← getObj buf
  pure (typedLenOf (isDetached bo) off len (elemSize ty) (bufferBytes bo).size)

/-- Element `i` of the typed array `id` as its buffer now is (§10.4.5.15 TypedArrayGetElement:
`undefined` past the live length); `Value.hole` when `id` is not a typed array. A pure function
of the heap: no result cell, no key. -/
def typedElemAt (h : HeapOf H) (id i : Nat) : Value :=
  match (h.obj id).kind with
  | .typed ty b off len =>
    let bo := h.obj b
    let live := typedLenOf (isDetached bo) off len (elemSize ty) (bufferBytes bo).size
    if i < live then typedRead ty (bufferBytes bo) (off + i * elemSize ty) else .undef
  | _ => .hole

/-- `o[x]` for a Number `x` when `o` is a typed array and `x` an array index: the element, with
no key string (`getV` would make the string of `x`, parse it back into the index and read the
same element: `getV_typedElemNum` in `JS/Theorems.lean`). `Value.hole` otherwise: the caller
takes the general path. -/
@[inline] def typedElemNum (h : HeapOf H) (id : Nat) (x : Float) : Value :=
  let i := numIndex x
  if i < noIndex then typedElemAt h id i else .hole

/-- `o[x] = v` for a Number `x` and a Number `v`, when `o` is a typed array of a Number element
type, `x` is an array index and no undo log covers `o`: the element is written (or the write is
dropped past the live length, §10.4.5.16 TypedArraySetElement) with no key string, and the answer
is `true`. `false` otherwise, with nothing done: the caller takes the general path. `putV` on the
key of `x` does the same write (`typedSetNum_refines` in `JS/Theorems.lean`). The undo log is
part of the test because `putV` notes the object in it before it finds no plain property to
overwrite. Called after the Array path (`setElem`) has declined, so an Array write pays nothing. -/
@[inline] def typedSetNum (id : Nat) (x : Float) (v : Value) : M Bool := do
  let h ← get
  match (h.obj id).kind, v with
  | .typed ty b off len, .num _ =>
    let i := numIndex x
    if i < noIndex && !typedIsBig ty && h.undoObjs.base ≤ id then
      let bo := h.obj b
      let live := typedLenOf (isDetached bo) off len (elemSize ty) (bufferBytes bo).size
      if i < live then typedWriteV ty b off i v
      pure true
    else pure false
  | _, _ => pure false

/-- The %TypedArray%.prototype methods that validate the typed array and then take the steps
of the Array.prototype method of the same name (`NativeX.typedGeneric`): name, length. -/
def typedGenericNames : Array (String × Nat) :=
  #[("forEach", 1), ("join", 1), ("indexOf", 1), ("includes", 1), ("every", 1), ("some", 1), ("reduce", 1),
    ("find", 1), ("findIndex", 1), ("values", 0), ("keys", 0), ("entries", 0)]

/-- The key of the private name `k` where the scope `env` sees it (§9.2.1.2
ResolvePrivateIdentifier): each evaluation of a class binds its private names to keys of their
own in the class scope (`evalClass`), so two classes, or two evaluations of one class, never
share a private element. Any other key is itself. -/
def privRk (env : Nat) (k : String) : M String := do
  if !isPrivKey k then return k
  let h ← get
  match h.findEnv k 100000 env with
  | some e => match (h.envs.getD e default).get? k with
    | some b => match b.v with
      | .str s => pure s
      | _ => pure k
    | none => pure k
  | none => pure k

/-- The first character of a private name's key (`privKey`). -/
def privMark : Char := Char.ofNat 0x10FFFE

/-- An entry of a class constructor's `fields` that is a private method (`m`), getter (`g`) or
setter (`s`) of its instances, keyed by the private name's key `k`: two private marks and the
tag, which no field's key starts with (a private name is an identifier, a String key never
starts with the mark: `strKey`). -/
def privElemKey (tag : Char) (k : String) : String :=
  String.singleton privMark ++ String.singleton privMark ++ String.singleton tag ++ k

/-- The tag and private name of a `privElemKey` entry. -/
def privElemOf (ek : String) : Option (Char × String) :=
  if ek.front != privMark then none else
  let r := (ek.drop 1).toString
  if r.front != privMark then none else
  some ((r.drop 1).toString.front, (r.drop 2).toString)

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

/-- The hidden mark of an array whose `join` is running: joining it again from inside (an array
that holds itself, directly or through others) would recurse without end. -/
def joiningKey : String := privKey "%Joining"

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
  -- a script's source is for `classicScriptHost` alone: it never becomes a value
  | .script _ _ => pure .undef
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
      | .typed ty b off len => pure (.bytes ((bufferBytes (← getObj b)).extract off (off + (← liveLen ty b off len) * elemSize ty)))
      | _ => pure (.val a)
    | _ => pure (.val a)
  match st with
  | none => throwErr .type "this realm has no host"
  | some st =>
    let (st, ans) := call st k hargs left
    modify fun h => { h with host := some st }
    hostAnswer args ans


/-- The number of `HeapOf.hostCall` that answers a classic script's source for the engine to run
(`HostAns.script`; `Native.classicScriptHost`). No native the realm holds has this number. -/
def hostScriptId : Nat := 1000001

/-- The source the host holds for `key` and whether its errors are muted (`none`: the host
has none). The answer stays here: it is not made a value of the realm. -/
def hostScript (key : Value) : M (Option (String × Bool)) := do
  let (st, call, left) ← modifyGet fun h => ((h.host, h.hostCall, h.steps.toNat), { h with host := none })
  match st with
  | none => pure none
  | some st =>
    let (st, ans) := call st hostScriptId #[.val key] left
    modify fun h => { h with host := some st }
    match ans with
    | .script src muted => pure (some (src, muted))
    | _ => pure none

/-- The host's clock in ns (0 with no host). -/
def hostNowNs : M Float := do
  if (← get).host.isNone then return 0
  match ← callHost hostClockId #[] with
  | .num x => pure x
  | _ => pure 0

/-- AdvanceStringIndex (§22.2.7.3): past a surrogate pair at once when `unicode`. -/
def advanceIndex (s : String) (i : Nat) (unicode : Bool) : Nat :=
  if !unicode then i + 1 else
  match Str.unitAt? s i, Str.unitAt? s (i + 1) with
  | some a, some b => if 0xD800 ≤ a && a ≤ 0xDBFF && 0xDC00 ≤ b && b ≤ 0xDFFF then i + 2 else i + 1
  | _, _ => i + 1

/-- The group names a replacement template asks for (`$<name>`), in order. -/
def templateNames (tmpl : String) : List String := Id.run do
  let t := tmpl.toList.toArray
  let mut out : List String := []
  let mut i := 0
  for _ in [0:t.size + 1] do
    if i + 1 ≥ t.size then break
    if t[i]! == '$' && t[i+1]! == '$' then i := i + 2; continue
    if t[i]! == '$' && t[i+1]! == '<' then
      match (t.extract (i + 2) t.size).findIdx? (· == '>') with
      | some k => out := out ++ [String.ofList (t.extract (i + 2) (i + 2 + k)).toList]; i := i + 3 + k
      | none => i := i + 2
    else i := i + 1
  out

/-- GetSubstitution (§22.1.3.19.1) with the captures as strings (`none` for undefined) and the
named groups' values (`none` when the match has no `groups`). Indices are UTF-16 units. -/
def getSubstitutionG (tmpl matched str : String) (position : Nat) (caps : Array (Option String))
    (named : Option (List (String × String))) : String := Id.run do
  let t := tmpl.toList.toArray
  let len := Str.jsLength str
  let tail := position + Str.jsLength matched
  let m := caps.size
  let cap (k : Nat) : String := (caps.getD (k - 1) none).getD ""
  let mut out := ""
  let mut i := 0
  for _ in [0:t.size + 1] do
    if i ≥ t.size then break
    let c := t[i]!
    if c != '$' || i + 1 ≥ t.size then
      out := out.push c; i := i + 1; continue
    let d := t[i+1]!
    if d == '$' then out := out.push '$'; i := i + 2
    else if d == '&' then out := out ++ matched; i := i + 2
    else if d == '`' then out := out ++ Str.sliceUnits str 0 (min position len); i := i + 2
    else if d == '\'' then out := out ++ (if tail ≥ len then "" else Str.sliceUnits str tail len); i := i + 2
    else if d.isDigit then
      let n1 := d.toNat - 48
      let n2 := if i + 2 < t.size && t[i+2]!.isDigit then n1 * 10 + (t[i+2]!.toNat - 48) else 0
      if i + 2 < t.size && t[i+2]!.isDigit && 1 ≤ n2 && n2 ≤ m then
        out := out ++ cap n2; i := i + 3
      else if 1 ≤ n1 && n1 ≤ m then
        out := out ++ cap n1; i := i + 2
      else
        out := out.push '$'; i := i + 1
    else if d == '<' then
      match named with
      | none => out := out ++ "$<"; i := i + 2
      | some tbl =>
        match (t.extract (i + 2) t.size).findIdx? (· == '>') with
        | none => out := out ++ "$<"; i := i + 2
        | some k =>
          let nm := String.ofList (t.extract (i + 2) (i + 2 + k)).toList
          out := out ++ ((tbl.lookup nm).getD ""); i := i + 3 + k
    else
      out := out.push '$'; i := i + 1
  out

#guard getSubstitutionG "[$1|$2|$&|$`|$'|$$|$0|$10|$<x>]" "bc" "abcd" 1 #[some "b", none] none == "[b||bc|a|d|$|$0|b0|$<x>]"
#guard getSubstitutionG "$<x>-$<y" "b" "abc" 1 #[] (some [("x", "X")]) == "X-$<y"
#guard templateNames "$<a>$$<b>$<c>" == ["a", "c"]
#guard advanceIndex "a😀" 1 true == 3 && advanceIndex "a😀" 1 false == 2

/-- CanonicalNumericIndexString (§7.1.21): the number a property key names when the key is that
number's string ("-0" names -0). -/
def canonicalNumericIndex (k : String) : Option Float :=
  if k == "-0" then some (-0.0) else
  if k.isEmpty || isSymKey k then none else
  let x := strToNumber k
  if numToString x == k then some x else none

#guard canonicalNumericIndex "1" == some 1 && canonicalNumericIndex "1.5" == some 1.5
#guard (canonicalNumericIndex "01").isNone && (canonicalNumericIndex "Infinity").isSome && (canonicalNumericIndex "x").isNone

/-- IsArray (§7.2.2): a Proxy answers for its target; a revoked one throws. -/
def isArrayDeep : Nat → Value → M Bool
  | 0, _ => pure false
  | k + 1, .obj id => do
    let o ← getObj id
    match o.kind with
    | .proxy t hnd =>
      if let .null := hnd then throwErr .type "Cannot perform 'IsArray' on a proxy that has been revoked"
      isArrayDeep k t
    | _ => pure o.isArray
  | _ + 1, _ => pure false

/-- Where %RegExp.prototype% keeps %RegExpStringIteratorPrototype% (§22.2.9.2), and where a RegExp
String Iterator keeps its string: private-name keys, which no script can name. A RegExp String
Iterator is a `Kind.iter` of mode 20 + 1 (global) + 2 (full Unicode) over its matcher. -/
def rsiProtoKey : String := privKey " regexpStringIteratorPrototype"
def rsiStringKey : String := privKey " iteratedString"

/-- A RegExp whose methods may take the built-in fast paths: %RegExp.prototype% is its
prototype, `lastIndex` its only own property, and `exec` and `flags` there are the built-ins
(and, for `split`, `constructor` is %RegExp% with no own `@@species`). Anything else takes the
general steps, which call what the script put there. -/
def regexpPristine (rx : Value) (split : Bool) : M Bool := do
  let .obj id := rx | return false
  let o ← getObj id
  let .regexp .. := o.kind | return false
  let r ← realm
  let .obj p := o.proto | return false
  if p != r.regexpProto || o.props.size > 1 then return false
  let po ← getObj p
  let isNative (v : Value) (nt : Native) : M Bool := do
    match v with
    | .obj f => pure (match (← getObj f).kind with | .native x => x == nt | _ => false)
    | _ => pure false
  let execOk ← match po.props.get? "exec" with
    | some (.data v ..) => isNative v .regexpExec
    | _ => pure false
  let flagsOk ← match po.props.get? "flags" with
    | some (.acc g ..) => isNative g (.regexpGetter 1)
    | _ => pure false
  if !(execOk && flagsOk) then return false
  if !split then return true
  match po.props.get? "constructor" with
  | some (.data (.obj c) ..) =>
    let co ← getObj c
    pure ((match co.kind with | .native .regexpCtor => true | _ => false) && (co.props.get? (symKey 7)).isNone)
  | _ => pure false

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
        -- of groups that share the name, the one that took part in the match
        let gs := names.filter (·.1 == name)
        match gs.find? (fun (_, g) => (caps[g-1]?.join).isSome) with
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

/-- The compiled code of a call's callee: the `Option` of its function record, or `none`. -/
@[inline] def vmCallCode (h : HeapOf H) (fv : Value) : Option Code :=
  match fv with
  | .obj id => match (h.obj id).kind with
    | .closure fd _ _ _ _ _ => fd.info.code.get
    | _ => none
  | _ => none

/-- The environment a closure captured (0 for any other value). -/
@[inline] def vmCallEnv (h : HeapOf H) (fv : Value) : Nat :=
  match fv with
  | .obj id => match (h.obj id).kind with
    | .closure _ cenv _ _ _ _ => cenv
    | _ => 0
  | _ => 0

/-- The `this` a closure captured (`undefined` for any other value). -/
@[inline] def vmCallThis (h : HeapOf H) (fv : Value) : Value :=
  match fv with
  | .obj id => match (h.obj id).kind with
    | .closure _ _ capThis _ _ _ => capThis
    | _ => .undef
  | _ => .undef

/-- `tryCatch` for the completions of the language: the handler sees thrown values and the
evaluator's own `Abrupt` values, but never a halt (out of fuel, out of steps, a full heap, a
failed check): a halt is an interrupt and passes through every handler unchanged. Optional
chaining's `shortSignal` is a halt too, and only `Expr.chain` (with a plain `tryCatch`) stops it.

This makes the evaluator monotone in its fuel: a run that ends at fuel `n` with anything but
`halt "fuel"` ends the same way at every larger fuel (`JS/FuelMono.lean`). Before it, a handler
that dropped every completion (IteratorClose after a throw) also dropped an out-of-fuel halt in
the iterator's `return`, and the run went on with a different result. -/
@[inline] def catchJS {α : Type} (x : M α) (k : Abrupt → M α) : M α :=
  tryCatch x fun a => match a with
    | .halt w => throw (.halt w)
    | a => k a

/-- Compiled functions may nest this deep (they do not use the host's stack). -/
def vmMaxDepth : Nat := 20000

@[inline] def vmStash (regs : Array Value) (fregs : FloatArray) (top : Nat) : M Unit :=
  modify fun h => { h with vmRegs := regs, vmF := fregs, vmTop := top }

/-- Take the registers back out of the heap, for the caller to own. -/
@[inline] def vmTake : M (Array Value × FloatArray) :=
  modifyGet fun h => ((h.vmRegs, h.vmF), { h with vmRegs := #[], vmF := .empty })

/-- What `vmStash regs fregs top` followed by `vmTake` leaves in the heap, when the caller keeps
the registers: one update of the record, with no array moved in and out
(`vmStash_pure_vmTake` in `JS/Theorems.lean`). -/
@[inline] def vmSettle (top : Nat) : M Unit :=
  modify fun h => { h with vmRegs := #[], vmF := .empty, vmTop := top }

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

/-- The elements of an array value as they are (absent ones included); empty otherwise. -/
def rawElems (v : Value) : M (Array Value) := do
  match v with
  | .obj id => match (← getObj id).kind with
    | .array es => pure es
    | _ => pure #[]
  | _ => pure #[]

/-! ## The built-in dispatchers, outside the evaluator's mutual block

`callNative`, `extraNative` and `moreNative` (about 4,000 lines) call back into the evaluator
through one dispatcher, `CoreFn`: a request (`CoreOp`, one constructor per function of the block
they use) and its answer (`CoreOp.Res`). Out of the block they are plain definitions, so Lean
makes no structural-recursion equation lemmas for them (those of the block took minutes and
gigabytes), and a property of the block is proved for them once, from the same property of the
dispatcher (`JS/FuelMono.lean`). Inside the block, `coreRun n` answers requests at fuel `n`.

`callNative` and `moreNative` are each a `match id with` over calls of one definition per family
of built-ins (`callNativeObjectStatic`, `moreNativeTyped`, ...: `tools/natives-split.py`), so
that a property is proved family by family (a few hundred lines each; the two as single
definitions of 1,500 and 2,100 lines were beyond a 6 GB proof check). A new built-in is an arm
in its family's definition and an arm of the dispatcher that calls the family; a new family is a
definition before the dispatcher, with the same parameters, and `tools/fuelmono-natives.py`
writes its fuel-monotonicity lemma (`JS/FuelMonoNatives_*.lean`). -/

/-- A call from a built-in into the evaluator. -/
inductive CoreOp (H : Type) where
  | getV (a0 : Value) (a1 : String)
  | proxyTrap (a0 : Value) (a1 : String)
  | hasProp (a0 : Nat) (a1 : String)
  | getRecv (a0 : Nat) (a1 : String) (a2 : Value)
  | ownKeysOf (a0 : Nat)
  | ownDesc (a0 : Nat) (a1 : String)
  | putV (a0 : Value) (a1 : String) (a2 : Value) (a3 : Bool)
  | toPrim (a0 : Value) (a1 : String)
  | tryMethods (a0 : Value) (a1 : List String)
  | toNum (a0 : Value)
  | typedConv (a0 : Nat) (a1 : Value)
  | toStr (a0 : Value)
  | toKey (a0 : Value)
  | toObj (a0 : Value)
  | instOf (a0 : Value) (a1 : Value)
  | callV (a0 : Value) (a1 : Value) (a2 : Array Value)
  | construct (a0 : Value) (a1 : Array Value) (a2 : Value)
  | evalStmts (a0 : Ctx) (a1 : List Stmt)
  | evalExpr (a0 : Ctx) (a1 : Expr)
  | getIterator (a0 : Value)
  | iterStep (a0 : Value)
  | iterClose (a0 : Value)
  | iterToArray (a0 : Value) (a1 : Array Value)
  | iterCloseAbrupt (a0 : Value) (a1 : Abrupt)
  | directEval (a0 : Ctx) (a1 : Value)
  | genRun (a0 : List GFrame) (a1 : GInput)
  | asyncStep (a0 : Nat) (a1 : GInput)
  | promiseResolve (a0 : Value)
  | resolvePromise (a0 : Nat) (a1 : Value)
  | rejectPromise (a0 : Nat) (a1 : Value)
  | performThen (a0 : Nat) (a1 : Value) (a2 : Value) (a3 : Value)
  | iterResult (a0 : Value) (a1 : Bool)
  | agenDrain (a0 : Nat)
  | agenRun (a0 : Nat) (a1 : List GFrame) (a2 : GInput)
  | callNative (a0 : Native) (a1 : Value) (a2 : Array Value) (a3 : Option Value)
  | genericPush (a0 : Value) (a1 : Array Value)
  | arraySpliceGeneric (a0 : Value) (a1 : Array Value)
  | deleteOrThrow (a0 : Value) (a1 : String)
  | jsonRevive (a0 : Array (Nat × String × String × Value)) (a1 : Value) (a2 : Value) (a3 : String) (a4 : Nat)
  | arrayGeneric (a0 : Native) (a1 : Value) (a2 : Array Value)
  | speciesFrom (a0 : Value) (a1 : Nat)
  | speciesFill (a0 : Value) (a1 : Array Value) (a2 : Option Nat)
  | elemsOf (a0 : Value)
  | elemAt (a0 : Nat) (a1 : Nat) (a2 : Bool)
  | iterArray (a0 : Native) (a1 : Value) (a2 : Value) (a3 : Value) (a4 : Nat) (a5 : Nat) (a6 : Array Value)
  | reduceArray (a0 : Value) (a1 : Value) (a2 : Nat) (a3 : Nat) (a4 : Value)
  | arrayLikeLength (a0 : Value)
  | mergeSort (a0 : Value) (a1 : List Value)
  | toPropDesc (a0 : Value)
  | defineOwnProp (a0 : Nat) (a1 : String) (a2 : Desc)
  | defineFromDescriptor (a0 : Nat) (a1 : String) (a2 : Value)
  | jsonSer (a0 : Value) (a1 : Option (Array String)) (a2 : String) (a3 : String) (a4 : Array Nat) (a5 : Value) (a6 : String)
  | regexExec (a0 : Value) (a1 : String)
  | regExpExecG (a0 : Value) (a1 : String)
  | speciesCtor (a0 : Value) (a1 : Value)
  | matchArray (a0 : Re.Compiled) (a1 : String) (a2 : Array (Option (Nat × Nat)))
  | stringSymDispatch (a0 : Native) (a1 : Value) (a2 : Array Value)
  | regexpSymbol (a0 : Nat) (a1 : Value) (a2 : Array Value)
  | stringOrMath (a0 : Native) (a1 : Value) (a2 : Array Value)

/-- The type of the answer to a request. -/
def CoreOp.Res : CoreOp H → Type
  | .getV _ _ => Value
  | .proxyTrap _ _ => (Option Value)
  | .hasProp _ _ => Bool
  | .getRecv _ _ _ => Value
  | .ownKeysOf _ => (Array String)
  | .ownDesc _ _ => (Option PropV)
  | .putV _ _ _ _ => Unit
  | .toPrim _ _ => Value
  | .tryMethods _ _ => Value
  | .toNum _ => Float
  | .typedConv _ _ => Value
  | .toStr _ => String
  | .toKey _ => String
  | .toObj _ => Nat
  | .instOf _ _ => Bool
  | .callV _ _ _ => Value
  | .construct _ _ _ => Value
  | .evalStmts _ _ => Compl
  | .evalExpr _ _ => Value
  | .getIterator _ => Value
  | .iterStep _ => (Option Value)
  | .iterClose _ => Unit
  | .iterToArray _ _ => (Array Value)
  | .iterCloseAbrupt _ _ => Unit
  | .directEval _ _ => Value
  | .genRun _ _ => GOut
  | .asyncStep _ _ => Unit
  | .promiseResolve _ => Nat
  | .resolvePromise _ _ => Unit
  | .rejectPromise _ _ => Unit
  | .performThen _ _ _ _ => Unit
  | .iterResult _ _ => Value
  | .agenDrain _ => Unit
  | .agenRun _ _ _ => Unit
  | .callNative _ _ _ _ => Value
  | .genericPush _ _ => Value
  | .arraySpliceGeneric _ _ => Value
  | .deleteOrThrow _ _ => Unit
  | .jsonRevive _ _ _ _ _ => Value
  | .arrayGeneric _ _ _ => Value
  | .speciesFrom _ _ => (Option Value)
  | .speciesFill _ _ _ => Value
  | .elemsOf _ => (Array Value)
  | .elemAt _ _ _ => (Option Value)
  | .iterArray _ _ _ _ _ _ _ => Value
  | .reduceArray _ _ _ _ _ => Value
  | .arrayLikeLength _ => Nat
  | .mergeSort _ _ => (List Value)
  | .toPropDesc _ => Desc
  | .defineOwnProp _ _ _ => Bool
  | .defineFromDescriptor _ _ _ => Unit
  | .jsonSer _ _ _ _ _ _ _ => (Option String)
  | .regexExec _ _ => (Option (Array (Option (Nat × Nat))))
  | .regExpExecG _ _ => Value
  | .speciesCtor _ _ => Value
  | .matchArray _ _ _ => Value
  | .stringSymDispatch _ _ _ => (Option Value)
  | .regexpSymbol _ _ _ => Value
  | .stringOrMath _ _ _ => Value

/-- Requests answered in the monad: the evaluator, at some fuel, as built-ins see it. -/
abbrev CoreFn (H : Type) := (op : CoreOp H) → JSM H op.Res

@[reducible] def CoreFn.getV (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H Value := c (.getV a0 a1)
@[reducible] def CoreFn.proxyTrap (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H (Option Value) := c (.proxyTrap a0 a1)
@[reducible] def CoreFn.hasProp (c : CoreFn H) (a0 : Nat) (a1 : String) : JSM H Bool := c (.hasProp a0 a1)
@[reducible] def CoreFn.getRecv (c : CoreFn H) (a0 : Nat) (a1 : String) (a2 : Value) : JSM H Value := c (.getRecv a0 a1 a2)
@[reducible] def CoreFn.ownKeysOf (c : CoreFn H) (a0 : Nat) : JSM H (Array String) := c (.ownKeysOf a0)
@[reducible] def CoreFn.ownDesc (c : CoreFn H) (a0 : Nat) (a1 : String) : JSM H (Option PropV) := c (.ownDesc a0 a1)
@[reducible] def CoreFn.putV (c : CoreFn H) (a0 : Value) (a1 : String) (a2 : Value) (a3 : Bool) : JSM H Unit := c (.putV a0 a1 a2 a3)
@[reducible] def CoreFn.toPrim (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H Value := c (.toPrim a0 a1)
@[reducible] def CoreFn.tryMethods (c : CoreFn H) (a0 : Value) (a1 : List String) : JSM H Value := c (.tryMethods a0 a1)
@[reducible] def CoreFn.toNum (c : CoreFn H) (a0 : Value) : JSM H Float := c (.toNum a0)
@[reducible] def CoreFn.typedConv (c : CoreFn H) (a0 : Nat) (a1 : Value) : JSM H Value := c (.typedConv a0 a1)
@[reducible] def CoreFn.toStr (c : CoreFn H) (a0 : Value) : JSM H String := c (.toStr a0)
@[reducible] def CoreFn.toKey (c : CoreFn H) (a0 : Value) : JSM H String := c (.toKey a0)
@[reducible] def CoreFn.toObj (c : CoreFn H) (a0 : Value) : JSM H Nat := c (.toObj a0)
@[reducible] def CoreFn.instOf (c : CoreFn H) (a0 : Value) (a1 : Value) : JSM H Bool := c (.instOf a0 a1)
@[reducible] def CoreFn.callV (c : CoreFn H) (a0 : Value) (a1 : Value) (a2 : Array Value) : JSM H Value := c (.callV a0 a1 a2)
@[reducible] def CoreFn.construct (c : CoreFn H) (a0 : Value) (a1 : Array Value) (a2 : Value) : JSM H Value := c (.construct a0 a1 a2)
@[reducible] def CoreFn.evalStmts (c : CoreFn H) (a0 : Ctx) (a1 : List Stmt) : JSM H Compl := c (.evalStmts a0 a1)
@[reducible] def CoreFn.evalExpr (c : CoreFn H) (a0 : Ctx) (a1 : Expr) : JSM H Value := c (.evalExpr a0 a1)
@[reducible] def CoreFn.getIterator (c : CoreFn H) (a0 : Value) : JSM H Value := c (.getIterator a0)
@[reducible] def CoreFn.iterStep (c : CoreFn H) (a0 : Value) : JSM H (Option Value) := c (.iterStep a0)
@[reducible] def CoreFn.iterClose (c : CoreFn H) (a0 : Value) : JSM H Unit := c (.iterClose a0)
@[reducible] def CoreFn.iterToArray (c : CoreFn H) (a0 : Value) (a1 : Array Value) : JSM H (Array Value) := c (.iterToArray a0 a1)
@[reducible] def CoreFn.iterCloseAbrupt (c : CoreFn H) (a0 : Value) (a1 : Abrupt) : JSM H Unit := c (.iterCloseAbrupt a0 a1)
@[reducible] def CoreFn.directEval (c : CoreFn H) (a0 : Ctx) (a1 : Value) : JSM H Value := c (.directEval a0 a1)
@[reducible] def CoreFn.genRun (c : CoreFn H) (a0 : List GFrame) (a1 : GInput) : JSM H GOut := c (.genRun a0 a1)
@[reducible] def CoreFn.asyncStep (c : CoreFn H) (a0 : Nat) (a1 : GInput) : JSM H Unit := c (.asyncStep a0 a1)
@[reducible] def CoreFn.promiseResolve (c : CoreFn H) (a0 : Value) : JSM H Nat := c (.promiseResolve a0)
@[reducible] def CoreFn.resolvePromise (c : CoreFn H) (a0 : Nat) (a1 : Value) : JSM H Unit := c (.resolvePromise a0 a1)
@[reducible] def CoreFn.rejectPromise (c : CoreFn H) (a0 : Nat) (a1 : Value) : JSM H Unit := c (.rejectPromise a0 a1)
@[reducible] def CoreFn.performThen (c : CoreFn H) (a0 : Nat) (a1 : Value) (a2 : Value) (a3 : Value) : JSM H Unit := c (.performThen a0 a1 a2 a3)
@[reducible] def CoreFn.iterResult (c : CoreFn H) (a0 : Value) (a1 : Bool) : JSM H Value := c (.iterResult a0 a1)
@[reducible] def CoreFn.agenDrain (c : CoreFn H) (a0 : Nat) : JSM H Unit := c (.agenDrain a0)
@[reducible] def CoreFn.agenRun (c : CoreFn H) (a0 : Nat) (a1 : List GFrame) (a2 : GInput) : JSM H Unit := c (.agenRun a0 a1 a2)
@[reducible] def CoreFn.callNative (c : CoreFn H) (a0 : Native) (a1 : Value) (a2 : Array Value) (a3 : Option Value) : JSM H Value := c (.callNative a0 a1 a2 a3)
@[reducible] def CoreFn.genericPush (c : CoreFn H) (a0 : Value) (a1 : Array Value) : JSM H Value := c (.genericPush a0 a1)
@[reducible] def CoreFn.arraySpliceGeneric (c : CoreFn H) (a0 : Value) (a1 : Array Value) : JSM H Value := c (.arraySpliceGeneric a0 a1)
@[reducible] def CoreFn.deleteOrThrow (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H Unit := c (.deleteOrThrow a0 a1)
@[reducible] def CoreFn.jsonRevive (c : CoreFn H) (a0 : Array (Nat × String × String × Value)) (a1 : Value) (a2 : Value) (a3 : String) (a4 : Nat) : JSM H Value := c (.jsonRevive a0 a1 a2 a3 a4)
@[reducible] def CoreFn.arrayGeneric (c : CoreFn H) (a0 : Native) (a1 : Value) (a2 : Array Value) : JSM H Value := c (.arrayGeneric a0 a1 a2)
@[reducible] def CoreFn.speciesFrom (c : CoreFn H) (a0 : Value) (a1 : Nat) : JSM H (Option Value) := c (.speciesFrom a0 a1)
@[reducible] def CoreFn.speciesFill (c : CoreFn H) (a0 : Value) (a1 : Array Value) (a2 : Option Nat) : JSM H Value := c (.speciesFill a0 a1 a2)
@[reducible] def CoreFn.elemsOf (c : CoreFn H) (a0 : Value) : JSM H (Array Value) := c (.elemsOf a0)
@[reducible] def CoreFn.elemAt (c : CoreFn H) (a0 : Nat) (a1 : Nat) (a2 : Bool) : JSM H (Option Value) := c (.elemAt a0 a1 a2)
@[reducible] def CoreFn.iterArray (c : CoreFn H) (a0 : Native) (a1 : Value) (a2 : Value) (a3 : Value) (a4 : Nat) (a5 : Nat) (a6 : Array Value) : JSM H Value := c (.iterArray a0 a1 a2 a3 a4 a5 a6)
@[reducible] def CoreFn.reduceArray (c : CoreFn H) (a0 : Value) (a1 : Value) (a2 : Nat) (a3 : Nat) (a4 : Value) : JSM H Value := c (.reduceArray a0 a1 a2 a3 a4)
@[reducible] def CoreFn.arrayLikeLength (c : CoreFn H) (a0 : Value) : JSM H Nat := c (.arrayLikeLength a0)
@[reducible] def CoreFn.mergeSort (c : CoreFn H) (a0 : Value) (a1 : List Value) : JSM H (List Value) := c (.mergeSort a0 a1)
@[reducible] def CoreFn.toPropDesc (c : CoreFn H) (a0 : Value) : JSM H Desc := c (.toPropDesc a0)
@[reducible] def CoreFn.defineOwnProp (c : CoreFn H) (a0 : Nat) (a1 : String) (a2 : Desc) : JSM H Bool := c (.defineOwnProp a0 a1 a2)
@[reducible] def CoreFn.defineFromDescriptor (c : CoreFn H) (a0 : Nat) (a1 : String) (a2 : Value) : JSM H Unit := c (.defineFromDescriptor a0 a1 a2)
@[reducible] def CoreFn.jsonSer (c : CoreFn H) (a0 : Value) (a1 : Option (Array String)) (a2 : String) (a3 : String) (a4 : Array Nat) (a5 : Value) (a6 : String) : JSM H (Option String) := c (.jsonSer a0 a1 a2 a3 a4 a5 a6)
@[reducible] def CoreFn.regexExec (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H (Option (Array (Option (Nat × Nat)))) := c (.regexExec a0 a1)
@[reducible] def CoreFn.regExpExecG (c : CoreFn H) (a0 : Value) (a1 : String) : JSM H Value := c (.regExpExecG a0 a1)
@[reducible] def CoreFn.speciesCtor (c : CoreFn H) (a0 : Value) (a1 : Value) : JSM H Value := c (.speciesCtor a0 a1)
@[reducible] def CoreFn.matchArray (c : CoreFn H) (a0 : Re.Compiled) (a1 : String) (a2 : Array (Option (Nat × Nat))) : JSM H Value := c (.matchArray a0 a1 a2)
@[reducible] def CoreFn.stringSymDispatch (c : CoreFn H) (a0 : Native) (a1 : Value) (a2 : Array Value) : JSM H (Option Value) := c (.stringSymDispatch a0 a1 a2)
@[reducible] def CoreFn.regexpSymbol (c : CoreFn H) (a0 : Nat) (a1 : Value) (a2 : Array Value) : JSM H Value := c (.regexpSymbol a0 a1 a2)
@[reducible] def CoreFn.stringOrMath (c : CoreFn H) (a0 : Native) (a1 : Value) (a2 : Array Value) : JSM H Value := c (.stringOrMath a0 a1 a2)

namespace Natives

/-- `f` on each value of the iterator, a step at a time (IteratorStepValue, §7.4.10), as
AddEntriesFromIterable (§24.1.1.2) and the Promise combinators (§27.2.4) walk theirs: an abrupt
completion of `f` closes the iterator (`iterCloseAbrupt`); one of the step itself does not.
Nothing is collected first, so an iterator that never ends costs one step a value and stops
at the step budget or the heap's size (`tick`), not when memory runs out. -/
def iterEach (core : CoreFn H) (it : Value) (f : (Value → M Unit)) : M Unit := do
    for _ in [0:iterEachMax] do
      tick
      match ← core.iterStep it with
      | none => return
      | some v =>
        match ← catchJS (do f v; pure none) (fun a => pure (some a)) with
        | some a => core.iterCloseAbrupt it a
        | none => pure ()
    throw (.halt "iteration limit")

/-- Built-ins of `moreNative`: ArrayBuffer `resize`, `transfer` and accessors, the DataView accessors, SharedArrayBuffer, and Atomics without waiting. `r` is the realm `moreNative` read. -/
def moreNativeBuffers (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
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
    let maxOption : M (Option Float) := do
      match a1 with
      | .obj _ => match ← core.getV a1 "maxByteLength" with
        | .undef => pure none
        | v => do
          let m := toIntegerOrInf (← core.toNum v)
          if m < 0 || m > 268435456 then throwErr .range "Invalid array buffer max length"
          pure (some m)
      | _ => pure none
    let resized (bytes : ByteArray) (l : Nat) : ByteArray :=
      if l ≤ bytes.size then bytes.extract 0 l else bytes ++ zeroBytes (l - bytes.size)
    match id with
    | (.x (.dataViewGetter which)) =>
      -- §25.3.4.1 buffer, .2 byteLength, .3 byteOffset: a TypeError on a detached or
      -- out-of-bounds view (but for `buffer`)
      let .obj oid := thisV | throwErr .type "DataView.prototype accessor called on a non-object"
      let o ← getObj oid
      let .dataView b off len := o.kind | throwErr .type "DataView.prototype accessor called on an incompatible receiver"
      if which == 0 then return .obj b
      let bo ← getObj b
      if isDetached bo then throwErr .type "The DataView's buffer is detached"
      let size := (bufferBytes bo).size
      let auto := hiddenFlag o dataViewAutoKey
      if off > size || (!auto && off + len > size) then throwErr .type "The DataView is out of the bounds of its buffer"
      pure (.num (Float.ofNat (if which == 2 then off else if auto then size - off else len)))
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
      let l := toIntegerOrInf (← core.toNum a0)
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
          let l := toIntegerOrInf (← core.toNum v)
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
      let len := toIntegerOrInf (← core.toNum a0)
      if len < 0 || len > 268435456 then throwErr .range "Invalid array buffer length"
      let max ← maxOption
      if let some m := max then
        if len > m then throwErr .range "byteLength exceeds maxByteLength"
      let p ← core.getV nt "prototype"
      let sid ← alloc { proto := (← protoOr p nt (·.sharedBufferProto)),
                        kind := .buffer (zeroBytes (len.toUInt64.toNat)) }
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
      let l := toIntegerOrInf (← core.toNum a0)
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
      let a := relIndex (toIntegerOrInf (← core.toNum a0)) bytes.size
      let b ← match a1 with
        | .undef => pure bytes.size
        | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) bytes.size)
      let sid ← alloc { proto := .obj r.sharedBufferProto, kind := .buffer (bytes.extract a (max a b)) }
      defineOwn sid bufSharedKey (.data (.bool true) true false false)
      pure (.obj sid)
    | (.x (.atomics op)) =>
      if op == 4 then
        let k := toIntegerOrInf (← core.toNum a0)
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
      -- ValidateAtomicAccess (§25.4.3.2): the length is taken before the index is converted
      let live ← liveLen ty b off len
      let idx := toIntegerOrInf (← core.toNum a1)
      if idx < 0 || idx > 9007199254740991 then throwErr .range "Invalid atomic access index"
      if idx ≥ Float.ofNat live then throwErr .range "Invalid atomic access index"
      let i := idx.toUInt64.toNat
      let at_ := off + i * elemSize ty
      let read : M Value := do pure (typedRead ty (bufferBytes (← getObj b)) at_)
      if op == 10 then
        -- notify: no agent waits here
        let _ ← core.toNum (argD args 2)
        return .num 0
      if op == 5 then return ← read
      let v ← core.typedConv ty (argD args 2)
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
          let rep ← core.typedConv ty (argD args 3)
          pure (if (raw v).data == (raw old).data then some rep else none)
        | 3 => pure (some v)
        | 6 => pure (some (mk (bigBits Nat.lor o x)))
        | 8 => pure (some (mk (o - x)))
        | _ => pure (some (mk (bigBits Nat.xor o x)))
      if let some nv := newV? then typedWriteV ty b off i nv
      pure old
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: %TypedArray%: the constructor, `from`, `of`, the accessors, the methods with Array.prototype's steps, `toLocaleString`, and the Uint8Array base64 and hex methods. `r` is the realm `moreNative` read. -/
def moreNativeTyped (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
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
      -- the TypedArrayLength of the record (§23.2.4.4 step 4): a length-tracking view's too
      pure (ty, b, off, ← liveLen ty b off len)
    match id with
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
          | _ => core.getV a0 (symKey symIterator)
        let vs ← match usingIter with
          | .undef | .null => do core.elemsOf (.obj (← core.toObj a0))
          | f => do
            if !(← isCallable f) then throwErr .type "TypedArray.from: @@iterator is not callable"
            core.iterToArray (← core.getIterator a0) #[]
        if mapping then
          let mut out := #[]
          for i in [0:vs.size] do out := out.push (← core.callV mapFn (argD args 2) #[vs[i]!, .num (Float.ofNat i)])
          pure out
        else pure vs
      let ta ← core.construct thisV #[.num (Float.ofNat items.size)] thisV
      match ta with
      | .obj tid => match (← getObj tid).kind with
        | .typed ty b off len =>
          if (← liveLen ty b off len) < items.size then throwErr .type "TypedArray.from/of: the new typed array is too short"
        | _ => throwErr .type "TypedArray.from/of: the constructor did not make a typed array"
      | _ => throwErr .type "TypedArray.from/of: the constructor did not make a typed array"
      for i in [0:items.size] do core.putV ta (toString i) items[i]! true
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
      let gone := !(← typedInBounds ty b off len)
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
      let (_, _, _, len) ← validTyped s!"%TypedArray%.prototype.{nm.1}"
      -- the steps of §23.2.3: the length is the TypedArrayLength taken here (never a `length`
      -- property), and each element is a [[Get]] when it is reached (undefined once a resize or
      -- a detach in a callback has taken it); only indexOf asks HasProperty first
      let at_ (i : Nat) : M Value := core.getV thisV (toString i)
      let cbOf : M Value := do
        if !(← isCallable a0) then throwErr .type s!"%TypedArray%.prototype.{nm.1}: the callback is not a function"
        pure a0
      let call (f : Value) (i : Nat) : M (Value × Value) := do
        let v ← at_ i
        pure (v, ← core.callV f a1 #[v, .num (Float.ofNat i), thisV])
      if k == 0 || k == 4 || k == 5 || k == 7 || k == 8 then
        -- forEach, every, some, find, findIndex
        let f ← cbOf
        for i in [0:len] do
          let (v, res) ← call f i
          let t := toBool res
          if k == 4 && !t then return .bool false
          if k == 5 && t then return .bool true
          if k == 7 && t then return v
          if k == 8 && t then return .num (Float.ofNat i)
        return (if k == 4 then .bool true else if k == 5 then .bool false
          else if k == 8 then .num (-1) else .undef)
      if k == 6 then
        -- reduce
        let f ← cbOf
        if len == 0 && args.size < 2 then throwErr .type "Reduce of empty array with no initial value"
        let mut acc := a1
        let mut start := 0
        if args.size < 2 then
          acc ← at_ 0
          start := 1
        for i in [start:len] do
          let v ← at_ i
          acc ← core.callV f .undef #[acc, v, .num (Float.ofNat i), thisV]
        return acc
      if k == 2 || k == 3 then
        -- indexOf, includes
        if len == 0 then return (if k == 2 then .num (-1) else .bool false)
        let start := relIndex (← core.toNum a1) len
        for i in [start:len] do
          if k == 2 then
            if let .obj oid := thisV then
              if (← core.hasProp oid (toString i)) then
                if strictEq (← at_ i) a0 then return .num (Float.ofNat i)
          else if sameValueZero (← at_ i) a0 then return .bool true
        return (if k == 2 then .num (-1) else .bool false)
      if k == 1 then
        -- join
        let sep ← match a0 with | .undef => pure "," | v => core.toStr v
        let mut parts : Array String := Array.emptyWithCapacity len
        for i in [0:len] do
          match ← at_ i with
          | .undef | .null => parts := parts.push ""
          | v => parts := parts.push (← core.toStr v)
        checkStrLen (parts.foldl (fun acc t => acc + t.utf8ByteSize + sep.utf8ByteSize) 0)
        return .str (Str.canonical (sep.intercalate parts.toList))
      let tp ← match (← getObj r.typedArrayCtor).getOwn "prototype" with
        | some (.data (.obj p) ..) => pure p
        | _ => throwErr .type "no %TypedArray%.prototype"
      match (← getObj tp).getOwn (typedGenericKey nm.1) with
      | some (.data f ..) => core.callV f thisV args
      | _ => throwErr .type s!"%TypedArray%.prototype.{nm.1} is missing"
    | (.x (.u8Base64 k)) =>
      -- Uint8Array base64 and hex (§23.3.2): 0 fromBase64, 1 fromHex, 2 toBase64, 3 toHex,
      -- 4 setFromBase64, 5 setFromHex; the algorithms are JS.Base64's
      -- GetOptionsObject, then alphabet and lastChunkHandling (strings, not converted)
      let optsOf (v : Value) : M Value := do
        match v with
        | .undef => pure .undef
        | .obj _ => pure v
        | _ => throwErr .type "Uint8Array base64: the options are not an object"
      let getOpt (o : Value) (key : String) : M Value := do
        match o with | .obj _ => core.getV o key | _ => pure .undef
      let alphabetOf (o : Value) : M Bool := do
        match ← getOpt o "alphabet" with
        | .undef | .str "base64" => pure false
        | .str "base64url" => pure true
        | _ => throwErr .type "Uint8Array base64: alphabet is not \"base64\" or \"base64url\""
      let lchOf (o : Value) : M Nat := do
        match ← getOpt o "lastChunkHandling" with
        | .undef | .str "loose" => pure 0
        | .str "strict" => pure 1
        | .str "stop-before-partial" => pure 2
        | _ => throwErr .type "Uint8Array.fromBase64: lastChunkHandling is not loose, strict or stop-before-partial"
      -- ValidateUint8Array on `this`, and the view's bytes (a TypeError when detached)
      let thisU8 : M (Nat × Nat × Nat) := do
        let .obj tid := thisV | throwErr .type "not a Uint8Array"
        let .typed ty b off len := (← getObj tid).kind | throwErr .type "not a Uint8Array"
        if ty != 1 then throwErr .type "not a Uint8Array"
        if !(← typedInBounds ty b off len) then throwErr .type "Uint8Array: the buffer is detached or out of bounds"
        pure (b, off, ← liveLen ty b off len)
      let checkType : M Unit := do
        let .obj tid := thisV | throwErr .type "not a Uint8Array"
        let .typed ty .. := (← getObj tid).kind | throwErr .type "not a Uint8Array"
        if ty != 1 then throwErr .type "not a Uint8Array"
      let charsOfStr (v : Value) : M (Array Char) := do
        match v with
        | .str t => pure (Str.unitChars t)
        | _ => throwErr .type "Uint8Array base64: the input is not a string"
      match k with
      | 0 | 1 =>
        let cs ← charsOfStr a0
        let res ← if k == 0 then do
            let o ← optsOf a1
            let url ← alphabetOf o
            let lch ← lchOf o
            pure (Base64.fromBase64 cs url lch 9007199254740991)
          else pure (Base64.fromHex cs 9007199254740991)
        if res.err then throwErr .syntax "Uint8Array: the base64 or hex text is not valid"
        let buf ← newBuffer (ByteArray.mk res.bytes)
        let .obj bid := buf | pure .undef
        newTyped 1 bid 0 res.bytes.size
      | 2 | 3 =>
        checkType
        let o ← if k == 2 then optsOf a0 else pure .undef
        let url ← if k == 2 then alphabetOf o else pure false
        let pad ← if k == 2 then do pure !(toBool (← getOpt o "omitPadding")) else pure true
        let (b, off, len) ← thisU8
        let bytes := (bufferBytes (← getObj b)).extract off (off + len)
        pure (.str (if k == 2 then Base64.toBase64 bytes url pad else Base64.toHex bytes))
      | _ =>
        checkType
        let cs ← charsOfStr a0
        let (url, lch) ← if k == 4 then do
            let o ← optsOf a1
            let url ← alphabetOf o
            pure (url, ← lchOf o)
          else pure (false, 0)
        -- after the options (which may detach or shrink the buffer): the view's length
        let (b, off, len) ← thisU8
        let res := if k == 4 then Base64.fromBase64 cs url lch len else Base64.fromHex cs len
        let n' := min res.bytes.size len
        modifyObj b fun bo => match bo.kind with
          | .buffer bytes =>
            let bo := { bo with kind := .buffer ByteArray.empty }
            { bo with kind := .buffer ((ByteArray.mk (res.bytes.extract 0 n')).copySlice 0 bytes off n') }
          | _ => bo
        if res.err then throwErr .syntax "Uint8Array: the base64 or hex text is not valid"
        let ro ← newObject
        defineOwn ro "read" (.data (.num (Float.ofNat res.read)) true true true)
        defineOwn ro "written" (.data (.num (Float.ofNat n')) true true true)
        pure (.obj ro)
    | (.x (.arrayToLocaleString typed)) =>
      -- §23.1.3.32 Array.prototype.toLocaleString and §23.2.3.31 %TypedArray%.prototype's
      -- (ValidateTypedArray, its own length): each element's toLocaleString, joined with ","
      let (o, len) ← if typed then do
          let .obj tid := thisV | throwErr .type "not a typed array"
          let .typed ty b off l := (← getObj tid).kind | throwErr .type "not a typed array"
          if !(← typedInBounds ty b off l) then throwErr .type "toLocaleString: the typed array is detached or out of bounds"
          pure (thisV, ← liveLen ty b off l)
        else do
          let oid ← core.toObj thisV
          pure (Value.obj oid, ← core.arrayLikeLength (.obj oid))
      let mut out := ""
      for k in [0:len] do
        tick
        if k > 0 then out := out ++ ","
        let v ← core.getV o (toString k)
        match v with
        | .undef | .null => pure ()
        | _ =>
          let f ← core.getV v "toLocaleString"
          if !(← isCallable f) then throwErr .type "toLocaleString is not a function"
          out := out ++ (← core.toStr (← core.callV f v #[]))
          checkStrLen out.utf8ByteSize
      pure (.str (Str.canonical out))
    | _ => throwErr .type "not a function"

/-- The shared index and get steps of Array and TypedArray `at`. The caller reads
the length before coercing the index. The one indexed read observes any update
made during coercion, including a typed buffer resize or detachment. -/
def arrayAtWithLength (core : CoreFn H) (receiver : Value) (len : Nat) (index : Value) : M Value := do
  let k := toIntegerOrInf (← core.toNum index)
  let i := if k < 0 then Float.ofNat len + k else k
  if i < 0 || i ≥ Float.ofNat len then pure .undef
  else core.getV receiver (toString i.toUInt64.toNat)

/-- Built-ins of `moreNative`: the %TypedArray%.prototype methods that answer a typed array or work on its bytes. `r` is the realm `moreNative` read. -/
def moreNativeTypedMethod (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
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
      -- the TypedArrayLength of the record (§23.2.4.4 step 4): a length-tracking view's too
      pure (ty, b, off, ← liveLen ty b off len)
    -- a new typed array of type `ty` holding these (already converted) values
    let fresh (ty : Nat) (xs : Array Value) : M Value := do
      let buf ← newBuffer (zeroBytes (xs.size * elemSize ty))
      let .obj bid := buf | pure buf
      for i in [0:xs.size] do typedWriteV ty bid 0 i xs[i]!
      newTyped ty bid 0 xs.size
    let valuesOf (ty b off len : Nat) : M (Array Value) := do
      let len ← liveLen ty b off len
      let bytes := bufferBytes (← getObj b)
      pure ((List.range len).toArray.map fun i => typedRead ty bytes (off + i * elemSize ty))
    match id with
    | (.x (.typedMethod which)) =>
      let (ty, b, off, len) ← validTyped "TypedArray method"
      if which == 4 then return ← arrayAtWithLength core thisV len a0
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
          pure (← core.mergeSort cmp xs.toList).toArray
      let callback (f : Value) : M Unit := do
        if !(← isCallable f) then throwErr .type "callback is not a function"
      -- TypedArraySpeciesCreate (§23.2.4.1): `none` when the species is this array's own
      -- constructor (the fast path); else the new typed array, checked as TypedArrayCreate does
      let speciesTA (count : Nat) : M (Option Value) := do
        let c ← core.speciesCtor thisV .undef
        let own ← match c with
          | .undef => pure true
          | .obj cid => do pure (match (← getObj cid).kind with | .native (.typedCtor t) => t == ty | _ => false)
          | _ => pure false
        if own then return none
        if !(← isConstructor c) then throwErr .type "object.constructor[Symbol.species] is not a constructor"
        let a ← core.construct c #[.num (Float.ofNat count)] c
        let .obj aid := a | throwErr .type "The species constructor did not make a typed array"
        let .typed ty2 b2 off2 len2 := (← getObj aid).kind
          | throwErr .type "The species constructor did not make a typed array"
        let live2 ← liveLen ty2 b2 off2 len2
        if !(← typedInBounds ty2 b2 off2 len2) then throwErr .type "The species constructor made a detached typed array"
        if live2 < count then throwErr .type "The species constructor made a typed array that is too short"
        if typedIsBig ty2 != typedIsBig ty then throwErr .type "The species constructor made a typed array of the other content type"
        pure (some a)
      let fill (a : Value) (vs : Array Value) : M Value := do
        for i in [0:vs.size] do core.putV a (toString i) vs[i]! true
        pure a
      match which with
      | 0 =>
        -- copyWithin (§23.2.3.6): the elements move as the bytes would
        let to := relIndex (toIntegerOrInf (← core.toNum a0)) size
        let from_ := relIndex (toIntegerOrInf (← core.toNum a1)) size
        let fin ← match argD args 2 with
          | .undef => pure size
          | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) size)
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
        let st := relIndex (toIntegerOrInf (← core.toNum a0)) size
        let en ← match a1 with
          | .undef => pure size
          | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) size)
        let count := if en > st then en - st else 0
        let sp ← speciesTA count
        let vs ← valuesOf ty b off len
        let part := vs.extract st (max st en)
        match sp with
        | none => fresh ty part
        | some a => fill a part
      | 3 => writeAll (← sorted a0); pure thisV
      | 5 =>
        -- lastIndexOf (§23.2.3.20): strict equality, from the end
        let start ← if args.size > 1 then do
            let k := toIntegerOrInf (← core.toNum a1)
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
          -- each element is read when its turn comes (a callback may change or shrink the array)
          let v ← core.getV thisV (toString i)
          if toBool (← core.callV a0 a1 #[v, .num (Float.ofNat i), thisV]) then kept := kept.push v
        match ← speciesTA kept.size with
        | none => fresh ty kept
        | some a => fill a kept
      | 7 =>
        callback a0
        match ← speciesTA size with
        | some a =>
          for i in [0:size] do
            let v ← core.getV thisV (toString i)
            core.putV a (toString i) (← core.callV a0 a1 #[v, .num (Float.ofNat i), thisV]) true
          pure a
        | none =>
          let mut out := #[]
          for i in [0:size] do
            let v ← core.getV thisV (toString i)
            out := out.push (← core.typedConv ty (← core.callV a0 a1 #[v, .num (Float.ofNat i), thisV]))
          fresh ty out
      | 8 => fresh ty xs.reverse
      | 9 =>
        match a0 with
        | .undef => pure ()
        | f => callback f
        fresh ty (← sorted a0)
      | 10 =>
        -- with (§23.2.3.36): the index is checked against the length after the value converts
        let k := toIntegerOrInf (← core.toNum a0)
        let i := if k < 0 then Float.ofNat size + k else k
        let v ← core.typedConv ty a1
        let live ← liveLen ty b off len
        if i < 0 || i ≥ Float.ofNat live then throwErr .range "Invalid typed array index"
        fresh ty (xs.set! i.toUInt64.toNat v)
      | 11 | 12 =>
        callback a0
        let mut found : Option Nat := none
        for j in [0:size] do
          let i := size - 1 - j
          if found.isNone then
            if toBool (← core.callV a0 a1 #[xs[i]!, .num (Float.ofNat i), thisV]) then found := some i
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
          acc ← core.callV a0 .undef #[acc, xs[i]!, .num (Float.ofNat i), thisV]
        pure acc
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: SuppressedError, DisposableStack and `Iterator.prototype[@@dispose]`. `r` is the realm `moreNative` read. -/
def moreNativeDisposable (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    -- a DisposableStack receiver: its object and whether it is disposed
    let thisStack (what : String) : M (Nat × Bool) := do
      match thisV with
      | .obj sid =>
        let o ← getObj sid
        match o.getOwn dsStateKey with
        | some (.data (.bool b) ..) => pure (sid, b)
        | _ => throwErr .type s!"{what}: the receiver is not a DisposableStack"
      | _ => throwErr .type s!"{what}: the receiver is not a DisposableStack"
    match id with
    | (.x .suppressedErrorCtor) =>
      -- SuppressedError(error, suppressed, message)
      let proto ← match newTarget with
        | some nt => do
          let p ← core.getV nt "prototype"
          protoOr p nt (·.suppressedErrorProto)
        | none => pure (.obj r.suppressedErrorProto)
      let o ← alloc { proto, kind := .error }
      match argD args 2 with
      | .undef => pure ()
      | v => setHidden o "message" (.str (← core.toStr v))
      setHidden o "error" a0
      setHidden o "suppressed" a1
      pure (.obj o)
    | (.x .disposableStackCtor) =>
      let some nt := newTarget | throwErr .type "Constructor DisposableStack requires 'new'"
      let p ← core.getV nt "prototype"
      let o ← alloc { proto := (← protoOr p nt (·.disposableStackProto)) }
      setHidden o dsStackKey (← newArray #[])
      setHidden o dsStateKey (.bool false)
      pure (.obj o)
    | (.x .disposableStackDisposed) =>
      let (_, st) ← thisStack "get DisposableStack.prototype.disposed"
      pure (.bool st)
    | (.x (.disposableStackMethod k)) =>
      let mname := (#["dispose", "use", "adopt", "defer", "move"] : Array String).getD k ""
      let what := s!"DisposableStack.prototype.{mname}"
      let (sid, disposed) ← thisStack what
      let stackV := match (← getObj sid).getOwn dsStackKey with | some (.data v ..) => v | _ => .undef
      let push (v m : Value) : M Unit := do
        let es ← core.elemsOf stackV
        if let .obj aid := stackV then modifyObj aid fun o => { o with kind := .array ((es.push v).push m) }
      if k != 0 && disposed then throwErr .reference s!"{what}: the DisposableStack is disposed"
      match k with
      | 0 =>
        -- DisposeResources (§ explicit resource management): last in, first out; a later
        -- error wraps the earlier one in a SuppressedError
        if disposed then return .undef
        setHidden sid dsStateKey (.bool true)
        let es ← core.elemsOf stackV
        let mut err : Option Value := none
        let mut i := es.size / 2
        for _ in [0:es.size / 2] do
          i := i - 1
          let x ← catchJS (do let _ ← core.callV es[2 * i + 1]! es[2 * i]! #[]; pure none) fun e => match e with
            | .throw v => pure (some v)
            | a => throw a
          if let some v := x then
            match err with
            | none => err := some v
            | some old =>
              let s ← alloc { proto := .obj r.suppressedErrorProto, kind := .error }
              setHidden s "error" v
              setHidden s "suppressed" old
              err := some (.obj s)
        if let .obj aid := stackV then modifyObj aid fun o => { o with kind := .array #[] }
        match err with
        | some v => throw (.throw v)
        | none => pure .undef
      | 1 =>
        -- use(value): null and undefined hold nothing; an object needs a callable @@dispose
        match a0 with
        | .undef | .null => pure a0
        | .obj _ =>
          let m ← core.getV a0 (symKey symDispose)
          if !(← isCallable m) then throwErr .type "DisposableStack.prototype.use: the value has no callable [Symbol.dispose]"
          push a0 m
          pure a0
        | _ => throwErr .type "DisposableStack.prototype.use: the value is not an object"
      | 2 =>
        if !(← isCallable a1) then throwErr .type "DisposableStack.prototype.adopt: onDispose is not callable"
        let f ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x .adoptClosure)) .undef #[a0, a1] }
        push .undef (.obj f)
        pure a0
      | 3 =>
        if !(← isCallable a0) then throwErr .type "DisposableStack.prototype.defer: onDispose is not callable"
        push .undef a0
        pure .undef
      | _ =>
        -- move(): a new stack (of %DisposableStack.prototype%) takes the resources
        let o ← alloc { proto := .obj r.disposableStackProto }
        setHidden o dsStackKey stackV
        setHidden o dsStateKey (.bool false)
        setHidden sid dsStackKey (← newArray #[])
        setHidden sid dsStateKey (.bool true)
        pure (.obj o)
    | (.x .adoptClosure) => core.callV a1 .undef #[a0]
    | (.x .iteratorDispose) =>
      -- %IteratorPrototype%[@@dispose]: GetMethod(this, "return"), then call it
      let ret ← core.getV thisV "return"
      match ret with
      | .undef | .null => pure .undef
      | f =>
        if !(← isCallable f) then throwErr .type "Iterator.prototype[Symbol.dispose]: return is not callable"
        let _ ← core.callV f thisV #[]
        pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: AsyncDisposableStack. `r` is the realm `moreNative` read. -/
def moreNativeAsyncDisposable (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x .asyncDisposableStackCtor) =>
      let some nt := newTarget | throwErr .type "Constructor AsyncDisposableStack requires 'new'"
      let p ← core.getV nt "prototype"
      let dflt ← ownValue r.disposableStackProto adsKey
      let o ← alloc { proto := if p.isObj then p else dflt }
      setHidden o dsStackKey (← newArray #[])
      setHidden o dsStateKey (.bool false)
      setHidden o adsKey (.bool true)
      pure (.obj o)
    | (.x .asyncDsDisposed) =>
      let .obj sid := thisV | throwErr .type "get AsyncDisposableStack.prototype.disposed: the receiver is not an AsyncDisposableStack"
      let o ← getObj sid
      match o.getOwn adsKey, o.getOwn dsStateKey with
      | some _, some (.data (.bool b) ..) => pure (.bool b)
      | _, _ => throwErr .type "get AsyncDisposableStack.prototype.disposed: the receiver is not an AsyncDisposableStack"
    | (.x .asyncDsSyncWrap) =>
      -- a resource with only @@dispose: called on the value, its result dropped
      let _ ← core.callV a0 thisV #[]
      pure .undef
    | (.x (.asyncDsMethod k)) =>
      let mname := (#["disposeAsync", "use", "adopt", "defer", "move"] : Array String).getD k ""
      let what := s!"AsyncDisposableStack.prototype.{mname}"
      let asyncStack? : M (Option (Nat × Bool)) := do
        match thisV with
        | .obj sid =>
          let o ← getObj sid
          match o.getOwn adsKey, o.getOwn dsStateKey with
          | some _, some (.data (.bool b) ..) => pure (some (sid, b))
          | _, _ => pure none
        | _ => pure none
      if k == 0 then
        -- disposeAsync: a promise of %Promise%; a wrong receiver rejects it
        let cap ← core.callNative (.x .promiseWithResolvers) (.obj r.promiseCtor) #[] none
        let capP ← core.getV cap "promise"
        let res ← core.getV cap "resolve"
        let rej ← core.getV cap "reject"
        match ← asyncStack? with
        | none =>
          let _ ← core.callV rej .undef #[← mkError .type s!"{what}: the receiver is not an AsyncDisposableStack"]
          return capP
        | some (sid, disposed) =>
          if disposed then
            let _ ← core.callV res .undef #[.undef]
            return capP
          setHidden sid dsStateKey (.bool true)
          let stackV := match (← getObj sid).getOwn dsStackKey with | some (.data v ..) => v | _ => .undef
          let es ← core.elemsOf stackV
          setHidden sid dsStackKey (← newArray #[])
          let holder ← alloc { proto := .null }
          let _ ← core.callNative (.x (.asyncDsStep false)) .undef
            #[← newArray es, .num (Float.ofNat (es.size / 2)), .obj holder, res, rej, .undef, .bool true] none
          return capP
      let some (sid, disposed) ← asyncStack? | throwErr .type s!"{what}: the receiver is not an AsyncDisposableStack"
      let stackV := match (← getObj sid).getOwn dsStackKey with | some (.data v ..) => v | _ => .undef
      let push (v m : Value) : M Unit := do
        let es ← core.elemsOf stackV
        if let .obj aid := stackV then modifyObj aid fun o => { o with kind := .array ((es.push v).push m) }
      if disposed then throwErr .reference s!"{what}: the AsyncDisposableStack is disposed"
      match k with
      | 1 =>
        -- use(value): GetDisposeMethod(value, async-dispose); null and undefined are awaited
        match a0 with
        | .undef | .null => push .undef .undef; pure a0
        | .obj _ =>
          let m ← core.getV a0 (symKey 14)
          match m with
          | .undef | .null =>
            let sm ← core.getV a0 (symKey symDispose)
            if !(← isCallable sm) then throwErr .type s!"{what}: the value has no callable [Symbol.asyncDispose] or [Symbol.dispose]"
            let w ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x .asyncDsSyncWrap)) .undef #[sm] }
            push a0 (.obj w)
          | m =>
            if !(← isCallable m) then throwErr .type s!"{what}: [Symbol.asyncDispose] is not callable"
            push a0 m
          pure a0
        | _ => throwErr .type s!"{what}: the value is not an object"
      | 2 =>
        if !(← isCallable a1) then throwErr .type s!"{what}: onDisposeAsync is not callable"
        let f ← alloc { proto := .obj r.functionProto, kind := .bound (← nativeFn (.x .adoptClosure)) .undef #[a0, a1] }
        push .undef (.obj f)
        pure a0
      | 3 =>
        if !(← isCallable a0) then throwErr .type s!"{what}: onDisposeAsync is not callable"
        push .undef a0
        pure .undef
      | _ =>
        let dflt ← ownValue r.disposableStackProto adsKey
        let o ← alloc { proto := dflt }
        setHidden o dsStackKey stackV
        setHidden o dsStateKey (.bool false)
        setHidden o adsKey (.bool true)
        setHidden sid dsStackKey (← newArray #[])
        setHidden sid dsStateKey (.bool true)
        pure (.obj o)
    | (.x (.asyncDsStep rejected)) =>
      -- DisposeResources with the async-dispose hint, one Await at a time. Bound arguments:
      -- the resources (value, method pairs), how many are left, the record, resolve, reject;
      -- then the awaited value (or reason), and on the first call `true`.
      let stackV := a0
      let mut i := match a1 with | .num x => x.toUInt64.toNat | _ => 0
      let .obj holder := argD args 2 | pure .undef
      let res := argD args 3
      let rej := argD args 4
      let flag (k : String) : M Bool := do pure ((← getObj holder).getOwn k).isSome
      let record (e : Value) : M Unit := do
        match (← getObj holder).getOwn adsErrKey with
        | some (.data old ..) =>
          let sup ← alloc { proto := .obj r.suppressedErrorProto, kind := .error }
          setHidden sup "error" e
          setHidden sup "suppressed" old
          setHidden holder adsErrKey (.obj sup)
        | _ => setHidden holder adsErrKey e
      if rejected then record (argD args 5)
      let es ← core.elemsOf stackV
      -- Await(v), then this step again with `left` resources
      let awaitThen (v : Value) (left : Nat) : M Value := do
        let p ← core.promiseResolve v
        let mk (rj : Bool) : M Value := do
          let nf ← nativeFn (.x (.asyncDsStep rj))
          let f ← alloc { proto := .obj r.functionProto, kind := .bound nf .undef #[stackV, .num (Float.ofNat left), .obj holder, res, rej] }
          pure (.obj f)
        let onF ← mk false
        let onR ← mk true
        core.performThen p onF onR .undef
        pure .undef
      for _ in [0:es.size / 2 + 1] do
        if i == 0 then break
        let v := es.getD (2 * (i - 1)) .undef
        let m := es.getD (2 * (i - 1) + 1) .undef
        if m matches .undef then
          setHidden holder adsNeedKey (.bool true)
          i := i - 1
          continue
        if (← flag adsNeedKey) && !(← flag adsDoneKey) then
          deleteOwn holder adsNeedKey
          return ← awaitThen .undef i
        let x ← catchJS (do pure (Except.ok (← core.callV m v #[]))) fun e => pure (Except.error e)
        match x with
        | .ok result =>
          setHidden holder adsDoneKey (.bool true)
          return ← awaitThen result (i - 1)
        | .error (.throw e) =>
          record e
          i := i - 1
        | .error a => throw a
      if (← flag adsNeedKey) && !(← flag adsDoneKey) then
        deleteOwn holder adsNeedKey
        return ← awaitThen .undef 0
      match (← getObj holder).getOwn adsErrKey with
      | some (.data e ..) => let _ ← core.callV rej .undef #[e]
      | _ => let _ ← core.callV res .undef #[.undef]
      pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: the Iterator constructor, `Iterator.concat`, `Iterator.from` and the lazy iterator helpers. `r` is the realm `moreNative` read. -/
def moreNativeIterator (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x .iteratorCtor) =>
      -- §27.1.3.1 Iterator: abstract; a subclass may construct
      let some nt := newTarget | throwErr .type "Constructor Iterator requires 'new'"
      if strictEq nt (← core.getV (.obj r.globalObj) "Iterator") then throwErr .type "Abstract class Iterator not directly constructable"
      let p ← core.getV nt "prototype"
      pure (.obj (← alloc { proto := (← protoOr p nt (·.iterProto)) }))
    | (.x .iteratorConcat) =>
      -- §27.1.3.2.2 Iterator.concat: every argument an object with a callable @@iterator, checked
      -- first; the iterators are made one at a time as the result is read
      let mut items : Array Value := #[]
      for a in args do
        if !a.isObj then throwErr .type "Iterator.concat: an argument is not an object"
        let m ← core.getV a (symKey symIterator)
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
        | .str _ => core.getIterator a0
        | .obj _ => do
          let m ← core.getV a0 (symKey symIterator)
          match m with
          | .undef | .null => pure a0
          | f =>
            if !(← isCallable f) then throwErr .type "Iterator.from: @@iterator is not callable"
            let it ← core.callV f a0 #[]
            if !it.isObj then throwErr .type "Iterator.from: the iterator is not an object"
            pure it
        | _ => throwErr .type "Iterator.from called on a non-object"
      let next ← core.getV it "next"
      if ← core.instOf it (← core.getV (.obj r.globalObj) "Iterator") then return it
      let w ← alloc { proto := .obj r.wrapIterProto }
      defineOwn w helperIt (.data it true false false)
      defineOwn w helperNextKey (.data next true false false)
      defineOwn w helperKind (.data (.num 5) true false false)
      pure (.obj w)
    | (.x (.iterLazy k)) =>
      -- §27.1.4.{5,4,12,3,6}: GetIteratorDirect, the argument checked, a helper made
      if !thisV.isObj then throwErr .type "Iterator.prototype method called on a non-object"
      -- chunks (8) and windows (9) (proposal-iterator-chunking): the size a Number, integral,
      -- from 1 to 2^32 - 1, not converted; windows' `undersized` "only-full" or "allow-partial";
      -- an invalid argument closes the iterator (its own error wins)
      let closeWith (e : Abrupt) : M Unit := do
        catchJS (core.iterClose thisV) fun b => match b with | .halt w => throw (.halt w) | _ => pure ()
        throw e
      let mut allowPartial := false
      if k ≥ 8 then
        match a0 with
        | .num x =>
          if x.isNaN || !x.isFinite || toIntegerOrInf x != x then
            closeWith (.throw (← mkError .type "Iterator helper size is not an integral number"))
          if x < 1 || x > 4294967295 then closeWith (.throw (← mkError .range "Iterator helper size is out of range"))
        | _ => closeWith (.throw (← mkError .type "Iterator helper size is not a number"))
        if k == 9 then
          match a1 with
          | .undef | .str "only-full" => pure ()
          | .str "allow-partial" => allowPartial := true
          | _ => closeWith (.throw (← mkError .type "Iterator.prototype.windows: undersized is not \"only-full\" or \"allow-partial\""))
      let lim ← if k ≥ 8 then pure a0 else if k == 2 || k == 3 then do
          let x ← core.toNum a0
          if x.isNaN then
            core.iterClose thisV
            throwErr .range "Iterator helper limit is NaN"
          let x := toIntegerOrInf x
          if x < 0 then
            core.iterClose thisV
            throwErr .range "Iterator helper limit is negative"
          pure (Value.num x)
        else do
          if !(← isCallable a0) then
            core.iterClose thisV
            throwErr .type "Iterator helper callback is not a function"
          pure a0
      let next ← core.getV thisV "next"
      let h ← alloc { proto := .obj r.iterHelperProto }
      defineOwn h helperIt (.data thisV true false false)
      defineOwn h helperNextKey (.data next true false false)
      defineOwn h helperKind (.data (.num (Float.ofNat k)) true false false)
      defineOwn h helperFn (.data lim true false false)
      defineOwn h helperCount (.data (.num (if allowPartial then 1 else 0)) true false false)
      defineOwn h helperInner (.data .undef true false false)
      pure (.obj h)
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: `Iterator.zip` and `Iterator.zipKeyed`. `r` is the realm `moreNative` read. -/
def moreNativeIteratorZip (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.iteratorZip keyed)) =>
      -- §27.1.3.2.3 Iterator.zip, §27.1.3.2.4 Iterator.zipKeyed
      let what := if keyed then "Iterator.zipKeyed" else "Iterator.zip"
      if !a0.isObj then throwErr .type s!"{what}: the iterables are not an object"
      match a1 with
      | .undef | .obj _ => pure ()
      | _ => throwErr .type s!"{what}: the options are not an object"
      let modeV ← if a1.isObj then core.getV a1 "mode" else pure .undef
      let mode ← match modeV with
        | .undef => pure 0
        | .str "shortest" => pure 0
        | .str "longest" => pure 1
        | .str "strict" => pure 2
        | _ => throwErr .type s!"{what}: mode is not shortest, longest or strict"
      let padOpt ← if mode == 1 && a1.isObj then core.getV a1 "padding" else pure .undef
      if !(padOpt matches .undef) && !padOpt.isObj then throwErr .type s!"{what}: padding is not an object"
      let mut slots : Array Value := #[]
      let mut keys : Array Value := #[]
      -- the open iterators so far, closed (last first) when reading the iterables fails
      let closeAll (sl : Array Value) : M Unit := do
        for j in [0:sl.size / 2] do
          let i := sl.size / 2 - 1 - j
          catchJS (core.iterClose sl[2 * i]!) fun _ => pure ()
      -- GetIteratorFlattenable(value, reject-strings)
      let flat (v : Value) : M (Value × Value) := do
        if !v.isObj then throwErr .type s!"{what}: an iterable is not an object"
        let m ← core.getV v (symKey symIterator)
        let iter ← match m with
          | .undef | .null => pure v
          | f => core.callV f v #[]
        if !iter.isObj then throwErr .type s!"{what}: an iterator is not an object"
        pure (iter, ← core.getV iter "next")
      if keyed then
        let oid := match a0 with | .obj o => o | _ => 0
        for k in (← core.ownKeysOf oid) do
          let r ← catchJS (do
              match ← core.ownDesc oid k with
              | some d =>
                if d.enumerable then
                  let v ← core.getV a0 k
                  if (v matches .undef) then pure (Except.ok none)
                  else pure (Except.ok (some (← flat v)))
                else pure (Except.ok none)
              | none => pure (Except.ok none)) fun e => pure (Except.error e)
          match r with
          | .error e => closeAll slots; throw e
          | .ok none => pure ()
          | .ok (some (iv, nx)) =>
            slots := (slots.push iv).push nx
            keys := keys.push (keyValue k)
      else
        let input ← core.getIterator a0
        for _ in [0:1000000000] do
          let r ← catchJS (do
              match ← core.iterStep input with
              | none => pure (Except.ok none)
              | some v =>
                let x ← catchJS (do pure (Except.ok (← flat v))) fun e => pure (Except.error e)
                match x with
                | .ok p => pure (Except.ok (some p))
                | .error e =>
                  catchJS (core.iterClose input) fun _ => pure ()
                  throw e) fun e => pure (Except.error e)
          match r with
          | .error e => closeAll slots; throw e
          | .ok none => break
          | .ok (some (iv, nx)) => slots := (slots.push iv).push nx
      let count := slots.size / 2
      let mut pads : Array Value := Array.replicate count .undef
      if mode == 1 && padOpt.isObj then
        if keyed then
          for i in [0:count] do
            let pv ← catchJS (do pure (Except.ok (← core.getV padOpt (← core.toKey keys[i]!)))) fun e => pure (Except.error e)
            match pv with
            | .ok v => pads := pads.set! i v
            | .error e => closeAll slots; throw e
        else
          let r ← catchJS (do
              let pit ← core.getIterator padOpt
              let mut usePad := true
              let mut out : Array Value := #[]
              for _ in [0:count] do
                if usePad then
                  match ← core.iterStep pit with
                  | some v => out := out.push v
                  | none =>
                    usePad := false
                    out := out.push .undef
                else out := out.push .undef
              if usePad then core.iterClose pit
              pure (Except.ok out)) fun e => pure (Except.error e)
          match r with
          | .ok out => pads := out
          | .error e => closeAll slots; throw e
      let h ← alloc { proto := .obj r.iterHelperProto }
      defineOwn h helperIt (.data (← newArray slots) true false false)
      defineOwn h helperNextKey (.data .undef true false false)
      defineOwn h helperKind (.data (.num 7) true false false)
      defineOwn h helperFn (.data .undef true false false)
      defineOwn h helperCount (.data (.num 0) true false false)
      defineOwn h helperInner (.data .undef true false false)
      defineOwn h zipModeKey (.data (.num (Float.ofNat mode)) true false false)
      defineOwn h zipPadKey (.data (← newArray pads) true false false)
      let keysArr ← if keyed then newArray keys else pure .undef
      defineOwn h zipKeysKey (.data keysArr true false false)
      defineOwn h zipOpenKey (.data (.num (Float.ofNat count)) true false false)
      pure (.obj h)
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: the iterator helpers that run the iterator to its end (`reduce`, `toArray`, `forEach`, `some`, `every`, `find`). `r` is the realm `moreNative` read. -/
def moreNativeIterEager (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.iterEager 6)) | (.x (.iterEager 7)) =>
      -- Iterator.prototype.includes (proposal-iterator-includes) and .join
      -- (proposal-iterator-join): eager, the iterator closed on an argument error and on a match
      if !thisV.isObj then throwErr .type "Iterator.prototype method called on a non-object"
      let closeWith (e : Abrupt) : M Unit := do
        catchJS (core.iterClose thisV) fun b => match b with | .halt w => throw (.halt w) | _ => pure ()
        throw e
      let isJoin := id == (.x (.iterEager 7))
      let mut toSkip : Float := 0
      let mut sep := ","
      if isJoin then
        if !(a0 matches .undef) then
          match ← catchJS (do pure (Except.ok (← core.toStr a0))) (fun e => pure (Except.error e)) with
          | .ok t => sep := t
          | .error e => closeWith e
      else
        match a1 with
        | .undef => pure ()
        | .num x =>
          if x.isNaN || (x.isFinite && toIntegerOrInf x != x) then
            closeWith (.throw (← mkError .type "Iterator.prototype.includes: skippedElements is not an integral number"))
          if x < 0 then closeWith (.throw (← mkError .range "Iterator.prototype.includes: skippedElements is negative"))
          if x.isFinite && x > 9007199254740991 then
            closeWith (.throw (← mkError .range "Iterator.prototype.includes: skippedElements is too large"))
          toSkip := x
        | _ => closeWith (.throw (← mkError .type "Iterator.prototype.includes: skippedElements is not a number"))
      let next ← core.getV thisV "next"
      let mut skipped : Float := 0
      let mut acc := ""
      let mut first := true
      for _ in [0:1000000000] do
        tick
        let r ← core.callV next thisV #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← core.getV r "done") then break
        let v ← core.getV r "value"
        if isJoin then
          let part ← match v with
            | .undef | .null => pure ""
            | _ => match ← catchJS (do pure (Except.ok (← core.toStr v))) (fun e => pure (Except.error e)) with
              | .ok t => pure t
              | .error e => do closeWith e; pure ""
          acc := (if first then acc else acc ++ sep) ++ part
          checkStrLen acc.utf8ByteSize
          first := false
        else if skipped < toSkip then skipped := skipped + 1
        else if sameValueZero v a0 then
          core.iterClose thisV
          return .bool true
      if isJoin then pure (.str (Str.canonical acc)) else pure (.bool false)
    | (.x (.iterEager k)) =>
      if !thisV.isObj then throwErr .type "Iterator.prototype method called on a non-object"
      if k != 1 && !(← isCallable a0) then
        core.iterClose thisV
        throwErr .type "Iterator.prototype method: the callback is not a function"
      let next ← core.getV thisV "next"
      let step : M (Option Value) := do
        let r ← core.callV next thisV #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← core.getV r "done") then pure none else pure (some (← core.getV r "value"))
      -- a callback that throws closes the iterator, then the error goes on (§7.4.12)
      let guarded (f : M Value) : M Value := tryCatch f fun e => do
        match e with
        | .throw _ =>
          catchJS (core.iterClose thisV) fun _ => pure ()
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
          acc ← guarded (core.callV a0 .undef #[acc, v, .num (Float.ofNat i)])
        else if k == 1 then out := out.push v
        else
          let res ← guarded (core.callV a0 .undef #[v, .num (Float.ofNat i)])
          if k == 3 && toBool res then
            core.iterClose thisV
            return .bool true
          if k == 4 && !toBool res then
            core.iterClose thisV
            return .bool false
          if k == 5 && toBool res then
            core.iterClose thisV
            return v
        i := i + 1
      match k with
      | 0 => if haveAcc then pure acc else throwErr .type "Reduce of empty iterator with no initial value"
      | 1 => newArray out
      | 3 => pure (.bool false)
      | 4 => pure (.bool true)
      | _ => pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: `next` and `return` of the iterator helper objects. `r` is the realm `moreNative` read. -/
def moreNativeIterHelper (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    match id with
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
        if id == (.x .helperNext) then return ← core.callV (field helperNextKey) it #[]
        let ret ← core.getV it "return"
        match ret with
        | .undef | .null => return ← result .undef true
        | f => return ← core.callV f it #[]
      if hiddenFlag o helperRunning then throwErr .type "Iterator helper is already running"
      if id == (.x .helperReturn) && kind == 7 then
        if !(hiddenFlag o helperDone) then
          setF helperDone (.bool true)
          let cur ← core.elemsOf it
          let m := cur.size / 2
          let mut err : Option Value := none
          for j in [0:m] do
            let i := m - 1 - j
            match cur[2 * i]! with
            | .null => pure ()
            | iv =>
              let r ← catchJS (do core.iterClose iv; pure none) fun e => match e with
                | .throw v => pure (some v)
                | a => throw a
              if err.isNone then err := r
          if let some v := err then throw (.throw v)
        return ← result .undef true
      if id == (.x .helperReturn) then
        if !(hiddenFlag o helperDone) then
          setF helperDone (.bool true)
          match field helperInner with
          | .obj _ => catchJS (core.iterClose (field helperInner)) fun _ => pure ()
          | _ => pure ()
          core.iterClose it
        return ← result .undef true
      if hiddenFlag o helperDone then return ← result .undef true
      if kind == 6 then
        -- Iterator.concat's closure (§27.1.3.2.2): each iterable's iterator in turn, its
        -- values yielded again; `helperCount` the next iterable, `helperFn` the inner `next`
        let items ← core.elemsOf it
        setF helperRunning (.bool true)
        let out ← catchJS (do
          let mut answer : Option Value := none
          for _ in [0:1000000000] do
            let o ← getObj hid
            let inner := match o.props.get? helperInner with | some (.data v ..) => v | _ => .undef
            if inner.isObj then
              let nx := match o.props.get? helperFn with | some (.data v ..) => v | _ => .undef
              let r ← core.callV nx inner #[]
              if !r.isObj then throwErr .type "Iterator result is not an object"
              if !toBool (← core.getV r "done") then
                answer := some (← result (← core.getV r "value") false)
                break
              setF helperInner .undef
            else
              let count := match o.props.get? helperCount with | some (.data (.num x) ..) => x.toUInt64.toNat | _ => 0
              if 2 * count + 1 ≥ items.size then
                setF helperDone (.bool true)
                answer := some (← result .undef true)
                break
              let iter ← core.callV items[2 * count + 1]! items[2 * count]! #[]
              if !iter.isObj then throwErr .type "Iterator.concat: the iterator is not an object"
              setF helperCount (.num (Float.ofNat (count + 1)))
              setF helperFn (← core.getV iter "next")
              setF helperInner iter
          pure answer) fun e => do
            setF helperRunning (.bool false)
            setF helperDone (.bool true)
            throw e
        setF helperRunning (.bool false)
        return ← match out with
          | some v => pure v
          | none => result .undef true
      if kind == 7 then
        -- IteratorZip's closure (§27.1.3.2.3): one value of each iterator a step
        let slots ← core.elemsOf it
        let m := slots.size / 2
        let hf (k : String) : Value := match o.props.get? k with | some (.data v ..) => v | _ => .undef
        let mode := match hf zipModeKey with | .num x => x.toUInt64.toNat | _ => 0
        let pads ← match hf zipPadKey with | .undef => pure #[] | v => core.elemsOf v
        let keysV := hf zipKeysKey
        let setSlot (i : Nat) (v : Value) : M Unit := do
          if let .obj aid := it then modifyObj aid fun ob => match ob.kind with
            | .array es => { ob with kind := .array (es.set! (2 * i) v) }
            | _ => ob
        -- IteratorCloseAll (§7.4.12): the open iterators but `skip`, last first; an error of the
        -- first close is the answer unless one is already thrown
        let closeOthers (skip : Nat) (thrown : Bool) : M Unit := do
          let cur ← core.elemsOf it
          let mut err : Option Value := none
          for j in [0:m] do
            let i := m - 1 - j
            if i != skip then
              match cur[2 * i]! with
              | .null => pure ()
              | iv =>
                let r ← catchJS (do core.iterClose iv; pure none) fun e => match e with
                  | .throw v => pure (some v)
                  | a => throw a
                if err.isNone && !thrown then err := r
          if let some v := err then throw (.throw v)
        if m == 0 then
          setF helperDone (.bool true)
          return ← result .undef true
        setF helperRunning (.bool true)
        let out ← catchJS (do
          let mut results : Array Value := #[]
          let mut finished := false
          for i in [0:m] do
            if finished then break
            let cur ← core.elemsOf it
            match cur[2 * i]! with
            | .null => results := results.push (pads.getD i .undef)
            | iv =>
              -- IteratorStepValue; an abrupt step closes the others
              let step ← catchJS (do
                  let r ← core.callV cur[2 * i + 1]! iv #[]
                  if !r.isObj then throwErr .type "Iterator result is not an object"
                  if toBool (← core.getV r "done") then pure (Except.ok none)
                  else pure (Except.ok (some (← core.getV r "value")))) fun e => pure (Except.error e)
              match step with
              | .error e =>
                setSlot i .null
                closeOthers i true
                throw e
              | .ok (some v) => results := results.push v
              | .ok none =>
                setSlot i .null
                if mode == 0 then
                  closeOthers i false
                  finished := true
                else if mode == 2 then
                  if i != 0 then
                    closeOthers i true
                    throwErr .type "Iterator.zip: the iterators are of different lengths (strict)"
                  for k in [1:m] do
                    let cur2 ← core.elemsOf it
                    let ik := cur2[2 * k]!
                    let r2 ← catchJS (do
                        let r ← core.callV cur2[2 * k + 1]! ik #[]
                        if !r.isObj then throwErr .type "Iterator result is not an object"
                        pure (Except.ok (toBool (← core.getV r "done")))) fun e => pure (Except.error e)
                    match r2 with
                    | .error e =>
                      setSlot k .null
                      closeOthers k true
                      throw e
                    | .ok false =>
                      closeOthers 1000000000 true
                      throwErr .type "Iterator.zip: the iterators are of different lengths (strict)"
                    | .ok true => setSlot k .null
                  finished := true
                else
                  let openN := match hf zipOpenKey with | .num x => x.toUInt64.toNat | _ => m
                  let o' ← getObj hid
                  let openNow := match o'.props.get? zipOpenKey with | some (.data (.num x) ..) => x.toUInt64.toNat | _ => openN
                  setF zipOpenKey (.num (Float.ofNat (openNow - 1)))
                  if openNow ≤ 1 then finished := true
                  else results := results.push (pads.getD i .undef)
          if finished then
            setF helperDone (.bool true)
            pure none
          else
            match keysV with
            | .undef => pure (some (← newArray results))
            | kv =>
              let ks ← core.elemsOf kv
              let ob ← alloc { proto := .null }
              for i in [0:min ks.size results.size] do
                defineOwn ob (← core.toKey ks[i]!) (.data results[i]! true true true)
              pure (some (.obj ob))) fun e => do
            setF helperRunning (.bool false)
            setF helperDone (.bool true)
            throw e
        setF helperRunning (.bool false)
        return ← match out with
          | some v => result v false
          | none => result .undef true
      let next := field helperNextKey
      let fn := field helperFn
      let stepOuter : M (Option Value) := do
        let r ← core.callV next it #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        if toBool (← core.getV r "done") then pure none else pure (some (← core.getV r "value"))
      let finish : M Value := do setF helperDone (.bool true); result .undef true
      let callFn (args : Array Value) : M Value :=
        tryCatch (core.callV fn .undef args) fun e => do
          match e with
          | .throw _ =>
            setF helperDone (.bool true)
            catchJS (core.iterClose it) fun _ => pure ()
            throw e
          | _ => throw e
      if kind == 8 || kind == 9 then
        -- chunks: up to `size` values a step, the last chunk partial; windows: each run of
        -- `size` neighbours, or with "allow-partial" all the values once when they are fewer
        let size := match fn with | .num x => x.toUInt64.toNat | _ => 1
        let allowPartial := match field helperCount with | .num x => x == 1 | _ => false
        let saved ← if kind == 9 && (field helperInner).isObj then core.elemsOf (field helperInner) else pure #[]
        setF helperRunning (.bool true)
        let out ← catchJS (do
          let mut buf : Array Value := saved
          let mut answer : Option Value := none
          for _ in [0:1000000000] do
            tick
            match ← stepOuter with
            | none =>
              setF helperDone (.bool true)
              if (kind == 8 && !buf.isEmpty) || (kind == 9 && allowPartial && !buf.isEmpty && buf.size < size) then
                answer := some (← result (← newArray buf) false)
              break
            | some v =>
              if kind == 9 && buf.size == size then buf := buf.eraseIdxIfInBounds 0
              buf := buf.push v
              if kind == 9 then setF helperInner (← newArray buf)
              if buf.size == size then
                answer := some (← result (← newArray buf) false)
                break
          pure answer) fun e => do
            setF helperRunning (.bool false)
            setF helperDone (.bool true)
            throw e
        setF helperRunning (.bool false)
        return ← match out with
          | some v => pure v
          | none => result .undef true
      setF helperRunning (.bool true)
      let out ← catchJS (do
        let mut answer : Option Value := none
        for _ in [0:1000000000] do
          let o ← getObj hid
          let count := match o.props.get? helperCount with | some (.data (.num x) ..) => x.toUInt64.toNat | _ => 0
          let lim := match fn with | .num x => x | _ => 0
          if kind == 2 && Float.ofNat count ≥ lim then
            setF helperDone (.bool true)
            core.iterClose it
            answer := some (← result .undef true); break
          if kind == 4 then
            match o.props.get? helperInner with
            | some (.data inner ..) =>
              if inner.isObj then
                let r ← core.callV (← core.getV inner "next") inner #[]
                if !r.isObj then throwErr .type "Iterator result is not an object"
                if !toBool (← core.getV r "done") then
                  answer := some (← result (← core.getV r "value") false); break
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
              setF helperDone (.bool true); core.iterClose it
              throwErr .type "flatMap: the mapper did not return an object"
            let m ← core.getV mapped (symKey symIterator)
            let inner ← match m with
              | .undef | .null => pure mapped
              | f => core.callV f mapped #[]
            if !inner.isObj then throwErr .type "flatMap: the inner iterator is not an object"
            setF helperInner inner
        pure answer) fun e => do setF helperRunning (.bool false); throw e
      setF helperRunning (.bool false)
      match out with
      | some v => pure v
      | none => finish
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: Function, Error and Object additions (`@@hasInstance`, `Error.isError`, `stack`, AggregateError, `Object.hasOwn`, `__proto__`, `Proxy.revocable`, the Function constructors) and the host's realm hooks. `r` is the realm `moreNative` read. -/
def moreNativeObject (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x .fnHasInstance) =>
      -- §20.2.3.6: OrdinaryHasInstance(this, V): false for a non-callable `this`; a bound
      -- function asks its target; otherwise the prototype chain of V
      if !(← isCallable thisV) then return .bool false
      if let .obj cid := thisV then
        if let .bound t _ _ := (← getObj cid).kind then return .bool (← core.instOf a0 t)
      if !a0.isObj then return .bool false
      let p ← core.getV thisV "prototype"
      let .obj pid := p | throwErr .type "Function has non-object prototype in instanceof check"
      let mut cur := a0
      for _ in [0:100000] do
        let .obj o := cur | return .bool false
        let next ← match (← getObj o).kind with
          | .proxy .. => core.callNative .objectGetPrototypeOf .undef #[cur] none
          | _ => pure (← getObj o).proto
        match next with
        | .obj q => if q == pid then return .bool true else cur := next
        | _ => return .bool false
      pure (.bool false)
    | (.x .errorIsError) =>
      match a0 with
      | .obj id => pure (.bool (match (← getObj id).kind with | .error => true | _ => false))
      | _ => pure (.bool false)
    | (.x .speciesGetter) => pure thisV
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
    | (.x .objectHasOwn) =>
      let id ← core.toObj a0
      let k ← core.toKey a1
      pure (.bool (← core.ownDesc id k).isSome)
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
      match ← core.ownDesc oid "stack" with
      | some _ => core.putV thisV "stack" a0 true
      | none =>
        let o ← getObj oid
        match o.kind with
        | .proxy t hnd =>
          match ← core.proxyTrap hnd "defineProperty" with
          | some f =>
            let d ← newObject
            defineOwn d "value" (.data a0 true true true)
            defineOwn d "writable" (.data (.bool true) true true true)
            defineOwn d "enumerable" (.data (.bool true) true true true)
            defineOwn d "configurable" (.data (.bool true) true true true)
            if !toBool (← core.callV f hnd #[t, .str "stack", .obj d]) then
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
          let p ← core.getV nt "prototype"
          protoOr p nt (·.aggregateErrorProto)
        | none => pure (.obj r.aggregateErrorProto)
      let o ← alloc { proto, kind := .error }
      match a1 with
      | .undef => pure ()
      | v => setHidden o "message" (.str (← core.toStr v))
      -- InstallErrorCause (§20.5.8.1)
      if let .obj opts := argD args 2 then
        if ← core.hasProp opts "cause" then setHidden o "cause" (← core.getV (.obj opts) "cause")
      let errs ← core.iterToArray (← core.getIterator a0) #[]
      setHidden o "errors" (← newArray errs)
      pure (.obj o)
    | (.x .namedGetterSet) =>
      -- the host's function for the named properties of the global object (`namedGlobal`)
      defineOwn r.globalObj namedGetterKey (.data a0 false false false)
      pure .undef
    | (.x (.protoAccessor false)) =>
      -- get Object.prototype.__proto__ (B.2.2.1.1)
      let id ← core.toObj thisV
      core.callNative .objectGetPrototypeOf .undef #[.obj id] none
    | (.x (.protoAccessor true)) =>
      -- set Object.prototype.__proto__ (B.2.2.1.2)
      match thisV with
      | .undef | .null => throwErr .type "Object.prototype.__proto__ called on null or undefined"
      | .obj id =>
        match a0 with
        | .obj _ | .null =>
          if toBool (← core.callNative (.reflect 2) .undef #[.obj id, a0] none) then pure .undef
          else throwErr .type "Object.prototype.__proto__: the prototype of this object cannot be changed"
        | _ => pure .undef
      | _ => pure .undef
    | (.x (.dynFunction k)) =>
      -- CreateDynamicFunction (§20.2.1.1.1) for the generator, async and async generator kinds
      let strs ← args.toList.mapM (core.toStr)
      let (ps, body) := match strs.reverse with
        | [] => ([], "")
        | b :: rest => (rest.reverse, b)
      let kw := match k with | 1 => "function*" | 2 => "async function" | _ => "async function*"
      match (parseScript (dynFunctionSource kw ps body) false).map Resolve.script with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok { body := [.expr e], .. } =>
        core.evalExpr { env := 0, thisV := .obj r.globalObj, strict := false } e
      | .ok _ => throwErr .syntax "invalid function body"
    | (.x .realmTake) =>
      -- a test host's `$262.createRealm()`: the next realm the host made (`addRealm`)
      let h ← get
      match h.spareRealms[0]? with
      | none => throwErr .type "$262.createRealm: the host has no realm left to give"
      | some k =>
        set { h with spareRealms := h.spareRealms.extract 1 h.spareRealms.size }
        pure (h.realms.getD k {}).host
    | (.x .gcNoop) => pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: Temporal and the Date methods. `r` is the realm `moreNative` read. -/
def moreNativeDate (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    match id with
    | (.x .temporal) =>
      -- `n.temporal(op, ...)`: 0 regulate (y, m, d, reject) → [y, m, d] | null; 1 date facts
      -- (y, m, d) → [dayOfWeek, dayOfYear, weekOfYear, yearOfWeek, daysInMonth, daysInYear,
      -- inLeapYear]; 2 add (y, m, d, years, months, weeks, days, reject) → [y, m, d] | null;
      -- 3 until (y1, m1, d1, y2, m2, d2, largest) → [years, months, weeks, days]; 4 epoch days;
      -- 5 date of epoch days; 6 date-time string, 7 time string → parts | null; 8 duration
      -- string → ten fields | null; 9 date string; 10 time string (h, mi, s, ns, precision);
      -- 11 round (x, increment, mode) → BigInt; 12 balance time (ns) → [days, h, mi, s, ms, us,
      -- ns]; 13 date-time within limits (y, m, d, time ns); 14 compare dates; 15 a time zone
      -- identifier → [0 UTC | 1 offset, offset ns] | null; 16 an offset string (ns, full)
      let int (i : Nat) : Int := match argD args i with
        | .num x => if x.isFinite then truncInt x else 0
        | .big b => b
        | _ => 0
      let nat (i : Nat) : Nat := (int i).toNat
      let num (x : Int) : Value := .num (Float.ofInt x)
      let arr (xs : List Value) : M Value := newArray xs.toArray
      let date3 (r : Int × Nat × Nat) : M Value := arr [num r.1, num r.2.1, num r.2.2]
      let parts (p : Temporal.DateTimeParts) : M Value :=
        arr [num p.year, num p.month, num p.day, .bool p.hasDate, .bool p.hasTime, num p.hour,
             num p.minute, num p.second, num p.fracNs, num p.offsetKind, .big p.offsetNs,
             .str p.timeZone, .str p.calendar]
      let str (i : Nat) : M String := do match argD args i with
        | .str s => pure s
        | _ => throwErr .type "Temporal: a string was expected"
      match int 0 with
      | 0 => match Temporal.regulateDate (int 1) (int 2) (int 3) (toBool (argD args 4)) with
        | some r => date3 r
        | none => pure .null
      | 1 =>
        let (y, m, d) := (int 1, nat 2, nat 3)
        let (w, wy) := Temporal.weekOfYear y m d
        arr [num (Temporal.dayOfWeek y m d), num (Temporal.dayOfYear y m d), num w, num wy,
             num (Temporal.daysInMonth y m), num (Temporal.daysInYear y), .bool (Temporal.isLeapYear y)]
      | 2 => match Temporal.addDate (int 1) (nat 2) (nat 3) (int 4) (int 5) (int 6) (int 7) (toBool (argD args 8)) with
        | some r => date3 r
        | none => pure .null
      | 3 =>
        let (a, b, c, d) := Temporal.dateUntil (int 1, nat 2, nat 3) (int 4, nat 5, nat 6) (nat 7)
        arr [num a, num b, num c, num d]
      | 4 => pure (num (Temporal.epochDays (int 1) (nat 2) (nat 3)))
      | 5 => date3 (Temporal.fromEpochDays (int 1))
      | 6 => match Temporal.parseDateTime (← str 1) with
        | some p => parts p
        | none => pure .null
      | 7 => match Temporal.parseTimeString (← str 1) with
        | some p => parts p
        | none => pure .null
      | 8 => match Temporal.parseDuration (← str 1) with
        | some xs => arr (xs.toList.map num)
        | none => pure .null
      | 9 => pure (.str (Temporal.formatDate (int 1) (nat 2) (nat 3)))
      | 10 =>
        let prec : Option Int := match argD args 5 with | .undef => none | _ => some (int 5)
        pure (.str (Temporal.formatTime (nat 1) (nat 2) (nat 3) (nat 4) prec))
      | 11 => pure (.big (Temporal.roundIncrement (int 1) (nat 2) (nat 3)))
      | 12 =>
        let (dd, h, mi, s, ms, us, ns) := Temporal.balanceTime (int 1)
        arr [num dd, num h, num mi, num s, num ms, num us, num ns]
      | 13 => pure (.bool (Temporal.dateTimeWithinLimits (int 1) (nat 2) (nat 3) (int 4)))
      | 14 => pure (num (Temporal.compareDate (int 1, nat 2, nat 3) (int 4, nat 5, nat 6)))
      | 15 => match Temporal.parseTimeZoneId (← str 1) with
        | some (k, ns) => arr [num k, .big ns]
        | none => pure .null
      | 16 => pure (.str (Temporal.formatOffset (int 1) (toBool (argD args 2))))
      | _ => throwErr .type "temporal: unknown operation"
    | (.x .dateUTC) =>
      let mut xs : Array Float := #[]
      for i in [0:min 7 args.size] do xs := xs.push (← core.toNum args[i]!)
      pure (.num (Date.timeClip (dateOfParts xs)))
    | (.x .dateParse) => pure (.num (Date.parse (← core.toStr a0)))
    | (.x (.dateMethod k)) =>
      if k == 32 then
        -- toJSON (§21.4.4.37)
        let o ← core.toObj thisV
        let tv ← core.toPrim (.obj o) "number"
        if let .num x := tv then
          if !x.isFinite then return .null
        let f ← core.getV (.obj o) "toISOString"
        if !(← isCallable f) then throwErr .type "toISOString is not a function"
        return ← core.callV f (.obj o) #[]
      if k == 39 then
        -- @@toPrimitive (§21.4.4.45)
        if !thisV.isObj then throwErr .type "Date.prototype[Symbol.toPrimitive] called on a non-object"
        match a0 with
        | .str "string" | .str "default" => return ← core.tryMethods thisV ["toString", "valueOf"]
        | .str "number" => return ← core.tryMethods thisV ["valueOf", "toString"]
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
        if k == 27 then return ← set (Date.timeClip (← core.toNum a0))
        if k == 28 then
          -- setYear (Annex B.2.3.2)
          let y ← core.toNum a0
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
        for i in [0:min most (max 1 args.size)] do given := given.push (← core.toNum (argD args i))
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
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: `Promise.try`, `Promise.withResolvers`, the capability executor, thenable functions and `import()`. `r` is the realm `moreNative` read. -/
def moreNativePromise (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x .promiseTry) =>
      -- §27.2.4.8 Promise.try: the callback's completion; a normal one is PromiseResolve(C, v)
      -- (a promise of C is not wrapped again), an abrupt one rejects a new capability
      if !thisV.isObj then throwErr .type "Promise.try called on a non-object"
      let x ← catchJS (do pure (Except.ok (← core.callV a0 .undef (args.extract 1 args.size)))) (fun e => pure (Except.error e))
      match x with
      | .ok v => core.callNative .promiseResolveStatic thisV #[v] none
      | .error (.throw e) =>
        let cap ← core.callNative (.x .promiseWithResolvers) thisV #[] none
        let _ ← core.callV (← core.getV cap "reject") .undef #[e]
        core.getV cap "promise"
      | .error a => throw a
    | (.x .promiseWithResolvers) =>
      -- §27.2.4.8 Promise.withResolvers: NewPromiseCapability(this) (§27.2.1.5)
      if !(← isConstructor thisV) then throwErr .type "Promise.withResolvers: this is not a constructor"
      let cap ← alloc { proto := .null }
      let exec ← anonFn (.x .capabilityExecutor) #[.obj cap] 2
      let p ← core.construct thisV #[exec] thisV
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
    | (.x .dynImport) =>
      -- EvaluateImportCall (§13.3.10.1): the specifier as a string, then the options' `with`
      -- object, whose values must be strings (steps 7 to 10); an abrupt step rejects the promise.
      let pid ← newPromise
      let x ← catchJS (do
          let spec ← core.toStr a0
          let mut ty := ""
          match a1 with
          | .undef => pure ()
          | .obj _ =>
            match ← core.getV a1 "with" with
            | .undef => pure ()
            | .obj wid =>
              for k in ← core.ownKeysOf wid do
                if isSymKey k || isPrivKey k then continue
                let some d ← core.ownDesc wid k | continue
                if !d.enumerable then continue
                match ← core.getV (.obj wid) k with
                | .str v => if k == "type" then ty := Str.toHost v
                | _ => throwErr .type "import(): the value of an import attribute must be a string"
            | _ => throwErr .type "import(): the 'with' option must be an object"
          | _ => throwErr .type "import(): the second argument must be an object"
          pure (Except.ok (spec, ty)))
        (fun a => pure (Except.error a))
      match x with
      | .error (.throw e) => core.rejectPromise pid e
      | .error a => throw a
      | .ok (spec, ty) =>
        if args.size ≥ 3 then
          -- `import.source(x)` (the source phase imports proposal): every module this host loads
          -- is a Source Text Module Record, whose GetModuleSource throws a SyntaxError
          core.rejectPromise pid (← mkError .syntax "import.source(): a JavaScript module has no source phase representation")
        else
        match (← get).importQueue with
        | some q => modify fun h => { h with importQueue := some (q.push (Str.toHost spec, ty, pid)) }
        | none => core.rejectPromise pid (← mkError .type "import() is not supported in this script")
      pure (.obj pid)
    | (.x (.promiseThenableFn reject)) =>
      -- bound arguments: the promise and the pair's [[AlreadyResolved]] record
      match a0, a1 with
      | .obj pid, .obj record =>
        if !(← getObj record).props.contains "done" then
          setHidden record "done" (.bool true)
          if reject then core.rejectPromise pid (argD args 2) else core.resolvePromise pid (argD args 2)
        pure .undef
      | _, _ => pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: String, RegExp, Number and Symbol additions (the HTML methods, `compile`, `RegExp.escape`, `toExponential`, `toPrecision`, `localeCompare`, `String.raw`, `Symbol.for`, `isWellFormed`). `r` is the realm `moreNative` read. -/
def moreNativeString (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.regexpSym k)) => core.regexpSymbol k thisV args
    | (.x (.stringHtml k)) =>
      -- CreateHTML (Annex B.2.2.2.1): RequireObjectCoercible(this), ToString, then the
      -- attribute's value with each " as &quot;
      let (_, tag, attr) := htmlMethods.getD k ("", "", "")
      match thisV with
      | .undef | .null => throwErr .type "String.prototype HTML method called on null or undefined"
      | _ => pure ()
      let str ← core.toStr thisV
      let open_ ← if attr.isEmpty then pure ("<" ++ tag) else do
        let v ← core.toStr a0
        pure ("<" ++ tag ++ " " ++ attr ++ "=\"" ++ v.replace "\"" "&quot;" ++ "\"")
      pure (.str (Str.canonical (open_ ++ ">" ++ str ++ "</" ++ tag ++ ">")))
    | (.x .regexpCompile) =>
      -- Annex B.2.4.1: a RegExp object made again from a pattern and flags (or from another
      -- RegExp's source and flags), lastIndex set to 0
      let .obj oid := thisV | throwErr .type "RegExp.prototype.compile called on an incompatible receiver"
      let .regexp .. := (← getObj oid).kind | throwErr .type "RegExp.prototype.compile called on an incompatible receiver"
      if hiddenFlag (← getObj oid) regexpNoLegacyKey then throwErr .type "RegExp.prototype.compile called on a RegExp subclass instance"
      let (p, f) ← match a0 with
        | .obj pid => match (← getObj pid).kind with
          | .regexp _ src fl =>
            if !(a1 matches .undef) then throwErr .type "Cannot supply flags when constructing one RegExp from another"
            pure (src, fl)
          | _ => pure ((← core.toStr a0), ← (match a1 with | .undef => pure "" | v => core.toStr v))
        | .undef => pure ("", ← (match a1 with | .undef => pure "" | v => core.toStr v))
        | _ => pure ((← core.toStr a0), ← (match a1 with | .undef => pure "" | v => core.toStr v))
      match Re.compile p f with
      | .error e => throwErr .syntax (if e.startsWith "SyntaxError: " then (e.drop 13).toString else e)
      | .ok re =>
        modifyObj oid fun o => { o with kind := .regexp re p f }
        core.putV thisV "lastIndex" (.num 0) true
        pure thisV
    | (.x .regexpEscape) =>
      match a0 with
      | .str s => pure (.str (regexpEscapeStr s.toList))
      | _ => throwErr .type "RegExp.escape requires a string"
    | (.x .numberToExponential) | (.x .numberToPrecision) =>
      if (← thisDate? thisV).isSome then throwErr .type "Number.prototype method requires that 'this' be a Number"
      let x ← match ← thisPrim thisV with
        | .num x => pure x
        | _ => throwErr .type "Number.prototype method requires that 'this' be a Number"
      if id == (.x .numberToPrecision) && (a0 matches .undef) then return .str (numToString x)
      let f := toIntegerOrInf (← core.toNum a0)
      if !x.isFinite then return .str (numToString x)
      -- 64-bit fast paths with the exact path behind them (JS/NumFmt.lean, issue 1076)
      if id == (.x .numberToExponential) then
        if f < 0 || f > 100 then throwErr .range "toExponential() argument must be between 0 and 100"
        if a0 matches .undef then
          -- as many digits as Number::toString gives
          return .str (NumFmt.expoShortest x)
        pure (.str (NumFmt.expoOf x f.toUInt64.toNat))
      else
        if f < 1 || f > 100 then throwErr .range "toPrecision() argument must be between 1 and 100"
        pure (.str (NumFmt.precisionOf x f.toUInt64.toNat))
    | (.x .stringLocaleCompare) =>
      match ← thisPrim thisV with
      | .undef | .null => throwErr .type "String.prototype.localeCompare called on null or undefined"
      | _ => pure ()
      let s ← core.toStr (← thisPrim thisV)
      let t ← core.toStr a0
      let a := Str.units s
      let b := Str.units t
      pure (.num (if a == b then 0 else if decide (a < b) then -1 else 1))
    | (.x .stringNormalize) =>
      -- §22.1.3.15: RequireObjectCoercible(this), ToString, the form (NFC when undefined),
      -- a RangeError for any other form. A lone surrogate is held as a character of plane 16
      -- (`Str.loneChar`), which has class 0 and no decomposition, so it is left as it is, as a
      -- lone surrogate is by the normalization of other engines.
      match thisV with
      | .undef | .null => throwErr .type "String.prototype.normalize called on null or undefined"
      | _ => pure ()
      let s ← core.toStr thisV
      let form ← match a0 with
        | .undef => pure "NFC"
        | v => core.toStr v
      match form with
      | "NFC" => pure (.str (Unicode.Normalization.nfc s))
      | "NFD" => pure (.str (Unicode.Normalization.nfd s))
      | "NFKC" => pure (.str (Unicode.Normalization.nfkc s))
      | "NFKD" => pure (.str (Unicode.Normalization.nfkd s))
      | _ => throwErr .range "The normalization form should be one of NFC, NFD, NFKC, NFKD."
    | (.x .symbolFor) | (.x .symbolKeyFor) =>
      -- the GlobalSymbolRegistry is one for all realms (§20.4.2.2): it hangs on realm 0's global
      let h ← get
      let gReg := if h.curRealm == 0 then r.globalObj else (h.realms.getD 0 {}).realm.globalObj
      let reg ← match (← getObj gReg).props.get? symbolRegistryKey with
        | some (.data (.obj id) ..) => pure id
        | _ => do
          let id ← alloc { proto := .null }
          setHidden gReg symbolRegistryKey (.obj id)
          pure id
      if id == (.x .symbolFor) then
        let key ← core.toStr a0
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
      let cooked ← core.toObj a0
      let raw ← core.toObj (← core.getV (.obj cooked) "raw")
      let len := toIntegerOrInf (← core.toNum (← core.getV (.obj raw) "length"))
      let count := if len ≤ 0 then 0 else len.toUInt64.toNat
      charge (count / 8)
      let mut out := ""
      for i in [0:count] do
        out := Str.jsAppend out (← core.toStr (← core.getV (.obj raw) (toString i)))
        if i + 1 < count && i + 1 < args.size then
          out := Str.jsAppend out (← core.toStr (argD args (i + 1)))
      pure (.str out)
    | (.x .stringIsWellFormed) | (.x .stringToWellFormed) =>
      let tp ← thisPrim thisV
      match tp with
      | .undef | .null => throwErr .type "String.prototype method called on null or undefined"
      | _ => pure ()
      let s ← core.toStr tp
      if id == (.x .stringIsWellFormed) then pure (.bool (Str.isWellFormed s)) else pure (.str (Str.toWellFormed s))
    | _ => throwErr .type "not a function"

/-- The Set methods of two sets (§24.2.4 to §24.2.4.20: 0 `union`, 1 `intersection`, 2 `difference`, 3 `symmetricDifference`, 4 `isSubsetOf`, 5 `isSupersetOf`, else `isDisjointFrom`), after the receiver `sid` (entries `es`) and the argument's set record (`a0`, its `size`, `has` and `keys`) are read. -/
def setMethodRun (core : CoreFn H) (r : Realm) (k : Nat) (sid : Nat) (es : Array (Option (Value × Value))) (a0 : Value) (has : Value) (keys : Value) (otherSize : Float) : M Value := do
    let mine : Array Value := es.filterMap (·.map (·.1))
    let inThis (v : Value) : M Bool := do
      match (← getObj sid).kind with
      | .coll _ _ idx => pure (collFind idx v).isSome
      | _ => pure false
    let canon (v : Value) : Value := match v with | .num x => if x == 0 then .num 0 else v | _ => v
    let otherKeys : M (Value × Value) := do
      let it ← core.callV keys a0 #[]
      if !it.isObj then throwErr .type "Set method: keys() did not return an object"
      pure (it, ← core.getV it "next")
    let stepKeys (it next : Value) : M (Option Value) := do
      let r ← core.callV next it #[]
      if !r.isObj then throwErr .type "Iterator result is not an object"
      if toBool (← core.getV r "done") then pure none else pure (some (canon (← core.getV r "value")))
    let otherHas (v : Value) : M Bool := do pure (toBool (← core.callV has a0 #[v]))
    let thisSize := Float.ofNat mine.size
    let mkSet (vs : Array Value) : M Value := do
      let mut o : Obj := { proto := (← getObj sid).proto, kind := .coll 1 #[] {} }
      for v in vs do o := collPut v v o
      -- %Set.prototype%, not the receiver's
      let sc ← core.getV (.obj r.globalObj) "Set"
      let sp ← core.getV sc "prototype"
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
          core.iterClose it
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
            core.iterClose it
            return .bool false
        pure (.bool true)

/-- Built-ins of `moreNative`: the Set methods of two sets and the collection methods shared by Map, Set and their weak kinds. `r` is the realm `moreNative` read. -/
def moreNativeSet (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    match id with
    | (.x (.collMethod kind op)) =>
      match thisV with
      | .obj c =>
        match (← getObj c).kind with
        | .coll k _ _ =>
          if k != kind then throwErr .type "Collection method called on a collection of another kind"
        | _ => throwErr .type "Collection method called on an incompatible receiver"
      | _ => throwErr .type "Collection method called on an incompatible receiver"
      core.callNative (collOps.getD op .mapHas) thisV args newTarget
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
      let rawSize ← core.getV a0 "size"
      let numSize ← core.toNum rawSize
      if numSize.isNaN then throwErr .type "Set method: the argument's size is not a number"
      let otherSize := toIntegerOrInf numSize
      if otherSize < 0 then throwErr .range "Set method: the argument's size is negative"
      let has ← core.getV a0 "has"
      if !(← isCallable has) then throwErr .type "Set method: the argument's has is not a function"
      let keys ← core.getV a0 "keys"
      if !(← isCallable keys) then throwErr .type "Set method: the argument's keys is not a function"
      setMethodRun core r k sid es a0 has keys otherSize
    | _ => throwErr .type "not a function"

/-- Is the Symbol `sid` a value of the GlobalSymbolRegistry `reg` (a symbol `Symbol.for` made)? -/
def symRegistered (reg : Obj) (sid : Nat) : Bool :=
  reg.keys.any fun k => match reg.props.get? k with
    | some (.data (.sym j) ..) => j == sid
    | _ => false

/-- CanBeHeldWeakly (§9.13), given the GlobalSymbolRegistry `reg` if there is one: an object,
or a Symbol that `Symbol.for` did not make. -/
def holdableIn (reg : Option Obj) : Value → Bool
  | .obj _ => true
  | .sym sid => match reg with
    | some o => !symRegistered o sid
    | none => true
  | _ => false

/-- CanBeHeldWeakly (§9.13): a key of a WeakMap or WeakSet, the target of a WeakRef, the target
or unregister token of a FinalizationRegistry. An object asks nothing of the heap; a Symbol looks
in the registry, which hangs on realm 0's global object (as `Symbol.for` puts it there). -/
def canBeHeldWeakly (v : Value) : M Bool := do
  match v with
  | .obj _ => pure true
  | .sym _ =>
    let h ← get
    let g := if h.curRealm == 0 then h.realm.globalObj else (h.realms.getD 0 {}).realm.globalObj
    let reg ← match (← getObj g).props.get? symbolRegistryKey with
      | some (.data (.obj id) ..) => pure (some (← getObj id))
      | _ => pure none
    pure (holdableIn reg v)
  | _ => pure false

/-- Built-ins of `moreNative`: WeakRef, FinalizationRegistry, `groupBy` and the Map upsert methods. `r` is the realm `moreNative` read. -/
def moreNativeWeak (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.groupBy isMap)) =>
      -- GroupBy (§7.3.35): the items of an iterable, by key (property key or SameValueZero)
      if !(← isCallable a1) then throwErr .type "groupBy: the callback is not a function"
      let items ← core.iterToArray (← core.getIterator a0) #[]
      let mut keys : Array Value := #[]
      let mut groups : Array (Array Value) := #[]
      for i in [0:items.size] do
        let kv ← core.callV a1 .undef #[items[i]!, .num (Float.ofNat i)]
        let key ← if isMap then pure (match kv with | .num x => if x == 0 then .num 0 else kv | _ => kv)
          else do pure (keyValue (← core.toKey kv))
        match keys.findIdx? (sameValue · key) with
        | some j => groups := groups.modify j (·.push items[i]!)
        | none =>
          keys := keys.push key
          groups := groups.push #[items[i]!]
      if isMap then
        let mut o : Obj := { kind := .coll 0 #[] {} }
        for j in [0:keys.size] do o := collPut keys[j]! (← newArray groups[j]!) o
        let mc ← core.getV (.obj r.globalObj) "Map"
        let mp ← core.getV mc "prototype"
        pure (.obj (← alloc { o with proto := mp }))
      else
        let res ← alloc { proto := .null }
        for j in [0:keys.size] do
          defineOwn res (← core.toKey keys[j]!) (.data (← newArray groups[j]!) true true true)
        pure (.obj res)
    | (.x .weakRefCtor) =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Constructor WeakRef requires 'new'"
      if !(← canBeHeldWeakly a0) then throwErr .type "WeakRef: the target cannot be held weakly"
      let pp ← core.getV nt "prototype"
      let proto ← if pp.isObj then pure pp else core.getV (← core.getV (.obj (← funRealm nt).globalObj) "WeakRef") "prototype"
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
      let pp ← core.getV nt "prototype"
      let proto ← if pp.isObj then pure pp else core.getV (← core.getV (.obj (← funRealm nt).globalObj) "FinalizationRegistry") "prototype"
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
        if !(← canBeHeldWeakly a0) then throwErr .type "FinalizationRegistry.register: the target cannot be held weakly"
        if sameValue a0 a1 then throwErr .type "FinalizationRegistry.register: the target and the held value are the same"
        let tok := argD args 2
        match tok with
        | .undef => pure ()
        | _ =>
          if !(← canBeHeldWeakly tok) then
            throwErr .type "FinalizationRegistry.register: the unregister token cannot be held weakly"
          modifyObj tokens fun o => { o with kind := .array (held.push tok) }
        pure .undef
      else
        -- unregister(unregisterToken): were there cells with the token
        if !(← canBeHeldWeakly a0) then throwErr .type "FinalizationRegistry.unregister: the token cannot be held weakly"
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
      if weak && !(← canBeHeldWeakly a0) then throwErr .type "Invalid value used as weak collection key"
      if toBool (← core.callNative .mapHas thisV #[a0] none) then core.callNative .mapGet thisV #[a0] none
      else
        let key := match a0 with | .num x => if x == 0 then Value.num 0 else a0 | _ => a0
        let v ← if computed then core.callV a1 .undef #[key] else pure a1
        let _ ← core.callNative .mapSet thisV #[a0, v] none
        pure v
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: the Array methods that copy (`toReversed`, `toSorted`, `toSpliced`, `with`) and their kin. `r` is the realm `moreNative` read. -/
def moreNativeArray (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.arrayMethod k)) =>
      -- toSorted checks the comparator before ToObject and LengthOfArrayLike.
      if k == 3 && !(a0 matches .undef) && !(← isCallable a0) then
        throwErr .type "The comparison function must be either a function or undefined"
      -- generic over array-likes: ToObject(this), LengthOfArrayLike (§23.1.3)
      let oid ← core.toObj thisV
      let o := Value.obj oid
      let lenF := toIntegerOrInf (← core.toNum (← core.getV o "length"))
      let len := if lenF ≤ 0 then 0 else if lenF > 9007199254740991 then 9007199254740991 else lenF.toUInt64.toNat
      let rel (v : Value) (dflt : Nat) : M Nat := do
        match v with
        | .undef => pure dflt
        | v => pure (relIndex (toIntegerOrInf (← core.toNum v)) len)
      let valuesUpTo (m : Nat) : M (Array Value) := do
        let mut out := Array.emptyWithCapacity m
        for i in [0:m] do out := out.push (← core.getV o (toString i))
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
          if (← core.hasProp oid fk) then core.putV o tk (← core.getV o fk) true
          else deleteOwn oid tk
        pure o
      | 1 =>
        if !(← isCallable a0) then throwErr .type "reduceRight: the callback is not a function"
        if len > 10000000 then throwErr .range "reduceRight: too many elements"
        let mut acc := a1
        let mut got : Bool := args.size ≥ 2
        for j in [0:len] do
          let i := len - 1 - j
          if (← core.hasProp oid (toString i)) then
            let v ← core.getV o (toString i)
            if got then acc ← core.callV a0 .undef #[acc, v, .num (Float.ofNat i), o]
            else
              acc := v
              got := true
        if !got then throwErr .type "Reduce of empty array with no initial value"
        pure acc
      | 2 =>
        if len > 4294967295 then throwErr .range "Invalid array length"
        newArray (← valuesUpTo len).reverse
      | 3 =>
        if len > 4294967295 then throwErr .range "Invalid array length"
        newArray (← core.mergeSort a0 (← valuesUpTo len).toList).toArray
      | 4 =>
        let st ← rel a0 0
        let skip ← if args.size == 0 then pure 0 else if args.size == 1 then pure (len - st) else do
          let d := toIntegerOrInf (← core.toNum a1)
          pure (if d < 0 then 0 else min d.toUInt64.toNat (len - st))
        let items := args.extract (min 2 args.size) args.size
        let newLen := len + items.size - skip
        if Float.ofNat newLen > 9007199254740991 then throwErr .type "toSpliced: the length is too large"
        if newLen > 4294967295 then throwErr .range "Invalid array length"
        let mut out := Array.emptyWithCapacity newLen
        for i in [0:st] do out := out.push (← core.getV o (toString i))
        out := out ++ items
        for i in [st + skip:len] do out := out.push (← core.getV o (toString i))
        newArray out
      | _ =>
        let r := toIntegerOrInf (← core.toNum a0)
        let i := if r ≥ 0 then r else Float.ofNat len + r
        if i ≥ Float.ofNat len || i < 0 then throwErr .range "Invalid index for Array.prototype.with"
        if len > 4294967295 then throwErr .range "Invalid array length"
        -- §23.1.3.39: every index but the replaced one is read
        let at_ := i.toUInt64.toNat
        let mut vs := Array.emptyWithCapacity len
        for j in [0:len] do vs := vs.push (← if j == at_ then pure a1 else core.getV o (toString j))
        newArray vs
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: structured clone and classic scripts, for workers. `r` is the realm `moreNative` read. -/
def moreNativeClone (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
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
    | (.x .classicScript) | (.x .classicScriptHost) =>
      -- the source: the argument, or (`classicScriptHost`) the host's, which never becomes a
      -- value of the realm (a script of another origin: origin isolation, issue 518)
      let (src, muted, fromHost) ← match id with
        | .x .classicScriptHost => do
          match ← hostScript a0 with
          | some (src, muted) => pure (src, muted, true)
          | none => throwErr .type "runFetched: the host holds no script for this key"
        | _ => pure (← core.toStr a0, false, false)
      -- muted errors (HTML "report an exception"): any exception of the script ends it and the
      -- caller learns only that it threw (1), never the exception
      let mute (act : M Value) : M Value :=
        if muted then catchJS (do let _ ← act; pure (.num 0)) fun _ => pure (.num 1)
        else if fromHost then (do let _ ← act; pure (.num 0)) else act
      mute do
        -- GlobalDeclarationInstantiation (§16.1.7) and the statements, as `runScriptM` (which
        -- comes after this function), with no microtask checkpoint.
        match parseScript src false with
        | .error e => throwErr .syntax e
        | .ok sc =>
          let g := r.globalObj
          let ctx : Ctx := { env := 0, thisV := .obj g, strict := sc.strict }
          -- GlobalDeclarationInstantiation's checks (§16.1.7 steps 3 to 10), all before any binding
          -- is made: a lexical name that a var, a lexical binding or a non-configurable global
          -- property has is a SyntaxError; a function the global object cannot take
          -- (CanDeclareGlobalFunction) or a var it cannot take (CanDeclareGlobalVar) a TypeError
          let go ← getObj g
          let funNames := sc.body.filterMap fun st => match st with | .funDecl x _ => some x | _ => none
          let lexNames := sc.body.flatMap fun st => match st with
            | .decl .letK ds | .decl .constK ds => ds.flatMap (·.names)
            | .classDecl x _ => [x]
            | _ => []
          for x in lexNames do
            if (← getBinding 0 x).isSome then throwErr .syntax s!"Identifier '{x}' has already been declared"
            if sc.vars.contains x || funNames.contains x then throwErr .syntax s!"Identifier '{x}' has already been declared"
            if let some p := go.getOwn x then
              if !p.configurable then throwErr .syntax s!"Identifier '{x}' has already been declared"
          for x in sc.vars ++ funNames do
            if (← getBinding 0 x).isSome then throwErr .syntax s!"Identifier '{x}' has already been declared"
          for f in funNames do
            match go.getOwn f with
            | none => if !go.extensible then throwErr .type s!"Cannot declare global function '{f}'"
            | some p =>
              if !p.configurable then
                match p with
                | .data _ true true _ => pure ()
                | _ => throwErr .type s!"Cannot redefine global function '{f}'"
          for v in sc.vars do
            if !funNames.contains v && (go.getOwn v).isNone && !go.extensible then
              throwErr .type s!"Cannot declare global variable '{v}'"
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
          let _ ← core.evalStmts ctx sc.body
          pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: streams and URLPattern. `r` is the realm `moreNative` read. -/
def moreNativeWeb (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
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
            match ← core.getV v k with
            | .undef => pure none
            | x => pure (some (Str.toHost (← core.toStr x)))
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
        | x => pure (.str (Str.toHost (← core.toStr x)))
      let optStr (v : Value) : M (Option String) := do
        match v with
        | .undef => pure none
        | x => pure (some (Str.toHost (← core.toStr x)))
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
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: `for await` and the async-from-sync iterator. `r` is the realm `moreNative` read. -/
def moreNativeAsyncIter (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x (.forAwait 0)) =>
      -- GetIterator(obj, async) (§7.4.3): the @@asyncIterator method's iterator, or an
      -- async-from-sync iterator over the @@iterator method's (§27.1.6.1).
      let m ← match a0 with
        | .undef | .null => throwErr .type "object is not async iterable"
        | _ => core.getV a0 (symKey 1)
      match m with
      | .undef | .null =>
        let sync ← core.getIterator a0
        let nextM ← core.getV sync "next"
        let w ← alloc { proto := (← ownValue r.globalObj asyncFromSyncProtoKey) }
        setHidden w syncIterKey sync
        setHidden w syncNextKey nextM
        pure (.obj w)
      | _ =>
        if !(← isCallable m) then throwErr .type "Symbol.asyncIterator is not a function"
        let it ← core.callV m a0 #[]
        if !it.isObj then throwErr .type "Result of the Symbol.asyncIterator method is not an object"
        pure it
    | (.x (.forAwait 1)) =>
      if !(← isCallable a0) then throwErr .type "iterator method is not a function"
      core.callV a0 a1 #[]
    | (.x (.forAwait _)) =>
      if !a0.isObj then throwErr .type "Iterator result is not an object"
      pure .undef
    | (.x (.asyncFromSync 3)) => core.iterResult a0 false
    | (.x (.asyncFromSync 4)) => core.iterResult a0 true
    | (.x (.asyncFromSync 5)) =>
      -- the value was a rejected promise: IteratorClose(sync, ThrowCompletion(reason)); what
      -- `return` throws is dropped (bound argument: the sync iterator)
      let _ ← catchJS (core.iterClose a0) (fun a => match a with | .halt w => throw (.halt w) | _ => pure ())
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
      | none => core.rejectPromise pid (← mkError .type "not an async-from-sync iterator")
      | some (sync, nextM) =>
        let given : Array Value := if args.size > 0 then #[a0] else #[]
        let x ← catchJS (do
            let res : Option Value ← match k with
              | 0 => do pure (some (← core.callV nextM sync given))
              | 1 => do
                let m ← core.getV sync "return"
                match m with
                | .undef | .null => core.resolvePromise pid (← core.iterResult a0 true); pure none
                | _ =>
                  if !(← isCallable m) then throwErr .type "return is not a function"
                  pure (some (← core.callV m sync given))
              | _ => do
                let m ← core.getV sync "throw"
                match m with
                | .undef | .null =>
                  -- no `throw`: the protocol is broken; close the sync iterator, then a TypeError
                  core.iterClose sync
                  throwErr .type "The iterator does not provide a 'throw' method"
                | _ =>
                  if !(← isCallable m) then throwErr .type "throw is not a function"
                  pure (some (← core.callV m sync given))
            match res with
            | none => pure ()
            | some res =>
              -- AsyncFromSyncIteratorContinuation (§27.1.6.4); closeOnRejection is false for `return`
              if !res.isObj then throwErr .type "Iterator result is not an object"
              let done := toBool (← core.getV res "done")
              let value ← core.getV res "value"
              let close := !done && k != 1
              let vw ← catchJS (do pure (Except.ok (← core.promiseResolve value))) (fun a => pure (Except.error a))
              let vp ← match vw with
                | .ok vp => pure vp
                | .error (.throw e) =>
                  if close then
                    let _ ← catchJS (core.iterClose sync) (fun a => match a with | .halt w => throw (.halt w) | _ => pure ())
                  throw (.throw e)
                | .error a => throw a
              let onF ← nativeFn (.x (.asyncFromSync (if done then 4 else 3)))
              let onR ← if close then do
                  let f ← nativeFn (.x (.asyncFromSync 5))
                  pure (Value.obj (← alloc { proto := .obj r.functionProto, kind := .bound f .undef #[sync] }))
                else pure Value.undef
              core.performThen vp onF onR (.obj pid)
            pure none)
          (fun a => pure (some a))
        match x with
        | some (.throw e) => core.rejectPromise pid e
        | some a => throw a
        | none => pure ()
      pure (.obj pid)
    | _ => throwErr .type "not a function"

/-- Built-ins of `moreNative`: `Array.fromAsync`. `r` is the realm `moreNative` read. -/
def moreNativeFromAsync (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | (.x .arrayFromAsync) =>
      -- Array.fromAsync (asyncItems, mapfn, thisArg): a promise for the array; every abrupt
      -- completion of the setup rejects it (IfAbruptRejectPromise)
      let pid ← newPromise
      let x ← catchJS (do
          let mapfn := a1
          if !(mapfn matches .undef) && !(← isCallable mapfn) then throwErr .type "Array.fromAsync: mapfn is not callable"
          let nullish (v : Value) : Bool := match v with | .undef | .null => true | _ => false
          let am ← if nullish a0 then pure Value.undef else core.getV a0 (symKey 1)
          let sm ← if nullish am && !nullish a0 then core.getV a0 (symKey symIterator) else pure Value.undef
          if !nullish am || !nullish sm then
            -- an async iterator (or the async-from-sync wrapper of a sync one)
            let arr ← if ← isConstructor thisV then core.construct thisV #[] thisV else newArray #[]
            let it ← core.callNative (.x (.forAwait 0)) .undef #[a0] none
            let nextM ← core.getV it "next"
            let _ ← core.callNative (.x (.fromAsyncStep 6)) .undef #[.obj pid, arr, it, nextM, mapfn, argD args 2, .num 0] none
          else
            -- an array-like: each index read and awaited in turn
            let o ← core.toObj a0
            let len ← core.arrayLikeLength (.obj o)
            let arr ← if ← isConstructor thisV then core.construct thisV #[.num (Float.ofNat len)] thisV else newArray #[]
            let _ ← core.callNative (.x (.fromAsyncStep 7)) .undef #[.obj pid, arr, .obj o, .num (Float.ofNat len), mapfn, argD args 2, .num 0] none
          pure none)
        (fun a => pure (some a))
      match x with
      | some (.throw e) => core.rejectPromise pid e
      | some a => throw a
      | none => pure ()
      pure (.obj pid)
    | (.x (.fromAsyncStep k)) =>
      -- the state, bound in front of the reaction's argument: the promise, the array, the
      -- iterator (or the array-like), `next` (or the length), mapfn, thisArg, the index
      let pid := match a0 with | .obj p => p | _ => 0
      let arr := a1
      let src := argD args 2
      let aux := argD args 3
      let mapfn := argD args 4
      let thisArg := argD args 5
      let idx : Nat := match argD args 6 with | .num x => x.toUInt64.toNat | _ => 0
      let arg := argD args 7
      let bindStep (j : Nat) (st : Array Value) : M Value := do
        let f ← nativeFn (.x (.fromAsyncStep j))
        pure (Value.obj (← alloc { proto := .obj r.functionProto, kind := .bound f .undef st }))
      let state (i : Nat) : Array Value := #[.obj pid, arr, src, aux, mapfn, thisArg, .num (Float.ofNat i)]
      -- Await (§6.2.3.1): PromiseResolve, then the reactions
      let awaitV (v : Value) (onF onR : Value) : M Unit := do
        let vp ← core.promiseResolve v
        core.performThen vp onF onR .undef
      let closeIt : M Unit := do
        let _ ← catchJS (do
            let m ← core.getV src "return"
            if ← isCallable m then
              discard <| core.callV m src #[]
            pure ())
          (fun a => match a with | .halt w => throw (.halt w) | _ => pure ())
      let x ← catchJS (do
          match k with
          | 5 => core.rejectPromise pid (argD args 1)
          | 4 =>
            closeIt
            core.rejectPromise pid (argD args 3)
          | 6 =>
            let res ← core.callV aux src #[]
            if !res.isObj then throwErr .type "Array.fromAsync: the iterator result is not an object"
            awaitV res (← bindStep 0 (state idx)) (← bindStep 5 #[.obj pid])
          | 0 =>
            if !arg.isObj then throwErr .type "Array.fromAsync: the iterator result is not an object"
            if toBool (← core.getV arg "done") then
              core.putV arr "length" (.num (Float.ofNat idx)) true
              core.resolvePromise pid arr
            else
              let v ← core.getV arg "value"
              if mapfn matches .undef then
                core.putV arr (toString idx) v true
                let _ ← core.callNative (.x (.fromAsyncStep 6)) .undef (state (idx + 1)) none
              else
                let mv ← catchJS (do pure (Except.ok (← core.callV mapfn thisArg #[v, .num (Float.ofNat idx)])))
                  (fun a => pure (Except.error a))
                match mv with
                | .ok m => awaitV m (← bindStep 1 (state idx)) (← bindStep 4 (#[.obj pid, .undef, src]))
                | .error (.throw e) =>
                  closeIt
                  core.rejectPromise pid e
                | .error a => throw a
          | 1 =>
            core.putV arr (toString idx) arg true
            let _ ← core.callNative (.x (.fromAsyncStep 6)) .undef (state (idx + 1)) none
          | 7 =>
            let len : Nat := match aux with | .num x => x.toUInt64.toNat | _ => 0
            if idx ≥ len then
              core.putV arr "length" (.num (Float.ofNat len)) true
              core.resolvePromise pid arr
            else
              let v ← core.getV src (toString idx)
              awaitV v (← bindStep 2 (state idx)) (← bindStep 5 #[.obj pid])
          | 2 =>
            if mapfn matches .undef then
              core.putV arr (toString idx) arg true
              let _ ← core.callNative (.x (.fromAsyncStep 7)) .undef (state (idx + 1)) none
            else
              let m ← core.callV mapfn thisArg #[arg, .num (Float.ofNat idx)]
              awaitV m (← bindStep 3 (state idx)) (← bindStep 5 #[.obj pid])
          | _ =>
            core.putV arr (toString idx) arg true
            let _ ← core.callNative (.x (.fromAsyncStep 7)) .undef (state (idx + 1)) none
          pure none)
        (fun a => pure (some a))
      match x with
      | some (.throw e) =>
        if k == 0 || k == 1 || k == 6 then closeIt
        core.rejectPromise pid e
      | some a => throw a
      | none => pure ()
      pure Value.undef
    | _ => throwErr .type "not a function"

/-- ArrayBuffer `resize` and `transfer` and its accessors, SharedArrayBuffer, %TypedArray%
(the constructor, `from`, `of`, the accessors and the methods that answer typed arrays),
Atomics without waiting, and `String.prototype.isWellFormed`/`toWellFormed`. -/
def moreNative (core : CoreFn H) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let r ← realm
    match id with
    | (.x (.dataViewGetter _)) => moreNativeBuffers core r id thisV args newTarget
    | (.x (.bufferGetter _)) => moreNativeBuffers core r id thisV args newTarget
    | (.x .bufferResize) => moreNativeBuffers core r id thisV args newTarget
    | (.x (.bufferTransfer _)) => moreNativeBuffers core r id thisV args newTarget
    | (.x .sharedCtor) => moreNativeBuffers core r id thisV args newTarget
    | (.x (.sharedGetter _)) => moreNativeBuffers core r id thisV args newTarget
    | (.x .sharedGrow) => moreNativeBuffers core r id thisV args newTarget
    | (.x .sharedSlice) => moreNativeBuffers core r id thisV args newTarget
    | (.x .typedArrayCtor) => moreNativeTyped core r id thisV args newTarget
    | (.x .typedOf) | (.x .typedFrom) => moreNativeTyped core r id thisV args newTarget
    | (.x (.typedGetter _)) => moreNativeTyped core r id thisV args newTarget
    | (.x (.typedGeneric _)) => moreNativeTyped core r id thisV args newTarget
    | (.x (.typedMethod _)) => moreNativeTypedMethod core r id thisV args newTarget
    | (.x (.atomics _)) => moreNativeBuffers core r id thisV args newTarget
    | (.x .iteratorCtor) => moreNativeIterator core r id thisV args newTarget
    | (.x .suppressedErrorCtor) => moreNativeDisposable core r id thisV args newTarget
    | (.x .disposableStackCtor) => moreNativeDisposable core r id thisV args newTarget
    | (.x .disposableStackDisposed) => moreNativeDisposable core r id thisV args newTarget
    | (.x (.disposableStackMethod _)) => moreNativeDisposable core r id thisV args newTarget
    | (.x .adoptClosure) => moreNativeDisposable core r id thisV args newTarget
    | (.x .asyncDisposableStackCtor) => moreNativeAsyncDisposable core r id thisV args newTarget
    | (.x .asyncDsDisposed) => moreNativeAsyncDisposable core r id thisV args newTarget
    | (.x (.u8Base64 _)) => moreNativeTyped core r id thisV args newTarget
    | (.x (.arrayToLocaleString _)) => moreNativeTyped core r id thisV args newTarget
    | (.x .fnHasInstance) => moreNativeObject core r id thisV args newTarget
    | (.x .asyncDsSyncWrap) => moreNativeAsyncDisposable core r id thisV args newTarget
    | (.x (.asyncDsMethod _)) => moreNativeAsyncDisposable core r id thisV args newTarget
    | (.x (.asyncDsStep _)) => moreNativeAsyncDisposable core r id thisV args newTarget
    | (.x .iteratorDispose) => moreNativeDisposable core r id thisV args newTarget
    | (.x .temporal) => moreNativeDate core r id thisV args newTarget
    | (.x .errorIsError) => moreNativeObject core r id thisV args newTarget
    | (.x .promiseTry) => moreNativePromise core r id thisV args newTarget
    | (.x (.regexpSym _)) => moreNativeString core r id thisV args newTarget
    | (.x .speciesGetter) => moreNativeObject core r id thisV args newTarget
    | (.x (.collMethod _ _)) => moreNativeSet core r id thisV args newTarget
    | (.x (.stringHtml _)) => moreNativeString core r id thisV args newTarget
    | (.x .regexpCompile) => moreNativeString core r id thisV args newTarget
    | (.x .regexpEscape) => moreNativeString core r id thisV args newTarget
    | (.x (.iteratorZip _)) => moreNativeIteratorZip core r id thisV args newTarget
    | (.x .iteratorConcat) => moreNativeIterator core r id thisV args newTarget
    | (.x .iteratorFrom) => moreNativeIterator core r id thisV args newTarget
    | (.x (.iterLazy _)) => moreNativeIterator core r id thisV args newTarget
    | (.x (.iterEager 6)) | (.x (.iterEager 7)) => moreNativeIterEager core r id thisV args newTarget
    | (.x (.iterEager _)) => moreNativeIterEager core r id thisV args newTarget
    | (.x .helperNext) | (.x .helperReturn) => moreNativeIterHelper core r id thisV args newTarget
    | (.x .numberToExponential) | (.x .numberToPrecision) => moreNativeString core r id thisV args newTarget
    | (.x .cloneSerialize) => moreNativeClone core r id thisV args newTarget
    | (.x .cloneDeserialize) => moreNativeClone core r id thisV args newTarget
    | (.x .classicScript) => moreNativeClone core r id thisV args newTarget
    | (.x .classicScriptHost) => moreNativeClone core r id thisV args newTarget
    | (.x (.setMethod _)) => moreNativeSet core r id thisV args newTarget
    | (.x .proxyRevocable) => moreNativeObject core r id thisV args newTarget
    | (.x .proxyRevoke) => moreNativeObject core r id thisV args newTarget
    | (.x (.arrayMethod _)) => moreNativeArray core r id thisV args newTarget
    | (.x .objectHasOwn) => moreNativeObject core r id thisV args newTarget
    | (.x (.groupBy _)) => moreNativeWeak core r id thisV args newTarget
    | (.x .stringLocaleCompare) => moreNativeString core r id thisV args newTarget
    | (.x .stringNormalize) => moreNativeString core r id thisV args newTarget
    | (.x (.errorStack false)) => moreNativeObject core r id thisV args newTarget
    | (.x (.errorStack true)) => moreNativeObject core r id thisV args newTarget
    | (.x .aggregateErrorCtor) => moreNativeObject core r id thisV args newTarget
    | (.x .dateUTC) => moreNativeDate core r id thisV args newTarget
    | (.x .dateParse) => moreNativeDate core r id thisV args newTarget
    | (.x (.dateMethod _)) => moreNativeDate core r id thisV args newTarget
    | (.x .namedGetterSet) => moreNativeObject core r id thisV args newTarget
    | (.x .symbolFor) | (.x .symbolKeyFor) => moreNativeString core r id thisV args newTarget
    | (.x .stringRaw) => moreNativeString core r id thisV args newTarget
    | (.x .weakRefCtor) => moreNativeWeak core r id thisV args newTarget
    | (.x .weakRefDeref) => moreNativeWeak core r id thisV args newTarget
    | (.x .finRegCtor) => moreNativeWeak core r id thisV args newTarget
    | (.x (.finRegMethod _)) => moreNativeWeak core r id thisV args newTarget
    | (.x (.mapUpsert _ _)) => moreNativeWeak core r id thisV args newTarget
    | (.x .streams) => moreNativeWeb core r id thisV args newTarget
    | (.x (.protoAccessor false)) => moreNativeObject core r id thisV args newTarget
    | (.x (.protoAccessor true)) => moreNativeObject core r id thisV args newTarget
    | (.x .promiseWithResolvers) => moreNativePromise core r id thisV args newTarget
    | (.x .capabilityExecutor) => moreNativePromise core r id thisV args newTarget
    | (.x (.dynFunction _)) => moreNativeObject core r id thisV args newTarget
    | (.x .urlPattern) => moreNativeWeb core r id thisV args newTarget
    | (.x .realmTake) => moreNativeObject core r id thisV args newTarget
    | (.x .gcNoop) => moreNativeObject core r id thisV args newTarget
    | (.x .dynImport) => moreNativePromise core r id thisV args newTarget
    | (.x (.promiseThenableFn _)) => moreNativePromise core r id thisV args newTarget
    | (.x (.forAwait 0)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.forAwait 1)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.forAwait _)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.asyncFromSync 3)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.asyncFromSync 4)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.asyncFromSync 5)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x (.asyncFromSync _)) => moreNativeAsyncIter core r id thisV args newTarget
    | (.x .arrayFromAsync) => moreNativeFromAsync core r id thisV args newTarget
    | (.x (.fromAsyncStep _)) => moreNativeFromAsync core r id thisV args newTarget
    | (.x .stringIsWellFormed) | (.x .stringToWellFormed) => moreNativeString core r id thisV args newTarget
    | _ => throwErr .type "not a function"

/-- RegExp, the String methods with a RegExp, Proxy, JSON.parse, ArrayBuffer, the typed
arrays, Date, `performance.now` and the host's natives. -/
def extraNative (core : CoreFn H) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let r ← realm
    let needNew : String → M Unit := fun nm =>
      if newTarget.isNone then throwErr .type s!"Constructor {nm} requires 'new'" else pure ()
    match id with
    | .regexpCtor =>
      -- §22.2.4.1 RegExp(pattern, flags)
      let isRegExpCtor (v : Value) : M Bool := do
        match v with
        | .obj c => pure (match (← getObj c).kind with | .native .regexpCtor => true | _ => false)
        | _ => pure false
      -- IsRegExp (§7.2.8): @@match when it is not undefined, else [[RegExpMatcher]]
      let patIsRx ← match a0 with
        | .obj _ => do
          match ← core.getV a0 (symKey 8) with
          | .undef => isRegExpV a0
          | m => pure (toBool m)
        | _ => pure false
      if newTarget.isNone && patIsRx && a1 matches .undef then
        if ← isRegExpCtor (← core.getV a0 "constructor") then return a0
      let (pV, fV) ← match a0 with
        | .obj oid => match (← getObj oid).kind with
          | .regexp _ src f => pure (Value.str src, if a1 matches .undef then Value.str f else a1)
          | _ =>
            if patIsRx then do
              let p ← core.getV a0 "source"
              let f ← if a1 matches .undef then core.getV a0 "flags" else pure a1
              pure (p, f)
            else pure (a0, a1)
        | _ => pure (a0, a1)
      -- RegExpAlloc: the prototype of newTarget (§10.1.13 GetPrototypeFromConstructor)
      let proto ← match newTarget with
        | some nt =>
          if ← isRegExpCtor nt then pure none
          else do
            let p ← core.getV nt "prototype"
            pure (some (if p.isObj then p else .obj r.regexpProto))
        | none => pure none
      let src ← match pV with | .undef => pure "" | v => core.toStr v
      let fl ← match fV with | .undef => pure "" | v => core.toStr v
      let rx ← newRegExp (if src.isEmpty then "(?:)" else src) fl
      if let (some p, .obj id) := (proto, rx) then
        modifyObj id fun o => { o with proto := p }
        -- a subclass instance has no legacy features (Annex B.2.4: compile throws on it)
        setHidden id regexpNoLegacyKey (.bool true)
      pure rx
    | .regexpExec =>
      let s ← core.toStr a0
      match ← core.regexExec thisV s with
      | none => pure .null
      | some caps => core.matchArray (← regexpOf thisV).1 s caps
    | .regexpTest =>
      let s ← core.toStr a0
      pure (.bool (← core.regexExec thisV s).isSome)
    | .regexpToString =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .regexp _ src f => pure (.str ("/" ++ Re.escapeSource src ++ "/" ++ f))
        | _ => pure (.str ("/" ++ (← core.toStr (← core.getV thisV "source")) ++ "/" ++ (← core.toStr (← core.getV thisV "flags"))))
      | _ => throwErr .type "RegExp.prototype.toString called on a non-object"
    | .regexpGetter 1 =>
      -- get RegExp.prototype.flags (§22.2.6.4): each flag's property, read through the object
      if !thisV.isObj then throwErr .type "RegExp.prototype.flags getter called on a non-object"
      let mut out := ""
      for (c, nm) in [('d', "hasIndices"), ('g', "global"), ('i', "ignoreCase"), ('m', "multiline"),
          ('s', "dotAll"), ('u', "unicode"), ('v', "unicodeSets"), ('y', "sticky")] do
        if toBool (← core.getV thisV nm) then out := out.push c
      pure (.str out)
    | .regexpGetter which =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .regexp re src f =>
          pure (match which with
            | 0 => .str (Re.escapeSource src)
            -- §22.2.6.4 get flags: in the order "dgimsuvy"
            | 1 => .str (String.ofList ("dgimsuvy".toList.filter fun c => f.contains c))
            | 2 => .bool re.flags.global | 3 => .bool re.flags.icase
            | 4 => .bool re.flags.multiline | 5 => .bool re.flags.sticky | 6 => .bool (f.contains 'u')
            | 7 => .bool re.flags.dotAll | 8 => .bool (f.contains 'd') | _ => .bool (f.contains 'v'))
        | _ =>
          -- §22.2.6: %RegExp.prototype% itself answers undefined ("(?:)" for source); any
          -- other object without [[OriginalFlags]] is a TypeError
          if oid == r.regexpProto then pure (if which == 0 then .str "(?:)" else if which == 1 then .str "" else .undef)
          else throwErr .type "RegExp getter called on an incompatible receiver"
      | _ => throwErr .type "RegExp getter called on a non-object"
    | .stringMatch | .stringMatchAll | .stringSearch =>
      let s ← core.toStr (← thisPrim thisV)
      let rx ← if ← isRegExpV a0 then pure a0 else match a0 with
        | .undef => newRegExp "(?:)" (if id == .stringMatchAll then "g" else "")
        | _ => do newRegExp (← core.toStr a0) (if id == .stringMatchAll then "g" else "")
      let (re, src, fl) ← regexpOf rx
      if id == .stringSearch then
        return match Re.exec { re with flags := { re.flags with global := false, sticky := re.flags.sticky } } (charsOf s) 0 with
          | some caps => match caps[0]? with | some (some (a, _)) => .num (Float.ofNat a) | _ => .num (-1)
          | none => .num (-1)
      if id == .stringMatch && !re.flags.global then
        return ← match ← core.regexExec rx s with
          | none => pure .null
          | some caps => core.matchArray re s caps
      if id == .stringMatchAll && !re.flags.global then throwErr .type "String.prototype.matchAll called with a non-global RegExp argument"
      -- All matches, on a copy for matchAll (§22.2.6.9 step 6), from lastIndex 0.
      let rx ← if id == .stringMatchAll then newRegExp src fl else pure rx
      core.putV rx "lastIndex" (.num 0) true
      let cs := charsOf s
      let mut out : Array Value := #[]
      for _ in [0:cs.size + 2] do
        match ← core.regexExec rx s with
        | none => break
        | some caps =>
          let (a, b) := match caps[0]? with | some (some p) => p | _ => (0, 0)
          out := out.push (← if id == .stringMatch then pure (.str (Str.ofUnitChars (cs.extract a b))) else core.matchArray re s caps)
          if a == b then core.putV rx "lastIndex" (.num (Float.ofNat (advanceIndex s b re.flags.unicode))) true
      if id == .stringMatch then
        return ← (if out.isEmpty then pure .null else newArray out)
      let arr ← newArray out
      pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter arr 0 0 }))
    | .stringReplace | .stringReplaceAll =>
      let s ← core.toStr (← thisPrim thisV)
      let cs := charsOf s
      let (re, _, _) ← regexpOf a0
      if id == .stringReplaceAll && !re.flags.global then
        throwErr .type "replaceAll must be called with a global RegExp"
      let fnRepl ← isCallable a1
      let replStr ← if fnRepl then pure "" else core.toStr a1
      if re.flags.global then core.putV a0 "lastIndex" (.num 0) true
      let mut found : Array (Array (Option (Nat × Nat))) := #[]
      for _ in [0:cs.size + 2] do
        match ← core.regexExec a0 s with
        | none => break
        | some caps =>
          found := found.push caps
          if !re.flags.global then break
          match caps[0]? with
          | some (some (a, b)) => if a == b then core.putV a0 "lastIndex" (.num (Float.ofNat (advanceIndex s b re.flags.unicode))) true
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
              for (nm, k) in re.names do
                let v := capVals.getD (k - 1) .undef
                if !(v matches .undef) || ((← getObj o).getOwn nm).isNone then
                  defineOwn o nm (.data v true true true)
              pure #[Value.obj o]
            core.toStr (← core.callV a1 .undef (#[.str matched] ++ capVals ++ #[.num (Float.ofNat a), .str s] ++ groups))
          else match substitution replStr matched a cs capStrs re.names with
            | some t => pure t
            | none => throwErr .range "Invalid string length"
        checkStrLen (out.utf8ByteSize + rep.utf8ByteSize)
        out := out ++ Str.ofUnitChars (cs.extract last a) ++ rep
        last := b
      pure (.str (out ++ Str.ofUnitChars (cs.extract last cs.size)))
    | .stringSplit =>
      let s ← core.toStr (← thisPrim thisV)
      let cs := charsOf s
      let (re, _, _) ← regexpOf a0
      let lim ← match a1 with
        | .undef => pure 4294967295
        | l => do pure (toUint32 (← core.toNum l))
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
      let s ← core.toStr a0
      -- §25.5.1 reads code units: a lone surrogate escape (`"\uD800"`, which RFC 8259's
      -- strict parser refuses) is a string of that unit (`jsonParseText`: the strict parse
      -- first, the escaped reading only when it fails; `jsonParseText_strict`).
      match jsonParseText s with
      | .ok (j, _) =>
        let v ← jsonToValue 100000 j
        if !(← isCallable a1) then return v
        -- §25.5.1 step 6: the reviver, from a root object { "": value }
        let root ← newObject
        defineOwn root "" (.data v true true true)
        let srcs ← jsonSources 100000 root "" j v
        core.jsonRevive srcs a1 (.obj root) "" 0
      | .error e => throwErr .syntax s!"Unexpected token in JSON at position {e.pos}"
    | .bufferCtor =>
      needNew "ArrayBuffer"
      let len := toIntegerOrInf (← core.toNum a0)
      if len < 0 || len > 268435456 then throwErr .range "Invalid array buffer length"
      -- §25.1.4.1: the `maxByteLength` option makes a resizable buffer
      let max ← match a1 with
        | .obj _ => do
          match ← core.getV a1 "maxByteLength" with
          | .undef => pure none
          | v =>
            let m := toIntegerOrInf (← core.toNum v)
            if m < 0 || m > 268435456 then throwErr .range "Invalid array buffer max length"
            pure (some m)
        | _ => pure none
      if let some m := max then
        if len > m then throwErr .range "byteLength exceeds maxByteLength"
      let buf ← newBuffer (zeroBytes (len.toUInt64.toNat))
      if let (.obj bid, some m) := (buf, max) then
        defineOwn bid bufMaxKey (.data (.num m) true false false)
      -- the prototype is the new target's (OrdinaryCreateFromConstructor)
      if let (.obj bid, some nt) := (buf, newTarget) then
        let p ← core.getV nt "prototype"
        let p ← if p.isObj then pure p else pure (.obj (← funRealm nt).bufferProto)
        modifyObj bid fun o => { o with proto := p }
      pure buf
    | .bufferSlice =>
      let bytes ← match thisV with
        | .obj oid => match (← getObj oid).kind with
          | .buffer b => pure b
          | _ => throwErr .type "ArrayBuffer.prototype.slice called on incompatible receiver"
        | _ => throwErr .type "ArrayBuffer.prototype.slice called on incompatible receiver"
      if let .obj oid := thisV then
        if isDetached (← getObj oid) then throwErr .type "ArrayBuffer.prototype.slice called on a detached ArrayBuffer"
      let a := relIndex (toIntegerOrInf (← core.toNum a0)) bytes.size
      let b ← match a1 with
        | .undef => pure bytes.size
        | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) bytes.size)
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
        let buf ← newBuffer (zeroBytes (xs.size * es))
        let .obj bid := buf | pure buf
        for i in [0:xs.size] do typedWriteV ty bid 0 i (← core.typedConv ty xs[i]!)
        newTyped ty bid 0 xs.size
      match a0 with
      | .obj oid =>
        match (← getObj oid).kind with
        | .buffer bytes =>
          if isDetached (← getObj oid) then throwErr .type "Cannot construct a typed array on a detached ArrayBuffer"
          let off := (toIntegerOrInf (← core.toNum a1)).toUInt64.toNat
          if off % es != 0 then throwErr .range s!"start offset of {(typedNames[ty]?.map (·.1)).getD ""} should be a multiple of {es}"
          let resizable := (hiddenNum (← getObj oid) bufMaxKey).isSome
          let len ← match argD args 2 with
            | .undef =>
              -- §23.2.5.1.3 step 8: on a resizable buffer, a length-tracking view
              if resizable then
                if off > bytes.size then throwErr .range "Start offset is outside the bounds of the buffer"
                pure autoLen
              else
              if bytes.size < off || (bytes.size - off) % es != 0 then throwErr .range "byte length should be a multiple of the element size"
              pure ((bytes.size - off) / es)
            | v => do pure (toIntegerOrInf (← core.toNum v)).toUInt64.toNat
          if len != autoLen && off + len * es > bytes.size then throwErr .range "Invalid typed array length"
          newTyped ty oid off len
        | .typed sty sb soff slen =>
          let bytes := bufferBytes (← getObj sb)
          let slen ← liveLen sty sb soff slen
          -- §23.2.5.1.2 InitializeTypedArrayFromTypedArray: BigInts and Numbers do not mix
          if typedIsBig sty != typedIsBig ty then throwErr .type "Content types of the typed arrays differ"
          fromList ((List.range slen).toArray.map fun i => typedRead sty bytes (soff + i * elemSize sty))
        | _ =>
          let itf ← core.getV a0 (symKey symIterator)
          if itf.isObj then fromList (← core.iterToArray (← core.getIterator a0) #[])
          else fromList (← core.elemsOf a0)
      | .undef => fromList #[]
      | v =>
        let len := toIntegerOrInf (← core.toNum v)
        if len < 0 || len > 268435456 then throwErr .range "Invalid typed array length"
        let buf ← newBuffer (zeroBytes (len.toUInt64.toNat * es))
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
      let off := toIntegerOrInf (← core.toNum a1)
      if off < 0 || off > 9007199254740991 then throwErr .range "Start offset is outside the bounds of the buffer"
      let off := off.toUInt64.toNat
      if off > size then throwErr .range "Start offset is outside the bounds of the buffer"
      let len ← match argD args 2 with
        | .undef => pure (size - off)
        | v => do
          let l := toIntegerOrInf (← core.toNum v)
          if l < 0 || l > 9007199254740991 then throwErr .range "Invalid DataView length"
          pure l.toUInt64.toNat
      if off + len > size then throwErr .range "Invalid DataView length"
      let id ← alloc { proto := .obj (← realm).dataViewProto, kind := .dataView bid off len }
      -- a view without a length on a resizable buffer tracks the buffer's length
      if (argD args 2) matches .undef then
        if (hiddenNum (← getObj bid) bufMaxKey).isSome then setHidden id dataViewAutoKey (.bool true)
      pure (.obj id)
    | .dataViewGet ty | .dataViewSet ty =>
      -- GetViewValue and SetViewValue (§25.3.1.5, §25.3.1.6).
      let (b, voff, vlen, auto) ← match thisV with
        | .obj oid => do
          let o ← getObj oid
          match o.kind with
          | .dataView b off len => pure (b, off, len, hiddenFlag o dataViewAutoKey)
          | _ => throwErr .type "not a DataView"
        | _ => throwErr .type "not a DataView"
      let bsize := (bufferBytes (← getObj b)).size
      let vlen := if auto then bsize - voff else vlen
      let idx := toIntegerOrInf (← core.toNum a0)
      if idx < 0 || idx > 9007199254740991 then throwErr .range "Offset is outside the bounds of the DataView"
      let idx := idx.toUInt64.toNat
      let size := elemSize ty
      let isSet := match id with | .dataViewSet _ => true | _ => false
      -- set: the value is converted before the offset is checked.
      let bits : Option ByteArray ← if !isSet then pure none else
        if typedIsBig ty then do
          let i ← match ← core.toPrim a1 "number" with
            | .big i => pure i
            | .bool bb => pure (if bb then 1 else 0)
            | .str t => match strToBigInt t with
              | some i => pure i
              | none => throwErr .syntax s!"Cannot convert {t} to a BigInt"
            | _ => throwErr .type "Cannot convert value to a BigInt"
          let u := (i.emod (2 ^ 64)).toNat
          pure (some (ByteArray.mk ((List.range 8).toArray.map fun k => (u / 2 ^ (8 * k) % 256).toUInt8)))
        else do pure (some (typedBytes ty (← core.toNum a1)))
      let little := toBool (argD args (if isSet then 2 else 1))
      if isDetached (← getObj b) then throwErr .type "Cannot perform DataView access on a detached ArrayBuffer"
      if voff + vlen > (bufferBytes (← getObj b)).size || (auto && voff > (bufferBytes (← getObj b)).size) then
        throwErr .type "The DataView is out of the bounds of its buffer"
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
        let at_ := toIntegerOrInf (← core.toNum a1)
        if at_ < 0 then throwErr .range "offset is out of bounds"
        if !(← typedInBounds ty b off len) then throwErr .type "set: the typed array is detached or out of bounds"
        let at_ := at_.toUInt64.toNat
        let len ← liveLen ty b off len
        let xs ← core.elemsOf a0
        if at_ + xs.size > len then throwErr .range "offset is out of bounds"
        -- Every element a Number and the type not a BigInt one: no conversion can run page
        -- code, so the bytes of all the elements go in one write (the bytes `typedWriteV`
        -- writes one element at a time; issue 1098). Else one element at a time.
        let es := elemSize ty
        let fits := off + (at_ + xs.size) * es ≤ (bufferBytes (← getObj b)).size
        if !typedIsBig ty && fits && xs.all (fun x => x matches .num _) then
          let bs := xs.foldl (fun acc x => match x with | .num v => acc ++ typedBytes ty v | _ => acc)
            (ByteArray.emptyWithCapacity (xs.size * es))
          typedWriteAll b (off + at_ * es) bs
        else
          for i in [0:xs.size] do typedWriteV ty b off (at_ + i) (← core.typedConv ty xs[i]!)
        pure .undef
      | .typedSubarray =>
        -- §23.2.3.30: the bounds (converted first), then TypedArraySpeciesCreate(O, « buffer,
        -- beginByteOffset, newLength ») (§23.2.4.1): the species constructor, or the type's own.
        -- A length-tracking view with no `end` makes one too (step 13: « buffer, beginByteOffset »).
        let tracks := len == autoLen && a1 matches .undef
        let len ← liveLen ty b off len
        let a := relIndex (toIntegerOrInf (← core.toNum a0)) len
        let e ← match a1 with
          | .undef => pure len
          | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) len)
        let newLen := if e > a then e - a else 0
        let begin := off + a * elemSize ty
        let dflt ← ownValue (r.typedProtos.getD ty 0) "constructor"
        let c ← core.speciesCtor thisV dflt
        if strictEq c dflt then
          if isDetached (← getObj b) then throwErr .type "subarray: the buffer is detached"
          if tracks then
            if begin > (bufferBytes (← getObj b)).size then
              throwErr .range "subarray: the view is out of the buffer's bounds"
            return ← newTyped ty b begin autoLen
          if begin + newLen * elemSize ty > (bufferBytes (← getObj b)).size then
            throwErr .range "subarray: the view is out of the buffer's bounds"
          return ← newTyped ty b begin newLen
        let res ← core.construct c (if tracks then #[.obj b, .num (Float.ofNat begin)]
          else #[.obj b, .num (Float.ofNat begin), .num (Float.ofNat newLen)]) c
        -- TypedArrayCreateFromConstructor: a valid typed array of the same content type
        let .obj rid := res | throwErr .type "subarray: the species constructor did not make a typed array"
        let .typed rty rb roff rlen := (← getObj rid).kind
          | throwErr .type "subarray: the species constructor did not make a typed array"
        if !(← typedInBounds rty rb roff rlen) then throwErr .type "subarray: the new typed array is detached or out of bounds"
        if typedIsBig rty != typedIsBig ty then throwErr .type "subarray: the new typed array has another content type"
        pure res
      | _ =>
        -- §23.2.3.9 %TypedArray%.prototype.fill: ValidateTypedArray, the value, then the
        -- indices, then detachment
        if !(← typedInBounds ty b off len) then throwErr .type "fill: the typed array is detached or out of bounds"
        let x ← core.typedConv ty a0
        let len0 ← liveLen ty b off len
        let a ← match a1 with | .undef => pure 0 | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) len0)
        let e ← match argD args 2 with | .undef => pure len0 | v => do pure (relIndex (toIntegerOrInf (← core.toNum v)) len0)
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
            let v ← core.toPrim a0 "default"
            match v with
            | .str s => pure (Date.parse s)
            | v => pure (Date.timeClip (← core.toNum v))
        else do
          let mut xs : Array Float := #[]
          for i in [0:min 7 args.size] do xs := xs.push (← core.toNum args[i]!)
          pure (Date.timeClip (dateOfParts xs))
      let p ← core.getV nt "prototype"
      let id ← alloc { proto := (← protoOr p nt (·.dateProto)), kind := .prim (.num t) }
      defineOwn id dateKey (.data (.bool true) true false false)
      pure (.obj id)
    | .dateGetTime =>
      match ← thisDate? thisV with
      | some t => pure (.num t)
      | none => throwErr .type "this is not a Date object."
    | .perfNow => pure (.num ((← hostNowNs) / 1000000))
    | .uriFn which =>
      let s ← core.toStr a0
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

/-- Built-ins of `callNative`: the global functions, `eval`, `%ThrowTypeError%` and `Date.now`. `r` is the realm `callNative` read. -/
def callNativeGlobal (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | .print =>
      let parts ← args.toList.mapM (core.toStr)
      modify fun h => { h with out := h.out.push (Str.toHost (" ".intercalate parts)) }
      pure .undef
    | .isNaN => pure (.bool (← core.toNum a0).isNaN)
    | .isFinite => pure (.bool (← core.toNum a0).isFinite)
    | .parseInt =>
      let s ← core.toStr a0
      let rx ← core.toNum a1
      pure (.num (parseIntStr s (toInt32 rx)))
    | .parseFloat => pure (.num (parseFloatStr (← core.toStr a0)))
    | .throwTypeError => throwErr .type "'caller', 'callee', and 'arguments' properties may not be accessed"
    | .eval =>
      match a0 with
      | .str _ => core.directEval { env := 0, thisV := .obj r.globalObj, strict := false } a0
      | v => pure v
    | .dateNow => pure (.num ((← hostNowNs) / 1000000).floor)
    | _ => throwErr .type "not a function"

/-- Add one entry to the ordinary object made by `Object.fromEntries`.
Get both entry components before coercing the key. -/
def addObjectEntry (core : CoreFn H) (target : Nat) (entry : Value) : M Value := do
  if !entry.isObj then return ← throwErr .type "Iterator value is not an entry object"
  let rawKey ← core.getV entry "0"
  let value ← core.getV entry "1"
  let key ← core.toKey rawKey
  defineOwn target key (.data value true true true)
  pure .undef

/-- A primitive yields the TypeError completion before a property access or definition. -/
private theorem addObjectEntry_primitive (core : CoreFn H) (target : Nat)
    (entry : Value) (primitive : entry.isObj = false) :
    addObjectEntry core target entry = throwErr .type "Iterator value is not an entry object" := by
  simp [addObjectEntry, primitive]

#print axioms addObjectEntry_primitive

/-- Built-ins of `callNative`: the Object constructor and its static methods. `r` is the realm `callNative` read. -/
def callNativeObjectStatic (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .objectCtor =>
      match a0 with
      | .undef | .null => pure (.obj (← newObject))
      | v => pure (.obj (← core.toObj v))
    | .objectKeys =>
      let id ← core.toObj a0
      let o ← getObj id
      match o.kind with
      | .proxy .. | .typed .. =>
        let ks := (← core.ownKeysOf id).filter (fun k => !isSymKey k && !isPrivKey k)
        let ks ← ks.filterM fun k => do pure (match ← core.ownDesc id k with | some p => p.enumerable | none => false)
        newArray (ks.map keyStrV)
      | _ =>
        let ks := o.ownStrKeys.filter fun k => match o.getOwn k with
          | some p => p.enumerable | none => false
        newArray (ks.map keyStrV)
    | .objectGetOwnPropertyNames =>
      let id ← core.toObj a0
      newArray ((← core.ownKeysOf id).filter (fun k => !isSymKey k && !isPrivKey k) |>.map keyStrV)
    | .objectGetPrototypeOf =>
      -- [[GetPrototypeOf]] (§10.1.1, §10.5.1)
      let id ← core.toObj a0
      let o ← getObj id
      match o.kind with
      | .proxy t hnd =>
        let .obj _ := t | throwErr .type "Cannot perform 'getPrototypeOf' on a proxy that has been revoked"
        match ← core.proxyTrap hnd "getPrototypeOf" with
        | none => core.callNative .objectGetPrototypeOf .undef #[t] none
        | some f =>
          let p ← core.callV f hnd #[t]
          if !(p.isObj || (p matches .null)) then
            throwErr .type "'getPrototypeOf' on proxy: the trap returned neither an object nor null"
          if !toBool (← core.callNative .objectIsExtensible .undef #[t] none) then
            if !sameValue p (← core.callNative .objectGetPrototypeOf .undef #[t] none) then
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
            if toBool (← core.callNative (.reflect 2) .undef #[a0, a1] none) then pure a0
            else throwErr .type "Object.setPrototypeOf: the prototype of this object cannot be changed"
          | _ => pure a0
        | _ => throwErr .type "Object prototype may only be an Object or null" 
    | .objectCreate =>
      match a0 with
      | .obj _ | .null =>
        let id ← alloc { proto := a0 }
        -- §20.1.2.2 step 3: ObjectDefineProperties when Properties is not undefined
        if !(a1 matches .undef) then
          let _ ← core.callNative .objectDefineProperties .undef #[.obj id, a1] none
        pure (.obj id)
      | _ => throwErr .type "Object prototype may only be an Object or null"
    | .objectDefineProperty =>
      match a0 with
      | .obj id =>
        let k ← core.toKey a1
        core.defineFromDescriptor id k (argD args 2)
        pure a0
      | _ => throwErr .type "Object.defineProperty called on non-object"
    | .objectGetOwnPropertyDescriptor =>
      let id ← core.toObj a0
      let k ← core.toKey a1
      match ← core.ownDesc id k with
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
            -- the elements become ordinary properties; the object stays an Array (`markArray`)
            let o := ({ o with kind := .ordinary } : Obj).markArray
            let o := (List.range es.size).foldl (fun (o : Obj) i =>
              if Value.isHole es[i]! then o else o.putOwn (toString i) (PropV.data es[i]! true true true)) o
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
        if !toBool (← core.callNative (.reflect 12) .undef #[a0] none) then
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
            match ← core.proxyTrap hnd "isExtensible" with
            | some f =>
              let b := toBool (← core.callV f hnd #[t])
              if b != toBool (← core.callNative .objectIsExtensible .undef #[t] none) then
                throwErr .type "'isExtensible' on proxy: the trap's answer is not the target's"
              return .bool b
            | none => cur := tid
          | _ => return .bool (← getObj cur).extensible
        pure (.bool false)
      | _ => pure (.bool false)
    | .objectGetOwnPropertySymbols =>
      let id ← core.toObj a0
      let ks := (← getObj id).ownKeys.filter isSymKey
      newArray (ks.filterMap fun k => (symOfKey? k).map .sym)
    | .objectAssign =>
      let tid ← core.toObj a0
      for src in args.extract 1 args.size do
        match src with
        | .undef | .null => pure ()
        | _ =>
          let sid ← core.toObj src
          for k in (← getObj sid).ownKeys do
            match (← getObj sid).getOwn k with
            | some p => if p.enumerable then core.putV (.obj tid) k (← core.getV (.obj sid) k) true
            | none => pure ()
      pure (.obj tid)
    | .objectEntries | .objectValues =>
      let id ← core.toObj a0
      let o ← getObj id
      let ks := o.ownStrKeys.filter fun k => match o.getOwn k with | some p => p.enumerable | none => false
      let vs ← ks.mapM fun k => do
        let v ← core.getV (.obj id) k
        if id_ == .objectEntries then newArray #[keyStrV k, v] else pure v
      newArray vs
    | .objectDefineProperties =>
      match a0 with
      | .obj id =>
        -- ObjectDefineProperties (§20.1.2.3.1): every descriptor is read (and checked) before
        -- any property is defined; keys by [[OwnPropertyKeys]], enumerability by [[GetOwnProperty]]
        let pid ← core.toObj a1
        let mut descs : Array (String × Desc) := #[]
        for k in ← core.ownKeysOf pid do
          match ← core.ownDesc pid k with
          | some p =>
            if p.enumerable then descs := descs.push (k, ← core.toPropDesc (← core.getV (.obj pid) k))
          | none => pure ()
        for (k, d) in descs do
          if !(← core.defineOwnProp id k d) then throwErr .type s!"Cannot redefine property: {k}"
        pure a0
      | _ => throwErr .type "Object.defineProperties called on non-object"
    | .objectSeal =>
      match a0 with
      | .obj id =>
        let o ← getObj id
        -- a sealed Array's elements are not configurable: they leave the fast form (`markArray`)
        let o := match o.kind with
          | .array es =>
            let o := ({ o with kind := .ordinary } : Obj).markArray
            let o := (List.range es.size).foldl (fun (o : Obj) i =>
              if Value.isHole es[i]! then o else o.putOwn (toString i) (PropV.data es[i]! true true true)) o
            o.putOwn "length" (.data (.num (Float.ofNat es.size)) true false false)
          | _ => o
        let props := o.props.mapValues (fun p => (match p with
          | .data v w e _ => .data v w e false
          | .acc g s e _ => .acc g s e false))
        modifyObj id fun _ => { o with props, extensible := false }
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
      let id ← core.toObj a0
      let res ← newObject
      for k in (← getObj id).ownKeys do
        let d ← core.callNative .objectGetOwnPropertyDescriptor .undef #[.obj id, keyValue k] none
        defineOwn res k (.data d true true true)
      pure (.obj res)
    | .objectFromEntries =>
      let res ← newObject
      iterEach core (← core.getIterator a0) fun entry => do
        let _ ← addObjectEntry core res entry
        pure ()
      pure (.obj res)
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: Object.prototype and Function. `r` is the realm `callNative` read. -/
def callNativeObjectProto (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | .objectProtoHasOwnProperty =>
      let k ← core.toKey a0
      let id ← core.toObj thisV
      pure (.bool (← core.ownDesc id k).isSome)
    | .objectProtoPropertyIsEnumerable =>
      let k ← core.toKey a0
      let id ← core.toObj thisV
      pure (.bool (match ← core.ownDesc id k with | some p => p.enumerable | none => false))
    -- Annex B.2.2.2 and B.2.2.3: __defineGetter__ (P, getter), __defineSetter__ (P, setter):
    -- DefinePropertyOrThrow(O, key, { [[Get]] or [[Set]]: f, [[Enumerable]]: true, [[Configurable]]: true })
    | .objectProtoDefineGetter | .objectProtoDefineSetter =>
      let o ← core.toObj thisV
      if !(← isCallable a1) then
        throwErr .type (if id matches .objectProtoDefineGetter then "Object.prototype.__defineGetter__: Expecting function"
          else "Object.prototype.__defineSetter__: Expecting function")
      let k ← core.toKey a0
      let d ← newObject
      defineOwn d (if id matches .objectProtoDefineGetter then "get" else "set") (.data a1 true true true)
      defineOwn d "enumerable" (.data (.bool true) true true true)
      defineOwn d "configurable" (.data (.bool true) true true true)
      core.defineFromDescriptor o k (.obj d)
      pure .undef
    -- Annex B.2.2.4 and B.2.2.5: __lookupGetter__ (P), __lookupSetter__ (P): the getter or setter
    -- of the first object on the prototype chain that has P as its own property
    | .objectProtoLookupGetter | .objectProtoLookupSetter =>
      let o ← core.toObj thisV
      let k ← core.toKey a0
      let wantGet := id matches .objectProtoLookupGetter
      let mut cur := o
      let mut res : Value := .undef
      for _ in [0:10000] do
        match ← core.ownDesc cur k with
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
        let me ← core.toObj thisV
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
        let id ← core.toObj thisV
        let custom ← core.getV (.obj id) (symKey symToStringTag)
        let oo ← getObj id
        let builtin := if oo.isArray then "Array" else match oo.kind with
          | .array _ => "Array"
          | .closure .. | .native _ | .bound .. => "Function"
          | .error => "Error"
          | .args => "Arguments"
          | .prim (.bool _) => "Boolean"
          | .prim (.num _) => if hiddenFlag oo dateKey then "Date" else "Number"
          | .prim (.str _) => "String"
          | .regexp .. => "RegExp"
          | _ => "Object"
        let tag := match custom with | .str t => t | _ => builtin
        pure (.str s!"[object {tag}]")
    | .objectProtoToLocaleString => core.callV (← core.getV thisV "toString") thisV #[]
    | .objectProtoValueOf => pure (.obj (← core.toObj thisV))
    | .functionCtor =>
      let strs ← args.toList.mapM (core.toStr)
      let (ps, body) := match strs.reverse with
        | [] => ([], "")
        | b :: rest => (rest.reverse, b)
      let src := dynFunctionSource "function" ps body
      match (parseScript src false).map Resolve.script with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok { body := [.expr e], .. } =>
        core.evalExpr { env := 0, thisV := .obj r.globalObj, strict := false } e
      | .ok _ => throwErr .syntax "invalid function body"
    | .functionProto => pure .undef
    | .functionProtoCall =>
      if !(← isCallable thisV) then throwErr .type "Function.prototype.call called on non-function"
      core.callV thisV a0 (args.extract 1 args.size)
    | .functionProtoApply =>
      if !(← isCallable thisV) then throwErr .type "Function.prototype.apply called on non-function"
      let argv ← match a1 with
        | .undef | .null => pure #[]
        | .obj _ =>
          let len ← core.toNum (← core.getV a1 "length")
          let k := (toIntegerOrInf len).toUInt64.toNat
          (List.range k).toArray.mapM fun i => core.getV a1 (toString i)
        | _ => throwErr .type "CreateListFromArrayLike called on non-object"
      core.callV thisV a0 argv
    | .functionProtoBind =>
      if !(← isCallable thisV) then throwErr .type "Bind must be called on a function"
      -- §20.2.3.2: BoundFunctionCreate (the target's prototype), then `length` from an own
      -- `length` that is a Number (ToIntegerOrInfinity, minus the bound arguments, at least 0),
      -- then `name` ("bound " and a String name, else "")
      let tproto ← match thisV with
        | .obj tid => match (← getObj tid).kind with
          | .proxy .. => core.callNative .objectGetPrototypeOf .undef #[thisV] none
          | _ => pure (← getObj tid).proto
        | _ => pure (.obj r.functionProto)
      let o ← alloc { proto := tproto, kind := .bound thisV a0 (args.extract 1 args.size) }
      let argCount := Float.ofNat (args.size - 1 |>.min args.size)
      let hasLen ← match thisV with
        | .obj tid => do pure ((← core.ownDesc tid "length").isSome)
        | _ => pure false
      let l ← if hasLen then do
          match ← core.getV thisV "length" with
          | .num x =>
            if x == inf then pure inf
            else if x == -inf then pure 0
            else let k := toIntegerOrInf x - argCount; pure (if k < 0 then 0 else k)
          | _ => pure 0
        else pure 0
      defineOwn o "length" (.data (.num l) false false true)
      let nm ← core.getV thisV "name"
      let nm := match nm with | .str s => s | _ => ""
      defineOwn o "name" (.data (.str ("bound " ++ nm)) false false true)
      pure (.obj o)
    | .functionProtoToString =>
      match thisV with
      | .obj id => match (← getObj id).kind with
        -- the engine keeps no source text of functions (§20.2.3.5 step 2 wants it): the
        -- NativeFunction form instead, which Test262's assertToStringOrNativeFunction accepts
        | .closure f .. => pure (.str s!"function {f.name.getD ""}() {"{"} [native code] }")
        | .native _ | .bound .. => pure (.str "function () { [native code] }")
        -- a callable Proxy (§20.2.3.5 step 3): a NativeFunction string
        | .proxy .. =>
          if ← isCallable thisV then pure (.str "function () { [native code] }")
          else throwErr .type "Function.prototype.toString requires that 'this' be a Function"
        | _ => throwErr .type "Function.prototype.toString requires that 'this' be a Function"
      | _ => throwErr .type "Function.prototype.toString requires that 'this' be a Function"
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the Array constructor and the methods that change the array. `r` is the realm `callNative` read. -/
def callNativeArrayEdit (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | .arrayCtor =>
      if args.size == 1 then
        match a0 with
        | .num x =>
          if x < 0 || !isIntegral x || x ≥ twoPow32F then throwErr .range "Invalid array length"
          if x.toUInt64.toNat > maxDenseArray then throwErr .range "Invalid array length"
          charge (x.toUInt64.toNat / 64)
          newArray (Array.replicate x.toUInt64.toNat .hole)
        | v => newArray #[v]
      else newArray args
    | .arrayIsArray => pure (.bool (← isArrayDeep 100000 a0))
    | .arrayPush =>
      match thisV with
      | .obj id =>
        let r ← updateObj id fun o =>
          match o.takeArray with
          | (some es, o) =>
            if o.extensible then let es := es ++ args; (some es.size, { o with kind := .array es })
            else (none, { o with kind := .array es })
          | (none, o) => (none, o)
        match r with
        | some k => pure (.num (Float.ofNat k))
        | none => core.genericPush thisV args
      | _ => core.genericPush thisV args
    | .arrayPop =>
      -- the fast path: a plain Array whose last element is present
      let fast ← match thisV with
        | .obj id =>
          updateObj id fun o =>
            match o.takeArray with
            | (some es, o) =>
              match es.back? with
              | some .hole | none => (none, { o with kind := .array es })
              | some v => (some v, { o with kind := .array es.pop })
            | (none, o) => (none, o)
        | _ => pure none
      match fast with
      | some v => pure v
      | none => core.arrayGeneric id thisV args
    | .arrayShift =>
      -- the fast path: a plain Array with every element present
      let fast ← match thisV with
        | .obj id =>
          updateObj id fun o =>
            match o.takeArray with
            | (some es, o) =>
              if es.size == 0 || es.any (·.isHole) then (none, { o with kind := .array es })
              else (es[0]?, { o with kind := .array (es.eraseIdxIfInBounds 0) })
            | (none, o) => (none, o)
        | _ => pure none
      match fast with
      | some v => pure v
      | none => core.arrayGeneric id thisV args
    | .arrayUnshift =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .array es =>
          if (← getObj oid).extensible && !es.any (·.isHole) then
            modifyObj oid fun o => { o with kind := .array (args ++ es) }
            pure (.num (Float.ofNat (es.size + args.size)))
          else core.arrayGeneric id thisV args
        | _ => core.arrayGeneric id thisV args
      | _ => core.arrayGeneric id thisV args
    | .arraySlice =>
      -- §23.1.3.28: the length, the bounds, then ArraySpeciesCreate(O, count); only the indices
      -- from start to end are read (an array-like's length can be 2^53 - 1)
      let oid ← core.toObj thisV
      let len ← core.arrayLikeLength (.obj oid)
      let k := relIndex (← core.toNum a0) len
      let fin ← match a1 with
        | .undef => pure len
        | v => do pure (relIndex (← core.toNum v) len)
      let count := if fin > k then fin - k else 0
      let sp ← core.speciesFrom (.obj oid) count
      if sp.isNone && count > 4294967295 then throwErr .range "Invalid array length"
      let part ← match (← getObj oid).kind with
        | .array es => pure (if k < fin then es.extract k fin else #[])
        | _ => do
          let m := min count 10000000
          charge (m / 64)
          (List.range m).toArray.mapM fun j => do
            match ← core.elemAt oid (k + j) true with
            | some v => pure v
            | none => pure Value.hole
      match sp with
      | none => newArray part
      | some a => core.speciesFill a part (some count)
    | .arraySplice =>
      let fastOk ← match thisV with
        | .obj id => do
          let ob ← getObj id
          pure (match ob.kind with | .array es => ob.extensible && !es.any (·.isHole) | _ => false)
        | _ => pure false
      if !fastOk then return ← core.arraySpliceGeneric thisV args
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          let s := relIndex (← core.toNum a0) es.size
          let dc ← if args.size < 2 then pure (es.size - s) else do
            let d := toIntegerOrInf (← core.toNum a1)
            pure (if d < 0 then 0 else (min d.toUInt64.toNat (es.size - s)))
          let removed := es.extract s (s + dc)
          let sp ← core.speciesFrom thisV removed.size
          -- the species constructor may have changed the array: take its elements again
          let es ← match (← getObj id).kind with | .array es => pure es | _ => pure es
          let es' := es.extract 0 s ++ args.extract 2 args.size ++ es.extract (s + dc) es.size
          modifyObj id fun o => match o.kind with
            | .array _ => { o with kind := .array es' }
            | _ => o
          match sp with
          | none => newArray removed
          | some a => core.speciesFill a removed (some removed.size)
        | _ => newArray #[]
      | _ => newArray #[]
    | .arrayReverse =>
      match thisV with
      | .obj oid => match (← getObj oid).kind with
        | .array es =>
          if es.any (·.isHole) then core.arrayGeneric id thisV args
          else modifyObj oid (fun o => { o with kind := .array es.reverse }); pure thisV
        | _ => core.arrayGeneric id thisV args
      | _ => core.arrayGeneric id thisV args
    | .arrayFill =>
      -- §23.1.3.7 on any object: ToObject, LengthOfArrayLike, the bounds, Set each index
      let arrayFillGeneric : M Value := do
        let oid ← core.toObj thisV
        let o := Value.obj oid
        let len ← core.arrayLikeLength o
        let s := relIndex (← core.toNum a1) len
        let e ← match argD args 2 with
          | .undef => pure len
          | v => do pure (relIndex (← core.toNum v) len)
        for k in [s:e] do
          tick
          core.putV o (toString k) a0 true
        pure o
      match thisV with
      | .obj id => match (← getObj id).kind with
        | .array es =>
          let s := relIndex (← core.toNum a1) es.size
          let e ← match argD args 2 with
            | .undef => pure es.size
            | v => do pure (relIndex (← core.toNum v) es.size)
          let es' := es.mapIdx fun i v => if s ≤ i && i < e then a0 else v
          modifyObj id fun o => { o with kind := .array es' }
          pure thisV
        | _ => arrayFillGeneric
      | _ => arrayFillGeneric
    | .arraySort =>
      -- §23.1.3.30: the comparator is undefined or callable; SortIndexedProperties takes the
      -- present elements, sorts them, writes them back from 0 and deletes the rest
      if !(a0 matches .undef) && !(← isCallable a0) then
        throwErr .type "The comparison function must be either a function or undefined"
      let oid ← core.toObj thisV
      let o := Value.obj oid
      let fastEs ← match (← getObj oid).kind with
        | .array es => pure (if es.any (·.isHole) then none else some es)
        | _ => pure none
      let (items, len) ← match fastEs with
        | some es => pure (es, es.size)
        | none => do
          let len ← core.arrayLikeLength o
          let mut items : Array Value := #[]
          for k in [0:len] do
            tick
            if ← core.hasProp oid (toString k) then items := items.push (← core.getV o (toString k))
          pure (items, len)
      let sorted := (← core.mergeSort a0 items.toList).toArray
      -- write back into the object as it is now (the comparator may have changed it)
      let wrote ← updateObj oid fun ob =>
        match ob.kind with
        | .array cur =>
          if sorted.size == len && cur.size ≥ len && ob.extensible then
            (true, { ob with kind := .array (sorted ++ cur.extract len cur.size) })
          else (false, ob)
        | _ => (false, ob)
      if !wrote then
        for j in [0:sorted.size] do core.putV o (toString j) sorted[j]! true
        for k in [sorted.size:len] do
          tick
          core.deleteOrThrow o (toString k)
      pure o
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the Array methods that read the array, and its iterators. `r` is the realm `callNative` read. -/
def callNativeArrayRead (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .arrayJoin | .arrayToString =>
      -- a cycle (the array met again while it is being joined) is an implementation limit:
      -- RangeError, as exhausting the stack is in other engines, and never a native overflow
      let self? : Option Nat := match thisV with | .obj o => some o | _ => none
      if let some o := self? then
        if hiddenFlag (← getObj o) joiningKey then throwErr .range "Maximum call stack size exceeded"
        setHidden o joiningKey (.bool true)
      let res ← catchJS (do
          let es ← core.elemsOf thisV
          let sep ← if id == .arrayJoin then (match a0 with | .undef => pure "," | v => core.toStr v) else pure ","
          let parts ← es.toList.mapM fun v => match v with
            | .undef | .null => pure ""
            | v => core.toStr v
          checkStrLen (parts.foldl (fun acc t => acc + t.utf8ByteSize + sep.utf8ByteSize) 0)
          pure (Except.ok (Value.str (Str.canonical (sep.intercalate parts)))))
        (fun a => pure (Except.error a))
      if let some o := self? then deleteOwn o joiningKey
      match res with
      | .ok v => pure v
      | .error a => throw a
    | .arrayIndexOf | .arrayIncludes =>
      -- §23.1.3.17, §23.1.3.16: indexOf skips absent indices (HasProperty) and uses ===;
      -- includes reads every index and uses SameValueZero
      let oid ← core.toObj thisV
      let len ← core.arrayLikeLength (.obj oid)
      if len == 0 then return (if id == .arrayIncludes then .bool false else .num (-1))
      let start := relIndex (← core.toNum a1) len
      let mut found : Option Nat := none
      for k in [start:len] do
        let x? ← core.elemAt oid k (id == .arrayIndexOf)
        if let some x := x? then
          if (if id == .arrayIncludes then sameValueZero x a0 else strictEq x a0) then
            found := some k
            break
      if id == .arrayIncludes then pure (.bool found.isSome)
      else pure (.num (match found with | some i => Float.ofNat i | none => -1))
    | .arrayLastIndexOf =>
      -- §23.1.3.20: from fromIndex (default len - 1) down to 0, skipping absent indices
      let oid ← core.toObj thisV
      let len ← core.arrayLikeLength (.obj oid)
      if len == 0 then return .num (-1)
      let from_ ← if args.size ≥ 2 then do
          let x := toIntegerOrInf (← core.toNum a1)
          pure (if x ≥ 0 then (if x ≥ len.toFloat then some (len - 1) else some x.toUInt64.toNat)
            else let k := len.toFloat + x; if k < 0 then none else some k.toUInt64.toNat)
        else pure (some (len - 1))
      let some start := from_ | return .num (-1)
      let mut found : Option Nat := none
      for j in [0:start + 1] do
        let k := start - j
        let x? ← core.elemAt oid k true
        if let some x := x? then
          if strictEq x a0 then
            found := some k
            break
      pure (.num (match found with | some i => Float.ofNat i | none => -1))
    | .arrayConcat =>
      -- §23.1.3.1: O, then each argument; a spreadable one (IsConcatSpreadable: its
      -- @@isConcatSpreadable, else IsArray) gives its present elements at their offsets
      let oid ← core.toObj thisV
      let sp ← core.speciesFrom (.obj oid) 0
      let mut acc : Array Value := #[]
      for e in #[Value.obj oid] ++ args do
        tick
        let spreadable ← match e with
          | .obj _ =>
            match ← core.getV e (symKey 6) with
            | .undef => isArrayDeep 100000 e
            | v => pure (toBool v)
          | _ => pure false
        if !spreadable then
          if acc.size ≥ 9007199254740991 then throwErr .type "Concatenating past the largest array length"
          acc := acc.push e
          continue
        let .obj eid := e | continue
        match (← getObj eid).kind with
        | .array more =>
          -- a plain Array: its elements; an absent one is looked up the prototype chain
          if more.any (·.isHole) then
            for k in [0:more.size] do
              acc := acc.push ((← core.elemAt eid k true).getD .hole)
          else acc := acc ++ more
        | _ =>
          let len ← core.arrayLikeLength e
          if acc.size + len > 9007199254740991 then throwErr .type "Concatenating past the largest array length"
          for k in [0:len] do
            tick
            if acc.size ≥ maxDenseArray then throwErr .range "Invalid array length"
            acc := acc.push ((← core.elemAt eid k true).getD .hole)
      match sp with
      | none => newArray acc
      | some a => core.speciesFill a acc (some acc.size)
    | .arrayMap | .arrayForEach | .arrayFilter | .arraySome | .arrayEvery | .arrayFind
    | .arrayFindIndex =>
      -- §23.1.3: ToObject(this), LengthOfArrayLike, then the callback's check
      let oid ← core.toObj thisV
      let len ← core.arrayLikeLength (.obj oid)
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      -- map's ArraySpeciesCreate(O, len) is an ArrayCreate: a RangeError past 2^32 - 1
      if id == .arrayMap && len > 4294967295 then throwErr .range "Invalid array length"
      -- the indices visited stop at 10^7, as the element copy did before (an array-like
      -- whose length is 2^53 - 1 would not end)
      let sp ← if id == .arrayMap || id == .arrayFilter then
          core.speciesFrom (.obj oid) (if id == .arrayMap then len else 0) else pure none
      let res ← core.iterArray id a0 a1 (.obj oid) (min len 10000000) 0 #[]
      match sp with
      | none => pure res
      | some a => core.speciesFill a (← rawElems res) none
    | .arrayReduce =>
      -- §23.1.3.24: the first present element is the start when there is no initial value
      let oid ← core.toObj thisV
      let len ← core.arrayLikeLength (.obj oid)
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      if args.size ≥ 2 then core.reduceArray a0 (.obj oid) len 0 a1
      else
        let mut k := 0
        let mut first : Option Value := none
        for _ in [0:len] do
          if first.isSome then break
          first ← core.elemAt oid k true
          k := k + 1
        match first with
        | some acc => core.reduceArray a0 (.obj oid) len k acc
        | none => throwErr .type "Reduce of empty array with no initial value"
    | .arrayValues | .arrayKeys | .arrayEntries =>
      let o ← core.toObj thisV
      let mode := match id_ with | .arrayKeys => 1 | .arrayEntries => 2 | _ => 0
      pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter (.obj o) 0 mode }))
    | .arrayFlat | .arrayFlatMap =>
      -- flat skips absent elements (`flattenArr`); flatMap's callback sees them as undefined
      let raw ← match thisV with
        | .obj tid => match (← getObj tid).kind with
          | .array es => pure (if id_ == .arrayFlat then some es else none)
          | _ => pure none
        | _ => pure none
      let es ← match raw with | some es => pure es | none => core.elemsOf thisV
      let es ← if id_ == .arrayFlatMap then do
          if !(← isCallable a0) then throwErr .type "flatMap mapper is not callable"
          (List.range es.size).toArray.mapM fun i => core.callV a0 a1 #[es[i]!, .num (Float.ofNat i), thisV]
        else pure es
      let depth := if id_ == .arrayFlatMap then 1 else match a0 with
        | .undef => 1
        | .num d => if d.isNaN || d < 1 then 0 else (if d > 1000 then 1000 else d.toUInt64.toNat)
        | _ => 1
      let flat ← flattenArr depth es (depth + 1)
      match ← core.speciesFrom thisV 0 with
      | none => newArray flat
      | some a => core.speciesFill a flat none
    | .arrayAt =>
      let receiver := Value.obj (← core.toObj thisV)
      let len ← core.arrayLikeLength receiver
      arrayAtWithLength core receiver len a0
    | .arrayFindLast | .arrayFindLastIndex =>
      if !(← isCallable a0) then throwErr .type "callback is not a function"
      let es ← core.elemsOf thisV
      let mut found : Option Nat := none
      for j in [0:es.size] do
        let i := es.size - 1 - j
        if found.isNone then
          if toBool (← core.callV a0 a1 #[es[i]!, .num (Float.ofNat i), thisV]) then found := some i
      match found with
      | some i => pure (if id_ == .arrayFindLast then es[i]! else .num (Float.ofNat i))
      | none => pure (if id_ == .arrayFindLast then .undef else .num (-1))
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: `Array.from` and `Array.of`. `r` is the realm `callNative` read. -/
def callNativeArrayFrom (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | .arrayFrom =>
      -- §23.1.2.1: `this` makes the result when it is a constructor other than Array; a map
      -- function's error closes the iterator
      let mapFn := a1
      let mapping := !(mapFn matches .undef)
      if mapping && !(← isCallable mapFn) then throwErr .type "Array.from: the map function is not callable"
      let custom ← match thisV with
        | .obj cid => do
          let k := (← getObj cid).kind
          pure ((← isConstructor thisV) && !(match k with | .native .arrayCtor => true | _ => false))
        | _ => pure false
      match a0 with
      | .undef | .null => throwErr .type "Array.from requires an array-like or iterable"
      | _ => pure ()
      let put (a : Value) (i : Nat) (v : Value) : M Unit := do
        let .obj aid := a | throwErr .type "Array.from: the constructor did not make an object"
        if !(← core.defineOwnProp aid (toString i) { value := some v, writable := some true, enumerable := some true, configurable := some true }) then
          throwErr .type s!"Cannot define property {i} of the Array.from result"
      let usingIter ← core.getV a0 (symKey symIterator)
      match usingIter with
      | .undef | .null =>
        let oid ← core.toObj a0
        let len ← core.arrayLikeLength (.obj oid)
        let a ← if custom then some <$> core.construct thisV #[.num (Float.ofNat len)] thisV else pure none
        if a.isNone && len > 4294967295 then throwErr .range "Invalid array length"
        let m := min len 10000000
        charge (m / 64)
        let mut vs : Array Value := #[]
        for i in [0:m] do
          let v ← core.getV (.obj oid) (toString i)
          let v ← if mapping then core.callV mapFn (argD args 2) #[v, .num (Float.ofNat i)] else pure v
          match a with
          | some a => put a i v
          | none => vs := vs.push v
        match a with
        | none => newArray vs
        | some a => core.putV a "length" (.num (Float.ofNat len)) true; pure a
      | _ =>
        let a ← if custom then some <$> core.construct thisV #[] thisV else pure none
        if !(← isCallable usingIter) then throwErr .type "Array.from: Symbol.iterator is not a function"
        let it ← core.callV usingIter a0 #[]
        if !it.isObj then throwErr .type "Result of the Symbol.iterator method is not an object"
        let mut vs : Array Value := #[]
        let mut k := 0
        for _ in [0:10000000] do
          tick
          match ← core.iterStep it with
          | none => break
          | some v =>
            -- an abrupt completion of the mapping or the definition closes the iterator first
            let v ← catchJS (do
                let v ← if mapping then core.callV mapFn (argD args 2) #[v, .num (Float.ofNat k)] else pure v
                if let some a := a then put a k v
                pure v)
              fun e => do
                catchJS (core.iterClose it) fun _ => pure ()
                throw e
            if a.isNone then vs := vs.push v
            k := k + 1
        match a with
        | none => newArray vs
        | some a => core.putV a "length" (.num (Float.ofNat k)) true; pure a
    | .arrayOf =>
      let custom ← match thisV with
        | .obj cid => do
          let kd := (← getObj cid).kind
          pure ((← isConstructor thisV) && !(match kd with | .native .arrayCtor => true | _ => false))
        | _ => pure false
      if custom then
        let a ← core.construct thisV #[.num (Float.ofNat args.size)] thisV
        core.speciesFill a args (some args.size)
      else newArray args
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the String constructor and the String methods kept here. `r` is the realm `callNative` read. -/
def callNativeString (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .stringCtor =>
      let s ← match a0, newTarget with
        | .sym id, none => pure ("Symbol(" ++ (← get).syms.getD id "" ++ ")")
        | _, _ => if args.isEmpty then pure "" else core.toStr a0
      match newTarget with
      | some _ => pure (.obj (← alloc { proto := .obj r.stringProto, kind := .prim (.str s) }))
      | none => pure (.str s)
    | .stringFromCharCode =>
      let us ← args.toList.mapM fun a => do pure ((toUint32 (← core.toNum a)) % 65536)
      pure (.str (Str.ofCodeUnits us))
    | .stringToString =>
      match ← thisPrim thisV with
      | .str s => pure (.str s)
      | _ => throwErr .type "String.prototype.toString requires that 'this' be a String"
    | .stringIterator =>
      match thisV with
      | .undef | .null => throwErr .type "String.prototype[Symbol.iterator] called on null or undefined"
      | _ =>
        let s ← core.toStr thisV
        pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter (.str s) 0 3 }))
    | .stringAt =>
      -- §22.1.3.1: one code unit, found in constant time for ASCII (`Str.unitStrAt?`)
      let s ← core.toStr (← thisPrim thisV)
      let len := Str.jsLength s
      let k := toIntegerOrInf (← core.toNum a0)
      let i := if k < 0 then Float.ofNat len + k else k
      if i < 0 || i ≥ Float.ofNat len then pure .undef
      else pure ((Str.unitStrAt? s i.toUInt64.toNat).map Value.str |>.getD .undef)
    | .stringPadStart | .stringPadEnd =>
      let s ← core.toStr (← thisPrim thisV)
      let len := toIntegerOrInf (← core.toNum a0)
      let fill ← match a1 with | .undef => pure " " | v => core.toStr v
      let cur := Str.jsLength s
      if len ≤ Float.ofNat cur || fill.isEmpty then pure (.str s) else
      let need := len.toUInt64.toNat - cur
      if need > maxStringBytes then throwErr .range "Invalid string length"
      charge (need / 64)
      let reps := repeatStr fill (need / Str.jsLength fill + 1)
      let pad := substr reps 0 need
      pure (.str (if id_ == .stringPadStart then Str.jsAppend pad s else Str.jsAppend s pad))
    | .stringCodePointAt =>
      let s ← core.toStr (← thisPrim thisV)
      let i := toIntegerOrInf (← core.toNum a0)
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
      let s ← core.toStr (← thisPrim thisV)
      let cs := s.toList
      pure (.str (if id_ == .stringTrimStart then String.ofList (cs.dropWhile isStrWs)
        else String.ofList (cs.reverse.dropWhile isStrWs).reverse))
    | .stringReplace | .stringReplaceAll =>
      if let some v ← core.stringSymDispatch id_ thisV args then return v
      let s ← core.toStr (← thisPrim thisV)
      let pat ← core.toStr a0
      let fnRepl ← isCallable a1
      let replStr ← if fnRepl then pure "" else core.toStr a1
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
        let r ← if fnRepl then core.toStr (← core.callV a1 .undef #[.str pat, .num (Float.ofNat p), .str s])
          else pure (if replStr.contains '$' then getSubstitutionG replStr pat s p #[] none else replStr)
        checkStrLen (out.utf8ByteSize + r.utf8ByteSize)
        out := out ++ r
        last := p + Str.jsLength pat
      pure (.str (Str.canonical (out ++ substr s last (Str.jsLength s))))
    | .stringFromCodePoint =>
      let cs ← args.toList.mapM fun a => do
        let x ← core.toNum a
        if !isIntegral x || x < 0 || x > 1114111 then throwErr .range s!"Invalid code point {numToString x}"
        pure (Str.ofCodePoint x.toUInt64.toNat)
      pure (.str (Str.canonical (String.join cs)))
    | .stringSplit =>
      if let some v ← core.stringSymDispatch id thisV args then return v
      core.stringOrMath id thisV args
    | .stringMatch | .stringSearch =>
      if let some v ← core.stringSymDispatch id thisV args then return v
      Natives.extraNative core id thisV args newTarget
    | .stringMatchAll =>
      if let some v ← core.stringSymDispatch id thisV args then return v
      let s ← core.toStr thisV
      let rx ← match a0 with
        | .undef => newRegExp "(?:)" "g"
        | _ => do newRegExp (← core.toStr a0) "g"
      core.regexpSymbol 4 rx #[.str s]
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: Number, Boolean, Math and BigInt. `r` is the realm `callNative` read. -/
def callNativeNumber (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .numberCtor =>
      -- §21.1.1.1: ToNumeric, and a BigInt becomes the Number of its value.
      let x ← if args.isEmpty then pure 0 else match ← core.toPrim a0 "number" with
        | .big i => pure (Float.ofInt i)
        | p => core.toNum p
      match newTarget with
      | some _ => pure (.obj (← alloc { proto := .obj r.numberProto, kind := .prim (.num x) }))
      | none => pure (.num x)
    | .numberValueOf | .numberToString | .numberToFixed =>
      -- thisNumberValue (§21.1.3): a Number or a Number object; a Date's time value is not one
      if (← thisDate? thisV).isSome then throwErr .type "Number.prototype method requires that 'this' be a Number"
      let x ← match ← thisPrim thisV with
        | .num x => pure x
        | _ => throwErr .type "Number.prototype method requires that 'this' be a Number"
      match id with
      | .numberValueOf => pure (.num x)
      | .numberToString =>
        let radix ← match a0 with | .undef => pure 10 | v => do pure (toIntegerOrInf (← core.toNum v))
        if radix < 2 || radix > 36 then throwErr .range "toString() radix must be between 2 and 36"
        pure (.str (toStringRadix x radix.toUInt64.toNat))
      | _ =>
        let d := toIntegerOrInf (← core.toNum a0)
        if d < 0 || d > 100 then throwErr .range "toFixed() digits argument must be between 0 and 100"
        if x.abs ≥ 1e21 || !x.isFinite then pure (.str (numToString x)) else
        -- a 64-bit fast path with the exact path behind it (JS/NumFmt.lean, issue 1076)
        pure (.str (NumFmt.fixedOf x d.toUInt64.toNat))
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
    | .numberIsFinite => pure (.bool (match a0 with | .num x => x.isFinite | _ => false))
    | .numberIsNaN => pure (.bool (match a0 with | .num x => x.isNaN | _ => false))
    | .numberIsSafeInteger => pure (.bool (match a0 with | .num x => isIntegral x && x.abs ≤ maxSafeF | _ => false))
    | .math1 op =>
      let x ← core.toNum a0
      pure (.num (match op with
        | 0 => Float.cbrt x | 1 => Float.log2 x | 2 => Float.log10 x | 3 => Float.sinh x
        | 4 => Float.cosh x | 5 => Float.tanh x | 6 => Float.asin x | 7 => Float.acos x
        | 8 => Float.asinh x | 9 => Float.acosh x | 10 => Float.atanh x
        | 11 => mathExpMinusOne x
        | 12 => mathLogOnePlus x
        | 14 => L4Factoidal.Prim.Float16.round x
        | _ => x.toFloat32.toFloat))
    | .mathHypot =>
      let xs ← args.toList.mapM (core.toNum)
      if xs.any Float.isInf then pure (.num inf)
      else pure (.num (Float.sqrt (xs.foldl (fun a x => a + x * x) 0)))
    | .mathImul =>
      let a := toInt32 (← core.toNum a0); let b := toInt32 (← core.toNum a1)
      pure (intV (toInt32 (Float.ofInt (a * b % 4294967296))))
    | .mathClz32 =>
      let x := toUint32 (← core.toNum a0)
      pure (.num (Float.ofNat (if x == 0 then 32 else 31 - Nat.log2 x)))
    | .bigintCtor =>
      if newTarget.isSome then throwErr .type "BigInt is not a constructor"
      match ← core.toPrim a0 "number" with
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
      let bf := toIntegerOrInf (← core.toNum a0)
      if bf < 0 || bf > 9007199254740991 then throwErr .range "Invalid value: not (convertible to) a safe integer"
      let bits := bf.toUInt64.toNat
      if bits > 1000000 then throwErr .range "Maximum BigInt size exceeded"
      -- ToBigInt (§7.1.13): a Number is a TypeError.
      let x ← match ← core.toPrim a1 "number" with
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
        let radix ← match a0 with | .undef => pure 10 | v => do pure (toIntegerOrInf (← core.toNum v))
        if radix < 2 || radix > 36 then throwErr .range "toString() radix must be between 2 and 36"
        pure (.str ((if i < 0 then "-" else "") ++ natToRadix radix.toUInt64.toNat i.natAbs))
      | _ => throwErr .type "BigInt.prototype method requires that 'this' be a BigInt"
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: Error, `JSON.stringify` and Symbol. `r` is the realm `callNative` read. -/
def callNativeError (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .errorCtor k =>
      let proto ← match newTarget with
        | some nt => do
          let p ← core.getV nt "prototype"
          let nr ← funRealm nt
          pure (if p.isObj then p else .obj (nr.errorProtos.getD k nr.objectProto))
        | none => pure (.obj (r.errorProtos.getD k r.objectProto))
      let o ← alloc { proto, kind := .error }
      match a0 with
      | .undef => pure ()
      | v => setHidden o "message" (.str (← core.toStr v))
      pure (.obj o)
    | .errorToString =>
      if !thisV.isObj then throwErr .type "Error.prototype.toString called on non-object"
      let nm ← core.getV thisV "name"
      let nm ← match nm with | .undef => pure "Error" | v => core.toStr v
      let msg ← core.getV thisV "message"
      let msg ← match msg with | .undef => pure "" | v => core.toStr v
      pure (.str (if nm.isEmpty then msg else if msg.isEmpty then nm else nm ++ ": " ++ msg))
    | .jsonStringify =>
      -- §25.5.2.1 JSON.stringify(value, replacer, space)
      let mut plist : Option (Array String) := none
      let mut repl := Value.undef
      if a1.isObj then
        if ← isCallable a1 then repl := a1
        else if ← isArrayDeep 100000 a1 then
          let len ← core.arrayLikeLength a1
          let mut ks : Array String := #[]
          for i in [0:len] do
            tick
            let v ← core.getV a1 (toString i)
            let item ← match v with
              | .str t => pure (some t)
              | .num x => pure (some (numToString x))
              | .obj vid => do
                match (← getObj vid).kind with
                | .prim (.str _) | .prim (.num _) => pure (some (← core.toStr v))
                | _ => pure none
              | _ => pure none
            if let some t := item then
              if !ks.contains (strKey t) then ks := ks.push (strKey t)
          plist := some ks
      let mut space := argD args 2
      if let .obj sid := space then
        match (← getObj sid).kind with
        | .prim (.num _) => space := .num (← core.toNum space)
        | .prim (.str _) => space := .str (← core.toStr space)
        | _ => pure ()
      let gap := match space with
        | .num x =>
          let k := toIntegerOrInf x
          let k := if k > 10 then 10 else k
          if k ≥ 1 then String.ofList (List.replicate k.toUInt64.toNat ' ') else ""
        | .str t => Str.sliceUnits t 0 (min 10 (Str.jsLength t))
        | _ => ""
      let wrapper ← newObject
      defineOwn wrapper "" (.data a0 true true true)
      match ← core.jsonSer repl plist gap "" #[] (.obj wrapper) "" with
      | some t => pure (.str (Str.canonical t))
      | none => pure .undef
    | .symbolCtor =>
      if newTarget.isSome then throwErr .type "Symbol is not a constructor"
      let d ← match a0 with | .undef => pure "" | v => core.toStr v
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
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the built-in iterators' `next`, generators and async functions. `r` is the realm `callNative` read. -/
def callNativeGenerator (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
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
        if mode ≥ 20 then
          -- %RegExpStringIteratorPrototype%.next (§22.2.9.2.1)
          if let .undef := target then return ← result .undef true
          let s := match (← getObj id).props.get? rsiStringKey with
            | some (.data (.str s) ..) => s
            | _ => ""
          let m ← core.regExpExecG target s
          let finish : M Unit := modifyObj id fun o => { o with kind := .iter .undef idx mode }
          if let .null := m then finish; return ← result .undef true
          if mode % 2 == 0 then finish; return ← result m false
          if (← core.toStr (← core.getV m "0")).isEmpty then
            let x := toIntegerOrInf (← core.toNum (← core.getV target "lastIndex"))
            let li := if x ≤ 0 then 0 else if x ≥ 9007199254740991.0 then 9007199254740991 else x.toUInt64.toNat
            core.putV target "lastIndex" (.num (Float.ofNat (advanceIndex s li ((mode / 2) % 2 == 1)))) true
          return ← result m false
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
              | _ => do pure (toIntegerOrInf (← core.toNum (← core.getV target "length"))).toUInt64.toNat
            | _ => pure 0
          if idx < len then
            modifyObj id fun o => { o with kind := .iter target (idx + 1) mode }
            match mode with
            | 1 => result (.num (Float.ofNat idx)) false
            | 2 =>
              let v ← core.getV target (toString idx)
              result (← newArray #[.num (Float.ofNat idx), v]) false
            | _ => result (← core.getV target (toString idx)) false
          else
            modifyObj id fun o => { o with kind := .iter .undef idx mode }
            result .undef true
      | _ => throwErr .type "next method called on incompatible receiver"
    | .iterSelf => pure thisV
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
          core.agenDrain gid
        | _ => core.rejectPromise pid (← mkError .type "not an async generator")
      | _ => core.rejectPromise pid (← mkError .type "not an async generator")
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
          | 0 => core.agenRun gid fs (.send v)
          | 1 => core.agenRun gid fs (.throwV v)
          | 2 => finish 1; core.resolvePromise pid (← core.iterResult v false); core.agenDrain gid
          | 3 => core.agenRun gid fs (.retV v)
          | 4 => finish 3; core.resolvePromise pid (← core.iterResult v true); core.agenDrain gid
          | _ => finish 3; core.rejectPromise pid v; core.agenDrain gid
        | _ => pure ()
        pure .undef
      | _ => pure .undef
    | .asyncResume =>
      match a0 with
      | .obj co =>
        let input := if (match a1 with | .num m => m == 1 | _ => false) then GInput.throwV (argD args 2)
          else .send (argD args 2)
        core.asyncStep co input
        pure .undef
      | _ => pure .undef
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
          let r ← catchJS (do pure (Except.ok (← core.genRun frames input)))
            (fun a => pure (Except.error a))
          match r with
          | .error a => setG [] 3; throw a
          | .ok (.yielded v fs) => setG fs 1; result v false
          | .ok (.awaited _ _) => setG [] 3; throwErr .syntax "await outside an async function"
          | .ok (.done v) => setG [] 3; result v true
      | _ => throwErr .type "next method called on incompatible receiver"
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the Promise constructor, its prototype methods, `resolve`, `reject` and the jobs. `r` is the realm `callNative` read. -/
def callNativePromise (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .promiseCtor =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Promise constructor cannot be invoked without 'new'"
      if !(← isCallable a0) then throwErr .type "Promise resolver is not a function"
      let pid ← newPromise
      let pp ← core.getV nt "prototype"
      let pp ← if pp.isObj then pure pp else pure (.obj (← funRealm nt).promiseProto)
      modifyObj pid fun o => { o with proto := pp }
      let res ← anonFn .promiseResolveFn #[.obj pid] 1
      let rej ← anonFn .promiseRejectFn #[.obj pid] 1
      let x ← catchJS (do let _ ← core.callV a0 .undef #[res, rej]; pure none) (fun a => pure (some a))
      match x with
      | some (.throw e) => let _ ← core.callV rej .undef #[e]
      | some a => throw a
      | none => pure ()
      pure (.obj pid)
    | (.x .promiseInitOn) =>
      -- the Promise constructor's steps on an object a subclass constructor made (`this`)
      if !(← isCallable a0) then throwErr .type "Promise resolver is not a function"
      let .obj pid := thisV | throwErr .type "Promise constructor: no object"
      modifyObj pid fun o => { o with kind := .promise 0 .undef #[] false }
      let res ← anonFn .promiseResolveFn #[.obj pid] 1
      let rej ← anonFn .promiseRejectFn #[.obj pid] 1
      let x ← catchJS (do let _ ← core.callV a0 .undef #[res, rej]; pure none) (fun a => pure (some a))
      match x with
      | some (.throw e) => let _ ← core.callV rej .undef #[e]
      | some a => throw a
      | none => pure ()
      pure thisV
    | .promiseResolveFn | .promiseRejectFn =>
      match a0 with
      | .obj pid =>
        match (← getObj pid).kind with
        | .promise st v rs false =>
          modifyObj pid fun o => { o with kind := .promise st v rs true }
          if id_ == .promiseResolveFn then core.resolvePromise pid a1 else core.rejectPromise pid a1
        | _ => pure ()
        pure .undef
      | _ => pure .undef
    | .promiseThen =>
      let pid ← match thisV with
        | .obj p => match (← getObj p).kind with
          | .promise .. => pure p
          | _ => throwErr .type "Promise.prototype.then called on an incompatible receiver"
        | _ => throwErr .type "Promise.prototype.then called on an incompatible receiver"
      -- §27.2.5.4: C = SpeciesConstructor(promise, %Promise%), NewPromiseCapability(C)
      let c ← core.speciesCtor thisV (.obj r.promiseCtor)
      let onF := if ← isCallable a0 then a0 else .undef
      let onR := if ← isCallable a1 then a1 else .undef
      if strictEq c (.obj r.promiseCtor) then
        let d ← newPromise
        core.performThen pid onF onR (.obj d)
        pure (.obj d)
      else
        let cap ← core.callNative (.x .promiseWithResolvers) c #[] none
        -- the derived capability: a record with resolve and reject (not a promise)
        let rec_ ← alloc { proto := .null }
        setHidden rec_ "resolve" (← core.getV cap "resolve")
        setHidden rec_ "reject" (← core.getV cap "reject")
        core.performThen pid onF onR (.obj rec_)
        core.getV cap "promise"
    | .promiseCatch =>
      let th ← core.getV thisV "then"
      if !(← isCallable th) then throwErr .type "then is not a function"
      core.callV th thisV #[.undef, a0]
    | .promiseFinally =>
      -- §27.2.5.3 Promise.prototype.finally
      if !thisV.isObj then throwErr .type "Promise.prototype.finally called on a non-object"
      let c ← core.speciesCtor thisV (.obj r.promiseCtor)
      let th ← core.getV thisV "then"
      if !(← isCallable th) then throwErr .type "then is not a function"
      if !(← isCallable a0) then return ← core.callV th thisV #[a0, a0]
      let f ← anonFn .promiseFinallyF #[a0, c] 1
      let g ← anonFn .promiseFinallyR #[a0, c] 1
      core.callV th thisV #[f, g]
    | .promiseFinallyF | .promiseFinallyR =>
      -- Then Finally / Catch Finally functions: onFinally(), PromiseResolve(C, result), then
      -- Invoke(promise, "then", « valueThunk or thrower »)
      let res ← core.callV a0 .undef #[]
      let p ← core.callNative .promiseResolveStatic a1 #[res] none
      let k ← anonFn (if id_ == .promiseFinallyF then .promiseValueThunk else .promiseThrower) #[argD args 2] 0
      core.callV (← core.getV p "then") p #[k]
    | .promiseValueThunk => pure a0
    | .promiseThrower => throw (.throw a0)
    | .promiseResolveStatic =>
      -- §27.2.4.7 Promise.resolve: PromiseResolve(C, x) on the constructor `this`
      if !thisV.isObj then throwErr .type "Promise.resolve called on a non-object"
      if strictEq thisV (.obj r.promiseCtor) then return .obj (← core.promiseResolve a0)
      if let .obj xid := a0 then
        if let .promise .. := (← getObj xid).kind then
          if strictEq (← core.getV a0 "constructor") thisV then return a0
      let cap ← core.callNative (.x .promiseWithResolvers) thisV #[] none
      let _ ← core.callV (← core.getV cap "resolve") .undef #[a0]
      core.getV cap "promise"
    | .promiseRejectStatic =>
      -- §27.2.4.6 Promise.reject: NewPromiseCapability(C), then its reject
      if !thisV.isObj then throwErr .type "Promise.reject called on a non-object"
      if strictEq thisV (.obj r.promiseCtor) then
        let p ← newPromise
        core.rejectPromise p a0
        return .obj p
      let cap ← core.callNative (.x .promiseWithResolvers) thisV #[] none
      let _ ← core.callV (← core.getV cap "reject") .undef #[a0]
      core.getV cap "promise"
    | .promiseReactionJob =>
      -- args: handler, derived promise (or a capability record of another constructor),
      -- argument, rejected?
      let settleDerived (derived : Value) (rej : Bool) (v : Value) : M Unit := do
        match derived with
        | .obj d =>
          match (← getObj d).kind with
          | .promise .. => if rej then core.rejectPromise d v else core.resolvePromise d v
          | _ => let _ ← core.callV (← core.getV derived (if rej then "reject" else "resolve")) .undef #[v]
        | _ => pure ()
      let handler := a0
      let derived := a1
      let arg := argD args 2
      let rejected := toBool (argD args 3)
      if ← isCallable handler then
        let x ← catchJS (do pure (Except.ok (← core.callV handler .undef #[arg]))) (fun a => pure (Except.error a))
        match x with
        | .error (.halt w) => throw (.halt w)
        | .ok v => settleDerived derived false v
        | .error (.throw e) => settleDerived derived true e
      else settleDerived derived rejected arg
      pure .undef
    | .promiseThenableJob =>
      match a0 with
      | .obj pid =>
        -- CreateResolvingFunctions (§27.2.1.3): a new pair with its own [[AlreadyResolved]]
        -- record. The promise's own flag is already set when its resolve function was called
        -- with the thenable, so a pair that read that flag could never settle the promise
        -- (`new Promise(r => r(otherPromise))` stayed pending for ever, before 2026-11-14).
        let record ← alloc { proto := .null }
        let res ← anonFn (.x (.promiseThenableFn false)) #[.obj pid, .obj record] 1
        let rej ← anonFn (.x (.promiseThenableFn true)) #[.obj pid, .obj record] 1
        let x ← catchJS (do let _ ← core.callV (argD args 2) a1 #[res, rej]; pure none) (fun a => pure (some a))
        match x with
        | some (.throw e) => let _ ← core.callV rej .undef #[e]
        | some a => throw a
        | none => pure ()
        pure .undef
      | _ => pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: the Promise combinators (`all`, `allSettled`, `any`, `race`, the keyed ones) and their element functions. `r` is the realm `callNative` read. -/
def callNativePromiseAll (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .promiseAll | (.x (.promiseCombinator _)) | (.x .promiseAny) =>
      -- §27.2.4.1 Promise.all, §27.2.4.2 allSettled, §27.2.4.3 any, §27.2.4.5 race, on the
      -- constructor `this`: kind 0 race, 1 allSettled, 2 all, 3 any
      let kind : Nat := match id_ with
        | .promiseAll => 2 | (.x (.promiseCombinator 0)) => 0 | (.x (.promiseCombinator _)) => 1 | _ => 3
      -- NewPromiseCapability(C): its abrupt completions are thrown, not a rejected promise
      let cap ← core.callNative (.x .promiseWithResolvers) thisV #[] none
      let capP ← core.getV cap "promise"
      let capRes ← core.getV cap "resolve"
      let capRej ← core.getV cap "reject"
      -- IfAbruptRejectPromise (§27.2.1.1.1)
      let rejectWith : Abrupt → M Value := fun a => do
        match a with
        | .throw e => let _ ← core.callV capRej .undef #[e]; pure capP
        | a => throw a
      -- GetPromiseResolve(C) (§27.2.4.1.1)
      let pr ← catchJS (do
          let f ← core.getV thisV "resolve"
          if !(← isCallable f) then throwErr .type "Promise resolve is not a function"
          pure (Except.ok f)) (fun a => pure (Except.error a))
      if let .error a := pr then return ← rejectWith a
      let resolveF := match pr with | .ok f => f | .error _ => .undef
      let itR ← catchJS (do pure (Except.ok (← core.getIterator a0))) (fun a => pure (Except.error a))
      if let .error a := itR then return ← rejectWith a
      let it := match itR with | .ok it => it | .error _ => .undef
      -- values (or errors), remainingElementsCount and the list length: internal records
      let vals ← alloc { proto := .null }
      let counter ← alloc { proto := .null }
      setHidden counter "n" (.num 1)
      setHidden counter "len" (.num 0)
      let elementFn (nid : Native) (target : Value) (idx : Nat) (called : Nat) : M Value := do
        let nf ← nativeFn nid
        let f ← alloc { proto := .obj r.functionProto, kind := .bound nf .undef #[target, .obj vals, .obj counter, .num (Float.ofNat idx), .obj called] }
        -- CreateBuiltinFunction(…, 1, "") (§27.2.4.1.3 and the others)
        defineOwn f "length" (.data (.num 1) false false true)
        defineOwn f "name" (.data (.str "") false false true)
        pure (.obj f)
      let mut index := 0
      -- (iterator done, the abrupt completion) when the loop ends abruptly
      let mut out : Option (Bool × Abrupt) := none
      for _ in [0:1000000000] do
        tick
        let st ← catchJS (do pure (Except.ok (← core.iterStep it))) (fun a => pure (Except.error a))
        match st with
        | .error a => out := some (true, a); break
        | .ok none =>
          -- the iterator is done: remainingElementsCount − 1, settle when it is 0
          let fin ← catchJS (do
              if kind != 0 then
                let k ← core.toNum (← core.getV (.obj counter) "n")
                setHidden counter "n" (.num (k - 1))
                if k - 1 == 0 then
                  let mut xs : Array Value := #[]
                  for i in [0:index] do xs := xs.push (← core.getV (.obj vals) (toString i))
                  let arr ← newArray xs
                  if kind == 3 then
                    let e ← alloc { proto := .obj r.aggregateErrorProto, kind := .error }
                    setHidden e "message" (.str "All promises were rejected")
                    setHidden e "errors" arr
                    let _ ← core.callV capRej .undef #[.obj e]
                  else
                    let _ ← core.callV capRes .undef #[arr]
              pure none) (fun a => pure (some a))
          if let some a := fin then out := some (true, a)
          break
        | .ok (some v) =>
          let step ← catchJS (do
              setHidden vals (toString index) .undef
              setHidden counter "len" (.num (Float.ofNat (index + 1)))
              let nextP ← core.callV resolveF thisV #[v]
              let called ← alloc { proto := .null }
              let (onF, onR) ← match kind with
                | 0 => pure (capRes, capRej)
                | 1 => do
                  let f ← elementFn (.x (.promiseSettleElement 0)) capRes index called
                  let g ← elementFn (.x (.promiseSettleElement 1)) capRes index called
                  pure (f, g)
                | 2 => do
                  let f ← elementFn .promiseAllElement capRes index called
                  pure (f, capRej)
                | _ => do
                  let g ← elementFn (.x .promiseAnyReject) capRej index called
                  pure (capRes, g)
              if kind != 0 then
                let k ← core.toNum (← core.getV (.obj counter) "n")
                setHidden counter "n" (.num (k + 1))
              -- Invoke(nextPromise, "then", « onFulfilled, onRejected »)
              let th ← core.getV nextP "then"
              let _ ← core.callV th nextP #[onF, onR]
              pure none) (fun a => pure (some a))
          if let some a := step then out := some (false, a); break
          index := index + 1
      match out with
      | none => pure capP
      | some (true, a) => rejectWith a
      | some (false, a) =>
        match a with
        | .throw _ =>
          -- IteratorClose with a throw completion: the original completion wins (§7.4.11 step 5)
          let _ ← catchJS (do
              match ← core.getV it "return" with
              | .undef | .null => pure ()
              | f => let _ ← core.callV f it #[]; pure ())
            (fun b => match b with | .halt w => throw (.halt w) | _ => pure ())
          rejectWith a
        | a => throw a
    | (.x (.promiseKeyed settled)) =>
      -- Promise.allKeyed / allSettledKeyed (proposal-await-dictionary, PerformPromiseAllKeyed):
      -- the own enumerable keys of `promises`, each value through C.resolve and `then`; the
      -- result is a null-prototype object with the same keys
      let cap ← core.callNative (.x .promiseWithResolvers) thisV #[] none
      let capP ← core.getV cap "promise"
      let capRes ← core.getV cap "resolve"
      let capRej ← core.getV cap "reject"
      let x ← catchJS (do
          let .obj pid := a0 | throwErr .type "Promise.allKeyed: the argument is not an object"
          let f ← core.getV thisV "resolve"
          if !(← isCallable f) then throwErr .type "Promise resolve is not a function"
          let vals ← alloc { proto := .null }
          let counter ← alloc { proto := .null }
          setHidden counter "n" (.num 1)
          setHidden counter "keyed" (.bool true)
          let mut index := 0
          for key in ← core.ownKeysOf pid do
            tick
            match ← core.ownDesc pid key with
            | some d =>
              if !d.enumerable then continue
              let v ← core.getV a0 key
              setHidden vals (toString index) .undef
              setHidden counter ("k" ++ toString index) (.str key)
              setHidden counter "len" (.num (Float.ofNat (index + 1)))
              let nextP ← core.callV f thisV #[v]
              let called ← alloc { proto := .null }
              let el (nid : Native) : M Value := do
                let nf ← nativeFn nid
                let g ← alloc { proto := .obj r.functionProto, kind := .bound nf .undef #[capRes, .obj vals, .obj counter, .num (Float.ofNat index), .obj called] }
                defineOwn g "length" (.data (.num 1) false false true)
                defineOwn g "name" (.data (.str "") false false true)
                pure (.obj g)
              let onF ← el (if settled then .x (.promiseSettleElement 0) else .promiseAllElement)
              let onR ← if settled then el (.x (.promiseSettleElement 1)) else pure capRej
              let k ← core.toNum (← core.getV (.obj counter) "n")
              setHidden counter "n" (.num (k + 1))
              let _ ← core.callV (← core.getV nextP "then") nextP #[onF, onR]
              index := index + 1
            | none => pure ()
          let _ ← core.callNative .promiseAllElement .undef #[capRes, .obj vals, .obj counter, .num (-1), .undef, .undef] none
          pure none) (fun a => pure (some a))
      match x with
      | some (.throw e) => let _ ← core.callV capRej .undef #[e]; pure capP
      | some a => throw a
      | none => pure capP
    | .promiseAllElement | (.x (.promiseSettleElement _)) | (.x .promiseAnyReject) =>
      -- the element functions (§27.2.4.1.3 Promise.all Resolve Element Functions, §27.2.4.2.2
      -- and .3 allSettled, §27.2.4.3.2 Promise.any Reject Element Functions). Bound arguments:
      -- the capability's resolve (reject for any), values, the counter record, the index, the
      -- [[AlreadyCalled]] record; then the argument.
      let x := argD args 5
      let final := match argD args 3 with | .num i => i < 0 | _ => false
      match argD args 4 with
      | .obj c =>
        if ((← getObj c).getOwn "called").isSome then return .undef
        setHidden c "called" (.bool true)
      | _ => pure ()
      let x ← match id_ with
        | (.x (.promiseSettleElement rejected)) =>
          let o ← newObject
          defineOwn o "status" (.data (.str (if rejected == 1 then "rejected" else "fulfilled")) true true true)
          defineOwn o (if rejected == 1 then "reason" else "value") (.data x true true true)
          pure (.obj o)
        | _ => pure x
      let idx := match argD args 3 with | .num i => i.toUInt64.toNat | _ => 0
      if !final then setHidden (match a1 with | .obj v => v | _ => 0) (toString idx) x
      let c := argD args 2
      let k ← core.toNum (← core.getV c "n")
      setHidden (match c with | .obj v => v | _ => 0) "n" (.num (k - 1))
      if k - 1 == 0 then
        let len := (← core.toNum (← core.getV c "len")).toUInt64.toNat
        let mut xs : Array Value := #[]
        for i in [0:len] do xs := xs.push (← core.getV a1 (toString i))
        if (← core.getV c "keyed") matches .bool true then
          -- CreateKeyedPromiseCombinatorResultObject: a null-prototype object, key by key
          let o ← alloc { proto := .null }
          for i in [0:len] do
            if let .str key ← core.getV c ("k" ++ toString i) then
              defineOwn o key (.data (xs.getD i .undef) true true true)
          return ← core.callV a0 .undef #[.obj o]
        let arr ← newArray xs
        if id_ == (.x .promiseAnyReject) then
          let e ← alloc { proto := .obj r.aggregateErrorProto, kind := .error }
          setHidden e "message" (.str "All promises were rejected")
          setHidden e "errors" arr
          return ← core.callV a0 .undef #[.obj e]
        return ← core.callV a0 .undef #[arr]
      pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: Map, Set and their weak kinds. `r` is the realm `callNative` read. -/
def callNativeMap (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    let id_ := id
    match id with
    | .mapCtor k =>
      let nt ← match newTarget with
        | some nt => pure nt
        | none => throwErr .type "Constructor requires 'new'"
      let pp ← core.getV nt "prototype"
      -- GetPrototypeFromConstructor (§10.1.14): %Map.prototype% and the others of the new target's realm
      let pp ← if pp.isObj then pure pp else
        core.getV (← core.getV (.obj (← funRealm nt).globalObj) (#["Map", "Set", "WeakMap", "WeakSet"].getD k "Map")) "prototype"
      let o ← alloc { proto := pp, kind := .coll k #[] {} }
      match a0 with
      | .undef | .null => pure ()
      | it =>
        let adder ← core.getV (.obj o) (if k == 0 || k == 2 then "set" else "add")
        if !(← isCallable adder) then throwErr .type "adder is not a function"
        -- AddEntriesFromIterable (§24.1.1.2) and the Set constructor's loop (§24.2.2.1): a value
        -- at a time; an error of the adder or of an entry closes the iterator.
        Natives.iterEach core (← core.getIterator it) fun item => do
          if k == 0 || k == 2 then
            if !item.isObj then throwErr .type "Iterator value is not an entry object"
            let key ← core.getV item "0"
            let v ← core.getV item "1"
            let _ ← core.callV adder (.obj o) #[key, v]
          else let _ ← core.callV adder (.obj o) #[item]
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
        if weak && !(← canBeHeldWeakly key) then throwErr .type "Invalid value used as weak collection key"
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
            let _ ← core.callV a0 a1 #[v, k, thisV]
            i := j + 1
        pure .undef
      | .mapIter mode =>
        pure (.obj (← alloc { proto := .obj r.arrayIterProto, kind := .iter thisV 0 mode }))
      | _ => pure .undef
    | _ => throwErr .type "not a function"

/-- Built-ins of `callNative`: Reflect. `r` is the realm `callNative` read. -/
def callNativeReflect (core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    let a0 := argD args 0
    let a1 := argD args 1
    match id with
    | .reflect op =>
      let needObj : M Unit := if !a0.isObj then throwErr .type "Reflect method called on a non-object" else pure ()
      match op with
      | 0 => needObj; newArray ((← core.ownKeysOf (← core.toObj a0)).filter (!isPrivKey ·) |>.map keyValue)
      | 1 => needObj; core.callNative .objectGetPrototypeOf .undef args none
      | 2 => needObj
             match a0, a1 with
             | .obj id0, .obj _ | .obj id0, .null =>
               -- [[SetPrototypeOf]] (§10.1.2, §10.5.2): a Proxy asks its trap
               let mut cur := id0
               for _ in [0:64] do
                 match (← getObj cur).kind with
                 | .proxy t hnd =>
                   let .obj tid := t | throwErr .type "Cannot perform 'setPrototypeOf' on a proxy that has been revoked"
                   match ← core.proxyTrap hnd "setPrototypeOf" with
                   | some f =>
                     if !toBool (← core.callV f hnd #[t, a1]) then return .bool false
                     if !toBool (← core.callNative .objectIsExtensible .undef #[t] none) then
                       if !sameValue a1 (← core.callNative .objectGetPrototypeOf .undef #[t] none) then
                         throwErr .type "'setPrototypeOf' on proxy: the target is not extensible and has another prototype"
                     return .bool true
                   | none => cur := tid
                 | _ => return .bool (← setProtoOf cur a1)
               pure (.bool false)
             | _, _ => throwErr .type "Object prototype may only be an Object or null"
      | 3 => needObj; let k ← core.toKey a1; pure (.bool (← core.hasProp (← core.toObj a0) k))
      | 4 => needObj; if args.size > 2 then core.getRecv (← core.toObj a0) (← core.toKey a1) (argD args 2) else core.getV a0 (← core.toKey a1)
      | 5 =>
        needObj
        let recv := if args.size > 3 then argD args 3 else a0
        if !sameValue recv a0 then
          -- Reflect.set with a receiver that is not the target (§10.1.9.2
          -- OrdinarySetWithOwnDescriptor): a setter found on the target's chain is called with
          -- the receiver as `this`; a data property is made or changed on the receiver.
          let key ← core.toKey a1
          let val := argD args 2
          let tid ← core.toObj a0
          match (← getObj tid).kind with
          | .proxy t hnd =>
            match ← core.proxyTrap hnd "set" with
            | some f => return .bool (toBool (← core.callV f hnd #[t, keyValue key, val, recv]))
            | none => return ← core.callNative (.reflect 5) .undef #[t, a1, val, recv] none
          | _ => pure ()
          match (← get).findProp tid key 1000 with
          | some (.acc _ st _ _) =>
            if st.isObj then
              let _ ← core.callV st recv #[val]
              return .bool true
            else return .bool false
          | some (.data _ false _ _) => return .bool false
          | _ =>
            match recv with
            | .obj rid =>
              let existing ← core.ownDesc rid key
              match existing with
              | some (.acc ..) | some (.data _ false _ _) => return .bool false
              | _ => pure ()
              -- the receiver's [[DefineOwnProperty]]: a Proxy passes it to its `defineProperty`
              -- trap, or to its target when it has none
              let mut cur := rid
              for _ in [0:64] do
                match (← getObj cur).kind with
                | .proxy t hnd =>
                  match ← core.proxyTrap hnd "defineProperty" with
                  | some f =>
                    let d ← newObject
                    defineOwn d "value" (.data val true true true)
                    if existing.isNone then
                      defineOwn d "writable" (.data (.bool true) true true true)
                      defineOwn d "enumerable" (.data (.bool true) true true true)
                      defineOwn d "configurable" (.data (.bool true) true true true)
                    return .bool (toBool (← core.callV f hnd #[t, keyValue key, .obj d]))
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
        let ok ← catchJS (do core.putV a0 (← core.toKey a1) (argD args 2) true; pure true) (fun e => match e with
          | .throw _ => pure false
          | a => throw a)
        pure (.bool ok)
      | 6 =>
        -- §28.1.3: the key, the descriptor (its TypeErrors), then [[DefineOwnProperty]]
        let .obj tid := a0 | throwErr .type "Reflect.defineProperty called on a non-object"
        let k ← core.toKey a1
        let desc ← core.toPropDesc (argD args 2)
        pure (.bool (← core.defineOwnProp tid k desc))
      | 7 =>
        needObj
        let id ← core.toObj a0
        let k ← core.toKey a1
        match (← getObj id).getOwn k with
        | none => pure (.bool true)
        | some p => if p.configurable then deleteOwn id k; pure (.bool true) else pure (.bool false)
      | 8 =>
        if !(← isCallable a0) then throwErr .type "Reflect.apply target is not callable"
        let argv ← core.elemsOf (argD args 2)
        core.callV a0 a1 argv
      | 9 =>
        if !(← isConstructor a0) then throwErr .type "Reflect.construct target is not a constructor"
        if args.size > 2 && !(← isConstructor (argD args 2)) then throwErr .type "Reflect.construct newTarget is not a constructor"
        let argv ← core.elemsOf a1
        core.construct a0 argv (if args.size > 2 then argD args 2 else a0)
      | 10 => needObj; core.callNative .objectGetOwnPropertyDescriptor .undef args none
      | 11 => needObj; core.callNative .objectIsExtensible .undef args none
      | _ =>
        -- [[PreventExtensions]] (§10.1.4, §10.5.4)
        needObj
        let .obj id0 := a0 | pure (.bool false)
        let mut cur := id0
        for _ in [0:64] do
          match (← getObj cur).kind with
          | .proxy t hnd =>
            let .obj tid := t | throwErr .type "Cannot perform 'preventExtensions' on a proxy that has been revoked"
            match ← core.proxyTrap hnd "preventExtensions" with
            | some f =>
              let b := toBool (← core.callV f hnd #[t])
              if b && toBool (← core.callNative .objectIsExtensible .undef #[t] none) then
                throwErr .type "'preventExtensions' on proxy: the trap returned true but the target is extensible"
              return .bool b
            | none => cur := tid
          | _ =>
            modifyObj cur fun o => { o with extensible := false }
            return .bool true
        pure (.bool false)
    | _ => throwErr .type "not a function"

/-- Built-in functions. `newTarget` is set for `new`. -/
def callNative (core : CoreFn H) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value := do
    -- A built-in's loops are over its receiver and arguments: one step per call is not
    -- enough when it walks them, so the call takes steps for their size (`sizeCost`). The
    -- String methods that index an ASCII receiver in constant time (`charAt`, `charCodeAt`,
    -- `at`, `codePointAt`) or copy only their result (`slice`, `substring`, `substr`, which
    -- take steps for the result) do not walk it, and take no steps for it.
    -- From one read of the heap, with pure functions: each call of a monadic helper that is
    -- not inlined made a result cell (four or more a built-in call, 2026-11-27).
    let h0 ← get
    let recvCost := if indexesReceiver id thisV then 0 else
      match cachedReceiverCostOf h0 id thisV with
      | some c => c
      | none => sizeCostOf h0 thisV
    let argsCost := if subjectCachedOf h0 id args then 0
      else args.foldl (fun acc a => acc + sizeCostOf h0 a) 0
    let cost := recvCost + args.size / 64 + argsCost
    if cost != 0 then charge cost
    let r ← realm
    match id with
    | .print => callNativeGlobal core r id thisV args newTarget
    | .isNaN => callNativeGlobal core r id thisV args newTarget
    | .isFinite => callNativeGlobal core r id thisV args newTarget
    | .parseInt => callNativeGlobal core r id thisV args newTarget
    | .parseFloat => callNativeGlobal core r id thisV args newTarget
    | .objectCtor => callNativeObjectStatic core r id thisV args newTarget
    | .objectKeys => callNativeObjectStatic core r id thisV args newTarget
    | .objectGetOwnPropertyNames => callNativeObjectStatic core r id thisV args newTarget
    | .objectGetPrototypeOf => callNativeObjectStatic core r id thisV args newTarget
    | .objectSetPrototypeOf => callNativeObjectStatic core r id thisV args newTarget
    | .objectCreate => callNativeObjectStatic core r id thisV args newTarget
    | .objectDefineProperty => callNativeObjectStatic core r id thisV args newTarget
    | .objectGetOwnPropertyDescriptor => callNativeObjectStatic core r id thisV args newTarget
    | .objectIs => callNativeObjectStatic core r id thisV args newTarget
    | .objectFreeze => callNativeObjectStatic core r id thisV args newTarget
    | .objectIsFrozen => callNativeObjectStatic core r id thisV args newTarget
    | .objectPreventExtensions => callNativeObjectStatic core r id thisV args newTarget
    | .objectIsExtensible => callNativeObjectStatic core r id thisV args newTarget
    | .objectProtoHasOwnProperty => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoPropertyIsEnumerable => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoDefineGetter | .objectProtoDefineSetter => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoLookupGetter | .objectProtoLookupSetter => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoIsPrototypeOf => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoToString => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoToLocaleString => callNativeObjectProto core r id thisV args newTarget
    | .objectProtoValueOf => callNativeObjectProto core r id thisV args newTarget
    | .functionCtor => callNativeObjectProto core r id thisV args newTarget
    | .functionProto => callNativeObjectProto core r id thisV args newTarget
    | .functionProtoCall => callNativeObjectProto core r id thisV args newTarget
    | .functionProtoApply => callNativeObjectProto core r id thisV args newTarget
    | .functionProtoBind => callNativeObjectProto core r id thisV args newTarget
    | .functionProtoToString => callNativeObjectProto core r id thisV args newTarget
    | .arrayCtor => callNativeArrayEdit core r id thisV args newTarget
    | .arrayIsArray => callNativeArrayEdit core r id thisV args newTarget
    | .arrayPush => callNativeArrayEdit core r id thisV args newTarget
    | .arrayPop => callNativeArrayEdit core r id thisV args newTarget
    | .arrayShift => callNativeArrayEdit core r id thisV args newTarget
    | .arrayUnshift => callNativeArrayEdit core r id thisV args newTarget
    | .arraySlice => callNativeArrayEdit core r id thisV args newTarget
    | .arraySplice => callNativeArrayEdit core r id thisV args newTarget
    | .arrayJoin | .arrayToString => callNativeArrayRead core r id thisV args newTarget
    | .arrayIndexOf | .arrayIncludes => callNativeArrayRead core r id thisV args newTarget
    | .arrayLastIndexOf => callNativeArrayRead core r id thisV args newTarget
    | .arrayConcat => callNativeArrayRead core r id thisV args newTarget
    | .arrayReverse => callNativeArrayEdit core r id thisV args newTarget
    | .arrayFill => callNativeArrayEdit core r id thisV args newTarget
    | .arrayMap | .arrayForEach | .arrayFilter | .arraySome | .arrayEvery | .arrayFind
    | .arrayFindIndex => callNativeArrayRead core r id thisV args newTarget
    | .arrayReduce => callNativeArrayRead core r id thisV args newTarget
    | .arraySort => callNativeArrayEdit core r id thisV args newTarget
    | .stringCtor => callNativeString core r id thisV args newTarget
    | .stringFromCharCode => callNativeString core r id thisV args newTarget
    | .stringToString => callNativeString core r id thisV args newTarget
    | .numberCtor => callNativeNumber core r id thisV args newTarget
    | .numberValueOf | .numberToString | .numberToFixed => callNativeNumber core r id thisV args newTarget
    | .numberIsInteger => callNativeNumber core r id thisV args newTarget
    | .booleanCtor => callNativeNumber core r id thisV args newTarget
    | .booleanToString | .booleanValueOf => callNativeNumber core r id thisV args newTarget
    | .errorCtor _ => callNativeError core r id thisV args newTarget
    | .errorToString => callNativeError core r id thisV args newTarget
    | .throwTypeError => callNativeGlobal core r id thisV args newTarget
    | .jsonStringify => callNativeError core r id thisV args newTarget
    | .eval => callNativeGlobal core r id thisV args newTarget
    | .symbolCtor => callNativeError core r id thisV args newTarget
    | .symbolToString | .symbolDescription | .symbolValueOf => callNativeError core r id thisV args newTarget
    | .objectGetOwnPropertySymbols => callNativeObjectStatic core r id thisV args newTarget
    | .objectAssign => callNativeObjectStatic core r id thisV args newTarget
    | .objectEntries | .objectValues => callNativeObjectStatic core r id thisV args newTarget
    | .arrayValues | .arrayKeys | .arrayEntries => callNativeArrayRead core r id thisV args newTarget
    | .stringIterator => callNativeString core r id thisV args newTarget
    | .iterNext => callNativeGenerator core r id thisV args newTarget
    | .iterSelf => callNativeGenerator core r id thisV args newTarget
    | .arrayFrom => callNativeArrayFrom core r id thisV args newTarget
    | .arrayOf => callNativeArrayFrom core r id thisV args newTarget
    | .dateNow => callNativeGlobal core r id thisV args newTarget
    | .promiseCtor => callNativePromise core r id thisV args newTarget
    | (.x .promiseInitOn) => callNativePromise core r id thisV args newTarget
    | .promiseResolveFn | .promiseRejectFn => callNativePromise core r id thisV args newTarget
    | .promiseThen => callNativePromise core r id thisV args newTarget
    | .promiseCatch => callNativePromise core r id thisV args newTarget
    | .promiseFinally => callNativePromise core r id thisV args newTarget
    | .promiseFinallyF | .promiseFinallyR => callNativePromise core r id thisV args newTarget
    | .promiseValueThunk => callNativePromise core r id thisV args newTarget
    | .promiseThrower => callNativePromise core r id thisV args newTarget
    | .promiseResolveStatic => callNativePromise core r id thisV args newTarget
    | .promiseRejectStatic => callNativePromise core r id thisV args newTarget
    | .promiseReactionJob => callNativePromise core r id thisV args newTarget
    | .promiseThenableJob => callNativePromise core r id thisV args newTarget
    | .promiseAll | (.x (.promiseCombinator _)) | (.x .promiseAny) => callNativePromiseAll core r id thisV args newTarget
    | (.x (.promiseKeyed _)) => callNativePromiseAll core r id thisV args newTarget
    | .promiseAllElement | (.x (.promiseSettleElement _)) | (.x .promiseAnyReject) => callNativePromiseAll core r id thisV args newTarget
    | .agenNext | .agenReturn | .agenThrow => callNativeGenerator core r id thisV args newTarget
    | .agenResume => callNativeGenerator core r id thisV args newTarget
    | .mapCtor _ => callNativeMap core r id thisV args newTarget
    | .mapGet | .mapSet | .mapHas | .mapDelete | .mapClear | .mapSize | .mapForEach | .setAdd
    | .mapIter _ => callNativeMap core r id thisV args newTarget
    | .reflect _ => callNativeReflect core r id thisV args newTarget
    | .objectDefineProperties => callNativeObjectStatic core r id thisV args newTarget
    | .objectSeal => callNativeObjectStatic core r id thisV args newTarget
    | .objectIsSealed => callNativeObjectStatic core r id thisV args newTarget
    | .objectGetOwnPropertyDescriptors => callNativeObjectStatic core r id thisV args newTarget
    | .objectFromEntries => callNativeObjectStatic core r id thisV args newTarget
    | .arrayFlat | .arrayFlatMap => callNativeArrayRead core r id thisV args newTarget
    | .stringAt => callNativeString core r id thisV args newTarget
    | .arrayAt => callNativeArrayRead core r id thisV args newTarget
    | .arrayFindLast | .arrayFindLastIndex => callNativeArrayRead core r id thisV args newTarget
    | .stringPadStart | .stringPadEnd => callNativeString core r id thisV args newTarget
    | .stringCodePointAt => callNativeString core r id thisV args newTarget
    | .stringTrimStart | .stringTrimEnd => callNativeString core r id thisV args newTarget
    | .stringReplace | .stringReplaceAll => callNativeString core r id thisV args newTarget
    | .stringFromCodePoint => callNativeString core r id thisV args newTarget
    | .numberIsFinite => callNativeNumber core r id thisV args newTarget
    | .numberIsNaN => callNativeNumber core r id thisV args newTarget
    | .numberIsSafeInteger => callNativeNumber core r id thisV args newTarget
    | .math1 _ => callNativeNumber core r id thisV args newTarget
    | .mathHypot => callNativeNumber core r id thisV args newTarget
    | .mathImul => callNativeNumber core r id thisV args newTarget
    | .mathClz32 => callNativeNumber core r id thisV args newTarget
    | .asyncResume => callNativeGenerator core r id thisV args newTarget
    | .bigintCtor => callNativeNumber core r id thisV args newTarget
    | .bigintAsN _ => callNativeNumber core r id thisV args newTarget
    | .bigintToString | .bigintValueOf => callNativeNumber core r id thisV args newTarget
    | .genNext | .genReturn | .genThrow => callNativeGenerator core r id thisV args newTarget
    | .stringSplit => callNativeString core r id thisV args newTarget
    | .stringMatch | .stringSearch => callNativeString core r id thisV args newTarget
    | .stringMatchAll => callNativeString core r id thisV args newTarget
    | .regexpCtor | .regexpExec | .regexpTest | .regexpToString | .regexpGetter _
    | .proxyCtor | .jsonParse | .bufferCtor | .bufferSlice
    | .bufferIsView | .typedCtor _ | .typedSet | .typedSubarray | .typedFill | .dateCtor
    | .dataViewCtor | .dataViewGet _ | .dataViewSet _
    | .dateGetTime | .perfNow | .host _ | .uriFn _ =>
      Natives.extraNative core id thisV args newTarget
    | .x _ =>
      Natives.moreNative core id thisV args newTarget
    | _ =>
      -- string methods and Math
      core.stringOrMath id thisV args

end Natives

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

/-! ## Tier 1: guarded fast paths

The evaluator's arms for `x++` on a resolved name, `x = v` on a resolved name, `a op b` for
`+ - * /` and a block that declares nothing lexical first try a fast path (`Tier1.withFast`)
when the run's `Mode` has tier 1 on. A fast path reads the heap, and either answers at once or
answers `none` and the arm's own code runs. With tier 1 off (`Mode.ref`) only the arm's own code
runs: that is the reference. `JS/Tier1Proofs.lean` proves each fast path against its arm's code;
`JS/FuelMonoAll.lean` (`tier_refines`) composes them over the whole block: a run with tier 1 on
ends as the reference run does, in the same heap, whenever the reference does not run out of
fuel. -/
namespace Tier1

/-- Try `fast`; on `some b` continue with `c b`, on `none` run `g`. -/
@[inline] def attempt {α β : Type} (fast : M (Option β)) (c : β → M α) (g : M α) : M α := do
  match ← fast with
  | some b => c b
  | none => g

/-- A site of tier 1: with the tier on, `attempt fast c g`; off, `g`, the arm's own code. -/
@[inline] def withFast {α β : Type} (on : Bool) (fast : M (Option β)) (c : β → M α) (g : M α) : M α :=
  bif on then attempt fast c g else g

/-- The statement declares a name in its block's lexical environment (`let`, `const`, a
function or a class): `enterBlock` makes an environment for a block that has one. -/
def isLexical (s : Stmt) : Bool :=
  match s with
  | .decl .letK _ | .decl .constK _ | .funDecl .. | .classDecl .. => true
  | _ => false

/-- The environment and the number in slot `idx`, `hops` up, when that slot has the name `x`,
holds a number and may be written. -/
@[inline] def slotNum? (h : HeapOf H) (ctx : Ctx) (x : String) (hops idx : Nat) : Option (Nat × Float) :=
  let e := h.envUp hops ctx.env
  let env := h.envs.getD e default
  match env.names[idx]?, env.vals[idx]? with
  | some y, some (.num old) => if y == x && env.mutableAt idx then some (e, old) else none
  | _, _ => none

/-- The environment of slot `idx`, `hops` up, when that slot has the name `x`, is initialised
and may be written. -/
@[inline] def slotSet? (h : HeapOf H) (ctx : Ctx) (x : String) (hops idx : Nat) : Option Nat :=
  let e := h.envUp hops ctx.env
  let env := h.envs.getD e default
  match env.names[idx]?, env.vals[idx]? with
  | some _, some .hole => none
  | some y, some _ => if y == x && env.mutableAt idx then some e else none
  | _, _ => none

/-- `x++`, `x--`, `++x`, `--x` on a resolved name whose slot holds a number and may be written:
the slot is written in place, with no call of `lookupLocal` and `assignLocal`. -/
@[inline] def incLocal? (pre inc : Bool) (x : String) (hops idx : Nat) (ctx : Ctx) : M (Option Value) := do
  match slotNum? (← get) ctx x hops idx with
  | some (e, old) =>
    let nv := if inc then old + 1 else old - 1
    setSlot e idx (.num nv)
    pure (some (.num (if pre then nv else old)))
  | none => pure none

/-- The write of `v` to a resolved name whose slot is initialised and may be written, in
place, with no call of `putTarget` and `assignLocal`. -/
@[inline] def setLocal? (target : Expr) (v : Value) (ctx : Ctx) : M (Option Unit) := do
  match target with
  | .local x hops idx =>
    match slotSet? (← get) ctx x hops idx with
    | some e => setSlot e idx v; pure (some ())
    | none => pure none
  | _ => pure none

/-- The operations of the arithmetic fast path. -/
def isArith : BinOp → Bool
  | .add | .sub | .mul | .div => true
  | _ => false

/-- An operation of `isArith` on two numbers. -/
@[inline] def arithOp (op : BinOp) (p q : Float) : Float :=
  match op with
  | .add => p + q
  | .sub => p - q
  | .mul => p * q
  | _ => p / q

/-- The number an operand has, when it is a leaf that holds a number or a nested `+ - * /` of
such operands, down to depth `k`: computed with no step of the monad and no change to the heap. -/
def pureNum (h : HeapOf H) (ctx : Ctx) : Nat → Expr → Option Float
  | n, c =>
    match leafV h ctx c with
    | .num p => some p
    | .hole =>
      match n, c with
      | k + 1, .binary op a b =>
        if isArith op then
          match pureNum h ctx k a, pureNum h ctx k b with
          | some p, some q => some (arithOp op p q)
          | _, _ => none
        else none
      | _, _ => none
    | _ => none

/-- The nesting the arithmetic fast path follows. -/
def depth : Nat := 8

/-- `a op b` for `+ - * /` when both operands are numbers known by `pureNum`. -/
@[inline] def arith? (ctx : Ctx) (op : BinOp) (a b : Expr) : M (Option Value) := do
  if isArith op then
    let h ← get
    match pureNum h ctx depth a, pureNum h ctx depth b with
    | some p, some q => pure (some (.num (arithOp op p q)))
    | _, _ => pure none
  else pure none

/-- The evaluator's own code for `a op b` (the arm of `Expr.binary`), over the evaluator's
`evalExpr` and `binop` at the arm's fuel: operands that are leaves are read from the heap, and
number operands of the common operations are combined with no call. -/
@[inline] def binaryGen (ev : Expr → M Value) (bo : BinOp → Value → Value → M Value) (ctx : Ctx)
    (op : BinOp) (a b : Expr) : M Value := do
  let x ← (match leafV (← get) ctx a with | .hole => ev a | v => pure v)
  let y ← (match leafV (← get) ctx b with | .hole => ev b | v => pure v)
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
  | _, _, _ => bo op x y

/-- The evaluator's own code for `x++`, `x--`, `++x`, `--x` on a resolved name (the arm of
`Expr.update` on `Expr.local`), over the evaluator's `lookupLocal`, `assignLocal`, `toPrim` and
`toNum` at the arm's fuel. -/
@[inline] def updateGen (look : M Value) (asg : Value → M Unit) (prim : Value → M Value)
    (num : Value → M Float) (pre inc : Bool) : M Value := do
  match ← look with
  | .num old =>
    let nv := if inc then old + 1 else old - 1
    asg (.num nv)
    pure (.num (if pre then nv else old))
  | p =>
    match ← prim p with
    | .big big =>
      let nv := if inc then big + 1 else big - 1
      asg (.big nv)
      pure (.big (if pre then nv else big))
    | p =>
      let old ← num p
      let nv := if inc then old + 1 else old - 1
      asg (.num nv)
      pure (.num (if pre then nv else old))

/-- A block that declares nothing lexical: `evalBlock` would make no environment. -/
@[inline] def plainBlock? (ss : List Stmt) : M (Option Unit) :=
  pure (if ss.any isLexical then none else some ())

end Tier1

-- Helpers of the block that call none of its functions: defined before it, so that they do not
-- take the run's `Mode` (a section variable of the block would be added to each).
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

/-- What a loop does with the completion of its body (LoopContinues, §14.7.1.2). -/
def loopNext (labels : List String) : Compl → Option Compl
  | .normal => none
  | .cont none => none
  | .cont (some l) => if labels.contains l then none else some (.cont (some l))
  | .brk none => some .normal
  | .brk (some l) => if labels.contains l then some .normal else some (.brk (some l))
  | .ret v => some (.ret v)

/-- A global name read through the cache: the value, or `Value.hole` when the general path
must look (not a plain writable data property, or a lexical binding may shadow it). -/
def vmGlobalHit (h : HeapOf H) (env : Nat) (x : String) (site : Nat) : Value :=
  if !h.chainHit env x site then .hole else
    let g := h.obj h.realm.globalObj
    let slot := h.globalCache[site]!
    -- after `delete` the name may still be in a big map's keys as a tombstone (`PropMap.liveAt`)
    match g.props.ks[slot]?, g.props.vs[slot]? with
    | some k, some (.data v ..) => if k == x && g.props.liveAt slot x then v else .hole
    | _, _ => .hole

/-- Assign a global name through the cache: only when no lexical binding shadows it and the
cached slot holds this name as a plain writable data property; `false` otherwise. -/
def vmGlobalSet (env : Nat) (x : String) (site : Nat) (v : Value) : M Bool := do
  let h ← get
  if !h.chainHit env x site then return false
  let gid := h.realm.globalObj
  let slot := h.globalCache[site]!
  let g := h.obj gid
  match g.props.ks[slot]?, g.props.vs[slot]? with
  | some k, some (.data _ true e c) =>
    if k == x && g.props.liveAt slot x then
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

-- The evaluator's functions take the run's `Mode` (which tiers are on).
section Block
variable [md : Mode]

set_option hygiene false in
/-- `toNumQ n v`: ToNumber of `v` with fuel `n`, written so that a value that is a Number already
costs no call: `toNum` is a function of the block, so its answer is a result cell holding a boxed
number, and the operands of the numeric and bit operators are Numbers nearly always. The value of
the expression is `toNum n v` at every fuel but 0, where `toNum 0 v` is out of fuel and this
answers the Number (`toNumQ_succ`, `toNum_zero` in `JS/Theorems.lean`). Not hygienic: `toNum` is
defined after this point, in the block. -/
local macro "toNumQ " n:term:max v:term:max : term =>
  `((match $v:term with | Value.num toNumQ_x => pure toNumQ_x | toNumQ_w => toNum $n toNumQ_w : M Float))

mutual

/-- `[[Get]]` on any value (§7.3.2 GetV). -/
def getV : Nat → Value → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, key => do
    match v with
    | .obj id =>
      let c0 := key.front
      -- PrivateGet (§7.3.32): a private name is the object's own element, never a prototype's,
      -- and no Proxy trap sees it
      if c0 == privMark then
        match (← getObj id).getOwn key with
        | some (.data x ..) => return x
        | some (.acc g _ _ _) =>
          if g.isObj then return ← callV n g v #[]
          throwErr .type s!"'{privDisplay key}' was defined without a getter"
        | none => throwErr .type s!"Cannot read private member {privDisplay key} from an object whose class did not declare it"
      -- a typed array's integer index is its element, never a prototype's property
      -- (§10.4.5.4 TypedArrayGetElement)
      if c0.isDigit then
        if let .typed ty b off len := (← getObj id).kind then
          if let some i := arrayIndex? key then
            let live ← liveLen ty b off len
            let bo ← getObj b
            return (if i < live then typedRead ty (bufferBytes bo) (off + i * elemSize ty) else .undef)
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
          if isPrivKey key then throwErr .type s!"Cannot read private member {privDisplay key} from an object whose class did not declare it"
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
      -- PrivateSet (§7.3.33): the object's own element; a method is not writable, an accessor
      -- needs a setter
      if isPrivKey key then
        match o.getOwn key with
        | some (.data _ w e c) =>
          if w then defineOwn id key (.data val true e c)
          else throwErr .type s!"Private method {privDisplay key} is not writable"
        | some (.acc _ st _ _) =>
          if st.isObj then let _ ← callV n st target #[val]
          else throwErr .type s!"'{privDisplay key}' was defined without a setter"
        | none => throwErr .type s!"Cannot write private member {privDisplay key} to an object whose class did not declare it"
        return
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
      if key == "length" then
        if let some (_, writable) := o.generalArrayLen then
          let ok ← if writable then setGeneralArrayLength (toNum n) id { value := some val }
            else pure false
          if !ok && strict then throwErr .type "Cannot set array length"
          return
      match o.kind, key with
      | .array es, "length" =>
        let len ← toNum n val
        if len < 0 || !isIntegral len || len ≥ twoPow32F then throwErr .range "Invalid array length"
        let l := len.toUInt64.toNat
        if l > es.size then
          if l > maxDenseArray then throwErr .range "Invalid array length"
          charge ((l - es.size) / 64)
        let es' := if l ≤ es.size then es.extract 0 l else es ++ Array.replicate (l - es.size) .hole
        modifyObj id fun o => { o with kind := .array es' }
        return
      | _, _ => pure ()
      if isPrivKey key && ((← get).findProp id key 1000).isNone then
        throwErr .type s!"Cannot write private member {privDisplay key} to an object whose class did not declare it"
      match o.getOwn key with
      | some (.data _ w e c) =>
        -- (a String object's indices and length are reported read-only by `getOwn`; its other
        -- own properties, String.prototype's methods among them, are ordinary)
        if w then defineOwn id key (.data val true e c)
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
    -- a Number is stored as it is: no ToNumber call and no new box (`typedConv_num`)
    if typedIsBig ty then pure (.big (← toBigInt n v)) else
      match v with
      | .num _ => pure v
      | w => pure (.num (← toNum n w))
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
      | .obj fid =>
        -- Function.prototype[@@hasInstance] is OrdinaryHasInstance, done here without a call
        match (← getObj fid).kind with
        | .native (.x .fnHasInstance) => if !co.kind.callable then return false
        | _ => return toBool (← callV n hi c #[v])
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
    | .sub => pure (.num ((← toNumQ n a) - (← toNumQ n b)))
    | .mul => pure (.num ((← toNumQ n a) * (← toNumQ n b)))
    | .div => pure (.num ((← toNumQ n a) / (← toNumQ n b)))
    | .mod => pure (.num (jsMod (← toNumQ n a) (← toNumQ n b)))
    | .exp => pure (.num (jsPow (← toNumQ n a) (← toNumQ n b)))
    | .shl =>
      let x := toInt32 (← toNumQ n a); let s := toUint32 (← toNumQ n b) % 32
      pure (intV (toInt32 (Float.ofInt (x * 2 ^ s))))
    | .sar =>
      let x := toInt32 (← toNumQ n a); let s := toUint32 (← toNumQ n b) % 32
      pure (intV (x / 2 ^ s))
    | .shr =>
      let x := toUint32 (← toNumQ n a); let s := toUint32 (← toNumQ n b) % 32
      pure (.num (floatOfNat (x / 2 ^ s)))
    | .band | .bor | .bxor =>
      let x := toUint32 (← toNumQ n a)
      let y := toUint32 (← toNumQ n b)
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
        | .ctor _ =>
          -- the TypeError of the callee's realm (§10.2.1 step 2, after PrepareForOrdinaryCall)
          let h ← get
          let k := fnRealmIdx h id
          if h.realms.isEmpty || k == h.curRealm then throwErr .type "Class constructor cannot be invoked without 'new'"
          else inRealm k (throwErr .type "Class constructor cannot be invoked without 'new'")
        | _ => callClosure n fd env capThis capNT home f thisV .undef args
      | .native nid =>
        let h ← get
        let k := fnRealmIdx h id
        if h.realms.isEmpty || k == h.curRealm then callNative n nid thisV args none
        else inRealm k (callNative n nid thisV args none)
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
    -- PrepareForOrdinaryCall (§10.2.1.1): the callee's realm runs (only with more than one)
    if !h.realms.isEmpty then
      if let .obj fid := fnObj then
        let k := fnRealmIdx h fid
        if k != h.curRealm then
          return ← inRealm k (callClosure n fd env capThis capNT home fnObj thisV newTarget args)
    if h.depth ≥ h.maxDepth then throwErr .range "Maximum call stack size exceeded"
    let saved := h.depth
    set { h with depth := h.depth + 1 }
    -- The depth comes back on every exit, a throw included (a throw that a caller catches
    -- must not use up the call depth).
    -- the environment: the arguments are its first slots when the parameters are plain
    if h.useVm then
      if let some c := fd.info.code.get then
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
    -- the count of arguments, for `Expr.argCount` (taken before the plain path moves `args`)
    let argc := args.size
    -- `args` is moved into the environment on the plain path (the array must have one owner:
    -- `fillSlots` then grows it in place)
    let (fenv, args) ← if info.plain then do
        let e ← pushEnv { names := info.layout, vals := fillSlots args info.nParams info.layout.size, parent := env,
                          index := info.index }
        pure (e, (#[] : Array Value))
      else do
        let e ← newEnv env
        pure (e, args)
    tryCatch (callBody n fd env capThis capNT home fnObj thisV newTarget args fenv info argc) fun e => do
      modify fun h => { h with depth := saved }
      if info.frameLocal then releaseEnv fenv
      throw e
termination_by structural n _ _ _ _ _ _ _ _ _ => n

/-- The rest of a call, after the environment is made (`callClosure`). -/
def callBody : Nat → FunDef → Nat → Value → Value → Value → Value → Value → Value → Array Value → Nat → FunInfo → Nat → M Value
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, fd, env, capThis, capNT, home, fnObj, thisV, newTarget, args, fenv, info, argc => do
    let r ← realm
    let thisV ← if fd.arrow then pure capThis
      else if fd.strict then pure thisV
      else match thisV with
        | .undef | .null => pure (.obj r.globalObj)
        | .obj _ => pure thisV
        | v => do pure (.obj (← toObj n v))
    let nt := if fd.arrow then capNT else newTarget
    let fo := if fd.arrow then Value.undef else fnObj
    let ctx : Ctx := { env := fenv, thisV := thisV, strict := fd.strict, newTarget := nt, home := home, fnObj := fo, argc }
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
      -- parameters with expressions (defaults, patterns): every parameter name is in its
      -- temporal dead zone until its own parameter is bound (§10.2.11 steps 21 to 26), so a
      -- default that names itself or a later parameter is a ReferenceError
      let paramExprs := fd.params.any (fun pe => match pe with | .mk (.id _) none => false | _ => true)
      if paramExprs then
        for pe in fd.params do
          match pe with
          | .mk p _ => for x in p.names do declare fenv x { v := .undef, init := false }
        if let some rp := fd.rest then
          for x in rp.names do declare fenv x { v := .undef, init := false }
      let bindAll : M Unit := do
        bindParams n ctx fd.params args 0
        if let some rp := fd.rest then
          bindPat n ctx rp (← newArray (args.extract fd.params.length args.size)) (.declare fenv true)
      let bindChecked : M Unit :=
        if paramExprs && !fd.arrow then do
          -- while the parameters' expressions run, direct eval there sees `paramEnv`
          let outer := (← get).paramEnv
          modify fun h => { h with paramEnv := fenv }
          tryCatch bindAll fun e => do
            modify fun h => { h with paramEnv := outer }
            throw e
          modify fun h => { h with paramEnv := outer }
        else bindAll
      if fd.async && !fd.gen then
        -- EvaluateAsyncFunctionBody (§15.8.4): an error while the parameters are bound rejects
        -- the function's promise instead of throwing at the call
        let r ← catchJS (do bindChecked; pure none) fun e => match e with
          | .throw v => pure (some v)
          | a => throw a
        if let some v := r then
          let pid ← newPromise
          rejectPromise n pid v
          modify fun h => { h with depth := h.depth - 1 }
          return .obj pid
      else bindChecked
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
termination_by structural n _ _ _ _ _ _ _ _ _ _ _ _ => n

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
        -- the private methods and accessors first (PrivateMethodOrAccessorAdd, §7.3.30): a
        -- second add to the same object is a TypeError, a getter and setter make one accessor
        if let .obj tid := thisV then
          let mut added : Array String := #[]
          for (ek, fn) in fields do
            if let some (tag, k) := privElemOf ek then
              let own := (← getObj tid).getOwn k
              if tag == 'm' then
                if own.isSome then throwErr .type s!"Cannot initialize private method {privDisplay k} twice on the same object"
                defineOwn tid k (.data fn false false false)
              else
                let (g, st) ← match own with
                  | none => pure (Value.undef, Value.undef)
                  | some (.acc g st _ _) =>
                    if added.contains k then pure (g, st)
                    else throwErr .type s!"Cannot initialize {privDisplay k} twice on the same object"
                  | some _ => throwErr .type s!"Cannot initialize {privDisplay k} twice on the same object"
                defineOwn tid k (if tag == 'g' then .acc fn st false false else .acc g fn false false)
              added := added.push k
        for (k, init) in fields do
          if (privElemOf k).isSome then continue
          let v ← callV n init thisV #[]
          match thisV with
          | .obj tid =>
            match (← getObj tid).getOwn k with
            | some p =>
              -- PrivateFieldAdd (§7.3.31): never twice on one object
              if isPrivKey k then throwErr .type s!"Cannot initialize {privDisplay k} twice on the same object"
              if !p.configurable then throwErr .type s!"Cannot redefine property: {k}"
            | none => pure ()
            defineOwn tid k (.data v true (!isPrivKey k) true)
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()
termination_by structural n _ _ _ => n

/-- GetPrototypeFromConstructor (§10.1.14): `newTarget.prototype` when it is an object, else
the intrinsic `pick` of the new target's realm (GetFunctionRealm). -/
def protoFromCtor : Nat → Value → (Realm → Nat) → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, nt, pick => do
    let p ← getV n nt "prototype"
    if p.isObj then pure p else pure (.obj (pick (← funRealm nt)))
termination_by structural n _ _ => n

/-- [[Construct]] of a built-in constructor whose steps do not read the new target
(OrdinaryCreateFromConstructor, §10.1.13): with a new target other than the constructor itself
(`Reflect.construct`, a subclass), the object it made gets the new target's prototype, or the
intrinsic of the new target's realm. `Object` with such a new target makes a new ordinary
object and reads no argument (§20.1.1.1 step 1). -/
def constructNative : Nat → Native → Value → Array Value → Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, nid, f, args, nt => do
    let same := strictEq nt f
    let pick? : Option (Realm → Nat) := match nid with
      | .objectCtor => some (·.objectProto) | .functionCtor => some (·.functionProto)
      | .arrayCtor => some (·.arrayProto) | .stringCtor => some (·.stringProto)
      | .numberCtor => some (·.numberProto) | .booleanCtor => some (·.booleanProto)
      | .regexpCtor => some (·.regexpProto) | .dataViewCtor => some (·.dataViewProto)
      | .typedCtor i => some (fun r => r.typedProtos.getD i r.objectProto)
      | .x (.dynFunction 1) => some (fun r => r.orFn r.genFnProto)
      | .x (.dynFunction 2) => some (fun r => r.orFn r.asyncFnProto)
      | .x (.dynFunction 3) => some (fun r => r.orFn r.asyncGenFnProto)
      | _ => none
    match pick? with
    | some pick =>
      if same then callNative n nid .undef args (some nt)
      else if nid == .objectCtor then
        pure (.obj (← alloc { proto := ← protoFromCtor n nt pick }))
      else
        let res ← callNative n nid .undef args (some nt)
        if let .obj o := res then
          let p ← protoFromCtor n nt pick
          modifyObj o fun ob => { ob with proto := p }
        pure res
    | none => callNative n nid .undef args (some nt)
termination_by structural n _ _ _ _ => n

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
          -- GetPrototypeFromConstructor (§10.1.14): the fallback is of the new target's realm
          let o ← alloc { proto := (← protoOr p newTarget (·.objectProto)) }
          let res ← callClosure n fd env capThis capNT home f (.obj o) newTarget args
          match fd.kind, res with
          | _, .obj _ => pure res
          | .ctor true, .undef => pure (.obj o)
          | .ctor true, _ => throwErr .type "Derived constructors may only return object or undefined"
          | _, _ => pure (.obj o)
      | .native nid =>
        let h ← get
        let k := fnRealmIdx h id
        if h.realms.isEmpty || k == h.curRealm then constructNative n nid f args newTarget
        else inRealm k (constructNative n nid f args newTarget)
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
    let needs := ss.any Tier1.isLexical
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
    | .member o k => pure (some (← evalExpr n ctx o), some (← privRk ctx.env k))
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
    -- an elision in an array literal leaves the index absent (§13.2.4.1); no call has one
    | .ident "" => evalArgs n ctx as (acc.push .hole)
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
        | .member o k => do let b ← evalExpr n ctx o; pure (← getV n b (← privRk ctx.env k), b)
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
    | .argCount => pure (.num (Float.ofNat ctx.argc))
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
          | some e =>
            -- an object environment record of `with` (§9.1.1.2.7 DeleteBinding): the
            -- binding object's [[Delete]]
            let env := h.envs.getD e default
            match env.withObj with
            | some o =>
              if env.has x then pure (.bool false) else
              match (h.obj o).getOwn x with
              | none => pure (.bool true)
              | some p =>
                let arrayLen := match (h.obj o).kind with | .array _ => x == "length" | _ => false
                if p.configurable && !arrayLen then deleteOwn o x; pure (.bool true)
                else pure (.bool false)
            | none => pure (.bool false)
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
          | p => pure (.num (-(← toNumQ n p)))
        | .plus => pure (.num (← toNum n v))
        | .not => pure (.bool !(toBool v))
        | .bnot => match ← toPrim n v "number" with
          | .big i => pure (.big (-i - 1))
          | p => pure (intV (-(toInt32 (← toNumQ n p)) - 1))
        | .typeof => pure (.str (← typeOf v))
        | .void => pure .undef
        | .delete => pure (.bool true)
    | .binary .inOp (.member (.ident "") k) b =>
      -- `#x in o` (§13.10.1, `privIn`): the private name's key itself
      match ← evalExpr n ctx b with
      | .obj id => pure (.bool ((← getObj id).getOwn (← privRk ctx.env k)).isSome)
      | _ => throwErr .type "Cannot use 'in' operator to search for a key in a non-object"
    | .binary op a b =>
      -- tier 1: both operands numbers known without a step (`Tier1.arith?`)
      Tier1.withFast md.tier1 (Tier1.arith? ctx op a b) pure
        (Tier1.binaryGen (fun e => evalExpr n ctx e) (fun o x y => binop n o x y) ctx op a b)
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
        if !done then
          -- not an Array's element: a typed array's element by its number (`typedSetNum`), else `putV`
          let done ← typedSetNum id x v
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
      let k ← if isPrivKey k then privRk ctx.env k else pure k
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
      -- tier 1: a resolved name's slot written in place (`Tier1.setLocal?`)
      Tier1.withFast md.tier1 (Tier1.setLocal? target v ctx) pure (putTarget n ctx target b k v)
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
      -- tier 1: a number in a writable slot, read and written in place (`Tier1.incLocal?`)
      Tier1.withFast md.tier1 (Tier1.incLocal? pre inc x h i ctx) pure
        (Tier1.updateGen (lookupLocal n ctx x h i) (fun v => assignLocal n ctx x h i v)
          (fun p => toPrim n p "number") (fun p => toNum n p) pre inc)
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
    | .call (.ident "%dstr") [.str "init", .str x, e, .bool mutable] =>
      -- InitializeReferencedBinding of a `let` or `const` name of a lowered declaration
      let v ← evalNamed n ctx e (.id x)
      match (← get).findEnv x 100000 ctx.env with
      | some env => declare env x { v, mutable }
      | none => throwErr .reference s!"{x} is not defined"
      pure .undef
    | .call (.ident "%dstr") (.str op :: args) =>
      -- the internal calls of a lowered destructuring assignment (`dstrLower`)
      let argv ← evalArgs n ctx args #[]
      let a0 := argv.getD 0 .undef
      match op with
      | "iter" => getIterator n a0
      | "next" =>
        let next ← getV n a0 "next"
        let r ← callV n next a0 #[]
        if !r.isObj then throwErr .type "Iterator result is not an object"
        pure r
      | "close" => iterClose n a0; pure .undef
      | "closeQuiet" => let _ ← catchJS (iterClose n a0) (fun _ => pure ()); pure .undef
      | "push" =>
        if let .obj id := a0 then
          let v := argv.getD 1 .undef
          modifyObj id fun o => match o.kind with
            | .array es => { o with kind := .array (es.push v) }
            | _ => o
        pure .undef
      | "req" =>
        match a0 with
        | .undef | .null => throwErr .type "Cannot destructure 'undefined' or 'null'"
        | v => pure v
      | "rest" =>
        let mut used : List String := []
        for k in argv.toList.drop 1 do used := (← toKey n k) :: used
        let o ← newObject
        copyDataProps n o a0 used
        pure (.obj o)
      | _ => throwErr .syntax "internal destructuring call"
    | .call callee args =>
      let (f, thisV) ← match callee with
        | .optCallee inner =>
          let (f, t) ← match inner with
            | .member o k => do let b ← evalExpr n ctx o; pure (← getV n b (← privRk ctx.env k), b)
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
          -- (a private name's static key is never a property: `fastGetV` misses it, and the
          -- general path resolves it first, so the hit path pays nothing for private names)
          let f ← (match (← get).fastGetV b k with
            | .hole => do getV n b (← if isPrivKey k then privRk ctx.env k else pure k)
            | v => pure v)
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
      | .hole => getV n b (← if isPrivKey k then privRk ctx.env k else pure k)
      | v => pure v
    | .index o k =>
      let b ← (match leafV (← get) ctx o with | .hole => evalExpr n ctx o | v => pure v)
      let kv ← (match leafV (← get) ctx k with | .hole => evalExpr n ctx k | v => pure v)
      match b, kv with
      | .obj id, .num x =>
        match (← getObj id).kind with
        | .array es =>
          if x ≥ 0 && x < Float.ofNat es.size && x.floor == x then
            match es.getD x.toUInt64.toNat .undef with
            | .hole => getV n b (← toKey n kv)
            | v => pure v
          else getV n b (← toKey n kv)
        | _ =>
          -- an element of a typed array by its number (`typedElemNum`), else the general path
          match typedElemNum (← get) id x with
          | .hole => getV n b (← toKey n kv)
          | w => pure w
      | .undef, _ => throwErr .type "Cannot read properties of undefined"
      | .null, _ => throwErr .type "Cannot read properties of null"
      | _, _ => getV n b (← toKey n kv)


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
      let r ← catchJS (do
          let ctx' ← bindIter n ctx kind target v
          let c ← evalStmt n ctx' [] body
          pure (Except.ok c))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw e) =>
        let _ ← catchJS (iterClose n it) (fun _ => pure ())
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
      if (← get).useVm then
        let _ ← vmEnter n c ctx.env ctx.thisV ctx.thisV #[]
        pure .normal
      else evalStmt n ctx labels s
    -- tier 1: a block that declares nothing lexical needs no `evalBlock` and `enterBlock`
    | .block ss =>
      Tier1.withFast md.tier1 (Tier1.plainBlock? ss) (fun _ => evalStmts n ctx ss) (evalBlock n ctx ss)
    | .blockF ss =>
      -- no closure holds this block's environment: its slot is reused on a normal end
      -- (after a throw it stays allocated, which is only memory)
      let ctx' ← enterBlock n ctx ss
      let c ← evalStmts n ctx' ss
      if ctx'.env != ctx.env then releaseEnv ctx'.env
      pure c
    | .throwS e => throw (.throw (← evalExpr n ctx e))
    | .tryS body param handler fin =>
      let r ← catchJS (do let c ← evalBlock n ctx body; pure (Except.ok c))
        (fun a => pure (Except.error a))
      let r ← match r, handler with
        | .error (.throw v), some hs =>
          catchJS (do
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
      let r ← catchJS (do
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
        let _ ← catchJS (iterClose n it) (fun _ => pure ())
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

/-- IteratorClose (§7.4.11) with an abrupt completion: on a throw, `return` is called and what it
does is ignored (the original throw wins, step 5), then the completion goes on; a halt goes on
at once, with no call. It never returns normally. -/
def iterCloseAbrupt : Nat → Value → Abrupt → M Unit
  -- out of fuel like every function of the block (throwing `a` here, with no call, made a run
  -- end differently at fuel 0 than at fuel 1: not monotone in the fuel, `JS/FuelMono.lean`)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, it, a => do
    if let .throw _ := a then
      let _ ← catchJS (iterClose n it) (fun _ => pure ())
    throw a
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
                -- a proxy whose target is `this` itself (a parent constructor that returns
                -- `new Proxy(this, ...)`): `this` would become its own target, and every use of
                -- it a loop with no step taken (a Test262 STALL); the target becomes a copy of
                -- `this` as it was
                let kind ← match ro.kind with
                  | .proxy (.obj t) hnd =>
                    if t == tid then do
                      let o2 ← alloc (← getObj tid)
                      pure (Kind.proxy (.obj o2) hnd)
                    else pure ro.kind
                  | k => pure k
                modifyObj tid fun o => { o with kind, props := ro.props, keys := ro.keys }
      | .native .promiseCtor =>
        -- a subclass of Promise: `this` becomes the promise itself, so the resolving functions
        -- the executor gets settle the object the subclass constructor returns (a copy of
        -- another promise would never settle)
        let _ ← callNative n (.x .promiseInitOn) ctx.thisV args ctx.newTarget
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
    tagFn fid
    defineOwn fid "length" (.data (.num (Float.ofNat fd.expectedArgs)) false false true)
    defineOwn fid "name" (.data (.str cname) false false true)
    defineOwn fid "prototype" (.data (.obj proto) false false false)
    setHidden proto "constructor" (.obj fid)
    -- the private names of this evaluation (§15.7.14 steps 5-6: a new Private Name each)
    for m in members do
      if let .mk _ _ (.lit k) _ := m then
        if isPrivKey k && !((← get).envs.getD cenv default).has k then
          declare cenv k { v := .str (k ++ "#" ++ toString fid), mutable := false }
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
      | .lit s => privRk ctx.env s
      | .computed e => do toKey n (← evalExpr n { ctx with thisV := .obj fid } e)
    if static && key == "prototype" && kind != .field then
      throwErr .type "Classes may not have a static property named 'prototype'"
    let nm ← nameOfKey key
    -- a private method or accessor of the instances (§15.7.14 step 36: [[PrivateMethods]]) is
    -- added to each instance before its fields (InitializeInstanceElements), not to the prototype
    if !static && isPrivKey key && (kind == .method || kind == .getter || kind == .setter) then
      let tag := if kind == .method then 'm' else if kind == .getter then 'g' else 's'
      let fn ← makeClosure ctx f (if kind == .method then nm else if kind == .getter then "get " ++ nm else "set " ++ nm) (.obj proto)
      return ← defineMembers n ctx fid proto ms (acc.push (privElemKey tag key, fn))
    match kind with
    | .method =>
      let m ← makeClosure ctx f nm (.obj target)
      if isPrivKey key then defineOwn target key (.data m false false false) else setHidden target key m
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
      match (parseScript code ctx.strict (evalCode := true) (inFunction := ctx.env != 0)).map Resolve.script with
      | .error e => throwErr .syntax ((e.drop 13).toString)
      | .ok sc =>
        -- EvalDeclarationInstantiation: sloppy eval code in a function's parameters may not
        -- declare `arguments` as a var
        if !sc.strict && ctx.env != 0 && (← get).paramEnv == ctx.env && sc.vars.contains "arguments" then
          throwErr .syntax "eval code in parameter expressions cannot declare 'arguments'"
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
        let r ← catchJS (do
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
          let r ← catchJS (do
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
        let r ← catchJS (do
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
          let r ← catchJS (do let c ← evalStmt n ctx [] s; pure (Except.ok c))
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
        let r ← catchJS (do
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
        let r ← catchJS (do pure (Except.ok (← iterStep n it))) (fun a => pure (Except.error a))
        match r with
        | .error (.throw e) => genUnwind n rest (.throw e)
        | .error a => throw a
        | .ok none => genRun n rest (.send .undef)
        | .ok (some x) =>
          let r ← catchJS (do pure (Except.ok (← bindIter n ctx kind target x)))
            (fun a => pure (Except.error a))
          match r with
          | .error (.throw e) =>
            let _ ← catchJS (iterClose n it) (fun _ => pure ())
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
    let r ← catchJS (do pure (Except.ok (← evalExpr n ctx e))) (fun a => pure (Except.error a))
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
              let r ← catchJS (do
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
          let r ← catchJS (do pure (Except.ok (← getIterator n v))) (fun a => pure (Except.error a))
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
      let r ← catchJS (do
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
    | .forIn kind target obj body =>
      if target.hasYield then genEnter n ctx labels (forTargetTemp (← get).envs.size false kind target obj body) rest
      else if obj.hasYield then
        -- the object's yields first, in a temporary (as for `for-of`)
        let t := s!"%it{(← get).envs.size}"
        genRun n (.block ctx [.decl .letK [Decl.mk (.id t) (some obj)],
          labels.foldr .labeled (.forIn kind target (.ident t) body)] :: rest) (.send .undef)
      else if !body.hasYield then genLift n ctx s rest
      else
      -- a `for-in` whose body yields (an `await` in an async function): the keys of the object
      -- (EnumerateObjectProperties, §14.7.5.9) taken first, then walked as a `for-of` over
      -- them. Does not do: skip a key deleted by the body before its turn (`forInLoop` does).
      let r ← catchJS (do
          let o ← evalExpr n ctx obj
          let keys ← enumKeys o
          pure (Except.ok (← getIterator n (← newArray (keys.map keyStrV)))))
        (fun a => pure (Except.error a))
      match r with
      | .error (.throw x) => genUnwind n rest (.throw x)
      | .error a => throw a
      | .ok it => genRun n (.loopOf ctx labels kind target it body :: rest) (.send .undef)
    | .forOf kind target obj body =>
      if target.hasYield then genEnter n ctx labels (forTargetTemp (← get).envs.size true kind target obj body) rest
      else if obj.hasYield then
        -- the iterable's yields first, in a temporary
        let t := s!"%it{(← get).envs.size}"
        genRun n (.block ctx [.decl .letK [Decl.mk (.id t) (some obj)],
          labels.foldr .labeled (.forOf kind target (.ident t) body)] :: rest) (.send .undef)
      else
      let r ← catchJS (do pure (Except.ok (← getIterator n (← evalExpr n ctx obj))))
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
      let _ ← catchJS (iterClose n it) (fun _ => pure ())
      genUnwind n rest c
    | .delegate _ it _, .throw v =>
      if let some (iter, _, ph) := ← asyncDelegate? it then
        -- `yield*` in an async generator. Phase 0: `throw(v)` came to the `yield`; the inner
        -- `throw` is called and awaited, or the iterator is closed and a TypeError follows.
        -- Other phases: the awaited promise was rejected.
        if ph != 0 then
          setDelegatePhase it 0
          return ← genUnwind n rest c
        let r ← catchJS (do
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
        let _ ← catchJS (iterClose n it) (fun _ => pure ())
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
        let r ← catchJS (do
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
      let r ← catchJS (do
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
      let r ← catchJS (do pure (Except.ok (← genRun n frames input))) (fun a => pure (Except.error a))
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
      let r ← catchJS (do pure (Except.ok (← getV n x "then"))) (fun a => pure (Except.error a))
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
    let r ← catchJS (do let _ ← callV n f .undef args; pure none) (fun a => pure (some a))
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
    let p ← catchJS (promiseResolve n v) (fun a => match a with
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
    let r ← catchJS (do pure (Except.ok (← genRun n frames input))) (fun a => pure (Except.error a))
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

/-- The evaluator at fuel `n`, as the built-ins call it (`CoreFn`). -/
def coreRun : Nat → (op : CoreOp H) → M op.Res
  | 0, _ => throw (.halt "fuel")
  | n + 1, op =>
    match op with
    | .getV a0 a1 => getV n a0 a1
    | .proxyTrap a0 a1 => proxyTrap n a0 a1
    | .hasProp a0 a1 => hasProp n a0 a1
    | .getRecv a0 a1 a2 => getRecv n a0 a1 a2
    | .ownKeysOf a0 => ownKeysOf n a0
    | .ownDesc a0 a1 => ownDesc n a0 a1
    | .putV a0 a1 a2 a3 => putV n a0 a1 a2 a3
    | .toPrim a0 a1 => toPrim n a0 a1
    | .tryMethods a0 a1 => tryMethods n a0 a1
    | .toNum a0 => toNum n a0
    | .typedConv a0 a1 => typedConv n a0 a1
    | .toStr a0 => toStr n a0
    | .toKey a0 => toKey n a0
    | .toObj a0 => toObj n a0
    | .instOf a0 a1 => instOf n a0 a1
    | .callV a0 a1 a2 => callV n a0 a1 a2
    | .construct a0 a1 a2 => construct n a0 a1 a2
    | .evalStmts a0 a1 => evalStmts n a0 a1
    | .evalExpr a0 a1 => evalExpr n a0 a1
    | .getIterator a0 => getIterator n a0
    | .iterStep a0 => iterStep n a0
    | .iterClose a0 => iterClose n a0
    | .iterToArray a0 a1 => iterToArray n a0 a1
    | .iterCloseAbrupt a0 a1 => iterCloseAbrupt n a0 a1
    | .directEval a0 a1 => directEval n a0 a1
    | .genRun a0 a1 => genRun n a0 a1
    | .asyncStep a0 a1 => asyncStep n a0 a1
    | .promiseResolve a0 => promiseResolve n a0
    | .resolvePromise a0 a1 => resolvePromise n a0 a1
    | .rejectPromise a0 a1 => rejectPromise n a0 a1
    | .performThen a0 a1 a2 a3 => performThen n a0 a1 a2 a3
    | .iterResult a0 a1 => iterResult n a0 a1
    | .agenDrain a0 => agenDrain n a0
    | .agenRun a0 a1 a2 => agenRun n a0 a1 a2
    | .callNative a0 a1 a2 a3 => callNative n a0 a1 a2 a3
    | .genericPush a0 a1 => genericPush n a0 a1
    | .arraySpliceGeneric a0 a1 => arraySpliceGeneric n a0 a1
    | .deleteOrThrow a0 a1 => deleteOrThrow n a0 a1
    | .jsonRevive a0 a1 a2 a3 a4 => jsonRevive n a0 a1 a2 a3 a4
    | .arrayGeneric a0 a1 a2 => arrayGeneric n a0 a1 a2
    | .speciesFrom a0 a1 => speciesFrom n a0 a1
    | .speciesFill a0 a1 a2 => speciesFill n a0 a1 a2
    | .elemsOf a0 => elemsOf n a0
    | .elemAt a0 a1 a2 => elemAt n a0 a1 a2
    | .iterArray a0 a1 a2 a3 a4 a5 a6 => iterArray n a0 a1 a2 a3 a4 a5 a6
    | .reduceArray a0 a1 a2 a3 a4 => reduceArray n a0 a1 a2 a3 a4
    | .arrayLikeLength a0 => arrayLikeLength n a0
    | .mergeSort a0 a1 => mergeSort n a0 a1
    | .toPropDesc a0 => toPropDesc n a0
    | .defineOwnProp a0 a1 a2 => defineOwnProp n a0 a1 a2
    | .defineFromDescriptor a0 a1 a2 => defineFromDescriptor n a0 a1 a2
    | .jsonSer a0 a1 a2 a3 a4 a5 a6 => jsonSer n a0 a1 a2 a3 a4 a5 a6
    | .regexExec a0 a1 => regexExec n a0 a1
    | .regExpExecG a0 a1 => regExpExecG n a0 a1
    | .speciesCtor a0 a1 => speciesCtor n a0 a1
    | .matchArray a0 a1 a2 => matchArray n a0 a1 a2
    | .stringSymDispatch a0 a1 a2 => stringSymDispatch n a0 a1 a2
    | .regexpSymbol a0 a1 a2 => regexpSymbol n a0 a1 a2
    | .stringOrMath a0 a1 a2 => stringOrMath n a0 a1 a2
termination_by structural n _ => n

/-- Built-in functions. `newTarget` is set for `new`. -/
def callNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, a0, a1, a2, a3 => Natives.callNative (coreRun n) a0 a1 a2 a3
termination_by structural n _ _ _ _ => n


/-- The slow path of a global name: the lookup, and the cache learns the slot. -/
@[noinline]
def vmGlobalMiss : Nat → Nat → String → Nat → Bool → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, env, x, site, strict => do
    let v ← lookup n { env, thisV := .undef, strict } x
    modify fun h => h.globalLearn site env x
    pure v
termination_by structural n _ _ _ _ => n

/-- The unary operators, as the evaluator does them. -/
def vmUnary : Nat → UnOp → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, op, v => do
    match op with
    | .neg => match ← toPrim n v "number" with
      | .big i => pure (.big (-i))
      | p => pure (.num (-(← toNumQ n p)))
    | .plus => pure (.num (← toNum n v))
    | .not => pure (.bool !(toBool v))
    | .bnot => match ← toPrim n v "number" with
      | .big i => pure (.big (-i - 1))
      | p => pure (intV (-(toInt32 (← toNumQ n p)) - 1))
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
        if x ≥ 0 && x < Float.ofNat es.size && x.floor == x then
          match es.getD x.toUInt64.toNat .undef with
          | .hole => getV n b (← toKey n kv)
          | v => pure v
        else getV n b (← toKey n kv)
      | _ =>
        match typedElemNum (← get) id x with
        | .hole => getV n b (← toKey n kv)
        | w => pure w
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
        modify fun h => h.globalLearn site env x
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
          if x ≥ 0 && x < Float.ofNat es.size && x.floor == x && !(es.getD x.toUInt64.toNat .undef).isHole then
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
          -- a typed array's element by its number is read from the heap before the registers are
          -- stashed: with the stash and the take around it the compiled loop took the heap record
          -- apart and built it again for each read. `vmSettle` leaves the heap as they would.
          match typedElemNum (← get) id x with
          | .hole =>
            vmStash regs fregs (bp + code.nregs)
            let v ← getV n b (keyOfNum x)
            let (regs, fregs) ← vmTake
            match (v) with
            | .num x => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
            | wv => vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
          | .num x =>
            vmSettle (bp + code.nregs)
            vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x)
          | wv =>
            vmSettle (bp + code.nregs)
            vmLoop n code (pc + 1) bp env fr (regs.set! (bp + dst) wv) fregs
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
        if !done then
          let done ← typedSetNum id x v
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
      -- the callee's code is the `Option` already in its record: no tuple is made for a call
      -- (three cells a call, 2026-11-27); its environment and captured `this` are read apart
      let callee := vmCallCode h fv
      -- a primitive `this` for a sloppy function needs an object made: the general path
      let primThis := match thisV with | .undef | .null | .obj _ => false | _ => true
      -- with more than one realm, every call takes the general path (`callClosure` changes realm)
      let callee := match callee with
        | some c =>
          if (primThis && !c.isArrow && !c.strict) || !h.realms.isEmpty then none else callee
        | none => none
      match callee with
      | some c =>
        let cenv := vmCallEnv h fv
        let capThis := vmCallThis h fv
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
    -- §23.1.3.23 Array.prototype.push on any object
    let o := Value.obj (← toObj n thisV)
    let l ← arrayLikeLength n o
    if l + args.size > 9007199254740991 then throwErr .type "Pushing past the largest array length"
    for i in [0:args.size] do putV n o (toString (l + i)) args[i]! true
    putV n o "length" (.num (Float.ofNat (l + args.size))) true
    pure (.num (Float.ofNat (l + args.size)))
termination_by structural n _ _ => n

/-- Array.prototype.splice (§23.1.3.31) on any object, step by step. -/
def arraySpliceGeneric : Nat → Value → Array Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, thisV, args => do
    let oid ← toObj n thisV
    let o := Value.obj oid
    let len ← arrayLikeLength n o
    let start := relIndex (← toNum n (argD args 0)) len
    let itemCount := args.size - (min args.size 2)
    let skip ← if args.size == 0 then pure 0
      else if args.size == 1 then pure (len - start)
      else do
        let dc := toIntegerOrInf (← toNum n (argD args 1))
        pure (if dc ≤ 0 then 0 else min dc.toUInt64.toNat (len - start))
    if len + itemCount - skip > 9007199254740991 then throwErr .type "Splicing past the largest array length"
    -- ArraySpeciesCreate(O, actualSkipCount): an Array past 2^32 - 1 is a RangeError
    let sp ← speciesFrom n o skip
    if sp.isNone && skip > 4294967295 then throwErr .range "Invalid array length"
    let mut removed : Array Value := #[]
    for k in [0:skip] do
      tick
      let from_ := toString (start + k)
      let present ← hasProp n oid from_
      let v ← if present then getV n o from_ else pure .hole
      removed := removed.push v
    let a ← match sp with
      | none => newArray removed
      | some a => speciesFill n a removed (some skip)
    if sp.isNone then putV n a "length" (.num (Float.ofNat skip)) true
    if itemCount < skip then
      for k in [start:len - skip] do
        tick
        let from_ := toString (k + skip)
        let to := toString (k + itemCount)
        if ← hasProp n oid from_ then putV n o to (← getV n o from_) true
        else deleteOrThrow n o to
      for j in [0:skip - itemCount] do
        tick
        deleteOrThrow n o (toString (len - 1 - j))
    else if itemCount > skip then
      for j in [0:len - skip - start] do
        tick
        let k := len - skip - j
        let from_ := toString (k + skip - 1)
        let to := toString (k + itemCount - 1)
        if ← hasProp n oid from_ then putV n o to (← getV n o from_) true
        else deleteOrThrow n o to
    for i in [0:itemCount] do putV n o (toString (start + i)) args[i + 2]! true
    putV n o "length" (.num (Float.ofNat (len - skip + itemCount))) true
    pure a
termination_by structural n _ _ => n

/-- [[Delete]] (§10.1.10, §10.5.10 for a Proxy): whether the property is gone. -/
def deleteProp : Nat → Value → String → M Bool
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, key => do
    let .obj id := v | pure true
    let o ← getObj id
    if let .proxy pt hnd := o.kind then
      match ← proxyTrap n hnd "deleteProperty" with
      | some f => return toBool (← callV n f hnd #[pt, keyValue key])
      | none => return ← deleteProp n pt key
    match o.getOwn key with
    | none => pure true
    | some p =>
      let arrayLen := match o.kind with | .array _ => key == "length" | _ => false
      if p.configurable && !arrayLen then deleteOwn id key; pure true
      else pure false
termination_by structural n _ _ => n

/-- DeletePropertyOrThrow (§7.3.10): [[Delete]], a TypeError when it answers false (a
non-configurable property, a Proxy trap that says false). -/
def deleteOrThrow : Nat → Value → String → M Unit
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, v, key => do
    if !(← deleteProp n v key) then throwErr .type s!"Cannot delete property '{key}'"
termination_by structural n _ _ => n

/-- InternalizeJSONProperty (§25.5.1.1): the reviver called bottom-up on every property of
the parsed value, a result of undefined deleting it. `depth` bounds the nesting. -/
def jsonRevive : Nat → Array (Nat × String × String × Value) → Value → Value → String → Nat → M Value
  | 0, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, srcs, reviver, holder, name, depth => do
    if depth > 10000 then throwErr .range "Maximum call stack size exceeded"
    let val ← getV n holder name
    if let .obj vid := val then
      let keys ← if ← isArrayDeep 100000 val then do
          let len ← arrayLikeLength n val
          pure ((List.range len).toArray.map toString)
        else do
          let mut ks : Array String := #[]
          for k in ← ownKeysOf n vid do
            if isSymKey k || isPrivKey k then continue
            match ← ownDesc n vid k with
            | some p => if p.enumerable then ks := ks.push k
            | none => pure ()
          pure ks
      for k in keys do
        tick
        let nv ← jsonRevive n srcs reviver val k (depth + 1)
        match nv with
        | .undef => let _ ← deleteProp n val k
        | _ => let _ ← defineOwnProp n vid k { value := some nv, writable := some true, enumerable := some true, configurable := some true }
    -- the third argument (proposal-json-parse-with-source): an object, with `source` for a
    -- primitive that is still the parsed one
    let ctxObj ← newObject
    if !val.isObj then
      if let .obj hid := holder then
        if let some (_, _, t, ov) := srcs.find? (fun (h, k, _, _) => h == hid && k == name) then
          if sameValue ov val then
            defineOwn ctxObj "source" (.data (.str t) true true true)
    callV n reviver holder #[keyStrV name, val, .obj ctxObj]
termination_by structural n _ _ _ _ _ => n

/-- Array.prototype pop (§23.1.3.22), shift (§23.1.3.27), unshift (§23.1.3.34) and reverse
(§23.1.3.25) on any object, step by step: the path for what is not a plain Array with all of
its elements (an array-like, a frozen or non-extensible Array, an Array with holes that its
prototypes may fill, a Proxy). -/
def arrayGeneric : Nat → Native → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args => do
    let oid ← toObj n thisV
    let o := Value.obj oid
    let len ← arrayLikeLength n o
    let setLen (k : Nat) : M Unit := putV n o "length" (.num (Float.ofNat k)) true
    match id with
    | .arrayPop =>
      if len == 0 then setLen 0; return .undef
      let key := toString (len - 1)
      let e ← getV n o key
      deleteOrThrow n o key
      setLen (len - 1)
      pure e
    | .arrayShift =>
      if len == 0 then setLen 0; return .undef
      let first ← getV n o "0"
      for k in [1:len] do
        tick
        if ← hasProp n oid (toString k) then putV n o (toString (k - 1)) (← getV n o (toString k)) true
        else deleteOrThrow n o (toString (k - 1))
      deleteOrThrow n o (toString (len - 1))
      setLen (len - 1)
      pure first
    | .arrayUnshift =>
      let c := args.size
      if c > 0 then
        if len + c > 9007199254740991 then throwErr .type "Unshifting past the largest array length"
        for j in [0:len] do
          tick
          let k := len - j
          if ← hasProp n oid (toString (k - 1)) then putV n o (toString (k + c - 1)) (← getV n o (toString (k - 1))) true
          else deleteOrThrow n o (toString (k + c - 1))
        for i in [0:c] do putV n o (toString i) args[i]! true
      setLen (len + c)
      pure (.num (Float.ofNat (len + c)))
    | _ =>
      -- reverse: the pairs from the ends inwards, each present or absent
      for lower in [0:len / 2] do
        tick
        let upper := len - 1 - lower
        let lk := toString lower
        let uk := toString upper
        let lowerP ← hasProp n oid lk
        let lowerV ← if lowerP then getV n o lk else pure .undef
        let upperP ← hasProp n oid uk
        let upperV ← if upperP then getV n o uk else pure .undef
        if lowerP && upperP then putV n o lk upperV true; putV n o uk lowerV true
        else if upperP then putV n o lk upperV true; deleteOrThrow n o uk
        else if lowerP then deleteOrThrow n o lk; putV n o uk lowerV true
      pure o
termination_by structural n _ _ _ => n

/-- ArraySpeciesCreate (§10.4.2.3): the new object from the species constructor of an Array,
or `none` when the result is a plain Array (not an Array, no `constructor`, or the realm's
Array with its built-in `@@species` getter: the fast path, which reads two properties). -/
def speciesFrom : Nat → Value → Nat → M (Option Value)
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, orig, len => do
    if !(← isArrayDeep 100000 orig) then return none
    let c ← getV n orig "constructor"
    let c ← match c with
      | .obj cid =>
        let co ← getObj cid
        let builtinSpecies ← match co.kind, co.props.get? (symKey 7) with
          | .native .arrayCtor, some (.acc (.obj g) ..) => do
            pure (match (← getObj g).kind with | .native (.x .speciesGetter) => true | _ => false)
          | _, _ => pure false
        if builtinSpecies then return none
        -- another realm's %Array% makes a plain Array of this realm (§10.4.2.3 step 4)
        if let .native .arrayCtor := co.kind then
          match co.props.get? "prototype" with
          | some (.data (.obj p) ..) => if p != (← realm).arrayProto then return none
          | _ => pure ()
        match ← getV n c (symKey 7) with
        | .null => pure Value.undef
        | v => pure v
      | v => pure v
    match c with
    | .undef => pure none
    | _ =>
      if !(← isConstructor c) then throwErr .type "object.constructor[Symbol.species] is not a constructor"
      some <$> construct n c #[.num (Float.ofNat len)] c
termination_by structural n _ _ => n

/-- Fill the object a species constructor made: CreateDataPropertyOrThrow for each present
element, then `length` when the method sets it (slice, splice, concat). -/
def speciesFill : Nat → Value → Array Value → Option Nat → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, a, vals, setLen => do
    let .obj aid := a | throwErr .type "The species constructor did not make an object"
    for i in [0:vals.size] do
      let v := vals[i]!
      if v.isHole then continue
      if !(← defineOwnProp n aid (toString i) { value := some v, writable := some true, enumerable := some true, configurable := some true }) then
        throwErr .type s!"Cannot define property {i} of the species result"
    if let some l := setLen then putV n a "length" (.num (Float.ofNat l)) true
    pure a
termination_by structural n _ _ _ => n

/-- The elements of an array, or of an array-like object (`length` and indices). -/
def elemsOf : Nat → Value → M (Array Value)
  | 0, _ => throw (.halt "fuel")
  | n + 1, v => do
    match v with
    | .obj id => match (← getObj id).kind with
      | .array es => pure (holesAsUndef es)
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
      -- map's result leaves the index absent too
      | none => iterArray n id f thisArg arr len (i + 1) (if id == .arrayMap then acc.push .hole else acc)
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
    -- a typed array's numeric keys (§10.4.5.3): only a valid index, as a writable,
    -- enumerable, configurable data property; the value is written to the element
    if let .typed ty b off len := (← getObj id).kind then
      if let some x := canonicalNumericIndex k then
        let live ← liveLen ty b off len
        if !(isIntegral x && !isNegZero x && x ≥ 0 && x < Float.ofNat live) then return false
        if desc.configurable == some false || desc.enumerable == some false || desc.get.isSome
            || desc.set.isSome || desc.writable == some false then return false
        if let some v := desc.value then
          let cv ← typedConv n ty v
          -- the conversion may have detached or shrunk the buffer
          if x < Float.ofNat (← liveLen ty b off len) then typedWriteV ty b off x.toUInt64.toNat cv
        return true
    let o0 ← getObj id
    if k == "length" && o0.generalArrayLen.isSome then
      return ← setGeneralArrayLength (toNum n) id desc
    let old := o0.getOwn k
    match old with
    | some p => if !desc.allowedOn p then return false
    | none => if !o0.extensible then return false
    -- an Array in the general form keeps its length as a property: an index at or past it
    -- needs a writable length (§10.4.2.1 step 3)
    if let (some i, some (l, false)) := (arrayIndex? k, o0.generalArrayLen) then
      if Float.ofNat i ≥ l then return false
    let e := desc.enumerable.getD (match old with | some p => p.enumerable | none => false)
    let c := desc.configurable.getD (match old with | some p => p.configurable | none => false)
    let gt := desc.get
    let st := desc.set
    let vl := desc.value
    -- leave the fast form: keep the present elements, and the length, as ordinary properties;
    -- the object stays an Array (`markArray`)
    let demote : M Unit := do
      let o ← getObj id
      if let .array es := o.kind then
        let o' := (List.range es.size).foldl (fun o j => if Value.isHole es[j]! then o else { o with
            props := o.props.insert (toString j) (.data es[j]! true true true),
            keys := o.keys.push (toString j) }) ({ o with kind := .ordinary } : Obj).markArray
        modifyObj id fun _ => o'.putOwn "length" (.data (.num (Float.ofNat es.size)) true false false)
    if gt.isSome || st.isSome then
      let (og, os) := match old with | some (.acc g s _ _) => (g, s) | _ => (.undef, .undef)
      -- an accessor on an Array's index needs the general form (the fast form holds values only)
      if (arrayIndex? k).isSome then
        if let .array _ := o0.kind then demote
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
            demote
            defineOwn id k (.data v w e c)
            let _ := (i, es)
        | _, _ => defineOwn id k (.data v w e c)
    if let some i := arrayIndex? k then
      if let some (l, w) := (← getObj id).generalArrayLen then
        if Float.ofNat i ≥ l then
          modifyObj id (·.putOwn "length" (.data (.num (Float.ofNat (i + 1))) w false false))
    return true
termination_by structural n _ _ _ => n

/-- DefinePropertyOrThrow (§7.3.8) with the descriptor object `d` (Object.defineProperty,
Object.defineProperties, Object.create). -/
def defineFromDescriptor : Nat → Nat → String → Value → M Unit
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, k, d => do
    let desc ← toPropDesc n d
    if !(← defineOwnProp n id k desc) then
      if ((← getObj id).getOwn k).isSome then throwErr .type s!"Cannot redefine property: {k}"
      else throwErr .type s!"Cannot define property {k}, object is not extensible"
termination_by structural n _ _ _ => n

/-- SerializeJSONProperty (§25.5.2.2) with JSON.stringify's state: the replacer function
(`undefined` when none), the property list (when the replacer is an array), the gap, the indent
and the stack of the objects being serialized. `none` is undefined (the property is left out). -/
def jsonSer : Nat → Value → Option (Array String) → String → String → Array Nat → Value → String → M (Option String)
  | 0, _, _, _, _, _, _, _ => throw (.halt "fuel")
  | n + 1, repl, plist, gap, indent, stack, holder, key => do
    if stack.size > 1000 then throwErr .range "Maximum call stack size exceeded"
    let quote (s : String) : String :=
      "\"" ++ s.foldl (fun acc c => acc ++ match c with
        | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
        | '\x08' => "\\b" | '\x0c' => "\\f"
        | c => if c.toNat < 32 then "\\u" ++ String.ofList ((Nat.toDigits 16 c.toNat).leftpad 4 '0') else String.singleton c) ""
        |> jsonLone |> (· ++ "\"")
    let mut value ← getV n holder key
    match value with
    | .obj _ | .big _ =>
      let tj ← getV n value "toJSON"
      if ← isCallable tj then value ← callV n tj value #[keyStrV key]
    | _ => pure ()
    if ← isCallable repl then value ← callV n repl holder #[keyStrV key, value]
    -- a Number, String, Boolean or BigInt object stands for its primitive
    if let .obj vid := value then
      match (← getObj vid).kind with
      | .prim (.num _) => if !(hiddenFlag (← getObj vid) dateKey) then value := .num (← toNum n value)
      | .prim (.str _) => value := .str (← toStr n value)
      | .prim (.bool b) => value := .bool b
      | .prim (.big b) => value := .big b
      | _ => pure ()
    match value with
    | .null => return some "null"
    | .bool b => return some (if b then "true" else "false")
    | .str s => return some (quote s)
    | .num x => return some (if x.isFinite then numToString x else "null")
    | .big _ => throwErr .type "Do not know how to serialize a BigInt"
    | .obj vid =>
      if ← isCallable value then return none
      if stack.contains vid then throwErr .type "Converting circular structure to JSON"
      let stack := stack.push vid
      let inner := indent ++ gap
      let close (parts : Array String) (op cl : String) : String :=
        if parts.isEmpty then op ++ cl
        else if gap.isEmpty then op ++ ",".intercalate parts.toList ++ cl
        else op ++ "\n" ++ inner ++ (",\n" ++ inner).intercalate parts.toList ++ "\n" ++ indent ++ cl
      if ← isArrayDeep 100000 value then
        -- SerializeJSONArray (§25.5.2.6)
        let len ← arrayLikeLength n value
        let mut parts : Array String := #[]
        for i in [0:len] do
          tick
          parts := parts.push ((← jsonSer n repl plist gap inner stack value (toString i)).getD "null")
        return some (close parts "[" "]")
      -- SerializeJSONObject (§25.5.2.5): the property list, or the own enumerable string keys
      let keys ← match plist with
        | some ks => pure ks
        | none => do
          let mut ks : Array String := #[]
          for k in ← ownKeysOf n vid do
            if isSymKey k || isPrivKey k then continue
            match ← ownDesc n vid k with
            | some p => if p.enumerable then ks := ks.push k
            | none => pure ()
          pure ks
      let mut parts : Array String := #[]
      for k in keys do
        tick
        if let some s ← jsonSer n repl plist gap inner stack value k then
          parts := parts.push (quote (keyStr k) ++ ":" ++ (if gap.isEmpty then "" else " ") ++ s)
      return some (close parts "{" "}")
    | _ => return none
termination_by structural n _ _ _ _ _ _ _ => n

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
        if o.isArray then
          -- an Array that left the fast form (frozen, or with an index of other attributes)
          let es ← elemsOf n v
          let parts ← es.toList.mapM fun e => do
            match ← jsonStr n e (depth + 1) with
            | .str s => pure s
            | _ => pure "null"
          return .str ("[" ++ ",".intercalate parts ++ "]")

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
    -- §22.2.7.2 step 2: ToLength(Get(R, "lastIndex")), read (and converted) in every case
    let li0 := toIntegerOrInf (← toNum n (← getV n rv "lastIndex"))
    let li := if g then li0 else 0
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

/-- RegExpExec (§22.2.7.1): the object's `exec` when it is callable (its result must be an
object or null), else the built-in exec on a RegExp. -/
def regExpExecG : Nat → Value → String → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, rx, s => do
    let exec ← getV n rx "exec"
    let builtin ← match exec with
      | .obj e => do pure (match (← getObj e).kind with | .native .regexpExec => true | _ => false)
      | _ => pure false
    if !builtin && (← isCallable exec) then
      let r ← callV n exec rx #[.str s]
      match r with
      | .obj _ | .null => return r
      | _ => throwErr .type "The result of a RegExp exec method must be an object or null"
    if !(← isRegExpV rx) then throwErr .type "RegExp exec method called on an incompatible receiver"
    match ← regexExec n rx s with
    | none => pure .null
    | some caps => matchArray n (← regexpOf rx).1 s caps
termination_by structural n _ _ => n

/-- SpeciesConstructor (§7.3.22). -/
def speciesCtor : Nat → Value → Value → M Value
  | 0, _, _ => throw (.halt "fuel")
  | n + 1, o, dflt => do
    let c ← getV n o "constructor"
    match c with
    | .undef => pure dflt
    | .obj _ =>
      match ← getV n c (symKey 7) with
      | .undef | .null => pure dflt
      | sp => if ← isConstructor sp then pure sp else throwErr .type "object.constructor[Symbol.species] is not a constructor"
    | _ => throwErr .type "object.constructor is not an object"
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
    -- the groups object: each name once, in the order of the pattern; of groups that share a
    -- name (in different alternatives) the one that took part in the match
    let groupsOf (vs : Array Value) : M Value := do
      if re.names.isEmpty then return .undef
      let o ← alloc { proto := .null }
      let mut seen : Array String := #[]
      for (nm, k) in re.names do
        let v := vs.getD k .undef
        if seen.contains nm then
          if !(v matches .undef) then defineOwn o nm (.data v true true true)
        else
          seen := seen.push nm
          defineOwn o nm (.data v true true true)
      pure (.obj o)
    defineOwn aid "groups" (.data (← groupsOf vals) true true true)
    if re.flags.hasIndices then
      -- §22.2.7.8 MakeMatchIndicesIndexPairArray: [start, end] of each capture, and groups
      let mut pairs : Array Value := #[]
      for c in caps do
        match c with
        | some (a, b) => pairs := pairs.push (← newArray #[.num (Float.ofNat a), .num (Float.ofNat b)])
        | none => pairs := pairs.push .undef
      let ind ← newArray pairs
      if let .obj iid := ind then
        defineOwn iid "groups" (.data (← groupsOf pairs) true true true)
      defineOwn aid "indices" (.data ind true true true)
    pure arr
termination_by structural n _ _ _ => n

/-- String.prototype `match`, `replace`, `replaceAll`, `search` and `split` with a search
value that is an object: its `@@match`, `@@replace`, `@@search` or `@@split` method
decides (§22.1.3.13, .19, .20, .21, .23); `none` when it has none. `replaceAll` first asks a
RegExp for the `g` flag. -/
def stringSymDispatch : Nat → Native → Value → Array Value → M (Option Value)
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args => do
    let a0 := argD args 0
    match thisV with
    | .undef | .null => throwErr .type "String.prototype method called on null or undefined"
    | _ => pure ()
    -- only an object's method is asked (a primitive's prototype is not: ES2025)
    if !a0.isObj then return none
    let sym := match id with
      | .stringMatch => 8 | .stringMatchAll => 9 | .stringSearch => 11 | .stringSplit => 12 | _ => 10
    if id == .stringReplaceAll || id == .stringMatchAll then
      let isRx ← match ← getV n a0 (symKey 8) with
        | .undef => isRegExpV a0
        | m => pure (toBool m)
      if isRx then
        let fl ← getV n a0 "flags"
        match fl with
        | .undef | .null => throwErr .type "RegExp flags are undefined or null"
        | _ => pure ()
        if !(← toStr n fl).contains 'g' then throwErr .type s!"{if id == .stringMatchAll then "matchAll" else "replaceAll"} must be called with a global RegExp"
    match ← getV n a0 (symKey sym) with
    | .undef | .null => pure none
    | m =>
      if !(← isCallable m) then throwErr .type "The search value's Symbol method is not a function"
      let rest := if sym == 8 || sym == 9 || sym == 11 then #[] else #[argD args 1]
      pure (some (← callV n m a0 (#[thisV] ++ rest)))
termination_by structural n _ _ _ => n

/-- RegExp.prototype `[Symbol.match]` (k = 0), `[Symbol.replace]` (1), `[Symbol.search]` (2)
and `[Symbol.split]` (3) (§22.2.6.8, .11, .12, .14): the general steps, which read `flags`,
`lastIndex` and `exec` through the object and take the results apart with `[[Get]]`; a RegExp
that `regexpPristine` accepts takes the built-in fast path instead. -/
def regexpSymbol : Nat → Nat → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, k, rx, args => do
    if !rx.isObj then throwErr .type "RegExp.prototype method called on a non-object"
    let s ← toStr n (argD args 0)
    let len := Str.jsLength s
    let toLen : Value → M Nat := fun v => do
      let x := toIntegerOrInf (← toNum n v)
      pure (if x ≤ 0 then 0 else if x ≥ 9007199254740991.0 then 9007199254740991 else x.toUInt64.toNat)
    let advance : Bool → M Unit := fun fullU => do
      let li ← toLen (← getV n rx "lastIndex")
      putV n rx "lastIndex" (.num (Float.ofNat (advanceIndex s li fullU))) true
    match k with
    | 0 =>
      if ← regexpPristine rx false then return ← extraNative n .stringMatch (.str s) #[rx] none
      let flags ← toStr n (← getV n rx "flags")
      if !flags.contains 'g' then return ← regExpExecG n rx s
      let fullU := flags.contains 'u' || flags.contains 'v'
      putV n rx "lastIndex" (.num 0) true
      let mut out : Array Value := #[]
      for _ in [0:10000000] do
        let r ← regExpExecG n rx s
        if let .null := r then
          return ← (if out.isEmpty then pure .null else newArray out)
        let ms ← toStr n (← getV n r "0")
        out := out.push (.str ms)
        if ms.isEmpty then advance fullU
      throwErr .range "too many matches"
    | 1 =>
      let rv := argD args 1
      if ← regexpPristine rx false then return ← extraNative n .stringReplace (.str s) #[rx, rv] none
      let functional ← isCallable rv
      let tmpl ← if functional then pure "" else toStr n rv
      let flags ← toStr n (← getV n rx "flags")
      let global := flags.contains 'g'
      let fullU := flags.contains 'u' || flags.contains 'v'
      if global then putV n rx "lastIndex" (.num 0) true
      let mut results : Array Value := #[]
      for _ in [0:10000000] do
        let r ← regExpExecG n rx s
        if let .null := r then break
        results := results.push r
        if !global then break
        let ms ← toStr n (← getV n r "0")
        if ms.isEmpty then advance fullU
      let mut acc := ""
      let mut next := 0
      for r in results do
        let nCaps := (← toLen (← getV n r "length")) - 1
        let matched ← toStr n (← getV n r "0")
        let posF := toIntegerOrInf (← toNum n (← getV n r "index"))
        let pos := if posF ≤ 0 then 0 else if posF ≥ Float.ofNat len then len else posF.toUInt64.toNat
        let mut caps : Array Value := #[]
        for i in [1:nCaps + 1] do
          let c ← getV n r (toString i)
          let cv ← match c with
            | .undef => pure Value.undef
            | v => do pure (Value.str (← toStr n v))
          caps := caps.push cv
        let groups ← getV n r "groups"
        let rep ← if functional then do
            let extra : Array Value := match groups with | .undef => #[] | g => #[g]
            toStr n (← callV n rv .undef (#[.str matched] ++ caps ++ #[.num (Float.ofNat pos), .str s] ++ extra))
          else do
            let named ← match groups with
              | .undef => pure none
              | g => do
                let gid ← toObj n g
                let mut tbl : List (String × String) := []
                for nm in templateNames tmpl do
                  let v ← getV n (.obj gid) nm
                  let t ← match v with
                    | .undef => pure ""
                    | v => toStr n v
                  tbl := tbl ++ [(nm, t)]
                pure (some tbl)
            let capS := caps.map fun c => match c with | .str t => some t | _ => none
            pure (getSubstitutionG tmpl matched s pos capS named)
        if pos ≥ next then
          checkStrLen (acc.utf8ByteSize + rep.utf8ByteSize)
          acc := acc ++ Str.sliceUnits s next pos ++ rep
          next := pos + Str.jsLength matched
      pure (.str (if next ≥ len then acc else acc ++ Str.sliceUnits s next len))
    | 2 =>
      if ← regexpPristine rx false then return ← extraNative n .stringSearch (.str s) #[rx] none
      let prev ← getV n rx "lastIndex"
      if !sameValue prev (.num 0) then putV n rx "lastIndex" (.num 0) true
      let r ← regExpExecG n rx s
      let cur ← getV n rx "lastIndex"
      if !sameValue cur prev then putV n rx "lastIndex" prev true
      match r with
      | .null => pure (.num (-1))
      | _ => getV n r "index"
    | 3 =>
      let lim0 := argD args 1
      if ← regexpPristine rx true then return ← extraNative n .stringSplit (.str s) #[rx, lim0] none
      let dflt ← mkNative .regexpCtor "RegExp" 2
      let c ← speciesCtor n rx dflt
      let flags ← toStr n (← getV n rx "flags")
      let unicodeM := flags.contains 'u' || flags.contains 'v'
      let newFlags := if flags.contains 'y' then flags else flags ++ "y"
      let splitter ← construct n c #[rx, .str newFlags] c
      let lim ← match lim0 with
        | .undef => pure 4294967295
        | l => do pure (toUint32 (← toNum n l))
      if lim == 0 then return ← newArray #[]
      if len == 0 then
        let z ← regExpExecG n splitter s
        return ← newArray (match z with | .null => #[.str s] | _ => #[])
      let mut out : Array Value := #[]
      let mut p := 0
      let mut q := 0
      for _ in [0:10000000] do
        if q ≥ len then break
        putV n splitter "lastIndex" (.num (Float.ofNat q)) true
        let z ← regExpExecG n splitter s
        match z with
        | .null => q := advanceIndex s q unicodeM
        | _ =>
          let e := min (← toLen (← getV n splitter "lastIndex")) len
          if e == p then q := advanceIndex s q unicodeM
          else
            out := out.push (.str (Str.sliceUnits s p q))
            if out.size == lim then return ← newArray out
            p := e
            let nc := (← toLen (← getV n z "length")) - 1
            for i in [1:nc + 1] do
              out := out.push (← getV n z (toString i))
              if out.size == lim then return ← newArray out
            q := p
      out := out.push (.str (Str.sliceUnits s p len))
      newArray out
    | _ =>
      -- @@matchAll (§22.2.6.9): a RegExp String Iterator over a copy made by the species
      let dflt ← mkNative .regexpCtor "RegExp" 2
      let c ← speciesCtor n rx dflt
      let flags ← toStr n (← getV n rx "flags")
      let matcher ← construct n c #[rx, .str flags] c
      let li ← toLen (← getV n rx "lastIndex")
      putV n matcher "lastIndex" (.num (Float.ofNat li)) true
      let mode := 20 + (if flags.contains 'g' then 1 else 0) + (if flags.contains 'u' || flags.contains 'v' then 2 else 0)
      let r ← realm
      let proto := match (← getObj r.regexpProto).props.get? rsiProtoKey with
        | some (.data p ..) => p
        | _ => .obj r.arrayIterProto
      let it ← alloc { proto, kind := .iter matcher 0 mode }
      defineOwn it rsiStringKey (.data (.str s) false false false)
      pure (.obj it)
termination_by structural n _ _ _ => n

/-- RegExp, the String methods with a RegExp, Proxy, JSON.parse, ArrayBuffer, the typed
arrays, Date, `performance.now` and the host's natives. -/
def extraNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, a0, a1, a2, a3 => Natives.extraNative (coreRun n) a0 a1 a2 a3
termination_by structural n _ _ _ _ => n

def stringOrMath : Nat → Native → Value → Array Value → M Value
  | 0, _, _, _ => throw (.halt "fuel")
  | n + 1, id, thisV, args => do
    let a0 := argD args 0
    let a1 := argD args 1
    -- each case written out: a local helper that took the operation as a closure boxed its
    -- argument and its answer (three cells a call of `Math.floor`, 2026-11-27)
    match id with
    | .mathFloor => do pure (.num (Float.floor (← toNumQ n a0)))
    | .mathCeil => do pure (.num (Float.ceil (← toNumQ n a0)))
    | .mathAbs => do pure (.num (Float.abs (← toNumQ n a0)))
    | .mathSqrt => do pure (.num (Float.sqrt (← toNumQ n a0)))
    | .mathSin => do pure (.num (Float.sin (← toNumQ n a0)))
    | .mathCos => do pure (.num (Float.cos (← toNumQ n a0)))
    | .mathTan => do pure (.num (Float.tan (← toNumQ n a0)))
    | .mathAtan => do pure (.num (Float.atan (← toNumQ n a0)))
    | .mathLog => do pure (.num (Float.log (← toNumQ n a0)))
    | .mathExp => do pure (.num (Float.exp (← toNumQ n a0)))
    | .mathTrunc => do let x ← toNumQ n a0; pure (.num (if x.isFinite then (if x < 0 then -((-x).floor) else x.floor) else x))
    | .mathSign => do let x ← toNumQ n a0; pure (.num (if x.isNaN then x else if x > 0 then 1 else if x < 0 then -1 else x))
    | .mathRound => do pure (.num (mathRoundNumber (← toNumQ n a0)))
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
          -- IsRegExp(searchString) is a TypeError (§22.1.3.8 step 3 and the others)
          if let .obj _ := a0 then
            let isRx ← match ← getV n a0 (symKey 8) with
              | .undef => isRegExpV a0
              | m => pure (toBool m)
            if isRx then throwErr .type "First argument to String.prototype.includes/startsWith/endsWith must not be a regular expression"
          let p ← toStr n a0
          pure (.bool (indexOfFrom s p (clampPos (← toNum n a1) len)).isSome)
        | .stringStartsWith =>
          -- IsRegExp(searchString) is a TypeError (§22.1.3.8 step 3 and the others)
          if let .obj _ := a0 then
            let isRx ← match ← getV n a0 (symKey 8) with
              | .undef => isRegExpV a0
              | m => pure (toBool m)
            if isRx then throwErr .type "First argument to String.prototype.includes/startsWith/endsWith must not be a regular expression"
          let p ← toStr n a0
          pure (.bool (unitsAt s p (clampPos (← toNum n a1) len)))
        | .stringEndsWith =>
          -- IsRegExp(searchString) is a TypeError (§22.1.3.8 step 3 and the others)
          if let .obj _ := a0 then
            let isRx ← match ← getV n a0 (symKey 8) with
              | .undef => isRegExpV a0
              | m => pure (toBool m)
            if isRx then throwErr .type "First argument to String.prototype.includes/startsWith/endsWith must not be a regular expression"
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
          -- The limit conversion precedes separator conversion, which can throw even
          -- for a zero limit. The @@split dispatch has already run for objects.
          let limit ← match a1 with
            | .undef => pure 4294967295
            | l => do pure (toUint32 (← toNum n l))
          let sep ← toStr n a0
          let separator := match a0 with | .undef => none | _ => some sep
          newArray ((splitPlain s separator limit).map .str)
        | _ => throwErr .type "not a function"
termination_by structural n _ _ _ => n

/-- ArrayBuffer `resize` and `transfer` and its accessors, SharedArrayBuffer, %TypedArray%
(the constructor, `from`, `of`, the accessors and the methods that answer typed arrays),
Atomics without waiting, and `String.prototype.isWellFormed`/`toWellFormed`. -/
def moreNative : Nat → Native → Value → Array Value → Option Value → M Value
  | 0, _, _, _, _ => throw (.halt "fuel")
  | n + 1, a0, a1, a2, a3 => Natives.moreNative (coreRun n) a0 a1 a2 a3
termination_by structural n _ _ _ _ => n

end

end Block

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

/-- %GeneratorFunction%, %AsyncGeneratorFunction%, %AsyncFunction% and their prototypes
(§27.3, §27.4, §27.7), for `initRealm` (kept apart: one `do` block of the whole realm is past
the elaborator's depth). -/
def initFunctionKinds (g genProto asyncGenProto : Nat) : M Unit := do
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

/-- `get [Symbol.species]` on the constructors that have one besides Array (§22.2.5.2,
§24.1.2.3, §24.2.3.2, §25.1.5.3, §27.2.4.8, §23.2.2.4), for `initRealm`. -/
def initSpecies : M Unit := do
  let r ← realm
  let g := r.globalObj
  let mut ctors : Array Nat := if r.typedArrayCtor != 0 then #[r.typedArrayCtor] else #[]
  for nm in ["RegExp", "Promise", "Map", "Set", "ArrayBuffer"] do
    if let some (.data (.obj c) ..) := (← getObj g).props.get? nm then ctors := ctors.push c
  for c in ctors do
    if ((← getObj c).props.get? (symKey 7)).isNone then
      let gt ← mkNative (.x .speciesGetter) "get [Symbol.species]" 0
      defineOwn c (symKey 7) (.acc gt .undef false true)

/-- SuppressedError and DisposableStack (explicit resource management), for `initRealm`. -/
def initDisposal (g errorProto : Nat) : M Unit := do
  let mk : M Nat := alloc { proto := .obj (← realm).objectProto }
  let supProto ← alloc { proto := .obj errorProto }
  modify fun h => { h with realm := { h.realm with suppressedErrorProto := supProto } }
  let supC ← ctorWith "SuppressedError" (.x .suppressedErrorCtor) 3 supProto
  if let .obj cid := supC then
    if let .obj e0 ← ownValue g "Error" then modifyObj cid fun o => { o with proto := .obj e0 }
  setHidden g "SuppressedError" supC
  setHidden supProto "name" (.str "SuppressedError")
  setHidden supProto "message" (.str "")
  let dsProto ← mk
  modify fun h => { h with realm := { h.realm with disposableStackProto := dsProto } }
  setHidden g "DisposableStack" (← ctorWith "DisposableStack" (.x .disposableStackCtor) 0 dsProto)
  defineOwn dsProto "disposed" (.acc (← mkNative (.x .disposableStackDisposed) "get disposed" 0) .undef false true)
  for (nm, k, l) in [("dispose", 0, 0), ("use", 1, 1), ("adopt", 2, 2), ("defer", 3, 1), ("move", 4, 0)] do
    method dsProto nm (.x (.disposableStackMethod k)) l
  if let some p := (← getObj dsProto).getOwn "dispose" then defineOwn dsProto (symKey symDispose) p
  defineOwn dsProto (symKey symToStringTag) (.data (.str "DisposableStack") false false true)
  let adsProto ← mk
  setHidden dsProto adsKey (.obj adsProto)
  setHidden g "AsyncDisposableStack" (← ctorWith "AsyncDisposableStack" (.x .asyncDisposableStackCtor) 0 adsProto)
  defineOwn adsProto "disposed" (.acc (← mkNative (.x .asyncDsDisposed) "get disposed" 0) .undef false true)
  for (nm, k, l) in [("disposeAsync", 0, 0), ("use", 1, 1), ("adopt", 2, 2), ("defer", 3, 1), ("move", 4, 0)] do
    method adsProto nm (.x (.asyncDsMethod k)) l
  if let some p := (← getObj adsProto).getOwn "disposeAsync" then defineOwn adsProto (symKey 14) p
  defineOwn adsProto (symKey symToStringTag) (.data (.str "AsyncDisposableStack") false false true)

/-- More of the realm, apart so that `initRealm` stays within the elaborator's depth:
Function.prototype[@@hasInstance], Promise.allKeyed and allSettledKeyed, DataView.prototype's accessors, RegExp.prototype.compile,
the HTML methods of String.prototype, the @@toStringTag of Math and JSON, and
Array.prototype[@@unscopables]. -/
def initBuiltinsMore : M Unit := do
  let r ← realm
  let g := r.globalObj
  let pc := r.promiseCtor
  defineOwn r.functionProto (symKey symHasInstance)
    (.data (← mkNative (.x .fnHasInstance) "[Symbol.hasInstance]" 1) false false false)
  method r.arrayProto "toLocaleString" (.x (.arrayToLocaleString false)) 0
  if let .obj tp ← ownValue r.typedArrayCtor "prototype" then
    method tp "toLocaleString" (.x (.arrayToLocaleString true)) 0
  -- Uint8Array base64 and hex (§23.3.2)
  if let .obj u8 ← ownValue g "Uint8Array" then
    method u8 "fromBase64" (.x (.u8Base64 0)) 1
    method u8 "fromHex" (.x (.u8Base64 1)) 1
  if let some u8p := r.typedProtos[1]? then
    method u8p "toBase64" (.x (.u8Base64 2)) 0
    method u8p "toHex" (.x (.u8Base64 3)) 0
    method u8p "setFromBase64" (.x (.u8Base64 4)) 1
    method u8p "setFromHex" (.x (.u8Base64 5)) 1
  method pc "allKeyed" (.x (.promiseKeyed false)) 1
  method pc "allSettledKeyed" (.x (.promiseKeyed true)) 1
  for (nm, w) in [("buffer", 0), ("byteLength", 1), ("byteOffset", 2)] do
    defineOwn r.dataViewProto nm (.acc (← mkNative (.x (.dataViewGetter w)) ("get " ++ nm) 0) .undef false true)
  method r.regexpProto "compile" (.x .regexpCompile) 2
  for i in [0:htmlMethods.size] do
    let (nm, _, attr) := htmlMethods[i]!
    method r.stringProto nm (.x (.stringHtml i)) (if attr.isEmpty then 0 else 1)
  -- @@toStringTag of Math (§21.3.1.9) and JSON (§25.5.3)
  for nm in ["Math", "JSON"] do
    if let .obj o ← ownValue g nm then
      if ((← getObj o).getOwn (symKey symToStringTag)).isNone then
        defineOwn o (symKey symToStringTag) (.data (.str nm) false false true)
  -- Array.prototype[@@unscopables] (§23.1.3.41): a null-prototype object of the names
  let unscop ← alloc { proto := .null }
  for nm in ["at", "copyWithin", "entries", "fill", "find", "findIndex", "findLast", "findLastIndex",
      "flat", "flatMap", "includes", "keys", "toReversed", "toSorted", "toSpliced", "values"] do
    defineOwn unscop nm (.data (.bool true) true true true)
  defineOwn r.arrayProto (symKey 5) (.data (.obj unscop) false false true)

def initRealm : M Unit := do
  let objectProto ← alloc {}
  let functionProto ← alloc { proto := .obj objectProto, kind := .native .functionProto }
  tagFn functionProto
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
  if let .obj ac := arrayC then
    let g ← mkNative (.x .speciesGetter) "get [Symbol.species]" 0
    defineOwn ac (symKey 7) (.acc g .undef false true)
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
  if let .obj e0 ← ownValue g "Error" then method e0 "isError" (.x .errorIsError) 1
  initDisposal g errorProto
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
  defineOwn math "LOG2E" (.data (.num 1.4426950408889634) false false false)
  defineOwn math "LOG10E" (.data (.num 0.4342944819032518) false false false)
  defineOwn math "SQRT1_2" (.data (.num 0.7071067811865476) false false false)
  defineOwn math "SQRT2" (.data (.num 1.4142135623730951) false false false)
  -- Map, Set, WeakMap, WeakSet
  for (k, nm) in [(0, "Map"), (1, "Set"), (2, "WeakMap"), (3, "WeakSet")] do
    let p ← mk
    setHidden g nm (← ctorWith nm (.mapCtor k) 0 p)
    defineOwn p (symKey symToStringTag) (.data (.str nm) false false true)
    let isMap := k == 0 || k == 2
    if isMap then
      method p "get" (.x (.collMethod k 0)) 1
      method p "set" (.x (.collMethod k 1)) 2
      method p "getOrInsert" (.x (.mapUpsert false (k == 2))) 2
      method p "getOrInsertComputed" (.x (.mapUpsert true (k == 2))) 2
    else method p "add" (.x (.collMethod k 7)) 1
    if k == 1 then
      for (nm, j) in [("union", 0), ("intersection", 1), ("difference", 2), ("symmetricDifference", 3),
          ("isSubsetOf", 4), ("isSupersetOf", 5), ("isDisjointFrom", 6)] do
        method p nm ((.x (.setMethod j))) 1
    method p "has" (.x (.collMethod k 2)) 1
    method p "delete" (.x (.collMethod k 3)) 1
    if k < 2 then
      method p "clear" (.x (.collMethod k 4)) 0
      method p "forEach" (.x (.collMethod k 6)) 1
      defineOwn p "size" (.acc (← mkNative (.x (.collMethod k 5)) "get size" 0) .undef false true)
      let entries ← mkNative (.x (.collMethod k 8)) "entries" 0
      let values ← mkNative (.x (.collMethod k 10)) "values" 0
      setHidden p "entries" entries
      setHidden p "values" values
      if isMap then
        method p "keys" (.x (.collMethod k 9)) 0
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
  method stringProto "normalize" (.x .stringNormalize) 0
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
  setHidden iterProto (symKey symDispose) (← mkNative (.x .iteratorDispose) "[Symbol.dispose]" 0)
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
    method ac "fromAsync" (.x .arrayFromAsync) 1
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
  initFunctionKinds g genProto asyncGenProto
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
    method pc "try" (.x .promiseTry) 1
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
  let regexpC ← ctorWith "RegExp" .regexpCtor 2 regexpProto
  setHidden g "RegExp" regexpC
  if let .obj rc := regexpC then method rc "escape" (.x .regexpEscape) 1
  method regexpProto "exec" .regexpExec 1
  method regexpProto "test" .regexpTest 1
  method regexpProto "toString" .regexpToString 0
  for (k, sym, nm, l) in [(0, 8, "[Symbol.match]", 1), (1, 10, "[Symbol.replace]", 2),
      (2, 11, "[Symbol.search]", 1), (3, 12, "[Symbol.split]", 2), (4, 9, "[Symbol.matchAll]", 1)] do
    defineOwn regexpProto (symKey sym) (.data (← mkNative (.x (.regexpSym k)) nm l) true false true)
  let rsip ← alloc { proto := .obj (← realm).iterProto }
  defineOwn rsip "next" (.data (← mkNative .iterNext "next" 0) true false true)
  defineOwn rsip (symKey symToStringTag) (.data (.str "RegExp String Iterator") false false true)
  defineOwn regexpProto rsiProtoKey (.data (.obj rsip) false false false)
  for (nm, k) in [("source", 0), ("flags", 1), ("global", 2), ("ignoreCase", 3), ("multiline", 4),
      ("sticky", 5), ("unicode", 6), ("dotAll", 7), ("hasIndices", 8), ("unicodeSets", 9)] do
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
  -- %TypedArray%.prototype.toString is the function object Array.prototype.toString (§23.2.3.32),
  -- so a typed array converts to a string or a number through its elements (join)
  if let some p := (← getObj ap).getOwn "toString" then defineOwn typedProto "toString" p
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
    method ic "zip" (.x (.iteratorZip false)) 1
    method ic "zipKeyed" (.x (.iteratorZip true)) 1
  setHidden g "Iterator" iterC
  setHidden ip "constructor" iterC
  for (nm, k) in [("map", 0), ("filter", 1), ("take", 2), ("drop", 3), ("flatMap", 4), ("chunks", 8), ("windows", 9)] do
    method ip nm ((.x (.iterLazy k))) 1
  for (nm, k, l) in [("reduce", 0, 1), ("toArray", 1, 0), ("forEach", 2, 1), ("some", 3, 1), ("every", 4, 1), ("find", 5, 1),
      ("includes", 6, 1), ("join", 7, 1)] do
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
  initSpecies
  initBuiltinsMore

/-- A fresh realm. -/
def freshHeapOf (host : Option H) (hostCall : H → Nat → Array HostArg → Nat → H × HostAns) : HeapOf H :=
  match (initRealm : M Unit).run { host, hostCall } with
  | .ok _ h => h
  | .error _ h => h

/-- Make another realm in this heap (InitializeHostDefinedRealm, §9.6): its own intrinsics
and an empty global environment record, made by `initRealm` while it runs; then the realm
that ran before runs again. The answer is the new realm's number. A host calls this; no
script can. -/
def addRealm (h : HeapOf H) : Nat × HeapOf H :=
  let h := if h.realms.isEmpty then { h with realms := #[{}], curRealm := 0 } else h
  let back := h.curRealm
  let k := h.realms.size
  let saved : SavedRealm := { (h.realms.getD back {}) with realm := h.realm, env0 := h.envs[0]! }
  let envs := h.envs
  let h := { h with envs := #[] }
  let (h, envs) := h.noteEnv envs 0
  let h := { h with realms := (h.realms.set! back saved).push {}, realm := {},
                    envs := envs.set! 0 {}, curRealm := k }
  let h := match (initRealm : M Unit).run h with | .ok _ h => h | .error _ h => h
  match (switchRealm back : M Unit).run h with
  | .ok _ h => (k, h)
  | .error _ h => (k, h)

/-- Run `f` on the heap with realm `k` running, then switch back to the realm that ran. -/
def inRealmH {α : Type} (h : HeapOf H) (k : Nat) (f : HeapOf H → α × HeapOf H) : α × HeapOf H :=
  let back := h.curRealm
  let h := match (switchRealm k : M Unit).run h with | .ok _ h => h | .error _ h => h
  let (a, h) := f h
  let h := match (switchRealm back : M Unit).run h with | .ok _ h => h | .error _ h => h
  (a, h)

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
def runScriptM [Mode] (s : Script) (checkpoint : Bool := true) : M Unit := do
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

def runScript [Mode] (h : HeapOf H) (src : String) (strict : Bool := false) : Outcome × HeapOf H :=
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
def evalScript [Mode] (h : HeapOf H) (src : String) : Outcome × HeapOf H :=
  match (parseScript src false).map Resolve.script with
  | .error e => (.syntaxError e, h)
  | .ok s =>
    match (runScriptM s false : M Unit).run h with
    | .ok _ h' => (.ok, h')
    | .error (.throw v) h' => (.threw v (describeThrown h' v), h')
    | .error (.halt w) h' => (.halted w, h')

/-- Call a function value; the outcome and the value it returned. -/
def callFunction [Mode] (h : HeapOf H) (f thisV : Value) (args : Array Value) : (Outcome × Value) × HeapOf H :=
  match (callV defaultFuel f thisV args : M Value).run h with
  | .ok v h' => ((.ok, v), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), .undef), h')
  | .error (.halt w) h' => ((.halted w, .undef), h')

/-- `o[name](...args)`. -/
def callMethod [Mode] (h : HeapOf H) (o : Value) (name : String) (args : Array Value) : (Outcome × Value) × HeapOf H :=
  match (do let f ← getV defaultFuel o name; callV defaultFuel f o args : M Value).run h with
  | .ok v h' => ((.ok, v), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), .undef), h')
  | .error (.halt w) h' => ((.halted w, .undef), h')

/-- The completion value of a script (an indirect `eval`, §19.2.1.1). -/
def evalValue [Mode] (h : HeapOf H) (src : String) : (Outcome × Value) × HeapOf H :=
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
def checkpoint [Mode] (h : HeapOf H) : (Outcome × Nat) × HeapOf H :=
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
