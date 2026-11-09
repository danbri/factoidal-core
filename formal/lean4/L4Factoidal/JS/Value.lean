import Std.Data.HashMap
import L4Factoidal.JS.Syntax
import L4Factoidal.JS.Number
import L4Factoidal.JS.Regex

/-!
# L4Factoidal.JS.Value — values, objects, environments, the heap (§6, §9, §10)

- `Value` is the ECMAScript language type (§6.1) without Symbol and BigInt.
  An object is a number: its index in the heap's object arena.
- `Obj` is an ordinary object (§10.1): own properties in a hash map plus their
  insertion order (OrdinaryOwnPropertyKeys, §10.1.11, gives integer keys first;
  `ownKeys` does that), a prototype, `[[Extensible]]`, and what kind of exotic or
  built-in object it is (`Kind`). An Array (§10.4.2) keeps its elements in an
  `Array Value`; `length` is the element count.
- `Env` is a declarative Environment Record (§9.1.1.1): bindings with their
  mutability and initialisation state (the temporal dead zone). Closures hold the
  number of their environment, so a write through a closure is seen by every
  other closure of the same environment (the case that failed in the VerifiedJS
  Core semantics, https://github.com/danbri/factoidal/issues/1252).
- The heap is an arena with no collector yet. The design record gives the plan
  (mark and compact between tasks of the event loop).
-/

namespace L4Factoidal.JS

variable {H : Type}

inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (n : Float)
  | str (s : String)
  | obj (id : Nat)
  /-- A Symbol (§6.1.5): its number in `Heap.syms`. -/
  | sym (id : Nat)
  /-- A BigInt (§6.1.6.2). -/
  | big (i : Int)
  deriving Inhabited

/-- A property: data (value, writable, enumerable, configurable) or accessor. -/
inductive PropV where
  | data (v : Value) (w e c : Bool)
  | acc (get set : Value) (e c : Bool)
  deriving Inhabited

def PropV.enumerable : PropV → Bool
  | .data _ _ e _ => e
  | .acc _ _ e _ => e

def PropV.configurable : PropV → Bool
  | .data _ _ _ c => c
  | .acc _ _ _ c => c

/-- The built-in functions (§19 to §28 for the subset). -/
inductive Native where
  | print | isNaN | isFinite | parseInt | parseFloat
  | objectCtor | objectKeys | objectGetPrototypeOf | objectCreate | objectDefineProperty
  | objectGetOwnPropertyNames | objectIs | objectFreeze | objectIsFrozen | objectSetPrototypeOf
  | objectGetOwnPropertyDescriptor | objectPreventExtensions | objectIsExtensible
  | objectProtoHasOwnProperty | objectProtoToString | objectProtoValueOf
  | objectProtoIsPrototypeOf | objectProtoPropertyIsEnumerable | objectProtoToLocaleString
  | functionCtor | functionProtoCall | functionProtoApply | functionProtoBind
  | functionProtoToString | functionProto
  | arrayCtor | arrayIsArray | arrayPush | arrayPop | arrayShift | arrayUnshift | arraySlice
  | arraySplice | arrayJoin | arrayToString | arrayIndexOf | arrayLastIndexOf | arrayMap
  | arrayForEach | arrayFilter | arrayReduce | arrayConcat | arrayReverse | arraySort
  | arraySome | arrayEvery | arrayIncludes | arrayFind | arrayFindIndex | arrayFill
  | stringCtor | stringFromCharCode | stringCharAt | stringCharCodeAt | stringIndexOf
  | stringLastIndexOf | stringSlice | stringSubstring | stringSubstr | stringToUpperCase
  | stringToLowerCase | stringTrim | stringSplit | stringConcat | stringToString
  | stringIncludes | stringStartsWith | stringEndsWith | stringRepeat
  | numberCtor | numberToString | numberValueOf | numberToFixed | numberIsInteger
  | booleanCtor | booleanToString | booleanValueOf
  | errorCtor (kind : Nat) | errorToString
  | mathFloor | mathCeil | mathAbs | mathMax | mathMin | mathPow | mathSqrt | mathRound
  | mathRandom | mathSin | mathCos | mathTan | mathAtan | mathAtan2 | mathLog | mathExp
  | mathTrunc | mathSign
  | jsonStringify
  | throwTypeError
  | eval | symbolCtor | symbolToString | symbolDescription | symbolValueOf
  | objectGetOwnPropertySymbols | objectAssign | objectEntries | objectValues
  | arrayValues | arrayKeys | arrayEntries | arrayFrom | arrayOf | stringIterator
  | iterNext | iterSelf | dateNow
  | functionHasInstance
  | genNext | genReturn | genThrow
  | bigintCtor | bigintToString | bigintValueOf
  /-- `BigInt.asIntN` (signed) and `BigInt.asUintN` (§21.2.2.1, §21.2.2.2). -/
  | bigintAsN (signed : Bool)
  | promiseCtor | promiseThen | promiseCatch | promiseFinally | promiseResolveStatic
  | promiseRejectStatic | promiseAll | promiseResolveFn | promiseRejectFn | promiseReactionJob
  | promiseThenableJob | promiseAllElement | promiseFinallyF | promiseFinallyR | promiseValueThunk
  | promiseThrower | asyncResume
  | agenNext | agenReturn | agenThrow | agenResume
  | mapCtor (kind : Nat) | mapGet | mapSet | mapHas | mapDelete | mapClear | mapSize | mapForEach
  | mapIter (mode : Nat) | setAdd
  | reflect (op : Nat)
  | objectDefineProperties | objectSeal | objectIsSealed | objectGetOwnPropertyDescriptors
  | objectFromEntries
  | arrayFlat | arrayFlatMap | arrayAt | arrayFindLast | arrayFindLastIndex
  | stringPadStart | stringPadEnd | stringAt | stringCodePointAt | stringTrimStart | stringTrimEnd
  | stringReplace | stringReplaceAll | stringFromCodePoint
  | numberIsFinite | numberIsNaN | numberIsSafeInteger
  | math1 (op : Nat) | mathHypot | mathImul | mathClz32
  /-- RegExp (§22.2) and the String methods that take one. -/
  | regexpCtor | regexpExec | regexpTest | regexpToString | regexpGetter (which : Nat)
  | stringMatch | stringMatchAll | stringSearch
  /-- Proxy (§28.2). -/
  | proxyCtor
  /-- JSON.parse (§25.5.1), without a reviver. -/
  | jsonParse
  /-- ArrayBuffer (§25.1) and the typed arrays (§23.2): `ty` numbers the element type
  (`typedNames`). -/
  | bufferCtor | bufferSlice | bufferIsView
  | typedCtor (ty : Nat) | typedSet | typedSubarray | typedFill
  /-- DataView (§25.3): the constructor, and `get`/`set` of element type `ty` (the
  `typedNames` numbering, then 9 BigInt64 and 10 BigUint64). -/
  | dataViewCtor | dataViewGet (ty : Nat) | dataViewSet (ty : Nat)
  /-- `Date` as a constructor and `Date.prototype.getTime` (the host's clock). -/
  | dateCtor | dateGetTime
  /-- `performance.now()`: the host's clock in ms. -/
  | perfNow
  /-- A native of the embedding host: `HeapOf.hostCall` with this number. -/
  | host (k : Nat)
  deriving BEq, Repr, Inhabited

/-- What a running function sees. -/
structure Ctx where
  env : Nat
  thisV : Value
  strict : Bool
  newTarget : Value := .undef
  /-- `[[HomeObject]]` of the running method, for `super`. -/
  home : Value := .undef
  /-- The running function object (a class constructor's fields). -/
  fnObj : Value := .undef
  deriving Inhabited

inductive BindMode where
  /-- Initialise in this environment (let, const, parameters, catch). -/
  | declare (env : Nat) (mutable : Bool)
  /-- PutValue to a name already declared (var). -/
  | var
  /-- An assignment pattern (§13.15.5). -/
  | assign
  deriving Inhabited

/-- Completions while unwinding a generator's frames. -/
inductive GCompl where
  | ret (v : Value)
  | throw (v : Value)
  | brk (l : Option String)
  | cont (l : Option String)

/-- A suspended generator's control state (§27.5): the stack of what is left to
run, top first. The body runs on this machine only around a `yield`; code with
no `yield` runs in the ordinary evaluator. -/
inductive GFrame where
  /-- The rest of a statement list. -/
  | block (ctx : Ctx) (ss : List Stmt)
  /-- A `while` loop: test, then the body. -/
  | loopW (ctx : Ctx) (labels : List String) (c : Expr) (body : Stmt)
  /-- A `do`-`while` loop after its body: test, then the body again. -/
  | loopDo (ctx : Ctx) (labels : List String) (body : Stmt) (c : Expr)
  /-- A `for` loop: update (unless first), test, then the body. -/
  | loopFor (ctx : Ctx) (labels : List String) (perIter : List String) (test update : Option Expr)
      (body : Stmt) (first : Bool)
  /-- A `for`-`of` loop over an iterator. -/
  | loopOf (ctx : Ctx) (labels : List String) (kind : Option DeclKind) (target : Pat) (it : Value)
      (body : Stmt)
  /-- A `try` statement; `phase` 0 in the block, 1 in the handler. -/
  | tryF (ctx : Ctx) (param : Option Pat) (handler : Option (List Stmt)) (fin : Option (List Stmt))
      (phase : Nat)
  /-- A completion that waits for a `finally` block to end normally. -/
  | pending (c : GCompl)
  /-- Where the value sent by `next(v)` goes: a pattern, or nowhere. -/
  | resume (ctx : Ctx) (target : Option (Pat × BindMode))
  /-- `yield*`: the inner iterator. -/
  | delegate (ctx : Ctx) (it : Value) (target : Option (Pat × BindMode))


/-- What the caller of a generator sends (§27.5.3.3, §27.5.3.4). -/
inductive GInput where
  | send (v : Value)
  | throwV (v : Value)
  | retV (v : Value)

/-- What a generator step ends with. -/
inductive GOut where
  | yielded (v : Value) (frames : List GFrame)
  /-- An `await` in an async generator. -/
  | awaited (v : Value) (frames : List GFrame)
  | done (v : Value)

/-- A key of a Map or Set under SameValueZero (§7.2.11): `+0` and `-0` are one key,
every NaN is one key. Hashed, so a lookup does not scan the entries. -/
inductive VKey where
  | undef | null
  | bool (b : Bool)
  | num (bits : UInt64)
  | str (s : String)
  | obj (id : Nat)
  | sym (id : Nat)
  | big (i : Int)
  deriving BEq, Hashable, Inhabited

def VKey.of : Value → VKey
  | .undef => .undef
  | .null => .null
  | .bool b => .bool b
  | .num x => .num (if x == 0 then (0 : Float).toBits else if x.isNaN then 0x7FF8000000000000 else x.toBits)
  | .str s => .str s
  | .obj i => .obj i
  | .sym i => .sym i
  | .big i => .big i

/-- The typed array element types: name, bytes per element. -/
def typedNames : Array (String × Nat) :=
  #[("Int8Array", 1), ("Uint8Array", 1), ("Uint8ClampedArray", 1), ("Int16Array", 2), ("Uint16Array", 2),
    ("Int32Array", 4), ("Uint32Array", 4), ("Float32Array", 4), ("Float64Array", 8)]

inductive Kind where
  | ordinary
  | array (elems : Array Value)
  /-- A function object (§10.2) and the environment it closes over. An arrow
  function captured `thisV` and `newTarget`; `home` is `[[HomeObject]]` (a
  method's object, for `super`); `fields` are a class constructor's instance
  fields (§15.7.10: name and initialiser). -/
  | closure (f : FunDef) (env : Nat) (thisV newTarget home : Value)
      (fields : Array (String × Value))
  /-- An Array or String Iterator (§23.1.5, §22.1.5): the iterated object
  (`undefined` once done), the next index, and the kind (0 values, 1 keys,
  2 entries, 3 string code points). -/
  | iter (target : Value) (idx : Nat) (mode : Nat)
  /-- A generator object (§27.5): its frames and state (0 suspended at the start,
  1 suspended at a yield, 2 running, 3 completed). -/
  | gen (frames : List GFrame) (state : Nat)
  /-- A Map, Set, WeakMap or WeakSet (§24): entries in insertion order; a deleted
  entry is `none` so that live iterators keep their place (§24.1.3.5). `kind`: 0 Map,
  1 Set, 2 WeakMap, 3 WeakSet. -/
  | coll (kind : Nat) (entries : Array (Option (Value × Value))) (index : Std.HashMap VKey Nat)
  /-- A Promise (§27.2.6): state (0 pending, 1 fulfilled, 2 rejected), result,
  reactions (on fulfilled, on rejected, derived promise or `undefined`), and whether
  a resolving function has been called (`[[AlreadyResolved]]`, kept per promise). -/
  | promise (state : Nat) (result : Value) (reactions : Array (Value × Value × Value)) (locked : Bool)
  /-- A running async function (§27.7): its frames and the promise it returns. -/
  | coro (frames : List GFrame) (promise : Nat)
  /-- An async generator (§27.6): frames, state (0 start, 1 suspended at a yield,
  2 running or awaiting, 3 completed) and the queue of requests with their promises. -/
  | agen (frames : List GFrame) (state : Nat) (queue : Array (GInput × Nat))
  | native (id : Native)
  | bound (target thisV : Value) (args : Array Value)
  /-- A RegExp object (§22.2.6): the compiled pattern, its source and flags. -/
  | regexp (re : Re.Compiled) (source flags : String)
  /-- A Proxy exotic object (§10.5): its target and handler (`null` once revoked). -/
  | proxy (target handler : Value)
  /-- An ArrayBuffer (§25.1): its bytes. -/
  | buffer (bytes : ByteArray)
  /-- A typed array (§10.4.5): the element type (`typedNames`), the ArrayBuffer object,
  the byte offset and the element count. -/
  | typed (ty : Nat) (buf : Nat) (off len : Nat)
  /-- A DataView (§25.3): the ArrayBuffer object, the byte offset and the byte length. -/
  | dataView (buf : Nat) (off len : Nat)
  /-- A Boolean, Number or String object (`[[BooleanData]]` etc.). -/
  | prim (v : Value)
  | error
  | args
  deriving Inhabited

structure Obj where
  props : Std.HashMap String PropV := {}
  keys : Array String := #[]
  proto : Value := .null
  kind : Kind := .ordinary
  extensible : Bool := true
  deriving Inhabited

structure Binding where
  v : Value
  mutable : Bool := true
  init : Bool := true
  deriving Inhabited

structure Env where
  vars : Std.HashMap String Binding := {}
  parent : Option Nat := none
  /-- The binding object of an Object Environment Record (§9.1.1.2, `with`). -/
  withObj : Option Nat := none
  deriving Inhabited

/-- The intrinsics of the realm (§9.3). -/
structure Realm where
  globalObj : Nat := 0
  objectProto : Nat := 0
  functionProto : Nat := 0
  arrayProto : Nat := 0
  stringProto : Nat := 0
  numberProto : Nat := 0
  booleanProto : Nat := 0
  /-- Error, EvalError, RangeError, ReferenceError, SyntaxError, TypeError, URIError. -/
  errorProtos : Array Nat := #[]
  throwTypeError : Nat := 0
  symbolProto : Nat := 0
  iterProto : Nat := 0
  arrayIterProto : Nat := 0
  evalFn : Nat := 0
  generatorProto : Nat := 0
  bigintProto : Nat := 0
  promiseProto : Nat := 0
  promiseCtor : Nat := 0
  asyncGenProto : Nat := 0
  regexpProto : Nat := 0
  bufferProto : Nat := 0
  /-- The prototype of each typed array type (`typedNames`). -/
  typedProtos : Array Nat := #[]
  dataViewProto : Nat := 0
  dateProto : Nat := 0
  deriving Inhabited

/-- The error constructors, by their index in `Realm.errorProtos`. -/
def errorNames : Array String :=
  #["Error", "EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError", "URIError"]

inductive ErrKind where
  | error | eval | range | reference | syntax | type | uri
  deriving BEq, Repr, Inhabited

def ErrKind.idx : ErrKind → Nat
  | .error => 0 | .eval => 1 | .range => 2 | .reference => 3 | .syntax => 4 | .type => 5 | .uri => 6

/-- The well-known symbols (§6.1.5.1), numbered by their place here. -/
def wellKnown : Array String :=
  #["iterator", "asyncIterator", "hasInstance", "toPrimitive", "toStringTag", "unscopables",
    "isConcatSpreadable", "species", "match", "matchAll", "replace", "search", "split"]

def symIterator : Nat := 0
def symHasInstance : Nat := 2
def symToPrimitive : Nat := 3
def symToStringTag : Nat := 4

/-- The property key of a Symbol: a string that starts with U+10FFFF. Source text
can make such a string (`"\u{10FFFF}0"`), and it would then name the same
property as the Symbol: a known limit of this encoding (record, section 5). -/
def symMark : Char := Char.ofNat 0x10FFFF
def symKey (id : Nat) : String := String.singleton symMark ++ toString id
def isSymKey (k : String) : Bool := k.front == symMark
def symOfKey? (k : String) : Option Nat :=
  if isSymKey k then (k.drop 1).toString.toNat? else none

/-- A host's answer to a call of one of its natives (`Native.host`): a value, a list of
integers (made an Array), or a `TypeError` with this message. -/
inductive HostAns where
  | val (v : Value)
  | ints (xs : Array Int)
  /-- A new ArrayBuffer with these bytes. -/
  | bytes (b : ByteArray)
  | err (msg : String)
  /-- Write into the ArrayBuffer that was argument `arg` (offset, bytes; a write that does
  not fit is skipped), then answer `ans`. -/
  | writes (arg : Nat) (ws : Array (Nat × ByteArray)) (ans : HostAns)
  /-- Detach the ArrayBuffer that was argument `arg` (§25.1.3.5 DetachArrayBuffer: its
  bytes become empty and its `byteLength` 0); answers `undefined`. -/
  | detach (arg : Nat)
  deriving Inhabited

/-- An argument of a host's native: a value, or the bytes of an ArrayBuffer or of a typed
array's view. -/
inductive HostArg where
  | val (v : Value)
  | bytes (b : ByteArray)
  deriving Inhabited

/-- The heap, with the state `H` of the host that embeds the engine. A page host keeps
its DOM arena and event loop here (`WasmVM.Hosts.LeanJS`), so a native of the page
(`Native.host k`) reads and changes them at the call; the engine itself never looks
inside `H`. `Heap` is the heap with no host. -/
structure HeapOf (H : Type) where
  objs : Array Obj := #[]
  envs : Array Env := #[{}]
  out : Array String := #[]
  /-- Steps left before the script is stopped (an interrupt, not an exception). -/
  steps : Nat := 1000000000
  depth : Nat := 0
  maxDepth : Nat := 400
  rng : UInt64 := 0x2545F4914F6CDD1D
  /-- The job queue (§9.5 HostEnqueuePromiseJob): a function and its arguments.
  In a page these are the microtasks of the Lean event loop (record, section 6). -/
  jobs : Array (Value × Array Value) := #[]
  jobHead : Nat := 0
  /-- Jobs run in total (a host counts its microtasks with it). -/
  jobsRun : Nat := 0
  realm : Realm := {}
  /-- The description of each Symbol; the well-known ones first (`wellKnown`). -/
  syms : Array String := wellKnown.map ("Symbol." ++ ·)
  /-- The host's state; `none` while one of its natives runs (taken out, so the host
  changes it in place). -/
  host : Option H := none
  /-- The host's natives: `hostCall state k args steps`, with the steps left in the
  budget (`steps`), so a host can tell how far the script has run. -/
  hostCall : H → Nat → Array HostArg → Nat → H × HostAns := fun h _ _ _ => (h, .val .undef)

instance : Inhabited (HeapOf H) := ⟨{}⟩

abbrev Heap := HeapOf Unit

/-- Why evaluation stopped early: a thrown value, or the host stopped it. -/
inductive Abrupt where
  | throw (v : Value)
  | halt (why : String)
  deriving Inhabited

abbrev JSM (H : Type) := EStateM Abrupt (HeapOf H)

/-- Statement completions (§6.2.4) other than throw. -/
inductive Compl where
  | normal
  | ret (v : Value)
  | brk (label : Option String)
  | cont (label : Option String)
  deriving Inhabited


/-! ## Pure operations -/

def typeOfKind : Kind → String
  | .closure .. | .native _ | .bound .. => "function"
  | _ => "object"

def Kind.callable : Kind → Bool
  | .closure .. | .native _ | .bound .. => true
  | _ => false

/-- IsStrictlyEqual (§7.2.15). -/
def strictEq : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .obj a, .obj b => a == b
  | .sym a, .sym b => a == b
  | .big a, .big b => a == b
  | _, _ => false

/-- SameValue (§7.2.10): NaN is NaN, +0 is not -0. -/
def sameValue : Value → Value → Bool
  | .num a, .num b => (a.isNaN && b.isNaN) || (a == b && isNegZero a == isNegZero b)
  | a, b => strictEq a b

/-- SameValueZero (§7.2.11). -/
def sameValueZero : Value → Value → Bool
  | .num a, .num b => (a.isNaN && b.isNaN) || a == b
  | a, b => strictEq a b

def Value.isObj : Value → Bool
  | .obj _ => true
  | _ => false

/-- ToBoolean (§7.1.2). -/
def toBool : Value → Bool
  | .undef | .null => false
  | .bool b => b
  | .num n => !(n == 0 || n.isNaN)
  | .str s => !s.isEmpty
  | .obj _ => true
  | .sym _ => true
  | .big i => i != 0

def HeapOf.obj (h : HeapOf H) (id : Nat) : Obj := h.objs.getD id default

/-- An own property, with the Array exotic `length` and index properties. -/
def Obj.getOwn (o : Obj) (key : String) : Option PropV :=
  match o.kind with
  | .array es =>
    if key == "length" then some (.data (.num (Float.ofNat es.size)) true false false)
    else match arrayIndex? key with
      | some i => if h : i < es.size then some (.data es[i] true true true) else o.props.get? key
      | none => o.props.get? key
  | .prim (.str s) =>
    if key == "length" then some (.data (.num (Float.ofNat (utf16Length s))) false false false)
    else match arrayIndex? key with
      | some i => match s.toList[i]? with
        | some c => some (.data (.str (String.singleton c)) false true false)
        | none => o.props.get? key
      | none => o.props.get? key
  | _ => o.props.get? key

/-- The own keys in order (§10.1.11): array indices, then the rest by insertion. -/
def Obj.ownKeys (o : Obj) : Array String :=
  let idx := match o.kind with
    | .array es => (List.range es.size).toArray.map toString
    | .prim (.str s) => (List.range s.length).toArray.map toString
    | _ => #[]
  let ks := o.keys.filter fun k => o.props.contains k && !isPrivKey k
  let (ints, rest) := ks.partition fun k => (arrayIndex? k).isSome
  let ints := (ints.toList.mergeSort fun a b => (arrayIndex? a).getD 0 ≤ (arrayIndex? b).getD 0).toArray
  let extra := match o.kind with
    | .array _ => #["length"]
    | .prim (.str _) => #["length"]
    | _ => #[]
  let (syms, strs) := rest.partition isSymKey
  idx ++ ints ++ extra ++ strs ++ syms

/-- The own string keys (no Symbols), in order. -/
def Obj.ownStrKeys (o : Obj) : Array String := o.ownKeys.filter (!isSymKey ·)

/-- Find a property on the prototype chain (`fuel` bounds the chain). -/
def HeapOf.findProp (h : HeapOf H) (id : Nat) (key : String) : Nat → Option PropV
  | 0 => none
  | fuel + 1 =>
    let o := h.obj id
    match o.getOwn key with
    | some p => some p
    | none => match o.proto with
      | .obj p => h.findProp p key fuel
      | _ => none

/-- `@@unscopables` of a `with` object names `name` with a true data value. -/
def HeapOf.unscopable (h : HeapOf H) (o : Nat) (name : String) : Bool :=
  match h.findProp o (String.singleton (Char.ofNat 0x10FFFF) ++ "5") 1000 with
  | some (.data (.obj u) ..) =>
    match h.findProp u name 1000 with
    | some (.data v ..) => toBool v
    | _ => false
  | _ => false

/-- The binding of a name: the number of the environment that holds it. -/
def HeapOf.findEnv (h : HeapOf H) (name : String) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _, none => none
  | fuel + 1, some e =>
    let env := h.envs.getD e default
    if env.vars.contains name then some e
    else match env.withObj with
      | some o =>
        if (h.findProp o name 1000).isSome && !h.unscopable o name then some e
        else h.findEnv name fuel env.parent
      | none => h.findEnv name fuel env.parent

end L4Factoidal.JS
