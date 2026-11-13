import Std.Data.HashMap
import Std.Data.HashSet
import L4Factoidal.JS.Syntax
import L4Factoidal.JS.Number
import L4Factoidal.JS.Regex
import L4Factoidal.JS.Str
import L4Factoidal.JS.PropMap

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

/-- The built-ins added on 2026-11-09 (`Native.x`). -/
inductive NativeX where
  /-- ArrayBuffer (§25.1.6) accessors: 0 `byteLength`, 1 `maxByteLength`, 2 `resizable`,
  3 `detached`; `resize`; `transfer` and `transferToFixedLength`. -/
  | bufferGetter (which : Nat) | bufferResize | bufferTransfer (fixed : Bool)
  /-- SharedArrayBuffer (§25.2): the constructor, 0 `byteLength`, 1 `maxByteLength`,
  2 `growable`; `grow`; `slice`. -/
  | sharedCtor | sharedGetter (which : Nat) | sharedGrow | sharedSlice
  /-- %TypedArray% (§23.2.1): the constructor (which throws), `from`, `of`, the accessors
  (0 `buffer`, 1 `byteLength`, 2 `byteOffset`, 3 `length`, 4 `@@toStringTag`) and the
  methods that answer a typed array or work on its bytes (`typedMethods`). -/
  | typedArrayCtor | typedFrom | typedOf | typedGetter (which : Nat) | typedMethod (which : Nat)
  /-- Atomics (§25.4) on integer typed arrays, without waiting (`atomicsOps`). -/
  | atomics (op : Nat)
  /-- `String.prototype.isWellFormed` and `toWellFormed` (§22.1.3.10, §22.1.3.32). -/
  | stringIsWellFormed | stringToWellFormed
  /-- Date.prototype methods (§21.4.4, `dateMethodNames`), `Date.UTC`, `Date.parse`. -/
  | dateMethod (k : Nat) | dateUTC | dateParse
  /-- Iterator (§27.1.3): the constructor, `Iterator.from`, the lazy methods that make an
  iterator helper (0 `map`, 1 `filter`, 2 `take`, 3 `drop`, 4 `flatMap`), the eager ones
  (0 `reduce`, 1 `toArray`, 2 `forEach`, 3 `some`, 4 `every`, 5 `find`), and `next` and
  `return` of a helper (and of the wrapper of `Iterator.from`). -/
  | iteratorCtor | iteratorFrom | iterLazy (k : Nat) | iterEager (k : Nat) | helperNext | helperReturn
  /-- `Promise.race` (0) and `Promise.allSettled` (1) (§27.2.4.5, §27.2.4.2), and the
  function that records one settled element of `allSettled` (0 fulfilled, 1 rejected). -/
  | promiseCombinator (k : Nat) | promiseSettleElement (rejected : Nat)
  /-- `Number.prototype.toExponential` and `toPrecision` (§21.1.3.2, §21.1.3.5). -/
  | numberToExponential | numberToPrecision
  /-- The Set methods of ES2025 (§24.2.4: 0 `union`, 1 `intersection`, 2 `difference`,
  3 `symmetricDifference`, 4 `isSubsetOf`, 5 `isSupersetOf`, 6 `isDisjointFrom`), and
  `Proxy.revocable` with its revoke function (§28.2.2.1). -/
  | setMethod (k : Nat) | proxyRevocable | proxyRevoke
  /-- Array.prototype methods (§23.1.3): 0 `copyWithin`, 1 `reduceRight`, 2 `toReversed`,
  3 `toSorted`, 4 `toSpliced`, 5 `with`. -/
  | arrayMethod (k : Nat)
  /-- `Object.hasOwn` (§20.1.2.13), `Object.groupBy` and `Map.groupBy` (§20.1.2.12,
  §24.1.2.1; `true` for Map), `String.prototype.localeCompare` (§22.1.3.12, code unit order:
  there is no Intl here). -/
  | objectHasOwn | groupBy (map : Bool) | stringLocaleCompare
  /-- AggregateError (§20.5.7), `Promise.any` (§27.2.4.3) and the function that records one
  rejected element of it. -/
  | aggregateErrorCtor | promiseAny | promiseAnyReject
  /-- StructuredSerializeWithTransfer and StructuredDeserialize (HTML §2.7, `JS.Clone`): a
  host's `n.serialize(value, transfer)` (an ArrayBuffer of bytes) and `n.deserialize(buffer)`,
  for messages between the realms of a page and its dedicated workers. -/
  | cloneSerialize | cloneDeserialize
  /-- `n.runScript(source)`: run a classic script in the realm's global scope (the steps of
  `runScriptM`), for `importScripts` (HTML §10.3.4.2 "import scripts into worker global
  scope"); its exceptions reach the caller. -/
  | classicScript
  /-- `get Error.prototype.stack` (`false`) and `set Error.prototype.stack` (`true`): the
  accessor of the Error Stack Accessor proposal (test262 feature `error-stack-accessor`). -/
  | errorStack (setter : Bool)
  deriving BEq, Repr, Inhabited

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
  /-- encodeURIComponent, decodeURIComponent (§19.2.6), Annex B escape, unescape (§B.2.1),
  encodeURI, decodeURI (§19.2.6); 0, 1, 2, 3, 4, 5. -/
  | uriFn (which : Nat)
  /-- A native of the embedding host: `HeapOf.hostCall` with this number. -/
  | host (k : Nat)
  /-- The built-ins added on 2026-11-09 (`NativeX`): one constructor, so that `Native`
  stays under the runtime's limit on constructor tags. -/
  | x (op : NativeX)
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
  | .hole | .fl => .undef

/-- The typed array element types: name, bytes per element. -/
def typedNames : Array (String × Nat) :=
  #[("Int8Array", 1), ("Uint8Array", 1), ("Uint8ClampedArray", 1), ("Int16Array", 2), ("Uint16Array", 2),
    ("Int32Array", 4), ("Uint32Array", 4), ("Float32Array", 4), ("Float64Array", 8),
    ("BigInt64Array", 8), ("BigUint64Array", 8)]

/-- The element types whose values are BigInts (§23.2: `BigInt64Array`, `BigUint64Array`). -/
def typedIsBig (ty : Nat) : Bool := ty == 9 || ty == 10

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
  props : PropMap PropV := {}
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

/-- An environment record: bindings in slots. `names[i]` is the name of slot `i`; a function's
environment shares its names array with the other activations of the function
(`FunInfo.layout`). A slot holds `Value.hole` while its binding is not initialised. -/
structure Env where
  names : Array String := #[]
  vals : Array Value := #[]
  /-- The slots whose bindings are immutable (`const`, a function expression's own name). -/
  immut : Array Nat := #[]
  /-- Name to slot, once the record has many names (the global record). -/
  index : Option (Std.HashMap String Nat) := none
  /-- The enclosing environment; the global environment, number 0, has none. -/
  parent : Nat := 0
  /-- The binding object of an Object Environment Record (§9.1.1.2, `with`). -/
  withObj : Option Nat := none
  deriving Inhabited

/-- The first index at or after `i` where `names` has `x`; `names.size` when it does not. -/
def Env.scan (names : Array String) (x : String) (i : Nat) : Nat :=
  if h : i < names.size then
    if names[i] == x then i else scan names x (i + 1)
  else names.size
termination_by names.size - i
decreasing_by simp_wf; omega

/-- The slot of a name in this record; `names.size` when absent. -/
def Env.slotN (e : Env) (x : String) : Nat :=
  match e.index with
  | some m => (m.get? x).getD e.names.size
  | none => Env.scan e.names x 0

def Env.slot? (e : Env) (x : String) : Option Nat :=
  let i := e.slotN x
  if i == e.names.size then none else some i

def Env.has (e : Env) (x : String) : Bool := e.slotN x != e.names.size

def Env.mutableAt (e : Env) (i : Nat) : Bool := e.immut.isEmpty || !e.immut.contains i

/-- The binding of a name, as a record (`Binding`). -/
def Env.get? (e : Env) (x : String) : Option Binding :=
  match e.slot? x with
  | some i => match e.vals.getD i .undef with
    | .hole => some { v := .undef, mutable := e.mutableAt i, init := false }
    | v => some { v, mutable := e.mutableAt i, init := true }
  | none => none

/-- Records with more names than this keep an index (`Env.index`). -/
def envIndexed : Nat := 24

/-- Declare or replace a binding. The new binding takes the next slot. -/
def Env.put (e : Env) (x : String) (b : Binding) : Env :=
  let val := if b.init then b.v else .hole
  match e.slot? x with
  | some i =>
    let immut :=
      if b.mutable then (if e.immut.contains i then e.immut.filter (· != i) else e.immut)
      else if e.immut.contains i then e.immut else e.immut.push i
    { e with vals := e.vals.set! i val, immut }
  | none =>
    let i := e.names.size
    let names := e.names.push x
    let vals := e.vals.push val
    let immut := if b.mutable then e.immut else e.immut.push i
    let index :=
      match e.index with
      | some m => some (m.insert x i)
      | none =>
        if names.size > envIndexed then
          some ((names.zipIdx).foldl (fun m (n, k) => m.insert n k) {})
        else none
    { e with names, vals, immut, index }

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
  sharedBufferProto : Nat := 0
  /-- %TypedArray% (§23.2.1), the constructor every typed array constructor inherits. -/
  typedArrayCtor : Nat := 0
  /-- %IteratorHelperPrototype% and %WrapForValidIteratorPrototype% (§27.1.2.1, §27.1.3.2.1.1). -/
  iterHelperProto : Nat := 0
  wrapIterProto : Nat := 0
  aggregateErrorProto : Nat := 0
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

/-- The fields of the heap that change rarely. They live apart from the hot fields of
`HeapOf`, so that a change of a hot field (the step count on every call and loop iteration,
the environment and object arrays) copies a small record, not all of these. -/
structure ColdHeap (H : Type) where
  out : Array String := #[]
  /-- The last string decoded for a regular expression, and its units (`cachedChars`). -/
  reCache : Option (String × Array Char) := none
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

/-- The heap, with the state `H` of the host that embeds the engine. A page host keeps
its DOM arena and event loop here (`WasmVM.Hosts.LeanJS`), so a native of the page
(`Native.host k`) reads and changes them at the call; the engine itself never looks
inside `H`. `Heap` is the heap with no host.

The counters are machine integers held in the record itself: no boxing, and no reference
counts to update when the record changes. -/
structure HeapOf (H : Type) extends ColdHeap H where
  objs : Array Obj := #[]
  envs : Array Env := #[{}]
  /-- Environments whose slots can be reused (`callClosure`, `FunInfo.frameLocal`). -/
  envFree : Array Nat := #[]
  /-- The register machine's registers and float registers, kept here between runs, and the
  first free register. -/
  vmRegs : Array Value := #[]
  vmF : FloatArray := .empty
  vmTop : Nat := 0
  /-- The slot of a name in the global object's property map, by a hash of the name; checked
  at each use (the name in that slot). Starts out empty. -/
  globalCache : Array Nat := Array.replicate 1024 0
  /-- Steps left before the script is stopped (an interrupt, not an exception). -/
  steps : UInt64 := 1000000000
  depth : UInt32 := 0
  maxDepth : UInt32 := 400

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
  | .hole | .fl => false

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
    if key == "length" then some (.data (.num (Float.ofNat (Str.jsLength s))) false false false)
    else match arrayIndex? key with
      | some i => match Str.unitStrAt? s i with
        | some c => some (.data (.str c) false true false)
        | none => o.props.get? key
      | none => o.props.get? key
  | _ => o.props.get? key

/-- The keys of `props` in insertion order. A `delete` leaves its key in `keys` (and
removing it there would cost a scan), so a key can be stale and, if added back, appear
twice: the last occurrence is the one that counts. When the sizes agree there is nothing
stale, and this is `keys` itself. -/
def Obj.liveKeys (o : Obj) : Array String :=
  if o.keys.size == o.props.size then o.keys else
  let (out, _) : Array String × Std.HashSet String :=
    o.keys.foldr (fun k (acc, seen) =>
      if seen.contains k || !o.props.contains k then (acc, seen)
      else (acc.push k, seen.insert k)) (#[], {})
  out.reverse

/-- The own keys in order (§10.1.11): array indices, then the rest by insertion. -/
def Obj.ownKeys (o : Obj) : Array String :=
  let idx := match o.kind with
    | .array es => (List.range es.size).toArray.map toString
    | .prim (.str s) => (List.range (Str.jsLength s)).toArray.map toString
    | _ => #[]
  let ks := o.liveKeys.filter fun k => !isPrivKey k
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

/-- The value of a data property found on the prototype chain, for the common kinds of
object, without building a `PropV`; `Value.hole` when the general path must decide (an accessor,
an exotic own key, or a miss). It gives the value of `findProp` on these objects: the
ordinary kinds keep their properties in `props` alone (`Obj.getOwn`), and an Array or
String exotic object is only skipped for keys that cannot be an index or `length`. -/
def HeapOf.fastGet (h : HeapOf H) (id : Nat) (key : String) : Nat → Value
  | 0 => .hole
  | fuel + 1 =>
    let o := h.objs.getD id default
    let kindOk := match o.kind with
      | .proxy .. | .typed .. | .prim _ => false
      | .array _ => key != "length" && !key.front.isDigit
      | _ => true
    if !kindOk then .hole else
    match o.props.get? key with
    | some (.data v ..) => v
    | some _ => .hole
    | none => match o.proto with
      | .obj p => h.fastGet p key fuel
      | _ => .hole

/-- `fastGet` from a value: an object, or a string's prototype. -/
@[inline] def HeapOf.fastGetV (h : HeapOf H) (v : Value) (key : String) : Value :=
  match v with
  | .obj id =>
    if key == "length" then
      match (h.objs.getD id default).kind with
      | .array es => .num (Float.ofNat es.size)
      | .proxy .. | .typed .. | .prim _ => .hole
      | _ => h.fastGet id key 1000
    else h.fastGet id key 1000
  | .str s =>
    if key == "length" then .num (Float.ofNat (Str.jsLength s))
    else if key.front.isDigit then .hole
    else h.fastGet h.realm.stringProto key 1000
  | _ => .hole

/-- `@@unscopables` of a `with` object names `name` with a true data value. -/
def HeapOf.unscopable (h : HeapOf H) (o : Nat) (name : String) : Bool :=
  match h.findProp o (String.singleton (Char.ofNat 0x10FFFF) ++ "5") 1000 with
  | some (.data (.obj u) ..) =>
    match h.findProp u name 1000 with
    | some (.data v ..) => toBool v
    | _ => false
  | _ => false

/-- The binding of a name: the number of the environment that holds it, walking out from
environment `e`. -/
def HeapOf.findEnv (h : HeapOf H) (name : String) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    let env := h.envs.getD e default
    if env.has name then some e
    else match env.withObj with
      | some o =>
        if (h.findProp o name 1000).isSome && !h.unscopable o name then some e
        else if e == 0 then none else h.findEnv name fuel env.parent
      | none => if e == 0 then none else h.findEnv name fuel env.parent

/-- The environment `hops` up from `e`. -/
def HeapOf.envUp (h : HeapOf H) : Nat → Nat → Nat
  | 0, e => e
  | k + 1, e => h.envUp k (h.envs.getD e default).parent

end L4Factoidal.JS
