import Std.Data.HashMap
import L4Factoidal.JS.Syntax
import L4Factoidal.JS.Number

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
  | done (v : Value)

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
  | native (id : Native)
  | bound (target thisV : Value) (args : Array Value)
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

structure Heap where
  objs : Array Obj := #[]
  envs : Array Env := #[{}]
  out : Array String := #[]
  /-- Steps left before the script is stopped (an interrupt, not an exception). -/
  steps : Nat := 1000000000
  depth : Nat := 0
  maxDepth : Nat := 400
  rng : UInt64 := 0x2545F4914F6CDD1D
  realm : Realm := {}
  /-- The description of each Symbol; the well-known ones first (`wellKnown`). -/
  syms : Array String := wellKnown.map ("Symbol." ++ ·)
  deriving Inhabited

/-- Why evaluation stopped early: a thrown value, or the host stopped it. -/
inductive Abrupt where
  | throw (v : Value)
  | halt (why : String)
  deriving Inhabited

abbrev M := EStateM Abrupt Heap

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

def Heap.obj (h : Heap) (id : Nat) : Obj := h.objs.getD id default

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
  let ks := o.keys.filter fun k => o.props.contains k
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
def Heap.findProp (h : Heap) (id : Nat) (key : String) : Nat → Option PropV
  | 0 => none
  | fuel + 1 =>
    let o := h.obj id
    match o.getOwn key with
    | some p => some p
    | none => match o.proto with
      | .obj p => h.findProp p key fuel
      | _ => none

/-- `@@unscopables` of a `with` object names `name` with a true data value. -/
def Heap.unscopable (h : Heap) (o : Nat) (name : String) : Bool :=
  match h.findProp o (String.singleton (Char.ofNat 0x10FFFF) ++ "5") 1000 with
  | some (.data (.obj u) ..) =>
    match h.findProp u name 1000 with
    | some (.data v ..) => toBool v
    | _ => false
  | _ => false

/-- The binding of a name: the number of the environment that holds it. -/
def Heap.findEnv (h : Heap) (name : String) : Nat → Option Nat → Option Nat
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
