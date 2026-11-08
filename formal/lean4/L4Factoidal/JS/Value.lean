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
  deriving BEq, Repr, Inhabited

inductive Kind where
  | ordinary
  | array (elems : Array Value)
  /-- A function object (§10.2) and the environment it closes over. `thisV` is
  the `this` an arrow function captured. -/
  | closure (f : FunDef) (env : Nat) (thisV : Value)
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
  deriving Inhabited

/-- The error constructors, by their index in `Realm.errorProtos`. -/
def errorNames : Array String :=
  #["Error", "EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError", "URIError"]

inductive ErrKind where
  | error | eval | range | reference | syntax | type | uri
  deriving BEq, Repr, Inhabited

def ErrKind.idx : ErrKind → Nat
  | .error => 0 | .eval => 1 | .range => 2 | .reference => 3 | .syntax => 4 | .type => 5 | .uri => 6

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

/-- What a running function sees. -/
structure Ctx where
  env : Nat
  thisV : Value
  strict : Bool
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
  let ints := ints.qsort fun a b => (arrayIndex? a).getD 0 < (arrayIndex? b).getD 0
  let extra := match o.kind with
    | .array _ => #["length"]
    | .prim (.str _) => #["length"]
    | _ => #[]
  idx ++ ints ++ extra ++ rest

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

/-- The binding of a name: the number of the environment that holds it. -/
def Heap.findEnv (h : Heap) (name : String) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _, none => none
  | fuel + 1, some e =>
    let env := h.envs.getD e default
    if env.vars.contains name then some e else h.findEnv name fuel env.parent

end L4Factoidal.JS
