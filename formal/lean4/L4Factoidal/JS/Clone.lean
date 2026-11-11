import L4Factoidal.JS.Value

/-!
# L4Factoidal.JS.Clone — StructuredSerialize and StructuredDeserialize (HTML §2.7)

The structured clone algorithm of HTML for the values of BubblePopJS, over the heap: a
value of one realm becomes bytes (`serialize`), and the bytes a value of another realm
(`deserialize`). Dedicated workers (`WasmVM.Hosts.LeanJSWorkers`) send messages this way:
the sender's heap and the receiver's heap never meet, only these bytes cross. The page's
`n.serialize` and `n.deserialize` are `Native.x .cloneSerialize` and `.cloneDeserialize`.

What is cloned (HTML §2.7.3 StructuredSerializeInternal):

- primitives (not Symbols); Boolean, Number, BigInt and String objects; Date; RegExp
  (source and flags, `lastIndex` 0);
- ArrayBuffer (its bytes; resizable keeps its maximum), with transfer (§2.7.5: the
  sender's buffer is detached, `serialize` answers which); typed arrays and DataView with
  their buffer;
- Map and Set (entries in order), Error objects (name from the prototype, `message`);
- Array and ordinary objects: their own enumerable string-keyed data properties, in order.

`DataCloneError` (the answer `.error`): Symbols, functions, Proxy, WeakMap, WeakSet,
Promise, generators, iterators, SharedArrayBuffer, a detached ArrayBuffer, a transfer list
with a buffer twice. Known limit: an accessor property is read as `undefined` (its getter
does not run: this is a walk of the heap, not of the evaluator).

Identity is kept: an object reached twice is one object in the copy (the memory of
§2.7.3 step 1), so cycles clone.

The walk is a loop over an explicit work stack, and decoding a loop over the bytes, so
nesting depth costs no Lean stack. Format: a value is a tag and its fields; numbers are
unsigned LEB128 (`natBytes`, whose round trip is `natOf_natBytes`); objects are numbered in
the order first met, and `back i` names object `i` again.
-/

namespace L4Factoidal.JS.Clone

/-! ## Numbers as bytes -/

/-- Unsigned LEB128, as a list: the specification. -/
def natBytes (n : Nat) : List UInt8 :=
  if h : n < 128 then [n.toUInt8]
  else (n % 128 + 128).toUInt8 :: natBytes (n / 128)
termination_by n
decreasing_by omega

/-- Read a LEB128 number from the front of a list. -/
def natOf : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else match natOf rest with
      | some (n, rest') => some (b.toNat - 128 + 128 * n, rest')
      | none => none

/-- The round trip of the number codec. -/
theorem natOf_natBytes (n : Nat) (rest : List UInt8) : natOf (natBytes n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natBytes
    by_cases h : n < 128
    · simp only [h, dite_true, List.singleton_append, natOf]
      have : (n.toUInt8).toNat = n := by
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat]; omega
      simp [this, h]
    · simp only [h, dite_false, List.cons_append, natOf]
      have hb : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 := by
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat]; omega
      have hlt : n / 128 < n := by omega
      simp only [hb, ih (n / 128) hlt]
      have : ¬ (n % 128 + 128 < 128) := by omega
      simp only [this, if_false, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-- `natBytes` on a byte array (the fast path; `putNat_agrees` checks it against the
specification). -/
def putNat (b : ByteArray) (n : Nat) : ByteArray :=
  -- recursion, not a `for` with an early `return`: that form kept the array shared, and
  -- each push copied the whole output (a message of n objects cost O(n²); 2026-11-11)
  if n < 128 then b.push n.toUInt8 else putNat (b.push (n % 128 + 128).toUInt8) (n / 128)
termination_by n
decreasing_by omega

#guard [0, 1, 127, 128, 300, 16383, 16384, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 64 + 5].all fun n =>
  (putNat ByteArray.empty n).toList == natBytes n

/-- Read a number at `i`: the number and the next index. -/
def readNat (b : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut acc := 0
  let mut scale := 1
  let mut j := i
  for _ in [0:b.size - i] do
    let x := b.get! j
    j := j + 1
    if x.toNat < 128 then return some (acc + scale * x.toNat, j)
    acc := acc + scale * (x.toNat - 128)
    scale := scale * 128
  return none

#guard [0, 1, 127, 128, 300, 2 ^ 32, 2 ^ 64 + 5].all fun n =>
  readNat (putNat (ByteArray.mk #[7]) n) 1 == some (n, (putNat (ByteArray.mk #[7]) n).size)

def zig (i : Int) : Nat := if i ≥ 0 then 2 * i.toNat else 2 * (-i).toNat - 1
def unzig (n : Nat) : Int := if n % 2 == 0 then (n / 2 : Nat) else -((n + 1) / 2 : Nat)

theorem unzig_zig (i : Int) : unzig (zig i) = i := by
  unfold zig unzig
  by_cases h : i ≥ 0
  · have e : (2 * i.toNat) % 2 = 0 := by omega
    simp only [h, if_true, e, beq_self_eq_true, if_true]
    omega
  · have e : (2 * (-i).toNat - 1) % 2 = 1 := by omega
    simp only [h, if_false, e]
    simp
    omega

/-! ## Tags -/

def tUndef : Nat := 0
def tNull : Nat := 1
def tFalse : Nat := 2
def tTrue : Nat := 3
def tNum : Nat := 4
def tStr : Nat := 5
def tBig : Nat := 6
def tBack : Nat := 7
def tBoolObj : Nat := 10
def tNumObj : Nat := 11
def tStrObj : Nat := 12
def tBigObj : Nat := 13
def tDate : Nat := 14
def tRegExp : Nat := 15
def tBuffer : Nat := 16
def tTyped : Nat := 18
def tDataView : Nat := 19
def tMap : Nat := 20
def tSet : Nat := 21
def tError : Nat := 22
def tArray : Nat := 23
def tObject : Nat := 24

/-- The hidden slots this walk reads (the evaluator's names, `JS.Interp`: `dateKey`,
`bufDetachedKey`, `bufSharedKey`, `bufMaxKey`). -/
def dateKey : String := privKey "%DateValue"
def detachedKey : String := privKey "%ArrayBufferDetached"
def sharedKey : String := privKey "%ArrayBufferShared"
def maxKey : String := privKey "%ArrayBufferMaxByteLength"

def flag (o : Obj) (k : String) : Bool :=
  match o.props.get? k with
  | some (.data (.bool b) ..) => b
  | _ => false

def hiddenNat (o : Obj) (k : String) : Option Nat :=
  match o.props.get? k with
  | some (.data (.num x) ..) => some x.toUInt64.toNat
  | _ => none

/-! ## StructuredSerialize -/

/-- A step of the walk: a value to write, or a property key. -/
inductive Work where
  | val (v : Value)
  | key (k : String)

structure SState where
  out : ByteArray := .empty
  /-- The memory: an object's number in the copy. -/
  memory : Std.HashMap Nat Nat := {}
  count : Nat := 0

/-- Write to the output, taken out of the state first so it grows in place. -/
@[inline] def SState.emit (st : SState) (f : ByteArray → ByteArray) : SState :=
  let ⟨out, memory, count⟩ := st
  ⟨f out, memory, count⟩

def putStr (b : ByteArray) (s : String) : ByteArray :=
  let u := s.toUTF8
  putNat b u.size ++ u

def errIdx (protos : Array Nat) (p : Value) : Nat :=
  match p with
  | .obj id => (protos.findIdx? (· == id)).getD 0
  | _ => 0

variable {H : Type}

/-- The own enumerable string-keyed properties of an object, with their values (an
accessor reads as `undefined`), in order (§2.7.3 step 26, EnumerableOwnProperties). -/
def enumProps (o : Obj) : Array (String × Value) :=
  let keys := match o.kind with
    | .array _ => o.keys.filter fun k => o.props.contains k && !isSymKey k && (arrayIndex? k).isNone
    | _ => o.ownStrKeys
  keys.filterMap fun k =>
    if isPrivKey k then none else
    match o.getOwn k with
    | some (.data v _ e _) => if e then some (k, v) else none
    | some (.acc _ _ e _) => if e then some (k, .undef) else none
    | none => none

/-- One object: its header written, and the work its fields need (in order). -/
def serializeObj (h : HeapOf H) (id : Nat) (o : Obj) (out : ByteArray) :
    Except String (ByteArray × Array Work) :=
  let r := h.realm
  match o.kind with
  | .prim (.bool b) => .ok (putNat (putNat out tBoolObj) (if b then 1 else 0), #[])
  | .prim (.num x) =>
    .ok (putNat (putNat out (if flag o dateKey then tDate else tNumObj)) x.toBits.toNat, #[])
  | .prim (.str s) => .ok (putStr (putNat out tStrObj) s, #[])
  | .prim (.big i) => .ok (putNat (putNat out tBigObj) (zig i), #[])
  | .regexp _ src flags => .ok (putStr (putStr (putNat out tRegExp) src) flags, #[])
  | .buffer bytes =>
    if flag o sharedKey then .error "SharedArrayBuffer could not be cloned"
    else if flag o detachedKey then .error "a detached ArrayBuffer could not be cloned"
    else
      let maxLen := match hiddenNat o maxKey with | some m => m + 1 | none => 0
      .ok (putNat (putNat (putNat out tBuffer) bytes.size ++ bytes) maxLen, #[])
  | .typed ty buf off len => .ok (putNat (putNat (putNat (putNat out tTyped) ty) off) len, #[.val (.obj buf)])
  | .dataView buf off len => .ok (putNat (putNat (putNat out tDataView) off) len, #[.val (.obj buf)])
  | .coll 0 es _ =>
    let live := es.filterMap fun e => e
    .ok (putNat (putNat out tMap) live.size, live.flatMap fun (k, v) => #[.val k, .val v])
  | .coll 1 es _ =>
    let live := es.filterMap fun e => e
    .ok (putNat (putNat out tSet) live.size, live.map fun (k, _) => .val k)
  | .error =>
    let msg := match o.getOwn "message" with
      | some (.data (.str m) ..) => some m
      | _ => none
    let out := putNat (putNat out tError) (errIdx r.errorProtos o.proto)
    .ok (match msg with
      | some m => putStr (putNat out 1) m
      | none => putNat out 0, #[])
  | .array es =>
    -- the elements by place, then the other properties
    let ps := (enumProps o).filter fun (k, _) => (arrayIndex? k).isNone
    .ok (putNat (putNat (putNat out tArray) es.size) ps.size,
      es.map .val ++ ps.flatMap fun (k, v) => #[.key k, .val v])
  | .ordinary | .args =>
    let ps := enumProps o
    .ok (putNat (putNat out tObject) ps.size, ps.flatMap fun (k, v) => #[.key k, .val v])
  | .closure .. | .native _ | .bound .. => .error s!"function could not be cloned (object {id})"
  | .proxy .. => .error "#<Object> could not be cloned (a Proxy)"
  | _ => .error "#<Object> could not be cloned"

/-- StructuredSerializeWithTransfer (§2.7.5) of `v`: the bytes, and the ArrayBuffers of
`transfer` that the sender must detach. `transfer` holds ArrayBuffer objects only; one
named twice, or detached, is a `DataCloneError`. `limit` bounds the work. -/
def serialize (h : HeapOf H) (v : Value) (transfer : Array Nat) (limit : Nat := 1 <<< 24) :
    Except String (ByteArray × Array Nat) := Id.run do
  for i in [0:transfer.size] do
    let t := transfer[i]!
    if transfer.extract 0 i |>.contains t then return .error "ArrayBuffer at index is a duplicate of an earlier ArrayBuffer"
    match (h.obj t).kind with
    | .buffer _ => if flag (h.obj t) detachedKey || flag (h.obj t) sharedKey then
        return .error "ArrayBuffer at index is detached or shared and could not be transferred"
    | _ => return .error "Value at index in the transfer list is not an ArrayBuffer"
  let mut st : SState := {}
  let mut stack : Array Work := #[.val v]
  for _ in [0:limit] do
    match stack.back? with
    | none => return .ok (st.out, transfer)
    | some w =>
      stack := stack.pop
      match w with
      | .key k => st := st.emit fun o => putStr o k
      | .val v =>
        match v with
        -- `hole` (a binding not yet initialised) and `fl` (a float register) are the
        -- interpreter's own and read as undefined, as `Value.toUndef` gives them
        | .undef | .hole | .fl => st := st.emit fun o => putNat o tUndef
        | .null => st := st.emit fun o => putNat o tNull
        | .bool b => st := st.emit fun o => putNat o (if b then tTrue else tFalse)
        | .num x => st := st.emit fun o => putNat (putNat o tNum) x.toBits.toNat
        | .str s => st := st.emit fun o => putStr (putNat o tStr) s
        | .big i => st := st.emit fun o => putNat (putNat o tBig) (zig i)
        | .sym _ => return .error "Symbol could not be cloned"
        | .obj id =>
          match st.memory.get? id with
          | some k => st := st.emit fun o => putNat (putNat o tBack) k
          | none =>
            -- the output and the memory are taken out of the state first (the state then
            -- holds empty ones), so both grow in place
            let out0 := st.out
            let memory0 := st.memory
            let count := st.count
            st := {}
            let memory := memory0.insert id count
            match serializeObj h id (h.obj id) out0 with
            | .error e => return .error e
            | .ok (out, more) =>
              st := { out, memory, count := count + 1 }
              -- the fields in order: the last pushed first
              stack := stack ++ more.reverse
  return .error "the value is too large to clone"

/-! ## StructuredDeserialize -/

/-- A container being filled: its object, its kind, and what it still waits for. -/
inductive Frame where
  /-- An array's elements: the next index, the length, and the properties after them. -/
  | elems (obj : Nat) (i len : Nat) (props : Nat)
  /-- An object or array: properties left; the key read, when its value comes next. -/
  | props (obj : Nat) (left : Nat) (key : Option String)
  /-- A Map (`map`) or Set: entries left; the key read, for a Map. -/
  | coll (obj : Nat) (map : Bool) (left : Nat) (key : Option Value)
  /-- A typed array or DataView waits for its buffer. -/
  | view (obj : Nat)
  deriving Inhabited

/-- The prototype of a global constructor (`Map`, `Set`): `Map.prototype`. -/
def protoOf (h : HeapOf H) (name : String) : Value :=
  match (h.obj h.realm.globalObj).getOwn name with
  | some (.data (.obj c) ..) => match (h.obj c).getOwn "prototype" with
    | some (.data p ..) => p
    | _ => .obj h.realm.objectProto
  | _ => .obj h.realm.objectProto

structure DState (H : Type) where
  heap : HeapOf H
  memory : Array Nat := #[]
  frames : Array Frame := #[]
  at_ : Nat := 0
  result : Option Value := none

/- Cost: every change of the heap's object array below takes the array out of the heap
first (`modObj`, `alloc`, `newObj`, `place`), as `JS.modifyObj` does, so it is changed in
place: a message of n objects into a heap of m objects costs O(n), not O(n·m). -/
def alloc (h : HeapOf H) (o : Obj) : Nat × HeapOf H :=
  let objs := h.objs
  let h := { h with objs := #[] }
  (objs.size, { h with objs := objs.push o })

/-- `f` on object `obj`, in place when nothing else holds the heap. -/
@[inline] def modObj (h : HeapOf H) (obj : Nat) (f : Obj → Obj) : HeapOf H :=
  let objs := h.objs
  let h := { h with objs := #[] }
  { h with objs := objs.modify obj f }

/-- A non-enumerable, non-writable, configurable own data property. -/
def ownData (o : Obj) (k : String) (v : Value) : Obj :=
  { o with props := o.props.insert k (.data v false false true), keys := if o.props.contains k then o.keys else o.keys.push k }

/-- Give a decoded value to the container on top, and pop the containers it completes.
`none`: the value is the whole result. -/
def place (st : DState H) (v : Value) : DState H := Id.run do
  -- taken apart, so that the heap and the frames are changed in place
  let ⟨heap0, memory, frames0, at_, result⟩ := st
  let mut heap := heap0
  let mut frames := frames0
  let mut v := v
  for _ in [0:frames.size + 1] do
    match frames.back? with
    | none => return ⟨heap, memory, frames, at_, some v⟩
    | some f =>
      frames := frames.pop
      match f with
      | .elems obj i len n =>
        heap := modObj heap obj fun o =>
          match o.kind with
          | .array es => { o with kind := .array (es.set! i v) }
          | _ => o
        if i + 1 < len then return ⟨heap, memory, frames.push (.elems obj (i + 1) len n), at_, result⟩
        else if n > 0 then return ⟨heap, memory, frames.push (.props obj n none), at_, result⟩
        else v := .obj obj
      | .props obj left none =>
        -- a key always comes first (`readKey`); a value here is a bad stream
        return ⟨heap, memory, frames.push (.props obj left none), at_, result⟩
      | .props obj left (some k) =>
        heap := modObj heap obj fun o =>
          match o.kind, arrayIndex? k with
          | .array es, some i =>
            if i < es.size then { o with kind := .array (es.set! i v) }
            else { o with props := o.props.insert k (.data v true true true), keys := o.keys.push k }
          | _, _ => { o with props := o.props.insert k (.data v true true true),
                             keys := if o.props.contains k then o.keys else o.keys.push k }
        if left ≤ 1 then v := .obj obj
        else return ⟨heap, memory, frames.push (.props obj (left - 1) none), at_, result⟩
      | .coll obj map left key =>
        match map, key with
        | true, none => return ⟨heap, memory, frames.push (.coll obj map left (some v)), at_, result⟩
        | _, _ =>
          let k := key.getD v
          heap := modObj heap obj fun o =>
            match o.kind with
            | .coll c es idx =>
              match idx.get? (VKey.of k) with
              | some i => { o with kind := .coll c (es.set! i (some (k, v))) idx }
              | none => { o with kind := .coll c (es.push (some (k, v))) (idx.insert (VKey.of k) es.size) }
            | _ => o
          if left ≤ 1 then v := .obj obj
          else return ⟨heap, memory, frames.push (.coll obj map (left - 1) none), at_, result⟩
      | .view obj =>
        let buf := match v with | .obj b => b | _ => 0
        heap := modObj heap obj fun o =>
          match o.kind with
          | .typed ty _ off len => { o with kind := .typed ty buf off len }
          | .dataView _ off len =>
            -- a DataView's `byteLength`, `byteOffset` and `buffer` are own properties here
            -- (as the evaluator's constructor makes them)
            let o := { o with kind := .dataView buf off len }
            let o := ownData o "byteLength" (.num (Float.ofNat len))
            let o := ownData o "byteOffset" (.num (Float.ofNat off))
            ownData o "buffer" (.obj buf)
          | _ => o
        v := .obj obj
  return ⟨heap, memory, frames, at_, result⟩

def readStr (b : ByteArray) (i : Nat) : Option (String × Nat) := do
  let (n, j) ← readNat b i
  if j + n > b.size then none
  let s ← String.fromUTF8? (b.extract j (j + n))
  some (s, j + n)

/-- A new object in the copy: allocated and remembered (its number is its place in
`memory`). -/
def newObj (st : DState H) (o : Obj) : DState H × Nat :=
  let ⟨heap, memory, frames, at_, result⟩ := st
  let (id, heap) := alloc heap o
  (⟨heap, memory.push id, frames, at_, result⟩, id)

/-- An object or Map/Set with no entries is complete at once; else it waits. -/
def openOr (st : DState H) (id : Nat) (left : Nat) (f : Frame) : DState H :=
  if left == 0 then place st (.obj id) else { st with frames := st.frames.push f }

/-- StructuredDeserialize (§2.7.6): the value, in the heap `h` (whose realm gives the
prototypes), and the heap. `none`: the bytes are not a serialization (a `messageerror`);
the heap may then hold objects of the part read, which nothing refers to. -/
def deserializeIn (h : HeapOf H) (b : ByteArray) : Option Value × HeapOf H := Id.run do
  let r := h.realm
  let mut st : DState H := { heap := h }
  for _ in [0:b.size + 1] do
    if let some v := st.result then return (some v, st.heap)
    -- a property key comes before each value of an object
    if let some (.props obj left none) := st.frames.back? then
      match readStr b st.at_ with
      | none => return (none, st.heap)
      | some (k, j) => st := { st with at_ := j, frames := st.frames.pop.push (.props obj left (some k)) }
      continue
    let some (tag, j) := readNat b st.at_ | return (none, st.heap)
    st := { st with at_ := j }
    let num := fun (st : DState H) => readNat b st.at_
    if tag == tUndef then st := place st .undef
    else if tag == tNull then st := place st .null
    else if tag == tFalse then st := place st (.bool false)
    else if tag == tTrue then st := place st (.bool true)
    else if tag == tNum then
      let some (x, j) := num st | return (none, st.heap)
      st := place { st with at_ := j } (.num (Float.ofBits x.toUInt64))
    else if tag == tStr then
      let some (s, j) := readStr b st.at_ | return (none, st.heap)
      st := place { st with at_ := j } (.str s)
    else if tag == tBig then
      let some (x, j) := num st | return (none, st.heap)
      st := place { st with at_ := j } (.big (unzig x))
    else if tag == tBack then
      let some (k, j) := num st | return (none, st.heap)
      let some id := st.memory[k]? | return (none, st.heap)
      st := place { st with at_ := j } (.obj id)
    else if tag == tBoolObj then
      let some (x, j) := num st | return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.booleanProto, kind := .prim (.bool (x != 0)) }
      st := place st' (.obj id)
    else if tag == tNumObj || tag == tDate then
      let some (x, j) := num st | return (none, st.heap)
      let dateProps : PropMap PropV := ({} : PropMap PropV).insert dateKey (.data (.bool true) true false false)
      let o : Obj := if tag == tDate then
          { proto := .obj r.dateProto, kind := .prim (.num (Float.ofBits x.toUInt64)), props := dateProps, keys := #[dateKey] }
        else { proto := .obj r.numberProto, kind := .prim (.num (Float.ofBits x.toUInt64)) }
      let (st', id) := newObj { st with at_ := j } o
      st := place st' (.obj id)
    else if tag == tStrObj then
      let some (s, j) := readStr b st.at_ | return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.stringProto, kind := .prim (.str s) }
      st := place st' (.obj id)
    else if tag == tBigObj then
      let some (x, j) := num st | return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.bigintProto, kind := .prim (.big (unzig x)) }
      st := place st' (.obj id)
    else if tag == tRegExp then
      let some (src, j) := readStr b st.at_ | return (none, st.heap)
      let some (fl, j) := readStr b j | return (none, st.heap)
      let .ok re := Re.compile src fl | return (none, st.heap)
      let props : PropMap PropV := ({} : PropMap PropV).insert "lastIndex" (.data (.num 0) true false false)
      let o : Obj := { proto := .obj r.regexpProto, kind := .regexp re src fl, props, keys := #["lastIndex"] }
      let (st', id) := newObj { st with at_ := j } o
      st := place st' (.obj id)
    else if tag == tBuffer then
      let some (n, j) := num st | return (none, st.heap)
      if j + n > b.size then return (none, st.heap)
      let bytes := b.extract j (j + n)
      let some (m, j) := readNat b (j + n) | return (none, st.heap)
      let o : Obj := { proto := .obj r.bufferProto, kind := .buffer bytes }
      let o := if m == 0 then o else
        { o with props := o.props.insert maxKey (.data (.num (Float.ofNat (m - 1))) true false false), keys := #[maxKey] }
      let (st', id) := newObj { st with at_ := j } o
      st := place st' (.obj id)
    else if tag == tTyped then
      let some (ty, j) := num st | return (none, st.heap)
      let some (off, j) := readNat b j | return (none, st.heap)
      let some (len, j) := readNat b j | return (none, st.heap)
      if ty ≥ typedNames.size then return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj (r.typedProtos.getD ty r.objectProto), kind := .typed ty 0 off len }
      st := { st' with frames := st'.frames.push (.view id) }
    else if tag == tDataView then
      let some (off, j) := num st | return (none, st.heap)
      let some (len, j) := readNat b j | return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.dataViewProto, kind := .dataView 0 off len }
      st := { st' with frames := st'.frames.push (.view id) }
    else if tag == tMap || tag == tSet then
      let some (n, j) := num st | return (none, st.heap)
      let proto := protoOf st.heap (if tag == tMap then "Map" else "Set")
      let o : Obj := { proto, kind := .coll (if tag == tMap then 0 else 1) #[] {} }
      let (st', id) := newObj { st with at_ := j } o
      st := openOr st' id n (.coll id (tag == tMap) n none)
    else if tag == tError then
      let some (k, j) := num st | return (none, st.heap)
      let some (has, j) := readNat b j | return (none, st.heap)
      let read := if has == 0 then some (none, j) else (readStr b j).map fun (m, j) => (some m, j)
      let some (msg, j) := read | return (none, st.heap)
      let o : Obj := { proto := .obj (r.errorProtos.getD k r.objectProto), kind := .error }
      let o := match msg with
        | some m => { o with props := o.props.insert "message" (.data (.str m) true false true), keys := #["message"] }
        | none => o
      let (st', id) := newObj { st with at_ := j } o
      st := place st' (.obj id)
    else if tag == tArray then
      let some (len, j) := num st | return (none, st.heap)
      let some (n, j) := readNat b j | return (none, st.heap)
      if len > b.size then return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.arrayProto, kind := .array (Array.replicate len .undef) }
      st := if len > 0 then { st' with frames := st'.frames.push (.elems id 0 len n) }
        else openOr st' id n (.props id n none)
    else if tag == tObject then
      let some (n, j) := num st | return (none, st.heap)
      let (st', id) := newObj { st with at_ := j } { proto := .obj r.objectProto }
      st := openOr st' id n (.props id n none)
    else return (none, st.heap)
  match st.result with
  | some v => return (some v, st.heap)
  | none => return (none, st.heap)

/-- `deserializeIn` as an option: the value and the heap, or `none`. -/
def deserialize (h : HeapOf H) (b : ByteArray) : Option (Value × HeapOf H) :=
  match deserializeIn h b with
  | (some v, h) => some (v, h)
  | (none, _) => none

end L4Factoidal.JS.Clone
