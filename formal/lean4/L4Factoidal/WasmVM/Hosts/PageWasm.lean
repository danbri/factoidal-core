/-
L4Factoidal.WasmVM.Hosts.PageWasm: the WebAssembly JavaScript API of page scripts
(https://webassembly.github.io/spec/js-api/), served by Lean on WasmVM
(record: docs/designissues/2026-11-08-page-wasm.md; engine: issue 1244).

A page's modules, instances, memories, tables, globals and tags live in one WasmVM store
of their own, `State.store`, held in the page's host state (`Hosts.Page.Host.wasm`). It is
a different Lean value from the store of the script engine (the QuickJS heap): nothing a
page module runs can name the script engine's memory, and the script engine reaches the
page store only through the one import `foafnaut_dom.wasm_call`, served here.

    wasm_call(op, handle, ptr, len, out, cap, view, viewLen) -> answer length | negative code

- `ptr, len`: the request bytes (read only).
- `out, cap`: the answer buffer. An answer longer than `cap` is kept (`State.pending`) and
  its length answered; op `fetch` then writes it, so no op runs twice.
- `view, viewLen`: the bytes of a `Memory.buffer` ArrayBuffer of the script engine, or
  `0, 0`. Calls and the view ops copy the pages that changed between it and the module's
  memory (`pushView`, `pullView`).

`serve_writes` states what a call can do to the script engine's memory: only writes inside
`[out, out + cap)` and `[view, view + viewLen)`. Everything else it changes is this
module's own state.

The calls into a module are WasmVM's `invokeSteps`/`resumeSteps`: a call of an imported
JavaScript function stops the run (`Outcome.hostCall`), the run is kept here (`State.paused`), and the
answer tells the prelude which JavaScript function to call; the prelude answers with op
`resume`. So a page module never runs while a script runs, and the script engine is never
entered from Lean: there is no re-entrant call.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Hosts.Dom

namespace L4Factoidal.WasmVM.Hosts.PageWasm
open L4Factoidal.WasmVM

/-! ## State -/

/-- A compiled module: the validator's certificate and the custom sections. -/
structure Mod where
  valid : ValidModule
  customs : Array (String × ByteArray)
  deriving Inhabited

/-- A `Memory.buffer` the script holds: the memory and the bytes the script's copy had at
the last copy in either direction. -/
structure View where
  mem : Nat
  shadow : ByteArray
  deriving Inhabited

/-- A run stopped at a call of a JavaScript function, and the fuel it has left. -/
structure Paused where
  k : Suspended
  fuel : Nat
  deriving Inhabited

/-- The page's budgets for WebAssembly. -/
structure Config where
  /-- Instructions for one call from JavaScript, the calls back into JavaScript included. -/
  fuel : Nat := 4000000000
  /-- Pages of 64 KiB one memory may have: 1024 is 64 MiB. -/
  pages : Nat := 1024
  /-- Pages of all the page's memories together: 4096 is 256 MiB. A new memory, an
  instantiation and a call are refused while the memories hold more (a module can still
  grow each of its memories up to `pages` within one call). -/
  totalPages : Nat := 4096
  /-- Memories in the page store (their pages are bounded by `totalPages`). -/
  memories : Nat := 65536
  /-- Modules a page may compile, the bytes of one module, and of all of them. -/
  modules : Nat := 1000000
  moduleBytes : Nat := 67108864
  allModuleBytes : Nat := 268435456
  /-- Bytes of a view (an ArrayBuffer of the script engine). -/
  viewBytes : Nat := 67108864
  /-- Calls back into JavaScript that may wait at once (nested). -/
  depth : Nat := 1000
  deriving Inhabited, Repr


structure State where
  store : Store := { pageLimit := 1024 }
  modules : Array Mod := #[]
  /-- Runs waiting for a JavaScript function, innermost last. -/
  paused : Array Paused := #[]
  views : Array View := #[]
  /-- An answer longer than the buffer the script gave, for op `fetch`. -/
  pending : ByteArray := ByteArray.empty
  /-- Instructions run by page modules in total. -/
  steps : Nat := 0
  /-- Bytes of all the modules compiled. -/
  moduleBytes : Nat := 0
  config : Config := {}
  deriving Inhabited

def State.ofConfig (c : Config) : State := { store := { pageLimit := c.pages }, config := c }

/-! ## Bytes -/

def u32 (b : ByteArray) (n : Nat) : ByteArray :=
  let v := n.toUInt32
  (((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

def u64 (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut b := b
  for k in [0:8] do b := b.push (v >>> (8 * k).toUInt64).toUInt8
  return b

def rd32 (b : ByteArray) (p : Nat) : Nat :=
  (b.get! p).toNat ||| ((b.get! (p + 1)).toNat <<< 8) ||| ((b.get! (p + 2)).toNat <<< 16) ||| ((b.get! (p + 3)).toNat <<< 24)

def rd64 (b : ByteArray) (p : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for k in [0:8] do v := v ||| ((b.get! (p + k)).toUInt64 <<< (8 * k).toUInt64)
  return v

def none32 : Nat := 0xFFFFFFFF

/-! ## Types and values as the prelude names them -/

def heapName : HeapType → String
  | .func | .idx _ => "func" | .extern => "extern" | .exn => "exn" | .any => "any" | .eq => "eq"
  | .i31 => "i31" | .struct => "struct" | .array => "array" | .none => "none" | .nofunc => "nofunc"
  | .noextern => "noextern" | .noexn => "noexn"

/-- `i32`, `i64`, `f32`, `f64`, `v128`; a nullable reference `funcref`, `externref`,
`exnref`, `anyref`...; a non-null reference `func!`, `extern!`... -/
def valName : ValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | .v128 => "v128"
  | .ref r => heapName r.heap ++ (if r.nullable then "ref" else "!")

def valOfName : String → Option ValType
  | "i32" => some .i32 | "i64" => some .i64 | "f32" => some .f32 | "f64" => some .f64
  | "funcref" | "anyfunc" => some (.ref ⟨true, .func⟩)
  | "externref" => some (.ref ⟨true, .extern⟩)
  | "exnref" => some (.ref ⟨true, .exn⟩)
  | _ => none

def typesName (ts : Array ValType) : String := " ".intercalate (ts.map valName).toList

def typesOfName (s : String) : Option (Array ValType) :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.mapM valOfName

/-- A value as the prelude reads it: a tag, then the 8 bytes of its bits. -/
def valTag : Value → UInt8
  | .i32 _ => 0 | .i64 _ => 1 | .f32 _ => 2 | .f64 _ => 3 | .funcRef _ => 4 | .externRef _ => 5 | .exnRef _ => 6
  | .v128 .. => 7

def putVal (b : ByteArray) (v : Value) : ByteArray := u64 (b.push (valTag v)) v.toBits

def putVals (b : ByteArray) (vs : Array Value) : ByteArray := vs.foldl putVal (u32 b vs.size)

/-- `n` values of types `ts` from bits at `p`, or none when the bytes are short. -/
def valsAt (b : ByteArray) (p : Nat) (ts : Array ValType) : Option (Array Value) :=
  if b.size < p + 8 * ts.size then none
  else some (ts.zipIdx.map fun (t, i) => Value.ofBits t (rd64 b (p + 8 * i)))

/-! ## JSON for the descriptions (small; not on the call path) -/

def hex (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def jstr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c.toNat < 32 then
      out := out ++ "\\u00" ++ String.singleton (hex (c.toNat / 16)) ++ String.singleton (hex c.toNat)
    else out := out.push c
  return out ++ "\""

def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def limitsJson (l : Limits) : String :=
  s!"{l.min},{match l.max with | some m => toString m | none => "null"}"

/-! ## Custom sections (the decoder keeps none) -/

/-- The custom sections of a module that decoded: (name, contents) in order. Each step
reads one section header, so `fuel` (the byte count) bounds the scan. -/
def customSections (b : ByteArray) : Array (String × ByteArray) :=
  go 8 b.size #[]
where
  go (p : Nat) : Nat → Array (String × ByteArray) → Array (String × ByteArray)
    | 0, acc => acc
    | fuel + 1, acc =>
      if p ≥ b.size then acc else
      let id := b.get! p
      match Binary.Leb.uSpec b (p + 1) 32 with
      | none => acc
      | some (size, q) =>
        let next := q + size
        if next > b.size then acc else
        if id != 0 then go next fuel acc else
        match Binary.Leb.uSpec b q 32 with
        | none => acc
        | some (nl, r) =>
          if r + nl > next then acc else
          -- A name that is not UTF-8 matches no name a script can ask for.
          match String.fromUTF8? (b.extract r (r + nl)) with
          | some name => go next fuel (acc.push (name, b.extract (r + nl) next))
          | none => go next fuel acc

/-! ## Comparing and copying pages -/

/-- The unit of copying between a view and its memory. -/
def chunk : Nat := 4096

/-- Bytes `[o, o + n)` of `a` and `b` are the same. The reference (spec) form; the copy
loops below use it on one chunk at a time, after one whole-array compare (`==`, a
`memcmp` in the runtime) says something changed. -/
def sameAt (a b : ByteArray) (o n : Nat) : Bool := a.extract o (o + n) == b.extract o (o + n)

/-- The chunks where `a` and `b` differ (they have the same size), as (offset, bytes of
`a`). -/
def changedChunks (a b : ByteArray) : Array (Nat × ByteArray) := Id.run do
  if a == b then return #[]
  let mut out := #[]
  for i in [0:(a.size + chunk - 1) / chunk] do
    let o := i * chunk
    let n := min chunk (a.size - o)
    if !sameAt a b o n then out := out.push (o, a.extract o (o + n))
  return out

/-- The chunks of `a` that are not all zero (a new ArrayBuffer is all zero). -/
def nonZeroChunks (a : ByteArray) : Array (Nat × ByteArray) := Id.run do
  let zero := ByteArray.mk (Array.replicate chunk 0)
  let mut out := #[]
  for i in [0:(a.size + chunk - 1) / chunk] do
    let o := i * chunk
    let n := min chunk (a.size - o)
    let c := a.extract o (o + n)
    if c != zero.extract 0 n then out := out.push (o, c)
  return out

/-- Write chunks into a byte array (in place when it is not shared). -/
def patch (base : ByteArray) (cs : Array (Nat × ByteArray)) : ByteArray :=
  cs.foldl (fun acc (o, c) => c.copySlice 0 acc o c.size) base

def memBytes (st : Store) (a : Nat) : ByteArray :=
  match st.mems[a]? with
  | some m => m.data.data
  | none => ByteArray.empty

def memPages (st : Store) (a : Nat) : Nat := (memBytes st a).size / pageSize

/-- Pages of all the memories of the page store. -/
def totalPages (st : Store) : Nat := st.mems.foldl (fun n m => n + LinearMemory.size m.data / pageSize) 0

/-- The script wrote its view: the changed chunks go into the memory, and the bytes read
are the new shadow. A view whose memory changed size is left (the prelude closes it). -/
def pushView (s : State) (vi : Nat) (j : ByteArray) : State :=
  match s.views[vi]? with
  | none => s
  | some v =>
    if j.size != v.shadow.size || j.size != (memBytes s.store v.mem).size then s else
    let cs := changedChunks j v.shadow
    if cs.isEmpty then s else
    -- The store is taken out of the state first, so the memory is written in place.
    let st := s.store
    let s := { s with store := {} }
    let st := cs.foldl (fun st (o, c) => (st.writeMemS v.mem o c).1) st
    { s with store := st, views := s.views.set! vi { v with shadow := j } }

/-- After a run: the chunks of the memory that changed go to the script's view (offsets in
the view). A memory whose size changed is reported grown and its view is dropped. -/
def pullView (s : State) (vi : Nat) : State × Array (Nat × ByteArray) × Option (Nat × Nat) :=
  match s.views[vi]? with
  | none => (s, #[], none)
  | some v =>
    let m := memBytes s.store v.mem
    if m.size != v.shadow.size then
      ({ s with views := s.views.eraseIdxIfInBounds vi }, #[], some (v.mem, m.size / pageSize))
    else
      let cs := changedChunks m v.shadow
      if cs.isEmpty then (s, #[], none) else
      let s := { s with views := s.views.set! vi default }
      ({ s with views := s.views.set! vi { v with shadow := patch v.shadow cs } }, cs, none)

def viewOf (s : State) (mem : Nat) : Option Nat := s.views.findIdx? (·.mem == mem)

/-! ## The calls -/

/-- What one call asks of the script engine's memory: the bytes of the view, when it
reads them. -/
abbrev ReadView := Unit → Option ByteArray

/-- The result of a call: the state, the writes into the view (offset, bytes) and the
answer, or a negative code. -/
abbrev Result := State × Array (Nat × ByteArray) × Except Int ByteArray

def ok (s : State) (b : ByteArray) : Result := (s, #[], .ok b)
def okText (s : State) (t : String) : Result := ok s t.toUTF8
def err (s : State) (c : Int) : Result := (s, #[], .error c)

def trapKind : Trap → Nat
  | .callStackExhausted => 1
  | .host m => if m == "javascript exception" then 2 else 0
  | _ => 0

/-- The answer of a run, and the view copy after it. Kinds: 0 values; 1 trap (kind,
message); 2 a call of a JavaScript function (paused run, host id, result types, values);
3 an exception (tag, values). Then the memories whose views grew: (memory, pages). -/
def finishRun (s : State) (viewMem : Nat) (fuelLeft : Nat) (st : Store) (o : Outcome) (n : Nat) : Result :=
  let s := { s with store := st, steps := s.steps + n }
  let (s, body) : State × ByteArray := match o with
    | .values vs => (s, putVals (ByteArray.empty.push 0) vs)
    | .trap t => (s, (u32 ((ByteArray.empty.push 1).push (trapKind t).toUInt8) 0) ++ t.message.toUTF8)
    | .outOfFuel _ => (s, (u32 ((ByteArray.empty.push 1).push 3) 0) ++ "out of fuel".toUTF8)
    | .exit _ => (s, (u32 ((ByteArray.empty.push 1).push 0) 0) ++ "exit".toUTF8)
    | .exception tag vs => (s, putVals (u32 (ByteArray.empty.push 3) tag) vs)
    | .hostCall id vs k =>
      if s.paused.size ≥ s.config.depth then
        (s, (u32 ((ByteArray.empty.push 1).push 1) 0) ++ "too many nested calls".toUTF8)
      else
        let rs := (k.hostResults.getD #[])
        let b := u32 (u32 (ByteArray.empty.push 2) s.paused.size) id
        let tn := (typesName rs).toUTF8
        let b := u32 b tn.size ++ tn
        ({ s with paused := s.paused.push { k, fuel := fuelLeft - n } }, putVals b vs)
  -- The views: the one given with the call, then any other whose memory grew.
  let (s, writes, grown) := match viewOf s viewMem with
    | some vi => let (s, w, g) := pullView s vi; (s, w, g.toList)
    | none => (s, #[], [])
  let (s, grown) := s.views.foldl (init := (s, grown)) fun (s, g) v =>
    if (memBytes s.store v.mem).size != v.shadow.size then
      ({ s with views := s.views.filter (·.mem != v.mem) }, (v.mem, memPages s.store v.mem) :: g)
    else (s, g)
  let tail := grown.foldl (fun b (m, p) => u32 (u32 b m) p) (u32 ByteArray.empty grown.length)
  -- The answer: its length first, so the prelude finds the grown list after it.
  (s, writes, .ok (u32 ByteArray.empty body.size ++ body ++ tail))

/-- Push the view given with a call (the script may have written it). -/
def pushGiven (s : State) (viewMem : Nat) (read : ReadView) : State :=
  match viewOf s viewMem with
  | none => s
  | some vi => match read () with
    | some j => pushView s vi j
    | none => s

/-- Op 5: call function `fa`: the view's memory at 0, the arguments' bits from 8. -/
def invoke (s : State) (fa : Nat) (payload : ByteArray) (read : ReadView) : Result :=
  if totalPages s.store > s.config.totalPages then err s (-5) else
  match s.store.funcs[fa]? with
  | none => err s (-2)
  | some fi =>
    match valsAt payload 8 fi.type.params with
    | none => err s (-2)
    | some args =>
      let vm := rd32 payload 0
      let s := pushGiven s vm read
      -- The store leaves the state while it runs, so the run changes it in place.
      let st := s.store
      let s := { s with store := {} }
      let (st, o, n) := invokeSteps st fa args { fuel := s.config.fuel }
      finishRun s vm s.config.fuel st o n

/-- Op 6: the JavaScript function of the innermost paused run answered (view memory at 0,
status at 4, results' bits from 8): status 0, or 1 (it threw: the run ends as a trap the prelude turns back into the
JavaScript exception). -/
def resume (s : State) (id : Nat) (payload : ByteArray) (read : ReadView) : Result :=
  if id + 1 != s.paused.size then err s (-2) else
  let p := s.paused.back!
  let s := { s with paused := s.paused.pop }
  let vm := rd32 payload 0
  let s := pushGiven s vm read
  let r : HostResult :=
    if payload.get! 4 != 0 then .trap "javascript exception"
    else match valsAt payload 8 (p.k.hostResults.getD #[]) with
      | some vs => .values vs
      | none => .trap "javascript results"
  let st := s.store
  let s := { s with store := {} }
  let (st, o, n) := resumeSteps st p.k r { fuel := p.fuel }
  finishRun s vm p.fuel st o n

/-- The description of an import or export type, as JSON fields after its kind. -/
def funcJson (ft : FuncType) : String := s!"{jstr (typesName ft.params)},{jstr (typesName ft.results)}"

def importJson (m : Module) (i : Import) : String :=
  match i.desc with
  | .func t => s!"[{jstr i.module},{jstr i.name},\"function\",{funcJson (m.types[t]?.getD ⟨#[], #[]⟩)}]"
  | .table tt => s!"[{jstr i.module},{jstr i.name},\"table\",{jstr (valName (.ref tt.elem))},{limitsJson tt.limits}]"
  | .mem mt => s!"[{jstr i.module},{jstr i.name},\"memory\",{limitsJson mt.limits}]"
  | .global gt => s!"[{jstr i.module},{jstr i.name},\"global\",{jstr (valName gt.type)},{gt.mutable}]"
  | .tag t => s!"[{jstr i.module},{jstr i.name},\"tag\",{jstr (typesName (m.types[t]?.getD ⟨#[], #[]⟩).params)}]"

def exportKind : ExternIdx → String
  | .func _ => "function" | .table _ => "table" | .mem _ => "memory" | .global _ => "global" | .tag _ => "tag"

/-- Op 2: decode and validate; the module's number, imports and exports. -/
def compile (s : State) (bytes : ByteArray) : Result :=
  if s.modules.size ≥ s.config.modules then okText s "{\"error\":\"too many modules\"}" else
  if bytes.size > s.config.moduleBytes || s.moduleBytes + bytes.size > s.config.allModuleBytes then
    okText s "{\"error\":\"module too large\"}" else
  match Binary.decode bytes with
  | .error e => okText s s!"\{\"error\":{jstr e.toString}}"
  | .ok m =>
    match validate m with
    | .error e => okText s s!"\{\"error\":{jstr e.toString}}"
    | .ok vm =>
      let id := s.modules.size
      let md : Mod := { valid := vm, customs := customSections bytes }
      let s := { s with modules := s.modules.push md, moduleBytes := s.moduleBytes + bytes.size }
      let imports := m.imports.toList.map (importJson m)
      let exports := m.exports.toList.map fun x => s!"[{jstr x.name},{jstr (exportKind x.desc)}]"
      okText s s!"\{\"m\":{id},\"imports\":{jarr imports},\"exports\":{jarr exports}}"

/-- Op 3: the custom sections of module `mi` with this name: count, then (length, bytes). -/
def custom (s : State) (mi : Nat) (name : ByteArray) : Result :=
  match s.modules[mi]? with
  | none => err s (-2)
  | some md =>
    let nm := (String.fromUTF8? name).getD ""
    let cs := md.customs.filter (·.1 == nm)
    ok s (cs.foldl (fun b (_, c) => u32 b c.size ++ c) (u32 ByteArray.empty cs.size))

/-- An export of an instance, with what the prelude needs to make its object. -/
def exportJson (st : Store) (m : Module) (name : String) (x : ExternIdx) (v : ExternVal) : String :=
  match v with
  | .func a =>
    let ft := (st.funcs[a]?.map (·.type)).getD ⟨#[], #[]⟩
    let idx := match x with | .func i => i | _ => 0
    s!"[{jstr name},\"function\",{a},{funcJson ft},{idx}]"
  | .table a =>
    let elem := (st.tables[a]?.map (·.elem)).getD ⟨true, .func⟩
    s!"[{jstr name},\"table\",{a},{jstr (valName (.ref elem))}]"
  | .mem a => s!"[{jstr name},\"memory\",{a}]"
  | .global a =>
    let gt := st.globalTypes[a]?.getD ⟨false, .i32⟩
    s!"[{jstr name},\"global\",{a},{jstr (valName gt.type)},{gt.mutable}]"
  | .tag a =>
    let ps := (st.exc.tags[a]?.map (·.params)).getD #[]
    let _ := m
    s!"[{jstr name},\"tag\",{a},{jstr (typesName ps)}]"

/-- The canonical function type of a module's type `t`, as `instantiate` makes it. -/
def canonType (st : Store) (m : Module) (t : Nat) : Store × FuncType := Id.run do
  let mut st := st
  let mut ids := #[]
  for ft in m.types do
    let (st', i) := st.typeId (canonFunc ids ft)
    st := st'
    ids := ids.push i
  return (st, canonFunc ids (m.types[t]?.getD ⟨#[], #[]⟩))

/-- Op 4: instantiate module `mi`. Each import is 8 bytes, a kind and a number (u32 each): 0 a function
address, 1 a JavaScript function (its host id), 2 a table, 3 a memory, 4 a global, 5 a tag
address, 6 a new immutable global of the import's type with these bits (8 more bytes).
The answer: the instance and its exports, with the start function for the prelude to
call; or a link error or a trap. -/
def instantiateOp (s : State) (mi : Nat) (p : ByteArray) : Result := Id.run do
  let some md := s.modules[mi]? | return err s (-2)
  let m := md.valid.module
  let ownMems := m.mems.size
  if s.store.mems.size + ownMems > s.config.memories ||
      totalPages s.store + (m.mems.foldl (fun n mt => n + mt.limits.min) 0) > s.config.totalPages then
    return okText s "{\"trap\":\"over the page's memory budget\"}"
  let mut st := s.store
  let mut ev : Array ExternVal := #[]
  let mut q := 0
  for imp in m.imports do
    if p.size < q + 8 then return okText { s with store := st } "{\"link\":\"imports\"}"
    let kind := rd32 p q
    let a := rd32 p (q + 4)
    q := q + 8
    match kind, imp.desc with
    | 1, .func t =>
      let (st', ft) := canonType st m t
      let (st'', fa) := st'.addHostFunc ft a
      st := st''
      ev := ev.push (.func fa)
    | 6, .global gt =>
      if p.size < q + 8 then return okText { s with store := st } "{\"link\":\"imports\"}"
      let bits := rd64 p q
      q := q + 8
      let (st', ga) := st.addGlobal { gt with mutable := false } bits
      st := st'
      ev := ev.push (.global ga)
    | 0, _ => ev := ev.push (.func a)
    | 2, _ => ev := ev.push (.table a)
    | 3, _ => ev := ev.push (.mem a)
    | 4, _ => ev := ev.push (.global a)
    | 5, _ => ev := ev.push (.tag a)
    | _, _ => return okText { s with store := st } "{\"link\":\"imports\"}"
  match instantiate st md.valid ev with
  | (st2, .error (.link e)) => return okText { s with store := st2 } s!"\{\"link\":{jstr e}}"
  | (st2, .error (.trap t)) => return okText { s with store := st2 } s!"\{\"trap\":{jstr t.message}}"
  | (st2, .ok (ia, start)) =>
    let inst := st2.insts[ia]!
    let xs := (m.exports.zip inst.exports).toList.map fun (x, (name, v)) => exportJson st2 m name x.desc v
    let startJ := match start with | some a => toString a | none => "null"
    return okText { s with store := st2 } s!"\{\"i\":{ia},\"start\":{startJ},\"exports\":{jarr xs}}"

/-- Op 7: a function's type and its index in its module (the `name` of its JavaScript
function). -/
def funcInfo (s : State) (fa : Nat) : Result :=
  match s.store.funcs[fa]? with
  | none => err s (-2)
  | some fi =>
    let idx := match fi.kind with
      | .wasm ia _ => ((s.store.insts[ia]?.map (fun (i : ModuleInst) => i.funcs.idxOf fa))).getD fa
      | .host _ => fa
    okText s s!"[{funcJson fi.type},{idx}]"

/-- Op 8: a new memory: initial and maximum pages (`none32` for none). -/
def memNew (s : State) (p : ByteArray) : Result :=
  if p.size < 8 then err s (-2) else
  let ini := rd32 p 0
  let mx := rd32 p 4
  if s.store.mems.size ≥ s.config.memories || ini > s.config.pages ||
      totalPages s.store + ini > s.config.totalPages then err s (-5) else
  let (st, a) := s.store.addMem ⟨⟨ini, if mx == none32 then none else some mx⟩⟩
  ok { s with store := st } (u32 ByteArray.empty a)

/-- Op 10: grow a memory by `delta` pages: the old size, or -1. -/
def memGrow (s : State) (a : Nat) (p : ByteArray) : Result :=
  match s.store.mems[a]? with
  | none => err s (-2)
  | some mi =>
    let d := rd32 p 0
    let old := LinearMemory.size mi.data / pageSize
    if old + d > min (mi.max.getD 65536) s.store.pageLimit || totalPages s.store + d > s.config.totalPages then err s (-1) else
    let st := if d == 0 then s.store else
      { s.store with mems := s.store.mems.modify a fun ⟨data, max⟩ => ⟨LinearMemory.grow data (d * pageSize), max⟩ }
    -- The memory's views are dropped, also for 0 pages (the prelude detaches the buffer:
    -- JS API, "refresh the memory buffer").
    ok { s with store := st, views := s.views.filter (·.mem != a) } (u32 ByteArray.empty old)

/-- Op 11: the script made an ArrayBuffer of the memory's size for `Memory.buffer`: the
memory's chunks that are not zero are written into it, and it is a view from now on. -/
def viewOpen (s : State) (a : Nat) (viewLen : Nat) : Result :=
  let m := memBytes s.store a
  if a ≥ s.store.mems.size || m.size != viewLen || viewLen > s.config.viewBytes then err s (-2) else
  let cs := nonZeroChunks m
  let s := { s with views := (s.views.filter (·.mem != a)).push { mem := a, shadow := m.extract 0 m.size } }
  (s, cs, .ok ByteArray.empty)

/-- Ops 15 to 19: tables. -/
def tableNew (s : State) (p : ByteArray) : Result :=
  if p.size < 16 then err s (-2) else
  match valOfName ((String.fromUTF8? (p.extract 16 p.size)).getD "") with
  | some (.ref r) =>
    let ini := rd32 p 0
    let mx := rd32 p 4
    if ini > 10000000 then err s (-5) else
    let (st, a) := s.store.addTable ⟨⟨ini, if mx == none32 then none else some mx⟩, r⟩ (rd64 p 8)
    ok { s with store := st } (u32 ByteArray.empty a)
  | _ => err s (-2)

def refOk (st : Store) (r : RefType) (bits : UInt64) : Bool :=
  if bits == nullRef then r.nullable
  else match r.heap with
    | .func | .idx _ => bits.toNat < st.funcs.size
    | _ => true

def tableGet (s : State) (a : Nat) (p : ByteArray) : Result :=
  match s.store.tables[a]? with
  | none => err s (-2)
  | some t =>
    match t.elems[rd32 p 0]? with
    | none => err s (-1)
    | some bits => ok s (putVal ByteArray.empty (Value.ofBits (.ref t.elem) bits))

def tableSet (s : State) (a : Nat) (p : ByteArray) : Result :=
  match s.store.tables[a]? with
  | none => err s (-2)
  | some t =>
    let i := rd32 p 0
    let bits := rd64 p 8
    if !refOk s.store t.elem bits then err s (-3) else
    if i ≥ t.elems.size then err s (-1) else
    ok { s with store := { s.store with tables := s.store.tables.modify a fun t => { t with elems := t.elems.set! i bits } } } ByteArray.empty

def tableGrow (s : State) (a : Nat) (p : ByteArray) : Result :=
  match s.store.tables[a]? with
  | none => err s (-2)
  | some t =>
    let d := rd32 p 0
    let bits := rd64 p 8
    if !refOk s.store t.elem bits then err s (-3) else
    let old := t.elems.size
    if old + d > min (t.max.getD 4294967295) 10000000 then err s (-1) else
    ok { s with store := { s.store with tables := s.store.tables.modify a fun t => { t with elems := t.elems ++ Array.replicate d bits } } }
      (u32 ByteArray.empty old)

/-- Ops 20 to 22: globals. New: mutable (u32), bits at 8, the type's name from 16. -/
def globalNew (s : State) (p : ByteArray) : Result :=
  if p.size < 16 then err s (-2) else
  match valOfName ((String.fromUTF8? (p.extract 16 p.size)).getD "") with
  | none => err s (-2)
  | some t =>
    let bits := rd64 p 8
    match t with
    | .ref r => if !refOk s.store r bits then err s (-3) else
      let (st, a) := s.store.addGlobal ⟨p.get! 0 != 0, t⟩ bits
      ok { s with store := st } (u32 ByteArray.empty a)
    | _ =>
      let (st, a) := s.store.addGlobal ⟨p.get! 0 != 0, t⟩ bits
      ok { s with store := st } (u32 ByteArray.empty a)

def globalGet (s : State) (a : Nat) : Result :=
  match s.store.globalTypes[a]? with
  | none => err s (-2)
  | some gt => ok s (putVal ByteArray.empty (Value.ofBits gt.type (s.store.globalBits a)))

def globalSet (s : State) (a : Nat) (p : ByteArray) : Result :=
  match s.store.globalTypes[a]? with
  | none => err s (-2)
  | some gt =>
    if !gt.mutable then err s (-4) else
    let bits := rd64 p 0
    match gt.type with
    | .ref r => if !refOk s.store r bits then err s (-3) else
      ok { s with store := { s.store with globals := Slots.wr s.store.globals a.toUSize bits } } ByteArray.empty
    | _ => ok { s with store := { s.store with globals := Slots.wr s.store.globals a.toUSize bits } } ByteArray.empty

/-- Op 23: a new tag with these parameter types; op 24 a tag's parameter types. -/
def tagNew (s : State) (p : ByteArray) : Result :=
  match typesOfName ((String.fromUTF8? p).getD "") with
  | none => err s (-2)
  | some ps =>
    let ft : FuncType := ⟨ps, #[]⟩
    let (st, _) := s.store.typeId ft
    let (st, a) := st.addTag ft
    ok { s with store := st } (u32 ByteArray.empty a)

def tagType (s : State) (a : Nat) : Result :=
  match s.store.exc.tags[a]? with
  | none => err s (-2)
  | some ft => okText s (typesName ft.params)

/-- One call: op, handle, the request bytes, the view's length and how to read it. -/
def core (op h : Nat) (p : ByteArray) (viewLen : Nat) (read : ReadView) (s : State) : Result :=
  match op with
  | 0 => ok s (u32 ByteArray.empty 1)
  | 1 => ok s (ByteArray.empty.push (match Binary.decode p >>= (fun m => (validate m).mapError (fun _ => .malformed "" 0)) with
      | .ok _ => 1 | .error _ => 0))
  | 2 => compile s p
  | 3 => custom s h p
  | 4 => instantiateOp s h p
  | 5 => invoke s h p read
  | 6 => resume s h p read
  | 7 => funcInfo s h
  | 8 => memNew s p
  -- A memory's pages and its maximum (`none32` for none).
  | 9 => ok s (u32 (u32 ByteArray.empty (memPages s.store h))
      (((s.store.mems[h]?).bind (·.max)).getD none32))
  | 10 => memGrow s h p
  | 11 => viewOpen s h viewLen
  | 12 => ok { s with views := s.views.filter (·.mem != h) } ByteArray.empty
  | 13 => match viewOf s h, read () with
    | some vi, some j => ok (pushView s vi j) ByteArray.empty
    | _, _ => err s (-2)
  | 14 => match viewOf s h with
    | some vi =>
      let (s, w, g) := pullView s vi
      (s, w, .ok (match g with | some (_, pg) => u32 ByteArray.empty pg | none => ByteArray.empty))
    | none => err s (-2)
  | 15 => tableNew s p
  -- A table's length and its maximum (`none32` for none).
  | 16 => match s.store.tables[h]? with
    | some t => ok s (u32 (u32 ByteArray.empty t.elems.size) (t.max.getD none32))
    | none => err s (-2)
  | 17 => tableGet s h p
  | 18 => tableSet s h p
  | 19 => tableGrow s h p
  | 20 => globalNew s p
  | 21 => globalGet s h
  | 22 => globalSet s h p
  | 23 => tagNew s p
  | 24 => tagType s h
  | 31 => ok { s with pending := ByteArray.empty } s.pending
  | _ => err s (-10)

/-! ## The import, and what it can do to the script engine's memory -/

section
variable {M : Type} [LinearMemory M]

/-- Write `b` at offset `o` of the view `[base, base + len)`, only when it fits there. -/
def putIn (mem base len : Nat) (st : StoreOf M) (w : Nat × ByteArray) : StoreOf M :=
  if w.1 + w.2.size ≤ len then (st.writeMemS mem (base + w.1) w.2).1 else st

def putAll (mem base len : Nat) : List (Nat × ByteArray) → StoreOf M → StoreOf M
  | [], st => st
  | w :: ws, st => putAll mem base len ws (putIn mem base len st w)

/-- The bounds of one request and of one view. -/
def maxRequest : Nat := 67108864 + 65536

/-- `foafnaut_dom.wasm_call(op, handle, ptr, len, out, cap, view, viewLen)`. -/
def serve (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × StoreOf M × HostResult :=
  let a := Hosts.Dom.arg args
  if args.size != 8 || args.any (fun v => match v with | .i32 _ => false | _ => true) then
    (s, st, .trap "foafnaut_dom.wasm_call: wrong arguments")
  else if a 3 > maxRequest then (s, st, Hosts.Dom.ret (-5))
  else match st.readMem mem (a 2) (a 3) with
  | .error _ => (s, st, .trap "foafnaut_dom.wasm_call: request outside memory")
  | .ok p =>
    let read : ReadView := fun () =>
      if a 7 == 0 || a 7 > s.config.viewBytes then none
      else (st.readMem mem (a 6) (a 7)).toOption
    let (s, ws, ans) := core (a 0) (a 1) p (a 7) read s
    let st := putAll mem (a 6) (a 7) ws.toList st
    match ans with
    | .error c => (s, st, Hosts.Dom.ret c)
    | .ok b =>
      if b.size ≤ a 5 then
        let (st, r) := Hosts.Dom.putOut mem st (a 4) (a 5) b
        (s, st, r)
      else ({ s with pending := b }, st, Hosts.Dom.ret b.size)

/-- `st'` is `st` after writes of memory `mem`, each inside one of the ranges `rs`
(start, length). -/
inductive Writes (mem : Nat) (rs : List (Nat × Nat)) : StoreOf M → StoreOf M → Prop
  | refl (st : StoreOf M) : Writes mem rs st st
  | write (st st₁ st₂ : StoreOf M) (off : Nat) (b : ByteArray) (r : Nat × Nat)
      (hr : r ∈ rs) (hin : r.1 ≤ off ∧ off + b.size ≤ r.1 + r.2)
      (hw : st.writeMem mem off b = .ok st₁) (rest : Writes mem rs st₁ st₂) : Writes mem rs st st₂

theorem Writes.trans {mem : Nat} {rs : List (Nat × Nat)} {a b c : StoreOf M}
    (h₁ : Writes mem rs a b) (h₂ : Writes mem rs b c) : Writes mem rs a c := by
  induction h₁ with
  | refl => exact h₂
  | write st st₁ st₂ off bb r hr hin hw _ ih => exact .write st st₁ c off bb r hr hin hw (ih h₂)

theorem putIn_writes (mem base len : Nat) (rs : List (Nat × Nat)) (hr : (base, len) ∈ rs)
    (st : StoreOf M) (w : Nat × ByteArray) : Writes mem rs st (putIn mem base len st w) := by
  unfold putIn
  split
  · rename_i hfit
    cases hw : st.writeMemS mem (base + w.1) w.2 with
    | mk st' okw =>
      cases okw with
      | false => simp only; rw [StoreOf.writeMemS_false hw]; exact .refl _
      | true =>
        simp only
        exact .write st st' st' (base + w.1) w.2 (base, len) hr ⟨Nat.le_add_right _ _, by simp; omega⟩
          (StoreOf.writeMem_of_writeMemS hw) (.refl _)
  · exact .refl _

theorem putAll_writes (mem base len : Nat) (rs : List (Nat × Nat)) (hr : (base, len) ∈ rs) :
    ∀ (ws : List (Nat × ByteArray)) (st : StoreOf M), Writes mem rs st (putAll mem base len ws st)
  | [], st => .refl st
  | w :: ws, st => (putIn_writes mem base len rs hr st w).trans (putAll_writes mem base len rs hr ws _)

theorem putOut_writes (mem buf cap : Nat) (rs : List (Nat × Nat)) (hr : (buf, cap) ∈ rs)
    (st : StoreOf M) (b : ByteArray) : Writes mem rs st (Hosts.Dom.putOut mem st buf cap b).1 := by
  rcases Hosts.Dom.putOut_within mem st buf cap b with h | ⟨b', hs, hw⟩
  · rw [h]; exact .refl _
  · exact .write st _ _ buf b' (buf, cap) hr ⟨Nat.le_refl _, by omega⟩ hw (.refl _)

/-- **What a page's WebAssembly can do to the script engine's memory.** One
`wasm_call` changes the memory of the script engine (the QuickJS heap) only by writes
inside its answer buffer `[out, out + cap)` and its view `[view, view + viewLen)`; it
grows nothing and changes no table, global or function of that store. Whatever the op and
whatever the page's modules do, since they run on `State.store`, a different value. -/
theorem serve_writes (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) :
    Writes mem [(Hosts.Dom.arg args 4, Hosts.Dom.arg args 5), (Hosts.Dom.arg args 6, Hosts.Dom.arg args 7)]
      st (serve mem args s st).2.1 := by
  unfold serve
  dsimp only
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · exact .refl _
      · rename_i p _
        generalize core _ _ _ _ _ _ = r
        obtain ⟨s', ws, ans⟩ := r
        dsimp only
        have h₁ := putAll_writes (M := M) mem (Hosts.Dom.arg args 6) (Hosts.Dom.arg args 7)
          [(Hosts.Dom.arg args 4, Hosts.Dom.arg args 5), (Hosts.Dom.arg args 6, Hosts.Dom.arg args 7)]
          (by simp) ws.toList st
        cases ans with
        | error c => exact h₁
        | ok b =>
          dsimp only
          split
          · exact h₁.trans (putOut_writes mem _ _ _ (by simp) _ b)
          · exact h₁

end

end L4Factoidal.WasmVM.Hosts.PageWasm
