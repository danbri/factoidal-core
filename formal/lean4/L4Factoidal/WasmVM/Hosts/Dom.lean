/-
L4Factoidal.WasmVM.Hosts.Dom: the `foafnaut_dom` host functions for page scripts that
run in QuickJS inside the WasmVM engine (https://github.com/danbri/factoidal/issues/1244;
record: docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").

The guest is `tools/wasmvm/quickjs/qjs_wasmvm_entry.c`, built by
`tools/wasmvm/build-quickjs.sh`. Each DOM operation of a page script is one import.
This host reads its arguments from VM memory with bounds checks (`Store.readMem`),
turns it into a typed command on the Lean DOM arena (`DOM.Arena`, the arena that
`WebRenderScript` changes), and answers with an i32.

- The commands are those of `labs/demos/foafnaut/WebRenderScript.lean`
  (`setTextContent`, `setAttribute`), with the same bounds (a string of at most 64 KiB,
  an attribute name of at most 256 bytes, at most 4096 commands, at most 1048576 nodes),
  plus `createElement` and `appendChild`. `Command` records each one, so a host can
  send the same list to another arena.
- Timers and event listeners only record a `Request`. The host's event loop decides
  which callback runs, and when, and runs it with the guest export
  `qjs_call(callback, target)`. Nothing here runs JavaScript.
- Deny by default: the host is a pure function of its state, the arguments and the
  store. It has no network, file, clock or randomness access, because it has no monad.
  The WASI imports of the module are served by `WasmVM.Wasi` with `Caps` `{}` (nothing
  granted) unless the embedder grants more.

Results: a node id, a length, or 0 for success; negative values are errors, and the
guest turns them into JavaScript exceptions:
-1 none, -2 not an element node (or no such node), -3 InvalidCharacterError,
-4 HierarchyRequestError (or another DOM error), -5 over a budget, -7 a string that is
not UTF-8.

String results: the guest gives a buffer (pointer, capacity). The host writes the whole
string there when it fits, and nothing when it does not; it always answers the full
length, and the guest asks again with a larger buffer. `call_writes_within` proves that
the only memory a DOM import can change is at most `capacity` bytes at that buffer.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.DOM.Arena

namespace L4Factoidal.WasmVM.Hosts.Dom
open L4Factoidal.WasmVM L4Factoidal.DOM

def moduleName : String := "foafnaut_dom"

/-- A typed DOM command: what the page did to the arena. -/
inductive Command where
  | setTextContent (node : Nat) (value : String)
  | setAttribute (node : Nat) (name value : String)
  /-- `createElement(name)` made node `result`. -/
  | createElement (name : String) (result : Nat)
  | appendChild (parent child : Nat)
  deriving BEq, Repr, Inhabited

/-- A request to the event loop. -/
inductive Request where
  /-- Run `callback` with the target node when an event `type` is dispatched to `node`. -/
  | listen (node : Nat) (type : String) (callback : Nat)
  /-- Run `callback` after `delayMs`; again every `delayMs` when `repeating`. -/
  | timer (id callback delayMs : Nat) (repeating : Bool)
  | clearTimer (id : Nat)
  deriving BEq, Repr, Inhabited

/-- The host's state: the arena and what the page asked for. -/
structure State where
  dom : Dom
  commands : Array Command := #[]
  requests : Array Request := #[]
  logs : Array String := #[]
  nextTimer : Nat := 1
  deriving Inhabited

/-- Bounds, as in `WebRenderScript`. -/
def maxString : Nat := 65536
def maxAttrName : Nat := 256
def maxCommands : Nat := 4096
def maxNodes : Nat := 1048576
def maxRequests : Nat := 4096
def maxLogs : Nat := 1024

/-- The imports of `foafnaut_dom`. -/
inductive Import where
  | getElementById | documentElement | tagName | textContentGet | textContentSet
  | getAttribute | setAttribute | createElement | appendChild | addEventListener
  | setTimer | clearTimer | consoleLog
  deriving DecidableEq, Repr, Inhabited

namespace Import

def all : List Import :=
  [getElementById, documentElement, tagName, textContentGet, textContentSet, getAttribute,
   setAttribute, createElement, appendChild, addEventListener, setTimer, clearTimer, consoleLog]

def name : Import → String
  | getElementById => "get_element_by_id" | documentElement => "document_element"
  | tagName => "tag_name" | textContentGet => "text_content_get"
  | textContentSet => "text_content_set" | getAttribute => "get_attribute"
  | setAttribute => "set_attribute" | createElement => "create_element"
  | appendChild => "append_child" | addEventListener => "add_event_listener"
  | setTimer => "set_timer" | clearTimer => "clear_timer" | consoleLog => "console_log"

/-- Number of i32 parameters; every import answers one i32. -/
def arity : Import → Nat
  | getElementById => 2 | documentElement => 1 | tagName => 3 | textContentGet => 3
  | textContentSet => 3 | getAttribute => 5 | setAttribute => 5 | createElement => 2
  | appendChild => 2 | addEventListener => 4 | setTimer => 3 | clearTimer => 1 | consoleLog => 2

def type (f : Import) : FuncType := ⟨Array.replicate f.arity .i32, #[.i32]⟩

def ofName? (s : String) : Option Import := all.find? (·.name == s)

/-- The argument positions of the output buffer (pointer, capacity), for the imports
that write a string into VM memory. -/
def outBuffer : Import → Option (Nat × Nat)
  | tagName => some (1, 2) | textContentGet => some (1, 2) | getAttribute => some (3, 4)
  | _ => none

theorem all_length : all.length = 13 := rfl
theorem all_names_distinct : (all.map name).Nodup := by decide
theorem ofName?_name (f : Import) : ofName? f.name = some f := by cases f <;> rfl

end Import

section
variable {M : Type} [LinearMemory M]

/-- An i32 result. -/
def ret (r : Int) : HostResult := .values #[.i32 (Int.toNat (r % 4294967296)).toUInt32]

/-- Argument `k` as an unsigned i32. -/
def arg (args : Array Value) (k : Nat) : Nat :=
  match args[k]? with | some (.i32 v) => v.toNat | _ => 0

/-- Read a UTF-8 string of `len` bytes at `ptr`, at most `bound` bytes. -/
def readStr (mem : Nat) (st : StoreOf M) (ptr len bound : Nat) : Except Int String :=
  if len > bound then .error (-5) else
  match st.readMem mem ptr len with
  | .error _ => .error (-8)
  | .ok b => match String.fromUTF8? b with
    | some s => .ok s
    | none => .error (-7)

def domErr : DomError → Int
  | .invalidCharacter => -3
  | _ => -4

def isElement (d : Dom) (n : Nat) : Bool := n < d.size && (d.get n).type == .element

/-- The value of attribute `name` (no namespace) of element `n`. -/
def attrValue? (d : Dom) (n : Nat) (name : String) : Option String :=
  let q := if (d.get n).ns == some htmlNS then Dom.asciiLower name else name
  ((d.get n).attrs.find? (fun a => a.qname == q)).map (·.value)

/-- The first HTML element named `name` in tree order. -/
def firstNamed (d : Dom) (name : String) : Option Nat :=
  (d.treeOrder 0 false).find? fun k => Dom.isHtmlElement (d.get k) name

/-- Write `b` at `buf` when it fits in `cap` bytes, nothing otherwise; answer its length.
A pointer outside memory traps. -/
def putOut (mem : Nat) (st : StoreOf M) (buf cap : Nat) (b : ByteArray) : StoreOf M × HostResult :=
  if b.size ≤ cap then
    match st.writeMem mem buf b with
    | .ok st' => (st', ret b.size)
    | .error e => (st, .trap s!"foafnaut_dom: {e}")
  else (st, ret b.size)

/-- A string result, or an error code (nothing written). -/
def answerStr (mem : Nat) (st : StoreOf M) (buf cap : Nat) : Except Int String → StoreOf M × HostResult
  | .ok s => putOut mem st buf cap s.toUTF8
  | .error e => (st, ret e)

/-- A trap for an argument string outside memory, otherwise the code. -/
def codeOrTrap (e : Int) : HostResult := if e == -8 then .trap "foafnaut_dom: string outside memory" else ret e

def addCommand (s : State) (c : Command) (d : Dom) : State × HostResult :=
  if s.commands.size ≥ maxCommands || d.size > maxNodes then (s, ret (-5))
  else ({ s with dom := d, commands := s.commands.push c }, ret 0)

/-! ## The imports that do not write VM memory: `State → State × HostResult` -/

def getElementById (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  match readStr mem st (arg args 0) (arg args 1) maxString with
  | .error e => (s, codeOrTrap e)
  | .ok id => match s.dom.getElementById 0 id with
    | some n => (s, ret n)
    | none => (s, ret (-1))

def documentElement (args : Array Value) (s : State) : State × HostResult :=
  let name := match arg args 0 with | 0 => "html" | 1 => "body" | _ => "head"
  match firstNamed s.dom name with
  | some n => (s, ret n)
  | none => (s, ret (-1))

def textContentSet (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) maxString with
  | .error e => (s, codeOrTrap e)
  | .ok v => addCommand s (.setTextContent n v) (s.dom.setTextContent n v)

def setAttribute (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) maxAttrName, readStr mem st (arg args 3) (arg args 4) maxString with
  | .error e, _ => (s, codeOrTrap e)
  | _, .error e => (s, codeOrTrap e)
  | .ok name, .ok v =>
    match s.dom.setAttribute n name v with
    | (_, .error e) => (s, ret (domErr e))
    | (d, .ok ()) => addCommand s (.setAttribute n name v) d

def createElement (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  match readStr mem st (arg args 0) (arg args 1) maxAttrName with
  | .error e => (s, codeOrTrap e)
  | .ok name =>
    match s.dom.createElement 0 name with
    | (_, .error e) => (s, ret (domErr e))
    | (d, .ok n) =>
      match addCommand s (.createElement name n) d with
      | (s', .values #[.i32 0]) => (s', ret n)
      | r => r

def appendChild (args : Array Value) (s : State) : State × HostResult :=
  let p := arg args 0
  let c := arg args 1
  if !isElement s.dom p || !isElement s.dom c then (s, ret (-2)) else
  match s.dom.appendChild p c with
  | (_, .error e) => (s, ret (domErr e))
  | (d, .ok ()) => addCommand s (.appendChild p c) d

def addRequest (s : State) (r : Request) (answer : Int) : State × HostResult :=
  if s.requests.size ≥ maxRequests then (s, ret (-5))
  else ({ s with requests := s.requests.push r }, ret answer)

def addEventListener (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) maxAttrName with
  | .error e => (s, codeOrTrap e)
  | .ok t => addRequest s (.listen n t (arg args 3)) 0

def setTimer (args : Array Value) (s : State) : State × HostResult :=
  let id := s.nextTimer
  match addRequest s (.timer id (arg args 0) (arg args 1) (arg args 2 != 0)) id with
  | (s', .values #[.i32 v]) => if v.toNat == id then ({ s' with nextTimer := id + 1 }, ret id) else (s', ret v.toNat)
  | r => r

def clearTimer (args : Array Value) (s : State) : State × HostResult :=
  addRequest s (.clearTimer (arg args 0)) 0

def consoleLog (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  match readStr mem st (arg args 0) (arg args 1) maxString with
  | .error e => (s, codeOrTrap e)
  | .ok t => if s.logs.size ≥ maxLogs then (s, ret (-5)) else ({ s with logs := s.logs.push t }, ret 0)

/-! ## The imports that write a string into VM memory -/

def tagName (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  let n := arg args 0
  answerStr mem st (arg args 1) (arg args 2)
    (if isElement s.dom n then .ok (s.dom.get n).lname else .error (-2))

def textContentGet (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  let n := arg args 0
  answerStr mem st (arg args 1) (arg args 2)
    (if n < s.dom.size then match s.dom.textContent n with | some t => .ok t | none => .error (-1)
     else .error (-2))

def getAttribute (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (st, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) maxAttrName with
  | .error e => (st, codeOrTrap e)
  | .ok name => answerStr mem st (arg args 3) (arg args 4)
      (match attrValue? s.dom n name with | some v => .ok v | none => .error (-1))

/-- One import: the new state, the new store and the answer. -/
def call (mem : Nat) (f : Import) (args : Array Value) (s : State) (st : StoreOf M) :
    State × StoreOf M × HostResult :=
  let pure1 := fun (r : State × HostResult) => (r.1, st, r.2)
  let write := fun (r : StoreOf M × HostResult) => (s, r.1, r.2)
  match f with
  | .getElementById => pure1 (getElementById mem args s st)
  | .documentElement => pure1 (documentElement args s)
  | .tagName => write (tagName mem args s st)
  | .textContentGet => write (textContentGet mem args s st)
  | .textContentSet => pure1 (textContentSet mem args s st)
  | .getAttribute => write (getAttribute mem args s st)
  | .setAttribute => pure1 (setAttribute mem args s st)
  | .createElement => pure1 (createElement mem args s st)
  | .appendChild => pure1 (appendChild args s)
  | .addEventListener => pure1 (addEventListener mem args s st)
  | .setTimer => pure1 (setTimer args s)
  | .clearTimer => pure1 (clearTimer args s)
  | .consoleLog => pure1 (consoleLog mem args s st)

/-! ## What a DOM import can do to VM memory -/

/-- `st'` is `st`, or `st` after one write of at most `cap` bytes at `buf`. -/
def WritesWithin (mem buf cap : Nat) (st st' : StoreOf M) : Prop :=
  st' = st ∨ ∃ b : ByteArray, b.size ≤ cap ∧ st.writeMem mem buf b = .ok st'

theorem putOut_within (mem : Nat) (st : StoreOf M) (buf cap : Nat) (b : ByteArray) :
    WritesWithin mem buf cap st (putOut mem st buf cap b).1 := by
  unfold putOut
  split
  · rename_i h
    split
    · rename_i st' hw; exact .inr ⟨b, h, hw⟩
    · exact .inl rfl
  · exact .inl rfl

theorem answerStr_within (mem : Nat) (st : StoreOf M) (buf cap : Nat) (r : Except Int String) :
    WritesWithin mem buf cap st (answerStr mem st buf cap r).1 := by
  cases r with
  | ok s => exact putOut_within mem st buf cap s.toUTF8
  | error e => exact .inl rfl

theorem getAttribute_within (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) :
    WritesWithin mem (arg args 3) (arg args 4) st (getAttribute mem args s st).1 := by
  unfold getAttribute
  dsimp only
  by_cases h : (!isElement s.dom (arg args 0)) = true
  · rw [if_pos h]; exact .inl rfl
  · rw [if_neg h]
    split
    · exact .inl rfl
    · exact answerStr_within ..

/-- A DOM import changes VM memory only at its output buffer, by at most its capacity
bytes; an import with no output buffer does not change the store at all. -/
theorem call_writes_within (mem : Nat) (f : Import) (args : Array Value) (s : State) (st : StoreOf M) :
    match f.outBuffer with
    | none => (call mem f args s st).2.1 = st
    | some (b, c) => WritesWithin mem (arg args b) (arg args c) st (call mem f args s st).2.1 := by
  cases f <;> simp only [Import.outBuffer, call]
  · exact answerStr_within ..
  · exact answerStr_within ..
  · exact getAttribute_within ..

/-- A DOM import changes the store only by `writeMem`: never memory growth, tables,
globals or functions. (A corollary of `call_writes_within`.) -/
theorem call_store (mem : Nat) (f : Import) (args : Array Value) (s : State) (st : StoreOf M) :
    (call mem f args s st).2.1 = st ∨
      ∃ buf b, st.writeMem mem buf b = .ok (call mem f args s st).2.1 := by
  have h := call_writes_within mem f args s st
  revert h
  cases hf : f.outBuffer with
  | none => intro h; exact .inl h
  | some p =>
    intro h
    rcases h with h | ⟨b, _, hw⟩
    · exact .inl h
    · exact .inr ⟨_, b, hw⟩

/-- A host function set for `Wasi.load`'s `extra` names. -/
def accepts (mo nm : String) : Bool := mo == moduleName && (Import.ofName? nm).isSome

/-- Serve `foafnaut_dom.nm`. `Wasi.resolve` checks the types of WASI imports only, so
the arguments are checked here: `f.arity` values, all i32. -/
def serve (mem : Nat) (nm : String) (args : Array Value) (s : State) (st : StoreOf M) :
    State × StoreOf M × HostResult :=
  match Import.ofName? nm with
  | none => (s, st, .trap s!"no host function {moduleName}.{nm}")
  | some f =>
    if args.size != f.arity || args.any (fun v => match v with | .i32 _ => false | _ => true) then
      (s, st, .trap s!"{moduleName}.{nm}: wrong arguments")
    else call mem f args s st

end
end L4Factoidal.WasmVM.Hosts.Dom
