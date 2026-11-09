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
import L4Factoidal.PageGpu.Wire
import L4Factoidal.PageCanvas.Wire
import L4Factoidal.DOM.Selectors
import Std.Data.HashMap
import L4Factoidal.DOM.OfHtml
import L4Factoidal.DOM.OfXml
import L4Factoidal.DOM.Forms
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.HTML.Frames
import L4Factoidal.DOM.Live
import L4Factoidal.DOM.Fragment

namespace L4Factoidal.WasmVM.Hosts.Dom
open L4Factoidal.WasmVM L4Factoidal.DOM

def moduleName : String := "foafnaut_dom"

/-- A typed DOM command: what the page did to the arena. Each one is a DOM algorithm of
`DOM.Arena`; a node a command makes is the next node of the arena, so the same list
replayed over the same parsed document makes the same node numbers
(`labs/demos/foafnaut/WebRenderScript.lean` replays it for layout). -/
inductive Command where
  /-- `textContent` of any node (the data of a CharacterData node). -/
  | setTextContent (node : Nat) (value : String)
  | setAttribute (node : Nat) (name value : String)
  /-- `createElement(name)` made node `result`. -/
  | createElement (name : String) (result : Nat)
  | appendChild (parent child : Nat)
  | removeAttribute (node : Nat) (name : String)
  /-- A node of `createKind` (kind + 16 × document; see there). -/
  | createNode (kind : Nat) (data : String) (result : Nat)
  /-- `createElementNS(namespace, qualifiedName)`; the namespace "" is null. -/
  | createElementNS (ns qname : String) (result : Nat)
  | insertBefore (parent node : Nat) (child : Option Nat)
  | removeChild (parent child : Nat)
  | replaceChild (parent node child : Nat)
  | cloneNode (node : Nat) (deep : Bool) (result : Nat)
  | normalize (node : Nat)
  /-- `setAttributeNS(namespace, qualifiedName, value)`; the namespace "" is null. -/
  | setAttributeNS (node : Nat) (ns qname value : String)
  /-- `removeAttributeNS(namespace, localName)`; the namespace "" is null. -/
  | removeAttributeNS (node : Nat) (ns lname : String)
  /-- `document.adoptNode(node)` of document `doc`. -/
  | adoptNode (node doc : Nat)
  /-- `document.importNode(node, deep)` of document `doc` made node `result`. -/
  | importNode (node doc : Nat) (deep : Bool) (result : Nat)
  /-- The checkedness of an `input` set to `value` (`DOM.Forms.setChecked`). -/
  | setChecked (node : Nat) (value : Bool)
  /-- The reset algorithm of form `node` (`DOM.Forms.resetForm`). -/
  | resetForm (node : Nat)
  /-- "Replace data" (DOM §4.10) of CharacterData `node`: `count` UTF-16 code units at
  `offset` by `data` (`CharacterData.replaceData` and the methods built on it, and the
  Range algorithms). -/
  | replaceData (node offset count : Nat) (data : String)
  /-- `splitText(offset)` (DOM §4.11) of Text `node` made node `result`. -/
  | splitText (node offset result : Nat)
  /-- `iframe` element `el` got a document: the one the HTML parser (the XML parser with
  `xml`, for an XHTML document) makes from `source`, or `about:blank` for ""; its document
  node is `root` (`Dom.graft`, the next node numbers). So a replay over the parsed page
  makes the same node numbers after a frame loads. -/
  | frameDocument (el : Nat) (source : String) (xml : Bool) (root : Nat)
  deriving BEq, Repr, Inhabited

/-- A request to the event loop. -/
inductive Request where
  /-- Run `callback` with the target node when an event `type` is dispatched to `node`. -/
  | listen (node : Nat) (type : String) (callback : Nat)
  /-- Run `callback` after `delayMs`; again every `delayMs` when `repeating`. -/
  | timer (id callback delayMs : Nat) (repeating : Bool)
  | clearTimer (id : Nat)
  deriving BEq, Repr, Inhabited

/-- What recording a command reads of the arena before the change (`change`, `commit`): the
key of the write (`Command.writeKey`), the earlier command it takes the place of, and the
live ranges after it. -/
structure Pre where
  key : Option (Nat × String) := none
  prior : Option Nat := none
  live : L4Factoidal.DOM.Live.Live := {}
  deriving Inhabited

/-- The host's state: the arena and what the page asked for. -/
structure State where
  dom : Dom
  /-- The commands, compacted (`addCommand`): a write of an attribute or of character
  data takes the place of the last write of the same one, so the list is bounded by the
  DOM's size, not by the number of changes. -/
  commands : Array Command := #[]
  /-- Changes recorded since the start, including those that took the place of an
  earlier write. A host lays the page out again only when this grew. -/
  changes : Nat := 0
  /-- The last write of each attribute (node, ASCII-lowercase name) and of each node's
  character data (node, ""), as its index in `commands`, since the last command that
  reads them (`Command.reads`). -/
  writes : Std.HashMap (Nat × String) Nat := {}
  requests : Array Request := #[]
  logs : Array String := #[]
  nextTimer : Nat := 1
  /-- The most commands a page may make. A page that the engine lays out keeps
  `maxCommands`, the bound of `WebRenderScript`; a test runner that lays nothing out
  may allow more. -/
  commandLimit : Nat := 4096
  /-- The most console lines a page may write (`maxLogs` by default). -/
  logLimit : Nat := 1024
  /-- The nested browsing contexts: an `iframe` element and its content document. -/
  frames : Array (Nat × Nat) := #[]
  /-- The page's GPU objects (`L4Factoidal.PageGpu`), and the host commands Lean emitted
  that the host has not taken yet (a turn of `scriptSession` takes them). -/
  gpu : L4Factoidal.PageGpu.State := {}
  gpuOut : Array L4Factoidal.PageGpu.HostCmd := #[]
  /-- The page's Canvas 2D canvases and objects (`L4Factoidal.PageCanvas`); a canvas drawn
  since the last turn gives the host its pixels in that turn (`PageCanvas.Store.hostCmds`). -/
  canvas : L4Factoidal.PageCanvas.Store := {}
  /-- Whether an `iframe` that becomes connected gets a browsing context (HTML §4.8.5).
  A host that replays the command list over the parsed document for layout keeps this
  off: a frame's document is not a command. -/
  framing : Bool := false
  /-- Navigations the page started and the embedder has not answered: an `iframe` and
  the URL of its `src` ("" for its initial `about:blank`, whose `load` event is due). -/
  navigations : Array (Nat × String) := #[]
  /-- The page's live ranges and NodeIterators (`DOM.Live`): each command moves them, only
  when there is one (`DOM.Live.Live.idle`). A range or iterator is its index. -/
  live : L4Factoidal.DOM.Live.Live := {}
  /-- The selection of the page's document (Selection API §2): its range (an index of
  `live.ranges`) and its direction (0 directionless, 1 forwards, 2 backwards). -/
  selection : Option Nat := none
  selDirection : Nat := 0
  /-- What `commit` reads of the arena before a change (`change` sets it). -/
  pre : Option Pre := none
  /-- The document's URL (the base of a frame's `src`, and the page's origin). -/
  url : String := ""
  /-- Each `iframe` element's frame (`HTML.Frames.frameOf`) as it was when its browsing
  context was made: its sandboxing flags and its document's origin. -/
  frameInfo : Array (Nat × L4Factoidal.HTML.Frames.Frame) := #[]
  /-- The embedder loads URLs for frames (it answers `navigations`). Without it, a frame
  whose `src` is a URL keeps its `about:blank` document and gets its `load` event. -/
  hostLoads : Bool := false
  /-- The window's `load` event waits for frames that are still loading (HTML §8.4 "the
  end": the document's load event is delayed by its iframes' navigations). -/
  loadWaits : Bool := false
  deriving Inhabited

/-- Bounds, as in `WebRenderScript`. -/
def maxString : Nat := 65536
def maxAttrName : Nat := 256
def maxCommands : Nat := 4096
def maxNodes : Nat := 1048576
def maxRequests : Nat := 4096
def maxLogs : Nat := 1024

/-- The imports of `foafnaut_dom`. The first 13 are those of the first build
(2026-11-08); the node imports after them came with page scripts in the engine
(`WasmVM.Hosts.Page`). -/
inductive Import where
  | getElementById | documentElement | tagName | textContentGet | textContentSet
  | getAttribute | setAttribute | createElement | appendChild | addEventListener
  | setTimer | clearTimer | consoleLog
  | nodeInfo | nodeString | nodeChildren | createNode | insertBefore | removeChild
  | replaceChild | removeAttribute | cloneNode | treeOp | nodeQuery | gpuCommand
  deriving DecidableEq, Repr, Inhabited

namespace Import

def all : List Import :=
  [getElementById, documentElement, tagName, textContentGet, textContentSet, getAttribute,
   setAttribute, createElement, appendChild, addEventListener, setTimer, clearTimer, consoleLog,
   nodeInfo, nodeString, nodeChildren, createNode, insertBefore, removeChild, replaceChild,
   removeAttribute, cloneNode, treeOp, nodeQuery, gpuCommand]

def name : Import → String
  | getElementById => "get_element_by_id" | documentElement => "document_element"
  | tagName => "tag_name" | textContentGet => "text_content_get"
  | textContentSet => "text_content_set" | getAttribute => "get_attribute"
  | setAttribute => "set_attribute" | createElement => "create_element"
  | appendChild => "append_child" | addEventListener => "add_event_listener"
  | setTimer => "set_timer" | clearTimer => "clear_timer" | consoleLog => "console_log"
  | nodeInfo => "node_info" | nodeString => "node_string" | nodeChildren => "node_children"
  | createNode => "create_node" | insertBefore => "insert_before" | removeChild => "remove_child"
  | replaceChild => "replace_child" | removeAttribute => "remove_attribute"
  | cloneNode => "clone_node" | treeOp => "tree_op" | nodeQuery => "node_query"
  | gpuCommand => "gpu_command"

/-- Number of i32 parameters; every import answers one i32. -/
def arity : Import → Nat
  | getElementById => 2 | documentElement => 1 | tagName => 3 | textContentGet => 3
  | textContentSet => 3 | getAttribute => 5 | setAttribute => 5 | createElement => 2
  | appendChild => 2 | addEventListener => 4 | setTimer => 3 | clearTimer => 1 | consoleLog => 2
  | nodeInfo => 2 | nodeString => 4 | nodeChildren => 4 | createNode => 3 | insertBefore => 3
  | removeChild => 2 | replaceChild => 3 | removeAttribute => 3 | cloneNode => 2 | treeOp => 3
  | nodeQuery => 6 | gpuCommand => 6

def type (f : Import) : FuncType := ⟨Array.replicate f.arity .i32, #[.i32]⟩

def ofName? (s : String) : Option Import := all.find? (·.name == s)

/-- The argument positions of the output buffer (pointer, capacity), for the imports
that write a string into VM memory. -/
def outBuffer : Import → Option (Nat × Nat)
  | tagName => some (1, 2) | textContentGet => some (1, 2) | getAttribute => some (3, 4)
  | nodeString => some (2, 3) | nodeChildren => some (2, 3) | nodeQuery => some (4, 5)
  | gpuCommand => some (4, 5)
  | _ => none

theorem all_length : all.length = 25 := rfl
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
  | .hierarchyRequest => -4
  | .notFound => -9
  | .notSupported => -10
  | .namespace => -11

def isElement (d : Dom) (n : Nat) : Bool := n < d.size && (d.get n).type == .element

/-- A namespaced attribute argument: "namespace U+0000 name" (the namespace "" is
null). A name with no U+0000 is not namespaced: no valid name contains U+0000. -/
def nsName? (name : String) : Option (Option String × String) :=
  match name.splitOn "\x00" with
  | [ns, q] => some (if ns.isEmpty then none else some ns, q)
  | _ => none

/-- The value of attribute `name` of element `n`: `getAttribute(qualifiedName)`, or
`getAttributeNS(namespace, localName)` for "namespace U+0000 localName". -/
def attrValue? (d : Dom) (n : Nat) (name : String) : Option String :=
  match nsName? name with
  | some (ns, l) => d.getAttributeNS? n ns l
  | none =>
    let q := if (d.get n).ns == some htmlNS && (d.get (d.get n).doc).htmlDoc then Dom.asciiLower name else name
    ((d.get n).attrs.find? (fun a => a.qname == q)).map (·.value)

/-- The first HTML element named `name` in tree order. -/
def firstNamed (d : Dom) (name : String) : Option Nat :=
  (d.treeOrder 0 false).find? fun k => Dom.isHtmlElement (d.get k) name

/-- Write `b` at `buf` when it fits in `cap` bytes, nothing otherwise; answer its length.
A pointer outside memory traps. -/
def putOut (mem : Nat) (st : StoreOf M) (buf cap : Nat) (b : ByteArray) : StoreOf M × HostResult :=
  if b.size ≤ cap then
    match st.writeMemS mem buf b with
    | (st', true) => (st', ret b.size)
    | (st', false) => (st', .trap "foafnaut_dom: out of bounds memory access")
  else (st, ret b.size)

/-- A string result, or an error code (nothing written). -/
def answerStr (mem : Nat) (st : StoreOf M) (buf cap : Nat) : Except Int String → StoreOf M × HostResult
  | .ok s => putOut mem st buf cap s.toUTF8
  | .error e => (st, ret e)

/-- A trap for an argument string outside memory, otherwise the code. -/
def codeOrTrap (e : Int) : HostResult := if e == -8 then .trap "foafnaut_dom: string outside memory" else ret e

/-- Character data: the nodes whose `textContent` setter changes only their data. -/
def charData (d : Dom) (n : Nat) : Bool := Dom.isCharacterData (d.get n)

/-- What a command writes and nothing else reads until it is written again: an
attribute (node, ASCII-lowercase name: the names that may be one attribute) or the
data of a character data node (node, ""; an attribute name is never empty). `d` is the
arena before the command. -/
def Command.writeKey (d : Dom) : Command → Option (Nat × String)
  | .setAttribute n k _ => some (n, Dom.asciiLower k)
  | .removeAttribute n k => some (n, Dom.asciiLower k)
  | .setTextContent n _ => if charData d n then some (n, "") else none
  | _ => none

/-- `c` writes the same thing as `p` in the same way: the same attribute name, or the
same node's data. Then `c` may take `p`'s place. -/
def Command.sameWrite : Command → Command → Bool
  | .setAttribute n k _, .setAttribute m j _ => n == m && k == j
  | .removeAttribute n k, .removeAttribute m j => n == m && k == j
  | .setTextContent n _, .setTextContent m _ => n == m
  | _, _ => false

/-- The commands that read attributes or character data (`cloneNode`, `importNode`,
`normalize`), the namespaced attribute writes (whose attribute may be one that
`writeKey` names otherwise), and `adoptNode` (a node's document decides how
`setAttribute` names an attribute), and the form state commands (which read `type`,
`name` and the tree): a write before one of them stays before it. -/
def Command.reads : Command → Bool
  | .cloneNode .. | .importNode .. | .normalize _ | .setAttributeNS .. | .removeAttributeNS ..
  | .adoptNode .. | .setChecked .. | .resetForm _ | .replaceData .. | .splitText .. | .frameDocument .. => true
  | _ => false

/-- `Command.live` with a NodeIterator: each step on the arena as the change leaves it. -/
def Command.liveExact (d : Dom) (lv : L4Factoidal.DOM.Live.Live) : Command → L4Factoidal.DOM.Live.Live
  | .setTextContent n v => (L4Factoidal.DOM.Live.setTextContent d lv n v).2
  | .appendChild p c => (L4Factoidal.DOM.Live.preInsert d lv c p none).2
  | .insertBefore p n c => (L4Factoidal.DOM.Live.preInsert d lv n p c).2
  | .removeChild _ c => (L4Factoidal.DOM.Live.remove d lv c).2
  | .replaceChild p n c => (L4Factoidal.DOM.Live.replace d lv c n p).2
  | .normalize n => (L4Factoidal.DOM.Live.normalize d lv n).2
  | .adoptNode n doc => (L4Factoidal.DOM.Live.adopt d lv n doc).2
  | .replaceData n o k v => (L4Factoidal.DOM.Live.replaceData d lv n o k v).2
  | .splitText n o _ => (L4Factoidal.DOM.Live.splitText d lv n o).2.1
  | _ => lv

/-- `Command.live` with live ranges only: the steps read from the arena before the change
(`DOM.Live.fastRemove`, ...), so no arena is copied for them. -/
def Command.liveFast (d : Dom) (lv : L4Factoidal.DOM.Live.Live) : Command → L4Factoidal.DOM.Live.Live
  | .setTextContent n v =>
    if charData d n then L4Factoidal.DOM.Live.fastReplaceData d lv n 0 (L4Factoidal.DOM.Range.utf16Length (d.get n).data) v
    else if (d.get n).type == .element || (d.get n).type == .fragment then L4Factoidal.DOM.Live.fastReplaceAll d lv n
    else lv
  | .appendChild p c => L4Factoidal.DOM.Live.fastPreInsert d lv c p none
  | .insertBefore p n c => L4Factoidal.DOM.Live.fastPreInsert d lv n p c
  | .removeChild _ c => L4Factoidal.DOM.Live.fastRemove d lv c
  | .replaceChild p n c => L4Factoidal.DOM.Live.fastReplace d lv c n p
  | .adoptNode n _ => L4Factoidal.DOM.Live.fastRemove d lv n
  | .replaceData n o k v => L4Factoidal.DOM.Live.fastReplaceData d lv n o k v
  | c => c.liveExact d lv

/-- The live ranges and NodeIterators after command `c`, run on arena `d` (the arena before
it): `DOM.Live` follows the standard's steps for the change. -/
def Command.live (d : Dom) (lv : L4Factoidal.DOM.Live.Live) (c : Command) : L4Factoidal.DOM.Live.Live :=
  if lv.iters.isEmpty then c.liveFast d lv else c.liveExact d lv


/-- Record command `c`, whose result is the arena `d`. A write of an attribute or of
character data whose last write since the last reading command (`Command.reads`) is
of the same kind (`Command.sameWrite`) takes that write's place in the list: no
command between them reads what they write, so the replay gives the same arena, with
attributes in the order of their first write. So a page that animates attributes keeps
a list bounded by its DOM, and the 4096-command bound counts distinct writes. -/
def addCommand (s : State) (c : Command) (d : Dom) : State × HostResult :=
  if d.size > maxNodes then (s, ret (-5)) else
  -- a page with no live range and no NodeIterator runs no live step
  let live := fun (s : State) => if s.live.idle then s.live else c.live s.dom s.live
  let key := c.writeKey s.dom
  let prior := (key.bind s.writes.get?).filter fun i =>
    match s.commands[i]? with
    | some p => p.sameWrite c
    | none => false
  match prior with
  | some i => ({ s with live := live s, dom := d, commands := s.commands.set! i c, changes := s.changes + 1 }, ret 0)
  | none =>
    if s.commands.size ≥ s.commandLimit then (s, ret (-5)) else
    let writes := if c.reads then {} else match key with
      | some k => s.writes.insert k s.commands.size
      | none => s.writes
    ({ s with live := live s, dom := d, commands := s.commands.push c, changes := s.changes + 1, writes }, ret 0)

/-- A node argument: -1 (any value of 2^31 or more) is none. -/
def optNode (v : Nat) : Option Nat := if v ≥ 2147483648 then none else some v

def isNode (d : Dom) (n : Nat) : Bool := n < d.size

/-- `addCommand` that answers `r` in place of 0 on success. -/
def addCommandAnswer (s : State) (c : Command) (d : Dom) (r : Int) : State × HostResult :=
  match addCommand s c d with
  | (s', .values #[.i32 0]) => (s', ret r)
  | other => other

/-- The command that `c` takes the place of (`addCommand`). -/
def priorOf (s : State) (c : Command) (key : Option (Nat × String)) : Option Nat :=
  (key.bind s.writes.get?).filter fun i =>
    match s.commands[i]? with
    | some p => p.sameWrite c
    | none => false

/-- Record command `c` of the change that made `d`, with what `change` read before it
(`s.pre`), answering `r`: as `addCommand`. -/
def commit (s : State) (c : Command) (d : Dom) (r : Int) : State × HostResult :=
  let p := s.pre.getD {}
  match p.prior with
  | some i => ({ s with pre := none, live := p.live, dom := d, commands := s.commands.set! i c, changes := s.changes + 1 }, ret r)
  | none =>
    let writes := if c.reads then {} else match p.key with
      | some k => s.writes.insert k s.commands.size
      | none => s.writes
    ({ s with pre := none, live := p.live, dom := d, commands := s.commands.push c, changes := s.changes + 1, writes }, ret r)

/-- Run the change `f` of a command like `c0` on the arena, in place: what recording reads
of the arena before the change is read first (into `s.pre`), and the budgets are checked;
then the arena leaves the state, so that `f` holds the only reference and `Array` changes
it in place (no copy of the arena per change). `f` answers the command made and the
answer, `none` for no change, or a DOM error with the arena as it was. -/
def change (s : State) (c0 : Command) (f : Dom → Dom × Except DomError (Option (Command × Int))) : State × HostResult :=
  let key := c0.writeKey s.dom
  let prior := priorOf s c0 key
  if s.dom.size > maxNodes || (prior.isNone && s.commands.size ≥ s.commandLimit) then (s, ret (-5)) else
  let s := { s with pre := some { key, prior, live := if s.live.idle then s.live else c0.live s.dom s.live } }
  let dom := s.dom
  let s := { s with dom := {} }
  match f dom with
  | (d, .error e) => ({ s with dom := d, pre := none }, ret (domErr e))
  | (d, .ok none) => ({ s with dom := d, pre := none }, ret 0)
  | (d, .ok (some (c, r))) => commit s c d r

/-- A change that always succeeds. -/
def changed (c : Command) (d : Dom) (r : Int := 0) : Dom × Except DomError (Option (Command × Int)) := (d, .ok (some (c, r)))

/-- A change by an arena operation that can throw. -/
def changedRes (c : Command) : Res Unit → Dom × Except DomError (Option (Command × Int))
  | (d, .ok ()) => (d, .ok (some (c, 0)))
  | (d, .error e) => (d, .error e)

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
  if !isNode s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) maxString with
  | .error e => (s, codeOrTrap e)
  | .ok v =>
    -- On a document or doctype, setting `textContent` does nothing (DOM §4.4).
    let t := (s.dom.get n).type
    if t == .document || t == .doctype then (s, ret 0)
    -- The same data again changes nothing: no command, no layout; live ranges in it still
    -- move, as "replace data" says (DOM §4.10).
    else if charData s.dom n && (s.dom.get n).data == v then
      if s.live.idle then (s, ret 0) else ({ s with live := (Command.setTextContent n v).live s.dom s.live }, ret 0)
    else change s (.setTextContent n v) fun d => changed (.setTextContent n v) (d.setTextContent n v)

/-- A frame's `src` value parsed against the page's URL (HTML §4.8.5 "process the iframe
attributes": "parse a URL"), as its href; the value itself when it does not parse. -/
def frameURL (s : State) (v : String) : String :=
  match L4Factoidal.WHATWG.URL.parseUrl v (if s.url.isEmpty then none else some s.url) with
  | some u => u.href
  | none => v

def setAttribute (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) (maxAttrName + maxString), readStr mem st (arg args 3) (arg args 4) maxString with
  | .error e, _ => (s, codeOrTrap e)
  | _, .error e => (s, codeOrTrap e)
  | .ok name, .ok v =>
    -- The same value again changes nothing: no command, no layout.
    let record := fun (c : Command) (op : Dom → Res Unit) (d : Dom) =>
      let old := (d.get n).attrs
      match op d with
      | (d, .error e) => (d, .error e)
      | (d, .ok ()) => (d, .ok (if (d.get n).attrs == old then none else some (c, 0)))
    match nsName? name with
    | some (ns, q) =>
      if q.utf8ByteSize > maxAttrName then (s, ret (-5)) else
      let c := Command.setAttributeNS n (ns.getD "") q v
      change s c (record c fun d => d.setAttributeNS n ns q v)
    | none =>
      if name.utf8ByteSize > maxAttrName then (s, ret (-5)) else
      let c := Command.setAttribute n name v
      match change s c (record c fun d => d.setAttribute n name v) with
      | (s, r) =>
        -- HTML §4.8.5: setting `src` of an iframe with a browsing context navigates it.
        if Dom.isHtmlElement (s.dom.get n) "iframe" && Dom.asciiLower name == "src" && s.frames.any (·.1 == n) then
          ({ s with navigations := s.navigations.push (n, if s.hostLoads && !v.trimAscii.toString.isEmpty then frameURL s v else "") }, r)
        else (s, r)

def createElement (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  match readStr mem st (arg args 0) (arg args 1) maxAttrName with
  | .error e => (s, codeOrTrap e)
  | .ok name =>
    change s (.createElement name 0) fun d => match d.createElement 0 name with
      | (d, .error e) => (d, .error e)
      | (d, .ok n) => changed (.createElement name n) d n

def appendChild (args : Array Value) (s : State) : State × HostResult :=
  let p := arg args 0
  let c := arg args 1
  if !isElement s.dom p || !isElement s.dom c then (s, ret (-2)) else
  change s (.appendChild p c) fun d => changedRes (.appendChild p c) (d.appendChild p c)

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
  | .ok t => if s.logs.size ≥ s.logLimit then (s, ret (-5)) else ({ s with logs := s.logs.push t }, ret 0)


/-! ## Frames: origins and the sandbox (`HTML.Frames`) -/

open L4Factoidal.HTML.Frames in
/-- The origin of the page's document: of its URL, or an opaque origin of its own. -/
def pageOrigin (s : State) : L4Factoidal.HTML.Frames.Origin := originOfString s.url 999999999

open L4Factoidal.HTML.Frames in
/-- The frame of `iframe` element `el` whose container document has `parent`: the one kept
when its browsing context was made, else `frameOf` its attributes now (its `src` resolved
against the page's URL). A sandboxed origin's identity is `el` + 10^9: one per element. -/
def frameFor (s : State) (parent : L4Factoidal.HTML.Frames.Frame) (el : Nat) : L4Factoidal.HTML.Frames.Frame :=
  match s.frameInfo.find? (·.1 == el) with
  | some (_, f) => f
  | none =>
    let src := (attrValue? s.dom el "src").map fun v => match L4Factoidal.WHATWG.URL.parseUrl v (if s.url.isEmpty then none else some s.url) with
      | some u => u.href
      | none => v
    frameOf parent.flags parent.origin (attrValue? s.dom el "sandbox") (attrValue? s.dom el "srcdoc") src (1000000000 + el)

open L4Factoidal.HTML.Frames in
/-- The frame of a document: the page's (no flags, `pageOrigin`), or, for a frame's
document, its `iframe`'s, through at most `fuel` containing frames. -/
def docFrameGo (s : State) : Nat → Nat → L4Factoidal.HTML.Frames.Frame
  | 0, _ => { flags := {}, origin := pageOrigin s }
  | f + 1, doc =>
    match s.frames.find? (·.2 == doc) with
    | some (el, _) => frameFor s (docFrameGo s f (s.dom.get el).doc) el
    | none => { flags := {}, origin := pageOrigin s }

def docFrame (s : State) (doc : Nat) : L4Factoidal.HTML.Frames.Frame := docFrameGo s (s.frames.size + 1) doc

/-- The frame of `iframe` element `el`. -/
def elementFrame (s : State) (el : Nat) : L4Factoidal.HTML.Frames.Frame :=
  frameFor s (docFrame s (s.dom.get el).doc) el

/-- The page's scripts (one realm, the page's) may reach the document of `iframe` `el`:
same origin (`HTML.Frames.mayAccess`); a sandboxed frame without `allow-same-origin` has an
opaque origin and is never reached (`HTML.Frames.sandboxed_no_access`). -/
def frameAccessible (s : State) (el : Nat) : Bool :=
  L4Factoidal.HTML.Frames.mayAccess (pageOrigin s) (elementFrame s el).origin

/-- The scripts of the document of `iframe` `el` run in the page's realm: its document is
one the page may reach (the same origin) and its scripts may run. A sandboxed frame's
scripts never run there (`HTML.Frames.scripts_need_allow`, `sandboxed_no_access`). -/
def frameScriptsInRealm (s : State) (el : Nat) : Bool :=
  frameAccessible s el && (elementFrame s el).scriptsMayRun

/-- Isolation: a frame's scripts run in the page's realm only when the page may reach the
frame's document (the same origin) and the frame's sandbox allows scripts. -/
theorem frameScriptsInRealm_sameOrigin (s : State) (el : Nat) (h : frameScriptsInRealm s el = true) :
    frameAccessible s el = true ∧ (elementFrame s el).scriptsMayRun = true := by
  simpa [frameScriptsInRealm] using h

/-- The state of `iframe` `el` as bits (`node_info` 29): 1 its document is reachable, 2
scripts may run, 4 forms may submit, 8 popups, 16 top-level navigation, 32 modals, 64 it
has a browsing context (it is connected in a document that has one). -/
def frameBits (s : State) (el : Nat) : Nat :=
  let f := elementFrame s el
  (if frameAccessible s el then 1 else 0) + (if f.scriptsMayRun then 2 else 0) + (if f.formsMaySubmit then 4 else 0) +
  (if f.popupsAllowed then 8 else 0) + (if f.topNavigationAllowed false then 16 else 0) +
  (if f.modalsAllowed then 32 else 0) + (if s.frames.any (·.1 == el) then 64 else 0)

/-! ## Node imports (page scripts in the engine) -/

/-- `node_info(node, which)`: 0 `nodeType`; 1 parent; 2 first child; 3 last child;
4 previous sibling; 5 next sibling; 6 number of children; 7 node document; 8 1 when an
HTML element of an HTML document, else 0; 9 the template contents of a `template`
element; 10 1 for an HTML document; 11 the content document of an `iframe` element; 12
the `iframe` element whose content document this is (11 only for a frame whose document's
origin is the page's: `frameAccessible`); 29 an `iframe`'s frame (`frameBits`). -1 none, -2
no such node. -/
def nodeInfo (args : Array Value) (s : State) : State × HostResult :=
  let d := s.dom
  let n := arg args 0
  if !isNode d n then (s, ret (-2)) else
  let x := d.get n
  let opt := fun (o : Option Nat) => match o with | some k => (s, ret k) | none => (s, ret (-1))
  match arg args 1 with
  | 0 => (s, ret x.type.code)
  | 1 => opt x.parent
  | 2 => opt x.kids[0]?
  | 3 => opt x.kids.back?
  | 4 => opt (d.previousSibling n)
  | 5 => opt (d.nextSibling n)
  | 6 => (s, ret x.kids.size)
  | 7 => (s, ret (if x.type == .document then n else x.doc))
  | 8 => (s, ret (if x.type == .element && x.ns == some htmlNS && (d.get x.doc).htmlDoc then 1 else 0))
  | 9 => opt x.content
  | 10 => (s, ret (if x.htmlDoc then 1 else 0))
  | 11 => opt ((s.frames.find? (·.1 == n && frameAccessible s n)).map (·.2))
  | 12 => opt ((s.frames.find? (·.2 == n)).map (·.1))
  | 29 => if Dom.isHtmlElement x "iframe" then (s, ret (frameBits s n)) else (s, ret (-1))
  | _ => (s, ret (-2))

/-- `nodeName` (DOM §4.4). -/
def nodeName (d : Dom) (n : Nat) : String :=
  let x := d.get n
  match x.type with
  | .element =>
    let q := match x.pfx with | some p => p ++ ":" ++ x.lname | none => x.lname
    if x.ns == some htmlNS && (d.get x.doc).htmlDoc then q.toUpper else q
  | .text => "#text" | .cdata => "#cdata-section" | .comment => "#comment"
  | .document => "#document" | .fragment => "#document-fragment"
  | .doctype | .pi => x.lname

/-- `node_string(node, which, buf, cap)`: 0 local name (the name of a doctype, the
target of a processing instruction); 1 `nodeName`; 2 namespace; 3 data; 4
`textContent`; 5 prefix; 6 the attributes, name and value, each followed by U+0000; 7
public id and 8 system id of a doctype; 9 the content type of a document. -/
def nodeStringOf (d : Dom) (n which : Nat) : Except Int String :=
  if !isNode d n then .error (-2) else
  let x := d.get n
  let opt := fun (o : Option String) => match o with | some v => Except.ok v | none => .error (-1)
  match which with
  | 0 => .ok x.lname
  | 1 => .ok (nodeName d n)
  | 2 => opt x.ns
  | 3 => if Dom.isCharacterData x then .ok x.data else .error (-1)
  | 4 => opt (d.textContent n)
  | 5 => opt x.pfx
  | 6 => .ok (x.attrs.foldl (fun acc a => acc ++ a.qname ++ "\x00" ++ a.value ++ "\x00") "")
  | 7 => .ok x.pubId
  | 8 => .ok x.sysId
  | 9 => if x.type != .document then .error (-1)
    else .ok (if !x.contentType.isEmpty then x.contentType else if x.htmlDoc then "text/html" else "application/xml")
  | _ => .error (-2)

def le32 (v : Nat) : ByteArray := ⟨#[(v % 256).toUInt8, (v / 256 % 256).toUInt8, (v / 65536 % 256).toUInt8, (v / 16777216 % 256).toUInt8]⟩

/-- A list of i32 values as little-endian bytes; the answer of `putOut` counts bytes, so
an i32 list answers its length in values (`answerList`). -/
def i32Bytes (xs : Array Nat) : ByteArray := xs.foldl (fun b v => b ++ le32 v) ByteArray.empty

/-- Write a list of i32 values when it fits, and answer its length in values. -/
def answerList (mem : Nat) (st : StoreOf M) (buf cap : Nat) : Except Int (Array Nat) → StoreOf M × HostResult
  | .ok xs =>
    let r := putOut mem st buf cap (i32Bytes xs)
    (r.1, match r.2 with | .values #[.i32 _] => ret xs.size | other => other)
  | .error e => (st, ret e)

/-- `createElementNS` (DOM §4.5) in document `doc`: "validate and extract"
(`Dom.validateAndExtract`), then an element with that namespace, prefix and local name
(no custom elements). The namespace "" is null. -/
def createElementNS (d : Dom) (ns qname : String) (doc : Nat := 0) : Except DomError (Dom × Nat) := do
  let (ns, pfx, lname) ← Dom.validateAndExtract (some ns) qname false
  return d.create { type := .element, doc, ns, pfx, lname }

/-- A new document node (its own node document); `html` for an HTML document. -/
def newDocument (d : Dom) (html : Bool) : Dom × Nat :=
  let (d, doc) := d.push { type := .document, htmlDoc := html }
  (d.setNode doc fun n => { n with doc := doc }, doc)

/-- `createHTMLDocument(title)` (DOM §4.5.1): a doctype, `html`, `head`, the `title` with
its text when a title is given, and `body`. -/
def createHTMLDocument (d : Dom) (title : Option String) : Dom × Nat := Id.run do
  let (d, doc) := newDocument d true
  let el := fun (d : Dom) (name : String) => d.create { type := .element, doc, ns := some htmlNS, lname := name }
  let (d, dt) := d.create { type := .doctype, doc, lname := "html" }
  let d := d.linkChild doc dt none
  let (d, html) := el d "html"
  let d := d.linkChild doc html none
  let (d, head) := el d "head"
  let d := d.linkChild html head none
  let d := match title with
    | some t =>
      let (d, te) := el d "title"
      let d := d.linkChild head te none
      let (d, tx) := d.createTextNode doc t
      d.linkChild te tx none
    | none => d
  let (d, body) := el d "body"
  return (d.linkChild html body none, doc)

/-- `DOMParser.parseFromString(source, type)` for an XML type (HTML §8.5.1.1): the
document the XML parser makes, with that content type; when the source is not
namespace-well-formed, a document whose element is a `parsererror` element (in the
namespace browsers use for it) with the parser's message. -/
def parsererrorNS : String := "http://www.mozilla.org/newlayout/xml/parsererror.xml"

def xmlDocument (contentType source : String) : Dom :=
  let d := match parseXmlDocument source with
    | .ok d => d
    | .error msg => Id.run do
      let d : Dom := { nodes := #[{ type := .document, doc := 0, htmlDoc := false }] }
      let el0 : Node := { type := .element, doc := 0, ns := some parsererrorNS, lname := "parsererror" }
      let (d, el) := d.create el0
      let d := d.linkChild 0 el none
      let (d, t) := d.createTextNode 0 msg
      return d.linkChild el t none
  d.setNode 0 fun n => { n with contentType := contentType }

/-- `create_node(kind + 16 × doc, data)`: the node a script makes, in document `doc`.
Kinds: 0 `createTextNode`, 1 `createComment`, 2 `createDocumentFragment`, 3
`createElement`, 4 `createElementNS` (`data` is namespace, U+0000, qualified name), 5
`createProcessingInstruction` (target, U+0000, data), 6 `createCDATASection`, 7
`createHTMLDocument` with the title `data`, 10 the same with no title, 8 an XML document
(`createDocument`, `new Document()`), 9 `createDocumentType` (name, U+0000, public id,
U+0000, system id), 11 a document the HTML parser makes from `data` and 12 one the XML
parser makes (content type, U+0000, source) (`DOMParser`), 13 the DocumentFragment that the
HTML fragment parsing algorithm makes of a source for a context element (namespace, U+0000,
local name, U+0000, source; `DOM.Fragment.parseInto`: `innerHTML`, `outerHTML`,
`insertAdjacentHTML`, `createContextualFragment`). -/
def createKind (d : Dom) (kind : Nat) (data : String) : Res Nat :=
  let doc := kind / 16
  let ok := fun (r : Dom × Nat) => ((r.1, .ok r.2) : Res Nat)
  if kind % 16 ∉ [7, 8, 10, 11, 12] && (doc ≥ d.size || (d.get doc).type != .document) then (d, .error .notSupported) else
  match kind % 16, data.splitOn "\x00" with
  | 0, _ => ok (d.createTextNode doc data)
  | 1, _ => ok (d.createComment doc data)
  | 2, _ => ok (d.createDocumentFragment doc)
  | 3, _ => d.createElement doc data
  | 4, [ns, q] => match createElementNS d ns q doc with
    | .ok r => ok r
    | .error e => (d, .error e)
  | 5, [target, body] => d.createProcessingInstruction doc target body
  | 6, _ => d.createCDATASection doc data
  | 7, _ => ok (createHTMLDocument d (some data))
  | 10, _ => ok (createHTMLDocument d none)
  | 8, _ =>
    -- `createDocument(namespace, …)` (DOM §4.5.1 steps 5-7): the content type follows
    -- the namespace given as `data`.
    let (d, doc) := newDocument d false
    let ct := if data == htmlNS then "application/xhtml+xml" else if data == svgNS then "image/svg+xml" else ""
    ok (d.setNode doc fun n => { n with contentType := ct }, doc)
  | 9, [name, pub, sys] => d.createDocumentType doc name pub sys
  | 11, _ => ok (d.graft (parseHtmlDocument data))
  | 12, ct :: rest => ok (d.graft (xmlDocument ct ("\x00".intercalate rest)))
  | 13, ns :: name :: rest => ok (L4Factoidal.DOM.Fragment.parseInto d doc ns name ("\x00".intercalate rest))
  | _, _ => (d, .error .invalidCharacter)

def createNode (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  match readStr mem st (arg args 1) (arg args 2) maxString with
  | .error e => (s, codeOrTrap e)
  | .ok data =>
    let kind := arg args 0
    change s (.createNode kind data 0) fun d => match createKind d kind data with
      | (d, .error e) => (d, .error e)
      | (d, .ok n) =>
        -- `createElement` of the page's own document keeps its first command form.
        changed (if kind == 3 then Command.createElement data n else Command.createNode kind data n) d n

/-- The document of an `iframe` with no `src` (HTML §7.3.1 "about:blank"): an HTML
document with `html`, `head` and `body` and no doctype. -/
def aboutBlank : Dom := Id.run do
  let el := fun (d : Dom) (name : String) => d.create { type := .element, doc := 0, ns := some htmlNS, lname := name }
  let d : Dom := { nodes := #[{ type := .document, doc := 0 }] }
  let (d, html) := el d "html"
  let d := d.linkChild 0 html none
  let (d, head) := el d "head"
  let d := d.linkChild html head none
  let (d, body) := el d "body"
  return d.linkChild html body none

/-- The `src` URL of an `iframe` element, when it has a non-empty one. -/
def frameSrc (d : Dom) (el : Nat) : Option String :=
  match attrValue? d el "src" with
  | some v => if v.trimAscii.toString.isEmpty then none else some v
  | none => none

/-- HTML §4.8.5 "iframe insertion steps", for the nodes `inserted` (each with its
subtree): each `iframe` element that is now connected, in a document that has a browsing
context (the page's or a frame's), and has no browsing context of its own gets
one, with an `about:blank` document (`Dom.graft`), and its navigation: its `src` URL, or
"" (the `load` event of `about:blank`). Only with `framing`. -/
def connectFrames (s : State) (inserted : Array Nat) : State := Id.run do
  if !s.framing then return s
  let mut s := s
  for top in inserted do
    -- only in a document with a browsing context: the page's, or a frame's
    let root := s.dom.root top
    if (s.dom.get root).type != .document || !(root == 0 || s.frames.any (·.2 == root)) then continue
    for k in s.dom.treeOrder top do
      if Dom.isHtmlElement (s.dom.get k) "iframe" && !(s.frames.any (·.1 == k)) then
        let (d, doc) := s.dom.graft aboutBlank
        -- the frame's flags and origin as they are now (HTML §4.8.5: kept until it navigates)
        let info := frameFor s (docFrame s root) k
        -- HTML §4.8.5 "process the iframe attributes": `srcdoc` first (Lean loads it),
        -- then a `src` URL (the embedder's, when it loads URLs), else `about:blank`.
        let nav := if (attrValue? d k "srcdoc").isSome then "about:srcdoc"
          else if s.hostLoads then ((frameSrc d k).map (frameURL s)).getD "" else ""
        match addCommand s (.frameDocument k "" false doc) d with
        | (s', .values #[.i32 0]) =>
          s := { s' with frames := s'.frames.push (k, doc), frameInfo := s'.frameInfo.push (k, info),
                         navigations := s'.navigations.push (k, nav) }
        | _ => pure ()
  return s

/-- A frame's document from its source: `about:blank` for "", else what the HTML parser
makes of it, or with `xml` the XML parser (an XHTML document; a parse error gives the
`parsererror` document of `xmlDocument`). -/
def frameArena (source : String) (xml : Bool) : Dom :=
  if source.isEmpty then aboutBlank
  else if xml then xmlDocument "application/xhtml+xml" source
  else parseHtmlDocument source

/-- A frame navigation the document's load event waits for is under way: a `src` URL for the
embedder, or a `srcdoc`. -/
def framesLoading (s : State) : Bool :=
  -- a lazy-loading frame does not delay its document's load event (HTML §4.8.5,
  -- "will lazy load element steps")
  s.navigations.any fun (el, u) => !u.isEmpty && (attrValue? s.dom el "loading").map Dom.asciiLower != some "lazy"

/-- The navigation of `iframe` `el` ends with document `source` ("" is `about:blank`):
it joins the arena (`Dom.graft`, recorded as `Command.frameDocument`), becomes the frame's
document, and the frames it holds get their own browsing contexts. The answer has the new
document node, or none when the command was refused. -/
def attachDocument (s : State) (el : Nat) (source : String) (xml : Bool := false) : State × Option Nat :=
  let s := { s with navigations := s.navigations.filter (·.1 != el) }
  if !isNode s.dom el then (s, none) else
  let (d, root) := s.dom.graft (frameArena source xml)
  match addCommand s (.frameDocument el source xml root) d with
  | (s, .values #[.i32 0]) =>
    let s := { s with frames := (s.frames.filter (·.1 != el)).push (el, root) }
    (connectFrames s #[root], some root)
  | (s, _) => (s, none)

/-- The nodes an insertion of `n` inserts: the children of a fragment, else `n`. -/
def insertedBy (d : Dom) (n : Nat) : Array Nat :=
  if (d.get n).type == .fragment then (d.get n).kids else #[n]

def insertBefore (args : Array Value) (s : State) : State × HostResult :=
  let p := arg args 0
  let n := arg args 1
  let c := optNode (arg args 2)
  if !isNode s.dom p || !isNode s.dom n || !(c.all (isNode s.dom)) then (s, ret (-2)) else
  let moved := insertedBy s.dom n
  let cmd := if c.isNone then Command.appendChild p n else .insertBefore p n c
  match change s cmd fun d => changedRes cmd (d.insertBefore p n c) with
  | (s, r) => (connectFrames s moved, r)

def removeChild (args : Array Value) (s : State) : State × HostResult :=
  let p := arg args 0
  let c := arg args 1
  if !isNode s.dom p || !isNode s.dom c then (s, ret (-2)) else
  change s (.removeChild p c) fun d => changedRes (.removeChild p c) (d.preRemove c p)

def replaceChild (args : Array Value) (s : State) : State × HostResult :=
  let p := arg args 0
  let n := arg args 1
  let c := arg args 2
  if !isNode s.dom p || !isNode s.dom n || !isNode s.dom c then (s, ret (-2)) else
  let moved := insertedBy s.dom n
  match change s (.replaceChild p n c) fun d => changedRes (.replaceChild p n c) (d.replace c n p) with
  | (s, r) => (connectFrames s moved, r)

/-- `removeAttribute(qualifiedName)` (DOM §4.9): the first attribute with that
qualified name (lower case on an HTML element of an HTML document). -/
def removeAttr (d : Dom) (n : Nat) (name : String) : Dom :=
  match nsName? name with
  | some (ns, l) => d.removeAttributeNS n ns l
  | none =>
  let x := d.get n
  let q := if x.ns == some htmlNS && (d.get x.doc).htmlDoc then Dom.asciiLower name else name
  match x.attrs.findIdx? (·.qname == q) with
  | some i => d.setNode n fun e => { e with attrs := e.attrs.eraseIdxIfInBounds i }
  | none => d

def removeAttribute (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × HostResult :=
  let n := arg args 0
  if !isElement s.dom n then (s, ret (-2)) else
  match readStr mem st (arg args 1) (arg args 2) (maxAttrName + maxString) with
  | .error e => (s, codeOrTrap e)
  | .ok name => match nsName? name with
    | some (ns, l) =>
      let c := Command.removeAttributeNS n (ns.getD "") l
      change s c fun d => changed c (d.removeAttributeNS n ns l)
    | none =>
      if name.utf8ByteSize > maxAttrName then (s, ret (-5))
      else change s (.removeAttribute n name) fun d => changed (.removeAttribute n name) (removeAttr d n name)

def cloneNode (args : Array Value) (s : State) : State × HostResult :=
  let n := arg args 0
  if !isNode s.dom n then (s, ret (-2)) else
  let deep := arg args 1 != 0
  change s (.cloneNode n deep 0) fun d => let (d, c) := d.cloneNode n deep; changed (.cloneNode n deep c) d c

/-- `tree_op(a, b, which)`: 1 `isEqualNode` (1 or 0); 2 `normalize()` of `a`; 3
`b.adoptNode(a)` (DOM §4.5: a document is NotSupportedError); 4 and 5
`b.importNode(a, deep)` (shallow, deep; the new node); 6 set the checkedness of input `a`
to `b` (1 or 0); 7 the checkedness of `a`; 8 the other checked radio button of `a`'s
group, or -1; 9 reset form `a` (DOM.Forms). -/
def treeOp (args : Array Value) (s : State) : State × HostResult :=
  let a := arg args 0
  let b := arg args 1
  if !isNode s.dom a then (s, ret (-2)) else
  let isDoc := fun (k : Nat) => (s.dom.get k).type == .document
  match arg args 2 with
  | 3 => if !isNode s.dom b || !isDoc b then (s, ret (-2)) else if isDoc a then (s, ret (-10))
    -- the template contents of a template element stay where they are
    else if (s.dom.get a).type == .fragment && (s.dom.get a).host.isSome then (s, ret 0)
    else change s (.adoptNode a b) fun d => changed (.adoptNode a b) (d.adopt a b)
  | 6 => if !Forms.isHtml s.dom a ["input"] then (s, ret (-2))
    else change s (.setChecked a (b != 0)) fun d => changed (.setChecked a (b != 0)) (Forms.setChecked d a (b != 0))
  | 7 => (s, ret (if Forms.checkedness s.dom a then 1 else 0))
  | 8 => match Forms.checkedInGroup s.dom a with | some k => (s, ret k) | none => (s, ret (-1))
  | 9 => if !Forms.isHtml s.dom a ["form"] then (s, ret (-2))
    else change s (.resetForm a) fun d => changed (.resetForm a) (Forms.resetForm d a)
  | 4 | 5 => if !isNode s.dom b || !isDoc b then (s, ret (-2)) else if isDoc a then (s, ret (-10)) else
    let deep := arg args 2 == 5
    change s (.importNode a b deep 0) fun d => let (d, c) := d.cloneNode a deep (some b); changed (.importNode a b deep c) d c
  | 1 => if !isNode s.dom b then (s, ret (-2)) else (s, ret (if s.dom.isEqualNode a b then 1 else 0))
  | 2 => change s (.normalize a) fun d => changed (.normalize a) (d.normalize a)
  | _ => (s, ret (-2))

def nodeString (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  answerStr mem st (arg args 2) (arg args 3) (nodeStringOf s.dom (arg args 0) (arg args 1))

/-- `node_children(node, _, buf, cap)`: the children, as i32 node numbers. -/
def nodeChildren (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  let n := arg args 0
  answerList mem st (arg args 2) (arg args 3) (if isNode s.dom n then .ok (s.dom.get n).kids else .error (-2))

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
  match readStr mem st (arg args 1) (arg args 2) (maxAttrName + maxString) with
  | .error e => (st, codeOrTrap e)
  | .ok name => answerStr mem st (arg args 3) (arg args 4)
      (match attrValue? s.dom n name with | some v => .ok v | none => .error (-1))

/-- `node_query(node, op, s, len, buf, cap)`: a string question about a node, a string
answer (-1 for null). Ops: 0 `lookupNamespaceURI(s)` (U+0000 alone is the prefix null);
1 `lookupPrefix(s)`; 2 the attributes of an element, each as namespace, prefix, local
name and value, each followed by U+0000 (the empty string is null); 3 "" when `s` is a
valid attribute local name, else -3; 4 "validate and extract" (DOM §1.4) of an attribute
"namespace U+0000 qualifiedName": namespace, prefix and local name, each followed by U+0000,
or the error. Ops 3 and 4 do not read the node. 5 `getElementById(s)` in the subtree of
the node (DOM §4.2.4), as a decimal node number. 6 `querySelectorAll(s)`: the node numbers,
separated by spaces; 7 `querySelector(s)`: the first, or ""; 8 `matches(s)`: "1" or "0";
9 `closest(s)`: a node number, or -1 (DOM.Selectors). An invalid selector is -12
(SyntaxError). 10 the activation target of a click dispatched to the node (`s` "1" when
it bubbles); 11 "1" for a disabled form control; 12 the URL `input` parsed against `base`
("base U+0000 input"; WHATWG URL), as its href; 13 the control a click on label node
activates for the event target `s` (a decimal node number); 14 the type state of an
`input` or `button` (DOM.Forms); 15 the HTML serialization of the node's children (`s`
"0", `innerHTML`) or of the node (`s` "1", `outerHTML`) (`DOM.Fragment.serialize`). Op 12
does not read the node. -/
def nodeQueryOf (d : Dom) (n op : Nat) (q : String) : Except Int String :=
  if op == 3 then (if Dom.validAttributeLocalName q then .ok "" else .error (-3)) else
  if op == 12 then
    match q.splitOn "\x00" with
    | [base, input] => match L4Factoidal.WHATWG.URL.parseUrl input (if base.isEmpty then none else some base) with
      | some u => .ok u.href
      | none => .error (-1)
    | _ => .error (-2)
  else
  if op == 4 then
    match nsName? q with
    | none => .error (-2)
    | some (ns, qn) => match Dom.validateAndExtract ns qn true with
      | .ok (ns, p, l) => .ok (ns.getD "" ++ "\x00" ++ p.getD "" ++ "\x00" ++ l ++ "\x00")
      | .error e => .error (domErr e)
  else
  if !isNode d n then .error (-2) else
  let opt := fun (o : Option String) => match o with | some v => Except.ok v | none => .error (-1)
  match op with
  | 0 => opt (d.lookupNamespaceURI n (if q == "\x00" then none else some q))
  | 1 => opt (d.lookupPrefix n (some q))
  | 6 | 7 => match Selectors.parse q with
    | none => .error (-12)
    | some l => .ok (" ".intercalate ((Selectors.querySelectorAll d n l (op == 7)).toList.map toString))
  | 8 => match Selectors.parse q with
    | none => .error (-12)
    | some l => .ok (if Selectors.elementMatches d n l then "1" else "0")
  | 9 => match Selectors.parse q with
    | none => .error (-12)
    | some l => match Selectors.closest d n l with
      | some k => .ok (toString k)
      | none => .error (-1)
  | 10 => match Forms.activationTarget d n (q == "1") with
    | some k => .ok (toString k)
    | none => .error (-1)
  | 11 => .ok (if Forms.disabledControl d n then "1" else "0")
  | 13 => match q.toNat? with
    | some t => if t < d.size then (match Forms.labelActivates d n t with
        | some k => .ok (toString k)
        | none => .error (-1)) else .error (-2)
    | none => .error (-2)
  | 14 => .ok (if Forms.isHtml d n ["button"] then Forms.buttonType d n else Forms.inputType d n)
  | 15 => .ok (L4Factoidal.DOM.Fragment.serialize d n (q == "1"))
  | 5 => match d.getElementById n q with
    | some k => .ok (toString k)
    | none => .error (-1)
  | 2 => .ok ((d.get n).attrs.foldl (fun acc a =>
      acc ++ a.ns.getD "" ++ "\x00" ++ a.pfx.getD "" ++ "\x00" ++ a.lname ++ "\x00" ++ a.value ++ "\x00") "")
  | _ => .error (-2)

def nodeQuery (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : StoreOf M × HostResult :=
  match readStr mem st (arg args 2) (arg args 3) maxString with
  | .error e => (st, codeOrTrap e)
  | .ok q => answerStr mem st (arg args 4) (arg args 5) (nodeQueryOf s.dom (arg args 0) (arg args 1) q)

/-- The most host commands a page may have waiting for the host. -/
def maxGpuOut : Nat := 65536

/-- One page GPU command (`L4Factoidal.PageGpu.Wire.decode`, then `PageGpu.step`): the
new state and the answer text: "" when accepted (a WebGL program: its interface, JSON,
starting with `{`), else the refusal (at most 900 bytes, so the guest's first buffer
holds it and the import runs once). -/
@[irreducible] def gpuStep (s : State) (op : Nat) (bytes : ByteArray) : State × String :=
  match L4Factoidal.PageGpu.Wire.decode op bytes >>= L4Factoidal.PageGpu.step s.gpu with
  | .ok (g, out) =>
    if s.gpuOut.size + out.length > maxGpuOut then (s, "gpu: too many commands waiting for the host")
    else
      -- A linked WebGL program answers its interface (attribute locations, uniform offsets).
      -- Only a program decodes again (a frame's write and pass do not).
      let answer := if op != 9 && op != L4Factoidal.PageGpu.Wire.binaryOp + 9 then "" else
        match L4Factoidal.PageGpu.Wire.decode op bytes with
        | .ok (.createProgram _ vs fs) =>
          match L4Factoidal.PageGpu.Glsl.compileProgram vs fs with
          | .ok (_, info) => info.json
          | .error _ => ""
        | _ => ""
      ({ s with gpu := g, gpuOut := s.gpuOut ++ out.toArray }, answer)
  | .error e => (s, String.ofList (e.toList.take 900))

/-- `gpu_command(op, unused, ptr, len, buf, cap)`. -/
def gpuCommand (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) : State × StoreOf M × HostResult :=
  if arg args 3 > L4Factoidal.PageGpu.maxBuffer + 65536 then (s, st, ret (-5)) else
  match st.readMem mem (arg args 2) (arg args 3) with
  | .error _ => (s, st, codeOrTrap (-8))
  | .ok b =>
    let r := gpuStep s (arg args 0) b
    let a := answerStr mem st (arg args 4) (arg args 5) (.ok r.2)
    (r.1, a.1, a.2)

/-- One import: the new state, the new store and the answer. -/
def call (mem : Nat) (f : Import) (args : Array Value) (s : State) (st : StoreOf M) :
    State × StoreOf M × HostResult :=
  -- no closure holds `s`: a change of the arena is then in place (`change`)
  match f with
  | .getElementById => let r := getElementById mem args s st; (r.1, st, r.2)
  | .documentElement => let r := documentElement args s; (r.1, st, r.2)
  | .tagName => let r := tagName mem args s st; (s, r.1, r.2)
  | .textContentGet => let r := textContentGet mem args s st; (s, r.1, r.2)
  | .textContentSet => let r := textContentSet mem args s st; (r.1, st, r.2)
  | .getAttribute => let r := getAttribute mem args s st; (s, r.1, r.2)
  | .setAttribute => let r := setAttribute mem args s st; (r.1, st, r.2)
  | .createElement => let r := createElement mem args s st; (r.1, st, r.2)
  | .appendChild => let r := appendChild args s; (r.1, st, r.2)
  | .addEventListener => let r := addEventListener mem args s st; (r.1, st, r.2)
  | .setTimer => let r := setTimer args s; (r.1, st, r.2)
  | .clearTimer => let r := clearTimer args s; (r.1, st, r.2)
  | .consoleLog => let r := consoleLog mem args s st; (r.1, st, r.2)
  | .nodeInfo => let r := nodeInfo args s; (r.1, st, r.2)
  | .nodeString => let r := nodeString mem args s st; (s, r.1, r.2)
  | .nodeChildren => let r := nodeChildren mem args s st; (s, r.1, r.2)
  | .createNode => let r := createNode mem args s st; (r.1, st, r.2)
  | .insertBefore => let r := insertBefore args s; (r.1, st, r.2)
  | .removeChild => let r := removeChild args s; (r.1, st, r.2)
  | .replaceChild => let r := replaceChild args s; (r.1, st, r.2)
  | .removeAttribute => let r := removeAttribute mem args s st; (r.1, st, r.2)
  | .cloneNode => let r := cloneNode args s; (r.1, st, r.2)
  | .treeOp => let r := treeOp args s; (r.1, st, r.2)
  | .nodeQuery => let r := nodeQuery mem args s st; (s, r.1, r.2)
  | .gpuCommand => gpuCommand mem args s st

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
    · rename_i st' hw; exact .inr ⟨b, h, StoreOf.writeMem_of_writeMemS hw⟩
    · rename_i st' hw; exact .inl (StoreOf.writeMemS_false hw)
  · exact .inl rfl

theorem answerStr_within (mem : Nat) (st : StoreOf M) (buf cap : Nat) (r : Except Int String) :
    WritesWithin mem buf cap st (answerStr mem st buf cap r).1 := by
  cases r with
  | ok s => exact putOut_within mem st buf cap s.toUTF8
  | error e => exact .inl rfl

theorem answerList_within (mem : Nat) (st : StoreOf M) (buf cap : Nat) (r : Except Int (Array Nat)) :
    WritesWithin mem buf cap st (answerList mem st buf cap r).1 := by
  cases r with
  | ok xs => exact putOut_within mem st buf cap (i32Bytes xs)
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

theorem nodeQuery_within (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) :
    WritesWithin mem (arg args 4) (arg args 5) st (nodeQuery mem args s st).1 := by
  unfold nodeQuery
  split
  · exact .inl rfl
  · exact answerStr_within ..

theorem gpuCommand_within (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) :
    WritesWithin mem (arg args 4) (arg args 5) st (gpuCommand mem args s st).2.1 := by
  unfold gpuCommand
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · dsimp only
      exact answerStr_within mem st (arg args 4) (arg args 5) _

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
  · exact answerStr_within ..
  · exact answerList_within ..
  · exact nodeQuery_within ..
  · exact gpuCommand_within ..

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

/-! ## Replaying commands

`Command.apply` is the change each command made, as the arena operation the import ran.
A host that keeps the command list replays it over the same parsed document to get the
same arena (`WebRenderScript.applyCommands`, before layout). A command that makes a node
names the node it made; a replay that would make another node number is refused. -/

def checkNode (d : Dom) (n : Nat) : Except String Unit :=
  if n < d.size then .ok () else .error "script command: unknown nodeId"

def made (r : Nat) : Dom × Nat → Except String Dom
  | (d, n) => if n == r then .ok d else .error "script command: replay made another node"

def res : Res Unit → Except String Dom
  | (d, .ok ()) => .ok d
  | (_, .error e) => .error s!"script command: {e.name}"

def Command.apply (d : Dom) : Command → Except String Dom
  | .setTextContent n v => do
    checkNode d n
    let t := (d.get n).type
    if t == .document || t == .doctype then throw "script command: target must not be a document"
    return d.setTextContent n v
  | .setAttribute n k v => do
    checkNode d n
    if (d.get n).type != .element then throw "script command: target must be an element"
    res (d.setAttribute n k v)
  | .createElement k r =>
    match d.createElement 0 k with
    | (d, .ok n) => made r (d, n)
    | (_, .error e) => .error s!"script command: {e.name}"
  | .appendChild p c => do checkNode d p; checkNode d c; res (d.appendChild p c)
  | .removeAttribute n k => do
    checkNode d n
    if (d.get n).type != .element then throw "script command: target must be an element"
    return removeAttr d n k
  | .createNode k data r =>
    match createKind d k data with
    | (d, .ok n) => made r (d, n)
    | (_, .error e) => .error s!"script command: {e.name}"
  | .createElementNS ns q r =>
    match L4Factoidal.WasmVM.Hosts.Dom.createElementNS d ns q with
    | .ok x => made r x
    | .error e => .error s!"script command: {e.name}"
  | .insertBefore p n c => do
    checkNode d p; checkNode d n
    if let some k := c then checkNode d k
    res (d.insertBefore p n c)
  | .removeChild p c => do checkNode d p; checkNode d c; res (d.preRemove c p)
  | .replaceChild p n c => do checkNode d p; checkNode d n; checkNode d c; res (d.replace c n p)
  | .cloneNode n deep r => do
    checkNode d n
    made r (d.cloneNode n deep)
  | .normalize n => do checkNode d n; return d.normalize n
  | .setAttributeNS n ns q v => do
    checkNode d n
    if (d.get n).type != .element then throw "script command: target must be an element"
    res (d.setAttributeNS n (some ns) q v)
  | .removeAttributeNS n ns l => do
    checkNode d n
    if (d.get n).type != .element then throw "script command: target must be an element"
    return d.removeAttributeNS n (some ns) l
  | .adoptNode n doc => do
    checkNode d n; checkNode d doc
    if (d.get doc).type != .document || (d.get n).type == .document then throw "script command: NotSupportedError"
    return d.adopt n doc
  | .setChecked n v => do
    checkNode d n
    if !Forms.isHtml d n ["input"] then throw "script command: target must be an input"
    return Forms.setChecked d n v
  | .resetForm n => do
    checkNode d n
    if !Forms.isHtml d n ["form"] then throw "script command: target must be a form"
    return Forms.resetForm d n
  | .frameDocument el source xml r => do
    checkNode d el
    made r (d.graft (frameArena source xml))
  | .importNode n doc deep r => do
    checkNode d n; checkNode d doc
    if (d.get doc).type != .document || (d.get n).type == .document then throw "script command: NotSupportedError"
    made r (d.cloneNode n deep (some doc))
  | .replaceData n o k v => do
    checkNode d n
    if !charData d n then throw "script command: target must be character data"
    if o > L4Factoidal.DOM.Range.nodeLength d n then throw "script command: IndexSizeError"
    return (L4Factoidal.DOM.Live.replaceData d {} n o k v).1
  | .splitText n o r => do
    checkNode d n
    if !Dom.isTextNode (d.get n) then throw "script command: target must be a Text node"
    if o > L4Factoidal.DOM.Range.nodeLength d n then throw "script command: IndexSizeError"
    let (d, _, k) := L4Factoidal.DOM.Live.splitText d {} n o
    made r (d, k)

-- DOMParser: an XML document, a parse error, and an HTML document joined to an arena
#guard (match createKind { nodes := #[{ type := .document }] } 12 "application/xml\x00<a xmlns='u'/>" with
  | (d, .ok r) => let e := d.get ((d.get r).kids[0]!)
    (e.lname, e.ns, (d.get r).contentType, (d.get r).htmlDoc) == ("a", some "u", "application/xml", false)
  | _ => false)
#guard (match createKind { nodes := #[{ type := .document }] } 12 "text/xml\x00<a>" with
  | (d, .ok r) => (d.get ((d.get r).kids[0]!)).lname == "parsererror"
  | _ => false)
#guard (match createKind { nodes := #[{ type := .document }] } 11 "<p>x" with
  | (d, .ok r) => r == 1 && (d.get r).htmlDoc && (d.get r).doc == r
  | _ => false)

end L4Factoidal.WasmVM.Hosts.Dom
