/-
L4Factoidal.Foafos.GuestContract — the foafos-lite guest contract: what an
app in a frame may send to the page that embeds it, level by level, and what
that page promises in return.

The contract text is `docs/foafos-lite-contract.md` in foafos (branch
`foafos-lite-contract`, draft version 1 of 2026-11-12; issue
https://github.com/danbri/glitchcan-minigam/issues/1038). An app depends on
one small module, `@foafos/guest`, and on a fixed set of `postMessage`
messages, not on foafos. Each level (0 to 3) is opt-in and is a larger
promise about what can leave the app. This module is a specification of that
text: it states definitions and proves theorems about them. The JavaScript
(`@foafos/guest`, `@foafos/host-lite`) is not written yet; that it computes
what these definitions compute will be a matter for differential tests.

## The model

* **Payloads.** What the app declares about itself (`Name`, `ActionId`,
  `Label`, `ToolDecl`, `Topic`) and what the app holds (`AppData`: storage
  contents, what the person typed, what the app computed from them) are
  separate types. A message constructor that has no `AppData` field cannot
  carry app data. `GMsg.data` lists the `AppData` values in a message.
* **Messages** (`GMsg`, guest to host; `HMsg`, host to guest) have the fields
  the text gives. A `path` is a list of segments. A received message is a
  `Wire`: the `fl` field, the window it came from, and the message, or `none`
  for an unknown `type`. `accept` keeps a message only when `fl = 1` and it
  came from the expected window.
* **The guest** (`GState`, `gstep`) is the module and the app together. The
  app's calls (`AppCall`) are inputs; so are received messages and the 500 ms
  timeout (`GIn.timeout`, also used for "not in a frame"). An output is a
  message the module sends (`GOut.send`) or one it passes to the app
  (`GOut.deliver`). The module sends only on an app call, and what it sends
  is `AppCall.toMsg`: the app's call with the level the app asked for
  (from its manifest) and, for `store`, a fresh `rid` (a counter).
  `granted` is `none` until a `welcome` arrives or the timeout; a `welcome`
  above the level asked for is ignored (see gap 4); the first `welcome` or
  the timeout fixes the level for good.
* **The host** (`HState`, `hstep`) holds the level asked and granted, the
  lifecycle states it has sent (newest first), the app's folder (`root`, a
  key prefix in its backing store), the backing store, the subscriptions,
  the person's topic grants, and the outstanding tool calls. Its inputs are
  received messages and its own decisions (`setLife`, `notify`, `busEvent`,
  `callTool`). It answers each `store` in the same step it receives it.
* **Traces.** `runFrom` runs any step function over a list of inputs and
  collects the outputs. `grun` and `hrun` are the guest's and the host's
  runs. `Ev` is a two-sided trace, used to state the text's host promises as
  predicates (`NothingAfterEnding`, `OneReplyEach`).

## What is proved

Junk: `gstep_junk`, `hstep_junk` (a message with `fl ≠ 1`, an unknown type
or from the wrong window changes no state and causes no output).

The module adds nothing: `gstep_recv_no_send`, `gstep_timeout_no_send` (the
module never sends on its own), `gstep_app_send` (what it sends is the app's
call plus the asked level and a `rid`), `toMsg_data` (the app data in the
message is exactly the app data in the call).

Levels on the guest: `gstep_pending_send` (before the level is known, only
`hello`), `gstep_granted_send` (after, nothing above the granted level and
no `hello`), `gInv_step` and `grun_le_asked` (whatever the host sends, a
sent message is never above the level asked for), `grun_level0` (level 0
sends nothing), `grun_asked0` (an app that asks for level 0 sends nothing,
ever), `grun_level1` (level 1 sends only `ready`, `actions` and `paused`,
with no app data), `level_le_one_data`, `gstep_granted_keep` (the level is
fixed once known), `gstep_store_fresh` (a `store` rid is new).

Acknowledgements and replies on the guest: `gstep_paused_owed`,
`gstep_owed_set` (the module sends `paused` only while a `lifecycle paused`
is unanswered, and only a `lifecycle paused` makes one unanswered),
`gstep_reply_unknown` (a `store-result` for a rid not outstanding is
ignored), `gstep_welcome_above` (a `welcome` above the level asked for is
ignored).

Levels on the host: `hInv_step`, `hrun_inv` (granted ≤ asked and ≤ what the
host offers), `hrun_grant_le`.

Lifecycle: `lifeOk_ending_last` (`ending` only as the last state),
`hrun_life` (the lifecycle states the host sends, in the order sent, follow
the order `running`/`paused` alternating, then `ending` at most once and
last), `hstep_after_ending` (after `ending` the host sends only
`store-result`s).

One reply per request: `hstep_reply_count`, `hrun_replies` (for each rid,
the host's replies carrying it equal the requests carrying it, and each
reply is sent in the step that receives its request).

Folder confinement: `hstep_store_outside`, `hrun_store_outside` (no key
outside the app's folder is changed), `hstep_get_inside` (a read returns
only bytes from inside the folder), `hstep_bad_path` (any other path gets
`denied` and changes nothing), `pathOk_resolve` (for an accepted path, URL
resolution as WHATWG does it gives the same key as appending).

Events: `hstep_event` (an `event` only for a topic subscribed to and granted,
at level 3), `hrun_event_granted`.

Monotonicity: `mayLeave_mono`, `canCarry_mono`, `gstep_send_mayLeave`,
`payload_le_level`.

The contract text against itself: `ending_conflict` (no host output can keep
both "nothing after ending" and "exactly one reply" on the trace of gap 1).

## Gaps and contradictions found in the contract text

1. **`ending` and "exactly one reply" conflict.** The host promises that
   after `ending` nothing else comes, and that it answers every level-2 or
   level-3 request with exactly one reply. A `store` that crosses `ending`
   on the wire (or that the guest sends after it, which the text does not
   forbid) cannot be answered without breaking the first promise.
   Trace (`crossTrace`): guest `hello {level 2}`; host `welcome {level 2,
   lifecycle running}`; host `lifecycle {ending}`; guest
   `store {rid 7, get, notes}`. `ending_conflict`: for every continuation,
   the two promises do not both hold. Proposed wording: "After `ending` the
   host sends nothing except the replies it owes; it answers a request that
   arrives after `ending` with `store-result {ok: false, reason: "offline"}`.
   On `ending`, the guest treats every outstanding request as failed."
   This model's host does that (`hstep_after_ending`, `hstore`).
2. **A level-0 app by timeout has already sent `hello`.** The text says
   "Level 0: nothing" leaves, and "It sends nothing at level 0". An app that
   asks for level 1 or more sends `hello` (its level, name and first menu)
   before it knows its level; if no `welcome` comes, it is at level 0 and
   the `hello` has left, to whatever window frames it. Trace
   (`lateWelcome`): app start → `hello` sent → timeout → level 0. Proposed
   wording: "Level 0: nothing, except the `hello` of an app that asked for
   level 1 or more, which goes to the parent window whichever page that
   is." (`grun_asked0` proves the stronger claim for an app that asks for
   level 0.)
3. **A late `welcome` is not specified.** After the 500 ms timeout the guest
   is at level 0; a `welcome` that comes later leaves host and guest at
   different levels (the host sends `lifecycle paused` and waits for an
   acknowledgement that never comes). This model ignores a late `welcome`
   (example `lateWelcome`). Proposed wording: "The guest acts on the first
   `welcome` only, and only if it comes before the timeout. A host that
   gets no `ready` treats the guest as level 0."
4. **Nothing says what the guest does with `welcome.level` above the level
   asked.** The text: "The guest reads `welcome.level` as the most it may
   do." Read literally, a host that grants 3 to an app that asked for 1
   lets the module send `store` and `publish` if the app calls them. This
   model ignores such a `welcome` (`gstep_welcome_above`), so the guest
   never sends above the level asked (`grun_le_asked`). Proposed wording:
   "A `welcome` with a level above the level asked is ignored." (Or: "the
   guest takes the smaller of the two".)
5. **Path segments: `.`, percent-encoded dots and backslashes.** The text
   forbids `..` and empty parts. A host that checks that and then resolves
   the path with the URL parser escapes the folder: the WHATWG URL parser
   reads `%2e%2e`, `.%2e` and `%2e.` as `..`, and in `http(s)` URLs reads
   `\` as `/`. Trace (the `#guard`s on `escapePath`): `store {put, path
   ["%2e%2e", "other-app", "secret"]}` passes the text's check, and
   resolving against `apps/me/` gives `apps/other-app/secret`. The text
   also leaves `.` allowed, and with no empty part allowed it gives no way
   to name the folder itself for `list`. Proposed wording: "Each segment
   matches `[A-Za-z0-9._~-]+` and is not `.` or `..`; the path is `[]` (the
   folder itself) only for `list`." This model's `segOk` refuses the dot
   forms the URL parser knows, `/`, `\` and `%`; `pathOk_resolve` proves
   URL resolution then stays in the folder.
6. **Level 1 is a promise about the app, not the module.** "No storage
   content, nothing the person typed" at level 1 holds only if the app puts
   none in its name, action ids, labels and `checked` flags. The module
   cannot tell a declared label from data: `actions {items: [{id: "x",
   label: <diary text>}]}` is a valid level-1 message. In this model the
   types keep them apart (`Label` is not `AppData`), which is an assumption
   about the app (example `labelCarriesText`). `checked` and the timing of
   `ready`, `actions` and `paused` are also one-bit channels. Proposed
   wording: "Level 1: only what the app hands the module as its name,
   action ids, labels and `checked` flags. The module cannot check that
   these are not data. A host shows them to the person and does not store
   or forward them." The level list also leaves out `name`, which `hello`
   carries.
7. **`rid`s are not required to be unique.** Two outstanding requests with
   one `rid` make "exactly one reply carrying its rid" ambiguous. This
   model's guest uses a counter (`gstep_store_fresh`). Proposed wording:
   "A side never reuses a `rid` while a request with it is outstanding."
8. **The guest's side of `call` is not promised.** The host promises one
   reply per request; nothing says the guest answers each `call` once. This
   model's module sends at most one `tool-result` per received `call`
   (`calls` list), and only when the app hands it one.
9. **`welcome.lifecycle` may be `paused`.** The order "`running` →
   `paused` → `running` … `ending`" does not say where it starts; `welcome`
   carries the current state, which may be `paused` (a background tab), and
   the text does not say whether that `paused` needs an acknowledgement.
   This model counts the `welcome` state as the first state of the order
   (`LifeOk`), allows it to be `paused`, and does not ask for an
   acknowledgement of it. Proposed wording: "`welcome.lifecycle` is the
   first state of this order; a `paused` there is acknowledged like a
   `lifecycle paused`" (or "is never acknowledged").
10. **Smaller open points.** Whether `subscribe` replaces or adds (this
    model: replaces); what a guest does with a message of a level above its
    own (this model: ignores it; the host answers a `store` above the
    granted level with `denied`); an `action` for an id the app has just
    removed; a second `hello` or `welcome` (this model: ignored).
11. **The levels bound what leaves, not who receives it.** The module posts
    to `window.parent` with no origin; any page that frames the app and
    answers `welcome {level 2}` receives what the app saves. This is
    consistent with the text but not stated in it.

## What is not proved, and the assumptions

* **Refinement.** No JavaScript exists yet; that `@foafos/guest` and
  `@foafos/host-lite` compute what `gstep` and `hstep` compute is not
  proved. The static rules of the module (no globals replaced, no
  `fetch`/`WebSocket`/… named, no `import()`, no code at import time beyond
  one listener, IndexedDB only under `foafos-guest`) are not modelled:
  they are source checks for CI.
* **Payload types.** That the app keeps its data out of names, labels and
  ids is an assumption (gap 6). `contentType` and `etag` are strings the app
  hands over at level 2; they are not counted as `AppData`.
* **Time.** The 500 ms timeout is an input event; no clocks are modelled.
  Message order on the wire is the order of the input list; crossing
  messages are modelled only in the two-sided trace of gap 1.
* **The host's bus, tools and person.** `publish` goes nowhere in this
  model; the person's topic grants are a fixed list; viewport, audio and
  input contents are not checked (audio level range, declared ids).
* **The reply fields** `status`, `etag`, `contentType` and the backing
  store's own errors (`conflict`, `too-large`, `quota`) are not modelled.
* **Level 4** is outside the contract and outside this model, except that a
  host offering less (`cap`) grants less.
-/

namespace L4Factoidal.Foafos.GuestContract

/-! ## Payloads -/

/-- The app's name, as it declares it in `hello`. -/
structure Name where
  s : String
  deriving DecidableEq, Repr

/-- An action id the app declares. -/
structure ActionId where
  s : String
  deriving DecidableEq, Repr

/-- An action label the app declares. -/
structure Label where
  s : String
  deriving DecidableEq, Repr

/-- One entry in the app's menu of actions. -/
structure Item where
  id : ActionId
  label : Label
  checked : Option Bool
  deriving DecidableEq, Repr

/-- What the app holds: storage contents, what the person typed, what the
app computed from them. Only level-2 and level-3 messages carry it. -/
structure AppData where
  s : String
  deriving DecidableEq, Repr

/-- A bus topic. -/
structure Topic where
  s : String
  deriving DecidableEq, Repr

/-- A tool the app declares: name, description, input schema. -/
structure ToolDecl where
  name : String
  description : String
  schema : String
  deriving DecidableEq, Repr

/-- A request id. (The text says a string; a number is enough here.) -/
abbrev Rid := Nat

/-- A path, as a list of segments, relative to the app's folder. -/
abbrev Key := List String

/-- The four storage operations. -/
inductive Op
  | get
  | put
  | list
  | delete
  deriving DecidableEq, Repr

/-- Why a storage request failed. -/
inductive Reason
  | denied
  | notFound
  | conflict
  | tooLarge
  | quota
  | offline
  deriving DecidableEq, Repr

/-- The three lifecycle states. -/
inductive LState
  | running
  | paused
  | ending
  deriving DecidableEq, Repr

/-- Viewport modes. -/
inductive Mode
  | full
  | window
  | pip
  | split
  deriving DecidableEq, Repr

/-- `viewport { width, height, safe, mode }`. -/
structure Viewport where
  width : Nat
  height : Nat
  safe : Nat × Nat × Nat × Nat
  mode : Mode
  deriving DecidableEq, Repr

/-- `audio { level, muted }`; `level` in thousandths. -/
structure Audio where
  level : Nat
  muted : Bool
  deriving DecidableEq, Repr

/-- `input { map }`: host control names to the app's action ids. -/
abbrev InputMap := List (String × ActionId)

/-! ## Messages -/

/-- Guest to host. -/
inductive GMsg
  | hello (level : Nat) (name : Name) (actions : Option (List Item))
  | ready
  | actions (items : List Item)
  | paused
  | store (rid : Rid) (op : Op) (path : Key) (body : Option AppData) (etag : Option String)
      (contentType : Option String)
  | tools (items : List ToolDecl)
  | toolResult (rid : Rid) (ok : Bool) (result : Option AppData) (error : Option AppData)
  | publish (topic : Topic) (data : AppData)
  | subscribe (topics : List Topic)
  deriving DecidableEq, Repr

/-- Host to guest. -/
inductive HMsg
  | welcome (level : Nat) (life : LState) (view : Viewport) (audio : Audio) (input : Option InputMap)
  | lifecycle (st : LState)
  | audio (a : Audio)
  | viewport (v : Viewport)
  | input (map : InputMap)
  | action (id : ActionId)
  | storeResult (rid : Rid) (ok : Bool) (reason : Option Reason) (body : Option AppData)
      (items : List Key)
  | call (rid : Rid) (name : String) (args : AppData)
  | event (topic : Topic) (data : AppData)
  deriving DecidableEq, Repr

/-- The level a guest message belongs to (the table's last column). -/
def GMsg.level : GMsg → Nat
  | .hello .. | .ready | .actions _ | .paused => 1
  | .store .. => 2
  | .tools _ | .toolResult .. | .publish .. | .subscribe _ => 3

/-- The app data a guest message carries. -/
def GMsg.data : GMsg → List AppData
  | .store _ _ _ b _ _ => b.toList
  | .toolResult _ _ r e => r.toList ++ e.toList
  | .publish _ d => [d]
  | _ => []

/-- `true` for `hello`. -/
def GMsg.isHello : GMsg → Bool
  | .hello .. => true
  | _ => false

/-- A level-1 guest message carries no app data. -/
theorem level_le_one_data (m : GMsg) (h : m.level ≤ 1) : m.data = [] := by
  cases m <;> simp_all [GMsg.level, GMsg.data]

/-- The window a message came from. -/
inductive Win
  | expected
  | other (n : Nat)
  deriving DecidableEq, Repr

/-- A received `postMessage`: its `fl`, its source window, and the message,
or `none` for an unknown `type`. -/
structure Wire (α : Type) where
  fl : Nat
  src : Win
  msg : Option α
  deriving DecidableEq, Repr

/-- The message a side acts on: only with `fl = 1`, from the expected window,
of a known type. -/
def accept {α : Type} (w : Wire α) : Option α :=
  if w.fl = 1 ∧ w.src = .expected then w.msg else none

/-- A well-formed message from the expected window. -/
def wire {α : Type} (m : α) : Wire α := { fl := 1, src := .expected, msg := some m }

/-! ## What can leave, by level -/

/-- The table: a message may leave at level `n` when it is a level-1 to
level-`n` message. -/
def mayLeave (n : Nat) (m : GMsg) : Bool := decide (1 ≤ m.level ∧ m.level ≤ n)

/-- The classes of payload in the text's "What can leave the guest". -/
inductive PayloadClass
  /-- What the app declares about itself: level, name, actions, tools,
  topics, acknowledgements. -/
  | declared
  /-- What the app chooses to save. -/
  | saved
  /-- Tool results. -/
  | toolOut
  /-- Published events. -/
  | published
  deriving DecidableEq, Repr

/-- The level that first allows a payload class to leave. -/
def PayloadClass.level : PayloadClass → Nat
  | .declared => 1
  | .saved => 2
  | .toolOut => 3
  | .published => 3

/-- A payload class may leave at level `n`. -/
def canCarry (n : Nat) (c : PayloadClass) : Bool := decide (c.level ≤ n)

/-- The payload classes in a guest message. -/
def GMsg.payload : GMsg → List PayloadClass
  | .store .. => [.declared, .saved]
  | .toolResult .. => [.declared, .toolOut]
  | .publish .. => [.declared, .published]
  | _ => [.declared]

/-- What may leave at level `n` may leave at level `n + 1` and above. -/
theorem mayLeave_mono {n k : Nat} (h : n ≤ k) (m : GMsg) (hm : mayLeave n m = true) :
    mayLeave k m = true := by
  simp only [mayLeave, decide_eq_true_eq] at *
  omega

/-- What may be carried at level `n` may be carried at any higher level. -/
theorem canCarry_mono {n k : Nat} (h : n ≤ k) (c : PayloadClass) (hc : canCarry n c = true) :
    canCarry k c = true := by
  simp only [canCarry, decide_eq_true_eq] at *
  omega

/-- Nothing may leave at level 0. -/
theorem mayLeave_zero (m : GMsg) : mayLeave 0 m = false := by
  simp only [mayLeave, decide_eq_false_iff_not]
  omega

/-- A message's payload classes all belong to its level or below. -/
theorem payload_le_level (m : GMsg) : ∀ c ∈ m.payload, c.level ≤ m.level := by
  cases m <;> simp [GMsg.payload, GMsg.level, PayloadClass.level]

/-! ## The guest: module and app -/

/-- What the app calls. -/
inductive AppCall
  /-- Start: name and first menu; the module sends `hello` if the app asks
  for level 1 or more. -/
  | start (name : Name) (actions : Option (List Item))
  | ready
  | setActions (items : List Item)
  /-- The app has stopped its timers and sound. -/
  | ackPaused
  | store (op : Op) (path : Key) (body : Option AppData) (etag : Option String)
      (contentType : Option String)
  | tools (items : List ToolDecl)
  | toolResult (rid : Rid) (ok : Bool) (result : Option AppData) (error : Option AppData)
  | publish (topic : Topic) (data : AppData)
  | subscribe (topics : List Topic)
  deriving DecidableEq, Repr

/-- The message for an app call: the call's own fields, plus the level the
app asked for (in `hello`) and a `rid` (in `store`). Nothing else. -/
def AppCall.toMsg (asked rid : Nat) : AppCall → GMsg
  | .start n a => .hello asked n a
  | .ready => .ready
  | .setActions i => .actions i
  | .ackPaused => .paused
  | .store op p b e c => .store rid op p b e c
  | .tools i => .tools i
  | .toolResult r ok res err => .toolResult r ok res err
  | .publish t d => .publish t d
  | .subscribe ts => .subscribe ts

/-- The app data in a call. -/
def AppCall.data : AppCall → List AppData
  | .store _ _ b _ _ => b.toList
  | .toolResult _ _ r e => r.toList ++ e.toList
  | .publish _ d => [d]
  | _ => []

/-- The level of a call. -/
def AppCall.level : AppCall → Nat
  | .start .. | .ready | .setActions _ | .ackPaused => 1
  | .store .. => 2
  | .tools _ | .toolResult .. | .publish .. | .subscribe _ => 3

/-- The module adds no app data: the message carries exactly the call's. -/
theorem toMsg_data (c : AppCall) (a r : Nat) : (c.toMsg a r).data = c.data := by
  cases c <;> rfl

/-- The message has the call's level. -/
theorem toMsg_level (c : AppCall) (a r : Nat) : (c.toMsg a r).level = c.level := by
  cases c <;> rfl

/-- The guest's state. -/
structure GState where
  /-- The level in the app's manifest (`foafosLevel`). -/
  asked : Nat
  helloSent : Bool := false
  /-- `none` until a `welcome` or the timeout. -/
  granted : Option Nat := none
  life : Option LState := none
  /-- A `lifecycle paused` not yet acknowledged. -/
  pauseOwed : Bool := false
  nextRid : Nat := 0
  /-- `store` rids waiting for a reply. -/
  outstanding : List Rid := []
  /-- Host `call` rids waiting for a `tool-result`. -/
  calls : List Rid := []
  deriving DecidableEq, Repr

/-- The guest's inputs. -/
inductive GIn
  | app (c : AppCall)
  | recv (w : Wire HMsg)
  /-- 500 ms passed with no `welcome`, or the guest is not in a frame. -/
  | timeout
  deriving DecidableEq, Repr

/-- The guest's outputs: a message sent to the host, or one passed to the
app. -/
inductive GOut
  | send (m : GMsg)
  | deliver (m : HMsg)
  deriving DecidableEq, Repr

/-- The granted level allows a level-`k` message. `false` before the level
is known. -/
def GState.allows (s : GState) (k : Nat) : Bool :=
  match s.granted with
  | some n => decide (k ≤ n)
  | none => false

/-- The module on an app call. -/
def gapp (s : GState) (c : AppCall) : GState × Option GOut :=
  let out := some (GOut.send (c.toMsg s.asked s.nextRid))
  match c with
  | .start _ _ =>
    if s.granted.isNone && !s.helloSent then
      if s.asked = 0 then ({ s with granted := some 0 }, none)
      else ({ s with helloSent := true }, out)
    else (s, none)
  | .ackPaused =>
    if s.allows 1 && s.pauseOwed then ({ s with pauseOwed := false }, out) else (s, none)
  | .store .. =>
    if s.allows 2 then
      ({ s with nextRid := s.nextRid + 1, outstanding := s.nextRid :: s.outstanding }, out)
    else (s, none)
  | .toolResult r .. =>
    if s.allows 3 && s.calls.contains r then ({ s with calls := s.calls.erase r }, out)
    else (s, none)
  | .ready | .setActions _ | .tools _ | .publish .. | .subscribe _ =>
    if s.allows c.level then (s, out) else (s, none)

/-- The module on a message it accepted, once its level is `n ≥ 1`. -/
def grecvAt (s : GState) (n : Nat) (m : HMsg) : GState × Option GOut :=
  match m with
  | .welcome .. => (s, none)
  | .lifecycle st =>
    if s.life = some .ending then (s, none)
    else ({ s with life := some st, pauseOwed := st == .paused }, some (.deliver m))
  | .storeResult rid .. =>
    if 2 ≤ n && s.outstanding.contains rid then
      ({ s with outstanding := s.outstanding.erase rid }, some (.deliver m))
    else (s, none)
  | .call rid .. =>
    if 3 ≤ n && !s.calls.contains rid then ({ s with calls := rid :: s.calls }, some (.deliver m))
    else (s, none)
  | .event .. => if 3 ≤ n then (s, some (.deliver m)) else (s, none)
  | .audio _ | .viewport _ | .input _ | .action _ => (s, some (.deliver m))

/-- The module on a message it accepted. -/
def grecv (s : GState) (m : HMsg) : GState × Option GOut :=
  match m with
  | .welcome lvl life .. =>
    if s.granted.isNone && s.helloSent && decide (lvl ≤ s.asked) then
      ({ s with granted := some lvl, life := some life }, some (.deliver m))
    else (s, none)
  | _ =>
    match s.granted with
    | some n => if 1 ≤ n then grecvAt s n m else (s, none)
    | none => (s, none)

/-- One guest step. -/
def gstep (s : GState) : GIn → GState × Option GOut
  | .app c => gapp s c
  | .recv w =>
    match accept w with
    | some m => grecv s m
    | none => (s, none)
  | .timeout => (if s.granted.isNone then { s with granted := some 0 } else s, none)

/-! ## Runs -/

/-- Run a step function over a list of inputs, appending its outputs to
`acc`. (A left fold.) -/
def runFrom {σ ι ο : Type} (step : σ → ι → σ × Option ο) (s : σ) (acc : List ο)
    (ins : List ι) : σ × List ο :=
  ins.foldl (fun p i => let r := step p.1 i; (r.1, p.2 ++ r.2.toList)) (s, acc)

/-- One input, then the rest. -/
theorem runFrom_cons {σ ι ο : Type} (step : σ → ι → σ × Option ο) (s : σ) (acc : List ο)
    (i : ι) (is : List ι) :
    runFrom step s acc (i :: is) = runFrom step (step s i).1 (acc ++ (step s i).2.toList) is := rfl

/-- The accumulator is a prefix of the outputs. -/
theorem runFrom_acc {σ ι ο : Type} (step : σ → ι → σ × Option ο) (ins : List ι) :
    ∀ (s : σ) (acc : List ο),
      runFrom step s acc ins = ((runFrom step s [] ins).1, acc ++ (runFrom step s [] ins).2) := by
  induction ins with
  | nil => intro s acc; simp [runFrom]
  | cons i is ih =>
    intro s acc
    rw [runFrom_cons, runFrom_cons, ih, ih (step s i).1 ([] ++ _)]
    simp

/-- The outputs of a run on `i :: is`. -/
theorem runFrom_cons_out {σ ι ο : Type} (step : σ → ι → σ × Option ο) (s : σ) (i : ι)
    (is : List ι) :
    (runFrom step s [] (i :: is)).2 = (step s i).2.toList ++ (runFrom step (step s i).1 [] is).2 := by
  rw [runFrom_cons, runFrom_acc]
  simp

/-- The final state of a run on `i :: is`. -/
theorem runFrom_cons_st {σ ι ο : Type} (step : σ → ι → σ × Option ο) (s : σ) (i : ι)
    (is : List ι) :
    (runFrom step s [] (i :: is)).1 = (runFrom step (step s i).1 [] is).1 := by
  rw [runFrom_cons, runFrom_acc]

/-- An invariant of each step is an invariant of a run. -/
theorem runFrom_inv {σ ι ο : Type} (step : σ → ι → σ × Option ο) (P : σ → Prop)
    (hP : ∀ s i, P s → P (step s i).1) (ins : List ι) :
    ∀ s, P s → P (runFrom step s [] ins).1 := by
  induction ins with
  | nil => intro s h; simpa [runFrom] using h
  | cons i is ih =>
    intro s h
    rw [runFrom_cons_st]
    exact ih _ (hP s i h)

/-- If, under an invariant, every output of a step satisfies `Q`, every output
of a run does. -/
theorem runFrom_out {σ ι ο : Type} (step : σ → ι → σ × Option ο) (P : σ → Prop) (Q : ο → Prop)
    (hP : ∀ s i, P s → P (step s i).1) (hQ : ∀ s i o, P s → (step s i).2 = some o → Q o)
    (ins : List ι) : ∀ s, P s → ∀ o ∈ (runFrom step s [] ins).2, Q o := by
  induction ins with
  | nil => intro s _ o ho; simp [runFrom] at ho
  | cons i is ih =>
    intro s h o ho
    rw [runFrom_cons_out] at ho
    rcases List.mem_append.mp ho with h1 | h1
    · cases hs : (step s i).2 with
      | none => simp [hs] at h1
      | some o' =>
        simp [hs] at h1
        subst h1
        exact hQ s i _ h hs
    · exact ih _ (hP s i h) o h1

/-- If each step's outputs count `p` exactly as its input counts `q`, so do
a run's. -/
theorem runFrom_count {σ ι ο : Type} (step : σ → ι → σ × Option ο) (p : ο → Bool)
    (q : ι → Bool) (h : ∀ s i, (step s i).2.toList.countP p = if q i then 1 else 0)
    (ins : List ι) : ∀ s, (runFrom step s [] ins).2.countP p = ins.countP q := by
  induction ins with
  | nil => intro s; simp [runFrom]
  | cons i is ih =>
    intro s
    rw [runFrom_cons_out, List.countP_append, h, ih, List.countP_cons]
    cases q i <;> simp <;> omega

/-- If, under an invariant, each step extends a record `f` by its outputs
(projected, newest first), then after a run the record is the run's outputs
(projected, newest first) on top of the old record. -/
theorem runFrom_track {σ ι ο β : Type} (step : σ → ι → σ × Option ο) (P : σ → Prop)
    (f : σ → List β) (proj : ο → Option β) (hP : ∀ s i, P s → P (step s i).1)
    (hf : ∀ s i, P s → f (step s i).1 = ((step s i).2.toList.filterMap proj).reverse ++ f s)
    (ins : List ι) :
    ∀ s, P s → f (runFrom step s [] ins).1 = ((runFrom step s [] ins).2.filterMap proj).reverse ++ f s := by
  induction ins with
  | nil => intro s _; simp [runFrom]
  | cons i is ih =>
    intro s h
    rw [runFrom_cons_st, runFrom_cons_out, ih _ (hP s i h), hf s i h]
    simp

/-- A guest run. -/
def grun (s : GState) (ins : List GIn) : GState × List GOut := runFrom gstep s [] ins

/-- The messages a guest sent. -/
def sends (outs : List GOut) : List GMsg :=
  outs.filterMap (fun o => match o with | .send m => some m | .deliver _ => none)

/-- A message in `sends` came from a `send` output. -/
theorem mem_sends {outs : List GOut} {m : GMsg} (h : m ∈ sends outs) : GOut.send m ∈ outs := by
  unfold sends at h
  obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp h
  cases o with
  | send m' => simp at he; subst he; exact ho
  | deliver _ => simp at he

/-! ## Guest theorems -/

/-- A message with `fl ≠ 1`, an unknown `type`, or from another window
changes nothing in the guest. -/
theorem gstep_junk (s : GState) (w : Wire HMsg) (h : accept w = none) :
    gstep s (.recv w) = (s, none) := by
  simp [gstep, h]

/-- The module never sends on a received message. -/
theorem gstep_recv_no_send (s : GState) (w : Wire HMsg) (m : GMsg) :
    (gstep s (.recv w)).2 ≠ some (.send m) := by
  simp only [gstep]
  split
  · rename_i hm _
    simp only [grecv]
    split
    · split <;> simp
    · split
      · split
        · simp only [grecvAt]; split <;> (try split) <;> simp
        · simp
      · simp
  · simp

/-- The module never sends on the timeout. -/
theorem gstep_timeout_no_send (s : GState) (m : GMsg) :
    (gstep s .timeout).2 ≠ some (.send m) := by
  simp [gstep]

/-- What the module sends on an app call is that call, with only the level
asked for and a `rid` added. -/
theorem gstep_app_send (s : GState) (c : AppCall) (m : GMsg)
    (h : (gstep s (.app c)).2 = some (.send m)) : m = c.toMsg s.asked s.nextRid := by
  simp only [gstep, gapp] at h
  cases c <;> simp only at h <;> (repeat' split at h) <;> simp_all

/-- Every message the module sends is the message of an app call; so its app
data is that call's. -/
theorem gstep_send_from_app (s : GState) (i : GIn) (m : GMsg)
    (h : (gstep s i).2 = some (.send m)) :
    ∃ c, i = .app c ∧ m = c.toMsg s.asked s.nextRid ∧ m.data = c.data := by
  cases i with
  | app c => exact ⟨c, rfl, gstep_app_send s c m h, by rw [gstep_app_send s c m h, toMsg_data]⟩
  | recv w => exact absurd h (gstep_recv_no_send s w m)
  | timeout => exact absurd h (gstep_timeout_no_send s m)

theorem allows_le {s : GState} {k : Nat} (h : s.allows k = true) :
    ∃ n, s.granted = some n ∧ k ≤ n := by
  unfold GState.allows at h
  split at h
  · rename_i n hn; exact ⟨n, hn, by simpa using h⟩
  · simp at h

/-- Before the level is known, the module sends only `hello`, and only if
the app asked for level 1 or more. -/
theorem gstep_pending_send (s : GState) (i : GIn) (m : GMsg) (hg : s.granted = none)
    (h : (gstep s i).2 = some (.send m)) : m.isHello = true ∧ 1 ≤ s.asked ∧ m.level = 1 := by
  obtain ⟨c, rfl, rfl, -⟩ := gstep_send_from_app s i m h
  simp only [gstep, gapp] at h
  cases c <;> simp only at h <;> (repeat' split at h) <;>
    simp_all [GState.allows, AppCall.toMsg, GMsg.isHello, GMsg.level] <;> omega

/-- Once the level is `n`, the module sends no `hello` and nothing above
level `n`. -/
theorem gstep_granted_send (s : GState) (i : GIn) (m : GMsg) (n : Nat) (hg : s.granted = some n)
    (h : (gstep s i).2 = some (.send m)) : m.isHello = false ∧ 1 ≤ m.level ∧ m.level ≤ n := by
  obtain ⟨c, rfl, rfl, -⟩ := gstep_send_from_app s i m h
  simp only [gstep, gapp] at h
  cases c <;> simp only at h <;> (repeat' split at h) <;>
    simp_all [GState.allows, AppCall.toMsg, GMsg.isHello, GMsg.level, AppCall.level] <;>
    exact of_decide_eq_true (by assumption)

/-- What the module sends at level `n` is allowed at level `n` by the
table. -/
theorem gstep_send_mayLeave (s : GState) (i : GIn) (m : GMsg) (n : Nat) (hg : s.granted = some n)
    (h : (gstep s i).2 = some (.send m)) : mayLeave n m = true := by
  have := gstep_granted_send s i m n hg h
  simp [mayLeave]; omega

/-- Once known, the level does not change. -/
theorem gstep_granted_keep (s : GState) (i : GIn) (n : Nat) (hg : s.granted = some n) :
    (gstep s i).1.granted = some n := by
  cases i with
  | app c =>
    simp only [gstep, gapp]
    cases c <;> simp only <;> (repeat' split) <;> simp_all
  | recv w =>
    simp only [gstep]
    split
    · simp only [grecv]
      split
      · split <;> simp_all
      · split
        · split
          · simp only [grecvAt]; split <;> (try split) <;> simp_all
          · simp_all
        · simp_all
    · simp_all
  | timeout => simp [gstep, hg]

/-- The asked level never changes. -/
theorem gstep_asked (s : GState) (i : GIn) : (gstep s i).1.asked = s.asked := by
  cases i with
  | app c =>
    simp only [gstep, gapp]
    cases c <;> simp only <;> (repeat' split) <;> simp_all
  | recv w =>
    simp only [gstep]
    split
    · simp only [grecv]
      split
      · split <;> simp_all
      · split
        · split
          · simp only [grecvAt]; split <;> (try split) <;> simp_all
          · simp_all
        · simp_all
    · simp_all
  | timeout => simp only [gstep]; split <;> rfl

/-- A `welcome` above the level asked for is ignored. -/
theorem gstep_welcome_above (s : GState) (w : Wire HMsg) (lvl : Nat) (l : LState) (v : Viewport)
    (a : Audio) (inp : Option InputMap) (hw : accept w = some (.welcome lvl l v a inp))
    (h : s.asked < lvl) : gstep s (.recv w) = (s, none) := by
  simp only [gstep, hw, grecv]
  have : decide (lvl ≤ s.asked) = false := by simp; omega
  simp [this]

/-- The guest invariant: the level, once known, is at most the level asked
for; every outstanding `store` rid is below the counter. -/
def gInv (s : GState) : Prop :=
  (∀ n, s.granted = some n → n ≤ s.asked) ∧ (∀ r ∈ s.outstanding, r < s.nextRid)

/-- A step leaves the `store` counter and the outstanding rids as they were
(or with some removed), or takes one new rid. -/
theorem gstep_rids (s : GState) (i : GIn) :
    ((gstep s i).1.nextRid = s.nextRid ∧ ∀ r ∈ (gstep s i).1.outstanding, r ∈ s.outstanding) ∨
    ((gstep s i).1.nextRid = s.nextRid + 1 ∧
      (gstep s i).1.outstanding = s.nextRid :: s.outstanding) := by
  cases i with
  | app c =>
    simp only [gstep, gapp]
    cases c <;> simp only <;> (repeat' split) <;> simp
  | recv w =>
    simp only [gstep]
    split
    · simp only [grecv]
      split
      · split <;> simp
      · split
        · split
          · simp only [grecvAt]
            split <;> (try split) <;> simp
            exact fun r hr => List.mem_of_mem_erase hr
          · simp
        · simp
    · simp
  | timeout => simp only [gstep]; split <;> simp

/-- Each guest step keeps the invariant, whatever the host sends. -/
theorem gInv_step (s : GState) (i : GIn) (h : gInv s) : gInv (gstep s i).1 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro n hn
    rw [gstep_asked]
    match hg : s.granted with
    | some k =>
      rw [gstep_granted_keep s i k hg] at hn
      injection hn with hn
      subst hn
      exact h1 _ hg
    | none =>
      cases i with
      | app c =>
        simp only [gstep, gapp] at hn
        cases c <;> simp only at hn <;> (repeat' split at hn) <;> simp_all <;> omega
      | recv w =>
        simp only [gstep] at hn
        split at hn
        · simp only [grecv] at hn
          split at hn
          · split at hn
            · simp_all
            · simp_all
          · simp_all
        · simp_all
      | timeout => simp_all [gstep]; omega
  · intro r hr
    rcases gstep_rids s i with ⟨he, hs⟩ | ⟨he, hs⟩
    · rw [he]; exact h2 r (hs r hr)
    · rw [he]; rw [hs] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (h2 r hr)

/-- A `store` rid is new: no outstanding request has it. -/
theorem gstep_store_fresh (s : GState) (h : gInv s) (op : Op) (p : Key) (b : Option AppData)
    (e c : Option String) (m : GMsg) (hs : (gstep s (.app (.store op p b e c))).2 = some (.send m)) :
    m = .store s.nextRid op p b e c ∧ s.nextRid ∉ s.outstanding := by
  refine ⟨gstep_app_send s _ m hs, fun hm => ?_⟩
  exact Nat.lt_irrefl _ (h.2 _ hm)

/-- Whatever the host sends, every message a guest sends in a run is at
level 1 or more and at most the level the app asked for. -/
theorem grun_le_asked (s : GState) (h : gInv s) (ins : List GIn) :
    ∀ m ∈ sends (grun s ins).2, 1 ≤ m.level ∧ m.level ≤ s.asked := by
  intro m hm
  have := runFrom_out gstep (fun t => gInv t ∧ t.asked = s.asked)
    (fun o => ∀ m, o = .send m → 1 ≤ m.level ∧ m.level ≤ s.asked)
    (fun t i ht => ⟨gInv_step t i ht.1, by rw [gstep_asked]; exact ht.2⟩)
    (by
      intro t i o ht ho m' hm'
      subst hm'
      cases hg : t.granted with
      | none =>
        have := gstep_pending_send t i m' hg ho
        omega
      | some n =>
        have := gstep_granted_send t i m' n hg ho
        have := ht.1.1 n hg
        omega)
    ins s ⟨h, rfl⟩ _ (mem_sends hm)
  exact this m rfl

/-- At level 0 the guest sends nothing. -/
theorem grun_level0 (s : GState) (hg : s.granted = some 0) (ins : List GIn) :
    sends (grun s ins).2 = [] := by
  have := runFrom_out gstep (fun t => t.granted = some 0) (fun o => ∀ m, o ≠ .send m)
    (fun t i ht => gstep_granted_keep t i 0 ht)
    (by
      intro t i o ht ho m hm
      subst hm
      have := gstep_granted_send t i m 0 ht ho
      omega)
    ins s hg
  cases hx : sends (grun s ins).2 with
  | nil => rfl
  | cons m _ =>
    have hm : m ∈ sends (grun s ins).2 := by rw [hx]; simp
    exact absurd rfl (this _ (mem_sends hm) m)

/-- An app that asks for level 0 never sends anything, whatever comes. -/
theorem grun_asked0 (s : GState) (h : gInv s) (ha : s.asked = 0) (ins : List GIn) :
    sends (grun s ins).2 = [] := by
  cases hx : sends (grun s ins).2 with
  | nil => rfl
  | cons m _ =>
    have := grun_le_asked s h ins m (by rw [hx]; simp)
    omega

/-- At level 1 the guest sends only `ready`, `actions` and `paused`, and
they carry no app data. -/
theorem grun_level1 (s : GState) (hg : s.granted = some 1) (ins : List GIn) :
    ∀ m ∈ sends (grun s ins).2,
      (m = .ready ∨ (∃ i, m = .actions i) ∨ m = .paused) ∧ m.data = [] := by
  intro m hm
  have := runFrom_out gstep (fun t => t.granted = some 1)
    (fun o => ∀ m, o = .send m → m.isHello = false ∧ 1 ≤ m.level ∧ m.level ≤ 1)
    (fun t i ht => gstep_granted_keep t i 1 ht)
    (by intro t i o ht ho m hm; subst hm; exact gstep_granted_send t i m 1 ht ho)
    ins s hg _ (mem_sends hm) m rfl
  refine ⟨?_, level_le_one_data m this.2.2⟩
  cases m <;> simp_all [GMsg.isHello, GMsg.level]

/-- The module sends `paused` only while a `lifecycle paused` is
unanswered. -/
theorem gstep_paused_owed (s : GState) (i : GIn) (h : (gstep s i).2 = some (.send .paused)) :
    s.pauseOwed = true ∧ (gstep s i).1.pauseOwed = false := by
  obtain ⟨c, rfl, hc, -⟩ := gstep_send_from_app s i _ h
  simp only [gstep, gapp] at h ⊢
  cases c <;> simp [AppCall.toMsg] at hc <;> simp only at h ⊢ <;> (repeat' split at h) <;> simp_all

/-- Only an accepted `lifecycle paused` makes an acknowledgement owed. -/
theorem gstep_owed_set (s : GState) (i : GIn) (h : (gstep s i).1.pauseOwed = true) :
    s.pauseOwed = true ∨ ∃ w, i = .recv w ∧ accept w = some (.lifecycle .paused) := by
  cases i with
  | app c =>
    left
    simp only [gstep, gapp] at h
    cases c <;> simp only at h <;> (repeat' split at h) <;> simp_all
  | recv w =>
    simp only [gstep] at h
    split at h
    · rename_i m hm
      simp only [grecv] at h
      split at h
      · split at h <;> simp_all
      · split at h
        · split at h
          · simp only [grecvAt] at h
            split at h <;> (try split at h) <;> simp_all
          · simp_all
        · simp_all
    · simp_all
  | timeout => left; simp only [gstep] at h; split at h <;> simp_all

/-- A `store-result` for a rid that is not outstanding is ignored. -/
theorem gstep_reply_unknown (s : GState) (w : Wire HMsg) (rid : Rid) (ok : Bool)
    (r : Option Reason) (b : Option AppData) (items : List Key)
    (hw : accept w = some (.storeResult rid ok r b items)) (hr : rid ∉ s.outstanding) :
    gstep s (.recv w) = (s, none) := by
  simp only [gstep, hw, grecv]
  split
  · split
    · simp [grecvAt, hr]
    · rfl
  · rfl

/-! ## The host -/

/-- A backing store: keys (absolute paths) to contents. -/
abbrev Backing := List (Key × AppData)

/-- The contents at a key. -/
def lookup (b : Backing) (k : Key) : Option AppData :=
  (b.find? (fun e => e.1 == k)).map (·.2)

/-- Write at a key. -/
def bput (b : Backing) (k : Key) (d : AppData) : Backing :=
  (k, d) :: b.filter (fun e => e.1 != k)

/-- Delete a key. -/
def bdel (b : Backing) (k : Key) : Backing :=
  b.filter (fun e => e.1 != k)

/-- Removing a key's entries leaves the lookup of another key as it was. -/
theorem find_filter_ne {b : Backing} {k k' : Key} (h : k ≠ k') :
    (b.filter (fun e => e.1 != k)).find? (fun e => e.1 == k') = b.find? (fun e => e.1 == k') := by
  induction b with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, x⟩ := e
    by_cases ha : a = k
    · subst ha
      have : (a == k') = false := by simpa using h
      simp [this, ih]
    · by_cases hq : a = k'
      · subst hq; simp [ha]
      · simp [ha, hq, ih]

/-- A write at `k` leaves every other key as it was. -/
theorem lookup_bput_ne (b : Backing) {k k' : Key} (d : AppData) (h : k ≠ k') :
    lookup (bput b k d) k' = lookup b k' := by
  have : (k == k') = false := by simpa using h
  simp [lookup, bput, this, find_filter_ne h]

/-- A delete at `k` leaves every other key as it was. -/
theorem lookup_bdel_ne (b : Backing) {k k' : Key} (h : k ≠ k') :
    lookup (bdel b k) k' = lookup b k' := by
  simp [lookup, bdel, find_filter_ne h]

/-- The WHATWG URL parser's single-dot segment: `.` or `%2e`, any case. -/
def urlDot (s : String) : Bool := s == "." || s.toLower == "%2e"

/-- The WHATWG URL parser's double-dot segment: `..`, `.%2e`, `%2e.` or
`%2e%2e`, any case. -/
def urlDotDot (s : String) : Bool :=
  s == ".." || s.toLower == ".%2e" || s.toLower == "%2e." || s.toLower == "%2e%2e"

/-- A segment the host accepts: not empty, not a dot segment as the URL
parser reads it, and no `/`, `\` or `%`. -/
def segOk (s : String) : Bool :=
  s != "" && !urlDot s && !urlDotDot s && s.all (fun c => c != '/' && c != '\\' && c != '%')

/-- A path the host accepts for an operation: every segment accepted, and
not empty except for `list` (the folder itself). -/
def pathOk (op : Op) (p : Key) : Bool := (op == .list || !p.isEmpty) && p.all segOk

/-- The check the text states literally: no `..` and no empty part. -/
def naiveOk (p : Key) : Bool := p.all (fun s => s != "" && s != "..")

/-- URL resolution of segments against a base folder (the WHATWG path
state): a double-dot segment drops the last base segment, a single-dot
segment is skipped. -/
def urlResolve (base : Key) (p : Key) : Key :=
  p.foldl (fun acc seg => if urlDotDot seg then acc.dropLast else if urlDot seg then acc else acc ++ [seg])
    base

/-- For a path the host accepts, URL resolution gives the same key as
appending: the path stays inside the folder, however the host resolves it. -/
theorem pathOk_resolve (op : Op) (p : Key) (h : pathOk op p = true) (base : Key) :
    urlResolve base p = base ++ p := by
  have hall : ∀ s ∈ p, segOk s = true := by
    simp only [pathOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.2
  clear h
  induction p generalizing base with
  | nil => simp [urlResolve]
  | cons x xs ih =>
    have hx := hall x (by simp)
    simp only [segOk, Bool.and_eq_true, Bool.not_eq_true'] at hx
    have := ih (base ++ [x]) (fun s hs => hall s (by simp [hs]))
    simp only [urlResolve, List.foldl_cons, hx.1.1.2, hx.1.2, Bool.false_eq_true, if_false] at this ⊢
    rw [this]; simp

/-- The path of gap 5: a percent-encoded `..`. -/
def escapePath : Key := ["%2e%2e", "other-app", "secret"]

/-! `naive_escape`: the text's literal check lets a percent-encoded `..`
through, URL resolution then leaves the folder, and `pathOk` refuses it.
A backslash: the URL parser splits `..\secret` into `..` and `secret`. -/
#guard naiveOk escapePath
#guard urlResolve ["apps", "me"] escapePath == ["apps", "other-app", "secret"]
#guard !pathOk .put escapePath
#guard naiveOk ["..\\secret"] && ("..\\secret".splitOn "\\") == ["..", "secret"]
#guard !pathOk .get ["..\\secret"]

/-- The order of lifecycle states: `running` and `paused` alternate;
`ending` may follow either; nothing follows `ending`. -/
def nextOk : LState → LState → Bool
  | .running, .paused => true
  | .paused, .running => true
  | .running, .ending => true
  | .paused, .ending => true
  | _, _ => false

/-- A sequence of lifecycle states, newest first, in the text's order. The
first (oldest) is the state in `welcome`. -/
inductive LifeOk : List LState → Prop
  | first (st : LState) : LifeOk [st]
  | next {p st : LState} {l : List LState} : LifeOk (p :: l) → nextOk p st = true →
      LifeOk (st :: p :: l)

/-- `ending` comes at most once, and last: no older state is `ending`. -/
theorem lifeOk_ending_last {st : LState} {l : List LState} (h : LifeOk (st :: l)) :
    ∀ x ∈ l, x ≠ .ending := by
  generalize he : st :: l = l' at h
  induction h generalizing st l with
  | first _ => cases he; simp
  | next h0 hn ih =>
    cases he
    rename_i p _ _
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · intro hp; subst hp; simp [nextOk] at hn
    · exact ih rfl x hx

/-- The host's state. -/
structure HState where
  /-- The most this host offers (3 for `@foafos/host-lite`). -/
  cap : Nat
  initLife : LState
  view : Viewport
  aud : Audio
  /-- The app's folder: a key prefix in the backing store. The guest never
  sees it. -/
  root : Key
  /-- The topics the person granted. -/
  personGrants : List Topic
  asked : Option Nat := none
  granted : Option Nat := none
  /-- Lifecycle states sent (in `welcome` and `lifecycle`), newest first. -/
  life : List LState := []
  subs : List Topic := []
  calls : List Rid := []
  store : Backing := []
  deriving DecidableEq, Repr

/-- The host's inputs: received messages and its own decisions. -/
inductive HIn
  | recv (w : Wire GMsg)
  /-- The shell wants this lifecycle state. -/
  | setLife (st : LState)
  /-- The shell has a new audio level, viewport, input map or action. -/
  | notify (m : HMsg)
  /-- An event on the bus. -/
  | busEvent (t : Topic) (d : AppData)
  /-- A tool call for the app. -/
  | callTool (rid : Rid) (name : String) (args : AppData)
  deriving DecidableEq, Repr

/-- The granted level, 0 if none. -/
def HState.lvl (s : HState) : Nat := s.granted.getD 0

/-- The host has sent `ending`. -/
def HState.ended (s : HState) : Bool := s.life.head? == some .ending

/-- A failed `store-result`. -/
def failReply (rid : Rid) (r : Reason) : HMsg := .storeResult rid false (some r) none []

/-- The names under a key, relative to the folder. -/
def listUnder (b : Backing) (root k : Key) : List Key :=
  b.filterMap (fun e => if k.isPrefixOf e.1 then some (e.1.drop root.length) else none)

/-- The host on a `store` request: always exactly one reply with its rid. -/
def hstore (s : HState) (rid : Rid) (op : Op) (path : Key) (body : Option AppData) :
    HState × Option HMsg :=
  if s.lvl < 2 then (s, some (failReply rid .denied))
  else if s.ended then (s, some (failReply rid .offline))
  else if !pathOk op path then (s, some (failReply rid .denied))
  else
    let k := s.root ++ path
    match op with
    | .get =>
      match lookup s.store k with
      | some d => (s, some (.storeResult rid true none (some d) []))
      | none => (s, some (failReply rid .notFound))
    | .put => ({ s with store := bput s.store k (body.getD ⟨""⟩) }, some (.storeResult rid true none none []))
    | .delete =>
      match lookup s.store k with
      | some _ => ({ s with store := bdel s.store k }, some (.storeResult rid true none none []))
      | none => (s, some (failReply rid .notFound))
    | .list => (s, some (.storeResult rid true none none (listUnder s.store s.root k)))

/-- The host on a message it accepted. -/
def hrecv (s : HState) (m : GMsg) : HState × Option HMsg :=
  match m with
  | .hello lvl _ _ =>
    if s.asked.isNone then
      ({ s with asked := some lvl, granted := some (min lvl s.cap), life := [s.initLife] },
        some (.welcome (min lvl s.cap) s.initLife s.view s.aud none))
    else (s, none)
  | .store rid op path body _ _ => hstore s rid op path body
  | .subscribe ts => if 3 ≤ s.lvl then ({ s with subs := ts }, none) else (s, none)
  | .toolResult rid .. => ({ s with calls := s.calls.erase rid }, none)
  | .ready | .actions _ | .paused | .tools _ | .publish .. => (s, none)

/-- Level-1 notices: audio, viewport, input, action. -/
def HMsg.isNotice : HMsg → Bool
  | .audio _ | .viewport _ | .input _ | .action _ => true
  | _ => false

/-- The lifecycle state may follow the last one sent. -/
def HState.lifeNext (s : HState) (st : LState) : Bool :=
  match s.life.head? with
  | some p => nextOk p st
  | none => false

/-- One host step. -/
def hstep (s : HState) : HIn → HState × Option HMsg
  | .recv w =>
    match accept w with
    | some m => hrecv s m
    | none => (s, none)
  | .setLife st =>
    if 1 ≤ s.lvl && s.lifeNext st then ({ s with life := st :: s.life }, some (.lifecycle st))
    else (s, none)
  | .notify m => if 1 ≤ s.lvl && !s.ended && m.isNotice then (s, some m) else (s, none)
  | .busEvent t d =>
    if 3 ≤ s.lvl && !s.ended && s.subs.contains t && s.personGrants.contains t then
      (s, some (.event t d))
    else (s, none)
  | .callTool rid name args =>
    if 3 ≤ s.lvl && !s.ended && !s.calls.contains rid then
      ({ s with calls := rid :: s.calls }, some (.call rid name args))
    else (s, none)

/-- A host run. -/
def hrun (s : HState) (ins : List HIn) : HState × List HMsg := runFrom hstep s [] ins

/-! ## Host theorems -/

/-- A message with `fl ≠ 1`, an unknown `type`, or from another window
changes nothing in the host. -/
theorem hstep_junk (s : HState) (w : Wire GMsg) (h : accept w = none) :
    hstep s (.recv w) = (s, none) := by
  simp [hstep, h]

/-- The fields a `store` never changes. -/
theorem hstore_keeps (s : HState) (rid : Rid) (op : Op) (p : Key) (b : Option AppData) :
    let t := (hstore s rid op p b).1
    t.root = s.root ∧ t.asked = s.asked ∧ t.granted = s.granted ∧ t.life = s.life ∧
      t.subs = s.subs ∧ t.cap = s.cap ∧ t.personGrants = s.personGrants := by
  simp only [hstore]
  repeat' split
  all_goals simp

/-- A `store` changes no key outside the app's folder. -/
theorem hstore_outside (s : HState) (rid : Rid) (op : Op) (p : Key) (b : Option AppData)
    (k : Key) (hk : ¬ s.root <+: k) : lookup (hstore s rid op p b).1.store k = lookup s.store k := by
  have hne : s.root ++ p ≠ k := fun he => hk (he ▸ List.prefix_append _ _)
  simp only [hstore]
  repeat' split
  all_goals simp [lookup_bput_ne _ _ hne, lookup_bdel_ne _ hne]

/-- The host invariant: granted ≤ asked and ≤ what it offers; before
`hello`, nothing is granted and no lifecycle sent; after, the lifecycle
states sent are in order. -/
def hInv (s : HState) : Prop :=
  (∀ g, s.granted = some g → ∃ a, s.asked = some a ∧ g ≤ a ∧ g ≤ s.cap) ∧
  (s.asked = none → s.granted = none ∧ s.life = []) ∧
  (s.asked ≠ none → LifeOk s.life)

/-- Each host step keeps the invariant. -/
theorem hInv_step (s : HState) (i : HIn) (h : hInv s) : hInv (hstep s i).1 := by
  obtain ⟨h1, h2, h3⟩ := h
  cases i with
  | recv w =>
    simp only [hstep]
    split
    · rename_i m _
      cases m with
      | hello lvl n a =>
        simp only [hrecv]
        split
        · refine ⟨?_, ?_, ?_⟩
          · intro g hg; simp at hg; subst hg
            exact ⟨lvl, rfl, Nat.min_le_left _ _, Nat.min_le_right _ _⟩
          · simp
          · intro _; exact LifeOk.first _
        · exact ⟨h1, h2, h3⟩
      | store rid op p b e c =>
        simp only [hrecv]
        obtain ⟨-, ha, hg, hl, -, hc, -⟩ := hstore_keeps s rid op p b
        refine ⟨?_, ?_, ?_⟩
        · rw [hg, ha, hc]; exact h1
        · rw [ha, hg, hl]; exact h2
        · rw [ha, hl]; exact h3
      | subscribe ts =>
        simp only [hrecv]; split
        · exact ⟨h1, h2, h3⟩
        · exact ⟨h1, h2, h3⟩
      | toolResult => exact ⟨h1, h2, h3⟩
      | ready => exact ⟨h1, h2, h3⟩
      | actions => exact ⟨h1, h2, h3⟩
      | paused => exact ⟨h1, h2, h3⟩
      | tools => exact ⟨h1, h2, h3⟩
      | publish => exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  | setLife st =>
    simp only [hstep]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hs : s.asked ≠ none := by
        intro hn
        have := (h2 hn).1
        simp [HState.lvl, this] at hc
      refine ⟨h1, fun hn => absurd hn hs, fun _ => ?_⟩
      have hl := h3 hs
      unfold HState.lifeNext at hc
      cases hp : s.life with
      | nil => simp [hp] at hc
      | cons p l =>
        rw [hp] at hl hc
        exact LifeOk.next hl (by simpa using hc.2)
    · exact ⟨h1, h2, h3⟩
  | notify m => simp only [hstep]; split <;> exact ⟨h1, h2, h3⟩
  | busEvent t d => simp only [hstep]; split <;> exact ⟨h1, h2, h3⟩
  | callTool rid n a => simp only [hstep]; split <;> exact ⟨h1, h2, h3⟩

/-- A host's initial state. -/
def HState.init (s : HState) : Prop := s.asked = none ∧ s.granted = none ∧ s.life = []

theorem hInv_init (s : HState) (h : s.init) : hInv s := by
  obtain ⟨ha, hg, hl⟩ := h
  exact ⟨fun g hg' => by simp [hg] at hg', fun _ => ⟨hg, hl⟩, fun hn => absurd ha hn⟩

/-- The invariant holds after any run from an initial state. -/
theorem hrun_inv (s : HState) (h : s.init) (ins : List HIn) : hInv (hrun s ins).1 :=
  runFrom_inv hstep hInv hInv_step ins s (hInv_init s h)

/-- A host grants at most the level asked for, and at most what it offers. -/
theorem hrun_grant_le (s : HState) (h : s.init) (ins : List HIn) (g : Nat)
    (hg : (hrun s ins).1.granted = some g) :
    ∃ a, (hrun s ins).1.asked = some a ∧ g ≤ a ∧ g ≤ s.cap := by
  have hc : (hrun s ins).1.cap = s.cap :=
    runFrom_inv hstep (fun t => t.cap = s.cap)
      (by
        intro t i ht
        cases i with
        | recv w =>
          simp only [hstep]; split
          · rename_i m _
            cases m <;> simp only [hrecv] <;> (try split) <;> (try simp [ht])
            exact (hstore_keeps t _ _ _ _).2.2.2.2.2.1.trans ht
          · exact ht
        | setLife => simp only [hstep]; split <;> simp [ht]
        | notify => simp only [hstep]; split <;> simp [ht]
        | busEvent => simp only [hstep]; split <;> simp [ht]
        | callTool => simp only [hstep]; split <;> simp [ht])
      ins s rfl
  rw [← hc]
  exact (hrun_inv s h ins).1 g hg

/-- The request id of an input, if it is an accepted `store` request. -/
def reqRid : HIn → Option Rid
  | .recv w =>
    match accept w with
    | some (.store rid ..) => some rid
    | _ => none
  | _ => none

/-- A `store-result` carrying this rid. -/
def isReplyTo (r : Rid) : HMsg → Bool
  | .storeResult rid .. => rid == r
  | _ => false

theorem hstore_reply (s : HState) (rid : Rid) (op : Op) (p : Key) (b : Option AppData) :
    ∃ ok reason body items, (hstore s rid op p b).2 = some (.storeResult rid ok reason body items) := by
  simp only [hstore]
  repeat' split
  all_goals simp [failReply]

/-- Each step sends one reply carrying `r` if its input is a `store` request
with rid `r`, and none otherwise. -/
theorem hstep_reply_count (s : HState) (i : HIn) (r : Rid) :
    (hstep s i).2.toList.countP (isReplyTo r) = if reqRid i == some r then 1 else 0 := by
  cases i with
  | recv w =>
    cases hw : accept w with
    | none => simp [hstep, reqRid, hw]
    | some m =>
      cases m with
      | store rid op p b e c =>
        simp only [hstep, reqRid, hw, hrecv]
        obtain ⟨ok, rs, bd, it, he⟩ := hstore_reply s rid op p b
        rw [he]
        simp [isReplyTo]
      | hello => simp only [hstep, reqRid, hw, hrecv]; split <;> simp [isReplyTo]
      | subscribe => simp only [hstep, reqRid, hw, hrecv]; split <;> simp
      | _ => simp [hstep, reqRid, hw, hrecv]
  | setLife => simp only [hstep, reqRid]; split <;> simp [isReplyTo]
  | notify m =>
    simp only [hstep, reqRid]; split
    · rename_i hc; cases m <;> simp_all [HMsg.isNotice, isReplyTo]
    · simp
  | busEvent => simp only [hstep, reqRid]; split <;> simp [isReplyTo]
  | callTool => simp only [hstep, reqRid]; split <;> simp [isReplyTo]

/-- One reply per request: over a run, the replies carrying rid `r` are as
many as the `store` requests carrying `r` (each sent in the step that
received its request). -/
theorem hrun_replies (s : HState) (ins : List HIn) (r : Rid) :
    (hrun s ins).2.countP (isReplyTo r) = ins.countP (fun i => reqRid i == some r) :=
  runFrom_count hstep (isReplyTo r) (fun i => reqRid i == some r) (hstep_reply_count · · r) ins s

/-- No step changes a key outside the app's folder. -/
theorem hstep_store_outside (s : HState) (i : HIn) (k : Key) (hk : ¬ s.root <+: k) :
    lookup (hstep s i).1.store k = lookup s.store k ∧ (hstep s i).1.root = s.root := by
  cases i with
  | recv w =>
    simp only [hstep]
    split
    · rename_i m _
      cases m with
      | store rid op p b e c =>
        exact ⟨hstore_outside s rid op p b k hk, (hstore_keeps s rid op p b).1⟩
      | hello => simp only [hrecv]; split <;> simp
      | subscribe => simp only [hrecv]; split <;> simp
      | _ => simp [hrecv]
    · simp
  | setLife => simp only [hstep]; split <;> simp
  | notify => simp only [hstep]; split <;> simp
  | busEvent => simp only [hstep]; split <;> simp
  | callTool => simp only [hstep]; split <;> simp

/-- Over a run, no key outside the app's folder changes. -/
theorem hrun_store_outside (s : HState) (ins : List HIn) (k : Key) (hk : ¬ s.root <+: k) :
    lookup (hrun s ins).1.store k = lookup s.store k :=
  (runFrom_inv hstep (fun t => t.root = s.root ∧ lookup t.store k = lookup s.store k)
    (fun t i ht => by
      have := hstep_store_outside t i k (ht.1 ▸ hk)
      exact ⟨this.2.trans ht.1, this.1.trans ht.2⟩)
    ins s ⟨rfl, rfl⟩).2

/-- A successful read returns contents from inside the app's folder only. -/
theorem hstep_get_inside (s : HState) (i : HIn) (rid : Rid) (d : AppData) (items : List Key)
    (h : (hstep s i).2 = some (.storeResult rid true none (some d) items)) :
    ∃ p, lookup s.store (s.root ++ p) = some d := by
  cases i with
  | recv w =>
    simp only [hstep] at h
    split at h
    · rename_i m _
      cases m with
      | store rid' op p b e c =>
        simp only [hrecv, hstore] at h
        refine ⟨p, ?_⟩
        repeat' split at h
        all_goals simp_all [failReply]
      | hello => simp only [hrecv] at h; split at h <;> simp at h
      | subscribe => simp only [hrecv] at h; split at h <;> simp at h
      | _ => simp [hrecv] at h
    · simp at h
  | setLife => simp only [hstep] at h; split at h <;> simp at h
  | notify m =>
    simp only [hstep] at h; split at h
    · simp at h; subst h; simp_all [HMsg.isNotice]
    · simp at h
  | busEvent => simp only [hstep] at h; split at h <;> simp at h
  | callTool => simp only [hstep] at h; split at h <;> simp at h

/-- A path the host does not accept gets `denied` and changes nothing (before
`ending`; after it, every request gets `offline`). -/
theorem hstep_bad_path (s : HState) (w : Wire GMsg) (rid : Rid) (op : Op) (p : Key)
    (b : Option AppData) (e c : Option String) (hw : accept w = some (.store rid op p b e c))
    (hp : pathOk op p = false) (hl : s.ended = false) :
    hstep s (.recv w) = (s, some (failReply rid .denied)) := by
  simp only [hstep, hw, hrecv, hstore, hp, hl]
  split <;> simp

/-- An `event` goes out only at level 3, for a topic subscribed to and
granted by the person. -/
theorem hstep_event (s : HState) (i : HIn) (t : Topic) (d : AppData)
    (h : (hstep s i).2 = some (.event t d)) :
    3 ≤ s.lvl ∧ t ∈ s.subs ∧ t ∈ s.personGrants := by
  cases i with
  | recv w =>
    simp only [hstep] at h
    split at h
    · rename_i m _
      cases m with
      | store rid op p b e c =>
        obtain ⟨_, _, _, _, he⟩ := hstore_reply s rid op p b
        simp [hrecv, he] at h
      | hello => simp only [hrecv] at h; split at h <;> simp at h
      | subscribe => simp only [hrecv] at h; split at h <;> simp at h
      | _ => simp [hrecv] at h
    · simp at h
  | setLife => simp only [hstep] at h; split at h <;> simp at h
  | notify m =>
    simp only [hstep] at h; split at h
    · simp at h; subst h; simp_all [HMsg.isNotice]
    · simp at h
  | busEvent t' d' =>
    simp only [hstep] at h; split at h
    · rename_i hc
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp_all
    · simp at h
  | callTool => simp only [hstep] at h; split at h <;> simp at h

/-- Over a run, every `event` is for a topic the person granted. -/
theorem hrun_event_granted (s : HState) (ins : List HIn) (t : Topic) (d : AppData)
    (h : HMsg.event t d ∈ (hrun s ins).2) : t ∈ s.personGrants := by
  have := runFrom_out hstep (fun u => u.personGrants = s.personGrants)
    (fun o => ∀ t d, o = .event t d → t ∈ s.personGrants)
    (by
      intro u i hu
      cases i with
      | recv w =>
        simp only [hstep]; split
        · rename_i m _
          cases m <;> simp only [hrecv] <;> (try split) <;> (try simp [hu])
          exact (hstore_keeps u _ _ _ _).2.2.2.2.2.2.trans hu
        · exact hu
      | setLife => simp only [hstep]; split <;> simp [hu]
      | notify => simp only [hstep]; split <;> simp [hu]
      | busEvent => simp only [hstep]; split <;> simp [hu]
      | callTool => simp only [hstep]; split <;> simp [hu])
    (by
      intro u i o hu ho t' d' he
      subst he
      exact hu ▸ (hstep_event u i t' d' ho).2.2)
    ins s rfl _ h
  exact this t d rfl

/-- After `ending`, the host sends only `store-result`s (the replies it
owes; gap 1). -/
theorem hstep_after_ending (s : HState) (hi : hInv s) (he : s.ended = true) (i : HIn) (m : HMsg)
    (h : (hstep s i).2 = some m) : ∃ rid ok r b items, m = .storeResult rid ok r b items := by
  have hl : s.life ≠ [] := by intro hl; simp [HState.ended, hl] at he
  have ha : s.asked ≠ none := fun hn => hl (hi.2.1 hn).2
  have hnext : ∀ st, s.lifeNext st = false := by
    intro st
    unfold HState.lifeNext
    simp only [HState.ended, beq_iff_eq] at he
    rw [he]; cases st <;> rfl
  cases i with
  | recv w =>
    simp only [hstep] at h
    split at h
    · rename_i m' _
      cases m' with
      | store rid op p b e c =>
        obtain ⟨ok, r, bd, it, hr⟩ := hstore_reply s rid op p b
        simp only [hrecv, hr] at h
        cases h; exact ⟨_, _, _, _, _, rfl⟩
      | hello =>
        simp only [hrecv] at h
        split at h
        · rename_i hn; simp at hn; exact absurd hn ha
        · simp at h
      | subscribe => simp only [hrecv] at h; split at h <;> simp at h
      | _ => simp [hrecv] at h
    · simp at h
  | setLife st => simp [hstep, hnext] at h
  | notify => simp [hstep, he] at h
  | busEvent => simp [hstep, he] at h
  | callTool => simp [hstep, he] at h

/-- The lifecycle state in a host message, if any. -/
def lifeOf : HMsg → Option LState
  | .welcome _ l .. => some l
  | .lifecycle l => some l
  | _ => none

/-- Lifecycle order: from an initial state, the lifecycle states a host
sends (in `welcome` and `lifecycle`), in the order sent, are empty or in the
text's order (`LifeOk`, read oldest first); so `ending` is last, at most
once (`lifeOk_ending_last`). -/
theorem hrun_life (s : HState) (h : s.init) (ins : List HIn) :
    let sent := (hrun s ins).2.filterMap lifeOf
    sent = [] ∨ LifeOk sent.reverse := by
  intro sent
  have ht := runFrom_track hstep hInv (fun t => t.life) lifeOf hInv_step
    (by
      intro t i hi
      cases i with
      | recv w =>
        simp only [hstep]
        split
        · rename_i m _
          cases m with
          | hello =>
            simp only [hrecv]
            split
            · rename_i hn
              simp at hn
              simp [lifeOf, (hi.2.1 hn).2]
            · simp
          | store rid op p b e c =>
            obtain ⟨ok, r, bd, it, hr⟩ := hstore_reply t rid op p b
            simp only [hrecv, hr]
            simp [lifeOf, (hstore_keeps t rid op p b).2.2.2.1]
          | subscribe => simp only [hrecv]; split <;> simp
          | _ => simp [hrecv]
        · simp
      | setLife => simp only [hstep]; split <;> simp [lifeOf]
      | notify m =>
        simp only [hstep]; split
        · rename_i hc; cases m <;> simp_all [HMsg.isNotice, lifeOf]
        · simp
      | busEvent => simp only [hstep]; split <;> simp [lifeOf]
      | callTool => simp only [hstep]; split <;> simp [lifeOf])
    ins s (hInv_init s h)
  have hfin := hrun_inv s h ins
  simp only [h.2.2, List.append_nil] at ht
  change (hrun s ins).1.life = sent.reverse at ht
  by_cases hs : sent = []
  · left; exact hs
  · right
    rw [← ht]
    apply hfin.2.2
    intro hn
    have := (hfin.2.1 hn).2
    rw [ht] at this
    exact hs (List.reverse_eq_nil_iff.mp this)

/-! ## The contract text against itself (gap 1) -/

/-- An event in a two-sided trace, in the order the host sees it. -/
inductive Ev
  | g (m : GMsg)
  | h (m : HMsg)
  deriving DecidableEq, Repr

/-- The text: "After `ending`, nothing else comes." -/
def NothingAfterEnding (tr : List Ev) : Prop :=
  ∀ (i j : Nat) (m : HMsg), i < j → tr[i]? = some (Ev.h (.lifecycle .ending)) → tr[j]? ≠ some (Ev.h m)

/-- A guest `store` request carrying `r`. -/
def isReq (r : Rid) : Ev → Bool
  | .g (.store rid ..) => rid == r
  | _ => false

/-- A host reply carrying `r`. -/
def isRep (r : Rid) : Ev → Bool
  | .h m => isReplyTo r m
  | _ => false

/-- The text: "It answers every level-2 or level-3 request with exactly one
reply, carrying its `rid`." -/
def OneReplyEach (tr : List Ev) : Prop :=
  ∀ i r e, tr[i]? = some e → isReq r e = true → (tr.drop (i + 1)).countP (isRep r) = 1

/-- The trace of gap 1: a `store` that crosses `ending`. -/
def crossTrace : List Ev :=
  [.g (.hello 2 ⟨"notes"⟩ none),
   .h (.welcome 2 .running ⟨800, 600, (0, 0, 0, 0), .window⟩ ⟨1000, false⟩ none),
   .h (.lifecycle .ending),
   .g (.store 7 .get ["notes"] none none none)]

/-- No continuation of `crossTrace` keeps both host promises: the reply owed
to request 7 would come after `ending`. -/
theorem ending_conflict (rest : List Ev) :
    ¬ (NothingAfterEnding (crossTrace ++ rest) ∧ OneReplyEach (crossTrace ++ rest)) := by
  rintro ⟨hn, ho⟩
  have h1 := ho 3 7 (Ev.g (.store 7 .get ["notes"] none none none)) (by simp [crossTrace])
    (by simp [isReq])
  have h2 : ((crossTrace ++ rest).drop 4) = rest := by simp [crossTrace]
  rw [h2] at h1
  obtain ⟨e, he, hr⟩ := List.countP_pos_iff.mp (by omega : 0 < rest.countP (isRep 7))
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  cases e with
  | g m => simp [isRep] at hr
  | h m =>
    apply hn 2 (4 + k) m (by omega) (by simp [crossTrace])
    rw [List.getElem?_append_right (by simp [crossTrace])]
    simpa [crossTrace] using hk

/-! ## Example traces -/

/-- A viewport and audio for the examples. -/
def vp : Viewport := ⟨800, 600, (0, 0, 0, 0), .window⟩
def au : Audio := ⟨1000, false⟩

/-- A host for the examples: offers level 3, the person granted `chess`. -/
def host0 : HState :=
  { cap := 3, initLife := .running, view := vp, aud := au, root := ["apps", "me"],
    personGrants := [⟨"chess"⟩], store := [(["apps", "other", "secret"], ⟨"theirs"⟩)] }

/-- A level-1 app, paused and resumed: it sends `hello`, `ready`, one
`paused` acknowledgement (the second `ackPaused`, with nothing owed, sends
nothing), and the host's lifecycle sequence is `running paused running`. -/
def level1Guest : List GIn :=
  [.app (.start ⟨"tetris"⟩ (some [⟨⟨"new"⟩, ⟨"New game"⟩, none⟩])),
   .recv (wire (.welcome 1 .running vp au none)),
   .app .ready,
   .recv (wire (.lifecycle .paused)),
   .app .ackPaused,
   .recv (wire (.lifecycle .running)),
   .app .ackPaused]

#guard sends (grun { asked := 1 } level1Guest).2 ==
  [.hello 1 ⟨"tetris"⟩ (some [⟨⟨"new"⟩, ⟨"New game"⟩, none⟩]), .ready, .paused]

#guard ((hrun host0 [.recv (wire (.hello 1 ⟨"tetris"⟩ none)), .setLife .paused,
    .setLife .running, .setLife .running, .setLife .ending, .setLife .running]).2.filterMap lifeOf) ==
  [.running, .paused, .running, .ending]

/-- A level-2 app's `put` outside its folder is refused: `..`, a
percent-encoded `..`, and an empty part all get `denied`; the other app's
file is unchanged; a `put` inside the folder works. -/
def level2Host : List HIn :=
  [.recv (wire (.hello 2 ⟨"notes"⟩ none)),
   .recv (wire (.store 0 .put ["..", "other", "secret"] (some ⟨"mine"⟩) none none)),
   .recv (wire (.store 1 .put ["%2E%2e", "other", "secret"] (some ⟨"mine"⟩) none none)),
   .recv (wire (.store 2 .put ["a", "", "b"] (some ⟨"mine"⟩) none none)),
   .recv (wire (.store 3 .put ["diary.txt"] (some ⟨"mine"⟩) none none))]

#guard (hrun host0 level2Host).2 ==
  [.welcome 2 .running vp au none, failReply 0 .denied, failReply 1 .denied, failReply 2 .denied,
   .storeResult 3 true none none []]
#guard lookup (hrun host0 level2Host).1.store ["apps", "other", "secret"] == some ⟨"theirs"⟩
#guard lookup (hrun host0 level2Host).1.store ["apps", "me", "diary.txt"] == some ⟨"mine"⟩

/-- A level-3 app subscribes to `chess` and `chat`; the person granted only
`chess`; an event on `chat` is not delivered, one on `chess` is. -/
def level3Host : List HIn :=
  [.recv (wire (.hello 3 ⟨"board"⟩ none)),
   .recv (wire (.subscribe [⟨"chess"⟩, ⟨"chat"⟩])),
   .busEvent ⟨"chat"⟩ ⟨"hi"⟩,
   .busEvent ⟨"chess"⟩ ⟨"e4"⟩]

#guard (hrun host0 level3Host).2 == [.welcome 3 .running vp au none, .event ⟨"chess"⟩ ⟨"e4"⟩]

/-- A host that grants 3 to an app that asked for 1 is not followed: the
guest ignores the `welcome`, falls to level 0 at the timeout, and its later
`store` and `publish` calls send nothing. -/
def overGrant : List GIn :=
  [.app (.start ⟨"tetris"⟩ none),
   .recv (wire (.welcome 3 .running vp au none)),
   .timeout,
   .app (.store .put ["x"] (some ⟨"data"⟩) none none),
   .app (.publish ⟨"chat"⟩ ⟨"data"⟩)]

#guard (grun { asked := 1 } overGrant).1.granted == some 0
#guard sends (grun { asked := 1 } overGrant).2 == [.hello 1 ⟨"tetris"⟩ none]

-- Junk: a message with `fl = 2`, one from another window, and one of an
-- unknown type change nothing.
#guard (grun { asked := 1, helloSent := true }
  [.recv { fl := 2, src := .expected, msg := some (.welcome 1 .running vp au none) },
   .recv { fl := 1, src := .other 9, msg := some (.welcome 1 .running vp au none) },
   .recv { fl := 1, src := .expected, msg := none }]) ==
  ({ asked := 1, helloSent := true }, [])

/-- Gap 2 and gap 3: the app asked for level 2; `hello` left; no `welcome`
came in time; the guest is at level 0; a late `welcome` is ignored. -/
def lateWelcome : List GIn :=
  [.app (.start ⟨"notes"⟩ none), .timeout, .recv (wire (.welcome 2 .running vp au none)),
   .app (.store .put ["a"] (some ⟨"x"⟩) none none)]

#guard (grun { asked := 2 } lateWelcome).1.granted == some 0
#guard sends (grun { asked := 2 } lateWelcome).2 == [.hello 2 ⟨"notes"⟩ none]

/-- Gap 6: a level-1 app puts text it holds into a label; the module sends
it, as it must: it cannot tell a label from data. -/
def labelCarriesText : List GIn :=
  [.app (.start ⟨"diary"⟩ none), .recv (wire (.welcome 1 .running vp au none)),
   .app (.setActions [⟨⟨"x"⟩, ⟨"Dear diary, today I"⟩, none⟩])]

#guard sends (grun { asked := 1 } labelCarriesText).2 ==
  [.hello 1 ⟨"diary"⟩ none, .actions [⟨⟨"x"⟩, ⟨"Dear diary, today I"⟩, none⟩]]

-- A reply for an unknown rid is ignored.
#guard (grun { asked := 2, helloSent := true, granted := some 2 }
  [.recv (wire (.storeResult 5 true none (some ⟨"x"⟩) []))]).2 == []

/-- The lifecycle order the task names, `running (paused running)* paused?
ending?`, is an instance of `LifeOk`. -/
example : LifeOk [.ending, .paused, .running, .paused, .running] := by
  exact .next (.next (.next (.next (.first _) rfl) rfl) rfl) rfl

end L4Factoidal.Foafos.GuestContract
