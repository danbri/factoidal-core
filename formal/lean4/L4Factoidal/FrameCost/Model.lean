import L4Factoidal.FrameCost.Band
import L4Factoidal.FrameCost.Lru

/-! # Frame scheduling in the Foafnaut hosts, with its cost

Record: `docs/designissues/2026-11-08-cost-theorems.md`. Issues 1268 and 1292.

A host session holds the layout key of the page, the pointer state that is painted
and not laid out (hover and active), the scroll, the band of page rows on screen,
the kept layouts (the engine's `Lru`, `layoutSlots` entries) and a prefetched band.
For each event the host does one of four things:

* `shift`: the band on screen keeps the scroll; the composite runs at a new offset.
  No Lean call.
* `swap`: a prefetched band of the same state keeps the scroll; it is uploaded and
  shown. No Lean call (the prefetch already paid its render).
* `render`: a kept layout is the layout of this key; Lean draws a new band from it,
  with the pointer state painted on it (`WebDocument.cachedFrame`, `WebRepaint`).
* `layout`: the key is new; Lean parses, cascades and lays out, then draws a band.

The band, its keep range and the memo are the engine's own definitions
(`FrameCost.Band`, `FrameCost.Lru`, which `WebDocument` uses). The key has the fields
of `WebDocument.LayoutKey`; the scroll is not one of them, and the pointer is one only
when a `:hover` or `:active` style changes geometry (`WebDocument.LayoutKey.pointer`).

Only Lean core. -/
namespace L4Factoidal.FrameCost

/-- The fields of `WebDocument.LayoutKey`, each named by a number. `page` stands for
the HTML and the request fields that name the document (`url`, `resources`,
`commands`, `heldImages`, `graphModel`, `media`); `visited` for the visited URLs;
`fonts` for the held font list; `pointer` for the hover and active nodes when a style
of theirs changes geometry, else 0. There is no scroll. -/
structure Key where
  page : Nat
  width : Nat
  height : Nat
  /-- Height of the browser chrome above the page. -/
  top : Nat
  /-- `textScalePercent`. -/
  scale : Nat
  visited : Nat
  fonts : Nat
  pointer : Nat
  deriving Repr, DecidableEq

/-- What a band on screen shows: the key it was laid out for and the pointer state
painted on it. -/
abbrev Shown := Key × Nat

/-- A host session. -/
structure Session where
  key : Key
  /-- What the frame paints on its layout (0: nothing): one number for the hover and
  active state and the paint-only values (`Event.paintOnly`). The engine holds them apart;
  a change of either is one render here, which is the cost the model states. -/
  paint : Nat
  scroll : Nat
  /-- The largest scroll of the page. -/
  limit : Nat
  /-- The band on screen and the state it was drawn for. -/
  shown : Option (Shown × Band)
  /-- The keys of the kept layouts (`WebDocument.layoutRef` with the values left out,
  `Lru.erase`). -/
  kept : Lru Key Unit
  /-- A band drawn ahead for a state (`run_html.ts` `prefetched`). -/
  prefetched : Option (Shown × Band)
  deriving Repr

/-- Page rows of the window. -/
def Session.view (s : Session) : Nat := s.key.height-s.key.top

/-- The state on screen after this session's frame. -/
def Session.state (s : Session) : Shown := (s.key,s.paint)

/-- The first session of a window: nothing drawn, nothing kept. -/
def Session.start (key : Key) (limit : Nat) : Session :=
  {key, paint := 0, scroll := 0, limit, shown := none, kept := [], prefetched := none}

inductive Event where
  /-- A wheel or key scroll by `delta` rows; the host clamps it to `0 .. limit`. -/
  | scroll (delta : Int)
  | resize (width height : Nat)
  /-- Text zoom to `percent`. -/
  | zoom (percent : Nat)
  /-- The visited links change (a navigation in another tab). -/
  | visit (state : Nat)
  /-- The pointer moves onto another link, or a press starts or ends: `state` is the
  hover and active nodes (0: none). `geometry` is true when a `:hover` or `:active`
  style of the page for that state changes more than colours (`WebRepaint.restyle`
  answers `none`); then the state is in the layout key. -/
  | hover (state : Nat) (geometry : Bool)
  | navigate (page limit : Nat)
  | fontLoad
  /-- The host asks the worker for a band at this scroll (`scroll_prefetch.prefetchTarget`). -/
  | prefetch (target : Nat)
  /-- A timer tick with no DOM change. -/
  | tick
  /-- A change that is painted on the kept layout: a script's `transform` of an SVG
  element, or a frame of an SVG animation (`WebPaint`). `state` is what the frame
  paints; the layout key does not change (`WebPaint.slotKey`). -/
  | paintOnly (state : Nat)
  deriving Repr, DecidableEq

def clampScroll (limit scroll : Nat) (delta : Int) : Nat :=
  min limit ((scroll : Int)+delta).toNat

/-- What an event changes, before the host decides how to draw. -/
def apply (s : Session) : Event → Session
  | .scroll d => {s with scroll := clampScroll s.limit s.scroll d}
  | .resize w h => {s with key := {s.key with width := w, height := h}, scroll := min s.scroll s.limit}
  | .zoom p => {s with key := {s.key with scale := p}}
  | .visit v => {s with key := {s.key with visited := v}}
  | .hover e g => {s with key := {s.key with pointer := if g then e else 0}, paint := e}
  | .navigate p l => {s with key := {s.key with page := p, pointer := 0}, paint := 0, scroll := 0, limit := l}
  | .fontLoad => {s with key := {s.key with fonts := s.key.fonts+1}}
  | .prefetch _ => s
  | .tick => s
  | .paintOnly st => {s with paint := st}

inductive Decision where
  | shift
  | swap
  | render
  | layout
  deriving Repr, DecidableEq

def Decision.name : Decision → String
  | .shift => "shift"
  | .swap => "swap"
  | .render => "render"
  | .layout => "layout"

/-- A band for the state `st` that keeps `scroll`. -/
def keepsFor (band : Option (Shown × Band)) (st : Shown) (view scroll : Nat) : Bool :=
  match band with
  | some (k,b) => decide (k = st) && b.keeps view scroll
  | none => false

/-- The band on screen is for this state (it may not keep the scroll). -/
def shownFor (band : Option (Shown × Band)) (st : Shown) : Bool :=
  match band with
  | some (k,_) => decide (k = st)
  | none => false

/-- The engine keeps a layout of this key: the engine's own test, `Lru.find?`. -/
def Session.warmFor (s : Session) (k : Key) : Bool := (Lru.find? s.kept k).isSome

/-- The decision for a session after an event changed it: the one source of truth.
`run_html.ts` makes it as `canShift() && keeps(...)`, then `swapReady()` or
`bandComing()` (only when the band on screen is for this state: `canSwap`; a change of
state goes to a Lean frame), then a Lean frame (`dirty`), which takes a kept layout when the key
is kept (`WebDocument.cachedFrame`). -/
def decideFrame (s : Session) : Decision :=
  if keepsFor s.shown s.state s.view s.scroll then .shift
  else if shownFor s.shown s.state && keepsFor s.prefetched s.state s.view s.scroll then .swap
  else if s.warmFor s.key then .render
  else .layout

/-- What a decision leaves. A render uses the kept layout, which moves it first in the
memo (`Lru.putIn`, as `WebDocument.cachedLayOut` does; the memo keeps the layouts of one
page, so a navigation drops the others); a layout puts the new one, and
the band drawn ahead for another state is dropped (the host drops it). -/
def commit (s : Session) : Decision → Session
  | .shift => s
  | .swap => {s with shown := s.prefetched, prefetched := none}
  | .render => {s with kept := Lru.putIn Key.page layoutSlots s.kept s.key (), shown := some (s.state,band s.scroll s.view)}
  | .layout => {s with kept := Lru.putIn Key.page layoutSlots s.kept s.key (), shown := some (s.state,band s.scroll s.view), prefetched := none}

/-- The work of one step: Lean layouts, Lean band renders, bytes of page layer uploaded
to the GPU (four per pixel of the band), and bytes of request sent to Lean beyond
the fixed fields. -/
structure Cost where
  layouts : Nat
  renders : Nat
  bytes : Nat
  deriving Repr, DecidableEq

instance : Add Cost := ⟨fun a b => ⟨a.layouts+b.layouts,a.renders+b.renders,a.bytes+b.bytes⟩⟩
instance : OfNat Cost 0 := ⟨⟨0,0,0⟩⟩

@[simp] theorem Cost.add_layouts (a b : Cost) : (a+b).layouts = a.layouts+b.layouts := rfl
@[simp] theorem Cost.add_renders (a b : Cost) : (a+b).renders = a.renders+b.renders := rfl
@[simp] theorem Cost.add_bytes (a b : Cost) : (a+b).bytes = a.bytes+b.bytes := rfl
@[simp] theorem Cost.zero_layouts : (0 : Cost).layouts = 0 := rfl
@[simp] theorem Cost.zero_renders : (0 : Cost).renders = 0 := rfl
@[simp] theorem Cost.zero_bytes : (0 : Cost).bytes = 0 := rfl

def bandBytes (width : Nat) (b : Band) : Nat := width*b.height*4

def cost (s : Session) : Decision → Cost
  | .shift => 0
  | .swap => ⟨0,0,match s.prefetched with | some (_,b) => bandBytes s.key.width b | none => 0⟩
  | .render => ⟨0,1,bandBytes s.key.width (band s.scroll s.view)⟩
  | .layout => ⟨1,1,bandBytes s.key.width (band s.scroll s.view)⟩

/-- A prefetch is made only for the state on screen, whose layout is kept (the host
prefetches only when `canShift()`). It is one render from the kept layout and no
upload: the upload is at the swap. Otherwise it is not made. -/
def prefetchStep (s : Session) (target : Nat) : Session × Decision × Cost :=
  if s.warmFor s.key then ({s with prefetched := some (s.state,band target s.view)},.render,⟨0,1,0⟩)
  else (s,.shift,0)

/-- One event: the session after it, the decision and its cost. -/
def step (s : Session) (e : Event) : Session × Decision × Cost :=
  match e with
  | .prefetch t => prefetchStep s t
  | e => let s' := apply s e; let d := decideFrame s'; (commit s' d,d,cost s' d)

/-- A sequence of events: the last session and the total cost. -/
def run : Session → List Event → Session × Cost
  | s, [] => (s,0)
  | s, e :: es => let r := step s e; let rest := run r.1 es; (rest.1,r.2.2+rest.2)

/-- The decisions of a sequence, in order. -/
def decisions : Session → List Event → List Decision
  | _, [] => []
  | s, e :: es => let (s',d,_) := step s e; d :: decisions s' es

/-- Rows between two scrolls. -/
def dist (a b : Nat) : Nat := (a-b)+(b-a)

/-- Rows the scroll moved over a sequence of events. -/
def travelled : Session → List Event → Nat
  | _, [] => 0
  | s, e :: es => let s' := (step s e).1; dist s.scroll s'.scroll+travelled s' es

/-- Events that change the layout key. -/
def keyChanges : Session → List Event → Nat
  | _, [] => 0
  | s, e :: es => let s' := (step s e).1; (if s'.key = s.key then 0 else 1)+keyChanges s' es

/-- Every key that the sessions of a sequence take is in `W`. A proposition, so no
code is made for it. -/
def KeysIn (W : List Key) : Session → List Event → Prop
  | _, [] => True
  | s, e :: es => (step s e).1.key ∈ W ∧ KeysIn W (step s e).1 es

/-! ## The prefetch rule

`scroll_prefetch.prefetchTarget` with no speed term: the host asks for the next band
when the scroll is `prefetchMargin` rows or fewer from the edge of the keep range it
moves to. The next band starts its keep range where this one's ends. -/

/-- `scroll_prefetch.PREFETCH_MARGIN_ROWS`. -/
def prefetchMargin : Nat := 256

/-- The scroll to draw the next band at, or none when no prefetch is due. -/
def prefetchTarget (b : Band) (view scroll limit : Nat) (down : Bool) : Option Nat :=
  if scroll < b.keepFrom ∨ b.keepTo view < scroll ∨ reach view = 0 then none
  else if down then
    if limit ≤ b.keepTo view ∨ prefetchMargin < b.keepTo view-scroll then none
    else some (min limit (b.keepTo view+reach view))
  else
    if b.keepFrom = 0 ∨ prefetchMargin < scroll-b.keepFrom then none
    else some (b.keepFrom-reach view)

end L4Factoidal.FrameCost
