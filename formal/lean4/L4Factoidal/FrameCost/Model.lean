/-! # Frame scheduling in the Foafnaut hosts, with its cost

Record: `docs/designissues/2026-11-08-cost-theorems.md`. Issue 1268.

A host session holds the layout key of the page, the scroll, the band of page rows on
screen, the kept layout (one entry, as `WebDocument.layoutRef`) and a prefetched band.
For each event the host does one of four things:

* `shift`: the band on screen keeps the scroll; the composite runs at a new offset.
  No Lean call.
* `swap`: a prefetched band of the same state keeps the scroll; it is uploaded and
  shown. No Lean call (the prefetch already paid its render).
* `render`: the kept layout is the layout of this key; Lean draws a new band from it.
* `layout`: the key is new; Lean parses, cascades and lays out, then draws a band.

The band and its keep range are `WebDocument.band`, `Band.keepFrom` and `Band.keepTo`
with the same numbers; `run_html.ts` reads `keepFrom` and `keepTo` from Lean's answer
and tests them with `layer_compositor.keeps`. The key has the fields of
`WebDocument.LayoutKey`; the scroll is not one of them, as it is not in that structure.

Only Lean core. -/
namespace L4Factoidal.FrameCost

/-- Page rows that a page layer keeps above and below the view (`WebDocument.bandMargin`). -/
def bandMargin : Nat := 512
/-- `WebDocument.refreshMargin`. -/
def refreshMargin : Nat := 128
/-- `WebDocument.maxLayerRows`. -/
def maxLayerRows : Nat := 4096

/-- The page rows of a page layer: from page row `top`, `height` rows. -/
structure Band where
  top : Nat
  height : Nat
  deriving Repr, DecidableEq

/-- The margin of a band for a view of `view` rows. -/
def margin (view : Nat) : Nat := min bandMargin ((maxLayerRows-view)/2)

/-- The band around a view of `view` rows from page row `scroll` (`WebDocument.band`). -/
def band (scroll view : Nat) : Band :=
  ⟨scroll-min scroll (margin view),view+2*margin view⟩

/-- `WebDocument.Band.keepFrom`. -/
def Band.keepFrom (b : Band) : Nat := if b.top = 0 then 0 else b.top+refreshMargin
/-- `WebDocument.Band.keepTo`. -/
def Band.keepTo (b : Band) (view : Nat) : Nat := b.top+b.height-view-refreshMargin
/-- `layer_compositor.keeps`: the band shows this scroll with no new render. -/
def Band.keeps (b : Band) (view scroll : Nat) : Bool :=
  decide (b.keepFrom ≤ scroll) && decide (scroll ≤ b.keepTo view)

/-- Rows that a band made at scroll `s` keeps on each side of `s`
(`scroll_prefetch.keepReach`): 384 for a view of at most 3072 rows. -/
def reach (view : Nat) : Nat := margin view-refreshMargin

/-- The fields of `WebDocument.LayoutKey`, each named by a number. `page` stands for
the HTML and the request fields that name the document (`url`, `resources`,
`commands`, `images`, `graphModel`, `media`); `element` for `hover`, `active` and
`visited`; `fonts` for the held font list. There is no scroll. -/
structure Key where
  page : Nat
  width : Nat
  height : Nat
  /-- Height of the browser chrome above the page. -/
  top : Nat
  /-- `textScalePercent`. -/
  scale : Nat
  element : Nat
  fonts : Nat
  deriving Repr, DecidableEq

/-- A host session. -/
structure Session where
  key : Key
  scroll : Nat
  /-- The largest scroll of the page. -/
  limit : Nat
  /-- The band on screen and the key it was drawn for. -/
  shown : Option (Key × Band)
  /-- The key of the kept layout (`WebDocument.layoutRef` holds one entry). -/
  kept : Option Key
  /-- A band drawn ahead for a key (`run_html.ts` `prefetched`). -/
  prefetched : Option (Key × Band)
  deriving Repr

/-- Page rows of the window. -/
def Session.view (s : Session) : Nat := s.key.height-s.key.top

/-- The first session of a window: nothing drawn, nothing kept. -/
def Session.start (key : Key) (limit : Nat) : Session :=
  {key, scroll := 0, limit, shown := none, kept := none, prefetched := none}

inductive Event where
  /-- A wheel or key scroll by `delta` rows; the host clamps it to `0 .. limit`. -/
  | scroll (delta : Int)
  | resize (width height : Nat)
  /-- Text zoom to `percent`. -/
  | zoom (percent : Nat)
  /-- A change of hover, active or visited state. -/
  | element (state : Nat)
  | navigate (page limit : Nat)
  | fontLoad
  /-- The host asks the worker for a band at this scroll (`scroll_prefetch.prefetchTarget`). -/
  | prefetch (target : Nat)
  /-- A timer tick with no DOM change. -/
  | tick
  deriving Repr, DecidableEq

def clampScroll (limit scroll : Nat) (delta : Int) : Nat :=
  min limit ((scroll : Int)+delta).toNat

/-- What an event changes, before the host decides how to draw. -/
def apply (s : Session) : Event → Session
  | .scroll d => {s with scroll := clampScroll s.limit s.scroll d}
  | .resize w h => {s with key := {s.key with width := w, height := h}, scroll := min s.scroll s.limit}
  | .zoom p => {s with key := {s.key with scale := p}}
  | .element e => {s with key := {s.key with element := e}}
  | .navigate p l => {s with key := {s.key with page := p}, scroll := 0, limit := l}
  | .fontLoad => {s with key := {s.key with fonts := s.key.fonts+1}}
  | .prefetch _ => s
  | .tick => s

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

/-- A band for `key` that keeps `scroll`. -/
def keepsFor (band : Option (Key × Band)) (key : Key) (view scroll : Nat) : Bool :=
  match band with
  | some (k,b) => decide (k = key) && b.keeps view scroll
  | none => false

/-- The decision for a session after an event changed it: the one source of truth.
`run_html.ts` makes it as `canShift() && keeps(...)`, then `swapReady()` or
`bandComing()`, then a Lean frame (`dirty`), which takes the kept layout when the
key is the same (`WebDocument.cachedLayOut`). -/
def decideFrame (s : Session) : Decision :=
  if keepsFor s.shown s.key s.view s.scroll then .shift
  else if keepsFor s.prefetched s.key s.view s.scroll then .swap
  else if s.kept = some s.key then .render
  else .layout

/-- What a decision leaves. A layout replaces the kept entry; a band made for the old
entry is dropped with it (the host drops a prefetched band of another state). -/
def commit (s : Session) : Decision → Session
  | .shift => s
  | .swap => {s with shown := s.prefetched, prefetched := none}
  | .render => {s with shown := some (s.key,band s.scroll s.view)}
  | .layout => {s with kept := some s.key, shown := some (s.key,band s.scroll s.view), prefetched := none}

/-- The work of one step: Lean layouts, Lean band renders, and bytes of page layer
uploaded to the GPU (four per pixel of the band). -/
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

/-- A prefetch is made only for the state whose layout is kept (the host prefetches
only when `canShift()`, with a band of this state on screen). It is one render from
the kept layout and no upload: the upload is at the swap. Otherwise it is not made. -/
def prefetchStep (s : Session) (target : Nat) : Session × Decision × Cost :=
  if s.kept = some s.key then ({s with prefetched := some (s.key,band target s.view)},.render,⟨0,1,0⟩)
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

end L4Factoidal.FrameCost
