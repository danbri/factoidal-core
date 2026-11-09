/-
L4Factoidal.HTML.FrameSessions — the script sessions of a page and of its sandboxed
frames, and the messages between them (record:
docs/designissues/2026-11-08-shadow-dom-frames.md, "Frames").

A frame whose document has an opaque origin and may run scripts
(`HTML.Frames.Frame.scriptsMayRun`, no `allow-same-origin`) gets a script session of its
own: its own document (an arena of its own), its own JavaScript heap (a WasmVM instance
or a BubblePopJS realm) and its own event loop, with its own budgets. The host keeps the
sessions in a `SessionMap`: the page's session and each frame's, by the frame's `iframe`
element. Sessions meet only through `Message`s, which hold strings (the serialized data and
the source origin); `exchange` hands each session the messages addressed to it.

Theorems (`exchange_frame`, `exchange_parent`, `exchange_isolated`): after an exchange,
each session is a function of its own state before and of the messages addressed to it;
two maps that differ only in another session's state give it the same new state. So a
frame's script session never reads or writes another session's heap: only strings cross.
-/
namespace L4Factoidal.HTML.FrameSessions

/-- A message between the page and a frame (HTML §9.3.3): the `iframe` element of the frame
in the page, the direction, the serialized data, and the serialized origin of the
source. -/
structure Message where
  frame : Nat
  toParent : Bool
  data : String
  origin : String
  deriving DecidableEq, Repr, Inhabited

/-- The sessions of a page: its own, and each sandboxed frame's by its `iframe` element. -/
structure SessionMap (σ : Type) where
  parent : σ
  frames : Array (Nat × σ) := #[]

/-- The messages for the page. -/
def forParent (ms : Array Message) : Array Message := ms.filter (·.toParent)

/-- The messages for the frame of `el`. -/
def forFrame (ms : Array Message) (el : Nat) : Array Message := ms.filter fun m => !m.toParent && m.frame == el

/-- One exchange: each session runs once (`run`) on the messages addressed to it, and
answers its new state and the messages it sent. The page's messages for a frame name that
frame; a frame's messages always go to the page (`toParent`) through its own element. -/
def exchange {σ : Type} (run : σ → Array Message → σ × Array Message) (m : SessionMap σ) (ms : Array Message) :
    SessionMap σ × Array Message :=
  let p := run m.parent (forParent ms)
  let fs := m.frames.map fun (el, s) => (el, run s (forFrame ms el))
  ({ parent := p.1, frames := fs.map fun (el, r) => (el, r.1) },
   p.2.map (fun x => { x with toParent := false }) ++
     fs.flatMap fun (el, r) => r.2.map fun x => { x with toParent := true, frame := el })

/-- A frame's session after an exchange is its run on its own state and its own messages. -/
theorem exchange_frame {σ : Type} (run : σ → Array Message → σ × Array Message) (m : SessionMap σ)
    (ms : Array Message) (i : Nat) (h : i < m.frames.size) :
    ((exchange run m ms).1.frames[i]?) =
      some (m.frames[i].1, (run m.frames[i].2 (forFrame ms m.frames[i].1)).1) := by
  simp [exchange, h]

/-- The page's session after an exchange is its run on its own state and its messages. -/
theorem exchange_parent {σ : Type} (run : σ → Array Message → σ × Array Message) (m : SessionMap σ)
    (ms : Array Message) : (exchange run m ms).1.parent = (run m.parent (forParent ms)).1 := rfl

/-- Isolation: two maps whose frame `i` has the same element and state give frame `i` the
same new state, whatever the other sessions hold. -/
theorem exchange_isolated {σ : Type} (run : σ → Array Message → σ × Array Message) (m m' : SessionMap σ)
    (ms : Array Message) (i : Nat) (h : i < m.frames.size) (h' : i < m'.frames.size)
    (same : m.frames[i] = m'.frames[i]) :
    (exchange run m ms).1.frames[i]? = (exchange run m' ms).1.frames[i]? := by
  rw [exchange_frame run m ms i h, exchange_frame run m' ms i h', same]

end L4Factoidal.HTML.FrameSessions
