import L4Factoidal.FrameCost.Theorems

/-! # Event sequences for the hosts' differential test

`lake exe frame-cost-cases` prints, one JSON line per case, a start session, its events
and, for each event, Lean's decision, cost, band on screen, band drawn ahead and the
prefetch the rule asks for next (`due`, down and up).
`labs/demos/foafnaut/frame_cost_test.ts` replays the events through the host functions
(`layer_compositor.keeps`, `scroll_prefetch.canSwap`, `scroll_prefetch.prefetchTarget`)
and fails on any difference. `--check FILE` exits 1 when FILE is not the output. -/
namespace L4Factoidal.FrameCost.Cases
open L4Factoidal.FrameCost

/-- A linear congruential generator: deterministic, so the fixture is the same on
every machine. -/
def next (x : Nat) : Nat := (x*1103515245+12345) % 2147483648

/-- A number below `n` and the next seed. -/
def pick (x n : Nat) : Nat × Nat := let y := next x; ((y / 65536) % n,y)

/-- The prefetch that the rule asks for after this session's frame, down or up. -/
def due (s : Session) (down : Bool) : Option Nat :=
  match s.shown with
  | some (_,b) => prefetchTarget b s.view s.scroll s.limit down
  | none => none

def event (x : Nat) (s : Session) : Event × Nat :=
  let (kind,x) := pick x 100
  if kind < 50 then
    let (size,x) := pick x 4
    let (amount,x) := pick x (match size with | 0 => 40 | 1 => 400 | 2 => 1200 | _ => 6000)
    let (down,x) := pick x 3
    (.scroll (if down == 0 then -(amount : Int) else amount),x)
  else if kind < 60 then
    -- Half of the prefetches are the ones the rule asks for, when it asks for one.
    let (rule,x) := pick x 2
    let (up,x) := pick x 2
    let (off,x) := pick x 1600
    match rule,due s (up == 0) with
    | 0,some t => (.prefetch t,x)
    | _,_ => (.prefetch (s.scroll+off-min (s.scroll+off) 800),x)
  else if kind < 65 then
    let (w,x) := pick x 2
    let (h,x) := pick x 2
    (.resize (if w == 0 then 800 else 640) (if h == 0 then 600 else 500),x)
  else if kind < 70 then
    let (p,x) := pick x 2
    (.zoom (if p == 0 then 100 else 110),x)
  else if kind < 78 then
    -- Pointer state 2 has a `:hover` style that changes geometry; 1 has colours only.
    let (e,x) := pick x 3
    (.hover e (e == 2),x)
  else if kind < 80 then
    let (v,x) := pick x 2
    (.visit v,x)
  else if kind < 83 then
    let (p,x) := pick x 2
    (.navigate p (if p == 0 then 3000 else 9000),x)
  else if kind < 85 then (.fontLoad,x)
  else if kind < 88 then
    -- Painted values other than the pointer states 0 to 2, as a host's requests differ.
    let (v,x) := pick x 4
    (.paintOnly (v+3),x)
  else (.tick,x)

def eventJSON : Event → String
  | .scroll d => s!"[\"scroll\",{d}]"
  | .resize w h => s!"[\"resize\",{w},{h}]"
  | .zoom p => s!"[\"zoom\",{p}]"
  | .visit v => s!"[\"visit\",{v}]"
  | .hover e g => s!"[\"hover\",{e},{if g then 1 else 0}]"
  | .navigate p l => s!"[\"navigate\",{p},{l}]"
  | .fontLoad => "[\"fontLoad\"]"
  | .prefetch t => s!"[\"prefetch\",{t}]"
  | .tick => "[\"tick\"]"
  | .paintOnly v => s!"[\"paintOnly\",{v}]"

def bandJSON (view : Nat) : Option (Shown × Band) → String
  | some (_,b) => s!"[{b.top},{b.height},{b.keepFrom},{b.keepTo view}]"
  | none => "null"

def optJSON : Option Nat → String
  | some n => toString n
  | none => "null"

/-- The steps of a case as JSON objects, in order (a tail-recursive loop that makes the
events as it goes, since a prefetch the rule asks for depends on the band on screen). -/
def stepsJSON (s : Session) (seed count : Nat) : List String :=
  let rec go : Nat → Nat → Session → List String → List String
    | 0, _, _, acc => acc.reverse
    | n+1, x, s, acc =>
      let (e,x) := event x s
      let (s',d,c) := step s e
      go n x s' (s!"\{\"event\":{eventJSON e},\"decision\":\"{d.name}\",\"cost\":[{c.layouts},{c.renders},{c.bytes}],\"scroll\":{s'.scroll},\"view\":{s'.view},\"limit\":{s'.limit},\"shown\":{bandJSON s'.view s'.shown},\"prefetched\":{bandJSON s'.view s'.prefetched},\"due\":[{optJSON (due s' true)},{optJSON (due s' false)}]}" :: acc)
  go count (next (seed+1)) s []

def startKey : Key := ⟨0,800,600,80,100,0,0,0⟩

def caseJSON (seed : Nat) : String :=
  let s := Session.start startKey 3000
  let steps := ",".intercalate (stepsJSON s seed 40)
  s!"\{\"seed\":{seed},\"width\":800,\"height\":600,\"top\":80,\"limit\":3000,\"slots\":{layoutSlots},\"steps\":[{steps}]}"

def output : String := "\n".intercalate ((List.range 80).map caseJSON) ++ "\n"

end L4Factoidal.FrameCost.Cases
