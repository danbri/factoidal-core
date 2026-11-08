import L4Factoidal.FrameCost.Theorems

/-! # Event sequences for the hosts' differential test

`lake exe frame-cost-cases` prints, one JSON line per case, a start session, its events
and, for each event, Lean's decision, cost and band on screen.
`labs/demos/foafnaut/frame_cost_test.ts` replays the events through the host functions
(`layer_compositor.keeps`, `scroll_prefetch.canSwap`) and fails on any difference.
`--check FILE` exits 1 when FILE is not the output. -/
namespace L4Factoidal.FrameCost.Cases
open L4Factoidal.FrameCost

/-- A linear congruential generator: deterministic, so the fixture is the same on
every machine. -/
def next (x : Nat) : Nat := (x*1103515245+12345) % 2147483648

/-- A number below `n` and the next seed. -/
def pick (x n : Nat) : Nat × Nat := let y := next x; ((y / 65536) % n,y)

def event (x scroll : Nat) : Event × Nat :=
  let (kind,x) := pick x 100
  if kind < 50 then
    let (size,x) := pick x 4
    let (amount,x) := pick x (match size with | 0 => 40 | 1 => 400 | 2 => 1200 | _ => 6000)
    let (down,x) := pick x 3
    (.scroll (if down == 0 then -(amount : Int) else amount),x)
  else if kind < 60 then
    let (off,x) := pick x 1600
    (.prefetch (scroll+off-min (scroll+off) 800),x)
  else if kind < 65 then
    let (w,x) := pick x 2
    let (h,x) := pick x 2
    (.resize (if w == 0 then 800 else 640) (if h == 0 then 600 else 500),x)
  else if kind < 70 then
    let (p,x) := pick x 2
    (.zoom (if p == 0 then 100 else 110),x)
  else if kind < 80 then
    let (e,x) := pick x 3
    (.element e,x)
  else if kind < 83 then
    let (p,x) := pick x 2
    (.navigate p (if p == 0 then 3000 else 9000),x)
  else if kind < 85 then (.fontLoad,x)
  else (.tick,x)

def events (seed count : Nat) : List Event :=
  let rec go : Nat → Nat → Nat → List Event → List Event
    | 0, _, _, acc => acc.reverse
    | n+1, x, scroll, acc =>
      let (e,x) := event x scroll
      let scroll := match e with
        | .scroll d => clampScroll 9000 scroll d
        | .navigate _ _ => 0
        | _ => scroll
      go n x scroll (e :: acc)
  go count (next (seed+1)) 0 []

def startKey : Key := ⟨0,800,600,80,100,0,0⟩

def eventJSON : Event → String
  | .scroll d => s!"[\"scroll\",{d}]"
  | .resize w h => s!"[\"resize\",{w},{h}]"
  | .zoom p => s!"[\"zoom\",{p}]"
  | .element e => s!"[\"element\",{e}]"
  | .navigate p l => s!"[\"navigate\",{p},{l}]"
  | .fontLoad => "[\"fontLoad\"]"
  | .prefetch t => s!"[\"prefetch\",{t}]"
  | .tick => "[\"tick\"]"

def bandJSON (view : Nat) : Option (Key × Band) → String
  | some (_,b) => s!"[{b.top},{b.height},{b.keepFrom},{b.keepTo view}]"
  | none => "null"

/-- The steps of a case as JSON objects, in order (a tail-recursive loop). -/
def stepsJSON (s : Session) (es : List Event) : List String :=
  let rec go : Session → List Event → List String → List String
    | _, [], acc => acc.reverse
    | s, e :: es, acc =>
      let (s',d,c) := step s e
      go s' es (s!"\{\"event\":{eventJSON e},\"decision\":\"{d.name}\",\"cost\":[{c.layouts},{c.renders},{c.bytes}],\"scroll\":{s'.scroll},\"view\":{s'.view},\"shown\":{bandJSON s'.view s'.shown},\"prefetched\":{bandJSON s'.view s'.prefetched}}" :: acc)
  go s es []

def caseJSON (seed : Nat) : String :=
  let s := Session.start startKey 3000
  let steps := ",".intercalate (stepsJSON s (events seed 40))
  s!"\{\"seed\":{seed},\"width\":800,\"height\":600,\"top\":80,\"limit\":3000,\"steps\":[{steps}]}"

def output : String := "\n".intercalate ((List.range 80).map caseJSON) ++ "\n"

end L4Factoidal.FrameCost.Cases

open L4Factoidal.FrameCost.Cases in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--check",file] =>
    if (← IO.FS.readFile file) == output then return 0
    IO.eprintln s!"{file} is not the output of frame-cost-cases: regenerate it with `lake exe frame-cost-cases > {file}`"
    return 1
  | [] => IO.print output; return 0
  | _ => IO.eprintln "usage: frame-cost-cases [--check FILE]"; return 2
