/-
L4Factoidal.WasmVM.Bench.Sample: op, pair and triple counts of real workloads, by
sampling (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Fused ops").

With `WASMVM_PROFILE` set in the environment, the QuickJS, HarfBuzz and video
benchmarks run their calls through `runIO` here: `gap` instructions at full speed,
then `width` instructions one at a time (fuel 1), each recorded, and so on. A fused
op is recorded as its first part (with fuel 1 `run` executes only that part, and the
parts after it are in the code), so the counts are of the unfused instruction stream,
which is what new fusions are chosen from. Counts are kept in `prof` and printed by
`report`. Outside the benchmarks nothing calls this module.
-/
import L4Factoidal.WasmVM.Api
import Std.Data.HashMap

namespace L4Factoidal.WasmVM.Bench.Sample
open L4Factoidal.WasmVM

abbrev Counts := Std.HashMap String Nat

structure Prof where
  c1 : Counts := {}
  c2 : Counts := {}
  c3 : Counts := {}
  c4 : Counts := {}
  sampled : Nat := 0
  deriving Inhabited

initialize prof : IO.Ref Prof ← IO.mkRef {}

def enabled : IO Bool := return (← IO.getEnv "WASMVM_PROFILE").isSome

/-- The op's constructor, with the numeric, load or store op. -/
def opKey (o : Op) : String :=
  let r := (reprStr o).replace "L4Factoidal.WasmVM." ""
  let ws := (r.splitOn " ").filter (· ≠ "")
  match ws with
  | w :: v :: _ =>
    if w == "Op.num" || w == "Op.load" || w == "Op.store" then w ++ " " ++ (v.replace "(" "").replace ")" "" else w
  | w :: _ => w
  | [] => r

/-- The key of the op that runs first at this pc: a fused op's first part. -/
def key (o : Op) : String :=
  match o.parts with
  | p :: _ => opKey p
  | [] => opKey o

def bump (c : Counts) (k : String) : Counts := c.insert k (c.getD k 0 + 1)

def flush (ks : Array String) : IO Unit :=
  prof.modify fun p => Id.run do
    let mut p := { p with sampled := p.sampled + ks.size }
    for i in [0:ks.size] do
      p := { p with c1 := bump p.c1 ks[i]! }
      if i + 1 < ks.size then p := { p with c2 := bump p.c2 s!"{ks[i]!}; {ks[i+1]!}" }
      if i + 2 < ks.size then p := { p with c3 := bump p.c3 s!"{ks[i]!}; {ks[i+1]!}; {ks[i+2]!}" }
      if i + 3 < ks.size then
        p := { p with c4 := bump p.c4 s!"{ks[i]!}; {ks[i+1]!}; {ks[i+2]!}; {ks[i+3]!}" }
    return p

/-- `runIOSteps`, sampled: the same outcome and instruction count. -/
def runIO (st : Store) (fa : Nat) (args : Array Value) (lim : Budget)
    (host : Nat → Array Value → Store → IO (Store × HostResult)) (maxHostCalls : Nat := 1000000)
    (gap : Nat := 3000) (width : Nat := 48) : IO (Store × Outcome × Nat) := do
  let (st0, o0, n0) := invokeSteps st fa args { lim with fuel := gap }
  let mut st := st0
  let mut o := o0
  let mut n := n0
  let mut single := width
  let mut win : Array String := #[]
  let mut calls := 0
  for _ in [0:lim.fuel] do
    match o with
    | .outOfFuel k =>
      if single > 0 then
        let m := k.machine
        win := win.push (match m.code[m.pc.toNat]? with | some op => key op | none => "?")
        single := single - 1
        let (a, b, c) := resumeSteps st k (.values #[]) { lim with fuel := 1 }
        st := a; o := b; n := n + c
      else
        flush win
        win := #[]
        single := width
        let (a, b, c) := resumeSteps st k (.values #[]) { lim with fuel := gap }
        st := a; o := b; n := n + c
    | .hostCall id vs k =>
      calls := calls + 1
      if calls > maxHostCalls then break
      let (st', r) ← host id vs st
      let (a, b, c) := resumeSteps st' k r { lim with fuel := if single > 0 then 1 else gap }
      st := a; o := b; n := n + c
    | _ => break
  flush win
  return (st, o, n)

/-- The `n` largest counts, largest first. -/
def top (c : Counts) (n : Nat) : List (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  let mut rest := c
  for _ in [0:n] do
    let best := rest.fold (init := ("", 0)) fun b k v => if v > b.2 then (k, v) else b
    if best.2 == 0 then break
    out := out.push best
    rest := rest.erase best.1
  return out.toList

def pct (k total : Nat) : String :=
  let t := k * 1000 / (max total 1)
  s!"{t / 10}.{t % 10}%"

/-- Print the counts under `title`, then clear them. -/
def report (title : String) : IO Unit := do
  let p ← prof.get
  prof.set {}
  if p.sampled == 0 then return
  IO.println s!"== profile {title}: {p.sampled} instructions sampled"
  for (what, c, n) in [("ops", p.c1, 40), ("pairs", p.c2, 40), ("triples", p.c3, 30), ("quads", p.c4, 20)] do
    IO.println s!"-- {what}"
    for (k, m) in top c n do IO.println s!"{pct m p.sampled}\t{m}\t{k}"

end L4Factoidal.WasmVM.Bench.Sample
