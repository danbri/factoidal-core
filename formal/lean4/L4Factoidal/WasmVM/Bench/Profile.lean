/-
L4Factoidal.WasmVM.Bench.Profile: counts of adjacent op pairs and triples, to choose
fused ops (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Fused ops").

- `dynamic`: runs the benchmark exports one instruction at a time (fuel 1 per call of
  `Run.run`) and counts the op sequences executed.
- `static`: decodes and validates every `.wasm` file under a directory (the spec-test
  modules) and counts op sequences in the compiled code.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Bench.Engine
import Std.Data.HashMap

namespace L4Factoidal.WasmVM.Bench.Profile
open L4Factoidal.WasmVM

/-- The op's constructor, with the numeric, load or store op. -/
def opKey (o : Op) : String :=
  let r := (reprStr o).replace "L4Factoidal.WasmVM." ""
  let ws := (r.splitOn " ").filter (· ≠ "")
  match ws with
  | w :: v :: _ => if w == "Op.num" || w == "Op.load" || w == "Op.store" then w ++ " " ++ (v.replace "(" "").replace ")" "" else w
  | w :: _ => w
  | [] => r

abbrev Counts := Std.HashMap String Nat

def bump (c : Counts) (k : String) : Counts := c.insert k (c.getD k 0 + 1)

/-- Trace `steps` instructions of export `name` with argument `arg`. -/
def traceExport (st : Store) (ia : Nat) (name : String) (arg : Nat) (steps : Nat) : Array String := Id.run do
  let some (.func fa) := st.export? ia name | return #[]
  let stack := Run.wr (Slots.zeros 1024) 0 arg.toUInt64
  let code : Array Op := #[.call 0, .return_ 1]
  let mut m : Machine := ⟨stack, 1, 0, 0, code, { funcs := #[fa] }, #[]⟩
  let mut st := st
  let mut out := #[]
  for _ in [0:steps] do
    let some o := m.code[m.pc.toNat]? | break
    out := out.push (opKey o)
    let (st', m', _, ev) := Run.runM {} st m 1
    st := st'; m := m'
    match ev with
    | .outOfFuel => pure ()
    | _ => break
  return out

def countSeqs (c2 c3 : Counts) (ks : Array String) : Counts × Counts := Id.run do
  let mut c2 := c2
  let mut c3 := c3
  for i in [0:ks.size] do
    if i + 1 < ks.size then c2 := bump c2 s!"{ks[i]!}; {ks[i+1]!}"
    if i + 2 < ks.size then c3 := bump c3 s!"{ks[i]!}; {ks[i+1]!}; {ks[i+2]!}"
  return (c2, c3)

/-- The `n` largest counts, largest first (a fold per entry; `n` is small). -/
def top (c : Counts) (n : Nat) : List (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  let mut rest := c
  for _ in [0:n] do
    let best := rest.fold (init := ("", 0)) fun b k v => if v > b.2 then (k, v) else b
    if best.2 == 0 then break
    out := out.push best
    rest := rest.erase best.1
  return out.toList

def report (title : String) (c2 c3 : Counts) : IO Unit := do
  IO.println s!"== {title}: pairs"
  for (k, n) in top c2 25 do IO.println s!"{n}\t{k}"
  IO.println s!"== {title}: triples"
  for (k, n) in top c3 25 do IO.println s!"{n}\t{k}"

def dynamic : IO Unit := do
  let .ok m := decode Engine.benchModule | IO.println "decode failed"
  let .ok vm := validate m | IO.println "invalid"
  let (st, r) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | IO.println "instantiation failed"
  let mut c2 : Counts := {}
  let mut c3 : Counts := {}
  for (name, arg) in [("sum", 1000), ("memsum", 1000), ("fib", 12)] do
    let ks := traceExport st ia name arg 100000
    (c2, c3) := countSeqs c2 c3 ks
  report "benchmarks, executed" c2 c3

def static (dir : System.FilePath) : IO Unit := do
  let all ← dir.walkDir
  let mut c2 : Counts := {}
  let mut c3 : Counts := {}
  let mut nmod := 0
  for p in all do
    if p.extension != some "wasm" then continue
    let b ← IO.FS.readBinFile p
    let .ok m := decode b | continue
    let .ok vm := validate m | continue
    nmod := nmod + 1
    for cf in vm.code do
      (c2, c3) := countSeqs c2 c3 (cf.code.map opKey)
  report s!"spec-test modules ({nmod}), compiled code" c2 c3

end L4Factoidal.WasmVM.Bench.Profile
