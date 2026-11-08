import L4Factoidal.FrameCost.Cases

/-! `lake exe frame-cost-cases`: the event sequences that labs/demos/foafnaut/frame_cost_test.ts
replays. The entry point lives here, not in L4Factoidal/FrameCost/Cases.lean, because the
library imports Cases and the Wasm build links every library module: a `main` there clashed
with the other `main` in the link (Wasm/build-wasm.sh skips Harness units). -/

open L4Factoidal.FrameCost.Cases in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--check",file] =>
    if (← IO.FS.readFile file) == output then return 0
    IO.eprintln s!"{file} is not the output of frame-cost-cases: regenerate it with `lake exe frame-cost-cases > {file}`"
    return 1
  | [] => IO.print output; return 0
  | _ => IO.eprintln "usage: frame-cost-cases [--check FILE]"; return 2
