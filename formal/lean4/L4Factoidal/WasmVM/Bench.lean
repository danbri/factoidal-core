import L4Factoidal.WasmVM.Bench.Repr

/-! `lake exe wasmvm-bench`: measurements for the WasmVM engine (issue 1244). -/

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 20000000
  L4Factoidal.WasmVM.Bench.Repr.run n
  return 0
