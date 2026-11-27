import L4Factoidal.WasmVM.Hosts.LeanJSRealm

/-!
# Time of BubblePopJS's realm decode

`LeanJS.prepare` decodes the realm snapshot made at build time (`LeanJSRealmData`). Every
engine does this once, at the start turn of its first page with scripts (issue 471). This
program decodes it `n` times (argument, default 20) and prints the time of each decode and a
check value (objects, environments, and the sum of the property counts), so two builds can be
compared on the same data.
-/
open L4Factoidal.WasmVM.Hosts

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 20
  let mut times := #[]
  let mut check := ""
  for _ in [0:n] do
    let t0 ← IO.monoNanosNow
    match LeanJS.prepare with
    | .error e => IO.eprintln s!"realm: {e}"; return 1
    | .ok s =>
      let props := s.heap.objs.foldl (fun acc o => acc + o.keys.size) 0
      check := s!"objs {s.heap.objs.size} envs {s.heap.envs.size} props {props}"
      let t1 ← IO.monoNanosNow
      times := times.push ((t1 - t0) / 1000)
  let sorted := times.qsort (· < ·)
  IO.println s!"{check}"
  IO.println s!"decode us: min {sorted[0]!} p50 {sorted[sorted.size / 2]!} max {sorted[sorted.size - 1]!} (n={n})"
  return 0
