import L4Factoidal.WasmVM.Api

/-! A native measurement of SIMD dispatch, with the opcode supplied at run time.
`lake exe wasmvm-simd-dispatch direct|engine OPCODE COUNT`.
The direct case isolates the dispatch. The engine case includes local accesses,
the scalar loop counter and fuel accounting. The printed result checks that the
same workload was executed in before/after builds. No browser speed is inferred.
-/

namespace L4Factoidal.WasmVM.Bench.SimdDispatch

def directLoop (c : Nat) : Nat → Store → Slots → UInt64
  | 0, st, stack => Run.rd stack 0 ^^^ Run.hiRd st 0
  | n + 1, st, stack =>
    match Run.simdStep st stack (if c == 0x4d then 1 else 2) {} c 0 0 0 with
    | .ok st stack _ => directLoop c n st stack
    | .trap _ _ _ => 0

def seed : UInt64 := 0x123456789ABCDEF0
def mask : UInt64 := 0xF0F00F0FF0F00F0F

def direct (c n : Nat) : IO Unit := do
  let stack := Slots.zeros 2
  let stack := Run.wr (Run.wr stack 0 seed) 1 mask
  let st : Store := { exc := { hi := Run.wr (Run.wr (Slots.zeros 2) 0 mask) 1 seed } }
  let t0 ← IO.monoNanosNow
  let result ← IO.lazyPure fun _ => directLoop c n st stack
  let t1 ← IO.monoNanosNow
  IO.println s!"direct\t{c}\t{n}\t{t1-t0}\t{result}"

def program (c : Nat) : Module :=
  let body := #[.localGet 1] ++ (if c == 0x4d then #[] else #[.localGet 2]) ++
    #[.simd c ⟨0, 0, 0⟩ 0 0 0, .localSet 1,
      .localGet 0, .i32Const 1, .num .i32_sub, .localTee 0, .brIf 0, .end_,
      .localGet 1, .end_]
  { types := #[⟨#[.i32, .v128, .v128], #[.v128]⟩]
    funcs := #[{ type := 0, locals := #[], body := #[.loop .empty] ++ body }]
    exports := #[{ name := "loop", desc := .func 0 }] }

def engine (c n : Nat) : IO UInt32 := do
  let .ok vm := validate (program c) | IO.eprintln "validation failed"; return 1
  let (st, inst) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := inst | IO.eprintln "instantiation failed"; return 1
  let some (.func fa) := st.export? ia "loop" | return 1
  let t0 ← IO.monoNanosNow
  let (_, result) ← IO.lazyPure fun _ =>
    invoke st fa #[.i32 n.toUInt32, .v128 seed mask, .v128 mask seed]
      { fuel := n * 16 + 100 }
  let t1 ← IO.monoNanosNow
  match result with
  | .values vals => IO.println s!"engine\t{c}\t{n}\t{t1-t0}\t{repr vals}"; return 0
  | _ => IO.eprintln "invocation failed"; return 1

end L4Factoidal.WasmVM.Bench.SimdDispatch

def main (args : List String) : IO UInt32 := do
  let [mode, code, count] := args | IO.eprintln "usage: direct|engine OPCODE COUNT"; return 1
  let some c := code.toNat? | return 1
  let some n := count.toNat? | return 1
  if n == 0 then return 1
  if mode == "direct" then
    L4Factoidal.WasmVM.Bench.SimdDispatch.direct c n
    return 0
  else if mode == "engine" then
    L4Factoidal.WasmVM.Bench.SimdDispatch.engine c n
  else return 1
