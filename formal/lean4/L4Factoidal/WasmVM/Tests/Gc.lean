/-
L4Factoidal.WasmVM.Tests.Gc: tests of the garbage-collection proposal that the spec
suite does not have (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "GC").

Run by `lake exe wasmvm-spectest` (after the spec tests). The spec tests cover the
instructions and the type rules.

`noCopy`: a loop of `array.set` on an array of 8 elements and on one of 200 000
elements (1.6 MB of slots). A write that copied the array would make the second run
take seconds; the test allows 4 times the first run plus 200 ms, as `Tests/Simd.lean`
does for the hi stack.

`plain`: a module with function types only gets the same type ids with and without
`Module.typeDefs`, and they are the ids that `StoreOf.typeId` gives.

`refusals`: what the engine refuses, each with its text.
-/
import L4Factoidal.WasmVM.Api

namespace L4Factoidal.WasmVM.Tests.Gc

def arrI32 : TypeDef := { sub := { comp := .array ⟨true, .val .i32⟩ }, recStart := 0 }

/-- `(func (export "loop") (param $len i32) (param $n i32) (result i32))`: makes an
array of `$len` elements, writes `$n`, `$n - 1`, .. 1 into element 0, and gives
element 0. -/
def loopModule : Module :=
  let ft : FuncType := ⟨#[.i32, .i32], #[.i32]⟩
  { types := #[⟨#[], #[]⟩, ft]
    typeDefs := #[arrI32, { sub := { comp := .func ft }, recStart := 1 }]
    funcs := #[{ type := 1, locals := #[.ref ⟨true, .idx 0⟩],
                 body := #[.localGet 0, .gc GcCode.arrayNewDefault 0 0, .localSet 2,
                           .loop .empty,
                           .localGet 2, .i32Const 0, .localGet 1, .gc GcCode.arraySet 0 0,
                           .localGet 1, .i32Const 1, .num .i32_sub, .localTee 1, .brIf 0, .end_,
                           .localGet 2, .i32Const 0, .gc GcCode.arrayGet 0 0, .end_] }]
    exports := #[{ name := "loop", desc := .func 0 }] }

def noHost : PureHost ByteMem := fun _ _ st => (st, .values #[])

/-- Time of `n` writes into an array of `len` elements, in nanoseconds; none when the
run failed or gave a wrong value. -/
def timeLoop (len n : Nat) : IO (Option Nat) := do
  let .ok vm := validate loopModule | return none
  let (st, r) := instantiateRun noHost {} vm #[]
  let .ok ia := r | return none
  let some (.func fa) := st.export? ia "loop" | return none
  let t0 ← IO.monoNanosNow
  let (_, o) ← IO.lazyPure fun _ => invoke st fa #[.i32 (UInt32.ofNat len), .i32 (UInt32.ofNat n)]
  let t1 ← IO.monoNanosNow
  match o with
  | .values #[.i32 1] => return some (t1 - t0)
  | _ => return none

def noCopy : IO Bool := do
  let n := 20000
  let some small ← timeLoop 8 n | IO.println "gc array no-copy: FAIL (setup)"; return false
  let some big ← timeLoop 200000 n | IO.println "gc array no-copy: FAIL (setup)"; return false
  let ok := big ≤ 4 * small + 200000000
  IO.println s!"gc array no-copy: {n} writes, array of 8 elements {small / 1000000} ms, of 200000 elements {big / 1000000} ms: {if ok then "pass" else "FAIL"}"
  return ok

/-- The type ids of a module instantiated in an empty store. -/
def idsOf (m : Module) : Option (Array Nat × Nat) :=
  match validate m with
  | .error _ => none
  | .ok vm =>
    let (st, r) := instantiateRun noHost {} vm #[]
    match r with
    | .ok ia => some ((st.insts[ia]!).typeIds, st.exc.gc.types.size)
    | .error _ => none

def plain : IO Bool := do
  let a : FuncType := ⟨#[.i32], #[.i32]⟩
  let b : FuncType := ⟨#[.ref ⟨true, .idx 1⟩], #[]⟩
  let types := #[a, b, a]
  let m1 : Module := { types }
  let m2 : Module := { types, typeDefs := types.mapIdx fun i ft => { sub := { comp := .func ft }, recStart := i } }
  let want := some (#[0, 1, 0], 0)
  let ok := idsOf m1 == want && idsOf m2 == want
  IO.println s!"gc plain function types keep their ids: {if ok then "pass" else "FAIL"}"
  return ok

/-- What the engine refuses of the garbage-collection proposal. Each check expects the
refusal with its text. When a part is implemented its check fails here: change the
check and its issue together.
1. A struct field or an array element of type v128: validation error.
2. An array of more than `Run.maxArrayLen` elements: trap. -/
def refusals : IO Bool := do
  let v128Def : TypeDef := { sub := { comp := .struct #[⟨false, .val .v128⟩] }, recStart := 0 }
  let field := match validate { types := #[⟨#[], #[]⟩], typeDefs := #[v128Def] } with
    | .error e => e.msg == "unsupported: v128 field in a struct or array type"
    | .ok _ => false
  let big ← (do
    let .ok vm := validate loopModule | return false
    let (st, r) := instantiateRun noHost {} vm #[]
    let .ok ia := r | return false
    let some (.func fa) := st.export? ia "loop" | return false
    match (invoke st fa #[.i32 (UInt32.ofNat (Run.maxArrayLen + 1)), .i32 1]).2 with
    | .trap t => return t.message == "array larger than the engine limit"
    | _ => return false : IO Bool)
  let ok := field && big
  IO.println s!"gc refusals: v128 field {field}, array over the engine limit {big}: {if ok then "pass" else "FAIL"}"
  return ok

def run : IO Bool := do
  let a ← noCopy
  let b ← plain
  let c ← refusals
  return a && b && c

end L4Factoidal.WasmVM.Tests.Gc
