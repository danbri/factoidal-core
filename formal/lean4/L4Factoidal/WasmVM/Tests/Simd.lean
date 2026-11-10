/-
L4Factoidal.WasmVM.Tests.Simd: tests of how v128 values move
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "SIMD").

Run by `lake exe wasmvm-spectest` (after the spec tests). The spec tests cover the
SIMD instructions. These cases cover the ops that move both halves of a v128 value:
a branch, `br_if` and `br_table` that move a kept v128 down, `return`, a tail call
with a v128 argument, a v128 local at function entry, `local.tee`, `select`, a v128
global, the end of a legacy catch clause, `br_on_null`, and a function with two
results. Each case first leaves a different high half in the slot that the value
moves to (`v128.const B; drop`), so an op that moves the low half only gives a wrong
result.

The module is a `Module` value, not a binary: the cases need instruction sequences
that a compiler does not emit on request.

`noCopy`: a loop of `i8x16.add` on a v128 local runs with the local at slot 2 and at
slot 40 000 (a hi stack of 320 KiB). A write that copied the hi stack would make the
second run take seconds; the test allows 4 times the first run plus 200 ms, as
`Tests/Memory.lean` does for the linear memory.
-/
import L4Factoidal.WasmVM.Api

namespace L4Factoidal.WasmVM.Tests.Simd

def aLo : UInt64 := 0x1111111111111111
def aHi : UInt64 := 0xAAAAAAAAAAAAAAAA
def bLo : UInt64 := 0x2222222222222222
def bHi : UInt64 := 0xBBBBBBBBBBBBBBBB
def cLo : UInt64 := 0x3333333333333333
def cHi : UInt64 := 0xCCCCCCCCCCCCCCCC

def vconst (lo hi : UInt64) : Instr := .simd 0x0c ⟨0, 0, 0⟩ 0 lo hi
def cA : Instr := vconst aLo aHi
def cB : Instr := vconst bLo bHi
def cC : Instr := vconst cLo cHi

def vblock : Instr := .block (.val .v128)

/-- (export name, type index, declared locals, body). -/
def funcs : Array (String × Nat × Array ValType × Array Instr) :=
  #[("br", 0, #[], #[cB, .drop, vblock, .i32Const 7, cA, .br 0, .end_, .end_]),
    ("br_if", 1, #[], #[cB, .drop, vblock, .i32Const 7, cA, .localGet 0, .brIf 0, .drop, .drop, cC, .end_, .end_]),
    ("br_table", 1, #[], #[cB, .drop, vblock, .i32Const 7, cA, .localGet 0, .brTable #[0] 0, .end_, .end_]),
    ("return", 1, #[], #[.i32Const 7, cA, .return_, .end_]),
    ("id2", 2, #[], #[.localGet 1, .end_]),
    ("tail", 1, #[], #[.i32Const 1, .i32Const 2, cA, .returnCall 4, .end_]),
    ("local", 0, #[.v128], #[.localGet 0, .end_]),
    ("local_after", 0, #[], #[cB, .drop, .call 6, .end_]),
    ("select", 1, #[], #[cA, cB, .localGet 0, .select none, .end_]),
    ("global", 4, #[], #[.globalGet 0, .localGet 0, .globalSet 0, .end_]),
    ("catch", 0, #[], #[cB, .drop, .try_ (.val .v128), .throw 0, .catch_ 0, cA, .end_, .end_]),
    ("br_on_null", 0, #[], #[cB, .drop, vblock, .i32Const 7, cA, .refNull .func, .brOnNull 0,
      .drop, .drop, .drop, cC, .end_, .end_]),
    ("tee", 0, #[.v128], #[cA, .localTee 0, .drop, .localGet 0, .end_]),
    ("pair", 5, #[], #[.localGet 0, cA, .end_])]

def module : Module :=
  { types := #[⟨#[], #[.v128]⟩, ⟨#[.i32], #[.v128]⟩, ⟨#[.i32, .v128], #[.v128]⟩, ⟨#[], #[]⟩,
               ⟨#[.v128], #[.v128]⟩, ⟨#[.i32], #[.i32, .v128]⟩]
    funcs := funcs.map fun (_, t, ls, body) => { type := t, locals := ls, body }
    globals := #[{ type := ⟨true, .v128⟩, init := #[cC, .end_] }]
    tags := #[3]
    exports := funcs.zipIdx.map fun ((n, _), i) => { name := n, desc := .func i } }

def vA : Value := .v128 aLo aHi
def vB : Value := .v128 bLo bHi
def vC : Value := .v128 cLo cHi

/-- (export, arguments, expected values), run in order on one store. -/
def cases : List (String × Array Value × Array Value) :=
  [("br", #[], #[vA]), ("br_if", #[.i32 1], #[vA]), ("br_if", #[.i32 0], #[vC]),
   ("br_table", #[.i32 0], #[vA]), ("return", #[.i32 0], #[vA]), ("tail", #[.i32 0], #[vA]),
   ("local_after", #[], #[.v128 0 0]), ("select", #[.i32 1], #[vA]), ("select", #[.i32 0], #[vB]),
   ("global", #[vA], #[vC]), ("global", #[vB], #[vA]), ("catch", #[], #[vA]),
   ("br_on_null", #[], #[vA]), ("tee", #[], #[vA]), ("pair", #[.i32 9], #[.i32 9, vA])]

/-- `(func (export "loop") (param i32) (local v128 × k) ...)`: the last local is added
to itself (`i8x16.add`) the parameter's number of times. -/
def loopModule (k : Nat) : Module :=
  { types := #[⟨#[.i32], #[]⟩]
    funcs := #[{ type := 0, locals := Array.replicate k .v128,
                 body := #[.loop .empty, .localGet k, .localGet k, .simd 0x6e ⟨0, 0, 0⟩ 0 0 0, .localSet k,
                           .localGet 0, .i32Const 1, .num .i32_sub, .localTee 0, .brIf 0, .end_, .end_] }]
    exports := #[{ name := "loop", desc := .func 0 }] }

/-- Time of `n` iterations with `k` v128 locals, in nanoseconds; none when the run failed. -/
def timeLoop (k n : Nat) : IO (Option Nat) := do
  let .ok vm := validate (loopModule k) | return none
  let (st, r) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | return none
  let some (.func fa) := st.export? ia "loop" | return none
  let t0 ← IO.monoNanosNow
  let (_, o) ← IO.lazyPure fun _ => invoke st fa #[.i32 (UInt32.ofNat n)]
  let t1 ← IO.monoNanosNow
  match o with
  | .values _ => return some (t1 - t0)
  | _ => return none

def noCopy : IO Bool := do
  let n := 20000
  let some small ← timeLoop 2 n | IO.println "simd hi stack no-copy: FAIL (setup)"; return false
  let some big ← timeLoop 40000 n | IO.println "simd hi stack no-copy: FAIL (setup)"; return false
  let ok := big ≤ 4 * small + 200000000
  IO.println s!"simd hi stack no-copy: {n} iterations, local at slot 2 {small / 1000000} ms, at slot 40000 {big / 1000000} ms: {if ok then "pass" else "FAIL"}"
  return ok

def moves : IO Bool := do
  let vm ← match validate module with
    | .ok vm => pure vm
    | .error e => IO.println s!"simd moves: FAIL (validate: {e.toString})"; return false
  let (st, r) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | IO.println "simd moves: FAIL (instantiate)"; return false
  let mut st := st
  let mut ok := true
  for (name, args, want) in cases do
    match st.export? ia name with
    | some (.func fa) =>
      let (st', o) := invoke st fa args
      st := st'
      match o with
      | .values vs =>
        if vs != want then
          IO.println s!"  simd {name}: got {repr vs}, expected {repr want}"
          ok := false
      | o => IO.println s!"  simd {name}: {o.describe}"; ok := false
    | _ => IO.println s!"  simd {name}: no export"; ok := false
  IO.println s!"simd moves: {cases.length} cases: {if ok then "pass" else "FAIL"}"
  return ok

/-- The three parts of SIMD that the engine refuses
(https://github.com/danbri/factoidal-core/issues/385): relaxed SIMD, a tag type with a v128,
a host function type with a v128. Each check expects the refusal with its text. When a part
is implemented its check fails here: change the check and the issue together. -/
def refusals : IO Bool := do
  -- a module whose one function body is `i8x16.relaxed_swizzle` (0xFD 0x100)
  let bin : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x04, 0x01, 0x60, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
    0x0a, 0x07, 0x01, 0x05, 0x00, 0xfd, 0x80, 0x02, 0x0b]⟩
  let relaxed := match decode bin with
    | .error e => e.toString == "unsupported: relaxed SIMD instruction at byte 23"
    | .ok _ => false
  let tagM : Module := { types := #[⟨#[.v128], #[]⟩], tags := #[0] }
  let tag := match validate tagM with
    | .error e => e.msg == "unsupported: v128 in a tag type"
    | .ok _ => false
  let hostM : Module := { types := #[⟨#[.v128], #[]⟩], imports := #[⟨"env", "f", .func 0⟩] }
  let hostText := match validate hostM with
    | .error e => "validate: " ++ e.msg
    | .ok vm =>
      let (st, fa) := ({} : Store).addHostFunc ⟨#[.v128], #[]⟩ 0
      match (instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) st vm #[.func fa]).2 with
      | .error e => e.toString
      | .ok _ => "instantiated"
  let host := (hostText.splitOn "unsupported: v128 in the type of a host function").length == 2
  if !host then IO.println s!"  simd refusals: host function: {hostText}"
  let ok := relaxed && tag && host
  IO.println s!"simd refusals (issue 385): relaxed SIMD {relaxed}, v128 in a tag type {tag}, v128 in a host function type {host}: {if ok then "pass" else "FAIL"}"
  return ok

def run : IO Bool := do
  let a ← moves
  let b ← noCopy
  let c ← refusals
  return a && b && c

end L4Factoidal.WasmVM.Tests.Simd
