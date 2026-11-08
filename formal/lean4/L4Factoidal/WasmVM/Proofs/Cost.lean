/-
L4Factoidal.WasmVM.Proofs.Cost: the instruction-count cost model of the loop, a ratchet
for faster designs (https://github.com/danbri/factoidal/issues/1292; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Cost model and ratchet").

The fuel of `run` is the cost semantics: one unit per Wasm instruction of the unfused
code. A fused op stands for several instructions and is one dispatch of the loop (one
`switch` case in the emitted C).

- `cost`: the instructions an op stands for (its parts for a fused op, else 1).
- `fused_charges_parts`: at a pc where `fuse` put a fused op, `run` on the fused code
  with `cost f + n` fuel and `run` on the original code (its parts, one dispatch each)
  reach the same registers with the same `n` left. So fusion never changes the
  instruction count a run reports (the benchmark ratchet checks the counts exactly).
  On the fused code the step over the whole op is ONE dispatch: the proof of that half
  (`run_fused`, `run_fusedJump`) unfolds `run` once, the case of the fused op alone.
  With `cost f` instructions per dispatch, a run of fused code makes at most as many
  dispatches as it charges fuel, and `cost f - 1` fewer for each fused op it runs.
-/
import L4Factoidal.WasmVM.Proofs.Fuse

namespace L4Factoidal.WasmVM.Proofs.Cost
open L4Factoidal.WasmVM Run Fuse

/-- The instruction-count cost of an op: the Wasm instructions it stands for. -/
def cost (o : Op) : Nat := max 1 o.parts.length

theorem cost_pos (o : Op) : 1 ≤ cost o := Nat.le_max_left _ _

theorem cost_fused (f : Op) (h : f.parts ≠ []) : cost f = f.parts.length := by
  unfold cost
  cases hp : f.parts with
  | nil => exact absurd hp h
  | cons _ _ => simp

/-- Every op that `fuse` makes has parts. -/
theorem fuseAt_parts (c : Array Op) (i : Nat) (f : Op) (h : fuseAt c i = some f) : f.parts ≠ [] := by
  obtain ⟨-, ⟨hs, -⟩, hf⟩ := fuseAt_sound c i f h
  intro hp
  rw [hp] at hs
  simp only [List.take_nil, List.map_nil] at hs
  exact hf (List.map_eq_nil_iff.mp hs.symm)

variable {M : Type} [LinearMemory M]

/-- A fused op charges the fuel of its parts, in one dispatch (see the module doc):
with `cost f + n` fuel, `run` on the fused code (one case of the loop) and `run` on the
original code (one case per part) reach the same registers `r` with `n` left. -/
theorem fused_charges_parts (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (c : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (f : Op)
    (hsz : c.size < USize.size) (hpc : pc < (fuse c).usize)
    (hc : (fuse c)[pc.toNat]'(pc_ok hpc) = f) (hfa : fuseAt c pc.toNat = some f) :
    let r := after fp pc f ⟨stack, sp⟩
    run lim st stack sp fp pc (fuse c) inst frames (n + cost f) =
      run lim st r.1 r.2.1 fp r.2.2 (fuse c) inst frames n ∧
    run lim st stack sp fp pc c inst frames (n + cost f) =
      run lim st r.1 r.2.1 fp r.2.2 c inst frames n := by
  rw [cost_fused f (fuseAt_parts c pc.toNat f hfa)]
  exact fuse_agrees lim st stack sp fp pc c inst frames n f hsz hpc hc hfa

end L4Factoidal.WasmVM.Proofs.Cost
