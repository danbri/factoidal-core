/-
L4Factoidal.GpuKernel.Gather — the first compute kernel shape of core issue 398, and tile
binning written in it.

A gather kernel has one invocation per output cell `t < cells`. Invocation `t` walks the
items `k < items` in order and lists those for which the kernel's condition holds, keeping
the first `cap`, then writes how many there were (more than `cap` means the list was cut;
the host then knows to take another route). Output layout, `u32` words:

  count of cell t   at  t
  slot j of cell t  at  cells + t * cap + j        (j < min cap count)

Uniform parameters: `params.x` = cells, `params.y` = items; `params.z`, `params.w` are free for
the condition. `cap` and `maxItems` (the loop's cap) are literals of the kernel.

Proved here, for every gather kernel:
- `raceFree`: different invocations write different words, so by `Race.runOrder_perm` every
  order in which the GPU runs them gives the memory of the sequential loop `runSeq`;
- `writes_lt`: every word written is below `cells * (cap + 1)`, the size of the output
  buffer the host makes;
- `items_le`: the loop runs at most `maxItems` times.
And for tile binning (`bin`):
- `bin_hits`: what the kernel lists for tile `t` is `binSpec`, the boxes that meet the tile,
  defined from geometry with no reference to the IR;
- `binPred_fits` and `bin_eval32`: within the limits (tile size ≤ 1024, cells ≤ 2^20, tiles
  across ≤ 2^16, maxItems ≤ 65536) no `u32` operation of the condition wraps, so the GPU's
  arithmetic computes the Lean meaning;
- `binPred_loads_lt`: every input word the condition reads is below `4 * items`.
-/
import L4Factoidal.GpuKernel.Race
import L4Factoidal.GpuKernel.Expr

namespace L4Factoidal.GpuKernel

structure Gather where
  cap : Nat
  maxItems : Nat
  pred : P

namespace Gather

def items (g : Gather) (params : Fin 4 → Nat) : Nat := min (params 1) g.maxItems

def envAt (params : Fin 4 → Nat) (input : Nat → Nat) (t k : Nat) : Env :=
  { inv := t, k := k, params := params, input := input }

/-- The items cell `t` lists, in order, before the cut at `cap`. -/
def hits (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) (t : Nat) : List Nat :=
  (List.range (g.items params)).filter fun k => g.pred.eval (envAt params input t k)

/-- The writes of invocation `t`, in program order: the kept slots, then the count. -/
def writes (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) (t : Nat) : List (Nat × Nat) :=
  let hs := g.hits params input t
  (List.range (min g.cap hs.length)).map (fun j => (params 0 + t * g.cap + j, hs.getD j 0)) ++ [(t, hs.length)]

/-- The dispatch: `params.x` invocations. -/
def dispatch (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) : Dispatch Nat :=
  { n := params 0, writes := g.writes params input }

theorem items_le (g : Gather) (params : Fin 4 → Nat) : g.items params ≤ g.maxItems :=
  Nat.min_le_right _ _

theorem mem_keys_writes (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) (t i : Nat)
    (h : i ∈ keys (g.writes params input t)) :
    i = t ∨ ∃ j, j < g.cap ∧ i = params 0 + t * g.cap + j := by
  simp only [keys, writes, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_range, Function.comp_def, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨j, hj, rfl⟩ | rfl
  · exact Or.inr ⟨j, Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _), rfl⟩
  · exact Or.inl rfl

theorem slot_inj {c t u j j' : Nat} (hj : j < c) (hj' : j' < c)
    (h : t * c + j = u * c + j') : t = u := by
  have hc : 0 < c := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have e1 : (t * c + j) / c = t := by
    rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hj, Nat.add_zero]
  have e2 : (u * c + j') / c = u := by
    rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hj', Nat.add_zero]
  rw [← e1, ← e2, h]

/-- Different invocations write different words. -/
theorem raceFree (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) :
    (g.dispatch params input).RaceFree := by
  intro t u ht hu hne i hi hi'
  simp only [dispatch] at ht hu
  rcases g.mem_keys_writes params input t i hi with rfl | ⟨j, hj, rfl⟩ <;>
    rcases g.mem_keys_writes params input u _ hi' with e | ⟨j', hj', e⟩
  · exact hne e
  · omega
  · omega
  · exact hne (slot_inj hj hj' (by omega))

/-- Every order of the invocations gives the sequential loop's memory. -/
theorem gpu_eq_seq (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat)
    (order : List Nat) (hp : order.Perm (List.range (params 0))) (m : Mem Nat) :
    (g.dispatch params input).runOrder m order = (g.dispatch params input).runSeq m :=
  Dispatch.runOrder_perm _ (g.raceFree params input) order hp m

/-- Every word written is inside the output buffer of `cells * (cap + 1)` words. -/
theorem writes_lt (g : Gather) (params : Fin 4 → Nat) (input : Nat → Nat) (t : Nat)
    (ht : t < params 0) : ∀ w ∈ g.writes params input t, w.1 < params 0 * (g.cap + 1) := by
  intro w hw
  have hk : w.1 ∈ keys (g.writes params input t) := List.mem_map_of_mem hw
  have hle : (t + 1) * g.cap ≤ params 0 * g.cap := Nat.mul_le_mul_right _ ht
  rcases g.mem_keys_writes params input t _ hk with e | ⟨j, hj, e⟩
  · rw [e, Nat.mul_succ]; omega
  · rw [e, Nat.mul_succ]; rw [Nat.succ_mul] at hle; omega

/-! ## WGSL text -/

def wgsl (g : Gather) : String :=
  "@group(0) @binding(0) var<storage, read> inp : array<u32>;\n" ++
  "@group(0) @binding(1) var<storage, read_write> outp : array<u32>;\n" ++
  "@group(0) @binding(2) var<uniform> params : vec4<u32>;\n" ++
  "@compute @workgroup_size(64)\n" ++
  "fn main(@builtin(global_invocation_id) gid : vec3<u32>) {\n" ++
  "  let t = gid.x;\n" ++
  "  if (t >= params.x) { return; }\n" ++
  "  let last = arrayLength(&outp) - 1u;\n" ++
  "  var c = 0u;\n" ++
  s!"  for (var k = 0u; k < min(params.y, {g.maxItems}u); k = k + 1u) \{\n" ++
  s!"    if ({g.pred.wgsl}) \{\n" ++
  s!"      if (c < {g.cap}u) \{ outp[min(params.x + t * {g.cap}u + c, last)] = k; }\n" ++
  "      c = c + 1u;\n" ++
  "    }\n" ++
  "  }\n" ++
  "  outp[min(t, last)] = c;\n" ++
  "}\n"

end Gather

/-! ## Tile binning -/

/-- A box `[x0, x1) × [y0, y1)` in pixels. -/
structure Box where
  x0 : Nat
  y0 : Nat
  x1 : Nat
  y1 : Nat

/-- Item `k`'s box: input words `4k .. 4k+3`. -/
def boxOf (input : Nat → Nat) (k : Nat) : Box :=
  ⟨input (4 * k), input (4 * k + 1), input (4 * k + 2), input (4 * k + 3)⟩

/-- Tile `t` of a grid `across` tiles wide, tiles `size` pixels square, meets box `b`. -/
def meets (size across t : Nat) (b : Box) : Bool :=
  let tx := t % max across 1 * size
  let ty := t / max across 1 * size
  decide (b.x0 < tx + size) && decide (tx < b.x1) && decide (b.y0 < ty + size) && decide (ty < b.y1)

/-- The specification: the items `k < n`, in order, whose box meets tile `t`. -/
def binSpec (size across n : Nat) (input : Nat → Nat) (t : Nat) : List Nat :=
  (List.range n).filter fun k => meets size across t (boxOf input k)

def tileX (size : Nat) : E := .mul (.mod .inv (.param 2)) (.lit size)
def tileY (size : Nat) : E := .mul (.div .inv (.param 2)) (.lit size)
def boxAt (c : Nat) : E := .load (.add (.mul (.lit 4) .k) (.lit c))

def binPred (size : Nat) : P :=
  .and (.and (.lt (boxAt 0) (.add (tileX size) (.lit size))) (.lt (tileX size) (boxAt 2)))
       (.and (.lt (boxAt 1) (.add (tileY size) (.lit size))) (.lt (tileY size) (boxAt 3)))

/-- Tile binning as a gather kernel. `params.z` is the number of tiles across. -/
def bin (size cap maxItems : Nat) : Gather := { cap := cap, maxItems := maxItems, pred := binPred size }

theorem binPred_eval (size : Nat) (env : Env) :
    (binPred size).eval env = meets size (env.params 2) env.inv (boxOf env.input env.k) := by
  simp [binPred, meets, boxOf, tileX, tileY, boxAt, P.eval, E.eval, Bool.and_assoc, Nat.mul_comm]

/-- The kernel lists, for each tile, exactly the specification's boxes. -/
theorem bin_hits (size cap maxItems : Nat) (params : Fin 4 → Nat) (input : Nat → Nat) (t : Nat) :
    (bin size cap maxItems).hits params input t =
      binSpec size (params 2) (min (params 1) maxItems) input t := by
  simp only [Gather.hits, Gather.items, bin, binSpec, binPred_eval, Gather.envAt]

theorem binPred_fits (size : Nat) (hs : size ≤ 1024) (env : Env)
    (ht : env.inv < 1048576) (hk : env.k < 65536) (hx : env.params 2 < 65536) :
    (binPred size).Fits env := by
  have hmod : env.inv % max (env.params 2) 1 < 65536 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have hdiv : env.inv / max (env.params 2) 1 < 1048576 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht
  have hxm : env.inv % max (env.params 2) 1 * size ≤ 65536 * 1024 :=
    Nat.mul_le_mul (Nat.le_of_lt hmod) hs
  have hym : env.inv / max (env.params 2) 1 * size ≤ 1048576 * 1024 :=
    Nat.mul_le_mul (Nat.le_of_lt hdiv) hs
  simp only [binPred, tileX, tileY, boxAt, P.Fits, E.Fits, E.eval, U32]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem bin_eval32 (size : Nat) (hs : size ≤ 1024) (env : Env) (hin : ∀ i, env.input i < U32)
    (ht : env.inv < 1048576) (hk : env.k < 65536) (hx : env.params 2 < 65536) :
    (binPred size).eval32 env = (binPred size).eval env :=
  P.eval32_eq env hin _ (binPred_fits size hs env ht hk hx)

theorem binPred_loads_lt (size n : Nat) (env : Env) (hk : env.k < n) :
    ∀ e ∈ (binPred size).loads, e.eval env < 4 * n := by
  intro e he
  simp only [binPred, tileX, tileY, boxAt, P.loads, E.loads, List.append_nil, List.nil_append,
    List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp only [E.eval] <;> omega

/-! ## Checks on a small grid (2 tiles across, 16-pixel tiles) -/

private def sampleParams : Fin 4 → Nat := fun i => [2, 3, 2, 0][i]!
private def sampleInput : Nat → Nat := fun i => [0, 0, 20, 20, 17, 17, 18, 18, 40, 0, 41, 1][i]!

#guard (bin 16 4 100).hits sampleParams sampleInput 0 == [0]
#guard (bin 16 4 100).hits sampleParams sampleInput 1 == [0]
#guard binSpec 16 2 3 sampleInput 1 == [0]
#guard (bin 16 4 100).writes sampleParams sampleInput 1 == [(6, 0), (1, 1)]
#guard ((bin 16 4 100).wgsl.splitOn "arrayLength(&inp) - 1u").length == 5
#guard (binPred 16).eval32 ⟨3, 2, sampleParams, sampleInput⟩ == (binPred 16).eval ⟨3, 2, sampleParams, sampleInput⟩

end L4Factoidal.GpuKernel
