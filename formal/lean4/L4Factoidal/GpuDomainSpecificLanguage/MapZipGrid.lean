import L4Factoidal.GpuDomainSpecificLanguage.MapZipRefinement
import L4Factoidal.GpuDomainSpecificLanguage.MapZipPlan
import L4Factoidal.GpuKernel.Race

/-! Physical 64-lane dispatch, finite output arrays and write disjointness for
the parsed map/zip shader. Issue https://github.com/danbri/factoidal-core/issues/802.
The host launches (groups,1,1); the parsed workgroup dimensions are (64,1,1).
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipGrid

open L4Factoidal.Paralliverse.WGSL
open MapZipKind MapZipRefinement

def grid (words : Nat) : Nat := MapZipPlan.groups words * 64

/-- Kind: launch bounds.
Says: the exact emitted geometry covers every logical word, includes one group
for zero words, and has at most 65,535 groups without a u32 invocation-ID wrap.
Does not say: a host submitted those groups. -/
theorem grid_bounds (words : Nat) (small : words ≤ 4194240) :
    words ≤ grid words ∧ 64 ≤ grid words ∧ grid words ≤ 4194240 ∧
    MapZipPlan.groups words ≤ 65535 ∧ grid words < UInt32.size := by
  unfold grid MapZipPlan.groups
  change words ≤ max 1 ((words + 63) / 64) * 64 ∧
    64 ≤ max 1 ((words + 63) / 64) * 64 ∧
    max 1 ((words + 63) / 64) * 64 ≤ 4194240 ∧
    max 1 ((words + 63) / 64) ≤ 65535 ∧
    max 1 ((words + 63) / 64) * 64 < 4294967296
  omega

/-- Kind: invocation representation.
Says: every physical invocation's conversion to the shader's u32 ID is exact.
Does not say: addresses outside this bounded launch are meaningful. -/
theorem gid_exact (words i : Nat) (small : words ≤ 4194240) (physical : i < grid words) :
    (UInt32.ofNat i).toNat = i := by
  apply UInt32.toNat_ofNat_of_lt'
  exact Nat.lt_trans physical (grid_bounds words small).2.2.2.2

/-- Kind: physical lane coverage.
Says: each logical index has a workgroup/local-ID decomposition in the emitted
launch; the empty graph still launches one group but has no such active index.
Does not say: the GPU completed that invocation. -/
theorem active_lane (words i : Nat) (small : words ≤ 4194240) (active : i < words) :
    i / 64 < MapZipPlan.groups words ∧ i % 64 < 64 ∧
    i / 64 * 64 + i % 64 = i := by
  have cover := (grid_bounds words small).1
  unfold grid at cover
  omega

/-- Kind: unique invocation addresses.
Says: different (workgroup,local-ID) pairs produce different word indices.
Does not say: separate output allocations alias no input allocation. -/
theorem lane_address_injective (g h x y : Nat) (hx : x < 64) (hy : y < 64)
    (same : g * 64 + x = h * 64 + y) : g = h ∧ x = y := by
  omega

def foldLanes (result : List UInt32) (prior : Array UInt32) (lanes : List UInt32) :
    Array UInt32 :=
  lanes.foldl (fun dst gid => (laneEffect result dst gid).dst) prior

private theorem lane_size (result : List UInt32) (prior : Array UInt32) (gid : UInt32) :
    (laneEffect result prior gid).dst.size = prior.size := by
  unfold laneEffect
  split <;> simp

private theorem partial_cells (result : List UInt32) (lanes : List UInt32)
    (prior : Array UInt32) (room : result.length ≤ prior.size) :
    (∀ (i : Nat) (h : i < result.length), i ∈ lanes.map UInt32.toNat →
      (foldLanes result prior lanes)[i]? = some result[i]) ∧
    (∀ j : Nat, (∀ g ∈ lanes, g.toNat < result.length → g.toNat ≠ j) →
      (foldLanes result prior lanes)[j]? = prior[j]?) := by
  induction lanes generalizing prior with
  | nil =>
    constructor
    · intro i _ member; cases member
    · intro _ _; rfl
  | cons gid rest ih =>
    let next := (laneEffect result prior gid).dst
    have nextRoom : result.length ≤ next.size := by
      change result.length ≤ (laneEffect result prior gid).dst.size
      rw [lane_size]
      exact room
    obtain ⟨seen,untouched⟩ := ih next nextRoom
    constructor
    · intro i active member
      change (foldLanes result next rest)[i]? = _
      by_cases later : i ∈ rest.map UInt32.toNat
      · exact seen i active later
      · have same : i = gid.toNat := (List.mem_cons.mp member).resolve_right later
        subst i
        have skip : ∀ g ∈ rest, g.toNat < result.length → g.toNat ≠ gid.toNat := by
          intro g gm _ equal
          exact later (List.mem_map.mpr ⟨g,gm,equal⟩)
        rw [untouched _ skip]
        change (laneEffect result prior gid).dst[gid.toNat]? = _
        rw [laneEffect,dif_pos active]
        exact Array.getElem?_setIfInBounds_self_of_lt (by omega)
    · intro j keep
      change (foldLanes result next rest)[j]? = _
      rw [untouched j (fun g gm => keep g (List.mem_cons_of_mem gid gm))]
      change (laneEffect result prior gid).dst[j]? = _
      by_cases active : gid.toNat < result.length
      · rw [laneEffect,dif_pos active]
        exact Array.getElem?_setIfInBounds_ne (keep gid List.mem_cons_self active)
      · rw [laneEffect,dif_neg active]

/-- Kind: finite-array frame.
Says: covering every logical lane yields the whole reference result and preserves
any spare physical tail, including the one-word allocation for an empty result.
Does not say: the lane list is a valid launch or contains no duplicate invocation. -/
theorem fold_frame (result : List UInt32) (prior : Array UInt32) (lanes : List UInt32)
    (room : result.length ≤ prior.size)
    (cover : ∀ i : Nat, i < result.length → i ∈ lanes.map UInt32.toNat) :
    (foldLanes result prior lanes).toList = result ++ prior.toList.drop result.length := by
  obtain ⟨seen,untouched⟩ := partial_cells result lanes prior room
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList]
  by_cases active : j < result.length
  · rw [List.getElem?_append_left active,List.getElem?_eq_getElem active]
    exact seen j active (cover j active)
  · rw [List.getElem?_append_right (by omega),List.getElem?_drop,
      show result.length + (j - result.length) = j by omega,Array.getElem?_toList]
    exact untouched j (fun g _ valid => by omega)

/-- Parse the actual module once, then execute its actual stores in the supplied
    physical-lane order on the changing finite output allocation. -/
def runText (source : String) (inputs : MapZipSurface.Inputs)
    (prior : Array UInt32) (lanes : List UInt32) : Option (Array UInt32) := do
  let m ← MapZipSurface.parseShader source.toUTF8
  lanes.foldlM (fun dst gid => (MapZipSurface.run m inputs dst gid).map Surface.Outcome.dst) prior

private theorem simulate (kind : Kind) (xs ys : Array UInt32) (k : UInt32)
    (small : xs.size ≤ 4194240) (lengths : xs.size = ys.size)
    (lanes : List UInt32) (prior : Array UInt32) (room : xs.size ≤ prior.size) :
    lanes.foldlM (fun dst gid => (MapZipSurface.run shaderModule
      (inputs kind xs ys (UInt32.ofNat xs.size) k) dst gid).map Surface.Outcome.dst) prior =
      some (foldLanes (kind.result xs.toList ys.toList k) prior lanes) := by
  induction lanes generalizing prior with
  | nil => rfl
  | cons gid rest ih =>
    have lane := run_source_lane kind xs ys k small lengths prior room gid
    unfold MapZipSurface.runText at lane
    rw [parse_source] at lane
    dsimp only [Bind.bind,Option.bind] at lane
    rw [List.foldlM_cons,lane]
    dsimp only [Functor.map,Option.map,Bind.bind,Option.bind]
    apply ih
    rw [lane_size]
    exact room

/-- Kind: exact byte-to-grid refinement.
Says: every permutation of the actual rounded launch produces the complete
GraphWords buffer, preserving spare allocation words; padded invocations write
nothing. This includes zero, partial groups and wrapping arithmetic.
Does not say: the driver/hardware executed this semantics or buffers were uploaded
without change. Those host/device correspondences remain external assumptions. -/
theorem run_source_grid (kind : Kind) (xs ys : Array UInt32) (k : UInt32)
    (small : xs.size ≤ 4194240) (lengths : xs.size = ys.size)
    (prior : Array UInt32) (room : xs.size ≤ prior.size) (lanes : List UInt32)
    (order : (lanes.map UInt32.toNat).Perm (List.range (grid xs.size))) :
    ∃ out, runText MapZipShader.source (inputs kind xs ys (UInt32.ofNat xs.size) k)
      prior lanes = some out ∧
      out.toList = kind.result xs.toList ys.toList k ++ prior.toList.drop xs.size := by
  let result := kind.result xs.toList ys.toList k
  have resultLength : result.length = xs.size := by
    simpa [result] using result_length kind xs.toList ys.toList k (by simpa using lengths)
  refine ⟨foldLanes result prior lanes,?_,?_⟩
  · unfold runText
    rw [parse_source]
    dsimp only [Bind.bind,Option.bind]
    exact simulate kind xs ys k small lengths lanes prior room
  · rw [fold_frame result prior lanes (by omega)]
    · rw [resultLength]
    · intro i active
      apply order.mem_iff.mpr
      apply List.mem_range.mpr
      have := (grid_bounds xs.size small).1
      omega

/-- Kind: store footprint.
Says: an active parsed invocation logs exactly one in-range write; a padded
invocation logs no write. Distinct invocation IDs cannot share a store address.
Does not say: different storage bindings refer to disjoint physical memory. -/
theorem lane_store_bounds (result : List UInt32) (prior : Array UInt32) (gid : UInt32)
    (write : Surface.Write) (member : write ∈ (laneEffect result prior gid).writes) :
    write.group = 0 ∧ write.slot = 2 ∧ write.address = gid ∧
    write.address.toNat < result.length := by
  unfold laneEffect at member
  split at member
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst write
    exact ⟨rfl,rfl,rfl,by assumption⟩
  · cases member

#print axioms grid_bounds
#print axioms gid_exact
#print axioms active_lane
#print axioms lane_address_injective
#print axioms fold_frame
#print axioms run_source_grid
#print axioms lane_store_bounds

end L4Factoidal.GpuDomainSpecificLanguage.MapZipGrid
