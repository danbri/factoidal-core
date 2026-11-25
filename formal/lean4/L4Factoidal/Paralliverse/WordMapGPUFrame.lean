import L4Factoidal.Paralliverse.WordMapGPUSurface

/-! Finite word-array preservation for arbitrary orders of the shader's lane effects. -/

namespace L4Factoidal.Paralliverse.WordMapGPU

/-- Expected destination after visiting the supplied physical IDs in their given order. -/
def foldLanes (pass : Pass) (xs : List UInt32) (prior : Array UInt32) (lanes : List UInt32) :
    Array UInt32 :=
  lanes.foldl (fun dst gid => (laneEffect pass xs dst gid).dst) prior

/-- Kind: storage size.
Says: one invocation's finite destination has the same size as its input destination.
Does not say: that a host provided enough room for every logical word. -/
theorem lane_size (pass : Pass) (xs : List UInt32) (prior : Array UInt32) (gid : UInt32) :
    (laneEffect pass xs prior gid).dst.size = prior.size := by
  unfold laneEffect
  split <;> simp

private theorem partial_cells (pass : Pass) (xs : List UInt32) (lanes : List UInt32)
    (prior : Array UInt32) (room : 2 + xs.length ≤ prior.size) :
    (∀ (i : Nat) (h : i < xs.length), i ∈ lanes.map UInt32.toNat →
      (foldLanes pass xs prior lanes)[2 + i]? = some (pass.apply xs[i])) ∧
    (∀ j : Nat, (∀ g ∈ lanes, g.toNat < xs.length → 2 + g.toNat ≠ j) →
      (foldLanes pass xs prior lanes)[j]? = prior[j]?) := by
  induction lanes generalizing prior with
  | nil =>
    constructor
    · intro i _ member; cases member
    · intro _ _; rfl
  | cons gid rest ih =>
    let next := (laneEffect pass xs prior gid).dst
    have nextRoom : 2 + xs.length ≤ next.size := by
      change 2 + xs.length ≤ (laneEffect pass xs prior gid).dst.size
      rw [lane_size]
      exact room
    obtain ⟨seen, untouched⟩ := ih next nextRoom
    constructor
    · intro i active member
      change (foldLanes pass xs next rest)[2 + i]? = _
      by_cases later : i ∈ rest.map UInt32.toNat
      · exact seen i active later
      · have same : i = gid.toNat := (List.mem_cons.mp member).resolve_right later
        subst i
        have skip : ∀ g ∈ rest, g.toNat < xs.length → 2 + g.toNat ≠ 2 + gid.toNat := by
          intro g gm _ equal
          exact later (List.mem_map.mpr ⟨g, gm, by omega⟩)
        rw [untouched _ skip]
        change (laneEffect pass xs prior gid).dst[2 + gid.toNat]? = _
        rw [laneEffect, dif_pos active]
        exact Array.getElem?_setIfInBounds_self_of_lt (by omega)
    · intro j keep
      change (foldLanes pass xs next rest)[j]? = _
      rw [untouched j (fun g gm => keep g (List.mem_cons_of_mem gid gm))]
      change (laneEffect pass xs prior gid).dst[j]? = _
      by_cases active : gid.toNat < xs.length
      · rw [laneEffect, dif_pos active]
        exact Array.getElem?_setIfInBounds_ne (keep gid (List.mem_cons_self) active)
      · rw [laneEffect, dif_neg active]

/-- Kind: whole-buffer frame.
Says: covering every logical index replaces exactly the payload slice by the
mapped values, even with arbitrary lane order, padded lanes or repeated visits.
Does not say: a supplied schedule is a valid physical launch or issued each store once. -/
theorem foldLanes_frame (pass : Pass) (xs : List UInt32) (prior : Array UInt32) (lanes : List UInt32)
    (room : 2 + xs.length ≤ prior.size)
    (cover : ∀ i : Nat, i < xs.length → i ∈ lanes.map UInt32.toNat) :
    (foldLanes pass xs prior lanes).toList =
      prior.toList.take 2 ++ xs.map pass.apply ++ prior.toList.drop (2 + xs.length) := by
  obtain ⟨seen, untouched⟩ := partial_cells pass xs lanes prior room
  have header : (prior.toList.take 2).length = 2 := by
    apply List.length_take_of_le
    rw [Array.length_toList]
    omega
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList, List.append_assoc]
  by_cases first : j < 2
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt first, Array.getElem?_toList]
    exact untouched j (fun g _ _ => by omega)
  · rw [List.getElem?_append_right (by omega), header]
    by_cases middle : j - 2 < xs.length
    · rw [List.getElem?_append_left (by simpa only [List.length_map] using middle),
        List.getElem?_map, List.getElem?_eq_getElem middle]
      have hit := seen (j - 2) middle (cover _ middle)
      rw [show 2 + (j - 2) = j by omega] at hit
      exact hit
    · have beyond : (xs.map pass.apply).length ≤ j - 2 := by rw [List.length_map]; omega
      rw [List.getElem?_append_right beyond, List.length_map, List.getElem?_drop,
        show 2 + xs.length + (j - 2 - xs.length) = j by omega, Array.getElem?_toList]
      exact untouched j (fun g _ active => by omega)

#print axioms lane_size
#print axioms foldLanes_frame

end L4Factoidal.Paralliverse.WordMapGPU

