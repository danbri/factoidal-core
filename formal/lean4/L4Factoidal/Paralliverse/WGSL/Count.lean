import L4Factoidal.Paralliverse.WGSL.ShaderText
import L4Factoidal.Paralliverse.WGSL.Surface
import L4Factoidal.Paralliverse.CountPacketTheorems

/-! # A static count shader and the meaning of its concrete bytes

The independent surface parser and interpreter execute the static source exported by the Hub. -/

namespace L4Factoidal.Paralliverse.WGSL

def countModule : Surface.Module where
  first := ⟨0, 0, .read, .srcWords⟩
  second := ⟨0, 2, .readWrite, .dstWords⟩
  sizeX := 64
  sizeY := 1
  sizeZ := 1
  body := {
    left := .gidX
    right := .load .srcWords (.literal 1)
    destination := .dstWords
    address := .gidX
    value := .load .srcWords (.add (.literal 4) (.mul (.literal 2) .gidX))
  }

set_option maxRecDepth 8192 in
/-- Kind: concrete syntax.
Says: parsing all bytes of the exported count source yields the stated bindings,
workgroup dimensions, comparison, arithmetic, array reads and store.
Does not say: that a device compiler implements this restricted parser. -/
theorem parse_count_text : Surface.parseShader countText.toUTF8 = some countModule := by
  rfl

/-- Kind: launch arithmetic.
Says: the real shader's parsed workgroup dimensions, combined with the proposed
one-dimensional group count, give exactly the checked CountTarget grid.
Does not say: that the host submitted this number of groups or visited each lane. -/
theorem count_text_launch (n : Nat) :
    (Surface.parseShader countText.toUTF8).map (fun m => (((n + 63) / 64) * m.sizeX, m.sizeY, m.sizeZ)) =
      some (CountTarget.grid n, 1, 1) := by
  rw [parse_count_text] <;> rfl

private def written (prior : Array UInt32) (gid v : UInt32) : Option Surface.Outcome :=
  if h : gid.toNat < prior.size then
    some ⟨prior.set gid.toNat v h, [⟨0, 2, gid, v⟩]⟩
  else none

/-- Kind: one-invocation semantics.
Says: a readable header supplies the count guard. Only the active branch reads
the computed descriptor address and attempts a store to the modeled output.
Does not say: that the descriptor exists or the output has enough space. -/
private theorem surface_header (packet prior : Array UInt32) (gid n : UInt32)
    (header : packet[1]? = some n) :
    Surface.run countModule packet prior gid =
      if gid < n then (packet[(4 + 2 * gid : UInt32).toNat]?).bind (written prior gid)
      else some ⟨prior, []⟩ := by
  change (packet[1]?).bind (fun w =>
    if gid < w then (packet[(4 + 2 * gid : UInt32).toNat]?).bind (written prior gid)
    else some ⟨prior, []⟩) = _
  rw [header] <;> rfl

/-- Kind: target evaluation.
Says: the existing CountTarget instruction tree uses the same header, word
address, and guarded destination in its finite storage model.
Does not say: that the shader returns the target's error code for invalid data. -/
private theorem target_header (packet prior : Array UInt32) (gid n : UInt32)
    (header : packet[1]? = some n) :
    (CountTarget.lowerCount .count).exec packet gid prior =
      if gid < n then
        (CountTarget.loadWord packet (4 + 2 * gid)).bind (fun v => CountTarget.storeWord prior gid v)
      else .ok prior := by
  have head : CountTarget.loadWord packet 1 = .ok n := by
    change (match packet[1]? with
      | some v => Except.ok v
      | none => Except.error (CountTarget.Fault.readPastEnd 1)) = _
    rw [header]
  change (CountTarget.loadWord packet 1).bind (fun w =>
    if gid < w then (CountTarget.loadWord packet (4 + 2 * gid)).bind (fun v => CountTarget.storeWord prior gid v)
    else .ok prior) = _
  rw [head] <;> rfl

/-- Kind: byte-to-instruction refinement.
Says: for every accepted packet, sufficient count array and physical lane ID,
executing the actual parsed count text succeeds with the entire target destination.
An active lane's only store is its row length to its own (0,2) slot; an inactive
lane has an empty store trace.
Does not say: that WebGPU's parser, native compiler, bindings or scheduling
realise this formal byte-to-invocation model. -/
theorem decoded_count_text_lane {src : ByteArray} {rows : StaticPack.Rows}
    (accepted : PackWire.decode src = .ok rows) (prior : Array UInt32)
    (capacity : rows.length ≤ prior.size) (gid : UInt32) :
    ∃ result : Surface.Outcome,
      Surface.runText countText.toUTF8 (PackWire.wordView src) prior gid = some result ∧
      (CountTarget.lowerCount .count).exec (PackWire.wordView src) gid prior = .ok result.dst ∧
      result.dst.size = prior.size ∧
      (if gid.toNat < rows.length then
        ∃ v : UInt32, result.writes = [⟨0, 2, gid, v⟩] ∧ v.toNat = (rows.getD gid.toNat []).length
       else result.writes = []) := by
  let packet := PackWire.wordView src
  have source : CountTarget.SourceRows packet rows := CountTarget.accepted_sourceRows accepted
  obtain ⟨n, head, nVal⟩ := Option.map_eq_some_iff.mp source.header
  have branch : gid < n ↔ gid.toNat < rows.length := by rw [UInt32.lt_iff_toNat_lt, nVal]
  have surface : Surface.runText countText.toUTF8 packet prior gid =
      if gid < n then (packet[(4 + 2 * gid : UInt32).toNat]?).bind (written prior gid)
      else some ⟨prior, []⟩ := by
    unfold Surface.runText
    rw [parse_count_text]
    exact surface_header packet prior gid n head
  have target := target_header packet prior gid n head
  by_cases active : gid.toNat < rows.length
  · obtain ⟨v, descriptor, length⟩ := Option.map_eq_some_iff.mp (source.lengths _ active)
    have physical := CountTarget.descriptor_word_address gid (Nat.lt_of_lt_of_le active source.limit)
    have cell : packet[(4 + 2 * gid : UInt32).toNat]? = some v := by rw [physical, descriptor]
    have loaded : CountTarget.loadWord packet (4 + 2 * gid) = .ok v := by
      unfold CountTarget.loadWord
      rw [cell]
    have room := Nat.lt_of_lt_of_le active capacity
    refine ⟨⟨prior.set gid.toNat v room, [⟨0, 2, gid, v⟩]⟩, ?_, ?_, by simp, ?_⟩
    · rw [surface, if_pos (branch.mpr active), cell]
      change written prior gid v = _
      exact dif_pos room
    · rw [target, if_pos (branch.mpr active), loaded]
      change CountTarget.storeWord prior gid v = _
      exact dif_pos room
    · rw [if_pos active]
      exact ⟨v, rfl, length⟩
  · have inactive : ¬ gid < n := fun h => active (branch.mp h)
    refine ⟨⟨prior, []⟩, ?_, ?_, rfl, ?_⟩
    · rw [surface, if_neg inactive]
    · rw [target, if_neg inactive]
    · rw [if_neg active]

#print axioms parse_count_text
#print axioms count_text_launch
#print axioms surface_header
#print axioms target_header
#print axioms decoded_count_text_lane

end L4Factoidal.Paralliverse.WGSL
