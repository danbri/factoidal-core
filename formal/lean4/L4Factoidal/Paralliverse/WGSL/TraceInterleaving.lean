import L4Factoidal.GpuKernel.TraceInterleavingTheorems
import L4Factoidal.Paralliverse.WGSL.Pipeline

/-! # Individual stores recorded by the concrete scatter shader

The parsed grid returns a chronological log per invocation. Every recorded
scatter store has group 0 and binding 2. Its payload address and value suffice
to observe any prefix of the stores on the destination word memory.
-/

namespace L4Factoidal.Paralliverse.WGSL
open L4Factoidal.GpuKernel

/-- The address and value of every actual store, in the order recorded by the grid. -/
def scatterPayloadWrites (trace : List TextPipeline.LaneTrace) : List (Nat × UInt32) :=
  (trace.map (fun lane => lane.stores.map Prod.snd)).flatten

/-- All logged stores name the payload binding. Each visited address agrees with
its event and the final finite memory. Every unvisited address retains its
original word. A complete permutation has the final memory at every address. -/
def ScatterStoreObservations (initial final : Mem UInt32) (trace : List TextPipeline.LaneTrace) : Prop :=
  let issued := scatterPayloadWrites trace
  (∀ lane ∈ trace, ∀ event ∈ lane.stores, event.1 = (0, 2)) ∧ (keys issued).Nodup ∧
    ∀ (seen pending : List (Nat × UInt32)), (seen ++ pending).Perm issued →
      (∀ event ∈ seen, applyWrites initial seen event.1 = event.2 ∧ final event.1 = event.2) ∧
      (∀ i, i ∉ keys seen → applyWrites initial seen i = initial i) ∧
      applyWrites initial (seen ++ pending) = final

/-- Kind: trace observation.
Says: projecting the certified per-lane footprints removes padded lanes and keeps
the value and address of each individual active-row store in chronological order.
Does not say: how a host obtains the recorded grid. -/
private theorem footprint_writes (rows : StaticPack.Rows) (offsets : Array UInt32) (lanes : List UInt32) :
    scatterPayloadWrites (lanes.map (TextPipeline.scatterFootprint rows offsets)) =
      ((CountTarget.activeOrder rows.length lanes).map
        (DSL.scatterDispatch rows (CountTarget.memory offsets)).writes).flatten := by
  induction lanes with
  | nil => rfl
  | cons gid rest ih =>
    change ((TextPipeline.scatterFootprint rows offsets gid).stores.map Prod.snd) ++
      scatterPayloadWrites (rest.map (TextPipeline.scatterFootprint rows offsets)) = _
    have project : (TextPipeline.scatterFootprint rows offsets gid).stores.map Prod.snd = rowWrites rows offsets gid := by
      simp [TextPipeline.scatterFootprint, List.map_map, payloadEvent, Function.comp_def]
    rw [project, ih]
    by_cases active : gid.toNat < rows.length
    · have ids : CountTarget.activeOrder rows.length (gid :: rest) =
          gid.toNat :: CountTarget.activeOrder rows.length rest := by simp [CountTarget.activeOrder, active]
      rw [ids, List.map_cons, List.flatten_cons, rowWrites, if_pos active]
    · have ids : CountTarget.activeOrder rows.length (gid :: rest) =
          CountTarget.activeOrder rows.length rest := by simp [CountTarget.activeOrder, active]
      rw [ids, rowWrites, if_neg active, List.nil_append]

/-- Kind: scatter footprint invariant.
Says: a complete row permutation with scanned starts writes each output address
at most once, both within each row and across distinct rows.
Does not say: separate empty rows have distinct starts. -/
private theorem active_writes_nodup (rows : StaticPack.Rows) (offsets : Array UInt32) (ids : List Nat)
    (order : ids.Perm (List.range rows.length))
    (starts : DSL.view rows.length (CountTarget.memory offsets) = StaticPack.scanFrom 0 (StaticPack.counts rows)) :
    (keys (ids.map (DSL.scatterDispatch rows (CountTarget.memory offsets)).writes).flatten).Nodup := by
  apply keys_flatten_nodup
  · intro lane member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    let row := rows.getD i []
    let base := CountTarget.memory offsets i
    change (keys (DSL.writesFrom base row)).Nodup
    have addresses : keys (DSL.writesFrom base row) = List.range' base row.length := List.map_fst_zip (by simp)
    rw [addresses]
    exact List.nodup_range'
  · rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (order.nodup_iff.mpr List.nodup_range)
    intro i j hi hj different
    exact DSL.scatter_raceFree rows _ starts i j (List.mem_range.mp (order.mem_iff.mp hi))
      (List.mem_range.mp (order.mem_iff.mp hj)) different

/-- Kind: store replay.
Says: replaying flattened writes visits exactly the same stores as the lane fold.
Does not say: arbitrary permutations of those writes have that effect. -/
private theorem replay_rows {α : Type} (d : Dispatch α) (ids : List Nat) (initial : Mem α) :
    applyWrites initial (ids.map d.writes).flatten = d.runOrder initial ids := by
  induction ids generalizing initial with
  | nil => rfl
  | cons i rest ih =>
    change applyWrites initial (d.writes i ++ (rest.map d.writes).flatten) =
      d.runOrder (applyWrites initial (d.writes i)) rest
    calc
      _ = applyWrites (applyWrites initial (d.writes i)) (rest.map d.writes).flatten := by
        simp only [applyWrites, List.foldl_append]
      _ = _ := ih (applyWrites initial (d.writes i))

/-- Kind: concrete shader store-interleaving refinement.
Says: the parsed scatter grid succeeds on an accepted packet and visible finite
scan. Each prefix of any permutation of its actual stores has the stated visited
and untouched words. Every complete permutation reproduces its entire finite output.
Does not say: a device schedule finishes or exposes any particular intermediate state. -/
theorem decoded_scatter_text_store_interleavings {src : ByteArray} {rows : StaticPack.Rows}
    (accepted : PackWire.decode src = .ok rows) (offsets prior : Array UInt32) (lanes : List UInt32)
    (offsetRoom : rows.length + 1 ≤ offsets.size)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) = (StaticPack.counts rows).scanl (· + ·) 0)
    (room : (StaticPack.counts rows).sum ≤ prior.size) (order : CountTarget.ValidGrid rows.length lanes) :
    ∃ out, TextPipeline.scatterGrid scatterText.toUTF8 (PackWire.wordView src) offsets prior lanes = some out ∧
      out.dst.size = prior.size ∧
      ScatterStoreObservations (ScatterTarget.wordMemory prior) (ScatterTarget.wordMemory out.dst) out.trace := by
  obtain ⟨out, ran, instruction, size, trace⟩ :=
    TextPipeline.decoded_scatter_text_grid accepted offsets prior lanes offsetRoom scanned room order
  obtain ⟨dst, ranTarget, _, memory⟩ :=
    ScatterTarget.decoded_scatter_dispatch accepted offsets prior lanes offsetRoom scanned room
  have same : dst = out.dst := Except.ok.inj (ranTarget.symm.trans instruction)
  rw [same] at memory
  have binding : ∀ lane ∈ out.trace, ∀ event ∈ lane.stores, event.1 = (0, 2) := by
    rw [trace]
    intro lane member event store
    obtain ⟨gid, _, rfl⟩ := List.mem_map.mp member
    change event ∈ (rowWrites rows offsets gid).map payloadEvent at store
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp store
    rfl
  have issued := (congrArg scatterPayloadWrites trace).trans (footprint_writes rows offsets lanes)
  have unique : (keys (scatterPayloadWrites out.trace)).Nodup := by
    rw [issued]
    exact active_writes_nodup rows offsets _ (CountTarget.activeOrder_perm (PackWire.decode_row_count_le accepted) order)
      (ScatterTarget.scanned_starts rows offsets scanned)
  have replay : applyWrites (ScatterTarget.wordMemory prior) (scatterPayloadWrites out.trace) =
      ScatterTarget.wordMemory out.dst := by
    rw [issued, replay_rows]
    exact memory.symm
  refine ⟨out, ran, size, binding, unique, ?_⟩
  intro seen pending permutation
  obtain ⟨visited, untouched⟩ := applyWrites_perm_prefix (ScatterTarget.wordMemory prior) unique permutation
  rw [replay] at visited
  exact ⟨visited, untouched, (applyWrites_perm_of_nodup_keys _ unique permutation).trans replay⟩

/-- Kind: pipeline trace observation.
Says: a successful execution returns the payload and log of the very scatter grid
that read the returned offsets.
Does not say: that this run succeeds on arbitrary bytes or allocations. -/
private theorem scatter_grid_of_run {src : ByteArray} {prior : PipelineTarget.Buffers}
    {countLanes scatterLanes : List UInt32} {result : TextPipeline.Result}
    (ran : TextPipeline.run src prior countLanes scatterLanes = some result) :
    ∃ out, TextPipeline.scatterGrid scatterText.toUTF8 (PackWire.wordView src) result.offsets prior.words
      scatterLanes = some out ∧ out.dst = result.words ∧ out.trace = result.scatterTrace := by
  simp only [TextPipeline.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ran
  obtain ⟨_, _, _, _, out, scatterRun, _, _, _, _, same⟩ := ran
  subst result
  exact ⟨out, scatterRun, rfl, rfl⟩

/-- Kind: end-to-end concrete shader store-interleaving refinement.
Says: the real store log of the completed three-source program on any accepted
packet and sufficiently large arrays describes every individual-store prefix.
Every complete permutation produces its returned finite payload, including the
unchanged tail beyond the terminal word and the CPU specification prefix.
Does not say: that a compiler, host or device executes the modeled command sequence. -/
theorem decoded_text_pipeline_store_interleavings {src : ByteArray} {rows : StaticPack.Rows}
    (accepted : PackWire.decode src = .ok rows) (prior : PipelineTarget.Buffers) (countLanes scatterLanes : List UInt32)
    (countsCap : rows.length ≤ prior.counts.size) (offsetsCap : rows.length + 1 ≤ prior.offsets.size)
    (wordsCap : (StaticPack.counts rows).sum ≤ prior.words.size)
    (countOrder : CountTarget.ValidGrid rows.length countLanes) (scatterOrder : CountTarget.ValidGrid rows.length scatterLanes) :
    ∃ result, TextPipeline.run src prior countLanes scatterLanes = some result ∧
      result.words.size = prior.words.size ∧ result.offsets[rows.length]? = some result.terminal ∧
      result.terminal.toNat = (StaticPack.counts rows).sum ∧
      result.toPacked.readback.toList = StaticPack.packSpec rows ∧
      (∀ i, result.terminal.toNat ≤ i → result.words[i]? = prior.words[i]?) ∧
      ScatterStoreObservations (ScatterTarget.wordMemory prior.words) (ScatterTarget.wordMemory result.words)
        result.scatterTrace := by
  obtain ⟨result, ran, _, readback, _, offsetSize, size, countMemory, offsetMemory, terminal, total, tail, _⟩ :=
    decoded_text_pipeline accepted prior countLanes scatterLanes countsCap offsetsCap wordsCap countOrder scatterOrder
  have countView : DSL.view rows.length (CountTarget.memory result.counts) = StaticPack.counts rows := by
    rw [countMemory]
    exact DSL.count_visible rows _ (List.range rows.length) (List.Perm.refl _)
  have scanned : DSL.view (rows.length + 1) (CountTarget.memory result.offsets) =
      (StaticPack.counts rows).scanl (· + ·) 0 := by
    rw [offsetMemory]
    exact (DSL.scan_visible rows.length (CountTarget.memory result.counts) (CountTarget.memory prior.offsets)
      [0] (List.Perm.refl _)).trans (congrArg (fun counts : List Nat => counts.scanl (· + ·) 0) countView)
  have room : rows.length + 1 ≤ result.offsets.size := by rw [offsetSize]; exact offsetsCap
  obtain ⟨grid, scatterRun, words, trace⟩ := scatter_grid_of_run ran
  obtain ⟨other, sameRun, _, observations⟩ :=
    decoded_scatter_text_store_interleavings accepted result.offsets prior.words scatterLanes room scanned wordsCap scatterOrder
  have same : other = grid := Option.some.inj (sameRun.symm.trans scatterRun)
  rw [same, words, trace] at observations
  exact ⟨result, ran, size, terminal, total, readback, tail, observations⟩

#print axioms decoded_scatter_text_store_interleavings
#print axioms decoded_text_pipeline_store_interleavings

end L4Factoidal.Paralliverse.WGSL
