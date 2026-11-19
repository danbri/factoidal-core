import L4Factoidal.Paralliverse.PipelineTarget
import L4Factoidal.Paralliverse.WGSL.Dispatch
import L4Factoidal.Paralliverse.WGSL.Count
import L4Factoidal.Paralliverse.WGSL.Scan
import L4Factoidal.Paralliverse.WGSL.Scatter

/-! # Stable packing from the three concrete shader sources

The executable model independently parses each complete stage. It passes the count
array to one scan invocation, and the resulting offsets to each scatter invocation.
Each lane sees its predecessor's finite destination. Logs preserve both lane order
and the order of the real stores inside a lane, including their bindings and values.
-/

namespace L4Factoidal.Paralliverse.WGSL
namespace TextPipeline

private def countStep (m : Surface.Module) (packet dst : Array UInt32) (gid : UInt32) :
    Option ScanSurface.Outcome :=
  (Surface.run m packet dst gid).map (fun r => ⟨r.dst, r.writes, false⟩)

def countGrid (bytes : ByteArray) (packet dst : Array UInt32) (lanes : List UInt32) : Option GridState := do
  let m ← Surface.parseShader bytes
  dispatch (countStep m packet) lanes PackWire.maxRows ⟨dst, []⟩

def scatterGrid (bytes : ByteArray) (packet offsets dst : Array UInt32) (lanes : List UInt32) :
    Option GridState := do
  let m ← ScatterSurface.parseShader bytes
  dispatch (fun a gid => ScatterSurface.run m packet offsets a gid) lanes PackWire.maxRows ⟨dst, []⟩

structure Result extends PipelineTarget.Packed where
  countTrace : List LaneTrace
  scanWrites : List Surface.Write
  scanReturnedEarly : Bool
  scatterTrace : List LaneTrace

/-- The packet's physical header selects the terminal word of the completed scan. -/
def run (src : ByteArray) (prior : PipelineTarget.Buffers) (countLanes scatterLanes : List UInt32) :
    Option Result := do
  let packet := PackWire.wordView src
  let counted ← countGrid countText.toUTF8 packet prior.counts countLanes
  let scanned ← ScanSurface.runText scanText.toUTF8 packet counted.dst prior.offsets
  let scattered ← scatterGrid scatterText.toUTF8 packet scanned.dst prior.words scatterLanes
  let n ← packet[1]?
  let terminal ← scanned.dst[n.toNat]?
  return ⟨⟨⟨counted.dst, scanned.dst, scattered.dst⟩, terminal⟩, counted.trace, scanned.writes,
    scanned.returnedEarly, scattered.trace⟩

def countFootprint (rows : StaticPack.Rows) (gid : UInt32) : LaneTrace :=
  ⟨gid, false, if gid.toNat < rows.length then
    [payloadEvent (gid.toNat, UInt32.ofNat (rows.getD gid.toNat []).length)] else []⟩

def scatterFootprint (rows : StaticPack.Rows) (offsets : Array UInt32) (gid : UInt32) : LaneTrace :=
  ⟨gid, false, (rowWrites rows offsets gid).map payloadEvent⟩

/-- Kind: launch budget.
Says: every valid physical lane permutation for an accepted row count fits the hard dispatch cap.
Does not say: that passing the cap alone makes a lane order valid. -/
private theorem grid_budget {n : Nat} {lanes : List UInt32} (small : n ≤ PackWire.maxRows)
    (order : CountTarget.ValidGrid n lanes) : lanes.length ≤ PackWire.maxRows := by
  have perm : (lanes.map UInt32.toNat).Perm (List.range (CountTarget.grid n)) := order
  have len : lanes.length = CountTarget.grid n := by
    simpa only [List.length_map, List.length_range] using perm.length_eq
  rw [len]
  exact (CountTarget.grid_bounds n small).2

/-- Kind: bounded dispatch simulation.
Says: per-lane success, size preservation and a witnessed store trace lift to the
same finite target array and the concatenated chronological invocation records.
Does not say: arbitrary steps commute or an arbitrary lane list covers every row. -/
private theorem dispatch_simulates {ε : Type}
    (step : Array UInt32 → UInt32 → Option ScanSurface.Outcome)
    (target : Array UInt32 → UInt32 → Except ε (Array UInt32)) (footprint : UInt32 → LaneTrace)
    (need : Nat) (lane : ∀ (prior : Array UInt32) (gid : UInt32), need ≤ prior.size →
      ∃ r, step prior gid = some r ∧ target prior gid = .ok r.dst ∧
        r.dst.size = prior.size ∧ observed gid r = footprint gid)
    (lanes : List UInt32) (fuel : Nat) (s : GridState) (bounded : lanes.length ≤ fuel) (room : need ≤ s.dst.size) :
    ∃ out, dispatch step lanes fuel s = some out ∧ lanes.foldlM target s.dst = .ok out.dst ∧
      out.dst.size = s.dst.size ∧ out.trace = s.trace ++ lanes.map footprint := by
  induction lanes generalizing fuel s with
  | nil => exact ⟨s, rfl, rfl, rfl, by simp⟩
  | cons gid rest ih =>
    cases fuel with
    | zero => simp at bounded
    | succ k =>
      obtain ⟨r, ran, matched, size, event⟩ := lane s.dst gid room
      have nextRoom : need ≤ (s.record gid r).dst.size := by
        change need ≤ r.dst.size
        rw [size]
        exact room
      have nextTrace : (s.record gid r).trace = s.trace ++ [footprint gid] := by
        change (observed gid r :: s.reversed).reverse = s.reversed.reverse ++ [footprint gid]
        rw [List.reverse_cons, event]
      obtain ⟨out, tailRun, tailTarget, finalSize, finalTrace⟩ :=
        ih k (s.record gid r) (by simpa using bounded) nextRoom
      refine ⟨out, ?_, ?_, finalSize.trans size, ?_⟩
      · change (step s.dst gid).bind (fun r => dispatch step rest k (s.record gid r)) = _
        rw [ran]
        exact tailRun
      · change (target s.dst gid).bind (fun dst => rest.foldlM target dst) = _
        rw [matched]
        exact tailTarget
      · rw [finalTrace, nextTrace]
        simp [List.append_assoc]

/-- Kind: target dispatch unfolding.
Says: the existing count dispatcher executes the same instruction for successive IDs in order.
Does not say: that a particular count run succeeds. -/
private theorem count_fold (packet : Array UInt32) (lanes : List UInt32) (prior : Array UInt32) :
    CountTarget.dispatch (CountTarget.lowerCount .count) packet lanes prior =
      lanes.foldlM (fun a gid => (CountTarget.lowerCount .count).exec packet gid a) prior := by
  induction lanes generalizing prior with
  | nil => rfl
  | cons gid rest ih =>
    change ((CountTarget.lowerCount .count).exec packet gid prior).bind _ =
      ((CountTarget.lowerCount .count).exec packet gid prior).bind _
    cases (CountTarget.lowerCount .count).exec packet gid prior with
    | error _ => rfl
    | ok a => exact ih a

/-- Kind: count text dispatch.
Says: parsing the exact count shader and executing a valid grid yields its complete
finite target array and all the actual per-lane store records, including padded lanes.
Does not say: that hardware must issue these invocations in that particular order. -/
theorem decoded_count_text_grid {src : ByteArray} {rows : StaticPack.Rows} (accepted : PackWire.decode src = .ok rows)
    (prior : Array UInt32) (lanes : List UInt32) (room : rows.length ≤ prior.size)
    (order : CountTarget.ValidGrid rows.length lanes) :
    ∃ out, countGrid countText.toUTF8 (PackWire.wordView src) prior lanes = some out ∧
      CountTarget.dispatch (CountTarget.lowerCount .count) (PackWire.wordView src) lanes prior = .ok out.dst ∧
      out.dst.size = prior.size ∧ out.trace = lanes.map (countFootprint rows) := by
  let packet := PackWire.wordView src
  let step := countStep countModule packet
  let target := fun (a : Array UInt32) (gid : UInt32) => (CountTarget.lowerCount .count).exec packet gid a
  have lane : ∀ (a : Array UInt32) (gid : UInt32), rows.length ≤ a.size →
      ∃ r, step a gid = some r ∧ target a gid = .ok r.dst ∧ r.dst.size = a.size ∧
        observed gid r = countFootprint rows gid := by
    intro a gid cap
    obtain ⟨r, bytes, instruction, size, effects⟩ := decoded_count_text_lane accepted a cap gid
    unfold Surface.runText at bytes
    rw [parse_count_text] at bytes
    have parsed : Surface.run countModule packet a gid = some r := bytes
    refine ⟨⟨r.dst, r.writes, false⟩, ?_, instruction, size, ?_⟩
    · change (Surface.run countModule packet a gid).map
        (fun seen => (⟨seen.dst, seen.writes, false⟩ : ScanSurface.Outcome)) = _
      rw [parsed] <;> rfl
    · change LaneTrace.mk gid false (r.writes.map scatterEvent) =
        LaneTrace.mk gid false (if gid.toNat < rows.length then
          [payloadEvent (gid.toNat, UInt32.ofNat (rows.getD gid.toNat []).length)] else [])
      by_cases active : gid.toNat < rows.length
      · rw [if_pos active] at effects
        obtain ⟨v, stored, value⟩ := effects
        rw [if_pos active, stored, ← value, UInt32.ofNat_toNat] <;> rfl
      · rw [if_neg active] at effects
        rw [if_neg active, effects] <;> rfl
  obtain ⟨out, ran, matched, size, trace⟩ := dispatch_simulates step target (countFootprint rows) rows.length
    lane lanes PackWire.maxRows ⟨prior, []⟩ (grid_budget (PackWire.decode_row_count_le accepted) order) room
  refine ⟨out, ?_, (count_fold packet lanes prior).trans matched, size, trace⟩
  unfold countGrid
  rw [parse_count_text]
  exact ran

/-- Kind: scatter text dispatch.
Says: the actual parsed scatter grid on a completed scan agrees on its entire finite
payload with the instruction dispatcher and emits the precise sequence of row store traces.
Does not say: that the offsets exist before the preceding scan finishes. -/
theorem decoded_scatter_text_grid {src : ByteArray} {rows : StaticPack.Rows} (accepted : PackWire.decode src = .ok rows)
    (offsets prior : Array UInt32) (lanes : List UInt32) (offsetRoom : rows.length + 1 ≤ offsets.size)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) = (StaticPack.counts rows).scanl (· + ·) 0)
    (room : (StaticPack.counts rows).sum ≤ prior.size) (order : CountTarget.ValidGrid rows.length lanes) :
    ∃ out, scatterGrid scatterText.toUTF8 (PackWire.wordView src) offsets prior lanes = some out ∧
      ScatterTarget.dispatch ⟨PackWire.wordView src, offsets⟩ lanes prior = .ok out.dst ∧
      out.dst.size = prior.size ∧ out.trace = lanes.map (scatterFootprint rows offsets) := by
  let packet := PackWire.wordView src
  let step := fun (a : Array UInt32) (gid : UInt32) => ScatterSurface.run scatterModule packet offsets a gid
  let target := fun (a : Array UInt32) (gid : UInt32) => ScatterTarget.lane ⟨packet, offsets⟩ gid a
  have lane : ∀ (a : Array UInt32) (gid : UInt32), (StaticPack.counts rows).sum ≤ a.size →
      ∃ r, step a gid = some r ∧ target a gid = .ok r.dst ∧ r.dst.size = a.size ∧
        observed gid r = scatterFootprint rows offsets gid := by
    intro a gid cap
    obtain ⟨r, bytes, instruction, size, normal, trace⟩ :=
      decoded_scatter_text_lane accepted offsets a gid offsetRoom scanned cap
    unfold ScatterSurface.runText at bytes
    rw [parse_scatter_text] at bytes
    refine ⟨r, bytes, instruction, size, ?_⟩
    change LaneTrace.mk gid r.returnedEarly (r.writes.map scatterEvent) =
      LaneTrace.mk gid false ((rowWrites rows offsets gid).map payloadEvent)
    rw [normal, trace]
  obtain ⟨out, ran, matched, size, trace⟩ := dispatch_simulates step target (scatterFootprint rows offsets)
    (StaticPack.counts rows).sum lane lanes PackWire.maxRows ⟨prior, []⟩
    (grid_budget (PackWire.decode_row_count_le accepted) order) room
  refine ⟨out, ?_, matched, size, trace⟩
  unfold scatterGrid
  rw [parse_scatter_text]
  exact ran

end TextPipeline

/-- Kind: composed concrete-source refinement.
Says: decoding the actual packet, sufficient finite allocations, and independent
permutations of the count and scatter grids suffice to run all three concrete shader
sources. The terminal word of the returned offset array selects the ordinary CPU
pack. All spare payload words are preserved. Count and Scatter have exact per-lane
store addresses and values. Scan writes each offset address through the terminal in order.
Does not say: that a WebGPU compiler, driver, hardware scheduler, physical aliasing or
cross-pass visibility realizes the mathematical execution of these sources. -/
theorem decoded_text_pipeline {src : ByteArray} {rows : StaticPack.Rows} (accepted : PackWire.decode src = .ok rows)
    (prior : PipelineTarget.Buffers) (countLanes scatterLanes : List UInt32)
    (countsCap : rows.length ≤ prior.counts.size) (offsetsCap : rows.length + 1 ≤ prior.offsets.size)
    (wordsCap : (StaticPack.counts rows).sum ≤ prior.words.size)
    (countOrder : CountTarget.ValidGrid rows.length countLanes)
    (scatterOrder : CountTarget.ValidGrid rows.length scatterLanes) :
    ∃ result, TextPipeline.run src prior countLanes scatterLanes = some result ∧
      PipelineTarget.run src prior countLanes scatterLanes = .ok result.toPacked ∧
      result.toPacked.readback.toList = StaticPack.packSpec rows ∧
      result.counts.size = prior.counts.size ∧ result.offsets.size = prior.offsets.size ∧
      result.words.size = prior.words.size ∧
      CountTarget.memory result.counts = (DSL.countDispatch rows).runSeq (CountTarget.memory prior.counts) ∧
      CountTarget.memory result.offsets =
        (DSL.scanDispatch rows.length (CountTarget.memory result.counts)).runSeq (CountTarget.memory prior.offsets) ∧
      result.offsets[rows.length]? = some result.terminal ∧ result.terminal.toNat = (StaticPack.counts rows).sum ∧
      (∀ i, result.terminal.toNat ≤ i → result.words[i]? = prior.words[i]?) ∧
      result.countTrace = countLanes.map (TextPipeline.countFootprint rows) ∧
      result.scanReturnedEarly = false ∧ result.scanWrites.map writeKey = offsetKeys (rows.length + 1) ∧
      result.scatterTrace = scatterLanes.map (TextPipeline.scatterFootprint rows result.offsets) := by
  let packet := PackWire.wordView src
  obtain ⟨c, countTextRun, countTargetRun, _, countTrace⟩ :=
    TextPipeline.decoded_count_text_grid accepted prior.counts countLanes countsCap countOrder
  obtain ⟨counts, scan, terminal, countRun, scanTextRun, scanTargetRun, scanSize, scanNormal, _, scanned,
      terminalSlot, _, scanTrace⟩ :=
    decoded_count_scan_text accepted prior.counts prior.offsets countLanes countsCap offsetsCap countOrder
  have sameCount : counts = c.dst := Except.ok.inj (countRun.symm.trans countTargetRun)
  subst counts
  have offsetRoom : rows.length + 1 ≤ scan.dst.size := by rw [scanSize]; exact offsetsCap
  obtain ⟨d, scatterTextRun, scatterTargetRun, _, scatterTrace⟩ :=
    TextPipeline.decoded_scatter_text_grid accepted scan.dst prior.words scatterLanes offsetRoom
      scanned wordsCap scatterOrder
  obtain ⟨n, header, nVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_header_word accepted)
  have terminalRead : scan.dst[n.toNat]? = some terminal :=
    (congrArg (fun i : Nat => scan.dst[i]?) nVal).trans terminalSlot
  let packed : PipelineTarget.Packed := ⟨⟨c.dst, scan.dst, d.dst⟩, terminal⟩
  let result : TextPipeline.Result := ⟨packed, c.trace, scan.writes, scan.returnedEarly, d.trace⟩
  have textRun : TextPipeline.run src prior countLanes scatterLanes = some result := by
    simp only [TextPipeline.run, Option.bind_eq_bind, countTextRun, Option.bind_some, scanTextRun,
      scatterTextRun, header, terminalRead] <;> rfl
  let inputs : LoopTarget.Inputs := ⟨packet, scan.dst⟩
  have scattered : ScatterTarget.dispatch inputs scatterLanes prior.words = .ok d.dst := scatterTargetRun
  have readN : LoopTarget.read inputs .packet 1 = .ok n := LoopTarget.read_ok inputs .packet 1 n header
  have readEnd : LoopTarget.read inputs .auxiliary n = .ok terminal :=
    LoopTarget.read_ok inputs .auxiliary n terminal terminalRead
  have targetRun : PipelineTarget.run src prior countLanes scatterLanes = .ok packed := by
    dsimp only [PipelineTarget.run]
    rw [countTargetRun]
    change (ScanTarget.run ⟨packet, c.dst⟩ prior.offsets).bind _ = _
    rw [scanTargetRun]
    change (ScatterTarget.dispatch inputs scatterLanes prior.words).bind _ = _
    rw [scattered]
    change (LoopTarget.read inputs .packet 1).bind _ = _
    rw [readN]
    change (LoopTarget.read inputs .auxiliary n).bind _ = _
    rw [readEnd] <;> rfl
  obtain ⟨other, otherRun, readback, cs, os, ds, cm, om, last, total, tail⟩ :=
    PipelineTarget.decoded_pipeline accepted prior countLanes scatterLanes countsCap offsetsCap wordsCap
      countOrder scatterOrder
  have same : other = packed := Except.ok.inj (otherRun.symm.trans targetRun)
  subst other
  exact ⟨result, textRun, targetRun, readback, cs, os, ds, cm, om, last, total, tail, countTrace,
    scanNormal, scanTrace, scatterTrace⟩

/-- Kind: executable concrete-source readback.
Says: the prefix observed from the returned finite payload is exactly the CPU specification
on all admitted inputs and independent valid orders, including the empty dispatches.
Does not say: that a physical staging buffer contains this mathematical result. -/
theorem decoded_text_pipeline_eq_packSpec {src : ByteArray} {rows : StaticPack.Rows}
    (accepted : PackWire.decode src = .ok rows) (prior : PipelineTarget.Buffers) (countLanes scatterLanes : List UInt32)
    (countsCap : rows.length ≤ prior.counts.size) (offsetsCap : rows.length + 1 ≤ prior.offsets.size)
    (wordsCap : (StaticPack.counts rows).sum ≤ prior.words.size)
    (countOrder : CountTarget.ValidGrid rows.length countLanes) (scatterOrder : CountTarget.ValidGrid rows.length scatterLanes) :
    (TextPipeline.run src prior countLanes scatterLanes).map (fun result => result.toPacked.readback.toList) =
      some (StaticPack.packSpec rows) := by
  obtain ⟨result, run, _, readback, _⟩ :=
    decoded_text_pipeline accepted prior countLanes scatterLanes countsCap offsetsCap wordsCap countOrder scatterOrder
  rw [run]
  exact congrArg some readback

#print axioms TextPipeline.grid_budget
#print axioms TextPipeline.dispatch_simulates
#print axioms TextPipeline.count_fold
#print axioms TextPipeline.decoded_count_text_grid
#print axioms TextPipeline.decoded_scatter_text_grid
#print axioms decoded_text_pipeline
#print axioms decoded_text_pipeline_eq_packSpec

end L4Factoidal.Paralliverse.WGSL
