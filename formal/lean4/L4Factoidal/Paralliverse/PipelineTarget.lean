import L4Factoidal.Paralliverse.CountPacketTheorems
import L4Factoidal.Paralliverse.ScanTarget
import L4Factoidal.Paralliverse.ScatterTarget

/-! # Stable packing on finite target buffers

Count and scatter accept independent physical lane orders. A single scan invocation
reads the count result. Scatter then reads the returned offsets. The final readback
uses the packet's row-count word to find the terminal offset in that same array.
-/

namespace L4Factoidal.Paralliverse.PipelineTarget

structure Buffers where
  counts : Array UInt32
  offsets : Array UInt32
  words : Array UInt32

structure Packed extends Buffers where
  terminal : UInt32

def Packed.readback (result : Packed) : Array UInt32 :=
  result.words.extract 0 result.terminal.toNat

/-- Run the three lowered stages and read the terminal word from the completed scan.
Each checked operation propagates its fault. -/
def run (src : ByteArray) (prior : Buffers) (countLanes scatterLanes : List UInt32) :
    Except LoopTarget.Fault Packed := do
  let packet := PackWire.wordView src
  let counts ← (CountTarget.dispatch (CountTarget.lowerCount .count) packet countLanes prior.counts).mapError
    LoopTarget.Fault.storage
  let offsets ← ScanTarget.run ⟨packet, counts⟩ prior.offsets
  let inputs : LoopTarget.Inputs := ⟨packet, offsets⟩
  let words ← ScatterTarget.dispatch inputs scatterLanes prior.words
  let n ← LoopTarget.read inputs .packet 1
  let terminal ← LoopTarget.read inputs .auxiliary n
  return ⟨⟨counts, offsets, words⟩, terminal⟩

/-- Kind: composed finite target refinement.
Says: the accepted bytes, three allocation bounds and any two valid padded grids
suffice for the actual count, scan and scatter program to finish without fault.
Its finite readback is the ordinary CPU pack. All three allocations keep their
sizes, the entire count and offset memories match the corresponding DSL stages,
and every output slot from the physical terminal onwards retains its prior value.
Does not say: that a host supplies dispatch visibility or a device executes these
instructions, or that emitted shader text has this semantics. -/
theorem decoded_pipeline {src : ByteArray} {rows : StaticPack.Rows} (h : PackWire.decode src = .ok rows)
    (prior : Buffers) (countLanes scatterLanes : List UInt32)
    (countsCap : rows.length ≤ prior.counts.size) (offsetsCap : rows.length + 1 ≤ prior.offsets.size)
    (wordsCap : (StaticPack.counts rows).sum ≤ prior.words.size)
    (countOrder : CountTarget.ValidGrid rows.length countLanes)
    (scatterOrder : CountTarget.ValidGrid rows.length scatterLanes) :
    ∃ result, run src prior countLanes scatterLanes = .ok result ∧
      result.readback.toList = StaticPack.packSpec rows ∧
      result.counts.size = prior.counts.size ∧ result.offsets.size = prior.offsets.size ∧
      result.words.size = prior.words.size ∧
      CountTarget.memory result.counts = (DSL.countDispatch rows).runSeq (CountTarget.memory prior.counts) ∧
      CountTarget.memory result.offsets =
        (DSL.scanDispatch rows.length (CountTarget.memory result.counts)).runSeq (CountTarget.memory prior.offsets) ∧
      result.offsets[rows.length]? = some result.terminal ∧ result.terminal.toNat = (StaticPack.counts rows).sum ∧
      ∀ i, result.terminal.toNat ≤ i → result.words[i]? = prior.words[i]? := by
  obtain ⟨counted, countRun, countSize, countMem⟩ :=
    CountTarget.decoded_count_eq_dsl h prior.counts countsCap countLanes countOrder
  have countView : DSL.view rows.length (CountTarget.memory counted) = StaticPack.counts rows := by
    rw [countMem]
    exact DSL.count_visible rows _ (List.range rows.length) (.refl _)
  let scanInputs : LoopTarget.Inputs := ⟨PackWire.wordView src, counted⟩
  have header : (scanInputs.packet[1]?).map UInt32.toNat = some rows.length := PackWire.decode_header_word h
  have limit := PackWire.decode_row_count_le h
  have countRoom : rows.length ≤ counted.size := by rw [countSize]; exact countsCap
  have budget : (DSL.view rows.length (CountTarget.memory counted)).sum ≤ PackWire.maxWords := by
    rw [countView]
    exact PackWire.decode_total_bound h
  obtain ⟨offsets, scanRun, visible, _⟩ :=
    ScanTarget.scan_visible scanInputs rows.length prior.offsets header limit countRoom offsetsCap budget
  obtain ⟨other, sameRun, offsetSize, offsetMem⟩ :=
    ScanTarget.scan_memory scanInputs rows.length prior.offsets header limit countRoom offsetsCap budget
  have same : other = offsets := Except.ok.inj (sameRun.symm.trans scanRun)
  subst other
  have offsetRoom : rows.length + 1 ≤ offsets.size := by rw [offsetSize]; exact offsetsCap
  have scanView : DSL.view (rows.length + 1) (CountTarget.memory offsets) =
      (StaticPack.counts rows).scanl (· + ·) 0 :=
    visible.trans (congrArg (fun widths : List Nat => widths.scanl (· + ·) 0) countView)
  obtain ⟨words, terminal, scatterRun, wordsSize, endSlot, total, readback, tail⟩ :=
    ScatterTarget.decoded_scatter_grid_eq_packSpec h offsets prior.words scatterLanes offsetRoom scanView
      wordsCap scatterOrder
  let inputs : LoopTarget.Inputs := ⟨PackWire.wordView src, offsets⟩
  obtain ⟨n, nSlot, nVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_header_word h)
  have readN : LoopTarget.read inputs .packet 1 = .ok n := LoopTarget.read_ok inputs .packet 1 n nSlot
  have readEnd : LoopTarget.read inputs .auxiliary n = .ok terminal := by
    apply LoopTarget.read_ok
    change offsets[n.toNat]? = some terminal
    rwa [nVal]
  let result : Packed := ⟨⟨counted, offsets, words⟩, terminal⟩
  refine ⟨result, ?_, readback, countSize, offsetSize, wordsSize, countMem, offsetMem, endSlot, total, tail⟩
  dsimp only [run]
  rw [countRun]
  change (ScanTarget.run scanInputs prior.offsets).bind _ = _
  rw [scanRun]
  change (ScatterTarget.dispatch ⟨PackWire.wordView src, offsets⟩ scatterLanes prior.words).bind _ = _
  rw [scatterRun]
  change (LoopTarget.read inputs .packet 1).bind _ = _
  rw [readN]
  change (LoopTarget.read inputs .auxiliary n).bind _ = _
  rw [readEnd] <;> rfl

/-- Kind: executable readback equivalence.
Says: taking the returned finite prefix of the three-stage target program yields
exactly the CPU specification for every accepted packet, adequate allocation and
valid independent count and scatter order.
Does not say: that WGSL text, a driver or hardware gives the same result. -/
theorem decoded_pipeline_eq_packSpec {src : ByteArray} {rows : StaticPack.Rows}
    (h : PackWire.decode src = .ok rows) (prior : Buffers) (countLanes scatterLanes : List UInt32)
    (countsCap : rows.length ≤ prior.counts.size) (offsetsCap : rows.length + 1 ≤ prior.offsets.size)
    (wordsCap : (StaticPack.counts rows).sum ≤ prior.words.size)
    (countOrder : CountTarget.ValidGrid rows.length countLanes)
    (scatterOrder : CountTarget.ValidGrid rows.length scatterLanes) :
    (run src prior countLanes scatterLanes).map (fun result => result.readback.toList) =
      .ok (StaticPack.packSpec rows) := by
  obtain ⟨result, done_, readback, _⟩ :=
    decoded_pipeline h prior countLanes scatterLanes countsCap offsetsCap wordsCap countOrder scatterOrder
  rw [done_]
  exact congrArg Except.ok readback

#print axioms decoded_pipeline
#print axioms decoded_pipeline_eq_packSpec

-- Only the physical terminal selects the readback. Spare words in every array survive.
#guard match PackWire.encode [[], [0xffffffff, 4], [], [4]] with
  | .error _ => false
  | .ok src =>
    let prior : Buffers := ⟨#[91, 92, 93, 94, 95], #[81, 82, 83, 84, 85, 86], #[71, 72, 73, 74, 75]⟩
    let lanes := CountTarget.canonicalLanes 4
    match run src prior lanes lanes.reverse with
    | .error _ => false
    | .ok out => out.counts == #[0, 2, 0, 1, 95] && out.offsets == #[0, 0, 2, 2, 3, 86] &&
        out.words == #[0xffffffff, 4, 4, 74, 75] && out.readback == #[0xffffffff, 4, 4]

end L4Factoidal.Paralliverse.PipelineTarget
