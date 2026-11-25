import L4Factoidal.Paralliverse.WGSL.ShaderText
import L4Factoidal.Paralliverse.WGSL.ScanSurface
import L4Factoidal.Paralliverse.CountPacketTheorems
import L4Factoidal.Paralliverse.ScanTarget

/-! # The concrete single-invocation WGSL scan -/

namespace L4Factoidal.Paralliverse.WGSL

def scanModule : ScanSurface.Module where
  first := ⟨0, 0, .read, .srcWords⟩
  second := ⟨0, 1, .read, .auxWords⟩
  third := ⟨0, 2, .readWrite, .dstWords⟩
  sizeX := 1
  sizeY := 1
  sizeZ := 1
  code := {
    initialCarry := .literal 0
    snapshot := .load .srcWords (.literal 1)
    guardLeft := .localWord .bound
    guardRight := .literal 128
    initialIndex := .literal 0
    testLeft := .localWord .index
    testRight := .localWord .bound
    increment := .add (.localWord .index) (.literal 1)
    store := ⟨.dstWords, .localWord .index, .localWord .word0⟩
    updateCarry := .add (.localWord .word0) (.load .auxWords (.localWord .index))
    terminal := ⟨.dstWords, .load .srcWords (.literal 1), .localWord .word0⟩
  }

set_option maxRecDepth 8192 in
/-- Kind: concrete syntax.
Says: the exact UTF-8 source parses to these bindings, initialisers, limit guard,
for-loop test and increment, carry update, and final storage assignment.
Does not say: that a device's WGSL compiler preserves this meaning. -/
theorem parse_scan_text : ScanSurface.parseShader scanText.toUTF8 = some scanModule := by
  rfl

/-- Kind: launch geometry.
Says: the parsed shader's workgroup has one invocation in all cases, including
zero rows, when the host submits the specified single workgroup.
Does not say: that the host issued this dispatch after the Count pass. -/
theorem scan_text_launch :
    (ScanSurface.parseShader scanText.toUTF8).map (fun m => (m.sizeX, m.sizeY, m.sizeZ)) = some (1, 1, 1) := by
  rw [parse_scan_text] <;> rfl

def writeKey (w : Surface.Write) : Nat × Nat × Nat := (w.group, w.slot, w.address.toNat)

def offsetKeys (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).map (fun i => (0, 2, i))

private def frame (n i : UInt32) (s : LoopTarget.State) (seen : Array Surface.Write) : ScanSurface.Frame :=
  ⟨s.locals 0, n, i, s.dst, seen⟩

private def advanced (s : LoopTarget.State) (i v : UInt32) (h : i.toNat < s.dst.size) : LoopTarget.State :=
  ({s with dst := s.dst.set i.toNat (s.locals 0) h} : LoopTarget.State).assign 0 (s.locals 0 + v)

/-- Kind: store trace.
Says: appending the actual next offset store extends the chronological footprint by one word.
Does not say: that arbitrary storage assignments use consecutive addresses. -/
private theorem keys_push (seen : Array Surface.Write) (i v : UInt32) (base : Nat)
    (idx : i.toNat = base) (previous : seen.toList.map writeKey = offsetKeys base) :
    (seen.push ⟨0, 2, i, v⟩).toList.map writeKey = offsetKeys (base + 1) := by
  calc
    _ = seen.toList.map writeKey ++ [(0, 2, i.toNat)] := by simp [writeKey]
    _ = offsetKeys base ++ [(0, 2, base)] := by rw [previous, idx]
    _ = offsetKeys (base + 1) := by simp [offsetKeys, List.range_succ]

/-- Kind: target instruction evaluation.
Says: the target first stores the current carry, then loads the count and updates its local.
Does not say: that an arbitrary unsigned addition equals natural addition. -/
private theorem target_step (inputs : LoopTarget.Inputs) (i v : UInt32) (s : LoopTarget.State)
    (room : i.toNat < s.dst.size) (cell : inputs.auxiliary[i.toNat]? = some v) :
    ScanTarget.body.exec inputs 0 i s = .ok (advanced s i v room) := by
  have read := LoopTarget.read_ok inputs .auxiliary i v cell
  change (LoopTarget.store s i (s.locals 0)).bind (fun t =>
    ((LoopTarget.read inputs .auxiliary i).bind (fun w => .ok (t.locals 0 + w))).bind
      (fun w => .ok (t.assign 0 w))) = _
  rw [LoopTarget.store_ok s i (s.locals 0) room, read] <;> rfl

/-- Kind: surface instruction evaluation.
Says: the parsed body performs the same store and carry update using its actual
auxiliary binding, records that store and evaluates the unsigned index increment.
Does not say: that a host has supplied the completed count buffer. -/
private theorem surface_step (inputs : LoopTarget.Inputs) (n i v : UInt32) (s : LoopTarget.State)
    (seen : Array Surface.Write) (room : i.toNat < s.dst.size) (cell : inputs.auxiliary[i.toNat]? = some v) :
    ScanSurface.step scanModule inputs.packet inputs.auxiliary (frame n i s seen) =
      some (frame n (i + 1) (advanced s i v room) (seen.push ⟨0, 2, i, s.locals 0⟩)) := by
  let stored : ScanSurface.Frame := {
    frame n i s seen with dst := s.dst.set i.toNat (s.locals 0) room, writes := seen.push ⟨0, 2, i, s.locals 0⟩}
  have store : ScanSurface.write scanModule inputs.packet inputs.auxiliary scanModule.code.store (frame n i s seen) =
      some stored := by
    change (if h : i.toNat < s.dst.size then some {frame n i s seen with
      dst := s.dst.set i.toNat (s.locals 0) h, writes := seen.push ⟨0, 2, i, s.locals 0⟩} else none) = _
    exact dif_pos room
  have updated : ScanSurface.eval scanModule inputs.packet inputs.auxiliary stored scanModule.code.updateCarry =
      some (s.locals 0 + v) := by
    change (inputs.auxiliary[i.toNat]?).bind (fun w => some (s.locals 0 + w)) = _
    rw [cell] <;> rfl
  unfold ScanSurface.step
  rw [store]
  change (ScanSurface.eval scanModule inputs.packet inputs.auxiliary stored scanModule.code.updateCarry).bind _ = _
  rw [updated] <;> rfl

private def initial (prior : Array UInt32) : LoopTarget.State :=
  (⟨fun _ => 0, prior⟩ : LoopTarget.State).assign 0 0

private def finish (inputs : LoopTarget.Inputs) (s : ScanSurface.Frame) : Option ScanSurface.Outcome := do
  let t ← ScanSurface.write scanModule inputs.packet inputs.auxiliary scanModule.code.terminal s
  return ⟨t.dst, t.writes.toList, false⟩

/-- Kind: surface invocation evaluation.
Says: the header is captured once; on an admitted value the guard falls through
to the parsed loop at index zero and subsequently executes the terminal store.
Does not say: that the body of an arbitrary loop is safe. -/
private theorem surface_start (inputs : LoopTarget.Inputs) (n : UInt32) (prior : Array UInt32)
    (header : inputs.packet[1]? = some n) (small : n.toNat ≤ 128) :
    ScanSurface.run scanModule inputs.packet inputs.auxiliary prior =
      (ScanSurface.loop scanModule inputs.packet inputs.auxiliary n.toNat (frame n 0 (initial prior) #[])).bind
        (finish inputs) := by
  have valid : ¬ (128 : UInt32) < n := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬128 < n.toNat
    omega
  change (inputs.packet[1]?).bind (fun bound =>
    if (128 : UInt32) < bound then some ⟨prior, [], true⟩ else
      (ScanSurface.loop scanModule inputs.packet inputs.auxiliary (min bound.toNat 128)
        (frame bound 0 (initial prior) #[])).bind (finish inputs)) = _
  rw [header]
  change (if (128 : UInt32) < n then _ else _) = _
  rw [if_neg valid, Nat.min_eq_left small]

/-- Kind: target invocation evaluation.
Says: the lowered target on the same admitted header executes its source iterator
from zero and then the source terminal store.
Does not say: that all those accesses are in bounds without capacities. -/
private theorem target_start (inputs : LoopTarget.Inputs) (n : UInt32) (prior : Array UInt32)
    (header : inputs.packet[1]? = some n) (small : n.toNat ≤ PackWire.maxRows) :
    ScanTarget.run inputs prior =
      ((LoopTarget.iterate (fun j s => ScanTarget.body.exec inputs 0 j s) n.toNat 0 (initial prior)).bind
        (fun s => ScanTarget.terminal.exec inputs 0 0 s)).map LoopTarget.State.dst := by
  have head := LoopTarget.read_ok inputs .packet 1 n header
  have loopOK :
      (LoopTarget.Stmt.forRange PackWire.maxRows ScanTarget.header ScanTarget.body).exec inputs 0 0 (initial prior) =
        LoopTarget.iterate (fun j s => ScanTarget.body.exec inputs 0 j s) n.toNat 0 (initial prior) := by
    change (LoopTarget.read inputs .packet 1).bind (fun w =>
      if w.toNat ≤ PackWire.maxRows then
        LoopTarget.iterate (fun j s => ScanTarget.body.exec inputs 0 j s) w.toNat 0 (initial prior)
      else .error (.loopLimit w.toNat PackWire.maxRows)) = _
    rw [head]
    exact if_pos small
  change (((LoopTarget.Stmt.forRange PackWire.maxRows ScanTarget.header ScanTarget.body).exec inputs 0 0
    (initial prior)).bind (fun s => ScanTarget.terminal.exec inputs 0 0 s)).map LoopTarget.State.dst = _
  rw [loopOK]

/-- Kind: bounded loop simulation.
Says: the parsed loop and the original iterator reach the same carry and entire
offset buffer, extending the actual store trace up to the captured bound.
Does not say: that a loop which exhausts the model's budget produces a result. -/
private theorem loop_sync (inputs : LoopTarget.Inputs) (n : UInt32)
    (small : n.toNat ≤ 128) (countsCap : n.toNat ≤ inputs.auxiliary.size)
    (k base : Nat) (s : LoopTarget.State) (seen : Array Surface.Write)
    (stop : base + k = n.toNat) (room : n.toNat < s.dst.size)
    (keys : seen.toList.map writeKey = offsetKeys base) :
    ∃ (last : LoopTarget.State) (writes : Array Surface.Write),
      LoopTarget.iterate (fun j t => ScanTarget.body.exec inputs 0 j t) k (UInt32.ofNat base) s = .ok last ∧
      ScanSurface.loop scanModule inputs.packet inputs.auxiliary k (frame n (UInt32.ofNat base) s seen) =
        some (frame n n last writes) ∧
      last.dst.size = s.dst.size ∧ writes.toList.map writeKey = offsetKeys n.toNat := by
  induction k generalizing base s seen with
  | zero =>
    have hb : base = n.toNat := by omega
    have atEnd : UInt32.ofNat base = n := by rw [hb, UInt32.ofNat_toNat]
    have stopped : ScanSurface.running scanModule inputs.packet inputs.auxiliary (frame n n s seen) = some false := by
      change some (decide (n < n)) = some false
      simp
    refine ⟨s, seen, rfl, ?_, rfl, ?_⟩
    · rw [atEnd, ScanSurface.loop, stopped] <;> rfl
    · rw [← hb]
      exact keys
  | succ k ih =>
    let i := UInt32.ofNat base
    have fit : base < UInt32.size := by change base < 4294967296; omega
    have iNat : i.toNat = base := UInt32.toNat_ofNat_of_lt' fit
    have active : i < n := by rw [UInt32.lt_iff_toNat_lt, iNat]; omega
    have source : i.toNat < inputs.auxiliary.size := by omega
    have dest : i.toNat < s.dst.size := by omega
    let v := inputs.auxiliary[i.toNat]'source
    have cell : inputs.auxiliary[i.toNat]? = some v := Array.getElem?_eq_getElem source
    let next := advanced s i v dest
    let nextSeen := seen.push ⟨0, 2, i, s.locals 0⟩
    have size : next.dst.size = s.dst.size := by simp [next, advanced, LoopTarget.State.assign]
    have nextKeys : nextSeen.toList.map writeKey = offsetKeys (base + 1) := keys_push seen i _ base iNat keys
    obtain ⟨last, writes, targetRest, surfaceRest, lastSize, lastKeys⟩ :=
      ih (base + 1) next nextSeen (by omega) (by rw [size]; exact room) nextKeys
    have bump : i + 1 = UInt32.ofNat (base + 1) := (UInt32.ofNat_add base 1).symm
    have running : ScanSurface.running scanModule inputs.packet inputs.auxiliary (frame n i s seen) = some true := by
      change some (decide (i < n)) = some true
      exact congrArg some (decide_eq_true active)
    refine ⟨last, writes, ?_, ?_, lastSize.trans size, lastKeys⟩
    · change (ScanTarget.body.exec inputs 0 i s).bind (fun t =>
        LoopTarget.iterate (fun j t => ScanTarget.body.exec inputs 0 j t) k (i + 1) t) = _
      rw [target_step inputs i v s dest cell]
      change LoopTarget.iterate (fun j t => ScanTarget.body.exec inputs 0 j t) k (i + 1) next = _
      rw [bump]
      exact targetRest
    · change ScanSurface.loop scanModule inputs.packet inputs.auxiliary (k + 1) (frame n i s seen) = _
      rw [ScanSurface.loop, running]
      change (ScanSurface.step scanModule inputs.packet inputs.auxiliary (frame n i s seen)).bind _ = _
      rw [surface_step inputs n i v s seen dest cell]
      change ScanSurface.loop scanModule inputs.packet inputs.auxiliary k (frame n (i + 1) next nextSeen) = _
      rw [bump]
      exact surfaceRest

private def ended (n : UInt32) (s : LoopTarget.State) (seen : Array Surface.Write)
    (room : n.toNat < s.dst.size) : ScanSurface.Outcome :=
  ⟨s.dst.set n.toNat (s.locals 0) room, (seen.push ⟨0, 2, n, s.locals 0⟩).toList, false⟩

/-- Kind: terminal storage.
Says: the parsed final assignment rereads the packet header and writes the last
carry there, recording even the zero-row terminal event.
Does not say: that an arbitrary header lies within an offset buffer. -/
private theorem terminal_surface (inputs : LoopTarget.Inputs) (n : UInt32) (s : LoopTarget.State)
    (seen : Array Surface.Write) (header : inputs.packet[1]? = some n) (room : n.toNat < s.dst.size) :
    finish inputs (frame n n s seen) = some (ended n s seen room) := by
  let t : ScanSurface.Frame := {frame n n s seen with
    dst := s.dst.set n.toNat (s.locals 0) room, writes := seen.push ⟨0, 2, n, s.locals 0⟩}
  have wrote : ScanSurface.write scanModule inputs.packet inputs.auxiliary scanModule.code.terminal (frame n n s seen) =
      some t := by
    change (inputs.packet[1]?).bind (fun i => if h : i.toNat < s.dst.size then some {frame n n s seen with
      dst := s.dst.set i.toNat (s.locals 0) h, writes := seen.push ⟨0, 2, i, s.locals 0⟩} else none) = _
    rw [header]
    exact dif_pos room
  unfold finish
  rw [wrote] <;> rfl

/-- Kind: full invocation refinement.
Says: an admitted header and adequate finite bindings suffice to execute the
surface and target to the same entire offset array, with every offset written
once in order, including its terminal.
Does not say: that these counts were produced by a completed preceding dispatch. -/
private theorem scan_sync (inputs : LoopTarget.Inputs) (n : UInt32) (prior : Array UInt32)
    (header : inputs.packet[1]? = some n) (small : n.toNat ≤ 128)
    (countsCap : n.toNat ≤ inputs.auxiliary.size) (offsetCap : n.toNat < prior.size) :
    ∃ result : ScanSurface.Outcome,
      ScanSurface.run scanModule inputs.packet inputs.auxiliary prior = some result ∧
      ScanTarget.run inputs prior = .ok result.dst ∧ result.dst.size = prior.size ∧ result.returnedEarly = false ∧
      result.writes.map writeKey = offsetKeys (n.toNat + 1) := by
  obtain ⟨last, seen, targetLoop, surfaceLoop, size, keys⟩ :=
    loop_sync inputs n small countsCap n.toNat 0 (initial prior) #[] (by omega) offsetCap rfl
  have room : n.toNat < last.dst.size := by rw [size]; exact offsetCap
  have head := LoopTarget.read_ok inputs .packet 1 n header
  have targetEnd : ScanTarget.terminal.exec inputs 0 0 last =
      .ok {last with dst := last.dst.set n.toNat (last.locals 0) room} := by
    change (LoopTarget.read inputs .packet 1).bind (fun j => LoopTarget.store last j (last.locals 0)) = _
    rw [head]
    exact LoopTarget.store_ok last n (last.locals 0) room
  have zero : UInt32.ofNat 0 = 0 := by decide
  rw [zero] at targetLoop surfaceLoop
  refine ⟨ended n last seen room, ?_, ?_, ?_, rfl, ?_⟩
  · rw [surface_start inputs n prior header small, surfaceLoop]
    exact terminal_surface inputs n last seen header room
  · rw [target_start inputs n prior header small, targetLoop]
    change (ScanTarget.terminal.exec inputs 0 0 last).map LoopTarget.State.dst = _
    rw [targetEnd] <;> rfl
  · calc
      (ended n last seen room).dst.size = last.dst.size := by simp [ended]
      _ = (initial prior).dst.size := size
      _ = prior.size := rfl
  · exact keys_push seen n _ n.toNat rfl keys

/-- Kind: accepted packet and text refinement.
Says: the actual completed Count dispatch supplies the immutable auxiliary buffer.
The exact scan text produces the target's whole offset memory, all stable
prefixes, the physical terminal sum, and exactly the stores (0,2,0) through
(0,2,n) in order. Empty input still executes the terminal store.
Does not say: that a driver bound these buffers, enforced pass visibility,
compiled this text faithfully, or ran one workgroup. -/
theorem decoded_count_scan_text {src : ByteArray} {rows : StaticPack.Rows}
    (accepted : PackWire.decode src = .ok rows) (counts offsets : Array UInt32)
    (lanes : List UInt32) (countsCap : rows.length ≤ counts.size) (offsetsCap : rows.length + 1 ≤ offsets.size)
    (order : CountTarget.ValidGrid rows.length lanes) :
    ∃ (counted : Array UInt32) (result : ScanSurface.Outcome) (terminal : UInt32),
      CountTarget.dispatch (CountTarget.lowerCount .count) (PackWire.wordView src) lanes counts = .ok counted ∧
      ScanSurface.runText scanText.toUTF8 (PackWire.wordView src) counted offsets = some result ∧
      ScanTarget.run ⟨PackWire.wordView src, counted⟩ offsets = .ok result.dst ∧
      result.dst.size = offsets.size ∧ result.returnedEarly = false ∧
      CountTarget.memory result.dst =
        (DSL.scanDispatch rows.length (CountTarget.memory counted)).runSeq (CountTarget.memory offsets) ∧
      DSL.view (rows.length + 1) (CountTarget.memory result.dst) = (StaticPack.counts rows).scanl (· + ·) 0 ∧
      result.dst[rows.length]? = some terminal ∧ terminal.toNat = (StaticPack.counts rows).sum ∧
      result.writes.map writeKey = offsetKeys (rows.length + 1) := by
  obtain ⟨counted, countRun, countSize, countMem⟩ :=
    CountTarget.decoded_count_eq_dsl accepted counts countsCap lanes order
  have countView : DSL.view rows.length (CountTarget.memory counted) = StaticPack.counts rows := by
    rw [countMem]
    exact DSL.count_visible rows _ (List.range rows.length) (.refl _)
  let inputs : LoopTarget.Inputs := ⟨PackWire.wordView src, counted⟩
  have header : (inputs.packet[1]?).map UInt32.toNat = some rows.length := PackWire.decode_header_word accepted
  obtain ⟨n, cell, nVal⟩ := Option.map_eq_some_iff.mp header
  have small := PackWire.decode_row_count_le accepted
  have countRoom : rows.length ≤ counted.size := by rw [countSize]; exact countsCap
  have total : (DSL.view rows.length (CountTarget.memory counted)).sum ≤ PackWire.maxWords := by
    rw [countView]
    exact PackWire.decode_total_bound accepted
  obtain ⟨result, surface, target, size, normal, trace⟩ := scan_sync inputs n offsets cell
    (by rw [nVal]; exact small) (by rw [nVal]; exact countRoom) (by omega)
  obtain ⟨out, visibleRun, visible, last⟩ := ScanTarget.scan_visible inputs rows.length offsets header small
    countRoom offsetsCap total
  have eqOut := Except.ok.inj (visibleRun.symm.trans target)
  subst out
  obtain ⟨other, memoryRun, _, memory⟩ := ScanTarget.scan_memory inputs rows.length offsets header small
    countRoom offsetsCap total
  have eqOther := Except.ok.inj (memoryRun.symm.trans target)
  subst other
  have room : rows.length < result.dst.size := by rw [size]; omega
  let terminal := result.dst[rows.length]'room
  have physical : result.dst[rows.length]? = some terminal := Array.getElem?_eq_getElem room
  have sum : terminal.toNat = (StaticPack.counts rows).sum := by
    change ((result.dst[rows.length]?).getD 0).toNat = _ at last
    rw [physical, countView] at last
    exact last
  refine ⟨counted, result, terminal, countRun, ?_, target, size, normal, memory, ?_, physical, sum, ?_⟩
  · unfold ScanSurface.runText
    rw [parse_scan_text]
    exact surface
  · exact visible.trans (congrArg (fun widths : List Nat => widths.scanl (· + ·) 0) countView)
  · rw [nVal] at trace
    exact trace

#print axioms parse_scan_text
#print axioms scan_text_launch
#print axioms keys_push
#print axioms target_step
#print axioms surface_step
#print axioms surface_start
#print axioms target_start
#print axioms loop_sync
#print axioms terminal_surface
#print axioms scan_sync
#print axioms decoded_count_scan_text

end L4Factoidal.Paralliverse.WGSL
