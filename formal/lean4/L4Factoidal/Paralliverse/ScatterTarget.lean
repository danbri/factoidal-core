import L4Factoidal.Paralliverse.LoopTarget
import L4Factoidal.Paralliverse.PackWireTheorems

/-! # Finite storage instructions for the stable scatter

The only immutable inputs are the raw packet and completed offset binding. A lane
checks the row count before reading its descriptor. Locals 0 and 1 hold the absolute
source and destination starts. The copying loop uses native u32 address addition.
-/

namespace L4Factoidal.Paralliverse.ScatterTarget
open LoopTarget
open L4Factoidal.GpuKernel

def header : Expr := .load .packet (.literal 1)
def descriptor (field : UInt32) : Expr := .add (.literal field) (.mul (.literal 2) .globalId)
def bankBase : Expr := .add (.literal 3) (.mul (.literal 2) header)

def body : Stmt :=
  .storeWord (.add (.localWord 1) .index) (.load .packet (.add (.localWord 0) .index))

def activeLane : Stmt :=
  .seq (.assign 0 (.add bankBase (.load .packet (descriptor 3))))
    (.seq (.assign 1 (.load .auxiliary .globalId))
      (.forRange PackWire.maxWords (.load .packet (descriptor 4)) body))

def lowerScatter : DSL.Stage .scanned .packed → Stmt
  | .scatter => .whenLt .globalId header activeLane

def lane (inputs : Inputs) (gid : UInt32) (prior : Array UInt32) : Except Fault (Array UInt32) :=
  ((lowerScatter .scatter).exec inputs gid 0 ⟨fun _ => 0, prior⟩).map State.dst

def wordMemory (a : Array UInt32) : Mem UInt32 := fun j => a[j]?.getD 0

/-- Kind: instruction evaluation.
Says: the header load decides whether the whole active lane runs.
Does not say: that an active lane's descriptor is valid. -/
private theorem guard_ok (inputs : Inputs) (gid n : UInt32) (s : State)
    (head : read inputs .packet 1 = .ok n) :
    (lowerScatter .scatter).exec inputs gid 0 s =
      if gid < n then activeLane.exec inputs gid 0 s else .ok s := by
  change (read inputs .packet 1).bind (fun w =>
    if gid < w then activeLane.exec inputs gid 0 s else .ok s) = _
  rw [head] <;> rfl

/-- Kind: instruction refinement.
Says: every padded or otherwise inactive lane with a readable header returns the prior
destination, even if neither a descriptor nor an auxiliary word exists for that ID.
Does not say: that the active lanes have been dispatched. -/
theorem inactive_lane (inputs : Inputs) (gid n : UInt32) (prior : Array UInt32)
    (head : inputs.packet[1]? = some n) (inactive : ¬ gid < n) :
    lane inputs gid prior = .ok prior := by
  have hh : read inputs .packet 1 = .ok n := read_ok inputs .packet 1 n head
  unfold lane
  rw [guard_ok inputs gid n _ hh, if_neg inactive] <;> rfl

/-- Kind: arithmetic refinement.
Says: the u32 addition in a copy address equals natural addition when its sum fits.
Does not say: that the resulting address is within a supplied buffer. -/
private theorem add_index (base : UInt32) (k : Nat) (h : base.toNat + k < UInt32.size) :
    (base + UInt32.ofNat k).toNat = base.toNat + k := by
  have hk : k < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk, Nat.mod_eq_of_lt h]

/-- Kind: instruction evaluation.
Says: one successful body reads the physical source word and changes one checked slot
of the finite destination while preserving the local registers.
Does not say: that a source word agrees with a particular logical row. -/
private theorem body_ok (inputs : Inputs) (gid k w : UInt32) (s : State)
    (hr : read inputs .packet (s.locals 0 + k) = .ok w)
    (hd : (s.locals 1 + k).toNat < s.dst.size) :
    body.exec inputs gid k s = .ok {s with dst := s.dst.set (s.locals 1 + k).toNat w hd} := by
  change (read inputs .packet (s.locals 0 + k)).bind (fun v => store s (s.locals 1 + k) v) = _
  rw [hr]
  exact store_ok s _ _ hd

/-- Kind: memory algebra.
Says: the first word of a consecutive write is installed before the remaining words.
Does not say: that two overlapping writes can be reordered. -/
private theorem writes_cons (b : Nat) (x : UInt32) (xs : List UInt32) (m : Mem UInt32) :
    applyWrites m (DSL.writesFrom b (x :: xs)) =
      applyWrites (m.write b x) (DSL.writesFrom (b + 1) xs) := by
  have h : DSL.writesFrom b (x :: xs) = (b, x) :: DSL.writesFrom (b + 1) xs := by
    simp [DSL.writesFrom, List.range'_succ]
  rw [h] <;> rfl

/-- Kind: bounded loop simulation.
Says: copying an actual finite source window with representable addresses and sufficient
destination capacity terminates without a fault and performs precisely its indexed writes
on the entire prior destination, including preservation of the tail.
Does not say: that an arbitrary packet or arbitrary offsets supply those windows. -/
theorem copy_words (inputs : Inputs) (gid : UInt32) (words : List UInt32) (k : Nat) (s : State)
    (srcFit : (s.locals 0).toNat + k + words.length < UInt32.size)
    (dstFit : (s.locals 1).toNat + k + words.length < UInt32.size)
    (room : (s.locals 1).toNat + k + words.length ≤ s.dst.size)
    (source : ∀ j (hj : j < words.length),
      inputs.packet[(s.locals 0).toNat + k + j]? = some words[j]) :
    ∃ t, iterate (fun i st => body.exec inputs gid i st) words.length (UInt32.ofNat k) s = .ok t ∧
      t.dst.size = s.dst.size ∧ wordMemory t.dst = applyWrites (wordMemory s.dst)
        (DSL.writesFrom ((s.locals 1).toNat + k) words) := by
  induction words generalizing k s with
  | nil => exact ⟨s, rfl, rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.length_cons] at srcFit dstFit room
    have sa := add_index (s.locals 0) k (by omega)
    have da := add_index (s.locals 1) k (by omega)
    have rd : read inputs .packet (s.locals 0 + UInt32.ofNat k) = .ok x := by
      apply read_ok
      change inputs.packet[(s.locals 0 + UInt32.ofNat k).toNat]? = some x
      rw [sa]
      have firstPos : 0 < (x :: xs).length := by simp
      have first := source 0 firstPos
      rw [Nat.add_zero] at first
      exact first.trans (congrArg some (List.getElem_cons_zero x xs firstPos))
    have hd : (s.locals 1 + UInt32.ofNat k).toNat < s.dst.size := by rw [da]; omega
    let next : State := {s with dst := s.dst.set (s.locals 1 + UInt32.ofNat k).toNat x hd}
    have step : body.exec inputs gid (UInt32.ofNat k) s = .ok next := body_ok _ _ _ _ _ rd hd
    have size : next.dst.size = s.dst.size := by simp [next]
    have restRead : ∀ j (hj : j < xs.length),
        inputs.packet[(next.locals 0).toNat + (k + 1) + j]? = some xs[j] := by
      intro j hj
      change inputs.packet[(s.locals 0).toNat + (k + 1) + j]? = some xs[j]
      rw [show (s.locals 0).toNat + (k + 1) + j = (s.locals 0).toNat + k + (j + 1) by omega]
      exact source (j + 1) (by simpa using hj)
    obtain ⟨t, hrun, hsize, hmem⟩ := ih (k + 1) next
      (by change (s.locals 0).toNat + (k + 1) + xs.length < UInt32.size; omega)
      (by change (s.locals 1).toNat + (k + 1) + xs.length < UInt32.size; omega)
      (by rw [size]; change (s.locals 1).toNat + (k + 1) + xs.length ≤ s.dst.size; omega)
      restRead
    have stored : wordMemory next.dst = (wordMemory s.dst).write ((s.locals 1).toNat + k) x := by
      calc
        wordMemory next.dst = (wordMemory s.dst).write (s.locals 1 + UInt32.ofNat k).toNat x :=
          observe_set id 0 s.dst _ x hd
        _ = _ := by rw [da]
    refine ⟨t, ?_, hsize.trans size, ?_⟩
    · change iterate _ (xs.length + 1) _ s = _
      rw [iterate, step]
      change iterate _ xs.length (UInt32.ofNat k + 1) next = _
      have bump : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := (UInt32.ofNat_add k 1).symm
      rw [bump]
      exact hrun
    · rw [hmem, stored, writes_cons] <;> rfl

/-- Kind: input representation.
Says: taking the row-start slots from a completed finite scan gives the exclusive starts.
Does not say: that an arbitrary offset array is a completed scan. -/
theorem scanned_starts (rows : StaticPack.Rows) (offsets : Array UInt32)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) =
      (StaticPack.counts rows).scanl (· + ·) 0) :
    DSL.view rows.length (CountTarget.memory offsets) = StaticPack.scanFrom 0 (StaticPack.counts rows) := by
  have hv : DSL.view (rows.length + 1) (CountTarget.memory offsets) =
      DSL.view rows.length (CountTarget.memory offsets) ++ [CountTarget.memory offsets rows.length] := by
    simp [DSL.view, List.range_succ]
  have len : (StaticPack.counts rows).length = rows.length := by simp [StaticPack.counts]
  have extent : (DSL.view rows.length (CountTarget.memory offsets)).length = rows.length := by
    simp [DSL.view]
  unfold StaticPack.scanFrom
  rw [len, ← scanned, hv, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- Kind: bounded address.
Says: the actual completed offset and row length end within the logical allocation.
Does not say: that every allocation has room for that many words. -/
private theorem offset_end (rows : StaticPack.Rows) (offsets : Array UInt32)
    (starts : DSL.view rows.length (CountTarget.memory offsets) =
      StaticPack.scanFrom 0 (StaticPack.counts rows))
    (i : Nat) (hi : i < rows.length) :
    CountTarget.memory offsets i + (rows.getD i []).length ≤ (StaticPack.counts rows).sum := by
  let spans := (DSL.view rows.length (CountTarget.memory offsets)).zip (StaticPack.counts rows)
  have hl : spans.length = rows.length := by simp [spans, DSL.view, StaticPack.counts]
  have idx : i < spans.length := by simpa only [hl] using hi
  have mem : spans[i] ∈ spans := List.mem_of_getElem (i := i) (h := idx) rfl
  have bound := (StaticPack.scanFrom_bounds 0 (StaticPack.counts rows) spans[i] (by
    rw [← starts]
    exact mem)).2
  simpa only [spans, DSL.view, StaticPack.counts, List.getElem_zip, List.getElem_map,
    List.getElem_range, Nat.zero_add, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using bound

/-- Kind: arithmetic refinement.
Says: the physical header/descriptor stride and its three-word prefix fit on packet row counts.
Does not say: that a referenced word is present. -/
private theorem address3 (w : UInt32) (h : w.toNat ≤ PackWire.maxRows) :
    (3 + 2*w : UInt32).toNat = 3 + 2*w.toNat := by
  change w.toNat ≤ 128 at h
  have hm : 2*w.toNat < 4294967296 := by omega
  have ha : 3 + 2*w.toNat < 4294967296 := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  change (3 + (2*w.toNat % 4294967296)) % 4294967296 = _
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha]

/-- Kind: instruction evaluation.
Says: an active lane assigns the source and destination starts obtained by real reads,
then executes the actual bounded copy loop for the length from the physical descriptor.
Does not say: that the loop body will find its operands in bounds. -/
private theorem active_setup (inputs : Inputs) (gid n start off len : UInt32) (s : State)
    (head : read inputs .packet 1 = .ok n)
    (startRead : read inputs .packet (3 + 2*gid) = .ok start)
    (offsetRead : read inputs .auxiliary gid = .ok off)
    (lengthRead : read inputs .packet (4 + 2*gid) = .ok len)
    (limit : len.toNat ≤ PackWire.maxWords) :
    activeLane.exec inputs gid 0 s =
      iterate (fun i st => body.exec inputs gid i st) len.toNat 0
        ((s.assign 0 (3 + 2*n + start)).assign 1 off) := by
  let absolute := 3 + 2*n + start
  let loaded := s.assign 0 absolute
  let ready := loaded.assign 1 off
  let getSource : Stmt := .assign 0 (.add bankBase (.load .packet (descriptor 3)))
  let getOffset : Stmt := .assign 1 (.load .auxiliary .globalId)
  let loop : Stmt := .forRange PackWire.maxWords (.load .packet (descriptor 4)) body
  have setSource : getSource.exec inputs gid 0 s = .ok loaded := by
    change ((((read inputs .packet 1).bind (fun w => .ok (2*w))).bind (fun v => .ok (3+v))).bind
      (fun b => (read inputs .packet (3 + 2*gid)).bind (fun v => .ok (b+v)))).bind
      (fun v => .ok (s.assign 0 v)) = _
    rw [head, startRead] <;> rfl
  have setOffset : getOffset.exec inputs gid 0 loaded = .ok ready := by
    change (read inputs .auxiliary gid).bind (fun v => .ok (loaded.assign 1 v)) = _
    rw [offsetRead] <;> rfl
  have loopOK : loop.exec inputs gid 0 ready =
      iterate (fun i st => body.exec inputs gid i st) len.toNat 0 ready := by
    change (read inputs .packet (4 + 2*gid)).bind (fun w =>
      if w.toNat ≤ PackWire.maxWords then iterate (fun i st => body.exec inputs gid i st) w.toNat 0 ready
      else .error (.loopLimit w.toNat PackWire.maxWords)) = _
    rw [lengthRead]
    exact if_pos limit
  change (getSource.exec inputs gid 0 s).bind (fun t => (Stmt.seq getOffset loop).exec inputs gid 0 t) = _
  rw [setSource]
  change (getOffset.exec inputs gid 0 loaded).bind (fun t => loop.exec inputs gid 0 t) = _
  rw [setOffset]
  exact loopOK

/-- Kind: packet-size invariant.
Says: accepted bytes passed the decoder's actual packet-size precheck.
Does not say: that a device binding is allocated to that size. -/
private theorem packet_bytes {src : ByteArray} {rows : StaticPack.Rows} (h : PackWire.decode src = .ok rows) :
    src.size ≤ 5644 := by
  by_cases over : src.size > PackWire.maxPacketBytes
  · simp [PackWire.decode, over] at h
  · exact Nat.le_of_not_gt over

/-- Kind: finite target refinement.
Says: for every accepted byte packet, completed finite scan, sufficiently large prior
destination and u32 lane ID, actual scatter instructions return without fault and
preserve the destination's extent. An active lane performs exactly its DSL row writes
at every address, and an inactive lane preserves all prior words.
Does not say: that a host or GPU provides these bindings, visibility or scheduling. -/
theorem decoded_scatter_lane {src : ByteArray} {rows : StaticPack.Rows} (h : PackWire.decode src = .ok rows)
    (offsets prior : Array UInt32) (gid : UInt32)
    (offsetCap : rows.length + 1 ≤ offsets.size)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) =
      (StaticPack.counts rows).scanl (· + ·) 0)
    (room : (StaticPack.counts rows).sum ≤ prior.size) :
    ∃ out, lane ⟨PackWire.wordView src, offsets⟩ gid prior = .ok out ∧ out.size = prior.size ∧
      wordMemory out = if gid.toNat < rows.length then
        applyWrites (wordMemory prior) ((DSL.scatterDispatch rows (CountTarget.memory offsets)).writes gid.toNat)
      else wordMemory prior := by
  let inputs : Inputs := ⟨PackWire.wordView src, offsets⟩
  obtain ⟨n, hn, nNat⟩ := Option.map_eq_some_iff.mp (PackWire.decode_header_word h)
  have head : read inputs .packet 1 = .ok n := read_ok inputs .packet 1 n hn
  have branch : gid < n ↔ gid.toNat < rows.length := by rw [UInt32.lt_iff_toNat_lt, nNat]
  by_cases active : gid.toNat < rows.length
  · let words := rows.getD gid.toNat []
    obtain ⟨start, hstart, startVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_descriptor_span h _ active).1
    obtain ⟨len, hlen, lenVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_descriptor_length_word h _ active)
    have nr : n.toNat ≤ PackWire.maxRows := nNat.symm ▸ PackWire.decode_row_count_le h
    have gr := Nat.lt_of_lt_of_le active (PackWire.decode_row_count_le h)
    have sr : read inputs .packet (3 + 2*gid) = .ok start := by
      apply read_ok
      change (PackWire.wordView src)[(3 + 2*gid : UInt32).toNat]? = some start
      rw [address3 gid (Nat.le_of_lt gr)]
      exact hstart
    have lr : read inputs .packet (4 + 2*gid) = .ok len := by
      apply read_ok
      change (PackWire.wordView src)[(4 + 2*gid : UInt32).toNat]? = some len
      rw [CountTarget.descriptor_word_address gid gr]
      exact hlen
    have ho : gid.toNat < offsets.size := by omega
    let off := offsets[gid.toNat]
    have offSlot : offsets[gid.toNat]? = some off := Array.getElem?_eq_getElem ho
    have ofr : read inputs .auxiliary gid = .ok off := read_ok inputs .auxiliary gid off offSlot
    have offVal : off.toNat = CountTarget.memory offsets gid.toNat := by simp [CountTarget.memory, offSlot]
    have hend := offset_end rows offsets (scanned_starts rows offsets scanned) gid.toNat active
    have budget : (StaticPack.counts rows).sum ≤ 1024 := PackWire.decode_total_bound h
    have wordLimit : words.length ≤ 1024 := by change (rows.getD gid.toNat []).length ≤ 1024; omega
    have limit : len.toNat ≤ PackWire.maxWords := lenVal.symm ▸ wordLimit
    let absolute := 3 + 2*n + start
    let s : State := ⟨fun _ => 0, prior⟩
    let ready := (s.assign 0 absolute).assign 1 off
    have reg0 : ready.locals 0 = absolute := by simp [ready, State.assign]
    have reg1 : ready.locals 1 = off := by simp [ready, State.assign]
    have hbytes := packet_bytes h
    have extent := PackWire.decode_extent h
    have span := (PackWire.decode_descriptor_span h _ active).2
    have fits : 3 + 2*rows.length + (PackWire.descriptorAt src gid.toNat).1 < 4294967296 := by omega
    have absNat : absolute.toNat = 3 + 2*rows.length + (PackWire.descriptorAt src gid.toNat).1 := by
      change ((3 + 2*n) + start : UInt32).toNat = _
      rw [UInt32.toNat_add, address3 n nr, nNat, startVal, Nat.mod_eq_of_lt fits]
    obtain ⟨t, ran, sz, effect⟩ := copy_words inputs gid words 0 ready
      (by rw [reg0, absNat]; change _ < 4294967296; omega)
      (by rw [reg1, offVal]; change _ < 4294967296; change _ + 0 + (rows.getD gid.toNat []).length < _; omega)
      (by rw [reg1, offVal]; change _ + 0 + (rows.getD gid.toNat []).length ≤ prior.size; omega)
      (by
        intro j hj
        rw [reg0, absNat, Nat.add_zero]
        exact (PackWire.decode_source_word h _ active j hj).2)
    have zero : UInt32.ofNat 0 = (0 : UInt32) := by decide
    rw [zero] at ran
    refine ⟨t.dst, ?_, sz, ?_⟩
    · change ((lowerScatter .scatter).exec inputs gid 0 s).map State.dst = _
      rw [guard_ok inputs gid n s head, if_pos (branch.mpr active), active_setup _ _ _ _ _ _ _ head sr ofr lr limit]
      change (iterate _ len.toNat 0 ready).map State.dst = _
      rw [lenVal, ran] <;> rfl
    · rw [if_pos active, effect, reg1, offVal, Nat.add_zero] <;> rfl
  · exact ⟨prior, inactive_lane inputs gid n prior hn (fun hg => active (branch.mp hg)),
      rfl, (if_neg active).symm⟩

#print axioms inactive_lane
#print axioms copy_words
#print axioms scanned_starts
#print axioms decoded_scatter_lane

-- Alternate offsets and an inactive lane exercise the actual checked bindings.
#guard match lane ⟨#[1, 2, 4, 3, 1, 0, 2, 8, 9, 99, 7], #[2, 0]⟩ 0 #[17, 17, 17, 17] with
  | .ok a => a == #[17, 17, 7, 17]
  | .error _ => false
#guard match lane ⟨#[1, 2, 4, 3, 1, 0, 2, 8, 9, 99, 7], #[2, 0]⟩ 1 #[17, 17, 17, 17] with
  | .ok a => a == #[8, 9, 17, 17]
  | .error _ => false
#guard match lane ⟨#[1, 1], #[]⟩ 4 #[17] with
  | .ok a => a == #[17]
  | .error _ => false

end L4Factoidal.Paralliverse.ScatterTarget
