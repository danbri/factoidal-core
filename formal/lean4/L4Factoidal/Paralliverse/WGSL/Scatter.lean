import L4Factoidal.Paralliverse.WGSL.ShaderText
import L4Factoidal.Paralliverse.WGSL.Dispatch
import L4Factoidal.Paralliverse.WGSL.ScatterSurface
import L4Factoidal.Paralliverse.ScatterTarget

/-! # The concrete stable-scatter shader and its actual store traces -/

namespace L4Factoidal.Paralliverse.WGSL
open L4Factoidal.GpuKernel

def scatterModule : ScatterSurface.Module where
  first := ⟨0, 0, .read, .srcWords⟩
  second := ⟨0, 1, .read, .auxWords⟩
  third := ⟨0, 2, .readWrite, .dstWords⟩
  sizeX := 64
  sizeY := 1
  sizeZ := 1
  code := {
    laneLeft := .gidX
    laneRight := .load .srcWords (.literal 1)
    initial0 := .add (.literal 3) (.mul (.literal 2) (.load .srcWords (.literal 1)))
    initial1 := .load .srcWords (.add (.literal 3) (.mul (.literal 2) .gidX))
    assign0 := .add (.localWord .word0) (.localWord .word1)
    assign1 := .load .auxWords .gidX
    snapshot := .load .srcWords (.add (.literal 4) (.mul (.literal 2) .gidX))
    limitLeft := .localWord .bound
    limitRight := .literal 1024
    initialIndex := .literal 0
    testLeft := .localWord .index
    testRight := .localWord .bound
    increment := .add (.localWord .index) (.literal 1)
    store := ⟨.dstWords, .add (.localWord .word1) (.localWord .index),
      .load .srcWords (.add (.localWord .word0) (.localWord .index))⟩
  }

-- This certificate separates lexical reduction from grammar reduction in the kernel.
-- Both equalities check the real implementations with the standard CI memory cap.
private def scatterTokens : Surface.Tokens :=
  (["@", "group", "(", "0", ")", "@", "binding", "(", "0", ")", "var", "<", "storage", ",", "read", ">",
    "src_words", ":", "array", "<", "u32", ">", ";",
    "@", "group", "(", "0", ")", "@", "binding", "(", "1", ")", "var", "<", "storage", ",", "read", ">",
    "aux_words", ":", "array", "<", "u32", ">", ";",
    "@", "group", "(", "0", ")", "@", "binding", "(", "2", ")", "var", "<", "storage", ",",
    "read_write", ">", "dst_words", ":", "array", "<", "u32", ">", ";",
    "@", "compute", "@", "workgroup_size", "(", "64", ",", "1", ",", "1", ")",
    "fn", "main", "(", "@", "builtin", "(", "global_invocation_id", ")", "pv_gid", ":", "vec3", "<",
    "u32", ">", ")", "{",
    "if", "(", "pv_gid", ".", "x", "<", "src_words", "[", "1u", "]", ")", "{",
    "var", "pv_l0", ":", "u32", "=", "(", "3u", "+", "(", "2u", "*", "src_words", "[", "1u", "]", ")", ")", ";",
    "var", "pv_l1", ":", "u32", "=", "src_words", "[", "(", "3u", "+", "(", "2u", "*", "pv_gid", ".",
    "x", ")", ")", "]", ";",
    "pv_l0", "=", "(", "pv_l0", "+", "pv_l1", ")", ";",
    "pv_l1", "=", "aux_words", "[", "pv_gid", ".", "x", "]", ";",
    "let", "pv_bound", ":", "u32", "=", "src_words", "[", "(", "4u", "+", "(", "2u", "*", "pv_gid", ".",
    "x", ")", ")", "]", ";",
    "if", "(", "pv_bound", ">", "1024u", ")", "{", "return", ";", "}",
    "for", "(", "var", "pv_i", ":", "u32", "=", "0u", ";", "pv_i", "<", "pv_bound", ";", "pv_i", "=",
    "(", "pv_i", "+", "1u", ")", ")", "{",
    "dst_words", "[", "(", "pv_l1", "+", "pv_i", ")", "]", "=", "src_words", "[", "(", "pv_l0", "+",
    "pv_i", ")", "]", ";", "}", "}", "}"] : List String).map fun token => token.toUTF8.data.toList

set_option maxRecDepth 8192 in
/-- Kind: lexical certificate.
Says: independently tokenizing all concrete shader bytes yields this finite token sequence.
Does not say: that the sequence parses or that any invocation succeeds. -/
private theorem scatter_lex_tokens : Surface.lex scatterText.toUTF8 = scatterTokens := by
  rfl

set_option maxRecDepth 8192 in
/-- Kind: concrete syntax.
Says: the complete static source parses to these bindings, guarded reads,
address arithmetic, captured length, loop test, increment and indexed store.
Does not say: that an external compiler implements the parser or its semantics. -/
theorem parse_scatter_text : ScatterSurface.parseShader scatterText.toUTF8 = some scatterModule := by
  unfold ScatterSurface.parseShader
  rw [scatter_lex_tokens] <;> rfl

/-- Kind: physical launch geometry.
Says: the parsed size with the proposed group count yields the target's exact padded grid.
Does not say: that the host issued this dispatch. -/
theorem scatter_text_launch (n : Nat) :
    (ScatterSurface.parseShader scatterText.toUTF8).map (fun m => (((n + 63) / 64) * m.sizeX, m.sizeY, m.sizeZ)) =
      some (CountTarget.grid n, 1, 1) := by
  rw [parse_scatter_text] <;> rfl

def payloadEvent (w : Nat × UInt32) : (Nat × Nat) × (Nat × UInt32) := ((0, 2), w)

/-- Kind: invocation semantics.
Says: the packet header guards every active-lane descriptor read and output write in the parsed shader.
Does not say: that the packet has valid descriptors after that guard. -/
private theorem scatter_header (packet offsets prior : Array UInt32) (gid n : UInt32)
    (head : packet[1]? = some n) :
    ScatterSurface.runText scatterText.toUTF8 packet offsets prior gid =
      if gid < n then ScatterSurface.active scatterModule packet offsets prior gid
      else some ⟨prior, [], false⟩ := by
  unfold ScatterSurface.runText
  rw [parse_scatter_text]
  change (packet[1]?).bind (fun h => if gid < h then ScatterSurface.active scatterModule packet offsets prior gid
    else some ⟨prior, [], false⟩) = _
  rw [head] <;> rfl

/-- Kind: padded invocation.
Says: an inactive invocation preserves its actual payload and produces an empty store trace,
even without a descriptor or offset for its ID.
Does not say: that the packet header itself can be missing. -/
theorem inactive_scatter_text (packet offsets prior : Array UInt32) (gid n : UInt32)
    (head : packet[1]? = some n) (outside : ¬ gid < n) :
    ScatterSurface.runText scatterText.toUTF8 packet offsets prior gid = some ⟨prior, [], false⟩ := by
  rw [scatter_header _ _ _ _ _ head, if_neg outside]

/-- Kind: setup semantics.
Says: parsing and executing the active assignments captures the actual source,
offset, and length words before the bounded copy starts.
Does not say: the beginning of either range guarantees enough remaining storage. -/
private theorem scatter_active (packet offsets prior : Array UInt32) (gid n start off len : UInt32)
    (head : packet[1]? = some n) (source : packet[(3 + 2 * gid : UInt32).toNat]? = some start)
    (dest : offsets[gid.toNat]? = some off) (width : packet[(4 + 2 * gid : UInt32).toNat]? = some len)
    (limit : len.toNat ≤ 1024) :
    ScatterSurface.active scatterModule packet offsets prior gid =
      (ScatterSurface.loop scatterModule packet offsets gid len.toNat
        ⟨3 + 2 * n + start, off, len, 0⟩ ⟨prior, #[]⟩).map (fun s => ⟨s.dst, s.writes.toList, false⟩) := by
  have bank : ScatterSurface.eval scatterModule packet offsets gid ⟨0, 0, 0, 0⟩ scatterModule.code.initial0 =
      some (3 + 2 * n) := by
    change ((packet[1]?).bind (fun w => some (2 * w))).bind (fun w => some (3 + w)) = _
    rw [head] <;> rfl
  have allowed : ¬ (1024 : UInt32) < len := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬1024 < len.toNat
    omega
  change (ScatterSurface.eval scatterModule packet offsets gid ⟨0, 0, 0, 0⟩ scatterModule.code.initial0).bind _ = _
  rw [bank]
  change (packet[(3 + 2 * gid : UInt32).toNat]?).bind _ = _
  rw [source]
  change (offsets[gid.toNat]?).bind _ = _
  rw [dest]
  change (packet[(4 + 2 * gid : UInt32).toNat]?).bind _ = _
  rw [width]
  change (if (1024 : UInt32) < len then _ else _) = _
  rw [if_neg allowed]
  change (ScatterSurface.loop scatterModule packet offsets gid (min len.toNat 1024)
    ⟨3 + 2 * n + start, off, len, 0⟩ ⟨prior, #[]⟩).bind
    (fun s => some (⟨s.dst, s.writes.toList, false⟩ : ScanSurface.Outcome)) = _
  rw [Nat.min_eq_left limit] <;>
    cases ScatterSurface.loop scatterModule packet offsets gid len.toNat
      ⟨3 + 2 * n + start, off, len, 0⟩ ⟨prior, #[]⟩ <;> rfl

/-- Kind: address arithmetic.
Says: a representable sum of a base word and a natural index is the shader's u32 address.
Does not say: that the indexed buffer has that extent. -/
private theorem copy_address (base : UInt32) (k : Nat) (fits : base.toNat + k < UInt32.size) :
    (base + UInt32.ofNat k).toNat = base.toNat + k := by
  have hi : k < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hi, Nat.mod_eq_of_lt fits]

/-- Kind: surface loop simulation.
Says: the parsed copy loop loads the supplied physical window and emits exactly
the successive destination events, values included. Applying those events gives
the same whole payload as the invocation, for any initially allocated payload and trace.
Does not say: that different lanes' windows are disjoint without the completed scan. -/
private theorem copy_surface (packet offsets : Array UInt32) (gid base off len : UInt32)
    (words : List UInt32) (k : Nat) (s : ScatterSurface.Storage)
    (stop : k + words.length = len.toNat)
    (srcFit : base.toNat + k + words.length < UInt32.size)
    (dstFit : off.toNat + k + words.length < UInt32.size)
    (room : off.toNat + k + words.length ≤ s.dst.size)
    (contents : ∀ j (hj : j < words.length), packet[base.toNat + k + j]? = some words[j]) :
    ∃ out : ScatterSurface.Storage,
      ScatterSurface.loop scatterModule packet offsets gid words.length ⟨base, off, len, UInt32.ofNat k⟩ s = some out ∧
      out.dst.size = s.dst.size ∧ ScatterTarget.wordMemory out.dst =
        applyWrites (ScatterTarget.wordMemory s.dst) (DSL.writesFrom (off.toNat + k) words) ∧
      out.writes.toList.map scatterEvent =
        s.writes.toList.map scatterEvent ++ (DSL.writesFrom (off.toNat + k) words).map payloadEvent := by
  induction words generalizing k s with
  | nil =>
    have endAt : k = len.toNat := by simpa using stop
    have iEnd : UInt32.ofNat k = len := by rw [endAt, UInt32.ofNat_toNat]
    have falseTest : ScatterSurface.running scatterModule packet offsets gid ⟨base, off, len, len⟩ = some false := by
      change some (decide (len < len)) = some false
      simp
    refine ⟨s, ?_, rfl, rfl, ?_⟩
    · change ScatterSurface.loop scatterModule packet offsets gid 0 ⟨base, off, len, UInt32.ofNat k⟩ s = _
      rw [iEnd, ScatterSurface.loop, falseTest] <;> rfl
    · simp [DSL.writesFrom]
  | cons x xs ih =>
    have pending : k + (xs.length + 1) = len.toNat := stop
    have sf : base.toNat + k + (xs.length + 1) < UInt32.size := srcFit
    have df : off.toNat + k + (xs.length + 1) < UInt32.size := dstFit
    have capacity : off.toNat + k + (xs.length + 1) ≤ s.dst.size := room
    let i := UInt32.ofNat k
    have iNat : i.toNat = k := UInt32.toNat_ofNat_of_lt' (by omega)
    have go : i < len := by rw [UInt32.lt_iff_toNat_lt, iNat]; omega
    have sa : (base + i).toNat = base.toNat + k := copy_address base k (by omega)
    have da : (off + i).toNat = off.toNat + k := copy_address off k (by omega)
    have read : packet[(base + i).toNat]? = some x := by
      rw [sa]
      have pos : 0 < (x :: xs).length := by simp
      have first := contents 0 pos
      rw [Nat.add_zero] at first
      exact first.trans (congrArg some (List.getElem_cons_zero x xs pos))
    have hd : (off + i).toNat < s.dst.size := by omega
    let next : ScatterSurface.Storage :=
      ⟨s.dst.set (off + i).toNat x hd, s.writes.push ⟨0, 2, off + i, x⟩⟩
    have step : ScatterSurface.write scatterModule packet offsets gid ⟨base, off, len, i⟩ s = some next := by
      change (packet[(base + i).toNat]?).bind (fun v => if h : (off + i).toNat < s.dst.size then
        some (⟨s.dst.set (off + i).toNat v h, s.writes.push ⟨0, 2, off + i, v⟩⟩ : ScatterSurface.Storage)
        else none) = some next
      rw [read]
      exact dif_pos hd
    have size : next.dst.size = s.dst.size := by simp [next]
    have tailRead : ∀ j (hj : j < xs.length), packet[base.toNat + (k + 1) + j]? = some xs[j] := by
      intro j hj
      rw [show base.toNat + (k + 1) + j = base.toNat + k + (j + 1) by omega]
      exact contents (j + 1) (by simpa using hj)
    obtain ⟨out, tailRun, tailSize, tailMem, tailTrace⟩ :=
      ih (k + 1) next (by omega) (by omega) (by omega) (by rw [size]; omega) tailRead
    have cond : ScatterSurface.running scatterModule packet offsets gid ⟨base, off, len, i⟩ = some true := by
      change some (decide (i < len)) = some true
      exact congrArg some (decide_eq_true go)
    have bump : i + 1 = UInt32.ofNat (k + 1) := (UInt32.ofNat_add k 1).symm
    have writes : DSL.writesFrom (off.toNat + k) (x :: xs) =
        (off.toNat + k, x) :: DSL.writesFrom (off.toNat + (k + 1)) xs := by
      simp [DSL.writesFrom, List.range'_succ, Nat.add_assoc]
    refine ⟨out, ?_, tailSize.trans size, ?_, ?_⟩
    · change ScatterSurface.loop scatterModule packet offsets gid (xs.length + 1) ⟨base, off, len, i⟩ s = _
      rw [ScatterSurface.loop, cond]
      change (ScatterSurface.write scatterModule packet offsets gid ⟨base, off, len, i⟩ s).bind _ = _
      rw [step]
      change ScatterSurface.loop scatterModule packet offsets gid xs.length ⟨base, off, len, i + 1⟩ next = _
      rw [bump]
      exact tailRun
    · have stored : ScatterTarget.wordMemory next.dst = (ScatterTarget.wordMemory s.dst).write (off.toNat + k) x := by
        have raw : ScatterTarget.wordMemory next.dst = (ScatterTarget.wordMemory s.dst).write (off + i).toNat x :=
          LoopTarget.observe_set id 0 s.dst _ x hd
        exact raw.trans (congrArg (fun j => (ScatterTarget.wordMemory s.dst).write j x) da)
      rw [tailMem, stored, writes] <;> rfl
    · have first : next.writes.toList.map scatterEvent =
          s.writes.toList.map scatterEvent ++ [payloadEvent (off.toNat + k, x)] := by
        simp [next, scatterEvent, payloadEvent, da]
      rw [tailTrace, first, writes]
      simp [List.append_assoc]

/-- Kind: scanned capacity.
Says: the physical start plus the length of an active row lies within the logical total.
Does not say: the host allocated that many words. -/
private theorem scatter_end (rows : StaticPack.Rows) (offsets : Array UInt32)
    (starts : DSL.view rows.length (CountTarget.memory offsets) = StaticPack.scanFrom 0 (StaticPack.counts rows))
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

/-- Kind: unsigned address refinement.
Says: the three-word prefix and the two-word descriptor stride fit at all permitted row indices.
Does not say: a field at that address contains a valid bank index. -/
private theorem descriptor3 (w : UInt32) (bound : w.toNat ≤ PackWire.maxRows) :
    (3 + 2*w : UInt32).toNat = 3 + 2*w.toNat := by
  change w.toNat ≤ 128 at bound
  have twice : 2*w.toNat < 4294967296 := by omega
  have full : 3 + 2*w.toNat < 4294967296 := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  change (3 + 2*w.toNat % 4294967296) % 4294967296 = _
  rw [Nat.mod_eq_of_lt twice, Nat.mod_eq_of_lt full]

/-- Kind: finite storage observation.
Says: the extent and all observed words uniquely identify a finite payload.
Does not say: two equal final arrays have the same intermediate writes. -/
private theorem payload_ext {a b : Array UInt32} (size : a.size = b.size)
    (memory : ScatterTarget.wordMemory a = ScatterTarget.wordMemory b) : a = b := by
  apply Array.ext size
  intro i ha hb
  have h := congrFun memory i
  simpa only [ScatterTarget.wordMemory, Array.getElem?_eq_getElem ha, Array.getElem?_eq_getElem hb,
    Option.getD_some] using h

def rowWrites (rows : StaticPack.Rows) (offsets : Array UInt32) (gid : UInt32) : List (Nat × UInt32) :=
  if gid.toNat < rows.length then (DSL.scatterDispatch rows (CountTarget.memory offsets)).writes gid.toNat else []

/-- Kind: concrete shader refinement.
Says: for any accepted packet and completed offset window, the actual parsed
Scatter text produces the existing target's entire finite array. Its chronological
stores are exactly the original row words at successive addresses of binding (0,2);
inactive lanes and empty rows have empty event lists.
Does not say: that a host has bound separate buffers or made the scan visible. -/
theorem decoded_scatter_text_lane {src : ByteArray} {rows : StaticPack.Rows} (accepted : PackWire.decode src = .ok rows)
    (offsets prior : Array UInt32) (gid : UInt32) (offsetCap : rows.length + 1 ≤ offsets.size)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) = (StaticPack.counts rows).scanl (· + ·) 0)
    (room : (StaticPack.counts rows).sum ≤ prior.size) :
    ∃ r : ScanSurface.Outcome, ScatterSurface.runText scatterText.toUTF8 (PackWire.wordView src) offsets prior gid = some r ∧
      ScatterTarget.lane ⟨PackWire.wordView src, offsets⟩ gid prior = .ok r.dst ∧
      r.dst.size = prior.size ∧ r.returnedEarly = false ∧
      r.writes.map scatterEvent = (rowWrites rows offsets gid).map payloadEvent := by
  let packet := PackWire.wordView src
  obtain ⟨n, head, nVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_header_word accepted)
  have branch : gid < n ↔ gid.toNat < rows.length := by rw [UInt32.lt_iff_toNat_lt, nVal]
  by_cases active : gid.toNat < rows.length
  · let words := rows.getD gid.toNat []
    obtain ⟨start, startCell, startVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_descriptor_span accepted _ active).1
    obtain ⟨len, widthCell, lenVal⟩ := Option.map_eq_some_iff.mp (PackWire.decode_descriptor_length_word accepted _ active)
    have nr : n.toNat ≤ PackWire.maxRows := nVal.symm ▸ PackWire.decode_row_count_le accepted
    have gr := Nat.lt_of_lt_of_le active (PackWire.decode_row_count_le accepted)
    have sr : packet[(3 + 2*gid : UInt32).toNat]? = some start := by
      rw [descriptor3 gid (Nat.le_of_lt gr)]
      exact startCell
    have width : packet[(4 + 2*gid : UInt32).toNat]? = some len := by
      rw [CountTarget.descriptor_word_address gid gr]
      exact widthCell
    have oi : gid.toNat < offsets.size := by omega
    let off := offsets[gid.toNat]'oi
    have offSlot : offsets[gid.toNat]? = some off := Array.getElem?_eq_getElem oi
    have offVal : off.toNat = CountTarget.memory offsets gid.toNat := by simp [CountTarget.memory, offSlot]
    have bound := scatter_end rows offsets (ScatterTarget.scanned_starts rows offsets scanned) gid.toNat active
    have total : (StaticPack.counts rows).sum ≤ 1024 := PackWire.decode_total_bound accepted
    have wordLimit : words.length ≤ 1024 := by
      change (rows.getD gid.toNat []).length ≤ 1024
      omega
    have widthLimit : len.toNat ≤ 1024 := lenVal.symm ▸ wordLimit
    have hbytes : src.size ≤ 5644 := by
      by_cases over : src.size > PackWire.maxPacketBytes
      · simp [PackWire.decode, over] at accepted
      · exact Nat.le_of_not_gt over
    have extent := PackWire.decode_extent accepted
    have span := (PackWire.decode_descriptor_span accepted _ active).2
    let absolute := 3 + 2*n + start
    have fits : 3 + 2*rows.length + (PackWire.descriptorAt src gid.toNat).1 < 4294967296 := by omega
    have absNat : absolute.toNat = 3 + 2*rows.length + (PackWire.descriptorAt src gid.toNat).1 := by
      change ((3 + 2*n) + start : UInt32).toNat = _
      rw [UInt32.toNat_add, descriptor3 n nr, nVal, startVal, Nat.mod_eq_of_lt fits]
    obtain ⟨out, ran, size, mem, trace⟩ := copy_surface packet offsets gid absolute off len words 0 ⟨prior, #[]⟩
      (by rw [Nat.zero_add]; exact lenVal.symm)
      (by rw [absNat]; change _ < 4294967296; omega)
      (by rw [offVal]; change _ + 0 + (rows.getD gid.toNat []).length < 4294967296; omega)
      (by rw [offVal]; change _ + 0 + (rows.getD gid.toNat []).length ≤ prior.size; omega)
      (by intro j hj; rw [absNat, Nat.add_zero]; exact (PackWire.decode_source_word accepted _ active j hj).2)
    have zero : UInt32.ofNat 0 = (0 : UInt32) := by decide
    rw [zero] at ran
    obtain ⟨target, targetRun, targetSize, targetMem⟩ :=
      ScatterTarget.decoded_scatter_lane accepted offsets prior gid offsetCap scanned room
    rw [if_pos active] at targetMem
    rw [Nat.add_zero, offVal] at mem trace
    have same : target = out.dst := payload_ext (targetSize.trans size.symm) (targetMem.trans mem.symm)
    rw [same] at targetRun
    refine ⟨⟨out.dst, out.writes.toList, false⟩, ?_, targetRun, size, rfl, ?_⟩
    · rw [scatter_header packet offsets prior gid n head, if_pos (branch.mpr active)]
      rw [scatter_active packet offsets prior gid n start off len head sr offSlot width widthLimit]
      rw [lenVal, ran] <;> rfl
    · rw [rowWrites, if_pos active]
      exact trace
  · have inactive : ¬ gid < n := fun h => active (branch.mp h)
    refine ⟨⟨prior, [], false⟩, inactive_scatter_text packet offsets prior gid n head inactive,
      ScatterTarget.inactive_lane _ gid n prior head inactive, rfl, rfl, ?_⟩
    rw [rowWrites, if_neg active] <;> rfl

def payloadWrite (w : Surface.Write) : Nat × UInt32 := (w.address.toNat, w.value)

/-- Kind: trace observation.
Says: projecting away the known storage binding recovers exactly the original
address/value writes, preserving their multiplicity and order.
Does not say: other bindings may alias this output. -/
private theorem project_payload (actual : List Surface.Write) (row : List (Nat × UInt32))
    (h : actual.map scatterEvent = row.map payloadEvent) : actual.map payloadWrite = row := by
  have p := congrArg (List.map (fun e : (Nat × Nat) × (Nat × UInt32) => e.2)) h
  change actual.map (fun w : Surface.Write => (w.address.toNat, w.value)) = row
  simpa [List.map_map, scatterEvent, payloadEvent, Function.comp_def] using p

/-- Kind: dynamic write-footprint disjointness.
Says: the actual chronological store events of two different parsed shader lanes
have disjoint word addresses, even when run from different sufficiently large prior
payloads. Padded lanes and zero-width intervals need no uniqueness assumption on offsets.
Does not say: that arbitrary device executions are modeled by whole-lane permutations. -/
theorem scatter_text_traces_disjoint {src : ByteArray} {rows : StaticPack.Rows} (accepted : PackWire.decode src = .ok rows)
    (offsets leftPrior rightPrior : Array UInt32) (i j : UInt32) (different : i ≠ j)
    (offsetCap : rows.length + 1 ≤ offsets.size)
    (scanned : DSL.view (rows.length + 1) (CountTarget.memory offsets) = (StaticPack.counts rows).scanl (· + ·) 0)
    (leftRoom : (StaticPack.counts rows).sum ≤ leftPrior.size) (rightRoom : (StaticPack.counts rows).sum ≤ rightPrior.size)
    (left right : ScanSurface.Outcome)
    (leftRun : ScatterSurface.runText scatterText.toUTF8 (PackWire.wordView src) offsets leftPrior i = some left)
    (rightRun : ScatterSurface.runText scatterText.toUTF8 (PackWire.wordView src) offsets rightPrior j = some right) :
    Disjoint (left.writes.map payloadWrite) (right.writes.map payloadWrite) := by
  obtain ⟨a, ha, _, _, _, ta⟩ := decoded_scatter_text_lane accepted offsets leftPrior i offsetCap scanned leftRoom
  obtain ⟨b, hb, _, _, _, tb⟩ := decoded_scatter_text_lane accepted offsets rightPrior j offsetCap scanned rightRoom
  have ea : a = left := Option.some.inj (ha.symm.trans leftRun)
  have eb : b = right := Option.some.inj (hb.symm.trans rightRun)
  subst a
  subst b
  rw [project_payload _ _ ta, project_payload _ _ tb]
  by_cases ai : i.toNat < rows.length
  · by_cases aj : j.toNat < rows.length
    · have distinctNat : i.toNat ≠ j.toNat := fun h => different (by simpa using congrArg UInt32.ofNat h)
      simp only [rowWrites, if_pos ai, if_pos aj]
      exact DSL.scatter_raceFree rows _ (ScatterTarget.scanned_starts rows offsets scanned) _ _ ai aj distinctNat
    · simp [rowWrites, ai, aj, Disjoint, keys]
  · simp [rowWrites, ai, Disjoint, keys]

#print axioms scatter_lex_tokens
#print axioms parse_scatter_text
#print axioms scatter_text_launch
#print axioms scatter_header
#print axioms inactive_scatter_text
#print axioms scatter_active
#print axioms copy_address
#print axioms copy_surface
#print axioms scatter_end
#print axioms descriptor3
#print axioms payload_ext
#print axioms decoded_scatter_text_lane
#print axioms project_payload
#print axioms scatter_text_traces_disjoint

end L4Factoidal.Paralliverse.WGSL
