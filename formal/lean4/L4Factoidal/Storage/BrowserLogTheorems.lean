/-
L4Factoidal.Storage.BrowserLogTheorems — the properties of the browser update
log (`Storage.BrowserLog`, https://github.com/danbri/factoidal/issues/728)
that its host relies on.

1. The DLB1 record codec of `Storage.DeltaLog` round-trips, with arbitrary
   bytes after the record (`parseDeltaBatch_serializeDeltaBatch?`). The
   proof goes up the layers of the format: triple, graph name, entry
   payload, DLE1 entry frame, entry list, batch body, DLB1 batch frame. The
   term and string layers are `TermCodecTheorems`.
2. The loop decoders equal the store's decoders: `parseBatch_eq`
   (`parseDeltaBatch`) and `decode_eq_replay` (`replayDeltaBatches`).
3. `decode_encodeLog`: decode inverts encode, for every list of batches the
   encoder admits.
4. `decode_encodeLog_torn`: when the last record of a log does not verify,
   the log decodes to exactly the batches before it, and the decoder reports
   the bytes of that record. `parseDeltaBatch_take` shows that a record cut
   short at any byte does not verify, so `decode_encodeLog_cut` covers every
   torn write. `parseDeltaBatch_body_byte` shows that a record with one
   body byte changed after the write does not verify (the checksum), and
   `decode_encodeLog_byte` gives the decode of such a log.
5. `merge_encodeLog`: a merge of a log equals applying its batches one by one,
   in order; `merge_encodeLog_torn` the same for a log whose last record does
   not verify; `merge_encodeLog_append` gives an incremental merge. These are
   about the unchecked `merge`.
6. `parseLog_header_append`: a browser log after the eight-byte DLOG header is
   a Shardborough `deltas.dlog` with the same batches.
7. The rule of https://github.com/danbri/factoidal/issues/843: what follows
   the records that verify (`Storage.classifyTail`). Every cut of the last
   record, and a complete last record whose checksum fails, is torn, and
   `mergeChecked` merges the batches before it (`mergeChecked_encodeLog_cut`,
   `mergeChecked_encodeLog_byte`). A record that fails its checksum with bytes
   after it, and a record whose checksum verifies and whose body does not
   decode, stop the merge with an error (`mergeChecked_damaged`,
   `mergeChecked_undecodable`). `parseLogChecked_header_append`: the native
   readers decide the same.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.BrowserLog
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.BrowserLog

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## 1. The record codec, layer by layer -/

theorem parseTriple_serializeTriple? (t : Triple) (bs rest : List UInt8)
    (h : serializeTriple? t = some bs) :
    parseTriple (bs ++ rest) = some (t, rest) := by
  rw [serializeTriple?] at h
  cases hs : serializeSubject? t.s with
  | none => simp [hs, bind, Option.bind] at h
  | some sb =>
  cases hp : serializeLString? t.p.val with
  | none => simp [hs, hp, bind, Option.bind] at h
  | some pb =>
  cases ho : serializeTerm? t.o with
  | none => simp [hs, hp, ho, bind, Option.bind] at h
  | some ob =>
  simp only [hs, hp, ho, bind, Option.bind, Option.some.injEq] at h
  subst h
  have e : sb ++ pb ++ ob ++ rest = sb ++ (pb ++ (ob ++ rest)) := by
    simp [List.append_assoc]
  rw [e, parseTriple]
  simp only [bind, Option.bind,
    parseSubject_serializeSubject? t.s sb _ hs,
    parseLString_serializeLString? t.p.val pb _ hp,
    dif_pos t.p.property,
    parseTerm_serializeTerm?_checked t.o ob rest ho]

theorem parseGraphOpt_serializeGraphOpt? (g : Option Iri) (bs rest : List UInt8)
    (h : serializeGraphOpt? g = some bs) :
    parseGraphOpt (bs ++ rest) = some (g, rest) := by
  cases g with
  | none =>
      simp only [serializeGraphOpt?, Option.some.injEq] at h
      subst h
      rfl
  | some i =>
      rw [serializeGraphOpt?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseGraphOpt]
      simp [bind, Option.bind, parseU8, parseLString_serializeLString? i sb rest hsb]

theorem parseDeltaEntryPayload_serializeDeltaEntryPayload? (e : DeltaEntry)
    (bs rest : List UInt8) (h : serializeDeltaEntryPayload? e = some bs) :
    parseDeltaEntryPayload (bs ++ rest) = some (e, rest) := by
  cases e with
  | add t g =>
      rw [serializeDeltaEntryPayload?] at h
      cases ht : serializeTriple? t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
      cases hg : serializeGraphOpt? g with
      | none => simp [ht, hg, bind, Option.bind] at h
      | some gb =>
      simp only [ht, hg, bind, Option.bind, Option.some.injEq] at h
      subst h
      rw [List.cons_append, List.append_assoc, parseDeltaEntryPayload]
      simp [bind, Option.bind, parseU8, deTagAdd,
        parseTriple_serializeTriple? t tb _ ht,
        parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | remove t g =>
      rw [serializeDeltaEntryPayload?] at h
      cases ht : serializeTriple? t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
      cases hg : serializeGraphOpt? g with
      | none => simp [ht, hg, bind, Option.bind] at h
      | some gb =>
      simp only [ht, hg, bind, Option.bind, Option.some.injEq] at h
      subst h
      rw [List.cons_append, List.append_assoc, parseDeltaEntryPayload]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove,
        parseTriple_serializeTriple? t tb _ ht,
        parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | clear g =>
      rw [serializeDeltaEntryPayload?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayload]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear,
        parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | drop g =>
      rw [serializeDeltaEntryPayload?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayload]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear, deTagDrop,
        parseLString_serializeLString? g gb rest hg]
  | create g =>
      rw [serializeDeltaEntryPayload?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayload]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear, deTagDrop,
        deTagCreate, parseLString_serializeLString? g gb rest hg]

theorem parseFramedDeltaEntry_serializeFramedDeltaEntry? (e : DeltaEntry)
    (bs rest : List UInt8) (h : serializeFramedDeltaEntry? e = some bs) :
    parseFramedDeltaEntry (bs ++ rest) = some (e, rest) := by
  rw [serializeFramedDeltaEntry?] at h
  cases hp : serializeDeltaEntryPayload? e with
  | none => simp [hp, bind, Option.bind] at h
  | some pb =>
  simp only [hp, bind, Option.bind] at h
  have hpay := parseDeltaEntryPayload_serializeDeltaEntryPayload? e pb [] hp
  rw [List.append_nil] at hpay
  rw [parseFramedDeltaEntry]
  simp [bind, Option.bind, parseEntry_frameEntry?_append pb bs rest h, hpay]

/-- The entry list: the frames of the entries, concatenated, read back by
`parseNFramedDeltaEntries` with the count of entries. -/
theorem parseNFramedDeltaEntries_flatten (ops : List DeltaEntry)
    (frames : List (List UInt8)) (rest : List UInt8)
    (h : ops.mapM serializeFramedDeltaEntry? = some frames) :
    parseNFramedDeltaEntries ops.length (frames.flatten ++ rest) = some (ops, rest) := by
  induction ops generalizing frames with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      rfl
  | cons e es ih =>
      rw [List.mapM_cons] at h
      cases he : serializeFramedDeltaEntry? e with
      | none => simp [he, bind, Option.bind] at h
      | some eb =>
      cases hes : es.mapM serializeFramedDeltaEntry? with
      | none => simp [he, hes, bind, Option.bind] at h
      | some ebs =>
      simp only [he, hes, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      rw [List.length_cons, List.flatten_cons, List.append_assoc, parseNFramedDeltaEntries]
      simp [bind, Option.bind,
        parseFramedDeltaEntry_serializeFramedDeltaEntry? e eb _ he, ih ebs hes]

/-- A u64 field read at `pos` reads the bytes from `pos` on. -/
theorem readU64LE_drop (bs : List UInt8) (pos : Nat) :
    readU64LE bs pos = readU64LE (bs.drop pos) 0 := by
  simp [readU64LE, readU32LE, List.drop_drop]

theorem natFitsU64_toNat {n : Nat} (h : natFitsU64 n = true) : n.toUInt64.toNat = n := by
  simpa [natFitsU64] using h

/-- The batch body: seq, epoch, entry count, entries. -/
theorem parseDeltaBatchBody_serializeDeltaBatchBody? (b : DeltaBatch) (body : List UInt8)
    (h : serializeDeltaBatchBody? b = some body) :
    parseDeltaBatchBody body = some b := by
  rw [serializeDeltaBatchBody?] at h
  by_cases hb : (!natFitsU64 b.seq || !natFitsU64 b.epoch || b.ops.length >= two32) = true
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or,
    Bool.not_eq_false] at hb
  obtain ⟨⟨hseq, hepoch⟩, hlen⟩ := hb
  cases hes : b.ops.mapM serializeFramedDeltaEntry? with
  | none => simp [hes, bind, Option.bind] at h
  | some frames =>
  simp only [hes, bind, Option.bind, Option.some.injEq] at h
  subst h
  have hlt : b.ops.length < UInt32.size := by
    have : ¬ b.ops.length ≥ two32 := hlen
    rw [two32_eq_uint32Size] at this
    omega
  have hseqB : readU64LE (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
      writeU32LE (UInt32.ofNat b.ops.length) ++ frames.flatten) 0 = some b.seq.toUInt64 := by
    rw [List.append_assoc, List.append_assoc]
    exact readU64LE_writeU64LE_append _ _
  have hepochB : readU64LE (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
      writeU32LE (UInt32.ofNat b.ops.length) ++ frames.flatten) 8 = some b.epoch.toUInt64 := by
    rw [readU64LE_drop, List.append_assoc, List.append_assoc]
    have h8 : (writeU64LE b.seq.toUInt64).length = 8 := writeU64LE_length _
    rw [← h8, List.drop_left]
    exact readU64LE_writeU64LE_append _ _
  have hcountB : readU32LE (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
      writeU32LE (UInt32.ofNat b.ops.length) ++ frames.flatten) 16 =
        some (UInt32.ofNat b.ops.length) := by
    have h16 : (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64).length = 16 := by
      simp
    rw [← h16]
    exact readU32LE_append_writeU32LE _ _ _
  have hdrop : (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
      writeU32LE (UInt32.ofNat b.ops.length) ++ frames.flatten).drop 20 = frames.flatten := by
    have h20 : (writeU64LE b.seq.toUInt64 ++ writeU64LE b.epoch.toUInt64 ++
        writeU32LE (UInt32.ofNat b.ops.length)).length = 20 := by simp
    rw [← h20, List.drop_left]
  have hents := parseNFramedDeltaEntries_flatten b.ops frames [] hes
  rw [List.append_nil] at hents
  rw [parseDeltaBatchBody]
  simp only [bind, Option.bind, hseqB, hepochB, hcountB, hdrop,
    u32_toNat_ofNat_of_lt hlt, hents, List.isEmpty_nil, if_true,
    natFitsU64_toNat hseq, natFitsU64_toNat hepoch]

/-- The DLB1 record: the frame of a batch the encoder admits reads back as the
batch, with the bytes after the frame untouched. -/
theorem parseDeltaBatch_serializeDeltaBatch? (b : DeltaBatch) (frame rest : List UInt8)
    (h : serializeDeltaBatch? b = some frame) :
    parseDeltaBatch (frame ++ rest) = some (b, rest) := by
  rw [serializeDeltaBatch?] at h
  cases hbody : serializeDeltaBatchBody? b with
  | none => simp [hbody, bind, Option.bind] at h
  | some body =>
  simp only [hbody, bind, Option.bind] at h
  by_cases hlen : body.length ≥ two32
  · rw [if_pos hlen] at h; cases h
  rw [if_neg hlen, Option.some.injEq] at h
  subst h
  have hlt : body.length < UInt32.size := by
    rw [two32_eq_uint32Size] at hlen; omega
  have hb := parseDeltaBatchBody_serializeDeltaBatchBody? b body hbody
  -- The frame, regrouped as header ++ (body ++ checksum ++ rest).
  have hgroup : writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest =
      (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat body.length)) ++
        (body ++ writeU32LE (simpleChecksum body) ++ rest) := by
    simp [List.append_assoc]
  have hmagic : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest) 0 =
      some deltaBatchMagic := by
    simp only [List.append_assoc]
    exact readU32LE_writeU32LE_append _ _
  have hver : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest) 4 =
      some deltaBatchVersion := by
    have h4 : (writeU32LE deltaBatchMagic).length = 4 := writeU32LE_length _
    have := readU32LE_append_writeU32LE (writeU32LE deltaBatchMagic) deltaBatchVersion
      (writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest)
    rw [h4] at this
    simpa [List.append_assoc] using this
  have hlenB : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest) 8 =
      some (UInt32.ofNat body.length) := by
    have h8 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion).length = 8 := by simp
    have := readU32LE_append_writeU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion)
      (UInt32.ofNat body.length) (body ++ writeU32LE (simpleChecksum body) ++ rest)
    rw [h8] at this
    simpa [List.append_assoc] using this
  have hdrop12 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ rest).drop 12 =
      body ++ writeU32LE (simpleChecksum body) ++ rest := by
    rw [hgroup]
    have h12 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat body.length)).length = 12 := by simp
    rw [← h12, List.drop_left]
  have htake : (body ++ writeU32LE (simpleChecksum body) ++ rest).take body.length = body := by
    rw [List.append_assoc, List.take_left]
  have hchk : readU32LE (body ++ writeU32LE (simpleChecksum body) ++ rest) body.length =
      some (simpleChecksum body) := readU32LE_append_writeU32LE _ _ _
  have hafter : ((body ++ writeU32LE (simpleChecksum body) ++ rest).drop body.length).drop 4 = rest := by
    rw [List.append_assoc, List.drop_left]
    simp [writeU32LE]
  rw [parseDeltaBatch]
  simp only [bind, Option.bind, hmagic, bne_self_eq_false, Bool.false_eq_true, if_false,
    hver, hlenB, hdrop12, u32_toNat_ofNat_of_lt hlt, htake, hchk, hb, hafter]

/-! ## 2. The loop decoders equal the store's decoders -/

theorem entriesLoop_eq (n : Nat) (bs : List UInt8) (acc : List DeltaEntry) :
    entriesLoop n bs acc =
      (parseNFramedDeltaEntries n bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction n generalizing bs acc with
  | zero => simp [entriesLoop, parseNFramedDeltaEntries]
  | succ n ih =>
      rw [entriesLoop, parseNFramedDeltaEntries]
      cases h : parseFramedDeltaEntry bs with
      | none => simp [bind, Option.bind]
      | some p =>
          obtain ⟨e, rest⟩ := p
          simp only [ih, bind, Option.bind]
          cases parseNFramedDeltaEntries n rest with
          | none => rfl
          | some q => simp

theorem parseBody_eq : parseBody = parseDeltaBatchBody := by
  funext bs
  unfold parseBody parseDeltaBatchBody
  simp only [entriesLoop_eq, List.reverse_nil, List.nil_append]
  cases readU64LE bs 0 <;> cases readU64LE bs 8 <;> cases readU32LE bs 16 <;>
    simp only [bind, Option.bind] <;>
    cases parseNFramedDeltaEntries _ (bs.drop 20) <;> rfl

theorem parseBatch_eq : parseBatch = parseDeltaBatch := by
  funext bs
  unfold parseBatch parseDeltaBatch
  rw [parseBody_eq]

/-- The decode loop, against the store's replay loop. -/
theorem decodeGo_eq_replay (fuel : Nat) (bs : List UInt8) (acc : List DeltaBatch) :
    decodeGo fuel bs acc =
      { batches := (replayDeltaBatches.go fuel bs acc).1.reverse,
        rest := (replayDeltaBatches.go fuel bs acc).2 } := by
  induction fuel generalizing bs acc with
  | zero => rfl
  | succ fuel ih =>
      cases bs with
      | nil => rfl
      | cons b bs' =>
          rw [decodeGo, replayDeltaBatches.go, parseBatch_eq]
          simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
          cases parseDeltaBatch (b :: bs') with
          | none => rfl
          | some p => exact ih p.2 (p.1 :: acc)

/-- The browser decoder answers what the store's `replayDeltaBatches` answers on
the same bytes. -/
theorem decode_eq_replay (bs : List UInt8) :
    decode bs = { batches := (replayDeltaBatches bs).1, rest := (replayDeltaBatches bs).2 } := by
  rw [decode, decodeGo_eq_replay]
  rfl

/-! ## 3. What a record that verifies consumes -/

/-- A u32 read succeeds only with four bytes at the position. -/
theorem readU32LE_some_le {bs : List UInt8} {pos : Nat} {x : UInt32}
    (h : readU32LE bs pos = some x) : pos + 4 ≤ bs.length := by
  unfold readU32LE at h
  match hd : bs.drop pos with
  | _ :: _ :: _ :: _ :: t =>
      have hl := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hl
      omega
  | [] => rw [hd] at h; cases h
  | [_] => rw [hd] at h; cases h
  | [_, _] => rw [hd] at h; cases h
  | [_, _, _] => rw [hd] at h; cases h

/-- A u32 read inside the first `m` bytes does not see a cut after them. -/
theorem readU32LE_take (bs : List UInt8) (pos m : Nat) (h : pos + 4 ≤ m) :
    readU32LE (bs.take m) pos = readU32LE bs pos := by
  unfold readU32LE
  rw [List.drop_take]
  have hm : m - pos = (m - pos - 4) + 4 := by omega
  rw [hm]
  match bs.drop pos with
  | b0 :: b1 :: b2 :: b3 :: t => simp [List.take_succ_cons]
  | [] => simp
  | [_] => simp
  | [_, _] => simp
  | [_, _, _] => simp

/-- A record that verifies is its 12-byte header, the body the length field
names, and the 4-byte checksum: the decoder moves past exactly that many
bytes. -/
theorem parseDeltaBatch_some_length {bs rest : List UInt8} {b : DeltaBatch}
    (h : parseDeltaBatch bs = some (b, rest)) :
    ∃ len : UInt32, readU32LE bs 8 = some len ∧
      bs.length = 16 + len.toNat + rest.length := by
  unfold parseDeltaBatch at h
  cases hm : readU32LE bs 0 with
  | none => simp [hm, bind, Option.bind] at h
  | some magic =>
  simp only [hm, bind, Option.bind] at h
  split at h
  · cases h
  cases hv : readU32LE bs 4 with
  | none => simp [hv] at h
  | some ver =>
  simp only [hv] at h
  split at h
  · cases h
  cases hl : readU32LE bs 8 with
  | none => simp [hl] at h
  | some len =>
  simp only [hl] at h
  split at h
  · cases h
  cases hc : readU32LE (bs.drop 12) len.toNat with
  | none => simp [hc] at h
  | some chk =>
  simp only [hc] at h
  split at h
  · cases h
  cases hbody : parseDeltaBatchBody ((bs.drop 12).take len.toNat) with
  | none => simp [hbody] at h
  | some b' =>
  simp only [hbody, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hrest⟩ := h
  refine ⟨len, rfl, ?_⟩
  have hge := readU32LE_some_le hc
  simp only [List.length_drop] at hge
  rw [← hrest]
  simp only [List.length_drop]
  omega

/-- The decoder moves forward: a record that verifies is at least 16 bytes. -/
theorem parseDeltaBatch_shrinks {bs rest : List UInt8} {b : DeltaBatch}
    (h : parseDeltaBatch bs = some (b, rest)) : rest.length + 16 ≤ bs.length := by
  obtain ⟨len, -, hl⟩ := parseDeltaBatch_some_length h
  omega

/-- A record cut short at any byte does not verify: the length field asks for
more bytes than are left. This is every torn write of one record. -/
theorem parseDeltaBatch_take (b : DeltaBatch) (frame : List UInt8) (m : Nat)
    (h : serializeDeltaBatch? b = some frame) (hm : m < frame.length) :
    parseDeltaBatch (frame.take m) = none := by
  cases hp : parseDeltaBatch (frame.take m) with
  | none => rfl
  | some p =>
  obtain ⟨b', r⟩ := p
  obtain ⟨len, hlen, hl⟩ := parseDeltaBatch_some_length hp
  have hfull := parseDeltaBatch_serializeDeltaBatch? b frame [] h
  rw [List.append_nil] at hfull
  obtain ⟨len', hlen', hl'⟩ := parseDeltaBatch_some_length hfull
  have h12 : 8 + 4 ≤ m := by
    have := readU32LE_some_le hlen
    simp only [List.length_take] at this
    omega
  rw [readU32LE_take frame 8 m h12, hlen'] at hlen
  cases hlen
  simp only [List.length_take, List.length_nil] at hl hl'
  omega

/-! ### The checksum detects one changed body byte -/

private theorem foldl_sum (a : UInt32) (l : List UInt8) :
    l.foldl (fun acc b => acc + b.toUInt32) a =
      a + l.foldl (fun acc b => acc + b.toUInt32) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (a + x.toUInt32), ih (0 + x.toUInt32)]
      simp [UInt32.add_assoc]

/-- The checksum of bytes with one byte in the middle. -/
theorem simpleChecksum_middle (p q : List UInt8) (x : UInt8) :
    simpleChecksum (p ++ x :: q) = simpleChecksum p + x.toUInt32 + simpleChecksum q := by
  unfold simpleChecksum
  rw [List.foldl_append, List.foldl_cons, foldl_sum]

/-- Two byte sequences that differ in one byte have different checksums: the
sum moves by the difference of the two bytes, which is not 0 modulo 2^32. -/
theorem simpleChecksum_ne_of_byte (p q : List UInt8) (x y : UInt8) (hxy : x ≠ y) :
    simpleChecksum (p ++ x :: q) ≠ simpleChecksum (p ++ y :: q) := by
  intro h
  rw [simpleChecksum_middle, simpleChecksum_middle] at h
  have k : x.toUInt32 + (simpleChecksum p + simpleChecksum q) =
      y.toUInt32 + (simpleChecksum p + simpleChecksum q) := by
    have e1 : simpleChecksum p + x.toUInt32 + simpleChecksum q =
        x.toUInt32 + (simpleChecksum p + simpleChecksum q) := by
      rw [UInt32.add_comm (simpleChecksum p) x.toUInt32, UInt32.add_assoc]
    have e2 : simpleChecksum p + y.toUInt32 + simpleChecksum q =
        y.toUInt32 + (simpleChecksum p + simpleChecksum q) := by
      rw [UInt32.add_comm (simpleChecksum p) y.toUInt32, UInt32.add_assoc]
    rw [← e1, ← e2, h]
  have k2 := congrArg (fun z => z - (simpleChecksum p + simpleChecksum q)) k
  simp only [UInt32.add_sub_cancel] at k2
  exact hxy (UInt8.toUInt32_inj.mp k2)

/-- A DLB1 record with one body byte changed after the write does not verify:
the length and checksum fields are those of the written body `p ++ x :: q`,
the body bytes read are `p ++ y :: q`, and the sums differ. -/
theorem parseDeltaBatch_body_byte (p q rest : List UInt8) (x y : UInt8) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) :
    parseDeltaBatch (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++ (p ++ y :: q) ++
      writeU32LE (simpleChecksum (p ++ x :: q)) ++ rest) = none := by
  -- `body` is what was written; `body'` is what is read back.
  generalize hb : p ++ x :: q = body at hlen ⊢
  have hlen' : (p ++ y :: q).length = body.length := by rw [← hb]; simp
  have hne : simpleChecksum body ≠ simpleChecksum (p ++ y :: q) := by
    rw [← hb]; exact simpleChecksum_ne_of_byte p q x y hxy
  generalize hb' : p ++ y :: q = body' at hlen' hne ⊢
  have hmagic : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest) 0 =
      some deltaBatchMagic := by
    simp only [List.append_assoc]
    exact readU32LE_writeU32LE_append _ _
  have hver : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest) 4 =
      some deltaBatchVersion := by
    have h4 : (writeU32LE deltaBatchMagic).length = 4 := writeU32LE_length _
    have := readU32LE_append_writeU32LE (writeU32LE deltaBatchMagic) deltaBatchVersion
      (writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest)
    rw [h4] at this
    simpa [List.append_assoc] using this
  have hlenB : readU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest) 8 =
      some (UInt32.ofNat body.length) := by
    have h8 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion).length = 8 := by simp
    have := readU32LE_append_writeU32LE (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion)
      (UInt32.ofNat body.length) (body' ++ writeU32LE (simpleChecksum body) ++ rest)
    rw [h8] at this
    simpa [List.append_assoc] using this
  have hdrop12 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest).drop 12 =
      body' ++ writeU32LE (simpleChecksum body) ++ rest := by
    have hgroup : writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat body.length) ++ body' ++ writeU32LE (simpleChecksum body) ++ rest =
        (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
          writeU32LE (UInt32.ofNat body.length)) ++
          (body' ++ writeU32LE (simpleChecksum body) ++ rest) := by
      simp [List.append_assoc]
    rw [hgroup]
    have h12 : (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat body.length)).length = 12 := by simp
    rw [← h12, List.drop_left]
  have htake : (body' ++ writeU32LE (simpleChecksum body) ++ rest).take body.length = body' := by
    rw [← hlen', List.append_assoc, List.take_left]
  have hchk : readU32LE (body' ++ writeU32LE (simpleChecksum body) ++ rest) body.length =
      some (simpleChecksum body) := by
    rw [← hlen']; exact readU32LE_append_writeU32LE _ _ _
  have hne' : (simpleChecksum body != simpleChecksum body') = true := by
    simpa [bne_iff_ne] using hne
  rw [parseDeltaBatch]
  simp only [bind, Option.bind, hmagic, if_false,
    hver, hlenB, hdrop12, u32_toNat_ofNat_of_lt hlen, htake, List.length_take,
    hchk, hne', if_true, ite_self]

/-! ## 4. Decode inverts encode; a log with a torn last record -/

/-- Any fuel at least the byte length gives the same decode. -/
theorem decodeGo_fuel (f1 f2 : Nat) (bs : List UInt8) (acc : List DeltaBatch)
    (h1 : bs.length ≤ f1) (h2 : bs.length ≤ f2) :
    decodeGo f1 bs acc = decodeGo f2 bs acc := by
  induction f1 generalizing f2 bs acc with
  | zero =>
      have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      cases f2 <;> rfl
  | succ k ih =>
      cases f2 with
      | zero =>
          have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst this
          rfl
      | succ m =>
          cases bs with
          | nil => rfl
          | cons b bs' =>
              rw [decodeGo, decodeGo]
              cases hp : parseBatch (b :: bs') with
              | none => rfl
              | some p =>
                  obtain ⟨batch, rest⟩ := p
                  rw [parseBatch_eq] at hp
                  have hs := parseDeltaBatch_shrinks hp
                  simp only [List.length_cons] at h1 h2 hs
                  exact ih m rest (batch :: acc) (by omega) (by omega)

/-- The accumulator only prefixes the batches. -/
theorem decodeGo_acc (fuel : Nat) (bs : List UInt8) (acc : List DeltaBatch) :
    decodeGo fuel bs acc =
      { batches := acc.reverse ++ (decodeGo fuel bs []).batches,
        rest := (decodeGo fuel bs []).rest } := by
  induction fuel generalizing bs acc with
  | zero => simp [decodeGo]
  | succ k ih =>
      cases bs with
      | nil => simp [decodeGo]
      | cons b bs' =>
          rw [decodeGo, decodeGo]
          cases parseBatch (b :: bs') with
          | none => simp
          | some p =>
              obtain ⟨batch, rest⟩ := p
              simp only
              rw [ih rest (batch :: acc), ih rest [batch]]
              simp

/-- A record the encoder writes is at least 16 bytes long. -/
theorem encodeBatch?_length {b : DeltaBatch} {frame : List UInt8}
    (h : encodeBatch? b = some frame) : 16 ≤ frame.length := by
  have hp := parseDeltaBatch_serializeDeltaBatch? b frame [] h
  rw [List.append_nil] at hp
  have := parseDeltaBatch_shrinks hp
  simpa using this

theorem decodeGo_flatten (bs : List DeltaBatch) (frames : List (List UInt8))
    (rest : List UInt8) (h : bs.mapM encodeBatch? = some frames) (acc : List DeltaBatch)
    (fuel : Nat) (hf : (frames.flatten ++ rest).length ≤ fuel) :
    decodeGo fuel (frames.flatten ++ rest) acc = decodeGo rest.length rest (bs.reverse ++ acc) := by
  induction bs generalizing frames acc fuel with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      simp only [List.flatten_nil, List.nil_append, List.reverse_nil] at hf ⊢
      exact decodeGo_fuel fuel rest.length rest acc hf (Nat.le_refl _)
  | cons b bs ih =>
      rw [List.mapM_cons] at h
      cases hb : encodeBatch? b with
      | none => simp [hb, bind, Option.bind] at h
      | some frame =>
      cases hbs : bs.mapM encodeBatch? with
      | none => simp [hb, hbs, bind, Option.bind] at h
      | some frames' =>
      simp only [hb, hbs, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      have h16 := encodeBatch?_length hb
      rw [List.flatten_cons, List.append_assoc] at hf ⊢
      simp only [List.length_append] at hf
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hparse := parseDeltaBatch_serializeDeltaBatch? b frame (frames'.flatten ++ rest) hb
      obtain ⟨x, xs, hx⟩ : ∃ x xs, frame ++ (frames'.flatten ++ rest) = x :: xs := by
        cases frame with
        | nil => simp at h16
        | cons y ys => exact ⟨y, ys ++ (frames'.flatten ++ rest), rfl⟩
      rw [hx, decodeGo, parseBatch_eq, ← hx, hparse]
      simp only
      rw [ih frames' hbs (b :: acc) k (by simp only [List.length_append]; omega)]
      simp [List.reverse_cons, List.append_assoc]

/-- Decode of a log followed by more bytes: the log's batches, then whatever the
decode of the bytes after it finds. -/
theorem decode_encodeLog_append (bs : List DeltaBatch) (bytes rest : List UInt8)
    (h : encodeLog? bs = some bytes) :
    decode (bytes ++ rest) =
      { batches := bs ++ (decode rest).batches, rest := (decode rest).rest } := by
  unfold encodeLog? at h
  cases hm : bs.mapM encodeBatch? with
  | none => simp [hm] at h
  | some frames =>
  simp only [hm, Option.map_some, Option.some.injEq] at h
  subst h
  unfold decode
  rw [decodeGo_flatten bs frames rest hm [] _ (Nat.le_refl _), decodeGo_acc]
  simp

/-- Decode inverts encode: the log of a list of batches the encoder admits
decodes to exactly those batches, and nothing is left over. -/
theorem decode_encodeLog (bs : List DeltaBatch) (bytes : List UInt8)
    (h : encodeLog? bs = some bytes) :
    decode bytes = { batches := bs, rest := [] } := by
  have happ := decode_encodeLog_append bs bytes [] h
  rw [List.append_nil] at happ
  rw [happ]
  simp [decode, decodeGo]

/-- One record: decode inverts encode for every batch the encoder admits. -/
theorem decode_encodeBatch (b : DeltaBatch) (frame : List UInt8)
    (h : encodeBatch? b = some frame) :
    decode frame = { batches := [b], rest := [] } :=
  decode_encodeLog [b] frame (by simp [encodeLog?, h])

/-- Bytes whose first record does not verify decode to no batch; the decoder
reports all of them. -/
theorem decode_of_parseDeltaBatch_none (torn : List UInt8)
    (h : parseDeltaBatch torn = none) :
    decode torn = { batches := [], rest := torn } := by
  cases torn with
  | nil => rfl
  | cons x xs =>
      unfold decode
      rw [List.length_cons, decodeGo, parseBatch_eq, h]
      rfl

/-- A log whose last record does not verify (torn, or changed after the write)
decodes to exactly the batches before that record, and the decoder reports
the bytes of that record. -/
theorem decode_encodeLog_torn (bs : List DeltaBatch) (bytes torn : List UInt8)
    (h : encodeLog? bs = some bytes) (ht : parseDeltaBatch torn = none) :
    decode (bytes ++ torn) = { batches := bs, rest := torn } := by
  rw [decode_encodeLog_append bs bytes torn h, decode_of_parseDeltaBatch_none torn ht]
  simp

/-- Every torn write of a last record: the record of `b` cut after `m` of its
bytes, `m` less than its length, after the records of `bs`. The log decodes
to exactly `bs`, and the cut bytes are reported. -/
theorem decode_encodeLog_cut (bs : List DeltaBatch) (b : DeltaBatch)
    (bytes frame : List UInt8) (m : Nat)
    (h : encodeLog? bs = some bytes) (hb : encodeBatch? b = some frame)
    (hm : m < frame.length) :
    decode (bytes ++ frame.take m) = { batches := bs, rest := frame.take m } :=
  decode_encodeLog_torn bs bytes (frame.take m) h (parseDeltaBatch_take b frame m hb hm)

/-- The same in a log: when the last record has one body byte changed, the log
decodes to exactly the batches before it. -/
theorem decode_encodeLog_byte (bs : List DeltaBatch) (bytes p q : List UInt8) (x y : UInt8)
    (h : encodeLog? bs = some bytes) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) :
    decode (bytes ++ (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
      writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++ (p ++ y :: q) ++
      writeU32LE (simpleChecksum (p ++ x :: q)))) =
    { batches := bs,
      rest := writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++ (p ++ y :: q) ++
        writeU32LE (simpleChecksum (p ++ x :: q)) } := by
  apply decode_encodeLog_torn bs bytes _ h
  have := parseDeltaBatch_body_byte p q [] x y hxy hlen
  rwa [List.append_nil] at this

/-! ## 5. Merge -/

theorem applyBatches_nil (ds : Dataset) : applyBatches ds [] = ds := rfl

/-- Batches apply one by one, in order. -/
theorem applyBatches_cons (ds : Dataset) (b : DeltaBatch) (bs : List DeltaBatch) :
    applyBatches ds (b :: bs) = applyBatches (applyBatch ds b) bs := rfl

theorem applyBatches_append (ds : Dataset) (xs ys : List DeltaBatch) :
    applyBatches ds (xs ++ ys) = applyBatches (applyBatches ds xs) ys := by
  simp [applyBatches, List.foldl_append]

/-- A merge of a log equals applying its batches one by one, in order, over
the base. -/
theorem merge_encodeLog (base : Dataset) (bs : List DeltaBatch) (bytes : List UInt8)
    (h : encodeLog? bs = some bytes) :
    merge base bytes = applyBatches base bs := by
  rw [merge, decode_encodeLog bs bytes h]

/-- The same, when the last record does not verify: the torn record changes
nothing. -/
theorem merge_encodeLog_torn (base : Dataset) (bs : List DeltaBatch)
    (bytes torn : List UInt8) (h : encodeLog? bs = some bytes)
    (ht : parseDeltaBatch torn = none) :
    merge base (bytes ++ torn) = applyBatches base bs := by
  rw [merge, decode_encodeLog_torn bs bytes torn h ht]

/-- Incremental merge: the merge of a log extended by more bytes is the merge of
those bytes over the merge of the log. -/
theorem merge_encodeLog_append (base : Dataset) (bs : List DeltaBatch)
    (bytes more : List UInt8) (h : encodeLog? bs = some bytes) :
    merge base (bytes ++ more) = merge (merge base bytes) more := by
  rw [merge, decode_encodeLog_append bs bytes more h, merge_encodeLog base bs bytes h]
  simp only [applyBatches_append]
  rfl

/-! ## 6. The browser log is the body of a `deltas.dlog` -/

/-- A browser log after the eight-byte DLOG header is a Shardborough
`deltas.dlog` whose replay finds the same batches and the same torn bytes. -/
theorem parseLog_header_append (log : List UInt8) :
    parseLog (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ log) =
      some ((decode log).batches, (decode log).rest) := by
  rw [decode_eq_replay]
  have hm : readU32LE (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ log) 0 =
      some deltaLogMagic := by
    rw [List.append_assoc]
    exact readU32LE_writeU32LE_append _ _
  have hv : readU32LE (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ log) 4 =
      some deltaLogVersion := by
    have h4 : (writeU32LE deltaLogMagic).length = 4 := writeU32LE_length _
    have := readU32LE_append_writeU32LE (writeU32LE deltaLogMagic) deltaLogVersion log
    rwa [h4] at this
  have hd : (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ log).drop 8 = log := by
    have h8 : (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion).length = 8 := by simp
    rw [← h8, List.drop_left]
  simp only [List.append_assoc] at hm hv hd
  unfold parseLog
  simp [bind, Option.bind, hm, hv, hd]

/-! ## 7. What follows the committed records

https://github.com/danbri/factoidal/issues/843. `Storage.classifyTail` says what
the bytes after the records that verify are. Only a crash artifact at the end
is torn: every cut of the last record (`classifyTail_take`), and a complete last
record whose checksum fails (`decode_encodeLog_byte_tail`). A record that fails
its checksum with bytes after it is damaged (`decode_encodeLog_damaged`); a
record whose checksum verifies and whose body does not decode is undecodable,
wherever it is (`decode_encodeLog_undecodable`). `mergeChecked` merges the
batches before a torn tail and stops on the other two (`mergeChecked_*`), and
`parseLogChecked_header_append` shows that the native readers' decision is the
same as the browser's. -/

/-- A u32 read fails without four bytes at the position. -/
theorem readU32LE_none_of_lt {bs : List UInt8} {pos : Nat} (h : bs.length < pos + 4) :
    readU32LE bs pos = none := by
  cases hr : readU32LE bs pos with
  | none => rfl
  | some x => have := readU32LE_some_le hr; omega

theorem batchFrameStart_length : batchFrameStart.length = 8 := by
  simp [batchFrameStart]

/-- The frame `classifyTail` reads: the fixed start, a length field, the body
bytes that follow it, a checksum field, and the bytes after the frame. When
the length field is the length of the body that follows, the verdict depends
only on the checksum and on whether bytes follow. -/
theorem classifyTail_frame (body more : List UInt8) (c : UInt32)
    (hlen : body.length < UInt32.size) :
    classifyTail (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more) =
      if c = simpleChecksum body then .undecodable
      else if more = [] then .torn else .damaged := by
  have h8 : batchFrameStart.length = 8 := batchFrameStart_length
  have hread8 : readU32LE (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more) 8 = some (UInt32.ofNat body.length) := by
    have := readU32LE_append_writeU32LE batchFrameStart (UInt32.ofNat body.length)
      (body ++ writeU32LE c ++ more)
    rw [h8] at this
    simpa [List.append_assoc] using this
  have htake8 : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more).take 8 = batchFrameStart := by
    simp only [List.append_assoc]
    rw [List.take_append_of_le_length (by rw [h8]; exact Nat.le_refl 8), ← h8, List.take_length]
  have hdrop12 : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more).drop 12 = body ++ writeU32LE c ++ more := by
    have hg : batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
        writeU32LE c ++ more =
        (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length)) ++
          (body ++ writeU32LE c ++ more) := by simp [List.append_assoc]
    rw [hg]
    have h12 : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length)).length = 12 := by
      simp [h8]
    rw [← h12, List.drop_left]
  have hlenAll : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more).length = 16 + body.length + more.length := by
    simp [h8]; omega
  have htakeB : (body ++ writeU32LE c ++ more).take body.length = body := by
    rw [List.append_assoc, List.take_left]
  have hchk : readU32LE (body ++ writeU32LE c ++ more) body.length = some c :=
    readU32LE_append_writeU32LE _ _ _
  obtain ⟨x, xs, hx⟩ : ∃ x xs, batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++
      body ++ writeU32LE c ++ more = x :: xs := by
    refine ⟨68, (batchFrameStart.drop 1 ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE c ++ more), ?_⟩
    simp [batchFrameStart, deltaBatchMagic, writeU32LE]
  rw [hx, classifyTail, ← hx, hread8]
  simp only [htake8, bne_self_eq_false, Bool.false_eq_true, if_false, hlenAll,
    u32_toNat_ofNat_of_lt hlen, hdrop12, htakeB, hchk]
  by_cases hc : c = simpleChecksum body
  · simp [hc]
  · have hne : (some c == some (simpleChecksum body)) = false := by simp [hc]
    simp only [hne, hc, if_false, Bool.false_eq_true]
    by_cases hm : more = []
    · subst hm; simp
    · simp [hm]


theorem take8_batchFrameStart (rest : List UInt8) :
    (batchFrameStart ++ rest).take 8 = batchFrameStart := by
  rw [List.take_append_of_le_length (by rw [batchFrameStart_length]; exact Nat.le_refl 8),
    ← batchFrameStart_length, List.take_length]

theorem read8_batchFrameStart (n : UInt32) (rest : List UInt8) :
    readU32LE (batchFrameStart ++ writeU32LE n ++ rest) 8 = some n := by
  have := readU32LE_append_writeU32LE batchFrameStart n rest
  rwa [batchFrameStart_length] at this

/-- The frame of a batch the encoder admits: the fixed start, the length of the
body, the body, and its checksum. -/
theorem serializeDeltaBatch?_shape {b : DeltaBatch} {frame : List UInt8}
    (h : serializeDeltaBatch? b = some frame) :
    ∃ body, body.length < UInt32.size ∧ parseDeltaBatchBody body = some b ∧
      frame = batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
        writeU32LE (simpleChecksum body) := by
  rw [serializeDeltaBatch?] at h
  cases hbody : serializeDeltaBatchBody? b with
  | none => simp [hbody, bind, Option.bind] at h
  | some body =>
  simp only [hbody, bind, Option.bind] at h
  by_cases hlen : body.length ≥ two32
  · rw [if_pos hlen] at h; cases h
  rw [if_neg hlen, Option.some.injEq] at h
  subst h
  refine ⟨body, ?_, parseDeltaBatchBody_serializeDeltaBatchBody? b body hbody, ?_⟩
  · rw [two32_eq_uint32Size] at hlen; omega
  · simp [batchFrameStart, List.append_assoc]

/-- A record the encoder writes, cut after `m` of its bytes with
`0 < m < length`, is a torn tail: every torn write of one record. -/
theorem classifyTail_take (b : DeltaBatch) (frame : List UInt8) (m : Nat)
    (h : encodeBatch? b = some frame) (hpos : 0 < m) (hm : m < frame.length) :
    classifyTail (frame.take m) = .torn := by
  obtain ⟨body, hlen, -, rfl⟩ := serializeDeltaBatch?_shape h
  generalize hF : batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
    writeU32LE (simpleChecksum body) = F at hm ⊢
  have hFlen : F.length = 16 + body.length := by
    rw [← hF]; simp [batchFrameStart_length]; omega
  have hFtake8 : ∀ k, k ≤ 8 → F.take k = batchFrameStart.take k := by
    intro k hk
    rw [← hF]
    simp only [List.append_assoc]
    exact List.take_append_of_le_length (by rw [batchFrameStart_length]; exact hk)
  obtain ⟨x, xs, hx⟩ : ∃ x xs, F.take m = x :: xs := by
    cases hc : F.take m with
    | nil =>
        have := congrArg List.length hc
        simp only [List.length_take, List.length_nil] at this
        omega
    | cons y ys => exact ⟨y, ys, rfl⟩
  have hlenT : (F.take m).length = m := by simp [List.length_take]; omega
  by_cases h12 : m < 12
  · have hnone : readU32LE (F.take m) 8 = none := readU32LE_none_of_lt (by omega)
    have hpre : ((F.take m).take 8).isPrefixOf batchFrameStart = true := by
      rw [List.take_take, hFtake8 _ (Nat.min_le_left 8 m)]
      exact List.isPrefixOf_iff_prefix.mpr (List.take_prefix _ _)
    rw [hx, classifyTail, ← hx, hnone]
    simp only [hpre, if_true]
  · have hread : readU32LE (F.take m) 8 = some (UInt32.ofNat body.length) := by
      rw [readU32LE_take F 8 m (by omega), ← hF]
      simp only [List.append_assoc]
      rw [← List.append_assoc batchFrameStart]
      exact read8_batchFrameStart _ _
    have hstart : (F.take m).take 8 = batchFrameStart := by
      rw [List.take_take, Nat.min_eq_left (by omega), hFtake8 8 (Nat.le_refl 8),
        ← batchFrameStart_length, List.take_length]
    rw [hx, classifyTail, ← hx, hread]
    simp only [hstart, bne_self_eq_false, Bool.false_eq_true, if_false, hlenT,
      u32_toNat_ofNat_of_lt hlen]
    rw [if_pos (by omega)]

/-- A record whose header and checksum verify but whose body does not decode is
refused by `parseDeltaBatch`, whatever follows it. -/
theorem parseDeltaBatch_body_none (body more : List UInt8)
    (hlen : body.length < UInt32.size) (hb : parseDeltaBatchBody body = none) :
    parseDeltaBatch (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more) = none := by
  have hmagic : readU32LE (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more) 0 = some deltaBatchMagic := by
    simp only [batchFrameStart, List.append_assoc]
    exact readU32LE_writeU32LE_append _ _
  have hver : readU32LE (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more) 4 = some deltaBatchVersion := by
    have h4 : (writeU32LE deltaBatchMagic).length = 4 := writeU32LE_length _
    have := readU32LE_append_writeU32LE (writeU32LE deltaBatchMagic) deltaBatchVersion
      (writeU32LE (UInt32.ofNat body.length) ++ body ++ writeU32LE (simpleChecksum body) ++ more)
    rw [h4] at this
    simpa [batchFrameStart, List.append_assoc] using this
  have hlenB : readU32LE (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more) 8 = some (UInt32.ofNat body.length) := by
    simpa [List.append_assoc] using
      read8_batchFrameStart (UInt32.ofNat body.length) (body ++ writeU32LE (simpleChecksum body) ++ more)
  have hdrop12 : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more).drop 12 =
      body ++ writeU32LE (simpleChecksum body) ++ more := by
    have hg : batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
        writeU32LE (simpleChecksum body) ++ more =
        (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length)) ++
          (body ++ writeU32LE (simpleChecksum body) ++ more) := by simp [List.append_assoc]
    rw [hg]
    have h12 : (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length)).length = 12 := by
      simp [batchFrameStart_length]
    rw [← h12, List.drop_left]
  have htake : (body ++ writeU32LE (simpleChecksum body) ++ more).take body.length = body := by
    rw [List.append_assoc, List.take_left]
  have hchk : readU32LE (body ++ writeU32LE (simpleChecksum body) ++ more) body.length =
      some (simpleChecksum body) := readU32LE_append_writeU32LE _ _ _
  rw [parseDeltaBatch]
  simp only [bind, Option.bind, hmagic, bne_self_eq_false, Bool.false_eq_true, if_false,
    hver, hlenB, hdrop12, u32_toNat_ofNat_of_lt hlen, htake, List.length_take, hchk, hb]
  simp


/-! ### The verdicts on a log -/

/-- A torn final record: the log of `bs` followed by the record of `b` cut
after `m` bytes, `0 < m < length`. The decode keeps `bs`, and the tail is
torn. -/
theorem decode_encodeLog_cut_tail (bs : List DeltaBatch) (b : DeltaBatch)
    (bytes frame : List UInt8) (m : Nat)
    (h : encodeLog? bs = some bytes) (hb : encodeBatch? b = some frame)
    (hpos : 0 < m) (hm : m < frame.length) :
    (decode (bytes ++ frame.take m)).batches = bs ∧
      (decode (bytes ++ frame.take m)).tail = .torn := by
  rw [decode_encodeLog_cut bs b bytes frame m h hb hm]
  exact ⟨rfl, classifyTail_take b frame m hb hpos hm⟩

/-- The final record with one body byte changed after the write: the frame is
complete and its checksum fails, so the tail is torn. -/
theorem decode_encodeLog_byte_tail (bs : List DeltaBatch) (bytes p q : List UInt8)
    (x y : UInt8) (h : encodeLog? bs = some bytes) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) :
    (decode (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q))))).tail = .torn := by
  have hd := decode_encodeLog_byte bs bytes p q x y h hxy hlen
  simp only [batchFrameStart] at hd ⊢
  rw [hd]
  show classifyTail _ = _
  have hl : (p ++ x :: q).length = (p ++ y :: q).length := by simp
  have hl2 : (p ++ y :: q).length < UInt32.size := by rw [← hl]; exact hlen
  have hc := classifyTail_frame (p ++ y :: q) [] (simpleChecksum (p ++ x :: q)) hl2
  rw [← hl, List.append_nil] at hc
  simp only [batchFrameStart] at hc
  rw [hc, if_neg (simpleChecksum_ne_of_byte p q x y hxy)]
  simp

/-- A record with one body byte changed and more bytes after it, after the
records of `bs`: the decode keeps `bs`, and the tail is damaged. -/
theorem decode_encodeLog_damaged (bs : List DeltaBatch) (bytes p q more : List UInt8)
    (x y : UInt8) (h : encodeLog? bs = some bytes) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) (hmore : more ≠ []) :
    (decode (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q)) ++ more))).batches = bs ∧
    (decode (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q)) ++ more))).tail = .damaged := by
  have hnone := parseDeltaBatch_body_byte p q more x y hxy hlen
  have hnone' : parseDeltaBatch (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q)) ++ more) = none := hnone
  rw [decode_encodeLog_torn bs bytes _ h hnone']
  refine ⟨rfl, ?_⟩
  show classifyTail _ = _
  have hl : (p ++ x :: q).length = (p ++ y :: q).length := by simp
  have hl2 : (p ++ y :: q).length < UInt32.size := by rw [← hl]; exact hlen
  have hc := classifyTail_frame (p ++ y :: q) more (simpleChecksum (p ++ x :: q)) hl2
  rw [← hl] at hc
  rw [hc, if_neg (simpleChecksum_ne_of_byte p q x y hxy), if_neg hmore]

/-- A committed record whose header and checksum verify and whose body does not
decode, after the records of `bs` and before any bytes: the decode keeps `bs`,
and the tail is undecodable. -/
theorem decode_encodeLog_undecodable (bs : List DeltaBatch) (bytes body more : List UInt8)
    (h : encodeLog? bs = some bytes) (hlen : body.length < UInt32.size)
    (hb : parseDeltaBatchBody body = none) :
    (decode (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more))).batches = bs ∧
    (decode (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
      writeU32LE (simpleChecksum body) ++ more))).tail = .undecodable := by
  rw [decode_encodeLog_torn bs bytes _ h (parseDeltaBatch_body_none body more hlen hb)]
  refine ⟨rfl, ?_⟩
  show classifyTail _ = _
  rw [classifyTail_frame body more (simpleChecksum body) hlen, if_pos rfl]

/-! ### The checked merge -/

/-- A clean log merges to its batches applied one by one. -/
theorem mergeChecked_encodeLog (base : Dataset) (bs : List DeltaBatch) (bytes : List UInt8)
    (h : encodeLog? bs = some bytes) :
    mergeChecked base bytes = .ok (applyBatches base bs) := by
  unfold mergeChecked LogRead.error?
  rw [decode_encodeLog bs bytes h, merge_encodeLog base bs bytes h]
  rfl

/-- A torn final record changes nothing: every cut of the last record merges to
the batches before it. -/
theorem mergeChecked_encodeLog_cut (base : Dataset) (bs : List DeltaBatch) (b : DeltaBatch)
    (bytes frame : List UInt8) (m : Nat)
    (h : encodeLog? bs = some bytes) (hb : encodeBatch? b = some frame)
    (hm : m < frame.length) :
    mergeChecked base (bytes ++ frame.take m) = .ok (applyBatches base bs) := by
  have hmerge := merge_encodeLog_torn base bs bytes (frame.take m) h
    (parseDeltaBatch_take b frame m hb hm)
  unfold mergeChecked LogRead.error? LogRead.tail
  rw [decode_encodeLog_cut bs b bytes frame m h hb hm]
  by_cases hpos : 0 < m
  · rw [classifyTail_take b frame m hb hpos hm, hmerge]; rfl
  · have : m = 0 := by omega
    subst this
    rw [List.take_zero] at hmerge ⊢
    rw [hmerge]; rfl

/-- A final record with one body byte changed (a complete frame whose checksum
fails) is torn: the log merges to the batches before it. -/
theorem mergeChecked_encodeLog_byte (base : Dataset) (bs : List DeltaBatch)
    (bytes p q : List UInt8) (x y : UInt8) (h : encodeLog? bs = some bytes) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) :
    mergeChecked base (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q)))) = .ok (applyBatches base bs) := by
  have htail := decode_encodeLog_byte_tail bs bytes p q x y h hxy hlen
  have hnone := parseDeltaBatch_body_byte p q [] x y hxy hlen
  rw [List.append_nil] at hnone
  have hnone' : parseDeltaBatch (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q))) = none := hnone
  have hmerge := merge_encodeLog_torn base bs bytes _ h hnone'
  unfold mergeChecked LogRead.error?
  rw [htail, hmerge]; rfl

/-- A damaged record with bytes after it is an error: the merge stops. -/
theorem mergeChecked_damaged (base : Dataset) (bs : List DeltaBatch) (bytes p q more : List UInt8)
    (x y : UInt8) (h : encodeLog? bs = some bytes) (hxy : x ≠ y)
    (hlen : (p ++ x :: q).length < UInt32.size) (hmore : more ≠ []) :
    ∃ e, mergeChecked base (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat (p ++ x :: q).length) ++
      (p ++ y :: q) ++ writeU32LE (simpleChecksum (p ++ x :: q)) ++ more)) = .error e := by
  obtain ⟨-, htail⟩ := decode_encodeLog_damaged bs bytes p q more x y h hxy hlen hmore
  unfold mergeChecked LogRead.error?
  rw [htail]
  exact ⟨_, rfl⟩

/-- A committed record that does not decode is an error, at the end of the log
and in the middle: the merge stops. -/
theorem mergeChecked_undecodable (base : Dataset) (bs : List DeltaBatch) (bytes body more : List UInt8)
    (h : encodeLog? bs = some bytes) (hlen : body.length < UInt32.size)
    (hb : parseDeltaBatchBody body = none) :
    ∃ e, mergeChecked base (bytes ++ (batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++
      body ++ writeU32LE (simpleChecksum body) ++ more)) = .error e := by
  obtain ⟨-, htail⟩ := decode_encodeLog_undecodable bs bytes body more h hlen hb
  unfold mergeChecked LogRead.error?
  rw [htail]
  exact ⟨_, rfl⟩

/-! ### The native readers decide as the browser merge -/

/-- `parseLogChecked`, the decision of every native reader, on a log with its
DLOG header: the batches and the torn flag the browser decode gives when the
tail is clean or torn, and an error otherwise. -/
theorem parseLogChecked_header_append (log : List UInt8) :
    (parseLogChecked (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion ++ log)).toOption =
      if (decode log).tail.recoverable then some ((decode log).batches, (decode log).torn)
      else none := by
  unfold parseLogChecked
  rw [parseLog_header_append]
  simp only [LogRead.torn, LogRead.tail]
  split
  · rename_i hk; simp [hk, LogTail.recoverable, Except.toOption]
  · rename_i hk; simp [hk, LogTail.recoverable, Except.toOption]
  · rename_i _ hc ht
    obtain ⟨k, hk⟩ : ∃ k, classifyTail (decode log).rest = k := ⟨_, rfl⟩
    cases k with
    | clean => exact absurd hk hc
    | torn => exact absurd hk ht
    | damaged => simp [hk, LogTail.recoverable, Except.toOption]
    | undecodable => simp [hk, LogTail.recoverable, Except.toOption]


#print axioms parseTriple_serializeTriple?
#print axioms parseDeltaEntryPayload_serializeDeltaEntryPayload?
#print axioms parseFramedDeltaEntry_serializeFramedDeltaEntry?
#print axioms parseDeltaBatch_serializeDeltaBatch?
#print axioms parseBatch_eq
#print axioms decode_eq_replay
#print axioms parseDeltaBatch_take
#print axioms decode_encodeLog
#print axioms decode_encodeBatch
#print axioms decode_encodeLog_torn
#print axioms decode_encodeLog_cut
#print axioms parseDeltaBatch_body_byte
#print axioms decode_encodeLog_byte
#print axioms merge_encodeLog
#print axioms merge_encodeLog_torn
#print axioms merge_encodeLog_append
#print axioms parseLog_header_append
#print axioms classifyTail_frame
#print axioms classifyTail_take
#print axioms parseDeltaBatch_body_none
#print axioms serializeDeltaBatch?_shape
#print axioms decode_encodeLog_cut_tail
#print axioms decode_encodeLog_byte_tail
#print axioms decode_encodeLog_damaged
#print axioms decode_encodeLog_undecodable
#print axioms mergeChecked_encodeLog
#print axioms mergeChecked_encodeLog_cut
#print axioms mergeChecked_encodeLog_byte
#print axioms mergeChecked_damaged
#print axioms mergeChecked_undecodable
#print axioms parseLogChecked_header_append

end L4Factoidal.Storage.BrowserLog
