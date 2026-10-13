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
   torn write. A record with a changed body byte fails its checksum; the
   build-time checks of `BrowserLog` show one such case, and no theorem
   states it for every byte yet.
5. `merge_encodeLog`: a merge of a log equals applying its batches one by one,
   in order; `merge_encodeLog_torn` the same for a log with a torn last
   record; `merge_encodeLog_append` gives an incremental merge.
6. `parseLog_header_append`: a browser log after the eight-byte DLOG header is
   a Shardborough `deltas.dlog` with the same batches.

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
#print axioms merge_encodeLog
#print axioms merge_encodeLog_torn
#print axioms merge_encodeLog_append
#print axioms parseLog_header_append

end L4Factoidal.Storage.BrowserLog
