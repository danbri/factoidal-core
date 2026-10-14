/-
L4Factoidal.Storage.DeltaLogCodecTheorems — the DLE1/DLB1 entry and batch
codec of `Storage.DeltaLog`, proved once over any term codec
(https://github.com/danbri/factoidal/issues/792 item 1).

`DeltaLog` writes the entries of a DLOG of version 1 with the version 1 term
codec and those of a DLOG of version 2 with `DeltaTermCodec.v2` (triple
terms and directional literals). The framing does not depend on the term
codec, so the round trip of each layer (triple, entry payload, DLE1 entry
frame, entry list, batch body, DLB1 batch frame) is proved here for every
term codec whose decoder inverts its encoder (`DeltaTermCodec.RoundTrip`),
and instantiated for both versions: `DeltaTermCodec.v1_roundTrip` is
`TermCodecTheorems.parseTerm_serializeTerm?_checked`,
`DeltaTermCodec.v2_roundTrip` is `parseDeltaTerm_serializeDeltaTerm?`.

`appendPlan?_v1`: a batch that holds no RDF 1.2 term, on a new log or a
version 1 log, gets version 1 and the bytes the version 1 writer wrote before
version 2 existed, so a log without RDF 1.2 terms does not change.

The writer sets the header of an existing version 1 log to version 2, in
place, before it appends the first batch that holds an RDF 1.2 term
(`appendPlan?`). The frames already in the log are then read with the
version 2 codec. `DeltaTermCodec.v2_extends_v1`: the version 2 encoder writes
every term the version 1 encoder writes, with the same bytes; lifted through
the framing (`serializeDeltaBatchWith?_extends`), every version 1 frame is a
version 2 frame, which the version 2 reader inverts
(`parseDeltaBatchWith_v2_of_v1`). `parseLog_v2_of_frames`: a version 2 log
whose frames were written by either writer reads back every batch, in order,
with nothing left over. `termNeedsV2_eq`: a term needs version 2 exactly when
the version 1 codec does not support it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.BrowserLogTheorems
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-- A term codec whose decoder inverts its encoder, with any bytes after. -/
def DeltaTermCodec.RoundTrip (tc : DeltaTermCodec) : Prop :=
  ∀ (t : Term) (bs rest : List UInt8), tc.encode t = some bs → tc.decode (bs ++ rest) = some (t, rest)

theorem DeltaTermCodec.v1_roundTrip : DeltaTermCodec.v1.RoundTrip :=
  fun t bs rest h => parseTerm_serializeTerm?_checked t bs rest h

theorem DeltaTermCodec.v2_roundTrip : DeltaTermCodec.v2.RoundTrip :=
  fun t bs rest h => parseDeltaTerm_serializeDeltaTerm? t bs rest h

section
variable (tc : DeltaTermCodec) (hrt : tc.RoundTrip)
include hrt

theorem parseTripleWith_serializeTripleWith? (t : Triple) (bs rest : List UInt8)
    (h : serializeTripleWith? tc t = some bs) :
    parseTripleWith tc (bs ++ rest) = some (t, rest) := by
  rw [serializeTripleWith?] at h
  cases hs : serializeSubject? t.s with
  | none => simp [hs, bind, Option.bind] at h
  | some sb =>
  cases hp : serializeLString? t.p.val with
  | none => simp [hs, hp, bind, Option.bind] at h
  | some pb =>
  cases ho : tc.encode t.o with
  | none => simp [hs, hp, ho, bind, Option.bind] at h
  | some ob =>
  simp only [hs, hp, ho, bind, Option.bind, Option.some.injEq] at h
  subst h
  have e : sb ++ pb ++ ob ++ rest = sb ++ (pb ++ (ob ++ rest)) := by
    simp [List.append_assoc]
  rw [e, parseTripleWith]
  simp only [bind, Option.bind,
    parseSubject_serializeSubject? t.s sb _ hs,
    parseLString_serializeLString? t.p.val pb _ hp,
    dif_pos t.p.property,
    hrt t.o ob rest ho]

theorem parseDeltaEntryPayloadWith_serializeDeltaEntryPayloadWith? (e : DeltaEntry)
    (bs rest : List UInt8) (h : serializeDeltaEntryPayloadWith? tc e = some bs) :
    parseDeltaEntryPayloadWith tc (bs ++ rest) = some (e, rest) := by
  cases e with
  | add t g =>
      rw [serializeDeltaEntryPayloadWith?] at h
      cases ht : serializeTripleWith? tc t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
      cases hg : serializeGraphOpt? g with
      | none => simp [ht, hg, bind, Option.bind] at h
      | some gb =>
      simp only [ht, hg, bind, Option.bind, Option.some.injEq] at h
      subst h
      rw [List.cons_append, List.append_assoc, parseDeltaEntryPayloadWith]
      simp [bind, Option.bind, parseU8, deTagAdd,
        parseTripleWith_serializeTripleWith? tc hrt t tb _ ht,
        BrowserLog.parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | remove t g =>
      rw [serializeDeltaEntryPayloadWith?] at h
      cases ht : serializeTripleWith? tc t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
      cases hg : serializeGraphOpt? g with
      | none => simp [ht, hg, bind, Option.bind] at h
      | some gb =>
      simp only [ht, hg, bind, Option.bind, Option.some.injEq] at h
      subst h
      rw [List.cons_append, List.append_assoc, parseDeltaEntryPayloadWith]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove,
        parseTripleWith_serializeTripleWith? tc hrt t tb _ ht,
        BrowserLog.parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | clear g =>
      rw [serializeDeltaEntryPayloadWith?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayloadWith]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear,
        BrowserLog.parseGraphOpt_serializeGraphOpt? g gb rest hg]
  | drop g =>
      rw [serializeDeltaEntryPayloadWith?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayloadWith]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear, deTagDrop,
        parseLString_serializeLString? g gb rest hg]
  | create g =>
      rw [serializeDeltaEntryPayloadWith?, Option.map_eq_some_iff] at h
      obtain ⟨gb, hg, rfl⟩ := h
      rw [List.cons_append, parseDeltaEntryPayloadWith]
      simp [bind, Option.bind, parseU8, deTagAdd, deTagRemove, deTagClear, deTagDrop,
        deTagCreate, parseLString_serializeLString? g gb rest hg]

theorem parseFramedDeltaEntryWith_serializeFramedDeltaEntryWith? (e : DeltaEntry)
    (bs rest : List UInt8) (h : serializeFramedDeltaEntryWith? tc e = some bs) :
    parseFramedDeltaEntryWith tc (bs ++ rest) = some (e, rest) := by
  rw [serializeFramedDeltaEntryWith?] at h
  cases hp : serializeDeltaEntryPayloadWith? tc e with
  | none => simp [hp, bind, Option.bind] at h
  | some pb =>
  simp only [hp, bind, Option.bind] at h
  have hpay := parseDeltaEntryPayloadWith_serializeDeltaEntryPayloadWith? tc hrt e pb [] hp
  rw [List.append_nil] at hpay
  rw [parseFramedDeltaEntryWith]
  simp [bind, Option.bind, parseEntry_frameEntry?_append pb bs rest h, hpay]

theorem parseNFramedDeltaEntriesWith_flatten (ops : List DeltaEntry)
    (frames : List (List UInt8)) (rest : List UInt8) (acc : List DeltaEntry)
    (h : ops.mapM (serializeFramedDeltaEntryWith? tc) = some frames) :
    parseNFramedDeltaEntriesWith tc ops.length (frames.flatten ++ rest) acc =
      some (acc.reverse ++ ops, rest) := by
  induction ops generalizing frames acc with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      simp [parseNFramedDeltaEntriesWith]
  | cons e es ih =>
      rw [List.mapM_cons] at h
      cases he : serializeFramedDeltaEntryWith? tc e with
      | none => simp [he, bind, Option.bind] at h
      | some eb =>
      cases hes : es.mapM (serializeFramedDeltaEntryWith? tc) with
      | none => simp [he, hes, bind, Option.bind] at h
      | some ebs =>
      simp only [he, hes, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      rw [List.length_cons, List.flatten_cons, List.append_assoc, parseNFramedDeltaEntriesWith,
        parseFramedDeltaEntryWith_serializeFramedDeltaEntryWith? tc hrt e eb _ he]
      simp only
      rw [ih ebs (e :: acc) hes]
      simp

theorem parseDeltaBatchBodyWith_serializeDeltaBatchBodyWith? (b : DeltaBatch) (body : List UInt8)
    (h : serializeDeltaBatchBodyWith? tc b = some body) :
    parseDeltaBatchBodyWith tc body = some b := by
  rw [serializeDeltaBatchBodyWith?] at h
  by_cases hb : (!natFitsU64 b.seq || !natFitsU64 b.epoch || b.ops.length >= two32) = true
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or,
    Bool.not_eq_false] at hb
  obtain ⟨⟨hseq, hepoch⟩, hlen⟩ := hb
  cases hes : b.ops.mapM (serializeFramedDeltaEntryWith? tc) with
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
    rw [BrowserLog.readU64LE_drop, List.append_assoc, List.append_assoc]
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
  have hents := parseNFramedDeltaEntriesWith_flatten tc hrt b.ops frames [] [] hes
  rw [List.append_nil] at hents
  rw [parseDeltaBatchBodyWith]
  simp only [bind, Option.bind, hseqB, hepochB, hcountB, hdrop,
    u32_toNat_ofNat_of_lt hlt, hents, List.reverse_nil, List.nil_append, List.isEmpty_nil,
    if_true, BrowserLog.natFitsU64_toNat hseq, BrowserLog.natFitsU64_toNat hepoch]

theorem parseDeltaBatchWith_serializeDeltaBatchWith? (b : DeltaBatch) (frame rest : List UInt8)
    (h : serializeDeltaBatchWith? tc b = some frame) :
    parseDeltaBatchWith tc (frame ++ rest) = some (b, rest) := by
  rw [serializeDeltaBatchWith?] at h
  cases hbody : serializeDeltaBatchBodyWith? tc b with
  | none => simp [hbody, bind, Option.bind] at h
  | some body =>
  simp only [hbody, bind, Option.bind] at h
  by_cases hlen : body.length ≥ two32
  · rw [if_pos hlen] at h; cases h
  rw [if_neg hlen, Option.some.injEq] at h
  subst h
  have hlt : body.length < UInt32.size := by
    rw [two32_eq_uint32Size] at hlen; omega
  have hb := parseDeltaBatchBodyWith_serializeDeltaBatchBodyWith? tc hrt b body hbody
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
  rw [parseDeltaBatchWith]
  simp only [bind, Option.bind, hmagic, bne_self_eq_false, Bool.false_eq_true, if_false,
    hver, hlenB, hdrop12, u32_toNat_ofNat_of_lt hlt, htake, hchk, hb, hafter]

end


/-- The DLB1 frame of a DLOG of version 2 reads back with any bytes after it. -/
theorem parseDeltaBatchWith_v2 (b : DeltaBatch) (frame rest : List UInt8)
    (h : serializeDeltaBatchWith? .v2 b = some frame) :
    parseDeltaBatchWith .v2 (frame ++ rest) = some (b, rest) :=
  parseDeltaBatchWith_serializeDeltaBatchWith? .v2 DeltaTermCodec.v2_roundTrip b frame rest h

/-- The version 1 instance is the version 1 writer. -/
theorem serializeDeltaBatchWith?_v1 : serializeDeltaBatchWith? .v1 = serializeDeltaBatch? := rfl

/-- A batch with no RDF 1.2 term, on a new log or on a version 1 log, keeps
    version 1 and gets the bytes of the version 1 writer. -/
theorem appendPlan?_v1 (b : DeltaBatch) (logVersion : Option UInt32)
    (hlog : logVersion = none ∨ logVersion = some deltaLogVersion)
    (hb : b.ops.any entryNeedsV2 = false) :
    appendPlan? logVersion b =
      (serializeDeltaBatch? b).map fun frame =>
        { version := deltaLogVersion, setVersion2 := false,
          bytes := (if logVersion = none then logHeader deltaLogVersion else []) ++ frame } := by
  have hver : (if b.ops.any entryNeedsV2 || logVersion == some deltaLogVersion2 then
      deltaLogVersion2 else deltaLogVersion) = deltaLogVersion := by
    rcases hlog with rfl | rfl <;> simp [hb, deltaLogVersion, deltaLogVersion2]
  unfold appendPlan?
  simp only [hver]
  rw [show DeltaTermCodec.ofVersion deltaLogVersion = some .v1 by rfl]
  simp only [serializeDeltaBatchWith?_v1]
  cases hs : serializeDeltaBatch? b with
  | none => simp [bind, Option.bind]
  | some frame =>
    rcases hlog with rfl | rfl <;> simp [bind, Option.bind]

/-- `tc2` writes every term that `tc1` writes, with the same bytes. -/
def DeltaTermCodec.Extends (tc1 tc2 : DeltaTermCodec) : Prop :=
  ∀ (t : Term) (bs : List UInt8), tc1.encode t = some bs → tc2.encode t = some bs

/-- The version 1 encoder admits only terms that `termSupported` admits. -/
theorem termSupported_of_serializeTerm? (t : Term) (bs : List UInt8)
    (h : serializeTerm? t = some bs) : BlockWireV0.termSupported t = true := by
  cases t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal l =>
      cases hd : l.val.direction with
      | none => simp [BlockWireV0.termSupported, hd]
      | some d => simp [serializeTerm?, hd] at h
  | tripleTerm _ _ _ => simp [serializeTerm?] at h

/-- The version 2 encoder writes every term the version 1 encoder writes, with
    the same bytes. -/
theorem DeltaTermCodec.v2_extends_v1 : DeltaTermCodec.v1.Extends DeltaTermCodec.v2 := by
  intro t bs h
  have h' : serializeTerm? t = some bs := h
  show serializeDeltaTerm? t = some bs
  rw [serializeDeltaTerm?_of_supported t (termSupported_of_serializeTerm? t bs h')]
  exact h'

section
variable {tc1 tc2 : DeltaTermCodec} (hx : tc1.Extends tc2)
include hx

theorem serializeTripleWith?_extends (t : Triple) (bs : List UInt8)
    (h : serializeTripleWith? tc1 t = some bs) : serializeTripleWith? tc2 t = some bs := by
  unfold serializeTripleWith? at h ⊢
  cases hs : serializeSubject? t.s with
  | none => simp [hs, bind, Option.bind] at h
  | some sb =>
  cases hp : serializeLString? t.p.val with
  | none => simp [hs, hp, bind, Option.bind] at h
  | some pb =>
  cases ho : tc1.encode t.o with
  | none => simp [hs, hp, ho, bind, Option.bind] at h
  | some ob =>
  simp only [hs, hp, ho, bind, Option.bind] at h
  simp only [hx t.o ob ho, bind, Option.bind]
  exact h

theorem serializeDeltaEntryPayloadWith?_extends (e : DeltaEntry) (bs : List UInt8)
    (h : serializeDeltaEntryPayloadWith? tc1 e = some bs) :
    serializeDeltaEntryPayloadWith? tc2 e = some bs := by
  cases e with
  | add t g =>
      unfold serializeDeltaEntryPayloadWith? at h ⊢
      cases ht : serializeTripleWith? tc1 t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
        simp only [ht, bind, Option.bind] at h
        simp only [serializeTripleWith?_extends hx t tb ht, bind, Option.bind]
        exact h
  | remove t g =>
      unfold serializeDeltaEntryPayloadWith? at h ⊢
      cases ht : serializeTripleWith? tc1 t with
      | none => simp [ht, bind, Option.bind] at h
      | some tb =>
        simp only [ht, bind, Option.bind] at h
        simp only [serializeTripleWith?_extends hx t tb ht, bind, Option.bind]
        exact h
  | clear g => exact h
  | drop g => exact h
  | create g => exact h

theorem serializeFramedDeltaEntryWith?_extends (e : DeltaEntry) (bs : List UInt8)
    (h : serializeFramedDeltaEntryWith? tc1 e = some bs) :
    serializeFramedDeltaEntryWith? tc2 e = some bs := by
  unfold serializeFramedDeltaEntryWith? at h ⊢
  cases hp : serializeDeltaEntryPayloadWith? tc1 e with
  | none => simp [hp, bind, Option.bind] at h
  | some pb =>
    simp only [hp, bind, Option.bind] at h
    simp only [serializeDeltaEntryPayloadWith?_extends hx e pb hp, bind, Option.bind]
    exact h

theorem mapM_serializeFramedDeltaEntryWith?_extends (ops : List DeltaEntry)
    (frames : List (List UInt8))
    (h : ops.mapM (serializeFramedDeltaEntryWith? tc1) = some frames) :
    ops.mapM (serializeFramedDeltaEntryWith? tc2) = some frames := by
  induction ops generalizing frames with
  | nil => simpa using h
  | cons e es ih =>
    rw [List.mapM_cons] at h ⊢
    cases he : serializeFramedDeltaEntryWith? tc1 e with
    | none => simp [he, bind, Option.bind] at h
    | some eb =>
    cases hes : es.mapM (serializeFramedDeltaEntryWith? tc1) with
    | none => simp [he, hes, bind, Option.bind] at h
    | some ebs =>
    simp only [he, hes, bind, Option.bind] at h
    simp only [serializeFramedDeltaEntryWith?_extends hx e eb he, ih ebs hes, bind, Option.bind]
    exact h

theorem serializeDeltaBatchBodyWith?_extends (b : DeltaBatch) (body : List UInt8)
    (h : serializeDeltaBatchBodyWith? tc1 b = some body) :
    serializeDeltaBatchBodyWith? tc2 b = some body := by
  unfold serializeDeltaBatchBodyWith? at h ⊢
  split
  · rename_i hb; rw [if_pos hb] at h; cases h
  · rename_i hb
    rw [if_neg hb] at h
    cases hes : b.ops.mapM (serializeFramedDeltaEntryWith? tc1) with
    | none => simp [hes, bind, Option.bind] at h
    | some frames =>
      simp only [hes, bind, Option.bind] at h
      simp only [mapM_serializeFramedDeltaEntryWith?_extends hx b.ops frames hes, bind,
        Option.bind]
      exact h

theorem serializeDeltaBatchWith?_extends (b : DeltaBatch) (frame : List UInt8)
    (h : serializeDeltaBatchWith? tc1 b = some frame) :
    serializeDeltaBatchWith? tc2 b = some frame := by
  unfold serializeDeltaBatchWith? at h ⊢
  cases hb : serializeDeltaBatchBodyWith? tc1 b with
  | none => simp [hb, bind, Option.bind] at h
  | some body =>
    simp only [hb, bind, Option.bind] at h
    simp only [serializeDeltaBatchBodyWith?_extends hx b body hb, bind, Option.bind]
    exact h

end

/-- A frame the version 1 writer wrote reads back the same under the version 2
    reader: the frames of a version 1 log are unchanged when its header gets
    version 2. -/
theorem parseDeltaBatchWith_v2_of_v1 (b : DeltaBatch) (frame rest : List UInt8)
    (h : serializeDeltaBatch? b = some frame) :
    parseDeltaBatchWith .v2 (frame ++ rest) = some (b, rest) :=
  parseDeltaBatchWith_v2 b frame rest
    (serializeDeltaBatchWith?_extends DeltaTermCodec.v2_extends_v1 b frame
      (by rw [serializeDeltaBatchWith?_v1]; exact h))

theorem serializeDeltaBatchWith?_ne_nil (tc : DeltaTermCodec) (b : DeltaBatch) (frame : List UInt8)
    (h : serializeDeltaBatchWith? tc b = some frame) : frame ≠ [] := by
  unfold serializeDeltaBatchWith? at h
  cases hb : serializeDeltaBatchBodyWith? tc b with
  | none => simp [hb, bind, Option.bind] at h
  | some body =>
    simp only [hb, bind, Option.bind] at h
    split at h
    · cases h
    · cases h
      simp [writeU32LE]

/-- The replay loop over a sequence of frames, each read back by `tc`. -/
theorem replayDeltaBatchesWith_go_frames (tc : DeltaTermCodec) :
    ∀ (pairs : List (DeltaBatch × List UInt8)) (fuel : Nat) (acc : List DeltaBatch),
    (∀ p ∈ pairs, ∀ rest, parseDeltaBatchWith tc (p.2 ++ rest) = some (p.1, rest)) →
    (∀ p ∈ pairs, p.2 ≠ []) →
    pairs.length ≤ fuel →
    replayDeltaBatchesWith.go tc fuel (pairs.map Prod.snd).flatten acc =
      ((pairs.map Prod.fst).reverse ++ acc, [])
  | [], fuel, acc, _, _, _ => by
      cases fuel <;> simp [replayDeltaBatchesWith.go]
  | (b, f) :: ps, fuel, acc, hp, hne, hfuel => by
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
      have hf : f ≠ [] := hne (b, f) (List.mem_cons_self ..)
      have hparse := hp (b, f) (List.mem_cons_self ..) (ps.map Prod.snd).flatten
      simp only [List.map_cons, List.flatten_cons]
      rw [replayDeltaBatchesWith.go]
      have hnil : (f ++ (ps.map Prod.snd).flatten).isEmpty = false := by
        cases f with
        | nil => exact absurd rfl hf
        | cons x xs => rfl
      simp only [hnil, Bool.false_eq_true, if_false, hparse]
      rw [replayDeltaBatchesWith_go_frames tc ps k (b :: acc)
        (fun p hm => hp p (List.mem_cons_of_mem _ hm))
        (fun p hm => hne p (List.mem_cons_of_mem _ hm))
        (by simp at hfuel; omega)]
      simp

theorem length_le_flatten_length (pairs : List (DeltaBatch × List UInt8))
    (hne : ∀ p ∈ pairs, p.2 ≠ []) :
    pairs.length ≤ ((pairs.map Prod.snd).flatten).length := by
  induction pairs with
  | nil => simp
  | cons p ps ih =>
    have h1 : p.2 ≠ [] := hne p (List.mem_cons_self ..)
    have h2 := ih (fun q hm => hne q (List.mem_cons_of_mem _ hm))
    have h3 : 1 ≤ p.2.length := by
      cases hq : p.2 with
      | nil => exact absurd hq h1
      | cons _ _ => simp
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append]
    omega

theorem replayDeltaBatchesWith_frames (tc : DeltaTermCodec) (pairs : List (DeltaBatch × List UInt8))
    (hp : ∀ p ∈ pairs, ∀ rest, parseDeltaBatchWith tc (p.2 ++ rest) = some (p.1, rest))
    (hne : ∀ p ∈ pairs, p.2 ≠ []) :
    replayDeltaBatchesWith tc (pairs.map Prod.snd).flatten = (pairs.map Prod.fst, []) := by
  unfold replayDeltaBatchesWith
  rw [replayDeltaBatchesWith_go_frames tc pairs _ [] hp hne (length_le_flatten_length pairs hne)]
  simp

/-- A DLOG of version 2 whose frames were written by the version 1 writer
    (before its header got version 2) or by the version 2 writer reads back
    every batch, in order, with nothing left over. -/
theorem parseLog_v2_of_frames (pairs : List (DeltaBatch × List UInt8))
    (h : ∀ p ∈ pairs, serializeDeltaBatch? p.1 = some p.2 ∨
      serializeDeltaBatchWith? .v2 p.1 = some p.2) :
    parseLog (logHeader deltaLogVersion2 ++ (pairs.map Prod.snd).flatten) =
      some (pairs.map Prod.fst, []) := by
  have hm : readU32LE (logHeader deltaLogVersion2 ++ (pairs.map Prod.snd).flatten) 0 =
      some deltaLogMagic := by
    unfold logHeader; rw [List.append_assoc]; exact readU32LE_writeU32LE_append _ _
  have hv : readU32LE (logHeader deltaLogVersion2 ++ (pairs.map Prod.snd).flatten) 4 =
      some deltaLogVersion2 := by
    unfold logHeader
    have h4 : (writeU32LE deltaLogMagic).length = 4 := writeU32LE_length _
    have := readU32LE_append_writeU32LE (writeU32LE deltaLogMagic) deltaLogVersion2
      ((pairs.map Prod.snd).flatten)
    rwa [h4] at this
  have hd : (logHeader deltaLogVersion2 ++ (pairs.map Prod.snd).flatten).drop 8 =
      (pairs.map Prod.snd).flatten := by
    unfold logHeader
    have h8 : (writeU32LE deltaLogMagic ++ writeU32LE deltaLogVersion2).length = 8 := by simp
    rw [← h8, List.drop_left]
  have hr := replayDeltaBatchesWith_frames .v2 pairs
    (fun p hm rest => (h p hm).elim (fun h1 => parseDeltaBatchWith_v2_of_v1 p.1 p.2 rest h1)
      (fun h2 => parseDeltaBatchWith_v2 p.1 p.2 rest h2))
    (fun p hm => (h p hm).elim
      (fun h1 => serializeDeltaBatchWith?_ne_nil .v1 p.1 p.2
        (by rw [serializeDeltaBatchWith?_v1]; exact h1))
      (fun h2 => serializeDeltaBatchWith?_ne_nil .v2 p.1 p.2 h2))
  have h21 : (deltaLogVersion2 == deltaLogVersion) = false := by decide
  have h22 : (deltaLogVersion2 == deltaLogVersion2) = true := by decide
  unfold parseLog
  simp only [bind, Option.bind, hm, hv, hd, hr, bne_self_eq_false, Bool.false_eq_true, if_false,
    h21, h22, if_true]

theorem termNeedsV2_eq (t : Term) : termNeedsV2 t = !BlockWireV0.termSupported t := by
  cases t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal l =>
      simp only [termNeedsV2, BlockWireV0.termSupported]
      cases l.val.direction <;> rfl
  | tripleTerm _ _ _ => rfl

#print axioms DeltaTermCodec.v1_roundTrip
#print axioms DeltaTermCodec.v2_roundTrip
#print axioms parseTripleWith_serializeTripleWith?
#print axioms parseDeltaEntryPayloadWith_serializeDeltaEntryPayloadWith?
#print axioms parseFramedDeltaEntryWith_serializeFramedDeltaEntryWith?
#print axioms parseNFramedDeltaEntriesWith_flatten
#print axioms parseDeltaBatchBodyWith_serializeDeltaBatchBodyWith?
#print axioms parseDeltaBatchWith_serializeDeltaBatchWith?
#print axioms parseDeltaBatchWith_v2
#print axioms serializeDeltaBatchWith?_v1
#print axioms appendPlan?_v1
#print axioms termSupported_of_serializeTerm?
#print axioms DeltaTermCodec.v2_extends_v1
#print axioms serializeDeltaBatchWith?_extends
#print axioms parseDeltaBatchWith_v2_of_v1
#print axioms replayDeltaBatchesWith_frames
#print axioms parseLog_v2_of_frames
#print axioms termNeedsV2_eq

end L4Factoidal.Storage
