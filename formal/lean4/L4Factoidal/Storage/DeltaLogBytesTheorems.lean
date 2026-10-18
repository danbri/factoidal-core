/-
L4Factoidal.Storage.DeltaLogBytesTheorems — the byte-array delta log codec of
`Storage/DeltaLogBytes.lean` equals the specification of `Storage/DeltaLog.lean`.

Each decoder is proved equal to the list decoder on the window it reads
(`win b pos stop`), each encoder to the list encoder with the buffer in front:

* `readU32LE_win`, `readU64LE_win`: a read on a window is a read by position.
* `listOfRange_eq`, `sumRange_eq`: the range list and the range checksum.
* `parseEntry_win`, `entryAt_eq`: a DLE1 frame, with and without its payload.
* `entriesAt_eq`, `bodyAt_eq`, `parseDeltaBatchWith_win`: the entries, the body and
  the DLB1 frame of any term codec.
* `replayBatchesAt_eq`, `parseLog_eq`, `classifyAt_eq`: the replay, `parseLog` and
  `classifyTail`.
* `parseLogChecked_eq`, `parseLogCheckedV1_eq`: the readers of the SBM11 tools
  and of the IBK3 tools.
* `pushEntry?_eq`, `pushEntries?_eq`, `bodyBA?_eq`, `batchBA?_eq`,
  `appendPlanBA?_eq`: the encoder.

`parseLogChecked`, `parseLogCheckedV1` and `appendPlan?` are then replaced by
`@[csimp]` lemmas (`parseLogChecked_csimp`, `parseLogCheckedV1_csimp`,
`appendPlan?_csimp`), so that code which still passes a `List UInt8` runs the byte
array functions, and every theorem about the specification (the round trips of
`DeltaLogCodecTheorems`, the tail rules of `BrowserLogTheorems`) describes the
code that runs. The byte array functions also run directly in the SBM11 tools
(`Harness/Sbm11Delta.lean`, `Harness/Sbm11Update.lean`), which pass the file's
bytes without a list.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.DeltaLogBytes

namespace L4Factoidal.Storage.DeltaLogBytes

open L4Factoidal
open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## Windows -/

theorem length_data_toList (b : ByteArray) : b.data.toList.length = b.size := by
  simp only [Array.length_toList]; rfl

theorem win_nil (b : ByteArray) {pos stop : Nat} (h : stop ≤ pos) : win b pos stop = [] := by
  unfold win
  have : stop - pos = 0 := by omega
  rw [this, List.take_zero]

theorem win_length (b : ByteArray) {pos stop : Nat} (hs : stop ≤ b.size) :
    (win b pos stop).length = stop - pos := by
  unfold win
  rw [List.length_take, List.length_drop, length_data_toList]
  omega

theorem win_cons (b : ByteArray) {pos stop : Nat} (hp : pos < stop) (hs : stop ≤ b.size) :
    win b pos stop = b[pos]'(by omega) :: win b (pos + 1) stop := by
  unfold win
  have hl : pos < b.data.toList.length := by rw [length_data_toList]; omega
  rw [List.drop_eq_getElem_cons hl]
  have : stop - pos = (stop - (pos + 1)) + 1 := by omega
  rw [this, List.take_succ_cons]
  simp [ByteArray.getElem_eq_getElem_data]

theorem win_drop (b : ByteArray) (pos stop k : Nat) :
    (win b pos stop).drop k = win b (pos + k) stop := by
  unfold win
  rw [List.drop_take, List.drop_drop]
  congr 1
  omega

theorem win_take (b : ByteArray) {q stop n : Nat} (h : q + n ≤ stop) :
    (win b q stop).take n = win b q (q + n) := by
  unfold win
  rw [List.take_take]
  congr 1
  omega

/-- The window from the start of the array to its end is the whole list. -/
theorem win_zero_size (b : ByteArray) : win b 0 b.size = b.data.toList := by
  unfold win
  rw [List.drop_zero, Nat.sub_zero]
  exact List.take_of_length_le (by rw [length_data_toList]; exact Nat.le_refl _)

/-! ## Reads -/

theorem readU32LE_short (l : List UInt8) (h : l.length < 4) : readU32LE l 0 = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

theorem u32At?_some {b : ByteArray} {p stop : Nat} {v : UInt32} (h : u32At? b p stop = some v) :
    p + 4 ≤ stop ∧ stop ≤ b.size := by
  unfold u32At? at h
  split at h
  · rename_i hh; exact hh
  · cases h

/-- A read on a window is a read by position. -/
theorem readU32LE_win (b : ByteArray) (pos stop k : Nat) (hs : stop ≤ b.size) :
    readU32LE (win b pos stop) k = u32At? b (pos + k) stop := by
  unfold readU32LE
  rw [win_drop]
  by_cases h : pos + k + 4 ≤ stop
  · have e : win b (pos + k) stop =
        b[pos + k]'(by omega) :: b[pos + k + 1]'(by omega) :: b[pos + k + 2]'(by omega) ::
          b[pos + k + 3]'(by omega) :: win b (pos + k + 4) stop := by
      rw [win_cons b (by omega) hs, win_cons b (by omega) hs, win_cons b (by omega) hs,
        win_cons b (by omega) hs]
    rw [e]
    unfold u32At?
    rw [dif_pos ⟨h, hs⟩]
  · have hlen : (win b (pos + k) stop).length < 4 := by rw [win_length b hs]; omega
    unfold u32At?
    rw [dif_neg (by omega)]
    generalize win b (pos + k) stop = l at hlen ⊢
    match l, hlen with
    | [], _ => rfl
    | [_], _ => rfl
    | [_, _], _ => rfl
    | [_, _, _], _ => rfl

theorem readU64LE_win (b : ByteArray) (pos stop k : Nat) (hs : stop ≤ b.size) :
    readU64LE (win b pos stop) k = u64At? b (pos + k) stop := by
  unfold readU64LE u64At?
  rw [readU32LE_win b pos stop k hs, readU32LE_win b pos stop (k + 4) hs, ← Nat.add_assoc]

/-! ## The range list and the range checksum -/

theorem get!_eq_getElem (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  show b.data[i]! = b.data[i]
  rw [getElem!_pos]

theorem win_snoc (b : ByteArray) {s i : Nat} (h : s + i + 1 ≤ b.size) :
    win b s (s + (i + 1)) = win b s (s + i) ++ [b[s + i]'(by omega)] := by
  unfold win
  have e1 : s + (i + 1) - s = i + 1 := by omega
  have e2 : s + i - s = i := by omega
  rw [e1, e2, List.take_add_one]
  congr 1
  have hl : s + i < b.data.toList.length := by rw [length_data_toList]; omega
  rw [List.getElem?_drop, List.getElem?_eq_getElem hl]
  simp [ByteArray.getElem_eq_getElem_data]

theorem listOfRangeGo_eq (b : ByteArray) (s : Nat) :
    ∀ (i : Nat) (acc : List UInt8), s + i ≤ b.size →
      listOfRangeGo b s i acc = win b s (s + i) ++ acc
  | 0, acc, _ => by
      rw [listOfRangeGo, win_nil b (by omega)]; rfl
  | i + 1, acc, h => by
      rw [listOfRangeGo, listOfRangeGo_eq b s i _ (by omega), win_snoc b (by omega),
        get!_eq_getElem b (s + i) (by omega)]
      simp

theorem listOfRange_eq (b : ByteArray) {s e : Nat} (h : e ≤ b.size) :
    listOfRange b s e = win b s e := by
  unfold listOfRange
  by_cases hse : s ≤ e
  · have := listOfRangeGo_eq b s (e - s) [] (by omega)
    rw [List.append_nil] at this
    rw [this, Nat.add_sub_cancel' hse]
  · have : e - s = 0 := by omega
    rw [this, listOfRangeGo, win_nil b (by omega)]

theorem sumGo_eq (b : ByteArray) (e : Nat) (hs : e ≤ b.size) :
    ∀ (n i : Nat) (acc : UInt32), e - i = n →
      sumGo b e i acc = (win b i e).foldl (fun a x => a + x.toUInt32) acc
  | 0, i, acc, hn => by
      rw [sumGo, dif_neg (by omega), win_nil b (by omega)]; rfl
  | n + 1, i, acc, hn => by
      rw [sumGo, dif_pos ⟨by omega, hs⟩, win_cons b (by omega) hs, List.foldl_cons]
      exact sumGo_eq b e hs n (i + 1) _ (by omega)

/-- The range checksum is the checksum of the window. -/
theorem sumRange_eq (b : ByteArray) {s e : Nat} (h : e ≤ b.size) :
    sumRange b s e = simpleChecksum (win b s e) := by
  unfold sumRange simpleChecksum
  exact sumGo_eq b e h (e - s) s 0 rfl

/-! ## The DLE1 frame -/

theorem parseEntry_win (b : ByteArray) (pos stop : Nat) (hs : stop ≤ b.size) :
    parseEntry (win b pos stop) =
      (entryFrameAt? b pos stop).map (fun r => (win b (pos + 12) r.1, win b r.2 stop)) := by
  unfold parseEntry entryFrameAt?
  rw [readU32LE_win b pos stop 0 hs]
  simp only [Nat.add_zero]
  cases h0 : u32At? b pos stop with
  | none => rfl
  | some magic =>
    by_cases hm : (magic != deltaEntryMagic) = true
    · simp [hm]
    · simp only [hm, Bool.false_eq_true, if_false]
      rw [readU32LE_win b pos stop 4 hs]
      cases h1 : u32At? b (pos + 4) stop with
      | none => rfl
      | some ver =>
        by_cases hv : (ver != deltaEntryVersion) = true
        · simp [hv]
        · simp only [hv, Bool.false_eq_true, if_false]
          rw [readU32LE_win b pos stop 8 hs]
          cases h2 : u32At? b (pos + 8) stop with
          | none => rfl
          | some len =>
            have h12 : pos + 12 ≤ stop := by have := (u32At?_some h2).1; omega
            dsimp only
            rw [win_drop]
            have hlen : ((win b (pos + 12) stop).take len.toNat).length =
                min len.toNat (stop - (pos + 12)) := by
              rw [List.length_take, win_length b hs]
            by_cases hfit : pos + 12 + len.toNat ≤ stop
            · have hp : (((win b (pos + 12) stop).take len.toNat).length != len.toNat) = false := by
                rw [hlen]; simp <;> omega
              rw [if_neg (by rw [hp]; simp), if_pos hfit]
              rw [readU32LE_win b (pos + 12) stop len.toNat hs]
              cases h3 : u32At? b (pos + 12 + len.toNat) stop with
              | none => rfl
              | some stored =>
                rw [win_take b hfit, ← sumRange_eq b (by omega)]
                by_cases hc : (stored != sumRange b (pos + 12) (pos + 12 + len.toNat)) = true
                · simp [hc]
                · simp only [hc, Bool.false_eq_true, if_false, Option.map_some]
                  rw [win_drop, win_drop]
            · have hp : (((win b (pos + 12) stop).take len.toNat).length != len.toNat) = true := by
                rw [hlen]; simp <;> omega
              rw [if_pos hp, if_neg hfit]
              rfl

theorem entryFrameAt?_le {b : ByteArray} {pos stop e next : Nat}
    (h : entryFrameAt? b pos stop = some (e, next)) :
    pos + 12 ≤ e ∧ next = e + 4 ∧ next ≤ stop ∧ stop ≤ b.size := by
  unfold entryFrameAt? at h
  split at h
  · cases h
  · rename_i magic h0
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ver h1
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i len h2
            dsimp only at h
            split at h
            · rename_i hle
              split at h
              · cases h
              · rename_i stored h3
                split at h
                · cases h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have := u32At?_some h3
                  omega
            · cases h

/-- A DLE1 frame and its entry. -/
theorem entryAt_eq (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) (hs : stop ≤ b.size) :
    parseFramedDeltaEntryWith tc (win b pos stop) =
      (entryAt tc b pos stop).map (fun r => (r.1, win b r.2 stop)) := by
  unfold parseFramedDeltaEntryWith entryAt
  rw [parseEntry_win b pos stop hs]
  cases h : entryFrameAt? b pos stop with
  | none => rfl
  | some r =>
    obtain ⟨e, next⟩ := r
    have hle := entryFrameAt?_le h
    simp only [Option.map_some, bind, Option.bind]
    rw [listOfRange_eq b (by omega)]
    cases hp : parseDeltaEntryPayloadWith tc (win b (pos + 12) e) with
    | none => rfl
    | some q =>
      obtain ⟨entry, rest⟩ := q
      simp only
      by_cases hr : rest.isEmpty = true
      · simp [hr]
      · simp [hr]

/-! ## The entries, the body and the DLB1 frame -/

theorem entriesAt_eq (tc : DeltaTermCodec) (b : ByteArray) (stop : Nat) (hs : stop ≤ b.size) :
    ∀ (n pos : Nat) (acc : List DeltaEntry),
      parseNFramedDeltaEntriesWith tc n (win b pos stop) acc =
        (entriesAt tc b stop n pos acc).map (fun r => (r.1, win b r.2 stop))
  | 0, pos, acc => by simp [parseNFramedDeltaEntriesWith, entriesAt]
  | n + 1, pos, acc => by
      simp only [parseNFramedDeltaEntriesWith, entriesAt]
      rw [entryAt_eq tc b pos stop hs]
      cases h : entryAt tc b pos stop with
      | none => rfl
      | some r =>
        obtain ⟨e, next⟩ := r
        simp only [Option.map_some]
        exact entriesAt_eq tc b stop hs n next (e :: acc)

theorem win_isEmpty (b : ByteArray) (p stop : Nat) (hs : stop ≤ b.size) :
    (win b p stop).isEmpty = decide (stop ≤ p) := by
  by_cases h : stop ≤ p
  · rw [win_nil b h]; simp [h]
  · have hl := win_length b (pos := p) hs
    cases hw : win b p stop with
    | nil => rw [hw] at hl; simp at hl; omega
    | cons x xs => simp [h]

/-- The body of a DLB1 frame. -/
theorem bodyAt_eq (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) (hs : stop ≤ b.size) :
    parseDeltaBatchBodyWith tc (win b pos stop) = bodyAt tc b pos stop := by
  unfold parseDeltaBatchBodyWith bodyAt
  rw [readU64LE_win b pos stop 0 hs, readU64LE_win b pos stop 8 hs, readU32LE_win b pos stop 16 hs,
    win_drop]
  simp only [Nat.add_zero, bind, Option.bind, entriesAt_eq tc b stop hs]
  cases h0 : u64At? b pos stop with
  | none => rfl
  | some seq =>
    cases h1 : u64At? b (pos + 8) stop with
    | none => rfl
    | some epoch =>
      cases h2 : u32At? b (pos + 16) stop with
      | none => rfl
      | some count =>
        dsimp only
        cases h3 : entriesAt tc b stop count.toNat (pos + 20) [] with
        | none => rfl
        | some r =>
          obtain ⟨ops, p⟩ := r
          simp only [Option.map_some, win_isEmpty b p stop hs]
          by_cases hp : stop ≤ p <;> simp [hp]

theorem batchFrameAt?_le {b : ByteArray} {pos stop e next : Nat}
    (h : batchFrameAt? b pos stop = some (e, next)) :
    pos + 12 ≤ e ∧ next = e + 4 ∧ next ≤ stop ∧ stop ≤ b.size := by
  unfold batchFrameAt? at h
  split at h
  · cases h
  · rename_i magic h0
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ver h1
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i len h2
            dsimp only at h
            split at h
            · rename_i hle
              split at h
              · cases h
              · rename_i stored h3
                split at h
                · cases h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have := u32At?_some h3
                  omega
            · cases h

/-- The DLB1 frame of any term codec. -/
theorem parseDeltaBatchWith_win (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat)
    (hs : stop ≤ b.size) :
    parseDeltaBatchWith tc (win b pos stop) =
      (batchAt tc b pos stop).map (fun r => (r.1, win b r.2 stop)) := by
  unfold parseDeltaBatchWith batchAt batchFrameAt?
  rw [readU32LE_win b pos stop 0 hs]
  simp only [Nat.add_zero, bind, Option.bind]
  cases h0 : u32At? b pos stop with
  | none => rfl
  | some magic =>
    dsimp only
    by_cases hm : (magic != deltaBatchMagic) = true
    · simp only [hm, if_true]; rfl
    · simp only [hm, Bool.false_eq_true, if_false]
      rw [readU32LE_win b pos stop 4 hs]
      cases h1 : u32At? b (pos + 4) stop with
      | none => rfl
      | some ver =>
        dsimp only
        by_cases hv : (ver != deltaBatchVersion) = true
        · simp only [hv, if_true]; rfl
        · simp only [hv, Bool.false_eq_true, if_false]
          rw [readU32LE_win b pos stop 8 hs]
          cases h2 : u32At? b (pos + 8) stop with
          | none => rfl
          | some len =>
            dsimp only
            have h12 : pos + 12 ≤ stop := by have := (u32At?_some h2).1; omega
            rw [win_drop]
            have hlen : ((win b (pos + 12) stop).take len.toNat).length =
                min len.toNat (stop - (pos + 12)) := by
              rw [List.length_take, win_length b hs]
            by_cases hfit : pos + 12 + len.toNat ≤ stop
            · have hp : (((win b (pos + 12) stop).take len.toNat).length != len.toNat) = false := by
                rw [hlen]; simp <;> omega
              rw [if_neg (by rw [hp]; simp), if_pos hfit]
              rw [readU32LE_win b (pos + 12) stop len.toNat hs]
              cases h3 : u32At? b (pos + 12 + len.toNat) stop with
              | none => rfl
              | some stored =>
                dsimp only
                rw [win_take b hfit, ← sumRange_eq b (by omega)]
                by_cases hc : (stored != sumRange b (pos + 12) (pos + 12 + len.toNat)) = true
                · simp only [hc, if_true]; rfl
                · simp only [hc, Bool.false_eq_true, if_false]
                  rw [bodyAt_eq tc b (pos + 12) (pos + 12 + len.toNat) (by omega)]
                  cases hb : bodyAt tc b (pos + 12) (pos + 12 + len.toNat) with
                  | none => rfl
                  | some batch =>
                    dsimp only
                    simp only [Option.map_some]
                    rw [win_drop, win_drop]
            · have hp : (((win b (pos + 12) stop).take len.toNat).length != len.toNat) = true := by
                rw [hlen]; simp <;> omega
              rw [if_pos hp, if_neg hfit]
              rfl

/-! ## Version 1 is the codec of the specification's own functions -/

theorem parseNFramedDeltaEntriesWith_v1 :
    ∀ (n : Nat) (bs : List UInt8) (acc : List DeltaEntry),
      parseNFramedDeltaEntriesWith .v1 n bs acc = parseNFramedDeltaEntriesLoop n bs acc
  | 0, bs, acc => rfl
  | n + 1, bs, acc => by
      simp only [parseNFramedDeltaEntriesWith, parseNFramedDeltaEntriesLoop]
      show (match parseFramedDeltaEntry bs with
          | none => none
          | some (e, rest) => parseNFramedDeltaEntriesWith .v1 n rest (e :: acc)) = _
      cases parseFramedDeltaEntry bs with
      | none => rfl
      | some r =>
        obtain ⟨e, rest⟩ := r
        exact parseNFramedDeltaEntriesWith_v1 n rest (e :: acc)

theorem parseNFramedDeltaEntries_v1 (n : Nat) (bs : List UInt8) :
    parseNFramedDeltaEntries n bs = parseNFramedDeltaEntriesWith .v1 n bs [] := by
  rw [parseNFramedDeltaEntriesWith_v1]
  have := congrFun (congrFun parseNFramedDeltaEntries_eq_fast n) bs
  rw [this]
  rfl

theorem parseDeltaBatchBody_v1 (bs : List UInt8) :
    parseDeltaBatchBody bs = parseDeltaBatchBodyWith .v1 bs := by
  unfold parseDeltaBatchBody parseDeltaBatchBodyWith
  simp only [parseNFramedDeltaEntries_v1]

theorem parseDeltaBatch_v1 (bs : List UInt8) :
    parseDeltaBatch bs = parseDeltaBatchWith .v1 bs := by
  unfold parseDeltaBatch parseDeltaBatchWith
  simp only [parseDeltaBatchBody_v1]

theorem replayDeltaBatches_v1 (bs : List UInt8) :
    replayDeltaBatches bs = replayDeltaBatchesWith .v1 bs := by
  have key : ∀ (fuel : Nat) (remaining : List UInt8) (acc : List DeltaBatch),
      replayDeltaBatches.go fuel remaining acc = replayDeltaBatchesWith.go .v1 fuel remaining acc := by
    intro fuel
    induction fuel with
    | zero => intro remaining acc; rfl
    | succ fuel ih =>
      intro remaining acc
      rw [replayDeltaBatches.go, replayDeltaBatchesWith.go]
      by_cases hr : remaining.isEmpty = true
      · simp [hr]
      · simp only [hr, Bool.false_eq_true, if_false]
        rw [parseDeltaBatch_v1]
        cases parseDeltaBatchWith .v1 remaining with
        | none => rfl
        | some r => obtain ⟨batch, rest⟩ := r; exact ih rest (batch :: acc)
  unfold replayDeltaBatches replayDeltaBatchesWith
  rw [key]

/-! ## The replay, `parseLog` and `classifyTail` -/

theorem replayGo_eq (tc : DeltaTermCodec) (b : ByteArray) (stop : Nat) (hs : stop ≤ b.size) :
    ∀ (fuel pos : Nat) (acc : List DeltaBatch),
      replayDeltaBatchesWith.go tc fuel (win b pos stop) acc =
        ((replayGo tc b stop fuel pos acc).1, win b (replayGo tc b stop fuel pos acc).2 stop)
  | 0, pos, acc => by
      rw [replayDeltaBatchesWith.go, replayGo]
  | fuel + 1, pos, acc => by
      rw [replayDeltaBatchesWith.go, replayGo, win_isEmpty b pos stop hs]
      by_cases hp : stop ≤ pos
      · simp [hp, win_nil b hp]
      · simp only [hp, decide_false, Bool.false_eq_true, if_false]
        rw [parseDeltaBatchWith_win tc b pos stop hs]
        cases h : batchAt tc b pos stop with
        | none => rfl
        | some r =>
          obtain ⟨batch, next⟩ := r
          simp only [Option.map_some]
          exact replayGo_eq tc b stop hs fuel next (batch :: acc)

theorem replayBatchesAt_eq (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat)
    (hs : stop ≤ b.size) :
    replayDeltaBatchesWith tc (win b pos stop) =
      ((replayBatchesAt tc b pos stop).1, win b (replayBatchesAt tc b pos stop).2 stop) := by
  unfold replayDeltaBatchesWith replayBatchesAt
  rw [win_length b hs, replayGo_eq tc b stop hs]

theorem win_end (b : ByteArray) (p : Nat) : win b p b.size = b.data.toList.drop p := by
  unfold win
  exact List.take_of_length_le (by rw [List.length_drop, length_data_toList]; omega)

theorem parseLog_eq (b : ByteArray) :
    parseLog b.data.toList = (parseLogAt b).map (fun r => (r.1, b.data.toList.drop r.2)) := by
  have hs : b.size ≤ b.size := Nat.le_refl _
  rw [← win_zero_size b]
  unfold parseLog parseLogAt
  rw [readU32LE_win b 0 b.size 0 hs]
  simp only [Nat.zero_add, bind, Option.bind]
  cases h0 : u32At? b 0 b.size with
  | none => rfl
  | some magic =>
    dsimp only
    by_cases hm : (magic != deltaLogMagic) = true
    · simp only [hm, if_true]; rfl
    · simp only [hm, Bool.false_eq_true, if_false]
      rw [readU32LE_win b 0 b.size 4 hs]
      cases h1 : u32At? b 4 b.size with
      | none => rfl
      | some version =>
        dsimp only
        by_cases h1' : (version == deltaLogVersion) = true
        · simp only [h1', if_true, Option.map_some]
          rw [win_drop, replayDeltaBatches_v1, replayBatchesAt_eq .v1 b 8 b.size hs, win_end, win_zero_size]
        · simp only [h1', Bool.false_eq_true, if_false]
          by_cases h2' : (version == deltaLogVersion2) = true
          · simp only [h2', if_true, Option.map_some]
            rw [win_drop, replayBatchesAt_eq .v2 b 8 b.size hs, win_end, win_zero_size]
          · simp only [h2', Bool.false_eq_true, if_false]
            by_cases h3' : (version == deltaLogVersion3) = true
            · simp only [h3', if_true, Option.map_some]
              rw [win_drop, replayBatchesAt_eq .v3 b 8 b.size hs, win_end, win_zero_size]
            · simp only [h3', Bool.false_eq_true, if_false]
              rfl

theorem win_take_min (b : ByteArray) (q stop n : Nat) :
    (win b q stop).take n = win b q (min stop (q + n)) := by
  unfold win
  rw [List.take_take]
  congr 1
  omega

theorem classifyAt_eq (b : ByteArray) (p : Nat) :
    classifyTail (win b p b.size) = classifyAt b p := by
  have hs : b.size ≤ b.size := Nat.le_refl _
  by_cases hp : b.size ≤ p
  · rw [win_nil b hp]; simp [classifyAt, classifyTail, hp]
  · have hcons : win b p b.size = b[p]'(by omega) :: win b (p + 1) b.size := win_cons b (by omega) hs
    unfold classifyAt
    rw [if_neg hp]
    unfold classifyTail
    split
    · rename_i h; rw [hcons] at h; cases h
    · rename_i x xs hx
      rw [readU32LE_win b p b.size 8 hs]
      cases h8 : u32At? b (p + 8) b.size with
      | none =>
        dsimp only
        rw [win_take_min, listOfRange_eq b (by omega)]
      | some len =>
        dsimp only
        have h12 : p + 12 ≤ b.size := by have := (u32At?_some h8).1; omega
        rw [win_take b (q := p) (n := 8) (stop := b.size) (by omega), listOfRange_eq b (by omega)]
        by_cases hf : (win b p (p + 8) != batchFrameStart) = true
        · simp only [hf, if_true]
        · simp only [hf, Bool.false_eq_true, if_false]
          rw [win_length b hs]
          by_cases hl : b.size - p < 16 + len.toNat
          · simp only [hl, if_true]
          · simp only [hl, if_false]
            rw [win_drop, readU32LE_win b (p + 12) b.size len.toNat hs,
              win_take b (q := p + 12) (n := len.toNat) (stop := b.size) (by omega),
              ← sumRange_eq b (by omega)]

theorem logHeaderVersion_eq (b : ByteArray) :
    logHeaderVersion? b.data.toList = logHeaderVersionAt? b := by
  have hs : b.size ≤ b.size := Nat.le_refl _
  rw [← win_zero_size b]
  unfold logHeaderVersion? logHeaderVersionAt?
  rw [readU32LE_win b 0 b.size 0 hs]
  simp only [Nat.zero_add, bind, Option.bind]
  cases h0 : u32At? b 0 b.size with
  | none => rfl
  | some magic =>
    dsimp only
    by_cases hm : (magic != deltaLogMagic) = true
    · simp [hm]
    · simp only [hm, Bool.false_eq_true, if_false]
      rw [readU32LE_win b 0 b.size 4 hs]

theorem parseLogChecked_eq (b : ByteArray) :
    parseLogChecked b.data.toList = parseLogCheckedBA b := by
  unfold parseLogChecked parseLogCheckedBA
  rw [parseLog_eq]
  cases h : parseLogAt b with
  | none => rfl
  | some r =>
    obtain ⟨batches, p⟩ := r
    simp only [Option.map_some]
    rw [← win_end b p, classifyAt_eq]
    have hl : (win b p b.size).length = b.size - p := win_length b (Nat.le_refl _)
    rw [hl, length_data_toList]
    rfl

theorem parseLogCheckedV1_eq (b : ByteArray) :
    parseLogCheckedV1 b.data.toList = parseLogCheckedV1BA b := by
  unfold parseLogCheckedV1 parseLogCheckedV1BA
  rw [logHeaderVersion_eq, parseLogChecked_eq]
  cases v1Refusal? (logHeaderVersionAt? b) <;> rfl

/-! ## The encoder -/

theorem pushU32_data (out : ByteArray) (n : UInt32) :
    (pushU32 out n).data.toList = out.data.toList ++ writeU32LE n := by
  simp [pushU32, writeU32LE, ByteArray.data_push, Array.toList_push]

theorem pushU64_data (out : ByteArray) (n : UInt64) :
    (pushU64 out n).data.toList = out.data.toList ++ writeU64LE n := by
  simp only [pushU64, writeU64LE, pushU32_data, List.append_assoc]

theorem pushList_data : ∀ (l : List UInt8) (out : ByteArray),
    (pushList out l).data.toList = out.data.toList ++ l
  | [], out => by simp [pushList]
  | x :: xs, out => by
      simp [pushList, pushList_data xs, ByteArray.data_push, Array.toList_push]

theorem pushEntryFrame_data (out : ByteArray) (payload : List UInt8) :
    (pushEntryFrame out payload).data.toList = out.data.toList ++ frameEntry payload := by
  simp [pushEntryFrame, frameEntry, pushU32_data, pushList_data, List.append_assoc]

theorem pushEntry?_eq (tc : DeltaTermCodec) (out : ByteArray) (e : DeltaEntry) :
    (pushEntry? tc out e).map (·.data.toList) =
      (serializeFramedDeltaEntryWith? tc e).map (out.data.toList ++ ·) := by
  unfold pushEntry? serializeFramedDeltaEntryWith? frameEntry?
  cases h : serializeDeltaEntryPayloadWith? tc e with
  | none => rfl
  | some payload =>
    by_cases hl : payload.length < UInt32.size
    · simp [hl, pushEntryFrame_data]
    · simp [hl]

theorem pushEntries?_eq (tc : DeltaTermCodec) :
    ∀ (es : List DeltaEntry) (out : ByteArray),
      (pushEntries? tc out es).map (·.data.toList) =
        (es.mapM (serializeFramedDeltaEntryWith? tc)).map (fun l => out.data.toList ++ l.flatten)
  | [], out => by simp [pushEntries?]
  | e :: es, out => by
      rw [pushEntries?, List.mapM_cons]
      have h1 := pushEntry?_eq tc out e
      cases h : pushEntry? tc out e with
      | none =>
        rw [h] at h1
        cases hs : serializeFramedDeltaEntryWith? tc e with
        | none => rfl
        | some f => rw [hs] at h1; simp at h1
      | some out' =>
        rw [h] at h1
        cases hs : serializeFramedDeltaEntryWith? tc e with
        | none => rw [hs] at h1; simp at h1
        | some f =>
          rw [hs] at h1
          simp only [Option.map_some, Option.some.injEq] at h1
          have ih := pushEntries?_eq tc es out'
          simp only [bind, Option.bind, pure]
          cases hm : es.mapM (serializeFramedDeltaEntryWith? tc) with
          | none => rw [hm] at ih; simpa using ih
          | some fs =>
            rw [hm] at ih
            simp only [Option.map_some] at ih ⊢
            rw [ih, h1]
            simp [List.append_assoc]

theorem emptyWithCapacity_data (c : Nat) : (ByteArray.emptyWithCapacity c).data.toList = [] := by
  show (Array.emptyWithCapacity c).toList = []
  rfl

theorem bodyBA?_eq (tc : DeltaTermCodec) (b : DeltaBatch) :
    (bodyBA? tc b).map (·.data.toList) = serializeDeltaBatchBodyWith? tc b := by
  unfold bodyBA? serializeDeltaBatchBodyWith?
  by_cases hg : (!natFitsU64 b.seq || !natFitsU64 b.epoch || b.ops.length >= two32) = true
  · simp [hg]
  · simp only [hg, Bool.false_eq_true, if_false]
    rw [pushEntries?_eq]
    cases hm : b.ops.mapM (serializeFramedDeltaEntryWith? tc) with
    | none => rfl
    | some entries =>
      simp [pushU32_data, pushU64_data, emptyWithCapacity_data, List.append_assoc]

theorem sumRange_whole (body : ByteArray) :
    sumRange body 0 body.size = simpleChecksum body.data.toList := by
  rw [sumRange_eq body (Nat.le_refl _), win_zero_size]

theorem pushBatchFrame_data (pre body : ByteArray) :
    (pushBatchFrame pre body).data.toList = pre.data.toList ++
      (writeU32LE deltaBatchMagic ++ writeU32LE deltaBatchVersion ++
        writeU32LE (UInt32.ofNat body.data.toList.length) ++ body.data.toList ++
        writeU32LE (simpleChecksum body.data.toList)) := by
  unfold pushBatchFrame
  rw [pushU32_data, sumRange_whole]
  simp [pushU32_data, List.append_assoc]

theorem batchBA?_eq (tc : DeltaTermCodec) (pre : ByteArray) (b : DeltaBatch) :
    (batchBA? tc pre b).map (·.data.toList) =
      (serializeDeltaBatchWith? tc b).map (pre.data.toList ++ ·) := by
  unfold batchBA? serializeDeltaBatchWith?
  have h := bodyBA?_eq tc b
  cases hb : bodyBA? tc b with
  | none =>
    rw [hb] at h
    simp only [Option.map_none] at h
    rw [← h]; rfl
  | some body =>
    rw [hb] at h
    simp only [Option.map_some] at h
    rw [← h]
    simp only [bind, Option.bind]
    by_cases hz : body.size >= two32
    · have : body.data.toList.length >= two32 := by rw [length_data_toList]; exact hz
      simp [hz]
    · have : ¬ body.data.toList.length >= two32 := by rw [length_data_toList]; exact hz
      simp [hz, pushBatchFrame_data]

theorem logHeaderBA_data (version : UInt32) :
    (logHeaderBA version).data.toList = logHeader version := by
  simp [logHeaderBA, logHeader, pushU32_data]

theorem appendPlanBA?_eq (logVersion : Option UInt32) (batch : DeltaBatch) :
    (appendPlanBA? logVersion batch).map (fun p => (p.version, p.setVersion, p.bytes.data.toList)) =
      (appendPlan? logVersion batch).map (fun p => (p.version, p.setVersion, p.bytes)) := by
  unfold appendPlanBA? appendPlan?
  dsimp only
  generalize appendVersion logVersion batch = version
  cases hv : DeltaTermCodec.ofVersion version with
  | none => rfl
  | some tc =>
    dsimp only
    have h := batchBA?_eq tc ByteArray.empty batch
    have h' := batchBA?_eq tc (logHeaderBA version) batch
    rw [logHeaderBA_data] at h'
    cases logVersion with
    | none =>
      dsimp only
      cases hb : batchBA? tc (logHeaderBA version) batch with
      | none =>
        rw [hb] at h'
        cases hs : serializeDeltaBatchWith? tc batch with
        | none => simp [bind, Option.bind]
        | some f => rw [hs] at h'; simp at h'
      | some bytes =>
        rw [hb] at h'
        cases hs : serializeDeltaBatchWith? tc batch with
        | none => rw [hs] at h'; simp at h'
        | some f =>
          rw [hs] at h'
          simp only [Option.map_some, Option.some.injEq] at h'
          simp [bind, Option.bind, h']
    | some v =>
      dsimp only
      cases hb : batchBA? tc ByteArray.empty batch with
      | none =>
        rw [hb] at h
        cases hs : serializeDeltaBatchWith? tc batch with
        | none => simp [bind, Option.bind]
        | some f => rw [hs] at h; simp at h
      | some bytes =>
        rw [hb] at h
        cases hs : serializeDeltaBatchWith? tc batch with
        | none => rw [hs] at h; simp at h
        | some f =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          simp [bind, Option.bind, h]

/-! ## `csimp`: code that passes a list runs the byte array functions -/

/-- `appendPlan?` through `appendPlanBA?`: the bytes of the plan as a list at
    the end, for a caller that wants a list. -/
def appendPlanViaBA (logVersion : Option UInt32) (batch : DeltaBatch) : Option AppendPlan :=
  (appendPlanBA? logVersion batch).map fun p =>
    { version := p.version, setVersion := p.setVersion, bytes := p.bytes.data.toList }

theorem appendPlan?_eq_viaBA (logVersion : Option UInt32) (batch : DeltaBatch) :
    appendPlan? logVersion batch = appendPlanViaBA logVersion batch := by
  have h := appendPlanBA?_eq logVersion batch
  unfold appendPlanViaBA
  cases hb : appendPlanBA? logVersion batch with
  | none =>
    rw [hb] at h
    cases ha : appendPlan? logVersion batch with
    | none => rfl
    | some q => rw [ha] at h; simp at h
  | some p =>
    rw [hb] at h
    cases ha : appendPlan? logVersion batch with
    | none => rw [ha] at h; simp at h
    | some q =>
      rw [ha] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      cases q
      simp only [Option.map_some, Option.some.injEq, AppendPlan.mk.injEq]
      exact ⟨h1.symm, h2.symm, h3.symm⟩

@[csimp] theorem appendPlan?_csimp : @appendPlan? = @appendPlanViaBA := by
  funext logVersion batch
  exact appendPlan?_eq_viaBA logVersion batch

def parseLogCheckedViaBA (bs : List UInt8) : Except String (List DeltaBatch × Bool) :=
  parseLogCheckedBA ⟨bs.toArray⟩

theorem parseLogChecked_eq_viaBA (bs : List UInt8) :
    parseLogChecked bs = parseLogCheckedViaBA bs := by
  have := parseLogChecked_eq ⟨bs.toArray⟩
  simpa [parseLogCheckedViaBA] using this

@[csimp] theorem parseLogChecked_csimp : @parseLogChecked = @parseLogCheckedViaBA := by
  funext bs
  exact parseLogChecked_eq_viaBA bs

def parseLogCheckedV1ViaBA (bs : List UInt8) : Except String (List DeltaBatch × Bool) :=
  parseLogCheckedV1BA ⟨bs.toArray⟩

theorem parseLogCheckedV1_eq_viaBA (bs : List UInt8) :
    parseLogCheckedV1 bs = parseLogCheckedV1ViaBA bs := by
  have := parseLogCheckedV1_eq ⟨bs.toArray⟩
  simpa [parseLogCheckedV1ViaBA] using this

@[csimp] theorem parseLogCheckedV1_csimp : @parseLogCheckedV1 = @parseLogCheckedV1ViaBA := by
  funext bs
  exact parseLogCheckedV1_eq_viaBA bs

#print axioms readU32LE_win
#print axioms listOfRange_eq
#print axioms sumRange_eq
#print axioms parseEntry_win
#print axioms entryAt_eq
#print axioms entriesAt_eq
#print axioms bodyAt_eq
#print axioms parseDeltaBatchWith_win
#print axioms replayDeltaBatches_v1
#print axioms replayBatchesAt_eq
#print axioms parseLog_eq
#print axioms classifyAt_eq
#print axioms parseLogChecked_eq
#print axioms parseLogCheckedV1_eq
#print axioms pushEntry?_eq
#print axioms pushEntries?_eq
#print axioms bodyBA?_eq
#print axioms batchBA?_eq
#print axioms appendPlanBA?_eq
#print axioms appendPlan?_csimp
#print axioms parseLogChecked_csimp
#print axioms parseLogCheckedV1_csimp

end L4Factoidal.Storage.DeltaLogBytes
