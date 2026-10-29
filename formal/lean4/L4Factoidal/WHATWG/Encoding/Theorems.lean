/-
L4Factoidal.WHATWG.Encoding.Theorems — the UTF-8 encoder and decoder of the
Encoding Standard against Lean core's UTF-8.

Specifications:

  * Encoding Standard, WHATWG, commit be17ac5c (2026-10-19)
    (https://github.com/whatwg/encoding, commit
    `be17ac5c49881336538acfc7b40dba3c8009144b`): section 8.1.1 "UTF-8 decoder"
    (`utf8Handle` in `Core.lean`), section 8.1.2 "UTF-8 encoder"
    (`utf8EncodeCp`), section 6 "UTF-8 decode without BOM or fail"
    (`utf8DecodeWithoutBOMOrFail`).
  * Lean 4 core v4.33.1 String.utf8EncodeChar (`Init/Prelude.lean`), the
    encoding that `String.toUTF8` produces.

Theorems:

  * `utf8EncodeCp_eq_utf8EncodeChar`: the encoder of section 8.1.2 gives the
    same bytes as `String.utf8EncodeChar` for every Unicode scalar value.
  * `utf8_decode_encodeChar`: the decoder handler of section 8.1.1, given the
    bytes of one character one at a time, gives that character's code point
    and returns to its initial state, with no error and no restored byte.
    The proof uses the validity of `Char` (no surrogate D800-DFFF, at most
    10FFFF): the lead byte ED is followed by a byte at most 9F, the lead byte
    F4 by a byte at most 8F.
  * `utf8_decode_encodeList`: the same for a list of characters.
  * `utf8DecodeWithoutBOMOrFail_toUTF8`: "UTF-8 decode without BOM or fail"
    of the UTF-8 bytes of a Lean string gives that string.

`runHandle` is the reference run of the handler used in the statements: it
feeds the bytes with `some b`, and fails on a restored byte, an error or a
finished result.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.Encoding

/-! ## Facts about `Char` and arithmetic helpers -/

theorem char_toNat_lt (c : Char) : c.val.toNat < 0x110000 := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  omega

theorem char_not_surrogate (c : Char) : c.val.toNat < 0xD800 ∨ 0xDFFF < c.val.toNat := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  omega

private theorem and31 (x : Nat) : x &&& 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5
private theorem and15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4
private theorem and7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
private theorem and63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6
private theorem shl_or_mod (a r : Nat) (ha : a < 67108864) (hr : r < 64) :
    a <<< 6 % 4294967296 ||| r = a * 64 + r := by
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  exact (Nat.two_pow_add_eq_or_of_lt (i := 6) hr a).symm

private theorem or128 (r : Nat) (h : r < 64) : 128 ||| r = 128 + r :=
  (Nat.two_pow_add_eq_or_of_lt (i := 6) h 2).symm

private theorem range2 : List.range 2 = [0, 1] := rfl
private theorem range3 : List.range 3 = [0, 1, 2] := rfl

local macro "byte_bound" : tactic => `(tactic| (simp only [UInt8.toNat_ofNat', UInt8.reduceToNat, Nat.reducePow]; omega))

local macro "bound_if" : tactic => `(tactic| (split <;> rename_i h <;>
  (try simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', UInt8.reduceToNat, Nat.reducePow] at h) <;>
  simp only [UInt8.toNat_ofNat', UInt8.reduceToNat, Nat.reducePow] <;> omega))

/-! ## The encoder of section 8.1.2 equals `String.utf8EncodeChar` -/

theorem utf8EncodeCp_eq_utf8EncodeChar (c : Char) : utf8EncodeCp c.val = String.utf8EncodeChar c := by
  have hlt := char_toNat_lt c
  unfold String.utf8EncodeChar
  generalize c.val = n at hlt ⊢
  by_cases h1 : n.toNat ≤ 127
  · simp [utf8EncodeCp, UInt32.le_iff_toNat_le, h1]
  by_cases h2 : n.toNat ≤ 2047
  · simp [utf8EncodeCp, UInt32.le_iff_toNat_le, h1, h2]
    simp only [← UInt8.toNat_inj, UInt8.toNat_add, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow, and63, Nat.reduceMod, Nat.reducePow]
    refine ⟨by omega, ?_⟩
    rw [or128 _ (by omega)]; omega
  by_cases h3 : n.toNat ≤ 65535
  · simp [utf8EncodeCp, UInt32.le_iff_toNat_le, h1, h2, h3, range2]
    simp only [← UInt8.toNat_inj, UInt8.toNat_add, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow, and63, Nat.reduceMod, Nat.reducePow]
    refine ⟨by omega, ?_, ?_⟩
    · rw [or128 _ (by omega)]; omega
    · rw [or128 _ (by omega)]; omega
  · simp [utf8EncodeCp, UInt32.le_iff_toNat_le, h1, h2, h3, range3]
    simp only [← UInt8.toNat_inj, UInt8.toNat_add, UInt8.toNat_or, UInt8.toNat_and, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow, and63, Nat.reduceMod, Nat.reducePow]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [or128 _ (by omega)]; omega
    · rw [or128 _ (by omega)]; omega
    · rw [or128 _ (by omega)]; omega

/-! ## The handler run -/

/-- Feed the bytes to `Decoder.handle` one at a time with `some b`. The result
is `none` if a step restores bytes or returns `error` or `finished`; items
are collected in order, `cont` is skipped. -/
def runHandle : Decoder → List UInt8 → Option (Decoder × List UInt32)
  | d, [] => some (d, [])
  | d, b :: bs =>
    let s := d.handle (some b)
    if s.restore.isEmpty then
      match s.result with
      | .items cps =>
        match runHandle s.dec bs with
        | some (d', out) => some (d', cps ++ out)
        | none => none
      | .cont => runHandle s.dec bs
      | .error => none
      | .finished => none
    else none

theorem runHandle_cont {d d' : Decoder} {b : UInt8} (bs : List UInt8)
    (h : d.handle (some b) = ⟨d', .cont, []⟩) : runHandle d (b :: bs) = runHandle d' bs := by
  simp [runHandle, h]

theorem runHandle_items {d d' : Decoder} {b : UInt8} {cps : List UInt32} (bs : List UInt8)
    (h : d.handle (some b) = ⟨d', .items cps, []⟩) :
    runHandle d (b :: bs) = (runHandle d' bs).map fun r => (r.1, cps ++ r.2) := by
  simp only [runHandle, h, List.isEmpty_nil, if_true]
  cases runHandle d' bs <;> rfl

theorem handle_ascii (b : UInt8) (h : b.toNat ≤ 0x7F) :
    utf8Initial.handle (some b) = ⟨utf8Initial, .items [b.toUInt32], []⟩ := by
  have : b ≤ 0x7F := by rw [UInt8.le_iff_toNat_le]; exact h
  simp [utf8Initial, Decoder.handle, utf8Handle, this]

theorem handle_lead2 (b : UInt8) (h1 : 0xC2 ≤ b.toNat) (h2 : b.toNat ≤ 0xDF) :
    utf8Initial.handle (some b) = ⟨.utf8 (b &&& 0x1F).toUInt32 0 1 0x80 0xBF, .cont, []⟩ := by
  have a1 : ¬ b ≤ 0x7F := by rw [UInt8.le_iff_toNat_le]; simp; omega
  have a2 : 0xC2 ≤ b := by rw [UInt8.le_iff_toNat_le]; simpa using h1
  have a3 : b ≤ 0xDF := by rw [UInt8.le_iff_toNat_le]; simpa using h2
  simp [utf8Initial, Decoder.handle, utf8Handle, a1, a2, a3]

theorem handle_lead3 (b : UInt8) (h1 : 0xE0 ≤ b.toNat) (h2 : b.toNat ≤ 0xEF) :
    utf8Initial.handle (some b) = ⟨.utf8 (b &&& 0xF).toUInt32 0 2
      (if b = 0xE0 then 0xA0 else 0x80) (if b = 0xED then 0x9F else 0xBF), .cont, []⟩ := by
  have a1 : ¬ b ≤ 0x7F := by rw [UInt8.le_iff_toNat_le]; simp; omega
  have a2 : ¬ (0xC2 ≤ b ∧ b ≤ 0xDF) := by
    simp only [UInt8.le_iff_toNat_le]; simp; omega
  have a4 : 0xE0 ≤ b := by rw [UInt8.le_iff_toNat_le]; simpa using h1
  have a5 : b ≤ 0xEF := by rw [UInt8.le_iff_toNat_le]; simpa using h2
  simp [utf8Initial, Decoder.handle, utf8Handle, a1, a2, a4, a5]
  done

theorem handle_lead4 (b : UInt8) (h1 : 0xF0 ≤ b.toNat) (h2 : b.toNat ≤ 0xF4) :
    utf8Initial.handle (some b) = ⟨.utf8 (b &&& 0x7).toUInt32 0 3
      (if b = 0xF0 then 0x90 else 0x80) (if b = 0xF4 then 0x8F else 0xBF), .cont, []⟩ := by
  have a1 : ¬ b ≤ 0x7F := by rw [UInt8.le_iff_toNat_le]; simp; omega
  have a2 : ¬ (0xC2 ≤ b ∧ b ≤ 0xDF) := by
    simp only [UInt8.le_iff_toNat_le]; simp; omega
  have a3 : ¬ (0xE0 ≤ b ∧ b ≤ 0xEF) := by
    simp only [UInt8.le_iff_toNat_le]; simp; omega
  have a4 : 0xF0 ≤ b := by rw [UInt8.le_iff_toNat_le]; simpa using h1
  have a5 : b ≤ 0xF4 := by rw [UInt8.le_iff_toNat_le]; simpa using h2
  simp [utf8Initial, Decoder.handle, utf8Handle, a1, a2, a3, a4, a5]

theorem handle_more (cp : UInt32) (seen needed : Nat) (lower upper b : UInt8)
    (hn : needed ≠ 0) (hl : lower.toNat ≤ b.toNat) (hu : b.toNat ≤ upper.toNat)
    (hs : seen + 1 ≠ needed) :
    (Decoder.utf8 cp seen needed lower upper).handle (some b) =
      ⟨.utf8 ((cp <<< 6) ||| (b &&& 0x3F).toUInt32) (seen + 1) needed 0x80 0xBF, .cont, []⟩ := by
  have a1 : ¬ (b < lower ∨ b > upper) := by
    simp only [UInt8.lt_iff_toNat_lt, gt_iff_lt]; omega
  simp [Decoder.handle, utf8Handle, hn, hs, a1]

theorem handle_last (cp : UInt32) (seen needed : Nat) (lower upper b : UInt8)
    (hn : needed ≠ 0) (hl : lower.toNat ≤ b.toNat) (hu : b.toNat ≤ upper.toNat)
    (hs : seen + 1 = needed) :
    (Decoder.utf8 cp seen needed lower upper).handle (some b) =
      ⟨utf8Initial, .items [(cp <<< 6) ||| (b &&& 0x3F).toUInt32], []⟩ := by
  have a1 : ¬ (b < lower ∨ b > upper) := by
    simp only [UInt8.lt_iff_toNat_lt, gt_iff_lt]; omega
  simp [Decoder.handle, utf8Handle, hn, hs, a1, utf8Initial]

/-! ## The decoder on the bytes of one character -/

theorem utf8_decode_encodeChar (c : Char) :
    runHandle utf8Initial (String.utf8EncodeChar c) = some (utf8Initial, [c.val]) := by
  have hlt := char_toNat_lt c
  have hsur := char_not_surrogate c
  unfold String.utf8EncodeChar
  generalize c.val = n at hlt hsur ⊢
  by_cases h1 : n.toNat ≤ 127
  · simp only [h1, if_true]
    rw [runHandle_items [] (handle_ascii _ (by byte_bound))]
    simp only [runHandle, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq, true_and]
    simp only [List.cons.injEq, and_true, ← UInt32.toNat_inj, UInt8.toNat_toUInt32, UInt8.toNat_ofNat']
    omega
  by_cases h2 : n.toNat ≤ 2047
  · simp only [h1, h2, if_true, if_false]
    rw [runHandle_cont _ (handle_lead2 _ (by byte_bound) (by byte_bound))]
    rw [runHandle_items [] (handle_last _ _ _ _ _ _ (by decide) (by byte_bound) (by byte_bound) rfl)]
    simp only [runHandle, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq, true_and]
    simp only [List.cons.injEq, and_true, ← UInt32.toNat_inj, UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat,
      Nat.reducePow, Nat.reduceMod, and31, and63]
    simp (disch := omega) only [shl_or_mod]
    omega
  by_cases h3 : n.toNat ≤ 65535
  · simp only [h1, h2, h3, if_true, if_false]
    rw [runHandle_cont _ (handle_lead3 _ (by byte_bound) (by byte_bound))]
    rw [runHandle_cont _ (handle_more _ _ _ _ _ _ (by decide) (by bound_if) (by bound_if) (by decide))]
    rw [runHandle_items [] (handle_last _ _ _ _ _ _ (by decide) (by byte_bound) (by byte_bound) rfl)]
    simp only [runHandle, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq, true_and]
    simp only [List.cons.injEq, and_true, ← UInt32.toNat_inj, UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat,
      Nat.reducePow, Nat.reduceMod, and15, and63]
    simp (disch := omega) only [shl_or_mod]
    omega
  · simp only [h1, h2, h3, if_false]
    rw [runHandle_cont _ (handle_lead4 _ (by byte_bound) (by byte_bound))]
    rw [runHandle_cont _ (handle_more _ _ _ _ _ _ (by decide) (by bound_if) (by bound_if) (by decide))]
    rw [runHandle_cont _ (handle_more _ _ _ _ _ _ (by decide) (by byte_bound) (by byte_bound) (by decide))]
    rw [runHandle_items [] (handle_last _ _ _ _ _ _ (by decide) (by byte_bound) (by byte_bound) rfl)]
    simp only [runHandle, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq, true_and]
    simp only [List.cons.injEq, and_true, ← UInt32.toNat_inj, UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.toNat_ofNat', UInt8.reduceToNat, UInt32.reduceToNat,
      Nat.reducePow, Nat.reduceMod, and7, and63]
    simp (disch := omega) only [shl_or_mod]
    omega

/-! ## Lists of characters and the section 6 hook -/

theorem runHandle_append {d d' : Decoder} {xs : List UInt8} {out : List UInt32}
    (h : runHandle d xs = some (d', out)) (ys : List UInt8) :
    runHandle d (xs ++ ys) = (runHandle d' ys).map fun r => (r.1, out ++ r.2) := by
  induction xs generalizing d out with
  | nil =>
    simp only [runHandle, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons b bs ih =>
    simp only [List.cons_append, runHandle] at h ⊢
    generalize d.handle (some b) = s at h ⊢
    obtain ⟨d1, r, rs⟩ := s
    cases rs with
    | cons _ _ => simp at h
    | nil =>
      cases r with
      | finished => simp at h
      | error => simp at h
      | cont => exact ih h
      | items cps =>
        simp only [List.isEmpty_nil, if_true] at h ⊢
        cases hrun : runHandle d1 bs with
        | none => simp [hrun] at h
        | some p =>
          obtain ⟨d2, out2⟩ := p
          simp only [hrun, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ih hrun]
          cases runHandle d2 ys <;> simp

theorem utf8_decode_encodeList (cs : List Char) :
    runHandle utf8Initial (cs.flatMap String.utf8EncodeChar) = some (utf8Initial, cs.map (·.val)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, runHandle_append (utf8_decode_encodeChar c), ih]
    rfl

theorem pushItems_eq (out : Array UInt32) (cps : List UInt32) :
    pushItems out cps = out ++ cps.toArray := by
  induction cps generalizing out with
  | nil => simp [pushItems]
  | cons c cs ih => simp [pushItems, ih]

theorem decodeLoop_run (data : ByteArray) : ∀ (xs : List UInt8) (pos fuel : Nat) (d d' : Decoder)
    (out : Array UInt32) (cps : List UInt32),
    data.data.toList.drop pos = xs → runHandle d xs = some (d', cps) → xs.length < fuel →
    decodeLoop fuel d { front := [], data, pos } out .fatal false =
      decodeLoop (fuel - xs.length) d' { front := [], data, pos := pos + xs.length }
        (out ++ cps.toArray) .fatal false := by
  intro xs
  induction xs with
  | nil =>
    intro pos fuel d d' out cps _ hrun _
    simp only [runHandle, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp
  | cons x rest ih =>
    intro pos fuel d d' out cps hdrop hrun hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hpos' : pos < data.data.size := by
      have := congrArg List.length hdrop
      rw [List.length_drop, Array.length_toList, List.length_cons] at this
      omega
    have hpos : pos < data.size := hpos'
    have hx : data[pos] = x := by
      rw [ByteArray.getElem_eq_getElem_data]
      have h2 := congrArg (·[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero, Array.getElem?_toList] at h2
      rw [Array.getElem?_eq_getElem hpos'] at h2
      exact Option.some.inj h2
    have hdrop' : data.data.toList.drop (pos + 1) = rest := by
      rw [← List.drop_drop, hdrop]; rfl
    simp only [decodeLoop, Queue.read, hpos, dite_true, hx, Option.isNone_some, Bool.false_and,
      Bool.false_eq_true, if_false]
    simp only [runHandle] at hrun
    generalize d.handle (some x) = s at hrun ⊢
    obtain ⟨d1, r, rs⟩ := s
    cases rs with
    | cons _ _ => simp at hrun
    | nil =>
      cases r with
      | finished => simp at hrun
      | error => simp at hrun
      | cont =>
        simp only [List.isEmpty_nil, if_true] at hrun
        simp only [List.nil_append]
        rw [ih (pos + 1) f d1 d' out cps hdrop' hrun (by simp at hfuel; omega)]
        have e : pos + 1 + rest.length = pos + (rest.length + 1) := by omega
        rw [e, List.length_cons, Nat.add_sub_add_right]
      | items cps1 =>
        simp only [List.isEmpty_nil, if_true] at hrun
        cases hr2 : runHandle d1 rest with
        | none => simp [hr2] at hrun
        | some p =>
          obtain ⟨d2, out2⟩ := p
          simp only [hr2, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          simp only [List.nil_append]
          rw [ih (pos + 1) f d1 _ (pushItems out cps1) out2 hdrop' hr2 (by simp at hfuel; omega)]
          have e : pos + 1 + rest.length = pos + (rest.length + 1) := by omega
          rw [e, List.length_cons, Nat.add_sub_add_right, pushItems_eq, Array.append_assoc,
            ← List.append_toArray]

theorem cpsToString_map_val (cs : List Char) : cpsToString (cs.map (·.val)).toArray = String.ofList cs := by
  apply String.toList_injective
  rw [String.toList_ofList]
  unfold cpsToString
  rw [List.foldl_toArray]
  suffices h : ∀ (init : String),
      (List.foldl (fun s c => s.push (Char.ofNat c.toNat)) init (cs.map (·.val))).toList = init.toList ++ cs by
    simpa using h ""
  induction cs with
  | nil => simp
  | cons c cs ih =>
    intro init
    simp only [List.map_cons, List.foldl_cons]
    rw [ih, String.toList_push]
    simp

theorem utf8DecodeWithoutBOMOrFail_toUTF8 (s : String) :
    utf8DecodeWithoutBOMOrFail s.toUTF8 = some s := by
  have hb : s.toUTF8 = (s.toList.flatMap String.utf8EncodeChar).toByteArray := by
    rw [String.toUTF8_eq_toByteArray]
    conv => lhs; rw [← String.ofList_toList (s := s)]
    rw [String.toByteArray_ofList]
    rfl
  rw [hb]
  generalize hL : s.toList.flatMap String.utf8EncodeChar = L
  have hrun : runHandle utf8Initial L = some (utf8Initial, s.toList.map (·.val)) := by
    rw [← hL]; exact utf8_decode_encodeList s.toList
  unfold utf8DecodeWithoutBOMOrFail decodeQueue
  have hq : Queue.ofBytes L.toByteArray = { front := [], data := L.toByteArray, pos := 0 } := rfl
  have hfuel : fuelFor (Queue.ofBytes L.toByteArray) = (L.length + 1) + (7 * L.length + 23) := by
    simp [fuelFor, Queue.length, Queue.ofBytes]; omega
  rw [hq] at hfuel ⊢
  rw [hfuel, decodeLoop_run L.toByteArray L 0 _ _ _ _ _ (by simp [List.data_toByteArray]) hrun (by omega)]
  have e : L.length + 1 + (7 * L.length + 23) - L.length = (7 * L.length + 23) + 1 := by omega
  rw [e]
  generalize 7 * L.length + 23 = k
  have hr : ({ front := [], data := L.toByteArray, pos := 0 + L.length } : Queue).read = none := by
    simp [Queue.read]
  rw [decodeLoop]
  simp only [hr]
  simp [utf8Initial, Decoder.handle, utf8Handle]
  rw [cpsToString_map_val, String.ofList_toList]


end L4Factoidal.WHATWG.Encoding
