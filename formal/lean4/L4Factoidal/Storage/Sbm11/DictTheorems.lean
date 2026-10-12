/-
L4Factoidal.Storage.Sbm11.DictTheorems — the GDV1/GDX1 round trip.

* `decodePage_encodePage`: one front-coded page decodes to its keys and
  leaves the bytes after it.
* `decodeGdv_gdvBytes`, `decodeGdx_gdxBytes`: each file on its own.
* `decodeDict_encodeDict?`: `encodeDict? keys = some (v, x) →
  decodeDict v x = some keys`. The only hypothesis is the encoder's
  admission.
* `decodeDict_sorted`: a decoded dictionary is strictly increasing in
  unsigned byte order.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Dict
import L4Factoidal.Storage.Bytes

namespace L4Factoidal.Storage.Sbm11.Dict

open L4Factoidal.Storage (readU32LE writeU32LE readU64LE writeU64LE readU32LE_writeU32LE_append
  readU64LE_writeU64LE_append u32_toNat_ofNat_of_lt writeU32LE_length writeU64LE_length)
open L4Factoidal (two32 two64)

/-! ## Small fields -/

theorem putSmall_ne_nil (n : Nat) : putSmall n ≠ [] := by
  unfold putSmall; split <;> simp

theorem getSmall_putSmall (n : Nat) (rest : List UInt8) (h : n < 4294967296) :
    getSmall (putSmall n ++ rest) = some (n, rest) := by
  unfold putSmall
  by_cases hn : n < 255
  · simp only [hn, if_true, List.singleton_append, getSmall]
    have ht : (n.toUInt8).toNat = n := UInt8.toNat_ofNat_of_lt' (by show n < 256; omega)
    rw [ht]; simp [hn]
  · simp only [hn, if_false, List.cons_append, getSmall]
    have h255 : ¬ ((255 : UInt8).toNat < 255) := by decide
    rw [if_neg h255, readU32LE_writeU32LE_append]
    dsimp only
    rw [u32_toNat_ofNat_of_lt h]
    simp

/-! ## Longest common prefix -/

theorem lcpGo_spec (a b : List UInt8) (n : Nat) :
    ∃ m, lcpGo a b n = n + m ∧ m ≤ b.length ∧ a.take m = b.take m := by
  induction a generalizing b n with
  | nil => exact ⟨0, by cases b <;> simp [lcpGo], by simp, by simp⟩
  | cons x xs ih =>
    cases b with
    | nil => exact ⟨0, by simp [lcpGo], by simp, by simp⟩
    | cons y ys =>
      by_cases hxy : (x == y) = true
      · obtain ⟨m, h1, h2, h3⟩ := ih ys (n + 1)
        have hxy' : x = y := by simpa using hxy
        refine ⟨m + 1, ?_, ?_, ?_⟩
        · simp only [lcpGo, hxy, if_true, h1]; omega
        · simp; omega
        · simp [hxy', h3]
      · refine ⟨0, ?_, by simp, by simp⟩
        have hf : (x == y) = false := by simpa using hxy
        simp [lcpGo, hf]

theorem lcp_le (a b : List UInt8) : lcp a b ≤ b.length := by
  obtain ⟨m, h1, h2, _⟩ := lcpGo_spec a b 0
  unfold lcp; rw [h1]; omega

theorem take_lcp_append_drop (a b : List UInt8) : a.take (lcp a b) ++ b.drop (lcp a b) = b := by
  obtain ⟨m, h1, _, h3⟩ := lcpGo_spec a b 0
  have hl : lcp a b = m := by unfold lcp; rw [h1]; omega
  rw [hl, h3, List.take_append_drop]

/-! ## Entries and pages -/

theorem encodeEntriesGo_reverse (ks : List Key) :
    ∀ (prev : Key) (acc : List (List UInt8)),
      (encodeEntriesGo prev ks acc).reverse = acc.reverse ++ (encodeEntriesGo prev ks []).reverse := by
  induction ks with
  | nil => intro prev acc; simp [encodeEntriesGo]
  | cons k ks ih =>
    intro prev acc
    simp only [encodeEntriesGo]
    rw [ih k (piece prev k :: acc), ih k [piece prev k]]
    simp

theorem encodeEntries_nil (prev : Key) : encodeEntries prev [] = [] := by
  simp [encodeEntries, encodeEntriesGo]

theorem encodeEntries_cons (prev k : Key) (ks : List Key) :
    encodeEntries prev (k :: ks) = piece prev k ++ encodeEntries k ks := by
  unfold encodeEntries
  simp only [encodeEntriesGo]
  rw [encodeEntriesGo_reverse ks k [piece prev k]]
  simp

theorem decodeEntriesGo_piece (n : Nat) (prev k : Key) (accRev : List Key) (rest : List UInt8)
    (hk : k.length < 4294967296) :
    decodeEntriesGo (n + 1) prev accRev (piece prev k ++ rest) =
      decodeEntriesGo n k (k :: accRev) rest := by
  have hle := lcp_le prev k
  have hsplit := take_lcp_append_drop prev k
  unfold piece
  simp only [List.append_assoc]
  rw [decodeEntriesGo, getSmall_putSmall _ _ (by omega)]
  dsimp only
  rw [getSmall_putSmall _ _ (by omega)]
  dsimp only
  have hlen : (k.drop (lcp prev k)).length = k.length - lcp prev k := by simp
  rw [List.take_left' hlen, List.drop_left' hlen, hlen]
  simp only [beq_self_eq_true, if_true]
  rw [hsplit]

theorem decodeEntriesGo_encodeEntries (ks : List Key) :
    ∀ (prev : Key) (accRev : List Key) (rest : List UInt8),
      ks.all (fun k => decide (k.length < two32)) = true →
      decodeEntriesGo ks.length prev accRev (encodeEntries prev ks ++ rest) =
        some (accRev.reverse ++ ks, rest) := by
  induction ks with
  | nil => intro prev accRev rest _; simp [encodeEntries_nil, decodeEntriesGo]
  | cons k ks ih =>
    intro prev accRev rest hall
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    rw [List.length_cons, encodeEntries_cons, List.append_assoc,
      decodeEntriesGo_piece _ _ _ _ _ hall.1, ih k (k :: accRev) rest hall.2]
    simp

theorem decodePage_encodePage (ks : List Key) (rest : List UInt8) (h : pageFits ks = true) :
    decodePage (encodePage ks ++ rest) = some (ks, rest) := by
  simp only [pageFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hall⟩ := h
  cases ks with
  | nil =>
    simp only [encodePage]
    rw [decodePage, getSmall_putSmall _ _ (by omega)]
    simp
  | cons k r =>
    have hk : k.length < two32 := by
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall; exact hall.1
    have hr : r.all (fun k => decide (k.length < two32)) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
    simp only [encodePage, List.append_assoc]
    rw [decodePage, getSmall_putSmall _ _ (by simpa using hlen)]
    dsimp only
    have hc : ((k :: r).length == 0) = false := by simp
    rw [hc]
    simp only [Bool.false_eq_true, if_false]
    rw [getSmall_putSmall _ _ (by simpa using hk)]
    dsimp only
    rw [List.take_left' rfl, List.drop_left' rfl]
    simp only [beq_self_eq_true, if_true, List.length_cons, Nat.add_sub_cancel]
    rw [decodeEntriesGo_encodeEntries r k [k] rest hr]
    simp

theorem encodePage_ne_nil (ks : List Key) : encodePage ks ≠ [] := by
  cases ks with
  | nil => exact putSmall_ne_nil 0
  | cons k r =>
    simp only [encodePage, ne_eq, List.append_eq_nil_iff, not_and]
    intro h
    exact absurd h.1 (putSmall_ne_nil _)

/-! ## GDV1 -/

theorem length_le_flatten_encodePage (pages : List (List Key)) :
    pages.length ≤ (pages.map encodePage).flatten.length := by
  induction pages with
  | nil => simp
  | cons p ps ih =>
    have := encodePage_ne_nil p
    have hp : 0 < (encodePage p).length := List.length_pos_iff.mpr this
    rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem decodePagesGo_flatten (pages : List (List Key)) :
    ∀ (f : Nat) (accRev : List (List Key)),
      pages.length < f → pages.all pageFits = true →
      decodePagesGo f (pages.map encodePage).flatten accRev = some (accRev.reverse ++ pages) := by
  induction pages with
  | nil =>
    intro f accRev hf _
    cases f with
    | zero => omega
    | succ f => simp [decodePagesGo]
  | cons p ps ih =>
    intro f accRev hf hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    cases f with
    | zero => simp at hf
    | succ f =>
      simp only [List.map_cons, List.flatten_cons]
      have hdec := decodePage_encodePage p (ps.map encodePage).flatten hall.1
      cases hbs : encodePage p ++ (ps.map encodePage).flatten with
      | nil => exact absurd (List.append_eq_nil_iff.mp hbs).1 (encodePage_ne_nil p)
      | cons b t =>
        simp only [decodePagesGo]
        rw [← hbs, hdec]
        dsimp only
        rw [ih f (p :: accRev) (by simp at hf; omega) hall.2]
        simp

theorem decodeGdv_gdvBytes (pages : List (List Key)) (h : pages.all pageFits = true) :
    decodeGdv (gdvBytes pages) = some pages := by
  unfold decodeGdv gdvBytes
  have hh : gdvHeader.length = 6 := rfl
  rw [List.take_left' hh, List.drop_left' hh]
  simp only [beq_self_eq_true, if_true]
  have hle := length_le_flatten_encodePage pages
  rw [decodePagesGo_flatten pages _ [] (by rw [List.length_append]; omega) h]
  simp

/-! ## GDX1 -/

private theorem u64_toNat_ofNat {n : Nat} (h : n < 18446744073709551616) :
    (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' h

theorem decodeEntry_entryBytes (e : DirEntry) (rest : List UInt8) (h : entryFits e = true) :
    decodeEntry (entryBytes e ++ rest) = some (e, rest) := by
  simp only [entryFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  unfold decodeEntry entryBytes
  simp only [List.append_assoc]
  rw [readU64LE_writeU64LE_append]
  dsimp only
  rw [List.drop_left' (writeU64LE_length _), readU32LE_writeU32LE_append]
  dsimp only
  rw [List.drop_left' (writeU32LE_length _)]
  rw [u64_toNat_ofNat h1, u32_toNat_ofNat_of_lt h2]

theorem decodeEntriesN_entries (es : List DirEntry) :
    ∀ (accRev : List DirEntry) (rest : List UInt8), es.all entryFits = true →
      decodeEntriesN es.length ((es.map entryBytes).flatten ++ rest) accRev =
        some (accRev.reverse ++ es, rest) := by
  induction es with
  | nil => intro accRev rest _; simp [decodeEntriesN]
  | cons e es ih =>
    intro accRev rest hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeEntriesN]
    rw [decodeEntry_entryBytes e _ hall.1]
    dsimp only
    rw [ih (e :: accRev) rest hall.2]
    simp

theorem decodeGdx_gdxBytes (tc : Nat) (es : List DirEntry)
    (htc : tc < two64) (hn : es.length < two64) (hes : es.all entryFits = true) :
    decodeGdx (gdxBytes tc es) = some (tc, es) := by
  unfold decodeGdx gdxBytes
  have hm : gdxMagic.length = 5 := rfl
  simp only [List.append_assoc]
  rw [List.take_left' hm]
  simp only [beq_self_eq_true, if_true]
  rw [List.drop_left' hm, readU64LE_writeU64LE_append]
  dsimp only
  rw [List.drop_left' (writeU64LE_length _), readU64LE_writeU64LE_append]
  dsimp only
  rw [List.drop_left' (writeU64LE_length _), u64_toNat_ofNat hn]
  have he := decodeEntriesN_entries es [] [] hes
  simp only [List.append_nil] at he
  rw [he]
  simp [u64_toNat_ofNat htc]

/-! ## The directory -/

theorem dirEntriesGo_length (ps : List (List Key)) :
    ∀ (off : Nat) (acc : List DirEntry),
      (dirEntriesGo ps off acc).length = acc.length + ps.length := by
  induction ps with
  | nil => intro off acc; simp [dirEntriesGo]
  | cons p ps ih =>
    intro off acc
    simp only [dirEntriesGo]
    rw [ih]
    simp; omega

/-! ## Cutting into pages -/

theorem chunkGo_flatten {α : Type} (n : Nat) (hn : 0 < n) (f : Nat) :
    ∀ (l : List α) (acc : List (List α)), l.length < f →
      (chunkGo n f l acc).flatten = acc.reverse.flatten ++ l := by
  induction f with
  | zero => intro l acc h; omega
  | succ f ih =>
    intro l acc h
    cases l with
    | nil => simp [chunkGo]
    | cons x xs =>
      simp only [chunkGo]
      rw [ih _ _ (by simp at h ⊢; omega)]
      simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc, List.take_append_drop]

theorem chunk_flatten {α : Type} (n : Nat) (hn : 0 < n) (l : List α) :
    (chunk n l).flatten = l := by
  unfold chunk
  rw [chunkGo_flatten n hn _ l [] (by omega)]
  simp

/-! ## The dictionary round trip -/

/-- GDV1/GDX1 round trip: the only hypothesis is that the encoder admitted
    the key list. -/
theorem decodeDict_encodeDict? (keys : List Key) (v x : List UInt8)
    (h : encodeDict? keys = some (v, x)) : decodeDict v x = some keys := by
  unfold encodeDict? at h
  dsimp only at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hadm' := hadm
    simp only [dictAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm'
    obtain ⟨⟨⟨⟨_, hcount⟩, hpages⟩, hfits⟩, hents⟩ := hadm'
    have hflat : (chunk pageTerms keys).flatten = keys := chunk_flatten pageTerms (by decide) keys
    have hgdv := decodeGdv_gdvBytes (chunk pageTerms keys) hfits
    have hlenE : (dirEntries (chunk pageTerms keys)).length = (chunk pageTerms keys).length := by
      unfold dirEntries; rw [dirEntriesGo_length]; simp
    have hgdx := decodeGdx_gdxBytes keys.length (dirEntries (chunk pageTerms keys))
      (by simp only [maxTerms, two64] at hcount ⊢; omega) (by rw [hlenE]; exact hpages) hents
    unfold decodeDict
    rw [hgdv, hgdx]
    dsimp only
    rw [hflat]
    simp [hadm]
  · cases h

/-- A decoded dictionary is strictly increasing. -/
theorem decodeDict_sorted (v x : List UInt8) (ks : List Key) (h : decodeDict v x = some ks) :
    strictlySorted ks = true := by
  unfold decodeDict at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨_, hadm⟩, _⟩, _⟩ := hc
      simp only [dictAdmitted, Bool.and_eq_true] at hadm
      exact hadm.1.1.1.1
    · cases h
  · cases h

end L4Factoidal.Storage.Sbm11.Dict
