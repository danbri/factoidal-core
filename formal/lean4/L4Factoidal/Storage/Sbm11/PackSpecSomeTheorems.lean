/-
L4Factoidal.Storage.Sbm11.PackSpecSomeTheorems — the domain on which the
pure packer specification `PackSpec.packSpec` returns a generation
(https://github.com/danbri/factoidal/issues/776; row L3c of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`packSpec B qs decl` is `none` exactly when an encoder refuses. The
encoders refuse:

* `keysOf?`: a term with no inline id and no dictionary key
  (`termKey?` of the term with its language tags in lower case is `none`:
  a literal with a base direction and no language tag, a language tag or a
  datatype IRI with a `0x00` byte, a triple term with a part of `2^32`
  bytes or more);
* `encodeDict?`: `2^60` keys or more, a key of `2^32` bytes or more, a
  page or a GDV1 offset outside its field;
* `toCode?`: a dictionary rank of `2^60` or more;
* `encodeBlock?`: a block of `2^32` rows or more, or a frame of `2^32`
  bytes or more;
* `encodePrm?`: a PRB1 offset, a block count or a row count of `2^64` or
  more.

`packSpec_some` states the domain as three checkable conditions and proves
that `packSpec` is `some` on it:

* `hB`: `B < 2^28` (a block holds at most `max B 1` rows, so a frame holds
  fewer than `2^31 + 2` bytes);
* `hn`: `4 * qs.length + decl.length < 2^36` (at most `2^36` terms, so
  fewer than `2^36` keys, rows and blocks, and every offset below `2^62`);
* `hfit`: every term of the input is `termFits`: it has an inline id, or a
  dictionary key of fewer than `2^24` bytes (`packKeyLimit`).

None of the three mentions an encoder's result: `termFits` is a test of
one term, the other two are numbers of the input.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PackSpecTheorems

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.Dict (cmpKey encodeDict? pageTerms putSmall encodePage chunk chunkGo
  dirEntries dirEntriesGo pageFits entryFits dictAdmitted strictlySorted strictlySortedGo piece
  encodeEntries DirEntry)

/-- The bound on the length of a dictionary key in the domain of
    `packSpec_some`: `2^24` bytes. -/
def packKeyLimit : Nat := 16777216

/-- A term in the domain of `packSpec_some`: it has an inline id, or a
    dictionary key of fewer than `packKeyLimit` bytes. -/
def termFits (t : Term) : Bool :=
  match keyOfTerm? t with
  | some none => true
  | some (some k) => decide (k.length < packKeyLimit)
  | none => false

/-! ## Lists -/

theorem allSome_some {α β : Type} (f : α → Option β) : ∀ (l : List α), (∀ a ∈ l, (f a).isSome = true) →
    ∃ l', allSome f l = some l' ∧ l'.length = l.length
  | [], _ => ⟨[], rfl, rfl⟩
  | a :: as, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    obtain ⟨bs, hbs, hl⟩ := allSome_some f as (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨b :: bs, ?_, by simp [hl]⟩
    simp [allSome, hb, hbs]

theorem allSome_length {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β),
    allSome f l = some l' → l'.length = l.length
  | [], l', h => by simp only [allSome, Option.some.injEq] at h; subst h; rfl
  | a :: as, l', h => by
    simp only [allSome, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, _, bs, hbs, rfl⟩ := h
    simp [allSome_length f as bs hbs]

theorem insertUniq_length {α : Type} (cmp : α → α → Ordering) (a : α) :
    ∀ l, (insertUniq cmp a l).length ≤ l.length + 1
  | [] => by simp [insertUniq]
  | b :: bs => by
    unfold insertUniq
    have := insertUniq_length cmp a bs
    split <;> simp <;> omega

theorem foldl_insertUniq_length {α : Type} (cmp : α → α → Ordering) : ∀ (l acc : List α),
    (l.foldl (fun acc a => insertUniq cmp a acc) acc).length ≤ acc.length + l.length
  | [], acc => by simp
  | a :: l, acc => by
    have h1 := foldl_insertUniq_length cmp l (insertUniq cmp a acc)
    have h2 := insertUniq_length cmp a acc
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem sortUniq_length_le {α : Type} (cmp : α → α → Ordering) (l : List α) :
    (sortUniq cmp l).length ≤ l.length := by
  have := foldl_insertUniq_length cmp l []
  unfold sortUniq
  simpa using this

/-- A list of nonempty lists is no longer than its flattening. -/
theorem length_le_flatten {α : Type} : ∀ (ps : List (List α)), (∀ p ∈ ps, p ≠ []) →
    ps.length ≤ ps.flatten.length
  | [], _ => by simp
  | p :: ps, h => by
    have h1 := length_le_flatten ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 : 0 < p.length := List.length_pos_iff.2 (h p List.mem_cons_self)
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- A sum of `g` over lists, each at most `c` times its length. -/
theorem sum_le_flatten {α : Type} (g : List α → Nat) (c : Nat) : ∀ (ps : List (List α)),
    (∀ p ∈ ps, g p ≤ c * p.length) → (ps.map g).sum ≤ c * ps.flatten.length
  | [], _ => by simp
  | p :: ps, h => by
    have h1 := sum_le_flatten g c ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 := h p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, Nat.mul_add]
    omega

/-! ## The dictionary keys -/

theorem keyOfTerm_isSome (t : Term) (h : termFits t = true) : (keyOfTerm? t).isSome = true := by
  unfold termFits at h
  split at h <;> simp_all

theorem keysOf_some (ts : List Term) (ht : ∀ t ∈ ts, termFits t = true) :
    ∃ keys, keysOf? ts = some keys ∧ keys.length ≤ ts.length ∧ ∀ k ∈ keys, k.length < packKeyLimit := by
  obtain ⟨ks, hks, hl⟩ := allSome_some keyOfTerm? ts (fun t h => keyOfTerm_isSome t (ht t h))
  refine ⟨sortUniq cmpKey (ks.filterMap id), ?_, ?_, fun k hk => ?_⟩
  · simp [keysOf?, hks]
  · have h1 := sortUniq_length_le cmpKey (ks.filterMap id)
    have h2 := List.length_filterMap_le id ks
    omega
  · rw [mem_sortUniq strict_cmpKey, List.mem_filterMap] at hk
    obtain ⟨o, ho, ho'⟩ := hk
    simp only [id] at ho'
    subst ho'
    obtain ⟨t, htm, hkt⟩ := (allSome_mem _ ts ks hks).1 _ ho
    have := ht t htm
    unfold termFits at this
    rw [hkt] at this
    simpa using this

/-! ## The dictionary bytes -/

theorem strictlySortedGo_of (prev : Key) : ∀ (ks : List Key), (∀ k ∈ ks, cmpKey prev k = .lt) →
    ks.Pairwise (fun a b => cmpKey a b = .lt) → strictlySortedGo prev ks = true
  | [], _, _ => rfl
  | k :: ks, h1, h2 => by
    have hp := List.pairwise_cons.1 h2
    simp only [strictlySortedGo, h1 k List.mem_cons_self]
    exact strictlySortedGo_of k ks hp.1 hp.2

theorem strictlySorted_of (ks : List Key) (h : ks.Pairwise (fun a b => cmpKey a b = .lt)) :
    strictlySorted ks = true := by
  cases ks with
  | nil => rfl
  | cons k ks =>
    have hp := List.pairwise_cons.1 h
    exact strictlySortedGo_of k ks hp.1 hp.2

theorem chunkGo_mem {α : Type} (n : Nat) (hn : 0 < n) : ∀ (f : Nat) (l : List α) (acc : List (List α))
    (p : List α), p ∈ chunkGo n f l acc → p ∈ acc ∨ (p ≠ [] ∧ p.length ≤ n)
  | 0, l, acc, p, h => by simp only [chunkGo, List.mem_reverse] at h; exact Or.inl h
  | f + 1, [], acc, p, h => by simp only [chunkGo, List.mem_reverse] at h; exact Or.inl h
  | f + 1, x :: xs, acc, p, h => by
    simp only [chunkGo] at h
    rcases chunkGo_mem n hn f _ _ p h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · refine Or.inr ⟨?_, List.length_take_le _ _⟩
        cases n with
        | zero => omega
        | succ n => simp
      · exact Or.inl h
    · exact Or.inr h

theorem chunk_mem {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (p : List α) (h : p ∈ chunk n l) :
    p ≠ [] ∧ p.length ≤ n := by
  rcases chunkGo_mem n hn _ l [] p h with h | h
  · simp at h
  · exact h

theorem putSmall_length (n : Nat) : (putSmall n).length ≤ 5 := by
  unfold putSmall
  split <;> simp

theorem piece_length (prev k : Key) : (piece prev k).length ≤ 10 + k.length := by
  unfold piece
  have h1 := putSmall_length (Dict.lcp prev k)
  have h2 := putSmall_length (k.length - Dict.lcp prev k)
  simp only [List.length_append, List.length_drop]
  omega

theorem encodeEntries_length : ∀ (prev : Key) (ks : List Key),
    (encodeEntries prev ks).length ≤ 10 * ks.length + (ks.map List.length).sum
  | prev, [] => by simp [Dict.encodeEntries_nil]
  | prev, k :: ks => by
    rw [Dict.encodeEntries_cons]
    have h1 := piece_length prev k
    have h2 := encodeEntries_length k ks
    simp only [List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem sum_length_le (ks : List Key) (c : Nat) (h : ∀ k ∈ ks, k.length < c) :
    (ks.map List.length).sum ≤ c * ks.length := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := h k List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add]
    omega

/-- A nonempty page of keys shorter than `packKeyLimit` bytes is at most
    `packKeyLimit + 15` bytes a key. -/
theorem encodePage_length (p : List Key) (hp : p ≠ []) (hk : ∀ k ∈ p, k.length < packKeyLimit) :
    (encodePage p).length ≤ (packKeyLimit + 15) * p.length := by
  cases p with
  | nil => exact absurd rfl hp
  | cons k ks =>
    unfold encodePage
    have h1 := putSmall_length (k :: ks).length
    have h2 := putSmall_length k.length
    have h3 := encodeEntries_length k ks
    have h4 := sum_length_le ks packKeyLimit (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    have h5 := hk k List.mem_cons_self
    simp only [List.length_append, List.length_cons, Nat.mul_add] at h1 h2 h3 h4 ⊢
    unfold packKeyLimit at h4 h5 ⊢
    omega

theorem dirEntriesGo_mem : ∀ (ps : List (List Key)) (off : Nat) (acc : List DirEntry) (e : DirEntry),
    e ∈ dirEntriesGo ps off acc → e ∈ acc ∨
      ((∃ p ∈ ps, e.pageLen = (encodePage p).length) ∧
        e.pageOffset + e.pageLen ≤ off + ((ps.map encodePage).map List.length).sum)
  | [], off, acc, e, h => by simp only [dirEntriesGo, List.mem_reverse] at h; exact Or.inl h
  | p :: ps, off, acc, e, h => by
    simp only [dirEntriesGo] at h
    rcases dirEntriesGo_mem ps _ _ e h with h | ⟨⟨q, hq, hl⟩, ho⟩
    · rcases List.mem_cons.1 h with rfl | h
      · refine Or.inr ⟨⟨p, List.mem_cons_self, rfl⟩, ?_⟩
        simp only [List.map_cons, List.sum_cons]
        omega
      · exact Or.inl h
    · refine Or.inr ⟨⟨q, List.mem_cons_of_mem _ hq, hl⟩, ?_⟩
      simp only [List.map_cons, List.sum_cons] at ho ⊢
      omega

theorem encodeDict_some (keys : List Key) (hs : keys.Pairwise (fun a b => cmpKey a b = .lt))
    (hn : keys.length < 68719476736) (hk : ∀ k ∈ keys, k.length < packKeyLimit) :
    ∃ v x, encodeDict? keys = some (v, x) := by
  have hpages := chunk_mem pageTerms (by decide) keys
  have hflat := Dict.chunk_flatten pageTerms (by decide) keys
  have hk' : ∀ p ∈ chunk pageTerms keys, ∀ k ∈ p, k.length < packKeyLimit := fun p hp k hkp =>
    hk k (hflat ▸ List.mem_flatten.2 ⟨p, hp, hkp⟩)
  have hlen := length_le_flatten _ (fun p hp => (hpages p hp).1)
  rw [hflat] at hlen
  have hsum := sum_le_flatten (fun p => (encodePage p).length) (packKeyLimit + 15) (chunk pageTerms keys)
    (fun p hp => encodePage_length p (hpages p hp).1 (hk' p hp))
  rw [hflat] at hsum
  have hadm : dictAdmitted keys (chunk pageTerms keys) = true := by
    unfold dictAdmitted
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, L4Factoidal.two64_eq]
    refine ⟨⟨⟨⟨strictlySorted_of keys hs, ?_⟩, ?_⟩, fun p hp => ?_⟩, fun e he => ?_⟩
    · unfold Dict.maxTerms; omega
    · omega
    · unfold pageFits
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, L4Factoidal.two32_eq]
      have := (hpages p hp).2
      refine ⟨by unfold pageTerms at this; omega, fun k hkp => ?_⟩
      have := hk' p hp k hkp
      unfold packKeyLimit at this; omega
    · unfold dirEntries at he
      rcases dirEntriesGo_mem _ _ _ e he with h | ⟨⟨p, hp, hl⟩, ho⟩
      · simp at h
      · unfold entryFits
        simp only [Bool.and_eq_true, decide_eq_true_eq, L4Factoidal.two32_eq, L4Factoidal.two64_eq]
        have h1 := encodePage_length p (hpages p hp).1 (hk' p hp)
        have h2 := (hpages p hp).2
        rw [List.map_map] at ho
        have h3 : ((chunk pageTerms keys).map (List.length ∘ encodePage)).sum =
            ((chunk pageTerms keys).map (fun p => (encodePage p).length)).sum := rfl
        rw [h3] at ho
        simp only [Dict.gdvHeader, List.length_cons, List.length_nil] at ho
        unfold packKeyLimit at h1 hsum
        unfold pageTerms at h2
        constructor <;> omega
  unfold encodeDict?
  simp [hadm]

/-! ## The ids -/

theorem idOf_some (ts : List Term) (keys : List Key) (hk : keysOf? ts = some keys)
    (hlen : keys.length < two60) (t : Term) (ht : t ∈ ts) :
    ∃ n, idOf? keys t = some n := by
  unfold idOf? toCode?
  cases hin : inlineCode? (normalizeTerm t) with
  | some c => exact ⟨c, rfl⟩
  | none =>
    obtain ⟨k, hkt, hkm⟩ := (keysOf_spec ts keys hk).2.2 t ht hin
    have hi := List.idxOf_lt_length_of_mem hkm
    refine ⟨dictCode k (keys.idxOf k), ?_⟩
    simp only [hkt]
    simp [hi, show keys.idxOf k < two60 by omega]

theorem quadTerms_length (q : Quad) : (quadTerms q).length ≤ 4 := by
  obtain ⟨tr, g⟩ := q
  cases g <;> simp [quadTerms]

theorem termsOf_length (qs : List Quad) (decl : List Subject) :
    (termsOf qs decl).length ≤ 4 * qs.length + decl.length := by
  unfold termsOf
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have := quadTerms_length q
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at ih ⊢
    omega

theorem mem_termsOf_quad (qs : List Quad) (decl : List Subject) (q : Quad) (hq : q ∈ qs) (t : Term)
    (ht : t ∈ quadTerms q) : t ∈ termsOf qs decl := by
  unfold termsOf
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨q, hq, ht⟩)

theorem spoRow_some (keys : List Key) (q : Quad) (h : ∀ t ∈ quadTerms q, ∃ n, idOf? keys t = some n) :
    ∃ r, spoRow? keys q = some r := by
  obtain ⟨tr, g⟩ := q
  obtain ⟨a, ha⟩ := h tr.s.toTerm (by simp [quadTerms])
  obtain ⟨b, hb⟩ := h (.iri tr.p) (by simp [quadTerms])
  obtain ⟨c, hc⟩ := h tr.o (by simp [quadTerms])
  cases g with
  | none => exact ⟨⟨a, b, c, 0⟩, by simp [spoRow?, ha, hb, hc]⟩
  | some g =>
    obtain ⟨d, hd⟩ := h g.toTerm (by simp [quadTerms])
    exact ⟨⟨a, b, c, d⟩, by simp [spoRow?, ha, hb, hc, hd]⟩

theorem spoRow_fits (keys : List Key) (q : Quad) (r : Row) (h : spoRow? keys q = some r) : r.fits = true := by
  obtain ⟨h1, h2, h3, h4⟩ := spoRow_spec keys q r h
  have e1 := code_lt _ _ _ h1
  have e2 := code_lt _ _ _ h2
  have e3 := code_lt _ _ _ h3
  have e4 : r.g < 18446744073709551616 := by
    rcases h4 with ⟨_, h⟩ | ⟨g, _, h⟩
    · omega
    · exact code_lt _ _ _ h
  simp [Row.fits, e1, e2, e3, e4]

/-! ## Blocks -/

theorem cutGo_blocks (B c : Nat) : ∀ (xs cur : List Row), cur.length ≤ max B 1 →
    ∀ rs ∈ cutGo B c xs cur, rs ≠ [] ∧ rs.length ≤ max B 1
  | [], [], _, rs, h => by simp [cutGo] at h
  | [], y :: ys, hc, rs, h => by
    simp only [cutGo, List.mem_singleton] at h
    subst h
    simpa using hc
  | x :: xs, [], _, rs, h => by
    simp only [cutGo] at h
    exact cutGo_blocks B c xs [x] (by simp only [List.length_singleton]; omega) rs h
  | x :: xs, y :: ys, hc, rs, h => by
    unfold cutGo at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simpa using hc
      · exact cutGo_blocks B c xs [x] (by simp only [List.length_singleton]; omega) rs h
    · rename_i hne
      refine cutGo_blocks B c xs (x :: y :: ys) ?_ rs h
      have : ¬ (y :: ys).length ≥ B := fun hge => hne (by rw [Bool.or_eq_true]; exact Or.inl (decide_eq_true hge))
      simp only [List.length_cons] at this ⊢
      omega

theorem rawBytes_length : ∀ (xs : List Nat), (rawBytes xs).length = 8 * xs.length
  | [] => rfl
  | x :: xs => by
    have := rawBytes_length xs
    simp only [rawBytes, List.map_cons, List.flatten_cons, List.length_append, put64_length,
      List.length_cons] at this ⊢
    omega

theorem frameBytes_length (xs : List Nat) : (frameBytes xs).length ≤ 1 + 8 * xs.length := by
  cases xs with
  | nil => simp [frameBytes]
  | cons x rest =>
    have hr := rawBytes_length (x :: rest)
    simp only [frameBytes]
    by_cases h1 : (rest.all fun y => y == x) = true
    · rw [if_pos h1]; simp only [List.length_cons, put64_length]; omega
    · rw [if_neg h1]
      by_cases h2 : (deltaBytes (x :: rest)).length < 8 * (rest.length + 1)
      · rw [if_pos h2]; simp only [List.length_cons] at h2 ⊢; omega
      · rw [if_neg h2]; simp only [List.length_cons] at hr ⊢; omega

theorem sortedGo_of (prev : Row) : ∀ (rs : List Row), (∀ r ∈ rs, prev.lt r = true) →
    rs.Pairwise (fun a b => a.lt b = true) → sortedGo prev rs = true
  | [], _, _ => rfl
  | r :: rs, h1, h2 => by
    have hp := List.pairwise_cons.1 h2
    simp only [sortedGo, h1 r List.mem_cons_self, if_true]
    exact sortedGo_of r rs hp.1 hp.2

theorem rowsSorted_of (rs : List Row) (h : rs.Pairwise (fun a b => a.lt b = true)) : rowsSorted rs = true := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    have hp := List.pairwise_cons.1 h
    exact sortedGo_of r rs hp.1 hp.2

theorem blockAdmitted_of (rs : List Row) (hne : rs ≠ []) (hlen : rs.length < 268435456)
    (hs : rs.Pairwise (fun a b => a.lt b = true)) (hf : rs.all Row.fits = true) : blockAdmitted rs = true := by
  have f0 := frameBytes_length (rs.map Row.c0)
  have f1 := frameBytes_length (rs.map Row.c1)
  have f2 := frameBytes_length (rs.map Row.c2)
  have f3 := frameBytes_length (rs.map Row.g)
  simp only [List.length_map] at f0 f1 f2 f3
  unfold blockAdmitted
  simp only [Bool.and_eq_true, decide_eq_true_eq, L4Factoidal.two32_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨hne, rowsSorted_of rs hs⟩, hf⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩

theorem Row.le_head_last (r : Row) (rest : List Row) (hs : (r :: rest).Pairwise (fun a b => a.lt b = true)) :
    r.le ((r :: rest).getLastD default) = true := by
  unfold Row.le
  cases rest with
  | nil => simp
  | cons s ss =>
    have e : (r :: s :: ss).getLastD default = ss.getLastD s := by simp only [List.getLastD_cons]
    have hm : ss.getLastD s ∈ s :: ss := List.getLastD_mem_cons
    have := (List.pairwise_cons.1 hs).1 _ hm
    rw [e, this, Bool.or_true]

theorem blockBytes_length (rs : List Row) : (blockBytes rs).length =
    (frameBytes (rs.map Row.c0)).length + (frameBytes (rs.map Row.c1)).length +
      (frameBytes (rs.map Row.c2)).length + (frameBytes (rs.map Row.g)).length := by
  simp [blockBytes, Nat.add_assoc]

theorem rowSumGo_eq : ∀ (ms : List BlockMeta) (acc : Nat), rowSumGo ms acc = acc + (ms.map BlockMeta.rows).sum
  | [], acc => by simp [rowSumGo]
  | m :: ms, acc => by
    simp only [rowSumGo, rowSumGo_eq ms, List.map_cons, List.sum_cons]
    omega

/-- The blocks of a strictly increasing list of rows, each nonempty and of
    at most `L < 2^28` rows of 64-bit ids, encode, and their PRM1 entries
    form a chain from `off` when the bytes stay below `2^64`. -/
theorem encodeBlocks_some (L : Nat) (hL : L < 268435456) : ∀ (rss : List (List Row)) (off : Nat),
    (∀ rs ∈ rss, rs ≠ [] ∧ rs.length ≤ L ∧ rs.all Row.fits = true) →
    rss.flatten.Pairwise (fun a b => a.lt b = true) →
    off + 36 * rss.flatten.length < 18446744073709551616 →
    ∃ ms bs, encodeBlocks off rss = some (ms, bs) ∧ chainGo off ms = true ∧
      ms.length ≤ rss.flatten.length ∧ (ms.map BlockMeta.rows).sum = rss.flatten.length ∧
      ms.head?.map BlockMeta.first = rss.head?.map (·.headD default)
  | [], off, _, _, _ => ⟨[], [], rfl, rfl, by simp, by simp, rfl⟩
  | rs :: rss, off, hb, hp, hoff => by
    obtain ⟨hne, hlen, hf⟩ := hb rs List.mem_cons_self
    have hp' := List.pairwise_append.1 (by simpa using hp)
    have hadm := blockAdmitted_of rs hne (by omega) hp'.1 hf
    have f0 := frameBytes_length (rs.map Row.c0)
    have f1 := frameBytes_length (rs.map Row.c1)
    have f2 := frameBytes_length (rs.map Row.c2)
    have f3 := frameBytes_length (rs.map Row.g)
    simp only [List.length_map] at f0 f1 f2 f3
    have hpos : 0 < rs.length := List.length_pos_iff.2 hne
    have hbl := blockBytes_length rs
    simp only [List.flatten_cons, List.length_append] at hoff
    obtain ⟨ms, bs, h1, h2, h3, h4, h5⟩ := encodeBlocks_some L hL rss (off + (blockBytes rs).length)
      (fun r hr => hb r (List.mem_cons_of_mem _ hr)) hp'.2.1 (by omega)
    let m : BlockMeta := ⟨rs.headD default, rs.getLastD default, rs.length, off,
      (frameBytes (rs.map Row.c0)).length, (frameBytes (rs.map Row.c1)).length,
      (frameBytes (rs.map Row.c2)).length, (frameBytes (rs.map Row.g)).length⟩
    have he : encodeBlock? off rs = some (m, blockBytes rs) := by
      unfold encodeBlock?; rw [if_pos hadm]
    refine ⟨m :: ms, blockBytes rs ++ bs, ?_, ?_, ?_, ?_, ?_⟩
    · simp [encodeBlocks, he, h1]
    · obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hfr : ∀ x ∈ r :: rest, x.fits = true := fun x hx => List.all_eq_true.1 hf x hx
      have hmeta : metaFits m = true := by
        unfold metaFits
        simp only [m, Bool.and_eq_true, decide_eq_true_eq, L4Factoidal.two32_eq, L4Factoidal.two64_eq]
        refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfr _ List.mem_cons_self, hfr _ (by simp only [List.getLastD_cons]; exact List.getLastD_mem_cons)⟩, hpos⟩, by omega⟩, by omega⟩,
          by omega⟩, by omega⟩, by omega⟩, by omega⟩, Row.le_head_last r rest hp'.1⟩
      have hsize : m.size = (blockBytes (r :: rest)).length := by
        rw [hbl]; rfl
      have hoffm : (m.offset == off) = true := by simp [m]
      unfold chainGo
      rw [if_pos (by rw [hmeta, hoffm]; rfl)]
      cases ms with
      | nil => rfl
      | cons n ms' =>
        cases rss with
        | nil => simp at h5
        | cons rs' rss' =>
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h5
          have hlast : m.last ∈ r :: rest := by
            show (r :: rest).getLastD default ∈ r :: rest
            simp only [List.getLastD_cons]; exact List.getLastD_mem_cons
          have hrs' : rs' ≠ [] := (hb rs' (by simp)).1
          have hfirst : n.first ∈ (rs' :: rss').flatten := by
            rw [h5]
            obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hrs'
            simp
          have hlt := hp'.2.2 _ hlast _ hfirst
          simp only [hlt, if_true]
          rw [hsize]
          exact h2
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simp [h4, m]
    · rfl

theorem toPermRow_fits (k : Nat) (r : Row) (h : r.fits = true) : (Overlay.toPermRow k r).fits = true := by
  obtain ⟨h0, h1, h2, h3⟩ := toPermRow_cols k r
  simp only [Row.fits, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rcases h0 with e | e | e <;> rw [e] <;> omega
  · rcases h1 with e | e | e <;> rw [e] <;> omega
  · rcases h2 with e | e | e <;> rw [e] <;> omega
  · rw [h3]; omega

/-- Permutation `k` of rows of 64-bit ids, fewer than `2^36` of them, in
    blocks of at most `max B 1 < 2^28` rows: its blocks and its PRM1 list
    encode. -/
theorem packPerm_some (B k : Nat) (hB : B < 268435456) (hk : k < 4) (spo : List Row)
    (hn : spo.length < 68719476736) (hf : ∀ r ∈ spo, r.fits = true) :
    ∃ ms bytes, packPerm? B k spo = some (ms, bytes) ∧ ∃ r, encodePrm? k ms = some r := by
  let rows := sortUniq rowCmp (spo.map (Overlay.toPermRow k))
  have hrows : rows.Pairwise (fun a b => a.lt b = true) :=
    (sortUniq_pairwise strict_rowCmp _).imp fun h => (rowCmp_lt _ _).1 h
  have hlen : rows.length ≤ spo.length := by
    have := sortUniq_length_le rowCmp (spo.map (Overlay.toPermRow k))
    simpa using this
  have hflat := cutRows_flatten B rows
  have hblocks : ∀ rs ∈ cutRows B rows, rs ≠ [] ∧ rs.length ≤ max B 1 ∧ rs.all Row.fits = true := by
    intro rs hrs
    obtain ⟨h1, h2⟩ := cutGo_blocks B (max 1 (B / 16)) rows [] (by simp) rs hrs
    refine ⟨h1, h2, List.all_eq_true.2 fun r hr => ?_⟩
    have hr' : r ∈ rows := hflat ▸ List.mem_flatten.2 ⟨rs, hrs, hr⟩
    rw [mem_sortUniq strict_rowCmp, List.mem_map] at hr'
    obtain ⟨r0, hr0, rfl⟩ := hr'
    exact toPermRow_fits k r0 (hf r0 hr0)
  obtain ⟨ms, bs, h1, h2, h3, h4, _⟩ := encodeBlocks_some (max B 1) (by omega) (cutRows B rows)
    prbHeaderBytes hblocks (by rw [hflat]; exact hrows) (by rw [hflat]; unfold prbHeaderBytes; omega)
  rw [hflat] at h3 h4
  refine ⟨ms, prbHeader k ++ bs, by simp [packPerm?, rows, h1], prmBytes k ms, ?_⟩
  unfold encodePrm? prmAdmitted
  rw [if_pos]
  simp only [Bool.and_eq_true, decide_eq_true_eq, L4Factoidal.two64_eq, rowSum, rowSumGo_eq]
  exact ⟨⟨⟨hk, h2⟩, by omega⟩, by omega⟩

/-! ## The pack -/

/-- `packSpec` returns a generation on the domain: blocks of fewer than
    `2^28` rows (`hB`), at most `2^36` terms in the input (`hn`), and every
    term with an inline id or a dictionary key of fewer than `2^24` bytes
    (`hfit`). -/
theorem packSpec_some (B : Nat) (qs : List Quad) (decl : List Subject)
    (hB : B < 268435456) (hn : 4 * qs.length + decl.length < 68719476736)
    (hfit : ∀ t ∈ termsOf qs decl, termFits t = true) :
    ∃ G F, packSpec B qs decl = some (G, F) := by
  have htl := termsOf_length qs decl
  obtain ⟨keys, hkeys, hkl, hkb⟩ := keysOf_some (termsOf qs decl) hfit
  have hspec := keysOf_spec _ _ hkeys
  obtain ⟨gdv, gdx, hdict⟩ := encodeDict_some keys hspec.1 (by omega) hkb
  have hid : ∀ t ∈ termsOf qs decl, ∃ n, idOf? keys t = some n :=
    idOf_some _ keys hkeys (by rw [two60_eq]; omega)
  obtain ⟨spo, hspo, hspol⟩ := allSome_some (spoRow? keys) qs fun q hq =>
    Option.isSome_iff_exists.2 (spoRow_some keys q fun t ht => hid t (mem_termsOf_quad qs decl q hq t ht))
  obtain ⟨gids, hgids, _⟩ := allSome_some (fun g => idOf? keys g.toTerm) (qs.filterMap (·.2) ++ decl)
    fun g hg => by
      refine Option.isSome_iff_exists.2 (hid _ ?_)
      rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨q, hq, hqg⟩ := List.mem_filterMap.1 hg
        refine mem_termsOf_quad qs decl q hq _ ?_
        obtain ⟨tr, g'⟩ := q
        simp only at hqg
        subst hqg
        simp [quadTerms]
      · unfold termsOf
        exact List.mem_append_right _ (List.mem_map.2 ⟨g, hg, rfl⟩)
  have hfits : ∀ r ∈ spo, r.fits = true := fun r hr => by
    obtain ⟨q, _, hq⟩ := (allSome_mem _ qs spo hspo).1 r hr
    exact spoRow_fits keys q r hq
  have hsn : spo.length < 68719476736 := by omega
  obtain ⟨ms0, b0, p0, r0, e0⟩ := packPerm_some B 0 hB (by decide) spo hsn hfits
  obtain ⟨ms1, b1, p1, r1, e1⟩ := packPerm_some B 1 hB (by decide) spo hsn hfits
  obtain ⟨ms2, b2, p2, r2, e2⟩ := packPerm_some B 2 hB (by decide) spo hsn hfits
  obtain ⟨ms3, b3, p3, r3, e3⟩ := packPerm_some B 3 hB (by decide) spo hsn hfits
  unfold termsOf at hkeys
  unfold packSpec
  simp only [hkeys, hdict, hspo, hgids, p0, p1, p2, p3, e0, e1, e2, e3, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  exact ⟨_, _, rfl⟩

end L4Factoidal.Storage.Sbm11.PackSpec
