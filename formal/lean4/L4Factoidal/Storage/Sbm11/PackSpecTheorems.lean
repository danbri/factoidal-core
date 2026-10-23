/-
L4Factoidal.Storage.Sbm11.PackSpecTheorems — the generation of the pure
packer specification passes the activation checks and denotes its input
(https://github.com/danbri/factoidal/issues/776; row L3c of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

For `packSpec B qs decl = some (G, F)` (`PackSpec.lean`):

* `packSpec_written`: `FileGenTheorems.Written G F`, and no blocks in
  permutations 4 and above;
* `packSpec_check`: `G.check = true` (the dictionary check `keysOk`; per
  permutation the PRM1 admission and `decodeBlockAt` of every block, every
  row id the code of a term, the graph ids 0 or named, the rows a
  permutation of the SPO rows; the SPO subjects IRIs or blank nodes and the
  predicates IRIs; the named graph ids distinct codes of IRIs or blank
  nodes);
* `packSpec_default`, `packSpec_named`, `packSpec_names`: `denote G` is the
  input up to `normalizeTerm` of the objects and the order of triples (as
  sets: a triple is in the default graph, or in the graph named `g`, exactly
  when a quad of that graph has it, with its language tags in lower case;
  the named graphs are the graph names of the quads and of `decl`);
* `harness_where_allowed_packed`: the WHERE clause theorem of the harness
  (`MemGenWhereTheorems.harness_where_allowed_mem`) for `F.store`, the store
  over the files, with the query hypotheses `QHyps` only.

Steps: `sortUniq` is sorted, without duplicates, and has the elements of its
input (`StrictCmp`, for `cmpKey`, `rowCmp` and `compare` on `Nat`); a block
that `encodeBlock?` writes decodes from any buffer that holds its bytes at
its offset (`decodeBlockAt_encode`, with `decodeColumnAt_frame` and
`decodeColumnAt_le`); the blocks of `cutRows` flatten to the rows
(`cutRows_flatten`, `encodeBlocks_spec`, `packPerm_spec`).

Not proved here: that `packSpec` is `some` (it is `none` when an encoder
refuses: a term with no key, more than `2^60` keys, a block or a PRM1 list
outside the encoders' bounds; tested: `some` on every census input); that
the `IO` packer writes the bytes of `packSpec` (tested byte for byte by
`l4sbm11 packspec-check`); that `Allowed` is invariant under a permutation
of a graph's triples (needed to state the answer for the input `Dataset`
rather than for `denote G`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PackSpec
import L4Factoidal.Storage.Sbm11.ColumnTheorems
import L4Factoidal.Storage.Sbm11.BlockAtTheorems
import L4Factoidal.Storage.Sbm11.FilterIdTheorems

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.Dict (cmpKey encodeDict? bytesToList)

/-! ## Sorting without duplicates -/

/-- `cmp` is a strict total order: `.eq` exactly on equal elements, `.lt`
    and `.gt` swap, `.lt` is transitive. -/
structure StrictCmp {α : Type} (cmp : α → α → Ordering) : Prop where
  eq_iff : ∀ a b, cmp a b = .eq ↔ a = b
  swap : ∀ a b, cmp a b = .lt ↔ cmp b a = .gt
  trans : ∀ a b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt

section sort
variable {α : Type} {cmp : α → α → Ordering} (H : StrictCmp cmp)
include H

theorem mem_insertUniq (a x : α) : ∀ l, x ∈ insertUniq cmp a l ↔ x = a ∨ x ∈ l
  | [] => by simp [insertUniq]
  | b :: bs => by
    unfold insertUniq
    cases h : cmp a b with
    | lt => simp
    | eq =>
      have := (H.eq_iff a b).1 h
      subst this
      simp
    | gt =>
      have ih := mem_insertUniq a x bs
      simp only [List.mem_cons, ih]
      exact or_left_comm

theorem pairwise_insertUniq (a : α) : ∀ l, l.Pairwise (fun x y => cmp x y = .lt) →
    (insertUniq cmp a l).Pairwise (fun x y => cmp x y = .lt)
  | [] => fun _ => by simp [insertUniq]
  | b :: bs => fun hp => by
    unfold insertUniq
    have hp' := List.pairwise_cons.1 hp
    cases h : cmp a b with
    | lt =>
      refine List.Pairwise.cons ?_ hp
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h
      · exact H.trans _ _ _ h (hp'.1 y hy)
    | eq => exact hp
    | gt =>
      refine List.Pairwise.cons ?_ (pairwise_insertUniq a bs hp'.2)
      intro y hy
      rcases (mem_insertUniq H a y bs).1 hy with rfl | hy
      · exact (H.swap b y).2 h
      · exact hp'.1 y hy

theorem sortUniq_go : ∀ (l acc : List α), acc.Pairwise (fun x y => cmp x y = .lt) →
    (l.foldl (fun acc a => insertUniq cmp a acc) acc).Pairwise (fun x y => cmp x y = .lt) ∧
      ∀ x, x ∈ l.foldl (fun acc a => insertUniq cmp a acc) acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc, h => ⟨h, by simp⟩
  | a :: l, acc, h => by
    obtain ⟨h1, h2⟩ := sortUniq_go l (insertUniq cmp a acc) (pairwise_insertUniq H a acc h)
    refine ⟨h1, fun x => ?_⟩
    simp only [List.foldl_cons, h2, mem_insertUniq H, List.mem_cons]
    rw [or_comm (a := x = a), or_assoc]

theorem sortUniq_pairwise (l : List α) : (sortUniq cmp l).Pairwise (fun x y => cmp x y = .lt) :=
  (sortUniq_go H l [] List.Pairwise.nil).1

theorem mem_sortUniq (l : List α) (x : α) : x ∈ sortUniq cmp l ↔ x ∈ l := by
  have := (sortUniq_go H l [] List.Pairwise.nil).2 x
  unfold sortUniq
  simpa using this

theorem sortUniq_nodup (l : List α) : (sortUniq cmp l).Nodup :=
  (sortUniq_pairwise H l).imp fun {a b} h e => by
    subst e
    rw [(H.eq_iff a a).2 rfl] at h
    cases h

end sort

/-! ## The two orders -/

theorem strict_cmpKey : StrictCmp cmpKey :=
  ⟨Dict.cmpKey_eq_iff, Dict.cmpKey_swap, Dict.cmpKey_lt_trans⟩

theorem Row.lt_iff (a b : Row) : a.lt b = true ↔
    (a.c0 < b.c0 ∨ (a.c0 = b.c0 ∧ (a.c1 < b.c1 ∨ (a.c1 = b.c1 ∧ (a.c2 < b.c2 ∨ (a.c2 = b.c2 ∧ a.g < b.g)))))) := by
  unfold Row.lt
  by_cases h0 : a.c0 = b.c0 <;> by_cases h1 : a.c1 = b.c1 <;> by_cases h2 : a.c2 = b.c2 <;>
    simp [h0, h1, h2] <;> omega

theorem Row.ext' (a b : Row) : a = b ↔ a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2 ∧ a.g = b.g := by
  cases a; cases b; simp

theorem Row.lt_irrefl (a : Row) : a.lt a = false := by
  cases h : a.lt a
  · rfl
  · rw [Row.lt_iff] at h; omega

theorem rowCmp_lt (a b : Row) : rowCmp a b = .lt ↔ a.lt b = true := by
  unfold rowCmp
  by_cases h : a.lt b = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, iff_false]
    split <;> simp

theorem rowCmp_gt (a b : Row) : rowCmp a b = .gt ↔ a.lt b = false ∧ a ≠ b := by
  unfold rowCmp
  by_cases h : a.lt b = true
  · simp [h]
  · have h' : a.lt b = false := by simpa using h
    by_cases e : a = b
    · subst e; simp [Row.lt_irrefl]
    · simp [h', e]

theorem strict_rowCmp : StrictCmp rowCmp := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b c => ?_⟩
  · unfold rowCmp
    by_cases h : a.lt b = true
    · have hne : a ≠ b := by
        intro e; subst e; rw [Row.lt_irrefl] at h; cases h
      simp [h, hne]
    · by_cases e : a = b
      · subst e; simp [Row.lt_irrefl]
      · simp [h, e]
  · rw [rowCmp_lt, rowCmp_gt]
    constructor
    · intro h
      refine ⟨?_, fun e => ?_⟩
      · cases h' : b.lt a
        · rfl
        · rw [Row.lt_iff] at h h'; omega
      · subst e; rw [Row.lt_irrefl] at h; cases h
    · rintro ⟨h1, h2⟩
      have h2' : ¬ (b.c0 = a.c0 ∧ b.c1 = a.c1 ∧ b.c2 = a.c2 ∧ b.g = a.g) := fun e => h2 ((Row.ext' b a).2 e)
      have h1' : ¬ b.lt a = true := by rw [h1]; simp
      rw [Row.lt_iff] at h1' ⊢; omega
  · rw [rowCmp_lt, rowCmp_lt, rowCmp_lt]
    intro h1 h2
    rw [Row.lt_iff] at h1 h2 ⊢; omega

/-! ## `allSome` -/

theorem allSome_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β), allSome f l = some l' →
    (∀ b ∈ l', ∃ a ∈ l, f a = some b) ∧ (∀ a ∈ l, ∃ b ∈ l', f a = some b)
  | [], l', h => by
    simp only [allSome, Option.some.injEq] at h
    subst h; simp
  | a :: as, l', h => by
    simp only [allSome, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := allSome_mem f as bs hbs
    refine ⟨fun y hy => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, hb⟩
      · obtain ⟨x, hx, e⟩ := h1 y hy; exact ⟨x, List.mem_cons_of_mem _ hx, e⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, hb⟩
      · obtain ⟨y, hy, e⟩ := h2 x hx; exact ⟨y, List.mem_cons_of_mem _ hy, e⟩


/-! ## The end of a decoded frame is inside the bytes -/

theorem get64At_le (b : ByteArray) (i v j : Nat) (h : get64At b i = some (v, j)) : j ≤ b.size := by
  unfold get64At at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · cases h

theorem getVarAtGo_le (b : ByteArray) : ∀ f acc i v j, getVarAtGo b f acc i = some (v, j) → j ≤ b.size
  | 0, _, _, _, _, h => by simp [getVarAtGo] at h
  | f + 1, acc, i, v, j, h => by
    unfold getVarAtGo at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · exact getVarAtGo_le b f _ _ v j h
    · cases h

theorem rawAtGo_le (b : ByteArray) : ∀ n i (acc : Array Nat) c j, i ≤ b.size →
    rawAtGo b n i acc = some (c, j) → j ≤ b.size
  | 0, i, acc, c, j, hi, h => by
    simp only [rawAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | n + 1, i, acc, c, j, _, h => by
    unfold rawAtGo at h
    split at h
    · cases h
    · rename_i v j' hg
      exact rawAtGo_le b n j' _ c j (get64At_le b i v j' hg) h

theorem deltaAtGo_le (b : ByteArray) : ∀ n prev i (acc : Array Nat) c j, i ≤ b.size →
    deltaAtGo b n prev i acc = some (c, j) → j ≤ b.size
  | 0, _, i, acc, c, j, hi, h => by
    simp only [deltaAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | n + 1, prev, i, acc, c, j, _, h => by
    unfold deltaAtGo at h
    split at h
    · cases h
    · rename_i z j' hg
      split at h
      · cases h
      · split at h
        · exact deltaAtGo_le b n _ j' _ c j (getVarAtGo_le b _ _ _ z j' hg) h
        · cases h

theorem decodeColumnAt_le (b : ByteArray) (n i : Nat) (c : Array Nat) (j : Nat)
    (h : decodeColumnAt b n i = some (c, j)) : j ≤ b.size := by
  unfold decodeColumnAt at h
  split at h
  · rename_i hi
    dsimp only at h
    split at h
    · split at h
      · rename_i v j' hg
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact get64At_le b _ v j' hg
      · cases h
    · split at h
      · exact rawAtGo_le b n (i + 1) _ c j (by omega) h
      · split at h
        · exact deltaAtGo_le b n 0 (i + 1) _ c j (by omega) h
        · cases h
  · cases h

/-- A frame `frameBytes xs` at position `i` of `b` decodes to `xs` and ends
    at `i` plus its length. -/
theorem decodeColumnAt_frame (b : ByteArray) (i : Nat) (xs : List Nat) (rest : List UInt8)
    (hxs : ∀ x ∈ xs, x < two64) (hb : (bytesToList b).drop i = frameBytes xs ++ rest) :
    decodeColumnAt b xs.length i = some (xs.toArray, i + (frameBytes xs).length) := by
  have henc : encodeColumn? xs = some (frameBytes xs) := by
    unfold encodeColumn? columnAdmitted
    rw [if_pos (List.all_eq_true.mpr fun x hx => by simpa using hxs x hx)]
  have hd := decodeColumn_encodeColumn? xs _ henc rest
  rw [← hb, ← decodeColumnAt_eq] at hd
  cases hc : decodeColumnAt b xs.length i with
  | none => rw [hc] at hd; cases hd
  | some q =>
    obtain ⟨c, j⟩ := q
    rw [hc] at hd
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨h1, h2⟩ := hd
    have hj := decodeColumnAt_le b _ i c j hc
    have hne : (frameBytes xs).length ≠ 0 := by
      unfold frameBytes
      split
      · simp
      · split
        · simp
        · split <;> simp
    have hl1 := congrArg List.length hb
    have hl2 := congrArg List.length h2
    simp only [List.length_drop, List.length_append, Dict.bytesToList_length] at hl1 hl2
    have hcj : c = xs.toArray := by
      apply Array.ext'; simpa using h1
    rw [hcj]
    congr 2
    omega

/-! ## A block decodes from the bytes `encodeBlock?` writes -/

theorem sortedGo_get (prev : Row) : ∀ (rs : List Row), sortedGo prev rs = true →
    ∀ j (hj : j + 1 < (prev :: rs).length), ((prev :: rs)[j]'(by omega)).lt ((prev :: rs)[j + 1]) = true
  | [], _, j, hj => by simp at hj
  | r :: rs, h, j, hj => by
    unfold sortedGo at h
    split at h
    · rename_i hlt
      cases j with
      | zero => simpa using hlt
      | succ j =>
        have := sortedGo_get r rs h j (by simp at hj ⊢; omega)
        simpa using this
    · cases h

theorem rowsSorted_get (rs : List Row) (h : rowsSorted rs = true) (j : Nat) (hj : j + 1 < rs.length) :
    (rs[j]'(by omega)).lt (rs[j + 1]) = true := by
  cases rs with
  | nil => simp at hj
  | cons r rs => exact sortedGo_get r rs h j hj

theorem colsSortedGo_of (c : Cols) (hc : ∀ j, j + 1 < c.size → (c.row j).lt (c.row (j + 1)) = true) :
    ∀ f i, colsSortedGo c f i = true
  | 0, _ => rfl
  | f + 1, i => by
    unfold colsSortedGo
    split
    · rename_i hi; rw [if_pos (hc i hi)]; exact colsSortedGo_of c hc f (i + 1)
    · rfl

/-- The columns of a list of rows. -/
def colsOf (rs : List Row) : Cols :=
  ⟨(rs.map Row.c0).toArray, (rs.map Row.c1).toArray, (rs.map Row.c2).toArray, (rs.map Row.g).toArray⟩

theorem colsOf_row (rs : List Row) (i : Nat) (hi : i < rs.length) : (colsOf rs).row i = rs[i] := by
  simp [colsOf, Cols.row, hi]

theorem colsOf_size (rs : List Row) : (colsOf rs).size = rs.length := by
  simp [colsOf, Cols.size]

/-- A block at offset `off` of `b`, where `b` from `off` holds the bytes
    `encodeBlock? off rs` writes: it decodes to the rows `rs`. -/
theorem decodeBlockAt_encode (b : ByteArray) (off : Nat) (rs : List Row) (m : BlockMeta) (bs rest : List UInt8)
    (h : encodeBlock? off rs = some (m, bs)) (hb : (bytesToList b).drop off = bs ++ rest) :
    m.offset = off ∧ decodeBlockAt b m off = .ok (colsOf rs) ∧ bs.length = m.size := by
  unfold encodeBlock? at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold blockAdmitted at hadm
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq] at hadm
    obtain ⟨⟨⟨⟨⟨⟨⟨hne, hsort⟩, hfits⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hadm
    have hf : ∀ r ∈ rs, r.c0 < two64 ∧ r.c1 < two64 ∧ r.c2 < two64 ∧ r.g < two64 := by
      intro r hr
      have := List.all_eq_true.mp hfits r hr
      simpa [Row.fits, and_assoc] using this
    refine ⟨rfl, ?_, by simp [blockBytes, BlockMeta.size]; omega⟩
    have hlen : off + (blockBytes rs).length ≤ b.size := by
      have := congrArg List.length hb
      simp only [List.length_drop, List.length_append, Dict.bytesToList_length] at this
      have : off ≤ b.size ∨ (blockBytes rs).length = 0 := by omega
      rcases this with h | h
      · omega
      · have : (blockBytes rs).length ≠ 0 := by
          simp only [blockBytes, List.length_append]
          have : (frameBytes (rs.map Row.g)).length ≠ 0 := by
            unfold frameBytes; split
            · simp
            · split
              · simp
              · split <;> simp
          omega
        omega
    have hbb : blockBytes rs = (frameBytes (rs.map Row.c0)) ++ (frameBytes (rs.map Row.c1)) ++ (frameBytes (rs.map Row.c2)) ++ (frameBytes (rs.map Row.g)) := rfl
    rw [hbb] at hb hlen
    have d0 : (bytesToList b).drop off = (frameBytes (rs.map Row.c0)) ++ ((frameBytes (rs.map Row.c1)) ++ (frameBytes (rs.map Row.c2)) ++ (frameBytes (rs.map Row.g)) ++ rest) := by rw [hb]; simp
    have d1 : (bytesToList b).drop (off + (frameBytes (rs.map Row.c0)).length) = (frameBytes (rs.map Row.c1)) ++ ((frameBytes (rs.map Row.c2)) ++ (frameBytes (rs.map Row.g)) ++ rest) := by
      rw [← List.drop_drop, d0, List.drop_left]; simp
    have d2 : (bytesToList b).drop (off + (frameBytes (rs.map Row.c0)).length + (frameBytes (rs.map Row.c1)).length) = (frameBytes (rs.map Row.c2)) ++ ((frameBytes (rs.map Row.g)) ++ rest) := by
      rw [← List.drop_drop, d1, List.drop_left]; simp
    have d3 : (bytesToList b).drop (off + (frameBytes (rs.map Row.c0)).length + (frameBytes (rs.map Row.c1)).length + (frameBytes (rs.map Row.c2)).length) = (frameBytes (rs.map Row.g)) ++ rest := by
      rw [← List.drop_drop, d2, List.drop_left]
    have e0 := decodeColumnAt_frame b off (rs.map Row.c0) _
      (fun x hx => by obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx; exact (hf r hr).1) d0
    have e1 := decodeColumnAt_frame b _ (rs.map Row.c1) _
      (fun x hx => by obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx; exact (hf r hr).2.1) d1
    have e2 := decodeColumnAt_frame b _ (rs.map Row.c2) _
      (fun x hx => by obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx; exact (hf r hr).2.2.1) d2
    have e3 := decodeColumnAt_frame b _ (rs.map Row.g) _
      (fun x hx => by obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx; exact (hf r hr).2.2.2) d3
    rw [List.length_map] at e0 e1 e2 e3
    have hpos : 0 < rs.length := List.length_pos_iff.2 hne
    have hfirst : (colsOf rs).row 0 = rs.headD default := by
      rw [colsOf_row rs 0 hpos]
      cases rs with
      | nil => simp at hpos
      | cons r rs => rfl
    have hlast : (colsOf rs).row (rs.length - 1) = rs.getLastD default := by
      rw [colsOf_row rs _ (by omega), List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [List.getElem?_eq_getElem (show rs.length - 1 < rs.length by omega)]
    have hsorted : colsSortedGo (colsOf rs) rs.length 0 = true := by
      apply colsSortedGo_of
      intro j hj
      rw [colsOf_size] at hj
      rw [colsOf_row rs j (by omega), colsOf_row rs (j + 1) hj]
      exact rowsSorted_get rs hsort j hj
    unfold decodeBlockAt
    simp only [BlockMeta.size, List.length_append] at hlen ⊢
    rw [if_neg (by omega), e0, e1, e2, e3]
    simp only [beq_self_eq_true, List.size_toArray, List.length_map, Bool.and_self, if_true]
    have hc : (⟨(rs.map Row.c0).toArray, (rs.map Row.c1).toArray, (rs.map Row.c2).toArray,
        (rs.map Row.g).toArray⟩ : Cols) = colsOf rs := rfl
    simp only [bind, Except.bind]
    rw [hc, hfirst, hlast, hsorted]
    simp [show rs.length ≠ 0 by omega, pure, Except.pure]
  · cases h


theorem encodeBlock?_rows (off : Nat) (rs : List Row) (m : BlockMeta) (bs : List UInt8)
    (h : encodeBlock? off rs = some (m, bs)) : m.rows = rs.length := by
  unfold encodeBlock? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · cases h

theorem range_map_colsOf (rs : List Row) : (List.range rs.length).map (colsOf rs).row = rs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact colsOf_row rs i h2

/-! ## The blocks of a permutation -/

theorem encodeBlocks_spec : ∀ (rss : List (List Row)) (off : Nat) (ms : List BlockMeta) (bs : List UInt8)
    (b : ByteArray) (rest : List UInt8), encodeBlocks off rss = some (ms, bs) →
    (bytesToList b).drop off = bs ++ rest →
    ms.flatMap (ScanFoldTheorems.blockRows b) = rss.flatten ∧
      ∀ m ∈ ms, ∃ cols, decodeBlockAt b m m.offset = .ok cols
  | [], off, ms, bs, b, rest, h, _ => by
    simp only [encodeBlocks, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | rs :: rss, off, ms, bs, b, rest, h, hb => by
    simp only [encodeBlocks, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨m, b1⟩, h1, ⟨ms', bs'⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hb1 : (bytesToList b).drop off = b1 ++ (bs' ++ rest) := by rw [hb]; simp
    obtain ⟨hoff, hdec, hsz⟩ := decodeBlockAt_encode b off rs m b1 _ h1 hb1
    have hb2 : (bytesToList b).drop (off + b1.length) = bs' ++ rest := by
      rw [← List.drop_drop, hb1, List.drop_left]
    obtain ⟨ih1, ih2⟩ := encodeBlocks_spec rss _ ms' bs' b rest h2 hb2
    have hrows := encodeBlock?_rows off rs m b1 h1
    have hbr : ScanFoldTheorems.blockRows b m = rs := by
      unfold ScanFoldTheorems.blockRows
      rw [hoff, hdec, hrows]
      exact range_map_colsOf rs
    refine ⟨by simp [hbr, ih1], fun m' hm' => ?_⟩
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact ⟨_, hoff ▸ hdec⟩
    · exact ih2 m' hm'

theorem cutGo_flatten (B c : Nat) : ∀ (xs cur : List Row), (cutGo B c xs cur).flatten = cur.reverse ++ xs
  | [], [] => by simp [cutGo]
  | [], y :: ys => by simp [cutGo]
  | x :: xs, [] => by simp [cutGo, cutGo_flatten B c xs [x]]
  | x :: xs, y :: ys => by
    unfold cutGo
    split
    · simp [cutGo_flatten B c xs [x]]
    · simp [cutGo_flatten B c xs (x :: y :: ys)]

theorem cutRows_flatten (B : Nat) (rows : List Row) : (cutRows B rows).flatten = rows := by
  simp [cutRows, cutGo_flatten]

theorem drop_header (k : Nat) (bs : List UInt8) :
    (bytesToList ⟨(prbHeader k ++ bs).toArray⟩).drop prbHeaderBytes = bs ++ [] := by
  simp [Dict.bytesToList_mk, prbHeader, prbHeaderBytes]

/-- Permutation `k` of `packPerm?`: its blocks decode, and their rows are
    the rows of the permutation sorted without duplicates. -/
theorem packPerm_spec (B k : Nat) (spo : List Row) (ms : List BlockMeta) (bytes : List UInt8)
    (h : packPerm? B k spo = some (ms, bytes)) :
    ms.flatMap (ScanFoldTheorems.blockRows ⟨bytes.toArray⟩) = sortUniq rowCmp (spo.map (Overlay.toPermRow k)) ∧
      ∀ m ∈ ms, ∃ cols, decodeBlockAt ⟨bytes.toArray⟩ m m.offset = .ok cols := by
  simp only [packPerm?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨⟨ms', bs⟩, h1, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := encodeBlocks_spec _ _ _ bs _ [] h1 (drop_header k bs)
  rw [cutRows_flatten] at this
  exact this


/-! ## What `packSpec` computes -/

/-- The terms whose keys make the dictionary. -/
def termsOf (qs : List Quad) (decl : List Subject) : List Term :=
  qs.flatMap quadTerms ++ decl.map Subject.toTerm

/-- What a `some` of `packSpec` is made of. -/
structure Facts (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen) : Prop where
  keys : keysOf? (termsOf qs decl) = some G.keys
  dict : ∃ v x, encodeDict? G.keys = some (v, x) ∧ F.gdv = ⟨v.toArray⟩ ∧ F.gdx = ⟨x.toArray⟩
  spo : ∃ spo, allSome (spoRow? G.keys) qs = some spo ∧
    ∀ k, k < 4 → ∃ bytes, packPerm? B k spo = some (G.ms k, bytes) ∧ G.prb k = ⟨bytes.toArray⟩ ∧
      ∃ r, encodePrm? k (G.ms k) = some r ∧ F.prm k = ⟨r.toArray⟩
  gids : ∃ gids, allSome (fun g => idOf? G.keys g.toTerm) (qs.filterMap (·.2) ++ decl) = some gids ∧
    G.named = (sortUniq compare gids).toArray.map UInt64.ofNat
  named : F.named = G.named
  prb : ∀ k, F.prb k = G.prb k
  high : ∀ k, 4 ≤ k → G.ms k = []

theorem k_cases (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem packSpec_facts (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) : Facts B qs decl G F := by
  unfold packSpec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨keys, hkeys, ⟨gdv, gdx⟩, hdict, spo, hspo, gids, hgids, ⟨ms0, b0⟩, h0, ⟨ms1, b1⟩, h1,
    ⟨ms2, b2⟩, h2, ⟨ms3, b3⟩, h3, r0, e0, r1, e1, r2, e2, r3, e3, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨hkeys, ⟨gdv, gdx, hdict, rfl, rfl⟩, ⟨spo, hspo, fun k hk => ?_⟩, ⟨gids, hgids, rfl⟩, rfl,
    fun _ => rfl, fun k hk => ?_⟩
  · rcases k_cases k hk with rfl | rfl | rfl | rfl
    · exact ⟨b0, h0, rfl, r0, e0, rfl⟩
    · exact ⟨b1, h1, rfl, r1, e1, rfl⟩
    · exact ⟨b2, h2, rfl, r2, e2, rfl⟩
    · exact ⟨b3, h3, rfl, r3, e3, rfl⟩
  · show pick k ms0 ms1 ms2 ms3 [] = []
    match k, hk with
    | k + 4, _ => rfl

/-- The files of `packSpec` hold the bytes the encoders write for its
    generation (`FileGenTheorems.Written`). -/
theorem packSpec_written (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) : Written G F ∧ ∀ k, 4 ≤ k → G.ms k = [] := by
  have hf := packSpec_facts B qs decl G F h
  refine ⟨⟨hf.dict, fun k hk => ?_, hf.prb, hf.named⟩, hf.high⟩
  obtain ⟨_, _, hk'⟩ := hf.spo
  obtain ⟨_, _, _, r, hr, hp⟩ := hk' k hk
  exact ⟨r, hr, hp⟩


/-! ## The dictionary keys and the ids -/

theorem keysOf_spec (ts : List Term) (keys : List Key) (h : keysOf? ts = some keys) :
    keys.Pairwise (fun a b => cmpKey a b = .lt) ∧
      (∀ k ∈ keys, ∃ t ∈ ts, termKey? (normalizeTerm t) = some k) ∧
      (∀ t ∈ ts, inlineCode? (normalizeTerm t) = none → ∃ k, termKey? (normalizeTerm t) = some k ∧ k ∈ keys) := by
  unfold keysOf? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨ks, hks, rfl⟩ := h
  obtain ⟨h1, h2⟩ := allSome_mem _ ts ks hks
  refine ⟨sortUniq_pairwise strict_cmpKey _, fun k hk => ?_, fun t ht hin => ?_⟩
  · rw [mem_sortUniq strict_cmpKey, List.mem_filterMap] at hk
    obtain ⟨o, ho, ho'⟩ := hk
    simp only [id] at ho'
    subst ho'
    obtain ⟨t, ht, hkt⟩ := h1 _ ho
    refine ⟨t, ht, ?_⟩
    unfold keyOfTerm? at hkt
    dsimp only at hkt
    split at hkt
    · simp at hkt
    · simpa using hkt
  · obtain ⟨o, ho, hkt⟩ := h2 t ht
    unfold keyOfTerm? at hkt
    dsimp only at hkt
    rw [hin] at hkt
    cases hk : termKey? (normalizeTerm t) with
    | none => rw [hk] at hkt; cases hkt
    | some k =>
      rw [hk] at hkt
      simp only [Option.map_some, Option.some.injEq] at hkt
      subst hkt
      refine ⟨k, rfl, ?_⟩
      rw [mem_sortUniq strict_cmpKey, List.mem_filterMap]
      exact ⟨some k, ho, rfl⟩

theorem keysOk_of (ts : List Term) (keys : List Key) (h : keysOf? ts = some keys) : keysOk keys = true := by
  obtain ⟨_, h2, _⟩ := keysOf_spec ts keys h
  unfold keysOk
  apply List.all_eq_true.mpr
  intro k hk
  obtain ⟨t, _, htk⟩ := h2 k hk
  rw [decodeKey?_termKey? _ k htk]
  simp [FilterIdTheorems.normalize_idem]

theorem idOkB_of (keys : List Key) (u : Term) (n : Nat) (h : toCode? keys u = some n) : idOkB keys n = true := by
  unfold idOkB
  rw [ofCode?_toCode? keys u n h]
  simp [h]

/-- The term of the id of a subject is the subject. -/
theorem normalize_subject (s : Subject) : normalizeTerm s.toTerm = s.toTerm := by
  cases s <;> rfl

theorem subjB_of (keys : List Key) (s : Subject) (n : Nat) (h : toCode? keys s.toTerm = some n) :
    subjB keys n = true := by
  unfold subjB
  rw [ofCode?_toCode? keys _ n h]
  cases s <;> rfl

theorem iriB_of (keys : List Key) (p : WfIri) (n : Nat) (h : toCode? keys (.iri p) = some n) :
    iriB keys n = true := by
  unfold iriB
  rw [ofCode?_toCode? keys _ n h]

theorem code_lt (keys : List Key) (u : Term) (n : Nat) (h : toCode? keys u = some n) : n < 18446744073709551616 := by
  have := (toCode?_range keys u n h).2
  rw [two60_eq] at this
  omega


/-! ## Rows -/

theorem spoRow_spec (keys : List Key) (q : Quad) (r : Row) (h : spoRow? keys q = some r) :
    toCode? keys q.1.s.toTerm = some r.c0 ∧ toCode? keys (.iri q.1.p) = some r.c1 ∧
      toCode? keys (normalizeTerm q.1.o) = some r.c2 ∧
      ((q.2 = none ∧ r.g = 0) ∨ ∃ g, q.2 = some g ∧ toCode? keys g.toTerm = some r.g) := by
  obtain ⟨tr, g⟩ := q
  cases g with
  | none =>
    simp only [spoRow?, idOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, rfl, rfl⟩ := h
    rw [normalize_subject] at ha
    exact ⟨ha, hb, hc, Or.inl ⟨rfl, rfl⟩⟩
  | some g =>
    simp only [spoRow?, idOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    rw [normalize_subject] at ha hd
    exact ⟨ha, hb, hc, Or.inr ⟨g, rfl, hd⟩⟩

theorem toPermRow_cols (k : Nat) (r : Row) :
    ((Overlay.toPermRow k r).c0 = r.c0 ∨ (Overlay.toPermRow k r).c0 = r.c1 ∨ (Overlay.toPermRow k r).c0 = r.c2) ∧
    ((Overlay.toPermRow k r).c1 = r.c0 ∨ (Overlay.toPermRow k r).c1 = r.c1 ∨ (Overlay.toPermRow k r).c1 = r.c2) ∧
    ((Overlay.toPermRow k r).c2 = r.c0 ∨ (Overlay.toPermRow k r).c2 = r.c1 ∨ (Overlay.toPermRow k r).c2 = r.c2) ∧
    (Overlay.toPermRow k r).g = r.g := by
  match k with
  | 0 => simp [Overlay.toPermRow, Overlay.permCols, Overlay.quadPos]
  | 1 => simp [Overlay.toPermRow, Overlay.permCols, Overlay.quadPos]
  | 2 => simp [Overlay.toPermRow, Overlay.permCols, Overlay.quadPos]
  | k + 3 => simp [Overlay.toPermRow, Overlay.permCols, Overlay.quadPos]

theorem of_toPermRow (k : Nat) (hk : k < 4) (r : Row) : Overlay.ofPermRow k (Overlay.toPermRow k r) = r := by
  rcases k_cases k hk with rfl | rfl | rfl | rfl <;> rfl

theorem toPermRow_two (r : Row) : Overlay.toPermRow 2 r = r := rfl

theorem ofPermRow_inj (k : Nat) (hk : k < 4) (a b : Row) (h : Overlay.ofPermRow k a = Overlay.ofPermRow k b) :
    a = b := by
  rw [Row.ext'] at h ⊢
  rcases k_cases k hk with rfl | rfl | rfl | rfl <;> simp [Overlay.ofPermRow] at h <;> omega

section gen
variable (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
  (h : packSpec B qs decl = some (G, F))
include h

theorem rows_eq (spo : List Row) (hspo : allSome (spoRow? G.keys) qs = some spo) (k : Nat) (hk : k < 4) :
    G.rows k = sortUniq rowCmp (spo.map (Overlay.toPermRow k)) := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨spo', hspo', hk'⟩ := hf.spo
  rw [hspo] at hspo'
  simp only [Option.some.injEq] at hspo'
  subst hspo'
  obtain ⟨bytes, hp, hprb, _⟩ := hk' k hk
  unfold MemGen.rows
  rw [hprb]
  exact (packPerm_spec B k spo _ bytes hp).1

theorem mem_rows (spo : List Row) (hspo : allSome (spoRow? G.keys) qs = some spo) (k : Nat) (hk : k < 4)
    (r : Row) : r ∈ G.rows k ↔ ∃ r0 ∈ spo, Overlay.toPermRow k r0 = r := by
  rw [rows_eq B qs decl G F h spo hspo k hk, mem_sortUniq strict_rowCmp, List.mem_map]

end gen


theorem strict_compare : StrictCmp (compare : Nat → Nat → Ordering) := by
  refine ⟨fun a b => Nat.compare_eq_eq, fun a b => ?_, fun a b c => ?_⟩
  · rw [Nat.compare_eq_lt, Nat.compare_eq_gt]
  · rw [Nat.compare_eq_lt, Nat.compare_eq_lt, Nat.compare_eq_lt]; omega

theorem toNat_ofNat_code (n : Nat) (h : n < 18446744073709551616) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

section check
variable (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
  (h : packSpec B qs decl = some (G, F))
include h

/-- Every graph id is the code of a graph name of the quads or of `decl`. -/
theorem gid_spec (gids : List Nat)
    (hg : allSome (fun g => idOf? G.keys g.toTerm) (qs.filterMap (·.2) ++ decl) = some gids) :
    (∀ b ∈ gids, ∃ g, (g ∈ qs.filterMap (·.2) ∨ g ∈ decl) ∧ toCode? G.keys g.toTerm = some b) ∧
      ∀ g, (g ∈ qs.filterMap (·.2) ∨ g ∈ decl) → ∃ b ∈ gids, toCode? G.keys g.toTerm = some b := by
  obtain ⟨h1, h2⟩ := allSome_mem _ _ gids hg
  refine ⟨fun b hb => ?_, fun g hg' => ?_⟩
  · obtain ⟨g, hgm, e⟩ := h1 b hb
    unfold idOf? at e; rw [normalize_subject] at e
    exact ⟨g, List.mem_append.1 hgm, e⟩
  · obtain ⟨b, hb, e⟩ := h2 g (List.mem_append.2 hg')
    unfold idOf? at e; rw [normalize_subject] at e
    exact ⟨b, hb, e⟩

theorem named_mem (gids : List Nat) (hnamed : G.named = (sortUniq compare gids).toArray.map UInt64.ofNat)
    (x : UInt64) : x ∈ G.named.toList ↔ ∃ b ∈ gids, UInt64.ofNat b = x := by
  rw [hnamed]
  simp only [Array.toList_map, List.toList_toArray, List.mem_map, mem_sortUniq strict_compare]

/-- The generation of `packSpec` passes `MemGen.check`. -/
theorem packSpec_check : G.check = true := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨spo, hspo, hperm⟩ := hf.spo
  obtain ⟨gids, hgids, hnamed⟩ := hf.gids
  obtain ⟨hs1, hs2⟩ := allSome_mem _ qs spo hspo
  obtain ⟨hg1, hg2⟩ := gid_spec B qs decl G F h gids hgids
  -- an SPO row: the codes of a quad's terms
  have hrow : ∀ r0 ∈ spo, idOkB G.keys r0.c0 = true ∧ idOkB G.keys r0.c1 = true ∧ idOkB G.keys r0.c2 = true ∧
      subjB G.keys r0.c0 = true ∧ iriB G.keys r0.c1 = true ∧
      (r0.g == 0 || G.named.contains r0.g.toUInt64) = true := by
    intro r0 hr0
    obtain ⟨q, hq, hqr⟩ := hs1 r0 hr0
    obtain ⟨e0, e1, e2, e3⟩ := spoRow_spec G.keys q r0 hqr
    refine ⟨idOkB_of _ _ _ e0, idOkB_of _ _ _ e1, idOkB_of _ _ _ e2, subjB_of _ _ _ e0, iriB_of _ _ _ e1, ?_⟩
    rcases e3 with ⟨_, hg0⟩ | ⟨g, hqg, hgc⟩
    · simp [hg0]
    · have hgm : g ∈ qs.filterMap (·.2) := List.mem_filterMap.2 ⟨q, hq, hqg⟩
      obtain ⟨b, hb, hbc⟩ := hg2 g (Or.inl hgm)
      rw [hgc] at hbc
      simp only [Option.some.injEq] at hbc
      subst hbc
      have : G.named.contains r0.g.toUInt64 = true := by
        apply Array.contains_iff_mem.2
        rw [← Array.mem_toList_iff, named_mem B qs decl G F h gids hnamed]
        exact ⟨_, hb, rfl⟩
      rw [this, Bool.or_true]
  have hrows := mem_rows B qs decl G F h spo hspo
  simp only [MemGen.check, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
  refine ⟨⟨⟨keysOk_of _ _ hf.keys, ?_⟩, ?_⟩, ?_⟩
  · -- the four permutations
    have hk : ∀ k, k < 4 → G.prmOk k = true ∧ G.rowsOk k = true ∧ G.permOk k = true := by
      intro k hk
      obtain ⟨bytes, hp, hprb, r, hr, _⟩ := hperm k hk
      refine ⟨?_, ?_, ?_⟩
      · unfold MemGen.prmOk
        have hadm : prmAdmitted k (G.ms k) = true := by
          unfold encodePrm? at hr; split at hr
          · assumption
          · cases hr
        rw [hadm, Bool.true_and, hprb]
        apply List.all_eq_true.2
        intro b hb
        obtain ⟨cols, hc⟩ := (packPerm_spec B k spo _ bytes hp).2 b hb
        rw [hc]
      · unfold MemGen.rowsOk
        apply List.all_eq_true.2
        intro r hr
        obtain ⟨r0, hr0, rfl⟩ := (hrows k hk r).1 hr
        obtain ⟨i0, i1, i2, _, _, ig⟩ := hrow r0 hr0
        obtain ⟨c0, c1, c2, cg⟩ := toPermRow_cols k r0
        simp only [Bool.and_eq_true]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rcases c0 with e | e | e <;> rw [e] <;> assumption
        · rcases c1 with e | e | e <;> rw [e] <;> assumption
        · rcases c2 with e | e | e <;> rw [e] <;> assumption
        · rw [cg]; exact ig
      · unfold MemGen.permOk
        apply List.isPerm_iff.2
        have hn1 : ((G.rows k).map (Overlay.ofPermRow k)).Nodup := by
          rw [rows_eq B qs decl G F h spo hspo k hk]
          apply List.Pairwise.map _ _ (sortUniq_nodup strict_rowCmp _)
          intro a b hab e; exact hab (ofPermRow_inj k hk a b e)
        have hn2 : (G.rows 2).Nodup := by
          rw [rows_eq B qs decl G F h spo hspo 2 (by omega)]; exact sortUniq_nodup strict_rowCmp _
        apply (List.perm_ext_iff_of_nodup hn1 hn2).2
        intro x
        rw [List.mem_map, hrows 2 (by omega)]
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨r0, hr0, rfl⟩ := (hrows k hk y).1 hy
          exact ⟨r0, hr0, by rw [of_toPermRow k hk, toPermRow_two]⟩
        · rintro ⟨r0, hr0, rfl⟩
          exact ⟨Overlay.toPermRow k r0, (hrows k hk _).2 ⟨r0, hr0, rfl⟩, by rw [of_toPermRow k hk, toPermRow_two]⟩
    simp only [hk 0 (by omega), hk 1 (by omega), hk 2 (by omega), hk 3 (by omega), and_self]
  · unfold MemGen.spoOk
    apply List.all_eq_true.2
    intro r hr
    obtain ⟨r0, hr0, rfl⟩ := (hrows 2 (by omega) r).1 hr
    obtain ⟨_, _, _, s0, p1, _⟩ := hrow r0 hr0
    rw [toPermRow_two]
    simp [s0, p1]
  · unfold MemGen.namedOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hlt : ∀ b ∈ gids, b < 18446744073709551616 := by
      intro b hb; obtain ⟨g, _, e⟩ := hg1 b hb; exact code_lt _ _ _ e
    refine ⟨?_, ?_⟩
    · rw [hnamed]
      simp only [Array.toList_map, List.toList_toArray]
      rw [List.Nodup, List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ (sortUniq_nodup strict_compare gids)
      intro a b ha hb hab e
      apply hab
      have ha' := hlt a ((mem_sortUniq strict_compare gids a).1 ha)
      have hb' := hlt b ((mem_sortUniq strict_compare gids b).1 hb)
      have := congrArg UInt64.toNat e
      rwa [toNat_ofNat_code a ha', toNat_ofNat_code b hb'] at this
    · apply List.all_eq_true.2
      intro x hx
      obtain ⟨b, hb, rfl⟩ := (named_mem B qs decl G F h gids hnamed x).1 hx
      obtain ⟨g, _, e⟩ := hg1 b hb
      rw [toNat_ofNat_code b (hlt b hb)]
      simp [idOkB_of _ _ _ e, subjB_of _ _ _ e]

end check


/-! ## The dataset of the generation is the input -/

/-- A triple with its object's language tags in lower case. -/
def normTriple (tr : Triple) : Triple := ⟨tr.s, tr.p, normalizeTerm tr.o⟩

theorem subjOf_toTerm (s : Subject) : subjOf s.toTerm = s := by cases s <;> rfl

theorem Subject.toTerm_inj (a b : Subject) (h : a.toTerm = b.toTerm) : a = b := by
  cases a <;> cases b <;> simp_all [Subject.toTerm]

section denote
variable (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
  (h : packSpec B qs decl = some (G, F))
include h

theorem dec_code (u : Term) (n : Nat) (hc : toCode? G.keys u = some n) : G.dec n.toUInt64 = u := by
  unfold MemGen.dec
  rw [show n.toUInt64.toNat = n from toNat_ofNat_code n (code_lt _ _ _ hc), ofCode?_toCode? _ _ _ hc]
  rfl

/-- The triple a row of a quad decodes to is the quad's triple, normalised. -/
theorem tripleAt_row (q : Quad) (r0 : Row) (hq : spoRow? G.keys q = some r0) :
    G.tripleAt (ScanTableTheorems.tripleOf 2 r0) = normTriple q.1 := by
  obtain ⟨e0, e1, e2, _⟩ := spoRow_spec G.keys q r0 hq
  show (⟨subjOf (G.dec r0.c0.toUInt64), iriOf (G.dec r0.c1.toUInt64), G.dec r0.c2.toUInt64⟩ : Triple) = _
  rw [dec_code B qs decl G F h _ _ e0, dec_code B qs decl G F h _ _ e1, dec_code B qs decl G F h _ _ e2,
    subjOf_toTerm]
  rfl

/-- The triples of graph id `gid` are the normalised triples of the quads
    whose row has graph id `gid`. -/
theorem mem_graphOf (spo : List Row) (hspo : allSome (spoRow? G.keys) qs = some spo) (gid : Nat)
    (hgid : gid < 18446744073709551616) (tr : Triple) :
    tr ∈ G.graphOf (UInt64.ofNat gid) ↔
      ∃ q ∈ qs, ∃ r0, spoRow? G.keys q = some r0 ∧ r0.g = gid ∧ normTriple q.1 = tr := by
  obtain ⟨hs1, hs2⟩ := allSome_mem _ qs spo hspo
  unfold MemGen.graphOf ScanTableTheorems.permListing
  simp only [List.mem_map, List.mem_filter, beq_iff_eq, toNat_ofNat_code gid hgid]
  constructor
  · rintro ⟨x, ⟨r, ⟨hr, hg⟩, rfl⟩, rfl⟩
    obtain ⟨r0, hr0, rfl⟩ := (mem_rows B qs decl G F h spo hspo 2 (by omega) r).1 hr
    rw [toPermRow_two] at hg ⊢
    obtain ⟨q, hq, hqr⟩ := hs1 r0 hr0
    exact ⟨q, hq, r0, hqr, hg, (tripleAt_row B qs decl G F h q r0 hqr).symm⟩
  · rintro ⟨q, hq, r0, hqr, hg, rfl⟩
    obtain ⟨r1, hr1, e⟩ := hs2 q hq
    rw [hqr] at e
    simp only [Option.some.injEq] at e
    subst e
    refine ⟨_, ⟨r0, ⟨(mem_rows B qs decl G F h spo hspo 2 (by omega) r0).2 ⟨r0, hr1, rfl⟩, hg⟩, rfl⟩, ?_⟩
    exact tripleAt_row B qs decl G F h q r0 hqr

/-- The default graph of `denote G` is the triples of the default-graph
    quads, with language tags in lower case. -/
theorem packSpec_default (tr : Triple) :
    tr ∈ G.denote.default ↔ ∃ q ∈ qs, q.2 = none ∧ normTriple q.1 = tr := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨spo, hspo, _⟩ := hf.spo
  obtain ⟨_, hs2⟩ := allSome_mem _ qs spo hspo
  show tr ∈ G.graphOf (UInt64.ofNat 0) ↔ _
  rw [mem_graphOf B qs decl G F h spo hspo 0 (by decide)]
  constructor
  · rintro ⟨q, hq, r0, hqr, hg, rfl⟩
    refine ⟨q, hq, ?_, rfl⟩
    obtain ⟨_, _, _, e3⟩ := spoRow_spec G.keys q r0 hqr
    rcases e3 with ⟨hn, _⟩ | ⟨g, _, hgc⟩
    · exact hn
    · have := toCode?_pos _ _ _ hgc; omega
  · rintro ⟨q, hq, hn, rfl⟩
    obtain ⟨r0, _, hqr⟩ := hs2 q hq
    obtain ⟨_, _, _, e3⟩ := spoRow_spec G.keys q r0 hqr
    rcases e3 with ⟨_, hg⟩ | ⟨g, hqg, _⟩
    · exact ⟨q, hq, r0, hqr, hg, rfl⟩
    · rw [hn] at hqg; cases hqg

/-- The named graphs of `denote G`: a graph named `g` holds `tr` exactly
    when a quad of graph `g` has the triple `tr`, with language tags in lower
    case. -/
theorem packSpec_named (g : Subject) (tr : Triple) :
    (∃ ng ∈ G.denote.named, ng.name = g ∧ tr ∈ ng.graph) ↔ ∃ q ∈ qs, q.2 = some g ∧ normTriple q.1 = tr := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨spo, hspo, _⟩ := hf.spo
  obtain ⟨gids, hgids, hnamed⟩ := hf.gids
  obtain ⟨_, hs2⟩ := allSome_mem _ qs spo hspo
  obtain ⟨hg1, hg2⟩ := gid_spec B qs decl G F h gids hgids
  unfold MemGen.denote
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hname, htr⟩
    obtain ⟨b, hb, rfl⟩ := (named_mem B qs decl G F h gids hnamed x).1 hx
    obtain ⟨g', _, hgc⟩ := hg1 b hb
    have hb64 := code_lt _ _ _ hgc
    simp only at hname htr
    rw [dec_code B qs decl G F h _ _ hgc, subjOf_toTerm] at hname
    subst hname
    rw [mem_graphOf B qs decl G F h spo hspo b hb64] at htr
    obtain ⟨q, hq, r0, hqr, hg, rfl⟩ := htr
    refine ⟨q, hq, ?_, rfl⟩
    obtain ⟨_, _, _, e3⟩ := spoRow_spec G.keys q r0 hqr
    rcases e3 with ⟨_, hg0⟩ | ⟨g'', hqg, hgc''⟩
    · have := toCode?_pos _ _ _ hgc; omega
    · rw [hqg, Subject.toTerm_inj _ _ (toCode?_injective _ _ _ _ hgc'' (hg ▸ hgc))]
  · rintro ⟨q, hq, hqg, rfl⟩
    have hgm : g ∈ qs.filterMap (·.2) := List.mem_filterMap.2 ⟨q, hq, hqg⟩
    obtain ⟨b, hb, hbc⟩ := hg2 g (Or.inl hgm)
    have hb64 := code_lt _ _ _ hbc
    refine ⟨_, ⟨UInt64.ofNat b, (named_mem B qs decl G F h gids hnamed _).2 ⟨b, hb, rfl⟩, rfl⟩, ?_, ?_⟩
    · simp only
      rw [dec_code B qs decl G F h _ _ hbc, subjOf_toTerm]
    · simp only
      rw [mem_graphOf B qs decl G F h spo hspo b hb64]
      obtain ⟨r0, _, hqr⟩ := hs2 q hq
      obtain ⟨_, _, _, e3⟩ := spoRow_spec G.keys q r0 hqr
      rcases e3 with ⟨hn, _⟩ | ⟨g'', hqg', hgc''⟩
      · rw [hqg] at hn; cases hn
      · rw [hqg] at hqg'
        simp only [Option.some.injEq] at hqg'
        subst hqg'
        rw [hbc] at hgc''
        simp only [Option.some.injEq] at hgc''
        exact ⟨q, hq, r0, hqr, hgc''.symm, rfl⟩

/-- The names of the named graphs of `denote G` are the graph names of the
    quads and the declared graphs. -/
theorem packSpec_names (g : Subject) :
    (∃ ng ∈ G.denote.named, ng.name = g) ↔ g ∈ qs.filterMap (·.2) ∨ g ∈ decl := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨gids, hgids, hnamed⟩ := hf.gids
  obtain ⟨hg1, hg2⟩ := gid_spec B qs decl G F h gids hgids
  unfold MemGen.denote
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hname⟩
    obtain ⟨b, hb, rfl⟩ := (named_mem B qs decl G F h gids hnamed x).1 hx
    obtain ⟨g', hg', hgc⟩ := hg1 b hb
    simp only at hname
    rw [dec_code B qs decl G F h _ _ hgc, subjOf_toTerm] at hname
    subst hname
    exact hg'
  · intro hg
    obtain ⟨b, hb, hbc⟩ := hg2 g hg
    refine ⟨_, ⟨UInt64.ofNat b, (named_mem B qs decl G F h gids hnamed _).2 ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    simp only
    rw [dec_code B qs decl G F h _ _ hbc, subjOf_toTerm]

end denote


open L4Factoidal.SPARQL in
open L4Factoidal.Storage.Sbm11.IdQuery in
open L4Factoidal.Storage.Sbm11.IdGroup (nestedTableM queryEnvOf) in
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (WhereOk) in
open L4Factoidal.Storage.Sbm11.LocalVocab in
/-- The WHERE clause theorem of the harness for the store over the files of
    `packSpec B qs decl`: no hypothesis on the store or the generation
    remains; `packSpec_default`, `packSpec_named` and `packSpec_names` say
    what `denote G` holds. -/
theorem harness_where_allowed_packed (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) (clock : EvalEnv) (base : Option String)
    (plan : Plan) (p : QueryPattern) (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hq : QHyps G.cid p) :
    (∃ e, nestedTableM F.store plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM F.store plan (queryEnvOf clock base) =
          pure (t, F.store.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
          G.denote.default {} t s := by
  obtain ⟨hw, h4⟩ := packSpec_written B qs decl G F h
  exact harness_where_allowed_file G F hw h4 (packSpec_check B qs decl G F h) clock base plan p hnest hdsq hq

end L4Factoidal.Storage.Sbm11.PackSpec

#print axioms L4Factoidal.Storage.Sbm11.PackSpec.packSpec_check
#print axioms L4Factoidal.Storage.Sbm11.PackSpec.packSpec_written
#print axioms L4Factoidal.Storage.Sbm11.PackSpec.packSpec_default
#print axioms L4Factoidal.Storage.Sbm11.PackSpec.packSpec_named
#print axioms L4Factoidal.Storage.Sbm11.PackSpec.packSpec_names
#print axioms L4Factoidal.Storage.Sbm11.PackSpec.harness_where_allowed_packed
