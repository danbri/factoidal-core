/-
L4Factoidal.Storage.Sbm11.PackStream — the byte production of the SBM11
packer as pure step functions over a stream, proved equal to the pure
specification `PackSpec.packSpec`
(https://github.com/danbri/factoidal/issues/776; row L3c of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

The packer (`Harness/Sbm11PackLib.lean`) reads its keys and its rows from
k-way merges of run files, so it never holds a whole key list or row list.
It makes every byte it writes with the functions of this module, one key or
one row at a time, and writes what they return:

* `Pages.push` and `Pages.finish` (phase 2): the keys cut into pages of
  `pageTerms` keys; per page its bytes (`encodePage`) and its GDX1 entry
  (offset in GDV1, length).
* `Cut.push` and `Cut.finish` (phase 3b): the rows of a permutation cut into
  blocks as `PackSpec.cutRows` cuts them; per block its PRM1 entry and its
  four frames (`blockOut`, with `Column.encodeColumnFast`).

Theorems:

* `Pages.run_spec`: the pages and entries of a key stream are
  `chunk pageTerms keys` and `dirEntries` of it, so GDV1 and GDX1 are the
  bytes of `encodeDict? keys` (`Pages.gdv_eq`, `Pages.entries_eq`);
* `blockOut_eq`: `blockOut` is `encodeBlock?` of an admitted block
  (`ColumnFastTheorems.encodeColumnFast_eq`);
* `Cut.run_spec`: the entries and bytes of a row stream are those of
  `PackSpec.encodeBlocks prbHeaderBytes (PackSpec.cutRows B rows)`, so PRB1
  and (through `encodePrm?`) PRM1 are the bytes of `PackSpec.packPerm?`
  (`Cut.packPerm_eq`).

What these do not cover: that the merges deliver the keys of `packSpec`
(sorted, without duplicates) and, per permutation, its rows with the ids of
`toCode?`; and that a file holds the bytes written to it. The packer checks
the order of both streams and the agreement of the four permutations at run
time.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PackSpecTheorems
import L4Factoidal.Storage.Sbm11.ColumnFastTheorems

namespace L4Factoidal.Storage.Sbm11.PackStream

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.Dict (pageTerms encodePage DirEntry chunk chunkGo dirEntries dirEntriesGo
  gdvHeader gdvBytes)

/-! ## Pages (phase 2) -/

/-- The open page of the dictionary writer and the GDV1 offset where it
    starts. -/
structure Pages where
  page : Array Key
  off : Nat

/-- Add a key: a full page is closed, with its bytes and its GDX1 entry. -/
def Pages.push (st : Pages) (k : Key) : Pages × Option (List UInt8 × DirEntry) :=
  let page := st.page.push k
  if page.size ≥ pageTerms then
    let bytes := encodePage page.toList
    (⟨#[], st.off + bytes.length⟩, some (bytes, ⟨st.off, bytes.length⟩))
  else (⟨page, st.off⟩, none)

/-- The last page, when it holds a key. -/
def Pages.finish (st : Pages) : Option (List UInt8 × DirEntry) :=
  if st.page.isEmpty then none
  else
    let bytes := encodePage st.page.toList
    some (bytes, ⟨st.off, bytes.length⟩)

/-- What the writer returns for a key stream, in order. -/
def Pages.run : Pages → List Key → List (List UInt8 × DirEntry)
  | st, [] => st.finish.toList
  | st, k :: ks => (st.push k).2.toList ++ Pages.run (st.push k).1 ks

theorem chunkGo_acc' {α : Type} (n : Nat) : ∀ (f : Nat) (l : List α) (acc : List (List α)),
    chunkGo n f l acc = acc.reverse ++ chunkGo n f l [] :=
  MemGen.chunkGo_acc n

theorem chunkGo_fuel {α : Type} (n : Nat) (hn : 0 < n) : ∀ (f f' : Nat) (l : List α),
    l.length < f → l.length < f' → chunkGo n f l [] = chunkGo n f' l []
  | 0, _, l, h, _ => by omega
  | _, 0, l, _, h => by omega
  | f + 1, f' + 1, [], _, _ => by simp [chunkGo]
  | f + 1, f' + 1, x :: xs, h, h' => by
    simp only [chunkGo]
    rw [chunkGo_acc' n f, chunkGo_acc' n f']
    have hd : ((x :: xs).drop n).length < f := by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega
    have hd' : ((x :: xs).drop n).length < f' := by
      simp only [List.length_drop, List.length_cons] at h' ⊢; omega
    rw [chunkGo_fuel n hn f f' _ hd hd']

theorem chunk_nil {α : Type} (n : Nat) : chunk n ([] : List α) = [] := by
  simp [chunk, chunkGo]

theorem chunk_cons {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (hl : l ≠ []) :
    chunk n l = l.take n :: chunk n (l.drop n) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  unfold chunk
  rw [show chunkGo n ((x :: xs).length + 1) (x :: xs) [] =
      chunkGo n (x :: xs).length ((x :: xs).drop n) [(x :: xs).take n] from rfl, chunkGo_acc' n]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.cons.injEq, true_and]
  apply chunkGo_fuel n hn
  · simp only [List.length_drop, List.length_cons]; omega
  · omega

theorem chunk_single {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (hl : l ≠ []) (hlen : l.length ≤ n) :
    chunk n l = [l] := by
  rw [chunk_cons n hn l hl, List.take_of_length_le hlen, List.drop_of_length_le hlen, chunk_nil]

theorem dirEntriesGo_cons (p : List Key) (ps : List (List Key)) (off : Nat) :
    dirEntriesGo (p :: ps) off [] = ⟨off, (encodePage p).length⟩ :: dirEntriesGo ps (off + (encodePage p).length) [] := by
  have : ∀ (ps : List (List Key)) off (acc : List DirEntry), dirEntriesGo ps off acc = acc.reverse ++ dirEntriesGo ps off [] := by
    intro ps
    induction ps with
    | nil => intro off acc; simp [dirEntriesGo]
    | cons q qs ih =>
      intro off acc
      simp only [dirEntriesGo]
      rw [ih _ (_ :: acc), ih _ [_]]
      simp
  simp only [dirEntriesGo]
  rw [this]
  simp

theorem pageTerms_pos : 0 < pageTerms := by decide

/-- The pages and entries of a key stream: the cut of the open page and the
    stream into pages of `pageTerms` keys, and their directory from `off`. -/
theorem Pages.run_spec : ∀ (ks : List Key) (page : Array Key) (off : Nat), page.size < pageTerms →
    (Pages.run ⟨page, off⟩ ks).map Prod.fst = (chunk pageTerms (page.toList ++ ks)).map encodePage ∧
      (Pages.run ⟨page, off⟩ ks).map Prod.snd = dirEntriesGo (chunk pageTerms (page.toList ++ ks)) off []
  | [], page, off, hs => by
    simp only [Pages.run, Pages.finish, List.append_nil]
    by_cases he : page.isEmpty = true
    · have : page.toList = [] := by simpa using he
      simp [he, this, chunk_nil, dirEntriesGo]
    · have hne : page.toList ≠ [] := by simpa using he
      rw [if_neg he, chunk_single pageTerms pageTerms_pos _ hne (by simp; omega)]
      simp [dirEntriesGo]
  | k :: ks, page, off, hs => by
    simp only [Pages.run, Pages.push]
    by_cases hf : (page.push k).size ≥ pageTerms
    · rw [if_pos hf]
      have hsz : (page.push k).size = pageTerms := by simp at hf ⊢; omega
      obtain ⟨ih1, ih2⟩ := Pages.run_spec ks #[] (off + (encodePage (page.push k).toList).length) (by decide)
      have hl : page.toList ++ k :: ks = (page.push k).toList ++ ks := by simp
      have hlen : (page.push k).toList.length = pageTerms := by simpa using hsz
      have hc : chunk pageTerms (page.toList ++ k :: ks) = (page.push k).toList :: chunk pageTerms ks := by
        rw [hl, chunk_cons pageTerms pageTerms_pos _ (by simp), List.take_left' hlen, List.drop_left' hlen]
      simp only [Option.toList_some, List.cons_append, List.nil_append, List.map_cons, hc, ih1, ih2,
        dirEntriesGo_cons]
      exact ⟨by first | trivial | rfl, by first | trivial | rfl⟩
    · rw [if_neg hf]
      have hs' : (page.push k).size < pageTerms := by omega
      obtain ⟨ih1, ih2⟩ := Pages.run_spec ks (page.push k) off hs'
      have hl : (page.push k).toList ++ ks = page.toList ++ k :: ks := by simp
      rw [hl] at ih1 ih2
      simp only [Option.toList_none, List.nil_append]
      exact ⟨ih1, ih2⟩

/-- GDV1 of the dictionary writer over `keys`: the header and the page bytes
    in order are `gdvBytes` of the 64-key cut of `keys`. -/
theorem Pages.gdv_eq (keys : List Key) :
    gdvHeader ++ ((Pages.run ⟨#[], gdvHeader.length⟩ keys).map Prod.fst).flatten =
      gdvBytes (chunk pageTerms keys) := by
  rw [(Pages.run_spec keys #[] _ pageTerms_pos).1]
  simp [gdvBytes]

/-- The GDX1 entries of the dictionary writer over `keys` are the directory
    of its pages. -/
theorem Pages.entries_eq (keys : List Key) :
    (Pages.run ⟨#[], gdvHeader.length⟩ keys).map Prod.snd = dirEntries (chunk pageTerms keys) := by
  rw [(Pages.run_spec keys #[] _ pageTerms_pos).2]
  simp [dirEntries]

/-! ## Blocks (phase 3b) -/

/-- The PRM1 entry and the four frames of the block `rows` at PRB1 offset
    `off`, as the packer writes them. -/
def blockOut (off : Nat) (rows : Array Row) : BlockMeta × ByteArray :=
  let f0 := encodeColumnFast (rows.map Row.c0)
  let f1 := encodeColumnFast (rows.map Row.c1)
  let f2 := encodeColumnFast (rows.map Row.c2)
  let f3 := encodeColumnFast (rows.map Row.g)
  ({ first := rows[0]!, last := rows[rows.size - 1]!, rows := rows.size, offset := off,
     len0 := f0.size, len1 := f1.size, len2 := f2.size, len3 := f3.size }, f0 ++ f1 ++ f2 ++ f3)

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]; rfl

theorem frame_size (rows : Array Row) (f : Row → Nat) :
    (encodeColumnFast (rows.map f)).size = (frameBytes (rows.toList.map f)).length := by
  rw [size_eq_length, encodeColumnFast_eq, Array.toList_map]

theorem frame_data (rows : Array Row) (f : Row → Nat) :
    (encodeColumnFast (rows.map f)).data.toList = frameBytes (rows.toList.map f) := by
  rw [encodeColumnFast_eq, Array.toList_map]

/-- `blockOut` is `encodeBlock?` of an admitted block. -/
theorem blockOut_eq (off : Nat) (rows : Array Row) (h : blockAdmitted rows.toList = true) :
    encodeBlock? off rows.toList = some ((blockOut off rows).1, (blockOut off rows).2.data.toList) := by
  have hne : rows.toList ≠ [] := by
    unfold blockAdmitted at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    exact h.1.1.1.1.1.1.1
  obtain ⟨l⟩ := rows
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil (by simpa using hne)
  unfold encodeBlock?
  rw [if_pos h]
  simp only [blockOut, frame_size, frame_data, ByteArray.data_append, Array.toList_append, blockBytes,
    List.append_assoc, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_cons, Nat.add_sub_cancel]
  simp

/-- The open block of the block writer and the PRB1 offset where it starts. -/
structure Cut where
  off : Nat
  cur : Array Row

/-- Add a row: the open block is closed when it holds `B` rows, or `max 1
    (B / 16)` rows and the new row has another first column
    (`PackSpec.cutGo`). -/
def Cut.push (B : Nat) (st : Cut) (x : Row) : Cut × Option (BlockMeta × ByteArray) :=
  if decide (st.cur.size ≥ B) || (decide (st.cur.size ≥ max 1 (B / 16)) && st.cur.back!.c0 != x.c0) then
    if st.cur.isEmpty then (⟨st.off, #[x]⟩, none)
    else
      let o := blockOut st.off st.cur
      (⟨st.off + o.2.size, #[x]⟩, some o)
  else (⟨st.off, st.cur.push x⟩, none)

/-- The last block, when it holds a row. -/
def Cut.finish (st : Cut) : Option (BlockMeta × ByteArray) :=
  if st.cur.isEmpty then none else some (blockOut st.off st.cur)

/-- What the writer returns for a row stream, in order. -/
def Cut.run (B : Nat) : Cut → List Row → List (BlockMeta × ByteArray)
  | st, [] => st.finish.toList
  | st, x :: xs => (st.push B x).2.toList ++ Cut.run B (st.push B x).1 xs

theorem back_of_reverse (cur : Array Row) (y : Row) (ys : List Row) (h : cur.toList.reverse = y :: ys) :
    cur.back! = y ∧ cur.size = ys.length + 1 := by
  have hc : cur = (ys.reverse ++ [y]).toArray := by
    apply Array.ext'
    rw [← List.reverse_reverse cur.toList, h]
    simp
  subst hc
  simp [Array.back!]

theorem encodeBlocks_cons (off : Nat) (rs : List Row) (rss : List (List Row)) (ms : List BlockMeta)
    (bs : List UInt8) (h : PackSpec.encodeBlocks off (rs :: rss) = some (ms, bs)) :
    ∃ m b ms' bs', encodeBlock? off rs = some (m, b) ∧
      PackSpec.encodeBlocks (off + b.length) rss = some (ms', bs') ∧ ms = m :: ms' ∧ bs = b ++ bs' := by
  simp only [PackSpec.encodeBlocks, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨m, b⟩, h1, ⟨ms', bs'⟩, h2, he⟩ := h
  simp only [Prod.mk.injEq] at he
  exact ⟨m, b, ms', bs', h1, h2, he.1.symm, he.2.symm⟩

theorem admitted_of_encode (off : Nat) (rs : List Row) (m : BlockMeta) (b : List UInt8)
    (h : encodeBlock? off rs = some (m, b)) : blockAdmitted rs = true := by
  unfold encodeBlock? at h
  split at h
  · assumption
  · cases h

/-- The entries and bytes of the block writer over a row stream are those of
    `PackSpec.encodeBlocks` over the cut of the open block and the stream. -/
theorem Cut.run_spec (B : Nat) : ∀ (xs : List Row) (off : Nat) (cur : Array Row) (ms : List BlockMeta)
    (bs : List UInt8),
    PackSpec.encodeBlocks off (PackSpec.cutGo B (max 1 (B / 16)) xs cur.toList.reverse) = some (ms, bs) →
    (Cut.run B ⟨off, cur⟩ xs).map Prod.fst = ms ∧
      ((Cut.run B ⟨off, cur⟩ xs).map fun o => o.2.data.toList).flatten = bs
  | [], off, cur, ms, bs, h => by
    simp only [Cut.run, Cut.finish]
    by_cases he : cur.isEmpty = true
    · have : cur.toList = [] := by simpa using he
      rw [this] at h
      simp only [List.reverse_nil, PackSpec.cutGo, PackSpec.encodeBlocks, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [he]
    · rw [if_neg he]
      have hne : cur.toList.reverse ≠ [] := by simpa using he
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
      rw [hy] at h
      simp only [PackSpec.cutGo] at h
      rw [← hy, List.reverse_reverse] at h
      obtain ⟨m, b, ms', bs', h1, h2, rfl, rfl⟩ := encodeBlocks_cons _ _ _ _ _ h
      simp only [PackSpec.encodeBlocks, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [blockOut_eq off cur (admitted_of_encode _ _ _ _ h1)] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp
  | x :: xs, off, cur, ms, bs, h => by
    by_cases he : cur.isEmpty = true
    · have hc : cur.toList = [] := by simpa using he
      have hcur : cur = #[] := by simpa using he
      rw [hc] at h
      simp only [List.reverse_nil, PackSpec.cutGo] at h
      have hp : Cut.push B ⟨off, cur⟩ x = (⟨off, #[x]⟩, none) := by
        subst hcur
        unfold Cut.push
        split <;> simp
      have ih := Cut.run_spec B xs off #[x] ms bs (by simpa using h)
      simp only [Cut.run, hp, Option.toList_none, List.nil_append]
      exact ih
    · have hne : cur.toList.reverse ≠ [] := by simpa using he
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨hback, hsize⟩ := back_of_reverse cur y ys hy
      rw [hy] at h
      unfold PackSpec.cutGo at h
      have hcond : (decide (cur.size ≥ B) || (decide (cur.size ≥ max 1 (B / 16)) && cur.back!.c0 != x.c0)) =
          (decide ((y :: ys).length ≥ B) || (decide ((y :: ys).length ≥ max 1 (B / 16)) && y.c0 != x.c0)) := by
        rw [hback, hsize]; rfl
      by_cases hk : (decide ((y :: ys).length ≥ B) || (decide ((y :: ys).length ≥ max 1 (B / 16)) && y.c0 != x.c0)) = true
      · rw [if_pos hk, ← hy, List.reverse_reverse] at h
        obtain ⟨m, b, ms', bs', h1, h2, rfl, rfl⟩ := encodeBlocks_cons _ _ _ _ _ h
        rw [blockOut_eq off cur (admitted_of_encode _ _ _ _ h1)] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨hm, hb⟩ := h1
        have hp : Cut.push B ⟨off, cur⟩ x = (⟨off + (blockOut off cur).2.size, #[x]⟩, some (blockOut off cur)) := by
          unfold Cut.push
          simp only
          rw [hcond, if_pos hk, if_neg he]
        have hsz : (blockOut off cur).2.size = b.length := by rw [size_eq_length, hb]
        have ih := Cut.run_spec B xs (off + (blockOut off cur).2.size) #[x] ms' bs' (by rw [hsz]; simpa using h2)
        simp only [Cut.run, hp, Option.toList_some, List.cons_append, List.nil_append, List.map_cons,
          List.flatten_cons]
        rw [ih.1, ih.2, hm, hb]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hk] at h
        have hp : Cut.push B ⟨off, cur⟩ x = (⟨off, cur.push x⟩, none) := by
          unfold Cut.push
          simp only
          rw [hcond, if_neg hk]
        have hl : (cur.push x).toList.reverse = x :: y :: ys := by simp [hy]
        have ih := Cut.run_spec B xs off (cur.push x) ms bs (by rw [hl]; exact h)
        simp only [Cut.run, hp, Option.toList_none, List.nil_append]
        exact ih

/-- PRB1 and PRM1 of the block writer over the rows of permutation `k`: the
    header and the block bytes in order are the PRB1 bytes of
    `PackSpec.packPerm?`, and the entries its PRM1 list. -/
theorem Cut.packPerm_eq (B k : Nat) (spo : List Row) (ms : List BlockMeta) (bytes : List UInt8)
    (h : PackSpec.packPerm? B k spo = some (ms, bytes)) :
    let rows := PackSpec.sortUniq PackSpec.rowCmp (spo.map (Overlay.toPermRow k))
    (Cut.run B ⟨prbHeaderBytes, #[]⟩ rows).map Prod.fst = ms ∧
      prbHeader k ++ ((Cut.run B ⟨prbHeaderBytes, #[]⟩ rows).map fun o => o.2.data.toList).flatten = bytes := by
  intro rows
  simp only [PackSpec.packPerm?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨ms', bs⟩, h1, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := Cut.run_spec B rows prbHeaderBytes #[] _ bs (by simpa [PackSpec.cutRows] using h1)
  exact ⟨this.1, by rw [this.2]⟩

end L4Factoidal.Storage.Sbm11.PackStream
