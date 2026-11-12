/-
L4Factoidal.LWS.PodSearch — text search over a pod: what a search may return,
what it must return, and how the index stays correct as the pod changes.

The foafos shell keeps an inverted index of a pod's textual resources and
answers `pod.search(query)` (`packages/foafos/src/search.mjs`, class
`TextIndex`). This module is a specification of that index. It states the
data, the three operations (`put`, `remove`, `search`) and the theorems that
the definitions here satisfy. That the JavaScript refines these definitions
is not proved here; it is a matter for a differential test.

## The model

* A **document** is a path and its list of words (`Doc`). The pod's textual
  contents are a list of documents with distinct paths (`Pod`). A write
  replaces the document at a path; a delete removes it (`Pod.write`,
  `Pod.delete`).
* **Words.** How text becomes words (`words` in the shell: letters and digits
  in any script, lower case, accents folded) is *not* modelled. The model
  starts from the word lists. Every theorem holds for any tokeniser, provided
  the same tokeniser is used for documents and for queries. Whether a given
  tokeniser finds what a person expects ("café" against "cafe", Chinese text
  without spaces, hyphenated words) is a property of the tokeniser and is not
  proved.
* The **index** (`Index`) holds the documents (`docs`, the shell's `docs` map)
  and the inverted index (`terms`, from a word to the paths that contain it,
  the shell's `terms` map). `remove` drops a path from the posting lists of
  the words of its old text only, as the shell does; `put` first removes,
  then adds the path to the posting list of each of its words.
* **Search** (`search idx keep q limit`): if the query has no words, nothing.
  Otherwise the indexed paths that are in the posting list of every query
  word *and* pass `keep` (the asker's read scope), ranked best first (more
  occurrences of the query words, then path order), then cut to `limit`.
  `keep` is applied before ranking and before the limit.

## What is proved

Only readable: `search_keep` (every result passes `keep`),
`search_in_scope` (with `keep` = "path starts with the app's prefix", no
result lies outside the app's folder).

Sound: `search_sound` (every result is an indexed path whose document
contains every query word; stated against the pod contents for a fresh
index).

Complete: `ranked_complete` (with a fresh index, every readable document that
contains every query word is in the unlimited result),
`search_limit_prefix` (the limited result is the first `limit` entries of the
unlimited one), `search_limit_full` (filter before limit: if a readable,
matching document is cut by the limit, the result is full, with exactly
`limit` entries, all readable and matching, and all ranked before it; a
refused document never takes its place).

Empty query: `search_nil`.

No duplicates: `search_nodup`.

Freshness: `fresh_empty`, `fresh_remove`, `fresh_put`, `fresh_ops` (applying
`put` for each write and `remove` for each delete keeps the index fresh for
the pod), `fresh_build` (an index built from the contents is fresh),
`search_fresh_eq` (two indexes fresh for the same contents give the same
search result, list for list, for every query, scope and limit),
`search_ops_eq_build` (the index maintained by `put`/`remove` answers every
search exactly as an index built afresh from the resulting contents).

## What is not proved, and the assumptions

* **Tokenisation** is out of scope (see above).
* **The size budget.** The shell refuses a `put` that would take the indexed
  text over `MAX_INDEXED_BYTES` (32 MiB) and returns false; because it removes
  the old entry first, that path is then absent from the index. This model
  has no budget: every `put` succeeds. Under the budget, the shell's index is
  fresh for the pod *minus* the refused paths, so completeness fails for
  them; the caller sees `false` and must report it.
* **The caller keeps the index fresh.** Freshness is proved for an index
  that receives a `put` for every write and a `remove` for every delete, in
  the same order as the pod applies them. A write that does not reach the
  index (a crash between the two, a write by another process to the same
  storage) makes the index stale; no theorem here covers that case.
* **The read predicate is given.** `keep` is a parameter. That it matches the
  pod's access control (WAC/ACP, app scopes) is the caller's duty
  (`FoafPods.invoke` in the shell). The theorems prove that search applies
  `keep` correctly, not that `keep` is the right policy.
* **Relative paths.** The shell's `pod.search` returns paths relative to the
  app's scope prefix; this model returns the full path. Stripping a known
  prefix is not modelled.
* **What a result reveals.** A result contains the path, a score and a
  snippet of the text. Snippets are not modelled. The theorems say which
  paths come back; they do not bound what else a reader learns, for example
  from response time or from the number of results.
* **Ranking order.** The rank order is stated (score, then path) and used,
  but no theorem says that the order is a good one for people. The shell
  enumerates the shortest posting list; this model enumerates the documents
  in store order. The set of results is the same; the order after the sort
  is the same when no two results have the same path, which holds because
  paths are distinct.
* **Query words are not de-duplicated** in the score here; the shell
  de-duplicates them first. Pass a query without repeats to match the shell.
* **Snippets, counts and Unicode normalisation** are not modelled.

No `sorry`, no `axiom`, no `partial`. Lean core only (no Mathlib).
-/

namespace L4Factoidal.LWS.PodSearch

/-! ## Documents and the pod -/

/-- One textual resource after tokenisation: its path and its words, in
order, with repeats. -/
abbrev Doc := String × List String

/-- A pod's textual contents. The invariant that each path occurs once is
carried by `Fresh` below. -/
abbrev Pod := List Doc

/-- A write to the pod: the document at `p` is replaced (or created). -/
def Pod.write (p : String) (ws : List String) (c : Pod) : Pod :=
  (p, ws) :: c.filter (fun d => d.1 != p)

/-- A delete from the pod: the document at `p`, if any, is removed. -/
def Pod.delete (p : String) (c : Pod) : Pod :=
  c.filter (fun d => d.1 != p)

/-- The words of the document at path `p`, if there is one. -/
def findDoc (p : String) : List Doc → Option (List String)
  | [] => none
  | (q, ws) :: rest => if q = p then some ws else findDoc p rest

theorem findDoc_some {p : String} {ws : List String} :
    ∀ {l : List Doc}, findDoc p l = some ws → (p, ws) ∈ l
  | [], h => by simp [findDoc] at h
  | (q, vs) :: rest, h => by
      unfold findDoc at h
      split at h
      · rename_i hq; subst hq; cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (findDoc_some h)

theorem findDoc_none {p : String} :
    ∀ {l : List Doc}, findDoc p l = none → ∀ ws, (p, ws) ∉ l
  | [], _, _ => by simp
  | (q, vs) :: rest, h, ws => by
      unfold findDoc at h
      split at h
      · cases h
      · rename_i hq
        intro hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he; exact hq rfl
        · exact findDoc_none h ws hm

/-- In a pod whose paths are distinct, a path has one document. -/
theorem doc_unique {p : String} {ws₁ ws₂ : List String} :
    ∀ {l : List Doc}, (l.map (·.1)).Nodup → (p, ws₁) ∈ l → (p, ws₂) ∈ l → ws₁ = ws₂
  | [], _, h, _ => by simp at h
  | (q, vs) :: rest, hn, h₁, h₂ => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h₁ with e₁ | m₁ <;> rcases List.mem_cons.mp h₂ with e₂ | m₂
      · cases e₁; cases e₂; rfl
      · cases e₁; exact absurd (List.mem_map.mpr ⟨_, m₂, rfl⟩) hn.1
      · cases e₂; exact absurd (List.mem_map.mpr ⟨_, m₁, rfl⟩) hn.1
      · exact doc_unique hn.2 m₁ m₂

/-! ## The index -/

/-- The search index: the documents, and the inverted index from a word to
the paths whose document contains it (the posting list). -/
structure Index where
  docs : List Doc
  terms : String → List String

/-- The index of an empty pod. -/
def Index.empty : Index := ⟨[], fun _ => []⟩

/-- Drop path `p` from the index. As in the shell, only the posting lists of
the words of `p`'s old document are touched. -/
def Index.remove (p : String) (i : Index) : Index :=
  match findDoc p i.docs with
  | none => i
  | some old =>
    { docs := i.docs.filter (fun d => d.1 != p),
      terms := fun t => if t ∈ old then (i.terms t).filter (· != p) else i.terms t }

/-- Index (or re-index) the document at `p` with words `ws`: remove the old
entry, then add `p` to the posting list of each of its words. -/
def Index.put (p : String) (ws : List String) (i : Index) : Index :=
  let j := i.remove p
  { docs := (p, ws) :: j.docs,
    terms := fun t => if t ∈ ws then p :: j.terms t else j.terms t }

/-- The index is fresh for pod contents `c`: it holds exactly those documents,
their paths are distinct, and each posting list holds exactly the paths whose
document contains the word. -/
structure Fresh (i : Index) (c : Pod) : Prop where
  docs_eq : i.docs = c
  paths_nodup : (c.map (·.1)).Nodup
  postings : ∀ t p, p ∈ i.terms t ↔ ∃ ws, (p, ws) ∈ c ∧ t ∈ ws

/-! ## Search -/

/-- How often the query words occur in the document at `p` (0 if there is
none). -/
def score (i : Index) (q : List String) (p : String) : Nat :=
  match findDoc p i.docs with
  | none => 0
  | some ws => q.foldl (fun n t => n + ws.count t) 0

/-- Rank order: higher score first, then path order. -/
def before (i : Index) (q : List String) (a b : String) : Bool :=
  let sa := score i q a
  let sb := score i q b
  decide (sa > sb) || (sa == sb && decide (a ≤ b))

/-- Does path `p` match: it is in the posting list of every query word, and
the asker may read it. -/
def hit (i : Index) (keep : String → Bool) (q : List String) (p : String) : Bool :=
  q.all (fun t => decide (p ∈ i.terms t)) && keep p

/-- The unlimited result: no words, nothing; otherwise every matching,
readable path, best first. `keep` is applied here, before the limit. -/
def ranked (i : Index) (keep : String → Bool) (q : List String) : List String :=
  if q = [] then []
  else ((i.docs.map (·.1)).filter (hit i keep q)).mergeSort (before i q)

/-- `search`: the unlimited result cut to `limit` entries. -/
def search (i : Index) (keep : String → Bool) (q : List String) (limit : Nat) :
    List String :=
  (ranked i keep q).take limit

theorem mem_ranked {i : Index} {keep : String → Bool} {q : List String} {p : String} :
    p ∈ ranked i keep q ↔ q ≠ [] ∧ p ∈ i.docs.map (·.1) ∧ hit i keep q p = true := by
  unfold ranked
  split
  · simp_all
  · rename_i hq
    rw [List.mem_mergeSort, List.mem_filter]
    simp [hq]

/-! ### Only readable -/

/-- Every result of a search is readable by the asker: it passes `keep`. -/
theorem search_keep {i : Index} {keep : String → Bool} {q : List String} {n : Nat}
    {p : String} (h : p ∈ search i keep q n) : keep p = true := by
  have h' := mem_ranked.mp (List.mem_of_mem_take h)
  simp [hit] at h'
  exact h'.2.2.2

/-- An app scoped to the folder `pre` never sees a result outside that
folder: with `keep` = "path starts with `pre`", every result starts with
`pre`. -/
theorem search_in_scope {i : Index} {pre : String} {q : List String} {n : Nat}
    {p : String} (h : p ∈ search i (fun x => x.startsWith pre) q n) :
    p.startsWith pre = true :=
  search_keep h

/-! ### Empty query -/

/-- A query with no words finds nothing. -/
theorem search_nil (i : Index) (keep : String → Bool) (n : Nat) :
    search i keep [] n = [] := by
  simp [search, ranked]

/-! ### Sound -/

/-- Every result is an indexed path that is in the posting list of every
query word (stated on the index alone, with no freshness assumption). -/
theorem search_sound_index {i : Index} {keep : String → Bool} {q : List String}
    {n : Nat} {p : String} (h : p ∈ search i keep q n) :
    p ∈ i.docs.map (·.1) ∧ ∀ t ∈ q, p ∈ i.terms t := by
  have h' := mem_ranked.mp (List.mem_of_mem_take h)
  refine ⟨h'.2.1, fun t ht => ?_⟩
  have := h'.2.2
  simp [hit, List.all_eq_true] at this
  exact this.1 t ht

/-- For a fresh index: every result is a document of the pod that contains
every query word, and the asker may read it. -/
theorem search_sound {i : Index} {c : Pod} (hf : Fresh i c) {keep : String → Bool}
    {q : List String} {n : Nat} {p : String} (h : p ∈ search i keep q n) :
    keep p = true ∧ ∃ ws, (p, ws) ∈ c ∧ ∀ t ∈ q, t ∈ ws := by
  refine ⟨search_keep h, ?_⟩
  obtain ⟨hd, ht⟩ := search_sound_index h
  rw [hf.docs_eq] at hd
  obtain ⟨⟨p', ws⟩, hm, rfl⟩ := List.mem_map.mp hd
  refine ⟨ws, hm, fun t tq => ?_⟩
  obtain ⟨ws', hm', hw'⟩ := (hf.postings t p').mp (ht t tq)
  rw [doc_unique hf.paths_nodup hm hm']
  exact hw'

/-! ### Complete, and filter before limit -/

/-- For a fresh index and a query with words: every document the asker may
read that contains every query word is in the unlimited result. -/
theorem ranked_complete {i : Index} {c : Pod} (hf : Fresh i c) {keep : String → Bool}
    {q : List String} (hq : q ≠ []) {p : String} {ws : List String}
    (hm : (p, ws) ∈ c) (hk : keep p = true) (hw : ∀ t ∈ q, t ∈ ws) :
    p ∈ ranked i keep q := by
  refine mem_ranked.mpr ⟨hq, ?_, ?_⟩
  · rw [hf.docs_eq]; exact List.mem_map.mpr ⟨_, hm, rfl⟩
  · simp only [hit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun t tq => (hf.postings t p).mpr ⟨ws, hm, hw t tq⟩, hk⟩

/-- The limited result is the first `limit` entries of the unlimited one. -/
theorem search_limit_prefix (i : Index) (keep : String → Bool) (q : List String)
    (n : Nat) : ∃ rest, ranked i keep q = search i keep q n ++ rest :=
  ⟨_, (List.take_append_drop n _).symm⟩

/-- Filter before limit. If a document in the unlimited result is not in the
limited one, the limited result is full (`limit` entries), every entry in it
is readable and matches, and the document comes after all of them in rank
order. So a refused document never displaces a readable one. -/
theorem search_limit_full {i : Index} {keep : String → Bool} {q : List String}
    {n : Nat} {p : String} (hr : p ∈ ranked i keep q) (hs : p ∉ search i keep q n) :
    (search i keep q n).length = n ∧
    (∀ x ∈ search i keep q n, keep x = true ∧ hit i keep q x = true) ∧
    ∃ rest, ranked i keep q = search i keep q n ++ rest ∧ p ∈ rest := by
  refine ⟨?_, fun x hx => ⟨search_keep hx, (mem_ranked.mp (List.mem_of_mem_take hx)).2.2⟩,
    _, (List.take_append_drop n _).symm, ?_⟩
  · unfold search
    rw [List.length_take]
    apply Nat.min_eq_left
    apply Nat.le_of_not_lt
    intro hlt
    apply hs
    unfold search
    rw [List.take_of_length_le (Nat.le_of_lt hlt)]
    exact hr
  · have := List.take_append_drop n (ranked i keep q)
    rw [← this] at hr
    rcases List.mem_append.mp hr with h | h
    · exact absurd h hs
    · exact h

/-- Completeness up to the limit: for a fresh index, a readable document that
contains every query word is either in the result, or the result already
holds `limit` readable, matching documents ranked before it. -/
theorem search_complete {i : Index} {c : Pod} (hf : Fresh i c) {keep : String → Bool}
    {q : List String} (hq : q ≠ []) {n : Nat} {p : String} {ws : List String}
    (hm : (p, ws) ∈ c) (hk : keep p = true) (hw : ∀ t ∈ q, t ∈ ws) :
    p ∈ search i keep q n ∨
      ((search i keep q n).length = n ∧
        ∃ rest, ranked i keep q = search i keep q n ++ rest ∧ p ∈ rest) := by
  by_cases hs : p ∈ search i keep q n
  · exact Or.inl hs
  · obtain ⟨h1, -, h3⟩ := search_limit_full (ranked_complete hf hq hm hk hw) hs
    exact Or.inr ⟨h1, h3⟩

/-! ### No duplicates -/

theorem nodup_filter {α : Type} {f : α → Bool} {l : List α} (h : l.Nodup) :
    (l.filter f).Nodup :=
  h.sublist List.filter_sublist

/-- For a fresh index, no path occurs twice in a result. -/
theorem search_nodup {i : Index} {c : Pod} (hf : Fresh i c) (keep : String → Bool)
    (q : List String) (n : Nat) : (search i keep q n).Nodup := by
  unfold search
  apply List.Nodup.sublist (List.take_sublist _ _)
  unfold ranked
  split
  · exact List.nodup_nil
  · rw [(List.mergeSort_perm _ _).nodup_iff, hf.docs_eq]
    exact nodup_filter hf.paths_nodup

/-! ## Freshness -/

/-- The empty index is fresh for the empty pod. -/
theorem fresh_empty : Fresh Index.empty [] :=
  ⟨rfl, List.nodup_nil, fun _ _ => by simp [Index.empty]⟩

theorem map_fst_filter_nodup {c : Pod} {p : String} (h : (c.map (·.1)).Nodup) :
    ((c.filter (fun d => d.1 != p)).map (·.1)).Nodup :=
  h.sublist (List.filter_sublist.map _)

theorem filter_ne_self {c : Pod} {p : String} (h : ∀ ws, (p, ws) ∉ c) :
    c.filter (fun d => d.1 != p) = c := by
  apply List.filter_eq_self.mpr
  intro ⟨q, ws⟩ hm
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h ws hm

/-- Removing `p` from a fresh index gives an index fresh for the pod after
the delete of `p`. -/
theorem fresh_remove {i : Index} {c : Pod} (hf : Fresh i c) (p : String) :
    Fresh (i.remove p) (c.delete p) := by
  unfold Index.remove Pod.delete
  split
  · rename_i hn
    rw [hf.docs_eq] at hn
    rw [filter_ne_self (findDoc_none hn)]
    exact hf
  · rename_i old hs
    have hold : (p, old) ∈ c := by rw [← hf.docs_eq]; exact findDoc_some hs
    refine ⟨by simp [hf.docs_eq], map_fst_filter_nodup hf.paths_nodup, fun t x => ?_⟩
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    split
    · rename_i ht
      simp only [List.mem_filter, bne_iff_ne, ne_eq, hf.postings]
      constructor
      · rintro ⟨⟨ws, hm, hw⟩, hx⟩
        exact ⟨ws, ⟨hm, hx⟩, hw⟩
      · rintro ⟨ws, ⟨hm, hx⟩, hw⟩
        exact ⟨⟨ws, hm, hw⟩, hx⟩
    · rename_i ht
      rw [hf.postings]
      constructor
      · rintro ⟨ws, hm, hw⟩
        refine ⟨ws, ⟨hm, ?_⟩, hw⟩
        rintro rfl
        exact ht (doc_unique hf.paths_nodup hm hold ▸ hw)
      · rintro ⟨ws, ⟨hm, -⟩, hw⟩
        exact ⟨ws, hm, hw⟩

/-- Putting `(p, ws)` into a fresh index gives an index fresh for the pod
after the write of `(p, ws)`. -/
theorem fresh_put {i : Index} {c : Pod} (hf : Fresh i c) (p : String)
    (ws : List String) : Fresh (i.put p ws) (c.write p ws) := by
  have hr := fresh_remove hf p
  unfold Pod.delete at hr
  refine ⟨?_, ?_, fun t x => ?_⟩
  · simp [Index.put, Pod.write, hr.docs_eq]
  · simp only [Pod.write, List.map_cons, List.nodup_cons]
    refine ⟨?_, hr.paths_nodup⟩
    simp
  · simp only [Index.put, Pod.write, List.mem_cons]
    split
    · rename_i ht
      rw [List.mem_cons, hr.postings]
      constructor
      · rintro (rfl | ⟨vs, hm, hv⟩)
        · exact ⟨ws, Or.inl rfl, ht⟩
        · exact ⟨vs, Or.inr hm, hv⟩
      · rintro ⟨vs, (he | hm), hv⟩
        · cases he; exact Or.inl rfl
        · exact Or.inr ⟨vs, hm, hv⟩
    · rename_i ht
      rw [hr.postings]
      constructor
      · rintro ⟨vs, hm, hv⟩
        exact ⟨vs, Or.inr hm, hv⟩
      · rintro ⟨vs, (he | hm), hv⟩
        · cases he; exact absurd hv ht
        · exact ⟨vs, hm, hv⟩

/-- One change to the pod: a write of a document, or a delete. -/
inductive Op where
  | write (p : String) (ws : List String)
  | delete (p : String)
deriving Repr

/-- What the shell does to the index for one change. -/
def Op.toIndex : Op → Index → Index
  | .write p ws, i => i.put p ws
  | .delete p, i => i.remove p

/-- What the change does to the pod. -/
def Op.toPod : Op → Pod → Pod
  | .write p ws, c => c.write p ws
  | .delete p, c => c.delete p

/-- Apply a sequence of changes, first to last. -/
def applyIndex (ops : List Op) (i : Index) : Index := ops.foldl (fun j o => o.toIndex j) i
def applyPod (ops : List Op) (c : Pod) : Pod := ops.foldl (fun d o => o.toPod d) c

/-- A `put` for every write and a `remove` for every delete, in order, keep a
fresh index fresh. -/
theorem fresh_ops : ∀ (ops : List Op) {i : Index} {c : Pod}, Fresh i c →
    Fresh (applyIndex ops i) (applyPod ops c)
  | [], _, _, hf => hf
  | .write p ws :: ops, _, _, hf => fresh_ops ops (fresh_put hf p ws)
  | .delete p :: ops, _, _, hf => fresh_ops ops (fresh_remove hf p)

/-- An index built afresh from the pod's contents: one `put` per document. -/
def build (c : Pod) : Index := c.foldr (fun d i => i.put d.1 d.2) Index.empty

/-- An index built from contents with distinct paths is fresh for them. -/
theorem fresh_build : ∀ {c : Pod}, (c.map (·.1)).Nodup → Fresh (build c) c
  | [], _ => fresh_empty
  | (p, ws) :: rest, hn => by
      rw [List.map_cons, List.nodup_cons] at hn
      have h := fresh_put (fresh_build hn.2) p ws
      have he : Pod.write p ws rest = (p, ws) :: rest := by
        unfold Pod.write
        rw [filter_ne_self]
        intro vs hm
        exact hn.1 (List.mem_map.mpr ⟨_, hm, rfl⟩)
      rw [he] at h
      exact h

/-- Two indexes fresh for the same contents answer every search the same way:
the same paths, in the same order, for every query, read scope and limit. -/
theorem search_fresh_eq {i j : Index} {c : Pod} (hi : Fresh i c) (hj : Fresh j c)
    (keep : String → Bool) (q : List String) (n : Nat) :
    search i keep q n = search j keep q n := by
  have hs : score i q = score j q := by
    funext p; simp [score, hi.docs_eq, hj.docs_eq]
  have hb : before i q = before j q := by
    funext a b; simp [before, hs]
  have hh : ∀ p, hit i keep q p = hit j keep q p := by
    intro p
    have hm : ∀ t, decide (p ∈ i.terms t) = decide (p ∈ j.terms t) := fun t =>
      decide_eq_decide.mpr ((hi.postings t p).trans (hj.postings t p).symm)
    simp only [hit, hm]
  unfold search ranked
  rw [hi.docs_eq, hj.docs_eq, hb, show hit i keep q = hit j keep q from funext hh]

/-- Freshness. Start from an index fresh for the pod, and apply `put` for each
write and `remove` for each delete. Every search on the result gives exactly
what an index built afresh from the resulting contents gives. -/
theorem search_ops_eq_build {i : Index} {c : Pod} (hf : Fresh i c) (ops : List Op)
    (keep : String → Bool) (q : List String) (n : Nat) :
    search (applyIndex ops i) keep q n = search (build (applyPod ops c)) keep q n := by
  have h := fresh_ops ops hf
  exact search_fresh_eq h (fresh_build h.paths_nodup) keep q n

/-- The same, from an empty pod: any history of writes and deletes. -/
theorem search_history_eq_build (ops : List Op) (keep : String → Bool)
    (q : List String) (n : Nat) :
    search (applyIndex ops Index.empty) keep q n =
      search (build (applyPod ops [])) keep q n :=
  search_ops_eq_build fresh_empty ops keep q n

/-! ## Examples: two apps' files in one pod -/

/-- Notes app and chat app, each in its own folder. -/
def demoOps : List Op :=
  [ .write "/apps/notes/a.txt" ["red", "apple", "pie"],
    .write "/apps/chat/b.txt" ["a", "red", "apple", "red"],
    .write "/apps/notes/c.txt" ["green", "apple"],
    .write "/apps/notes/d.txt" ["red", "apple", "red", "apple"] ]

def demo : Index := applyIndex demoOps Index.empty

def inNotes (p : String) : Bool := p.startsWith "/apps/notes/"
def everyone (_ : String) : Bool := true

-- The notes app finds only its own files; d.txt ranks first (4 occurrences).
#guard search demo inNotes ["red", "apple"] 10 == ["/apps/notes/d.txt", "/apps/notes/a.txt"]
-- The chat file is not in the notes app's result, though it matches.
#guard search demo everyone ["red", "apple"] 10 ==
  ["/apps/notes/d.txt", "/apps/chat/b.txt", "/apps/notes/a.txt"]
-- Filter before limit: with limit 1, the notes app still gets a notes file.
#guard search demo inNotes ["red", "apple"] 1 == ["/apps/notes/d.txt"]
#guard search demo (fun p => p.startsWith "/apps/chat/") ["red", "apple"] 1 == ["/apps/chat/b.txt"]
-- Every query word must occur.
#guard search demo everyone ["green", "red"] 10 == []
-- No words, nothing.
#guard search demo everyone [] 10 == []
-- A rewrite drops the old words; a delete drops the path.
#guard search (demo.put "/apps/notes/d.txt" ["blue"]) inNotes ["red"] 10 == ["/apps/notes/a.txt"]
#guard search (demo.remove "/apps/notes/a.txt") inNotes ["red"] 10 == ["/apps/notes/d.txt"]
-- The maintained index agrees with one built from the contents.
#guard search demo everyone ["apple"] 10 == search (build (applyPod demoOps [])) everyone ["apple"] 10

end L4Factoidal.LWS.PodSearch
