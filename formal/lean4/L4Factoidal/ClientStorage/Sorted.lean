/-
L4Factoidal.ClientStorage.Sorted — records kept in key order, and the cursor over them.

An IndexedDB object store is a list of records sorted by key, and an index is a list of
entries sorted by (index key, primary key) (Indexed Database API 3.0 §2.6, §2.7). This
module is that list for any comparator that is a strict total order (`IsOrder`): `insert`,
`erase`, `find`, the running size count, and the cursor step `next` ("iterate a cursor",
§7.8: the first record after the cursor's position that is in its range).

Theorems: `insert_sorted` and `erase_sorted` (the order is kept), `find_insert_self`,
`find_erase_self`, `sizeSum_insert` (what the running byte count must add and take away),
and `walk_eq_filter` / `walkRev_eq_filter`: a cursor that starts with no position and steps
until it finds nothing visits exactly the records in its range, each once, in key order
(or in reverse order for a `prev` cursor).

`insert`, `erase`, `find` and `next` are single passes of core list combinators that
compile to loops (`filter`, `find?`); `walk` is a loop with an accumulator. The list is
the specification: a tree with the same answers can replace it later (open: the record's
"Performance").
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Sorted

/-- A comparator that is a strict total order. -/
structure IsOrder {κ : Type} (c : κ → κ → Ordering) : Prop where
  refl : ∀ a, c a a = .eq
  eq : ∀ a b, c a b = .eq → a = b
  swap : ∀ a b, c b a = (c a b).swap
  trans : ∀ a b d, c a b = .lt → c b d = .lt → c a d = .lt

/-- The lexicographic comparator of pairs (an index entry: index key, then primary key). -/
def lex {κ₁ κ₂ : Type} (c₁ : κ₁ → κ₁ → Ordering) (c₂ : κ₂ → κ₂ → Ordering) (a b : κ₁ × κ₂) : Ordering :=
  (c₁ a.1 b.1).then (c₂ a.2 b.2)

theorem then_lt' {o p : Ordering} : o.then p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> simp [Ordering.then]

/-- Kind: order law. Says: the lexicographic comparator of two strict total orders is a
strict total order, so index entries (index key, primary key) are totally ordered. -/
theorem IsOrder.lex {κ₁ κ₂ : Type} {c₁ : κ₁ → κ₁ → Ordering} {c₂ : κ₂ → κ₂ → Ordering}
    (h₁ : IsOrder c₁) (h₂ : IsOrder c₂) : IsOrder (lex c₁ c₂) where
  refl := fun a => by simp [Sorted.lex, h₁.refl, h₂.refl, Ordering.then]
  eq := fun a b h => by
    have h' : c₁ a.1 b.1 = .eq ∧ c₂ a.2 b.2 = .eq := by
      unfold Sorted.lex at h
      cases h1 : c₁ a.1 b.1 <;> cases h2 : c₂ a.2 b.2 <;> simp [h1, h2, Ordering.then] at h ⊢
    exact Prod.ext (h₁.eq _ _ h'.1) (h₂.eq _ _ h'.2)
  swap := fun a b => by
    unfold Sorted.lex
    rw [h₁.swap a.1 b.1, h₂.swap a.2 b.2]
    cases c₁ a.1 b.1 <;> cases c₂ a.2 b.2 <;> rfl
  trans := fun a b d hab hbd => by
    unfold Sorted.lex at *
    rw [then_lt'] at *
    rcases hab with hab | ⟨e1, hab⟩ <;> rcases hbd with hbd | ⟨e2, hbd⟩
    · exact .inl (h₁.trans _ _ _ hab hbd)
    · rw [← h₁.eq _ _ e2]; exact .inl hab
    · rw [h₁.eq _ _ e1]; exact .inl hbd
    · rw [h₁.eq _ _ e1, e2]; exact .inr ⟨rfl, h₂.trans _ _ _ hab hbd⟩

theorem IsOrder.gt_of_lt {κ : Type} {c : κ → κ → Ordering} (h : IsOrder c) {a b : κ} (hab : c a b = .lt) :
    c b a = .gt := by rw [h.swap a b, hab]; rfl

theorem IsOrder.lt_of_gt {κ : Type} {c : κ → κ → Ordering} (h : IsOrder c) {a b : κ} (hab : c a b = .gt) :
    c b a = .lt := by rw [h.swap a b, hab]; rfl

section
variable {κ ν : Type} (c : κ → κ → Ordering)

/-- Strictly ascending keys: no two records with one key. -/
def Sorted (l : List (κ × ν)) : Prop := l.Pairwise fun a b => c a.1 b.1 = .lt

/-- The list with the record of key `k` set to `v`: the records below `k`, the new record,
the records above `k`. -/
def insert (l : List (κ × ν)) (k : κ) (v : ν) : List (κ × ν) :=
  l.filter (fun e => c e.1 k == .lt) ++ (k, v) :: l.filter (fun e => c e.1 k == .gt)

/-- The list without the record of key `k`. -/
def erase (l : List (κ × ν)) (k : κ) : List (κ × ν) := l.filter fun e => c e.1 k != .eq

/-- The record of key `k`. -/
def find (l : List (κ × ν)) (k : κ) : Option (κ × ν) := l.find? fun e => c e.1 k == .eq

variable {c}

/-- Kind: invariant. Says: setting a record keeps the list strictly sorted (so it holds at
most one record a key). -/
theorem insert_sorted (h : IsOrder c) (l : List (κ × ν)) (k : κ) (v : ν) (hs : Sorted c l) :
    Sorted c (insert c l k v) := by
  unfold insert Sorted
  rw [List.pairwise_append]
  refine ⟨hs.filter _, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, hs.filter _⟩
    intro b hb
    have : c b.1 k = .gt := by simpa using (List.mem_filter.mp hb).2
    exact h.lt_of_gt this
  · intro a ha b hb
    have ha' : c a.1 k = .lt := by simpa using (List.mem_filter.mp ha).2
    rcases List.mem_cons.mp hb with e | hb
    · rw [e]; exact ha'
    · have hb' : c b.1 k = .gt := by simpa using (List.mem_filter.mp hb).2
      exact h.trans _ _ _ ha' (h.lt_of_gt hb')

/-- Kind: invariant. Says: removing a record keeps the list strictly sorted. -/
theorem erase_sorted (l : List (κ × ν)) (k : κ) (hs : Sorted c l) : Sorted c (erase c l k) :=
  hs.filter _

/-- Kind: functional law. Says: after a record is set, looking its key up answers it. -/
theorem find_insert_self (h : IsOrder c) (l : List (κ × ν)) (k : κ) (v : ν) :
    find c (insert c l k v) k = some (k, v) := by
  unfold find insert
  rw [List.find?_append]
  have hnone : (l.filter fun e => c e.1 k == .lt).find? (fun e => c e.1 k == .eq) = none := by
    rw [List.find?_eq_none]
    intro e he
    have : c e.1 k = .lt := by simpa using (List.mem_filter.mp he).2
    simp [this]
  rw [hnone]
  simp [h.refl]

/-- Kind: functional law. Says: after a record is removed, looking its key up answers
nothing. -/
theorem find_erase_self (l : List (κ × ν)) (k : κ) : find c (erase c l k) k = none := by
  unfold find erase
  rw [List.find?_eq_none]
  intro e he
  have := (List.mem_filter.mp he).2
  simpa using this

/-- Kind: accounting law. Says: the sizes of a list are the sizes of its records below,
at and above a key. -/
theorem sizeSum_split (size : κ × ν → Nat) (l : List (κ × ν)) (k : κ) :
    sizeSum size l = sizeSum size (l.filter fun e => c e.1 k == .lt)
      + sizeSum size (l.filter fun e => c e.1 k == .eq) + sizeSum size (l.filter fun e => c e.1 k == .gt) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [sizeSum_cons, ih]
    cases hx : c x.1 k <;> simp [hx, sizeSum_cons] <;> omega

/-- Kind: accounting law. Says: after a record is set, the sum of the stored sizes is the
sum before, less the sizes of the records that had that key, plus the size of the new
record: what a running byte count must do to stay equal to the sum. -/
theorem sizeSum_insert (size : κ × ν → Nat) (l : List (κ × ν)) (k : κ) (v : ν) :
    sizeSum size (insert c l k v) + sizeSum size (l.filter fun e => c e.1 k == .eq)
      = sizeSum size l + size (k, v) := by
  unfold insert
  rw [sizeSum_append, sizeSum_cons, sizeSum_split (c := c) size l k]
  omega

/-- Kind: accounting law. Says: after a record is removed, the sum of the stored sizes is
the sum before less the sizes of the records that had that key. -/
theorem sizeSum_erase (size : κ × ν → Nat) (l : List (κ × ν)) (k : κ) :
    sizeSum size (erase c l k) + sizeSum size (l.filter fun e => c e.1 k == .eq) = sizeSum size l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold erase at *
    cases hx : c x.1 k <;> simp [hx, sizeSum_cons] <;> omega

/-! ## The cursor -/

variable (c)

/-- A key is after a cursor's position (no position: every key is). -/
def after (pos : Option κ) (k : κ) : Bool :=
  match pos with
  | none => true
  | some p => c p k == .lt

/-- One step of a cursor ("iterate a cursor", §7.8, direction `next`): the first record
that is in the range and after the position. -/
def next (inR : κ → Bool) (l : List (κ × ν)) (pos : Option κ) : Option (κ × ν) :=
  l.find? fun e => inR e.1 && after c pos e.1

/-- A cursor run to its end: step from `pos` until nothing is found (at most `fuel`
steps), collecting the records visited. -/
def walk (inR : κ → Bool) (l : List (κ × ν)) : Nat → Option κ → List (κ × ν) → List (κ × ν)
  | 0, _, acc => acc.reverse
  | fuel + 1, pos, acc =>
    match next c inR l pos with
    | none => acc.reverse
    | some e => walk inR l fuel (some e.1) (e :: acc)

variable {c}

/-- A record that the cursor will never stop at: it is outside the range, or not after the
position. -/
private def skipped (c : κ → κ → Ordering) (inR : κ → Bool) (x : κ × ν) (pos : Option κ) : Prop :=
  inR x.1 = false ∨ ∃ p, pos = some p ∧ c p x.1 ≠ .lt

private theorem walk_skip (h : IsOrder c) (inR : κ → Bool) (x : κ × ν) (xs : List (κ × ν)) :
    ∀ (fuel : Nat) (pos : Option κ) (acc : List (κ × ν)), skipped c inR x pos →
      walk c inR (x :: xs) fuel pos acc = walk c inR xs fuel pos acc := by
  intro fuel
  induction fuel with
  | zero => intro pos acc _; rfl
  | succ n ih =>
    intro pos acc hs
    have hx : (inR x.1 && after c pos x.1) = false := by
      rcases hs with hr | ⟨p, hp, hlt⟩
      · simp [hr]
      · subst hp
        cases hc : c p x.1 <;> simp_all [after]
    have hn : next c inR (x :: xs) pos = next c inR xs pos := by
      unfold next; rw [List.find?_cons, hx]
    unfold walk
    rw [hn]
    cases hf : next c inR xs pos with
    | none => rfl
    | some e =>
      simp only
      apply ih
      rcases hs with hr | ⟨p, hp, hlt⟩
      · exact .inl hr
      · refine .inr ⟨e.1, rfl, ?_⟩
        subst hp
        have he := List.find?_some hf
        have hpe : c p e.1 = .lt := by simp [after] at he; exact he.2
        intro hex
        exact hlt (h.trans _ _ _ hpe hex)

private theorem walk_gen (h : IsOrder c) (inR : κ → Bool) :
    ∀ (l : List (κ × ν)) (fuel : Nat) (pos : Option κ) (acc : List (κ × ν)), Sorted c l →
      (∀ e ∈ l, after c pos e.1 = true) → l.length < fuel →
      walk c inR l fuel pos acc = acc.reverse ++ l.filter (fun e => inR e.1) := by
  intro l
  induction l with
  | nil =>
    intro fuel pos acc _ _ hf
    cases fuel with
    | zero => omega
    | succ n => simp [walk, next]
  | cons x xs ih =>
    intro fuel pos acc hs hall hf
    have hs' : Sorted c xs := (List.pairwise_cons.mp hs).2
    have hxlt : ∀ e ∈ xs, c x.1 e.1 = .lt := (List.pairwise_cons.mp hs).1
    cases hr : inR x.1 with
    | false =>
      rw [walk_skip h inR x xs fuel pos acc (.inl hr)]
      rw [ih fuel pos acc hs' (fun e he => hall e (List.mem_cons_of_mem _ he)) (by simp at hf; omega)]
      simp [hr]
    | true =>
      cases fuel with
      | zero => omega
      | succ n =>
        have hax : after c pos x.1 = true := hall x (List.mem_cons_self ..)
        have hn : next c inR (x :: xs) pos = some x := by
          unfold next; rw [List.find?_cons]; simp [hr, hax]
        unfold walk
        rw [hn]
        simp only
        rw [walk_skip h inR x xs n (some x.1) (x :: acc) (.inr ⟨x.1, rfl, by rw [h.refl]; simp⟩)]
        rw [ih n (some x.1) (x :: acc) hs' (fun e he => by simp [after, hxlt e he]) (by simp at hf; omega)]
        simp [hr]

/-- Kind: correctness of cursor iteration (direction `next`). Says: over a strictly sorted
list, a cursor that starts with no position and steps until it finds nothing visits exactly
the records whose keys are in its range, each once, in ascending key order. Does not say:
what a cursor sees when the list changes between steps (then each step is `next` on the
list of that moment: the first record in range after the last key visited), nor anything
about `nextunique` on an index. -/
theorem walk_eq_filter (h : IsOrder c) (inR : κ → Bool) (l : List (κ × ν)) (hs : Sorted c l) :
    walk c inR l (l.length + 1) none [] = l.filter (fun e => inR e.1) := by
  rw [walk_gen h inR l (l.length + 1) none [] hs (fun _ _ => rfl) (Nat.lt_succ_self _)]
  rfl

/-- The comparator in the other direction: a `prev` cursor is a `next` cursor over the
reversed list with this comparator. -/
def flip (c : κ → κ → Ordering) (a b : κ) : Ordering := c b a

theorem IsOrder.flip (h : IsOrder c) : IsOrder (flip c) where
  refl := fun a => h.refl a
  eq := fun a b hab => (h.eq b a hab).symm
  swap := fun a b => h.swap b a
  trans := fun a b d hab hbd => h.trans d b a hbd hab

/-- Kind: correctness of cursor iteration (direction `prev`). Says: over a strictly sorted
list, a `prev` cursor (a cursor over the reversed list, with the comparator reversed)
visits exactly the records in its range, each once, in descending key order. Does not say:
anything about `prevunique` on an index. -/
theorem walkRev_eq_filter (h : IsOrder c) (inR : κ → Bool) (l : List (κ × ν)) (hs : Sorted c l) :
    walk (flip c) inR l.reverse (l.length + 1) none [] = (l.filter (fun e => inR e.1)).reverse := by
  have hs' : Sorted (flip c) l.reverse := by
    unfold Sorted; rw [List.pairwise_reverse]; exact hs
  have := walk_eq_filter h.flip inR l.reverse hs'
  rw [List.length_reverse] at this
  rw [this, List.filter_reverse]

end

/-! ## Checks -/

private def cn (a b : Nat) : Ordering := compare a b
private def l0 : List (Nat × String) := insert cn (insert cn (insert cn (insert cn [] 5 "e") 1 "a") 9 "i") 3 "c"
#guard l0 == [(1, "a"), (3, "c"), (5, "e"), (9, "i")]
#guard insert cn l0 5 "E" == [(1, "a"), (3, "c"), (5, "E"), (9, "i")]
#guard erase cn l0 3 == [(1, "a"), (5, "e"), (9, "i")]
#guard find cn l0 9 == some (9, "i") && find cn l0 4 == none
#guard next cn (fun k => 2 ≤ k && k ≤ 9) l0 none == some (3, "c")
#guard next cn (fun k => 2 ≤ k && k ≤ 9) l0 (some 3) == some (5, "e")
#guard next cn (fun k => 2 ≤ k && k < 9) l0 (some 5) == none
#guard walk cn (fun k => 2 ≤ k) l0 5 none [] == [(3, "c"), (5, "e"), (9, "i")]
#guard walk (flip cn) (fun k => 2 ≤ k) l0.reverse 5 none [] == [(9, "i"), (5, "e"), (3, "c")]

end L4Factoidal.ClientStorage.Sorted
