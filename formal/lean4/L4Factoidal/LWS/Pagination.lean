/-
L4Factoidal.LWS.Pagination — the pages of a container listing.

Source: the W3C Linked Web Storage Working Group editor's draft,
https://w3c.github.io/lws-protocol/lws10-core/, read 2026-10-21 at
w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19), §LWS Media Type, "Pagination" (verbatim):

  "servers SHOULD support pagination for containers whose membership
  exceeds a server-determined threshold."
  "When a listing is paginated, the response body contains only the current
  page of items. The composite resource's `id`, `type`, and `totalItems`
  properties reflect the full membership, while `items` contains only the
  resources on the current page."
  "`rel="first"`: The URI of the first page of results. MUST be present on
  paginated responses." "`rel="last"`: ... MAY be present on paginated
  responses." "`rel="next"`: ... MUST be present when there are subsequent
  pages. MUST be omitted on the last page." "`rel="prev"`: ... MAY be
  present when there are preceding pages. MUST be omitted on the first
  page."

The draft does not state an order of the members or what a client sees when
the container changes between two page requests. This module states both:

* Order: the members are listed in increasing order of their path, by the
  `String` order (Unicode code points, which is also UTF-8 byte order), each
  path once (`orderPaths`). The order depends only on the set of paths, so
  it does not depend on the order in which a store enumerates them.
* Change between requests: every page is computed from the state at the
  time of its request. A page's entity tag starts with the container's
  modification clock, which every change to the membership advances
  (`Operations.touchContainer`), so a client that sees two different clocks
  across the pages of one scan knows that the container changed.

The page size is the server's threshold (`Config.pageSize`). Page numbers
start at 1. Everything here is a pure function; `pages_concat` is the
theorem that concatenating every page gives back the whole listing.
-/

namespace L4Factoidal.LWS

/-! ## Order: sorted by path, each path once -/

/-- Drop the elements equal to `prev` that follow it in a sorted list. -/
def dedupFrom (prev : String) : List String → List String
  | [] => []
  | x :: xs => if x == prev then dedupFrom prev xs else x :: dedupFrom x xs

/-- Remove adjacent repeats. On a sorted list this removes every repeat. -/
def dedupSorted : List String → List String
  | [] => []
  | x :: xs => x :: dedupFrom x xs

/-- The loop form of `dedupFrom`, with an accumulator. -/
def dedupFromTR (prev : String) (acc : Array String) : List String → Array String
  | [] => acc
  | x :: xs => if x == prev then dedupFromTR prev acc xs else dedupFromTR x (acc.push x) xs

theorem dedupFromTR_eq (prev : String) (acc : Array String) (l : List String) :
    dedupFromTR prev acc l = acc ++ (dedupFrom prev l).toArray := by
  induction l generalizing prev acc with
  | nil => simp [dedupFromTR, dedupFrom]
  | cons x xs ih =>
      by_cases h : x = prev
      · simp [dedupFromTR, dedupFrom, h, ih]
      · simp [dedupFromTR, dedupFrom, h, ih]

/-- `dedupFrom` runs as the loop `dedupFromTR`. -/
def dedupFromLoop (prev : String) (l : List String) : List String :=
  (dedupFromTR prev #[] l).toList

@[csimp] theorem dedupFrom_eq_TR : @dedupFrom = @dedupFromLoop := by
  funext prev l
  simp [dedupFromLoop, dedupFromTR_eq]

/-- The loop form of `dedupSorted`. -/
def dedupSortedTR : List String → List String
  | [] => []
  | x :: xs => (dedupFromTR x #[x] xs).toList

@[csimp] theorem dedupSorted_eq_TR : @dedupSorted = @dedupSortedTR := by
  funext l
  cases l with
  | nil => rfl
  | cons x xs => simp [dedupSorted, dedupSortedTR, dedupFromTR_eq]

theorem mem_of_mem_dedupFrom {prev y : String} {l : List String} :
    y ∈ dedupFrom prev l → y ∈ l := by
  induction l generalizing prev with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
      unfold dedupFrom
      split
      · intro h; exact List.mem_cons_of_mem x (ih h)
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem x (ih h)

theorem mem_dedupFrom_of_mem {prev y : String} {l : List String} :
    y ∈ l → y = prev ∨ y ∈ dedupFrom prev l := by
  induction l generalizing prev with
  | nil => simp
  | cons x xs ih =>
      intro hy
      unfold dedupFrom
      rcases List.mem_cons.mp hy with h | h
      · by_cases hx : x = prev
        · exact .inl (h ▸ hx)
        · simp [hx, h]
      · by_cases hx : x = prev
        · simp only [hx, beq_self_eq_true, ite_true]; exact ih h
        · simp only [beq_iff_eq, hx, ite_false, List.mem_cons]
          rcases ih (prev := x) h with h' | h'
          · exact .inr (.inl h')
          · exact .inr (.inr h')

/-- On a list sorted by `≤` that starts at `prev`, `dedupFrom` leaves a list
strictly increasing from `prev`. -/
theorem dedupFrom_strict {prev : String} {l : List String}
    (h : List.Pairwise (· ≤ ·) (prev :: l)) :
    List.Pairwise (· < ·) (prev :: dedupFrom prev l) := by
  induction l generalizing prev with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
      have hpx : prev ≤ x := (List.pairwise_cons.mp h).1 x List.mem_cons_self
      have hrest : List.Pairwise (· ≤ ·) (x :: xs) := (List.pairwise_cons.mp h).2
      have hprevxs : List.Pairwise (· ≤ ·) (prev :: xs) :=
        List.pairwise_cons.mpr ⟨fun y hy => (List.pairwise_cons.mp h).1 y
          (List.mem_cons_of_mem x hy), (List.pairwise_cons.mp hrest).2⟩
      unfold dedupFrom
      by_cases hx : x = prev
      · simp only [hx, beq_self_eq_true, ite_true]; exact ih hprevxs
      · simp only [beq_iff_eq, hx, ite_false]
        have hlt : prev < x := Std.lt_of_le_of_ne hpx (fun e => hx e.symm)
        have hx' := ih hrest
        refine List.pairwise_cons.mpr ⟨?_, hx'⟩
        intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · exact hy ▸ hlt
        · exact String.lt_trans hlt ((List.pairwise_cons.mp hx').1 y hy)

theorem dedupSorted_strict {l : List String} (h : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· < ·) (dedupSorted l) := by
  cases l with
  | nil => simp [dedupSorted]
  | cons x xs => exact dedupFrom_strict h

theorem mem_dedupSorted {y : String} {l : List String} : y ∈ dedupSorted l ↔ y ∈ l := by
  cases l with
  | nil => simp [dedupSorted]
  | cons x xs =>
      simp only [dedupSorted, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (mem_of_mem_dedupFrom h)
      · rintro (h | h)
        · exact .inl h
        · exact mem_dedupFrom_of_mem h

/-- The listing order: increasing path, each path once. -/
def orderPaths (ps : List String) : List String :=
  dedupSorted (ps.mergeSort (fun a b => decide (a ≤ b)))

theorem orderPaths_sorted (ps : List String) : List.Pairwise (· < ·) (orderPaths ps) := by
  apply dedupSorted_strict
  have h := List.pairwise_mergeSort (le := fun a b : String => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact String.le_trans hab hbc)
    (fun a b => by
      rcases String.le_total a b with h | h <;> simp [h])
    ps
  exact h.imp (fun h => by simpa using h)

/-- Each path of the listing occurs once. -/
theorem orderPaths_nodup (ps : List String) : (orderPaths ps).Nodup :=
  (orderPaths_sorted ps).imp (fun {a b} (h : a < b) (e : a = b) => String.lt_irrefl a (by rw [e] at h ⊢; exact h))

theorem mem_orderPaths {p : String} {ps : List String} : p ∈ orderPaths ps ↔ p ∈ ps := by
  simp [orderPaths, mem_dedupSorted, (List.mergeSort_perm ps _).mem_iff]

/-- Two lists in strictly increasing order with the same members are equal. -/
theorem sorted_eq_of_mem_iff : ∀ {l1 l2 : List String}, l1.Pairwise (· < ·) →
    l2.Pairwise (· < ·) → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: _, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: t1, b :: t2, h1, h2, h => by
      have p1 := List.pairwise_cons.mp h1
      have p2 := List.pairwise_cons.mp h2
      have hab : a = b := by
        rcases List.mem_cons.mp ((h a).mp (List.mem_cons_self ..)) with hab | hat
        · exact hab
        · rcases List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..)) with hba | hbt
          · exact hba.symm
          · exact absurd (p1.1 b hbt) (String.lt_asymm (p2.1 a hat))
      subst hab
      congr 1
      apply sorted_eq_of_mem_iff p1.2 p2.2
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with hxa | hxt
        · subst hxa; exact absurd (p1.1 _ hx) (String.lt_irrefl _)
        · exact hxt
      · intro hx
        rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with hxa | hxt
        · subst hxa; exact absurd (p2.1 _ hx) (String.lt_irrefl _)
        · exact hxt

/-- `orderPaths` depends only on the members of its argument. -/
theorem orderPaths_ext {l1 l2 : List String} (h : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    orderPaths l1 = orderPaths l2 :=
  sorted_eq_of_mem_iff (orderPaths_sorted _) (orderPaths_sorted _)
    (fun x => by rw [mem_orderPaths, mem_orderPaths]; exact h x)

/-! ## Pages -/

/-- The number of pages of a listing of `n` members at page size `k`. A page
size of 0 means the listing is not paginated: one page. An empty listing
still has one (empty) page. -/
def pageCount (n k : Nat) : Nat := if k = 0 then 1 else max 1 ((n + k - 1) / k)

/-- The page with zero-based index `i`. -/
def pageAt (xs : List α) (k i : Nat) : List α :=
  if k = 0 then xs else (xs.drop (i * k)).take k

/-- Is the listing paginated: does it have more members than one page holds?
Below the threshold the full listing is returned with no pagination links. -/
def paginated (n k : Nat) : Bool := k != 0 && n > k

theorem pages_take (xs : List α) (k n : Nat) (hk : k ≠ 0) :
    (List.range n).flatMap (pageAt xs k) = xs.take (n * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.take_add]
      simp [pageAt, hk]

theorem len_le_pageCount (n k : Nat) (hk : k ≠ 0) : n ≤ pageCount n k * k := by
  unfold pageCount
  simp only [hk, ite_false]
  have h1 := Nat.div_add_mod (n + k - 1) k
  have h2 := Nat.mod_lt (n + k - 1) (Nat.pos_of_ne_zero hk)
  have h3 : (n + k - 1) / k ≤ max 1 ((n + k - 1) / k) := Nat.le_max_right _ _
  have h4 : (n + k - 1) / k * k ≤ max 1 ((n + k - 1) / k) * k := Nat.mul_le_mul_right k h3
  rw [Nat.mul_comm] at h1
  omega

/-- Concatenating every page, in page order, gives the listing back: each
member once, in listing order. -/
theorem pages_concat (xs : List α) (k : Nat) :
    (List.range (pageCount xs.length k)).flatMap (pageAt xs k) = xs := by
  by_cases hk : k = 0
  · simp [pageCount, pageAt, hk]
  · rw [pages_take xs k _ hk]
    exact List.take_of_length_le (len_le_pageCount xs.length k hk)

/-- A page holds at most `k` members. -/
theorem pageAt_length_le (xs : List α) (k i : Nat) (hk : k ≠ 0) :
    (pageAt xs k i).length ≤ k := by
  simp [pageAt, hk, Nat.min_le_left]

/-! ## Page references in a request target

A page is named by the query `page=N`, N from 1. The URIs are opaque to a
client (the draft: "Clients SHOULD NOT construct or modify pagination
URIs"); this server reads only the ones it writes. -/

/-- The one-based page number a query names, if it names one. -/
def pageOfQuery? (q : String) : Option Nat :=
  if q.startsWith "page=" then
    let d := String.ofList (q.toList.drop 5)
    if d != "" && d.all Char.isDigit && !d.startsWith "0" then d.toNat? else none
  else none

/-- The query that names page `n`. -/
def pageQuery (n : Nat) : String := "page=" ++ toString n

#guard pageOfQuery? "page=2" == some 2
#guard pageOfQuery? "page=0" == none
#guard pageOfQuery? "page=02" == none
#guard pageOfQuery? "page=" == none
#guard pageOfQuery? "linkset" == none
#guard pageOfQuery? (pageQuery 17) == some 17
#guard orderPaths ["/c/b", "/c/a", "/c/b", "/c/A"] == ["/c/A", "/c/a", "/c/b"]
#guard pageCount 120 100 == 2
#guard pageCount 100 100 == 1
#guard pageCount 0 100 == 1
#guard pageCount 5 0 == 1
#guard paginated 120 100 && !paginated 100 100 && !paginated 120 0
#guard pageAt [1, 2, 3, 4, 5] 2 2 == [5]
#guard (List.range (pageCount 5 2)).flatMap (pageAt [1, 2, 3, 4, 5] 2) == [1, 2, 3, 4, 5]

end L4Factoidal.LWS
