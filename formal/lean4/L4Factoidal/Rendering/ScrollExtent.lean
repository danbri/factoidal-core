/-! The scrollable overflow of a box (CSSOM View §6.1 `scrollWidth` and `scrollHeight`;
CSS Overflow 3 §2.2), on layout units. This module has no import from the engine. -/
namespace L4Factoidal.Rendering.ScrollExtent

/-- The size of the scrollable overflow of a box, seen from the corner of its padding
box: `width` by `height` is the padding box (the client size) and `kids` are the right
and bottom edges of the boxes inside it, from that corner. The area is the padding box
extended to the furthest right and bottom edges. What lies above or to the left of the
corner can not be scrolled to and is not counted (a left-to-right, top-to-bottom box). -/
def extent (width height : Int) (kids : List (Int × Int)) : Int × Int :=
  kids.foldl (fun acc k => (max acc.1 k.1, max acc.2 k.2)) (width, height)

theorem foldl_ge (kids : List (Int × Int)) : ∀ acc : Int × Int,
    acc.1 ≤ (kids.foldl (fun acc k => (max acc.1 k.1, max acc.2 k.2)) acc).1 ∧
    acc.2 ≤ (kids.foldl (fun acc k => (max acc.1 k.1, max acc.2 k.2)) acc).2 := by
  induction kids with
  | nil => intro acc; simp
  | cons k rest ih =>
    intro acc
    simp only [List.foldl_cons]
    have h := ih (max acc.1 k.1, max acc.2 k.2)
    constructor
    · exact Int.le_trans (by simp only; omega) h.1
    · exact Int.le_trans (by simp only; omega) h.2

theorem foldl_ge_kid (kids : List (Int × Int)) : ∀ acc : Int × Int, ∀ k ∈ kids,
    k.1 ≤ (kids.foldl (fun acc k => (max acc.1 k.1, max acc.2 k.2)) acc).1 ∧
    k.2 ≤ (kids.foldl (fun acc k => (max acc.1 k.1, max acc.2 k.2)) acc).2 := by
  induction kids with
  | nil => intro acc k hk; simp at hk
  | cons j rest ih =>
    intro acc k hk
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hk'
    · have h := foldl_ge rest (max acc.1 k.1, max acc.2 k.2)
      constructor
      · exact Int.le_trans (by simp only; omega) h.1
      · exact Int.le_trans (by simp only; omega) h.2
    · exact ih _ k hk'

/-- Lower bound. Says: the scroll size is never less than the client size. -/
theorem extent_ge_client (width height : Int) (kids : List (Int × Int)) :
    width ≤ (extent width height kids).1 ∧ height ≤ (extent width height kids).2 :=
  foldl_ge kids (width, height)

/-- Reach. Says: every box inside is within the scrollable area: its right and bottom
edges are not past the scroll size. Does not say: anything about its left and top edges
(a box above or left of the padding box is out of reach). -/
theorem extent_ge_kid (width height : Int) (kids : List (Int × Int)) (k : Int × Int) (hk : k ∈ kids) :
    k.1 ≤ (extent width height kids).1 ∧ k.2 ≤ (extent width height kids).2 :=
  foldl_ge_kid kids (width, height) k hk

/-- No overflow. Says: when every box inside ends within the padding box, the scroll
size is the client size: a box that does not overflow has nothing to scroll. -/
theorem extent_inside (width height : Int) (kids : List (Int × Int))
    (h : ∀ k ∈ kids, k.1 ≤ width ∧ k.2 ≤ height) : extent width height kids = (width, height) := by
  unfold extent
  induction kids with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.foldl_cons]
    have hk := h k List.mem_cons_self
    have h1 : max width k.1 = width := by omega
    have h2 : max height k.2 = height := by omega
    rw [h1, h2]
    exact ih (fun j hj => h j (List.mem_cons_of_mem k hj))

#guard extent 100 50 [] == (100, 50)
#guard extent 100 50 [(80, 300), (120, 20)] == (120, 300)
#guard extent 100 50 [(-10, -10)] == (100, 50)

end L4Factoidal.Rendering.ScrollExtent
