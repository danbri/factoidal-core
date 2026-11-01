import SVGStroke
import Std.Tactic
namespace NativeSVGStroke
open NativeSVG NativeSVGPath
private theorem zip_tail_seam {α : Type} (a first : α) (rest : List α) :
    (a :: rest).zip (rest ++ [first]) =
      (a :: rest).zip rest ++ [(rest.getLast?.getD a,first)] := by
  induction rest generalizing a with
  | nil => simp
  | cons b tail ih =>
    simp only [List.cons_append, List.zip_cons_cons]
    rw [ih]
    simp [List.getLast?_cons]
/-- Open stroke edges are exactly the nonzero consecutive vertex pairs.
    No implicit fill-closing edge can enter the retained stroke. -/
theorem edges_open_exact (points : List Point) :
    edges ⟨points,false⟩ =
      (points.zip (points.drop 1)).filter (fun (a,b) => a.x != b.x || a.y != b.y) := by
  simp [edges]

/-- An explicitly closed nonempty contour adds only its last-to-first seam,
    before the same numeric zero-edge filter. -/
theorem edges_closed_exact (first : Point) (rest : List Point) :
    edges ⟨first::rest,true⟩ =
      ((first::rest).zip rest ++ [(rest.getLast?.getD first,first)]).filter
        (fun (a,b) => a.x != b.x || a.y != b.y) := by
  simp only [edges, List.drop_succ_cons, List.drop_zero, ↓reduceIte,
    List.take_succ_cons, List.take_zero]
  rw [zip_tail_seam]

/-- Every surviving open edge is consecutive and passes the actual Float filter. -/
theorem edges_open_member (points : List Point) (edge : Point × Point) :
    edge ∈ edges ⟨points,false⟩ ↔
      edge ∈ points.zip (points.drop 1) ∧ (edge.1.x != edge.2.x || edge.1.y != edge.2.y) = true := by
  rw [edges_open_exact, List.mem_filter]

/-- Numeric filtering can remove a closed edge, never invent a cross-contour link. -/
theorem edges_closed_member (first : Point) (rest : List Point) (edge : Point × Point) :
    edge ∈ edges ⟨first::rest,true⟩ ↔
      (edge ∈ (first::rest).zip rest ∨ edge = (rest.getLast?.getD first,first)) ∧
        (edge.1.x != edge.2.x || edge.1.y != edge.2.y) = true := by
  rw [edges_closed_exact, List.mem_filter]
  simp only [List.mem_append, List.mem_singleton]
end NativeSVGStroke
