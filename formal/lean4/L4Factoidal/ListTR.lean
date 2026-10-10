/-
L4Factoidal.ListTR — lemmas shared by the accumulator forms that replace
input-length recursion (https://github.com/danbri/factoidal/issues/746).

A self-call that is not in tail position costs one C stack frame per list
element; in the wasm module under Node's default stack that is a
`RangeError` near 10,000 elements. The repair keeps each readable
definition, adds a form whose self-call is a tail call (or a call of a core
combinator that compiles to a loop: `List.mapM` in `Option`,
`List.filterMap`, `List.foldl`), proves the two equal, and registers the
equality with `@[csimp]`. The method and the gate:
`skills/danbri-function-precrime-checkers/SKILL.md`,
`tools/lean-tail-recursion-audit.py --gate`.
-/

namespace L4Factoidal.ListTR

/-- One step of `List.mapM` in `Option`: a hand-written reader
`match f e with | none => none | some a => (rest).map (a :: ·)` is this
`Option.bind`. -/
theorem optionMapM_cons {α β : Type _} (f : α → Option β) (e : α) (es : List α) :
    (e :: es).mapM f = (f e).bind (fun a => (es.mapM f).map (a :: ·)) := by
  cases h : f e <;> cases h2 : es.mapM f <;> simp [List.mapM_cons, h, h2]

theorem optionMapM_nil {α β : Type _} (f : α → Option β) :
    ([] : List α).mapM f = some [] := rfl

end L4Factoidal.ListTR
