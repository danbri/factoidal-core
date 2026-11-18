import L4Factoidal.CompactLTJ.Model

/-!
SPDX-License-Identifier: Apache-2.0
Independent adaptive variable-at-a-time BGP reference.

At each level choose the not-yet-bound variable with the smallest
intersection of its incident triple-pattern domains. This resembles
adaptive variable ordering from the LTJ literature but does not copy
any GPL implementation.

The fuel parameter bounds recursion explicitly; the reference
candidate-domain computation is list-based. This is a correctness
model, not yet a high-performance WCOJ executor.
-/
namespace L4Factoidal.CompactLTJ

def chooseVariable (db : List Triple) (ps : List Atom)
    (vars : List Variable) (env : Binding) : Option Variable :=
  match vars with
  | [] => none
  | v :: rest =>
      some (rest.foldl (fun best w =>
        if (candidateDomain db ps w env).length <
           (candidateDomain db ps best env).length
        then w else best) v)

theorem chooseVariable_nil (db : List Triple)
    (ps : List Atom) (env : Binding) :
    chooseVariable db ps [] env = none := rfl

theorem chooseVariable_singleton (db : List Triple)
    (ps : List Atom) (v : Variable) (env : Binding) :
    chooseVariable db ps [v] env = some v := rfl

/-- A domain-first adaptive search. One variable disappears per recursive
level; the explicit fuel bounds evaluation even on malformed inputs.
The caller should supply at least variables.length + 1 fuel units. -/
def solveAdaptive (db : List Triple) (ps : List Atom) :
    Nat → List Variable → Binding → List Binding
  | 0, _, _ => []
  | _ + 1, [], b => if satisfies db ps b then [b] else []
  | fuel + 1, v :: vs, b =>
      let chosen := (chooseVariable db ps (v :: vs) b).getD v
      let remaining := (v :: vs).filter (fun w => w != chosen)
      (candidateDomain db ps chosen b).flatMap
        (fun x => solveAdaptive db ps fuel remaining ((chosen,x) :: b))

theorem solveAdaptive_zero (db : List Triple) (ps : List Atom)
    (vs : List Variable) (b : Binding) :
    solveAdaptive db ps 0 vs b = [] := rfl

theorem solveAdaptive_empty_variables (db : List Triple)
    (ps : List Atom) (fuel : Nat) (b : Binding) :
    solveAdaptive db ps (fuel+1) [] b =
      (if satisfies db ps b then [b] else []) := rfl

theorem solveAdaptive_sound (db : List Triple) (ps : List Atom)
    (fuel : Nat) (vs : List Variable)
    (initial result : Binding)
    (h : result ∈ solveAdaptive db ps fuel vs initial) :
    satisfies db ps result = true := by
  induction fuel generalizing vs initial with
  | zero =>
      simp [solveAdaptive] at h
  | succ n ih =>
      cases vs with
      | nil =>
          cases hs : satisfies db ps initial with
          | true =>
              simp [solveAdaptive, hs] at h
              subst result
              exact hs
          | false =>
              simp [solveAdaptive, hs] at h
      | cons v rest =>
          simp only [solveAdaptive] at h
          rcases List.mem_flatMap.mp h with ⟨x, _, hx⟩
          exact ih _ _ hx

private def tiny : List Triple :=
  [⟨1,9,2⟩, ⟨1,9,3⟩, ⟨2,9,3⟩]

private def outgoing : Atom :=
  ⟨.fixed 1, .fixed 9, .variable 0⟩

#guard chooseVariable tiny [outgoing] [0] [] == some 0
#guard (solveAdaptive tiny [outgoing] 2 [0] []).length == 2
#guard solveAdaptive tiny [] 1 [] [] == [[]]
#guard solveAdaptive tiny [] 0 [] [] == []

end L4Factoidal.CompactLTJ
