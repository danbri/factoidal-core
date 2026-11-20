import L4Factoidal.Par.Chunked
import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Paralliverse.Program

namespace L4Factoidal.Paralliverse.Program

variable {Atom : Type} {sig : Signature Atom} {a b : Shape Atom}

/-- CPU interpretation using the existing task-based array mapper at each list map. -/
def runCPU (base : Atom → Type) (ops : PrimitiveEval base sig) (workers : Nat)
    {a b : Shape Atom} : Program sig a b → Shape.Value base a → Shape.Value base b
  | .identity, x => x
  | .prim op, x => ops op x
  | .seq f g, x => runCPU base ops workers g (runCPU base ops workers f x)
  | .prod f g, x => (runCPU base ops workers f x.1, runCPU base ops workers g x.2)
  | .fanout f g, x => (runCPU base ops workers f x, runCPU base ops workers g x)
  | .map f, xs => (Par.mapChunks workers (runCPU base ops workers f) xs.toArray).toList

/-- Kind: compositional CPU refinement.
Says: agreement on primitive results extends to every well-typed CPU program.
Each map uses the actual CPU task mapper, for every worker count and every input.
Does not say: how the host schedules tasks or whether parallel evaluation is faster. -/
theorem runCPU_eq_eval (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (workers : Nat) (p : Program sig a b) :
    runCPU base implementation workers p = eval base reference p := by
  induction p with
  | identity => rfl
  | prim op => funext x; exact agree op x
  | seq f g hf hg =>
    funext x
    simp only [runCPU, eval, hf, hg]
  | prod f g hf hg =>
    funext x
    simp only [runCPU, eval, hf, hg]
    rfl
  | fanout f g hf hg =>
    funext x
    simp only [runCPU, eval, hf, hg]
    rfl
  | map f hf =>
    funext xs
    simp only [runCPU, eval, Par.mapChunks_eq, Array.toList_map, hf]
    rfl

/-- Kind: compiler-pass and backend refinement.
Says: running the fused syntax on the task-based CPU interpreter gives the original
source program's sequential meaning under the primitive agreement.
Does not say: that a C or device compiler implements different backend operations. -/
theorem runCPU_fuseMaps_eq_eval (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (workers : Nat) (p : Program sig a b) :
    runCPU base implementation workers (fuseMaps p) = eval base reference p :=
  (runCPU_eq_eval base reference implementation agree workers (fuseMaps p)).trans
    (eval_fuseMaps base reference p)

/-- Kind: ordered task result refinement.
Says: collecting any delivery permutation of the indexed, task-computed map results
returns exactly the reference map's values in input order.
Does not say: that a host assigned a reply to the right job or authenticated it. -/
theorem collect_mapCPU_eq_eval (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (workers : Nat) (p : Program sig a b) (xs : List (Shape.Value base a))
    (replies : List (Nat × Shape.Value base b))
    (hdelivered : replies.Perm ((List.range xs.length).zip
      (Par.mapChunks workers (runCPU base implementation workers p) xs.toArray).toList)) :
    Ordered.collect? xs.length replies = some (eval base reference (.map p) xs) := by
  apply (Ordered.collect?_eq_some_iff _ _ _).2
  refine ⟨List.length_map _, ?_⟩
  simpa only [Par.mapChunks_eq, Array.toList_map, List.toList_toArray,
    runCPU_eq_eval base reference implementation agree workers p, eval] using hdelivered

#print axioms runCPU_eq_eval
#print axioms runCPU_fuseMaps_eq_eval
#print axioms collect_mapCPU_eq_eval

end L4Factoidal.Paralliverse.Program
