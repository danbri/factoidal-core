import L4Factoidal.Paralliverse.ProgramCPU

/-!
# GpuDomainSpecificLanguage (GSSL)

The existing typed Paralliverse program is the starting point for GSSL's
workload-independent composition layer. This module does not yet define a
complete GPU kernel language, a parser, or a verified WGSL compiler.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage

open L4Factoidal.Paralliverse

variable {Atom : Type} {sig : Signature Atom} {a b : Shape Atom}

/-- If two interpretations agree on every primitive, their meanings agree
for every well-typed composed program. The same general result can be reused
by independently defined domain languages after they lower to `Program`.

The premise is an obligation on the primitive implementations; this theorem
does not verify a parser, generated WGSL, a driver, or device execution. -/
theorem eval_eq_of_primitive_agreement
    (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (p : Program sig a b) :
    Program.eval base implementation p = Program.eval base reference p := by
  calc
    Program.eval base implementation p = Program.runCPU base implementation 1 p := by
      symm
      exact Program.runCPU_eq_eval base implementation implementation (by intros; rfl) 1 p
    _ = Program.eval base reference p :=
      Program.runCPU_eq_eval base reference implementation agree 1 p

#print axioms eval_eq_of_primitive_agreement

end L4Factoidal.GpuDomainSpecificLanguage
