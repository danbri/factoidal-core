import Lake
open Lake DSL

/-!
System-level transition-system models of Foafnaut, written with Veil
(https://github.com/verse-lab/veil, Apache-2.0).

This package is separate from `formal/lean4` on purpose: the engine library does not import it
and builds without it (engine toolchain v4.33.1, no Lake requires). Veil pins its own toolchain
(v4.35.0) and dependencies (lean-smt, lean-auto, lean-cvc5, Loom, Lentil, Lasso, VerifiedHAMT,
batteries, aesop, ProofWidgets; all Apache-2.0; no Mathlib). lean-cvc5 downloads a static cvc5
1.3.2 library (cvc5: BSD-3-Clause; linked with CaDiCaL, MIT, and GMP, LGPL-3.0-or-later or
GPL-2.0-or-later) that the proof tactics call while this package builds. Nothing from this
package is linked into the browser.

Trust: every model sets `veil.smt.trust false`, so an SMT `unsat` answer counts only when
lean-smt reconstructs a kernel-checked proof; `#model_check` results are test evidence (compiled
or interpreted enumeration of a finite instance), not proofs. `#gen_theorems` adds each discharged
verification condition as a theorem, and `FoafnautModels/Audit.lean` prints the axioms of every
theorem in the models' namespaces; CI accepts only `propext`, `Classical.choice`, `Quot.sound`.
-/

package foafnautModels

require veil from git "https://github.com/verse-lab/veil.git" @ "317b2a995170521ddc561ed9f64289c5d545be45"

/-- Engine modules the models use as components, compiled here from the engine's own sources
(`formal/lean4`) with this package's toolchain. Only modules with no Lake requires and no
externs are listed. The engine's build does not change: this is a second compilation of the
same files, by Lean v4.35.0 instead of v4.33.1. -/
lean_lib EngineComponents where
  srcDir := "../lean4"
  roots := #[]
  globs := #[.andSubmodules `L4Factoidal.EventLoop]

@[default_target]
lean_lib FoafnautModels
