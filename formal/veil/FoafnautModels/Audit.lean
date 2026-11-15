import FoafnautModels.FramePipeline
import FoafnautModels.GpuProtocol
import FoafnautModels.HttpConnections
import FoafnautModels.Glue

/-!
# Axiom audit of the models' theorems

Lists every theorem declared under the models' namespaces (the verification conditions that
`#gen_theorems` added after `#check_invariants`, and any written by hand) with the axioms its
proof uses. CI fails when a line names an axiom other than `propext`, `Classical.choice` and
`Quot.sound` (for instance `sorryAx`, which an SMT answer trusted without a reconstructed proof
would show), and when no line is printed at all.
-/

open Lean Elab Command

def auditPrefixes : List Name := [`FramePipeline, `GpuProtocol, `HttpConnections, `PageLoops]

elab "#audit_models" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if auditPrefixes.any (·.isPrefixOf n) && !n.isInternal then
        names := names.push n
  names := names.qsort (·.toString < ·.toString)
  for n in names do
    let axs ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"audit {n} axioms: {axs.toList}"
  logInfo m!"audit total {names.size} theorems"

#audit_models
