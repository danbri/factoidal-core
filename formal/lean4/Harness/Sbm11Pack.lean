/-
Harness/Sbm11Pack — `l4sbm11-pack`, the SBM11 packer
(https://github.com/danbri/factoidal/issues/789). The code is in
`Harness/Sbm11PackLib.lean`; compaction (`l4sbm11 compact`, stage 5) runs its
phases 2 and 3.
-/
import Harness.Sbm11PackLib

open Sbm11Pack in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | src :: dir :: opts =>
      match parseOpts opts {} with
      | some o =>
        if o.phase2Only then runPhase2Only src dir o.workers o.runTerms o.source
        else runPack src dir o.workers o.runTerms o.blockRows o.sortRows o.source
      | none => IO.eprintln usage; pure 2
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11-pack: {e}"
    pure 1
