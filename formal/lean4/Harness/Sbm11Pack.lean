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
      let p2 := opts.contains "--phase2-only"
      match parseOpts (opts.filter (· != "--phase2-only")) (4, 262144, 4096, 524288) with
      | some (k, n, b, m) => if p2 then runPhase2Only src dir k n else runPack src dir k n b m
      | none => IO.eprintln usage; pure 2
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11-pack: {e}"
    pure 1
