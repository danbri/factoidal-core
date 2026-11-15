/-
The Lean reference of the tile-binning compute kernel (L4Factoidal.GpuKernel.Gather), for the
differential test gpu_kernel_diff.ts: it prints the kernel's WGSL and the output buffer the
Lean meaning gives (the sequential loop `runSeq` of `Gather.dispatch`, which
`Gather.gpu_eq_seq` says every GPU order equals), so the test can compare it with the GPU's.

  GpuKernelRef IN OUT_WORDS OUT_WGSL

IN: whitespace-separated words: size cap maxItems cells items across, then 4 words a box.
OUT_WORDS: the cells * (cap + 1) output words, one per line.
-/
import L4Factoidal.GpuKernel.Gather
open L4Factoidal.GpuKernel

def main (args : List String) : IO UInt32 := do
  match args with
  | [inPath, outPath, wgslPath] =>
    let text := (← IO.FS.readFile inPath).map (fun c => if c.isWhitespace then ' ' else c)
    let words := (text.splitOn " ").filter (· ≠ "") |>.map String.toNat!
    match words with
    | size :: cap :: maxItems :: cells :: items :: across :: rest =>
      let boxes := rest.toArray
      let g := bin size cap maxItems
      let params : Fin 4 → Nat := fun i => [cells, items, across, 0][i]!
      let input : Nat → Nat := fun i => boxes.getD i 0
      let mut out : Array Nat := Array.replicate (cells * (cap + 1)) 0
      for t in [0:cells] do
        for w in g.writes params input t do
          out := out.set! w.1 w.2
      IO.FS.writeFile outPath (String.intercalate "\n" (out.toList.map toString) ++ "\n")
      IO.FS.writeFile wgslPath g.wgsl
      return 0
    | _ => IO.eprintln "input: size cap maxItems cells items across boxes..."; return 2
  | _ => IO.eprintln "usage: GpuKernelRef IN OUT_WORDS OUT_WGSL"; return 2
