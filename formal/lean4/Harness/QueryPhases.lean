/-
Harness.QueryPhases — `l4query-phases`: the phases of `l4factoidal query`,
one at a time, with the resident memory after each.

    l4query-phases FILE [--format F] [--query-string Q] [--stop-after PHASE]

PHASE is one of `read`, `parse`, `normalize`, `index`, `eval`, `output`
(default `output`). The program runs the same functions, in the same order,
as `queryCmd` in `Wasm/Cli.lean` (`readInput`, `Ops.parseTextToDataset`,
`Ops.queryDatasetOf`, whose body is `datasetForOps`, `indexedDatasetBackend`
and `queryParsedDatasetWith`), and after each phase prints one line

    phase=NAME value=V rss_kb=R hwm_kb=H

where V is a number computed from the phase's result (so that the phase is
evaluated before the line is printed), R is `VmRSS` and H is `VmHWM` of
`/proc/self/status` (Linux only; 0 elsewhere). Run it once per PHASE under
`/usr/bin/time -v` to get the peak resident set of a process that stops after
that phase (https://github.com/danbri/factoidal/issues/729,
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md` §10).

The memory figures are of the process, not of one data structure: the
allocator keeps freed pages, so `rss_kb` after a phase includes memory a
finished phase released. `hwm_kb` is the peak so far.
-/
import Wasm.Ops.Parse
import Wasm.Ops.Query
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.QueryPhases

open L4Factoidal.RDF
open L4Factoidal.SPARQL.StoreDataset

/-- The value in kB of `key` (`VmRSS`, `VmHWM`) in `/proc/self/status`;
0 when the file or the key is absent. -/
def procStatusKb (key : String) : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let line? := (s.splitOn "\n").find? (fun l => l.startsWith (key ++ ":"))
    match line? with
    | none => pure 0
    | some l =>
        let digits := (l.drop (key.length + 1)).trim.takeWhile Char.isDigit
        pure digits.toNat!
  catch _ => pure 0

def report (phase : String) (value : Nat) : IO Unit := do
  let rss ← procStatusKb "VmRSS"
  let hwm ← procStatusKb "VmHWM"
  IO.println s!"phase={phase} value={value} rss_kb={rss} hwm_kb={hwm}"

def phases : List String := ["read", "chars", "parse", "normalize", "index", "eval", "output"]

def flagValue (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4query-phases FILE [--format F] [--query-string Q] [--stop-after PHASE]"
      pure 2
  | file :: rest =>
    let format := (flagValue rest "--format").getD "turtle"
    let sparql := (flagValue rest "--query-string").getD
      "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }"
    let stop := (flagValue rest "--stop-after").getD "output"
    unless phases.contains stop do
      IO.eprintln s!"l4query-phases: unknown phase '{stop}' ({String.intercalate " | " phases})"
      return 2
    report "start" 0
    let text ← IO.FS.readFile file
    report "read" text.utf8ByteSize
    if stop == "read" then return 0
    if stop == "chars" then
      report "chars" text.toList.length
      return 0
    match L4Wasm.Ops.parseTextToDataset text format "" with
    | .error e => IO.eprintln e; pure 1
    | .ok ds =>
      report "parse" (L4Wasm.Ops.datasetQuadCount ds)
      if stop == "parse" then return 0
      match datasetForOps .rdf12 ds with
      | .error _ => IO.eprintln "normalize: parse error"; pure 1
      | .ok nds =>
        report "normalize" (L4Wasm.Ops.datasetQuadCount nds)
        if stop == "normalize" then return 0
        -- `--no-index` (diagnostic): the reference evaluator, no backend.
        let dsb := indexedDatasetBackend nds
        if rest.contains "--no-index" then
          let out := L4Wasm.Ops.queryParsedDatasetWith nds none sparql
          report "eval-no-index" out.utf8ByteSize
          return 0
        report "index" (match dsb.default with
          | .indexed ix => ix.all.size
          | _ => 0)
        if stop == "index" then return 0
        let out := L4Wasm.Ops.queryParsedDatasetWith nds (some dsb) sparql
        report "eval" out.utf8ByteSize
        if stop == "eval" then return 0
        IO.println out
        report "output" out.utf8ByteSize
        pure 0

end Harness.QueryPhases

def main (args : List String) : IO UInt32 := Harness.QueryPhases.main args
