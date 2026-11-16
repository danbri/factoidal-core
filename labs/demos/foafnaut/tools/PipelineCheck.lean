/-
The host pipeline trace checker (L4Factoidal.HostPipeline.Model), for pipeline_trace_check.ts:
it reads a trace `run_html.ts --pipe-trace` wrote (one event a line: pump, submit, ask,
answer) and prints the violations of the rule (`check`), or `ok` with counts. By
`check_nil_sound` and `check_nil_prefix`, an accepted trace is a run of the model at every
event: at most BOUND frames in flight and at most one blocking GPU wait between two pumps.

  lean --run PipelineCheck.lean BOUND TRACE
-/
import L4Factoidal.HostPipeline.Model
open L4Factoidal.HostPipeline

def main (args : List String) : IO UInt32 := do
  match args with
  | [bound, path] =>
    let lines := (← IO.FS.readFile path).splitOn "\n"
    let events := lines.filterMap parseObs
    if events.length > maxEvents then
      IO.println s!"refused: {events.length} events, more than {maxEvents}"; return 2
    let c : Config := ⟨bound.toNat!⟩
    let count (o : Obs) := events.foldl (fun n e => if e == o then n + 1 else n) 0
    match check c events with
    | [] =>
      IO.println s!"ok: {events.length} events, {count .pump} pumps, {count .submit} submits, {count .askBegin} blocking waits; bound {c.bound}"
      return 0
    | vs =>
      IO.println s!"violations: {repr vs}"
      return 1
  | _ => IO.eprintln "usage: PipelineCheck BOUND TRACE"; return 2
