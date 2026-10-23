/-
  Harness/WorkerPoolBench.lean — start latency of a short job on the Lean task
  pool (`IO.asTask`, default priority) and on `Harness.WorkerPool` (issue
  https://github.com/danbri/factoidal/issues/961, stage 1g of
  docs/designissues/2026-10-12-parallel-block-scans.md).

  Usage: l4pool-bench [rounds] [gapUs] [jobs]
  Each round: the caller works (polls the clock) for `gapUs` microseconds, the
  time a query spends between two divided phases, then starts `jobs` jobs
  that each record the time they begin, and waits for all of them. Printed
  per mode: the median and 90th percentile of the latest job start after
  the post, and of the time until the caller has every result, in
  microseconds.
-/
import Harness.WorkerPool

open Harness.WorkerPool

def busyUntil (t : Nat) : IO Unit := do
  for _ in [0:100000000] do
    if (← IO.monoNanosNow) ≥ t then return

def pct (xs : Array Nat) (q : Nat) : Nat :=
  let s := xs.qsort (· < ·)
  if s.size == 0 then 0 else s[min (s.size - 1) (s.size * q / 100)]!

def report (name : String) (starts dones : Array Nat) : IO Unit :=
  IO.println s!"{name}: start p50 {pct starts 50 / 1000} us p90 {pct starts 90 / 1000} us; \
    all done p50 {pct dones 50 / 1000} us p90 {pct dones 90 / 1000} us"

/-- The Lean task pool: one `IO.asTask` per job. -/
def roundTasks (jobs : Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut ts := #[]
  for _ in [0:jobs] do
    ts := ts.push (← IO.asTask (IO.monoNanosNow))
  let mut latest := 0
  for t in ts do
    match ← IO.wait t with
    | .ok s => latest := max latest (s - t0)
    | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  return (latest, t1 - t0)

/-- The worker pool: `jobs` jobs on the workers (`runAll` with a no-op job 0
    on the caller). -/
def roundPool (p : Pool) (jobs : Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let js : Array (IO Nat) := #[(pure t0 : IO Nat)] ++ (Array.replicate jobs (IO.monoNanosNow : IO Nat))
  let rs ← p.runAll js
  let t1 ← IO.monoNanosNow
  let mut latest := 0
  for r in rs.extract 1 rs.size do
    match r with
    | .ok s => latest := max latest (s - t0)
    | .error _ => pure ()
  return (latest, t1 - t0)

def runMode (name : String) (rounds gapUs : Nat) (step : IO (Nat × Nat)) : IO Unit := do
  let mut starts := #[]
  let mut dones := #[]
  for _ in [0:rounds] do
    busyUntil ((← IO.monoNanosNow) + gapUs * 1000)
    let (s, d) ← step
    starts := starts.push s
    dones := dones.push d
  report name starts dones

def main (args : List String) : IO UInt32 := do
  let rounds := (args[0]? >>= String.toNat?).getD 2000
  let gapUs := (args[1]? >>= String.toNat?).getD 200
  let jobs := (args[2]? >>= String.toNat?).getD 3
  IO.println s!"rounds {rounds}, gap {gapUs} us, jobs {jobs}"
  runMode "lean task pool (IO.asTask)" rounds gapUs (roundTasks jobs)
  let spinning ← start jobs 1000000
  runMode "worker pool, poll 1 ms" rounds gapUs (roundPool spinning jobs)
  spinning.shutdown
  let parking ← start jobs 0
  runMode "worker pool, poll 0 (park at once)" rounds gapUs (roundPool parking jobs)
  parking.shutdown
  return 0
