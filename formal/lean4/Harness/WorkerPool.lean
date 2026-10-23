/-
  Harness/WorkerPool.lean — a per-session worker pool for the SBM11 query
  harness (OKR batch 3 KR 1.2, issue https://github.com/danbri/factoidal/issues/961).

  The Lean task pool starts its workers lazily and parks an idle worker on a
  condition variable. On the 4-vCPU test VM a parked thread runs 50 to 120
  microseconds after it is woken (stage 1f of
  docs/designissues/2026-10-12-parallel-block-scans.md), so a query phase of
  less than about 0.5 ms does not gain from `Task.spawn`.

  This pool has `n` threads of its own (`Task.Priority.dedicated`: each task
  gets a new thread, the Lean pool's worker limit does not apply, and no other
  task can be queued on that thread). A worker that has no job polls its
  mailbox (an `IO.Ref`, whose `swap` is an atomic exchange) for at most
  `spinNs` nanoseconds, then parks on an `IO.Promise` that the next `post`
  resolves. So a job posted while the worker polls starts without a kernel
  wake-up. `wake` makes every parked worker poll again: a query calls it when
  it starts, so the workers poll through the serial work before its first
  divided phase.

  Lost wake-up: a worker stores its promise in `parked` and then reads the
  mailbox once more before it waits; `post` writes the mailbox and then takes
  the promise out of `parked`. Both are atomic exchanges on the two refs (the
  runtime's `lean_st_ref_swap` on a shared ref), so either the worker reads
  the new job or `post` finds the promise and resolves it.

  The jobs are `IO Unit` closures. A job and what it captures become shared
  between threads (reference counts are atomic from then on): give a job the
  inputs that it reads, not a structure that the caller keeps changing
  (skill `lean4-performance`, "Comparisons over values that tasks share").
-/

namespace Harness.WorkerPool

/-- One pool thread: its mailbox (jobs in the order posted, newest first),
    the promise it waits on when parked, and its stop flag. -/
structure Worker where
  mail : IO.Ref (List (IO Unit))
  parked : IO.Ref (Option (IO.Promise Unit))
  stop : IO.Ref Bool

/-- A pool of `workers.size` threads (`Task.Priority.dedicated`). -/
structure Pool where
  workers : Array Worker
  threads : Array (Task (Except IO.Error Unit))
  spinNs : Nat
  /-- The next worker that `post` gives a job to (round robin). -/
  next : IO.Ref Nat

/-- Run the jobs of a mailbox in the order they were posted. A job's own
    errors are its business (`runJobs` gives each job a promise of its
    result); an error that escapes is dropped so the worker stays up. -/
private def runMail (js : List (IO Unit)) : IO Unit :=
  js.reverse.forM fun j => do let _ ← j.toBaseIO

/-- The loop of one worker thread. -/
partial def workerLoop (w : Worker) (spinNs : Nat) : IO Unit := do
  let rec poll (deadline : Nat) : IO Unit := do
    if ← w.stop.get then return
    let js ← w.mail.swap []
    if !js.isEmpty then
      runMail js
      poll ((← IO.monoNanosNow) + spinNs)
    else if (← IO.monoNanosNow) < deadline then
      poll deadline
    else
      -- park: publish the promise, then read the mailbox once more
      let p ← IO.Promise.new
      w.parked.set (some p)
      let js ← w.mail.swap []
      if !js.isEmpty then
        let _ ← w.parked.swap none
        runMail js
      else if ← w.stop.get then
        return
      else
        let _ ← IO.wait p.result?
      poll ((← IO.monoNanosNow) + spinNs)
  poll ((← IO.monoNanosNow) + spinNs)

/-- Start `n` worker threads that poll for `spinNs` nanoseconds before they
    park. -/
def start (n : Nat) (spinNs : Nat := 1000000) : IO Pool := do
  let mut ws := #[]
  let mut ts := #[]
  for _ in [0:n] do
    let w : Worker := { mail := ← IO.mkRef [], parked := ← IO.mkRef none, stop := ← IO.mkRef false }
    let t ← IO.asTask (workerLoop w spinNs) Task.Priority.dedicated
    ws := ws.push w
    ts := ts.push t
  return { workers := ws, threads := ts, spinNs, next := ← IO.mkRef 0 }

def Pool.size (p : Pool) : Nat := p.workers.size

/-- Resolve a parked worker's promise, if it has one. -/
private def unpark (w : Worker) : IO Unit := do
  if let some pr ← w.parked.swap none then pr.resolve ()

/-- Give `job` to worker `i mod size`. -/
def Pool.postTo (p : Pool) (i : Nat) (job : IO Unit) : IO Unit := do
  if h : 0 < p.workers.size then
    let w := p.workers[i % p.workers.size]'(Nat.mod_lt _ h)
    w.mail.modify (job :: ·)
    unpark w

/-- Give `job` to the next worker (round robin). -/
def Pool.post (p : Pool) (job : IO Unit) : IO Unit := do
  let i ← p.next.modifyGet fun i => (i, i + 1)
  p.postTo i job

/-- Make every parked worker poll again (call when a query starts). -/
def Pool.wake (p : Pool) : IO Unit :=
  p.workers.forM unpark

/-- Stop the workers and wait for their threads to end. -/
def Pool.shutdown (p : Pool) : IO Unit := do
  for w in p.workers do
    w.stop.set true
    unpark w
  for t in p.threads do
    let _ ← IO.wait t

/-- Wait for `t`: poll `IO.hasFinished` for at most `spinNs` nanoseconds,
    then block. The caller does not park while a short job ends. -/
def awaitSpin (t : Task α) (spinNs : Nat) : IO α := do
  let deadline := (← IO.monoNanosNow) + spinNs
  let rec go (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      if ← IO.hasFinished t then pure ()
      else if (← IO.monoNanosNow) < deadline then go fuel
      else pure ()
  go 100000000
  return t.get

/-- Run `jobs[0]` on the calling thread and `jobs[1..]` on the pool, one per
    worker in order (`jobs[i]` on worker `i - 1 mod size`), and return the
    results in job order. With an empty pool every job runs on the caller.
    An error of a job is returned in its slot. -/
def Pool.runAll (p : Pool) (jobs : Array (IO α)) : IO (Array (Except IO.Error α)) := do
  if p.size == 0 || jobs.size ≤ 1 then
    return ← jobs.mapM fun j => j.toBaseIO
  let mut proms : Array (IO.Promise (Except IO.Error α)) := #[]
  for i in [1:jobs.size] do
    let pr ← IO.Promise.new
    let j := jobs[i]!
    p.postTo (i - 1) (do pr.resolve (← j.toBaseIO))
    proms := proms.push pr
  let r0 ← jobs[0]!.toBaseIO
  let mut out := #[r0]
  for pr in proms do
    match ← awaitSpin pr.result? p.spinNs with
    | some r => out := out.push r
    | none => out := out.push (.error (IO.userError "worker pool: a job was dropped"))
  return out

end Harness.WorkerPool
