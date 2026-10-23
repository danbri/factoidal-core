/-
  Harness/WorkerPool.lean — a per-session worker pool for the SBM11 query
  harness (OKR batch 3 KR 1.2, issue https://github.com/danbri/factoidal/issues/961).

  The Lean task pool starts its workers lazily and parks an idle worker on a
  condition variable. On the 4-vCPU test VM a parked thread runs 50 to 120
  microseconds after it is woken (stage 1f of
  docs/designissues/2026-10-12-parallel-block-scans.md), so a query phase of
  less than about 0.5 ms does not gain from `Task.spawn`.

  This pool has `n` threads of its own (`Task.Priority.dedicated`: each gets
  a new thread, outside the Lean pool's worker limit, and no other task is
  queued on it). Jobs go to a worker, and results come back, through a
  `Cell`: an `IO.Ref` that the reader polls for at most `spinNs` nanoseconds
  before it blocks on a promise. Each cell has one reader, so the polled
  cache line moves only when the writer writes it. A promise is resolved only
  for a reader that blocked: `IO.Promise.resolve` and `IO.wait` take the Lean
  task manager's lock, which every thread shares (a first version that
  passed every job through a promise: 3 jobs started 24 microseconds after
  the post at the median, against 4 with cells; `l4pool-bench`).

  Lost wake-up: a reader that blocks stores its promise in `waiter` and then
  reads the value once more; a writer writes the value and then takes the
  promise out of `waiter`. `IO.Ref.set`, `swap` and `modify` on a ref that
  two threads reach are atomic exchanges in the runtime, so either the reader
  sees the value or the writer finds the promise and resolves it.

  The jobs are `IO Unit` closures. A job and what it captures become shared
  between threads (reference counts are atomic from then on): give a job the
  inputs that it reads, not a structure that the caller keeps changing
  (skill `lean4-performance`, "Comparisons over values that tasks share").
-/

namespace Harness.WorkerPool

/-! ## Cells -/

/-- A value that one thread writes and one other thread takes. -/
structure Cell (α : Type) where
  val : IO.Ref (Option α)
  waiter : IO.Ref (Option (IO.Promise Unit))

def Cell.new {α : Type} : IO (Cell α) :=
  return { val := ← IO.mkRef none, waiter := ← IO.mkRef none }

/-- Resolve the promise of a blocked reader, if there is one. -/
def Cell.notify {α : Type} (c : Cell α) : IO Unit := do
  if let some p ← c.waiter.swap none then p.resolve ()

/-- Write the value. -/
def Cell.put {α : Type} (c : Cell α) (a : α) : IO Unit := do
  c.val.set (some a)
  c.notify

/-- Poll the cell for at most `spinNs` nanoseconds (the clock is read every
    32 polls); `none` when it is still empty. -/
def Cell.poll {α : Type} (c : Cell α) (spinNs : Nat) : IO (Option α) := do
  let deadline := (← IO.monoNanosNow) + spinNs
  for _ in [0:1000000000] do
    for _ in [0:32] do
      if let some a ← c.val.swap none then return some a
    if (← IO.monoNanosNow) ≥ deadline then return (← c.val.swap none)
  c.val.swap none

/-- Take the value: poll for at most `spinNs` nanoseconds, then block until a
    writer (or `Cell.notify`) resolves the reader's promise. `none` when the
    reader was woken by `notify` with no value. -/
def Cell.take? {α : Type} (c : Cell α) (spinNs : Nat) : IO (Option α) := do
  if let some a ← c.poll spinNs then return some a
  let p : IO.Promise Unit ← IO.Promise.new
  c.waiter.set (some p)
  if let some a ← c.val.swap none then
    let _ ← c.waiter.swap none
    return some a
  let _ ← IO.wait p.result?
  c.val.swap none

/-- Take the value, blocking as often as needed. -/
partial def Cell.take {α : Type} (c : Cell α) (spinNs : Nat) : IO α := do
  match ← c.take? spinNs with
  | some a => return a
  | none => c.take spinNs

/-! ## The pool -/

/-- One pool thread: its mailbox (jobs, newest first) and its stop flag. -/
structure Worker where
  mail : Cell (List (IO Unit))
  stop : IO.Ref Bool

/-- A pool of `workers.size` threads (`Task.Priority.dedicated`). -/
structure Pool where
  workers : Array Worker
  threads : Array (Task (Except IO.Error Unit))
  spinNs : Nat

/-- The loop of one worker thread: run the jobs of the mailbox in the order
    they were posted; an error that escapes a job is dropped, so the worker
    stays up (`spawnOn` gives each job a cell for its own result). -/
partial def workerLoop (w : Worker) (spinNs : Nat) : IO Unit := do
  if ← w.stop.get then return
  if let some js ← w.mail.take? spinNs then
    js.reverse.forM fun j => do let _ ← j.toBaseIO
  workerLoop w spinNs

/-- Start `n` worker threads that poll for `spinNs` nanoseconds before they
    block. -/
def start (n : Nat) (spinNs : Nat := 1000000) : IO Pool := do
  let mut ws := #[]
  let mut ts := #[]
  for _ in [0:n] do
    let w : Worker := { mail := ← Cell.new, stop := ← IO.mkRef false }
    let t ← IO.asTask (workerLoop w spinNs) Task.Priority.dedicated
    ws := ws.push w
    ts := ts.push t
  return { workers := ws, threads := ts, spinNs }

def Pool.size (p : Pool) : Nat := p.workers.size

/-- Give `job` to worker `i mod size` (nothing happens on an empty pool). -/
def Pool.postTo (p : Pool) (i : Nat) (job : IO Unit) : IO Unit := do
  if h : 0 < p.workers.size then
    let c := (p.workers[i % p.workers.size]'(Nat.mod_lt _ h)).mail
    -- `swap` then `put`, not `IO.Ref.modify`: see `Cell.put`
    let old ← c.val.swap none
    c.put (job :: old.getD [])

/-- Make every blocked worker poll again (call when a query starts). -/
def Pool.wake (p : Pool) : IO Unit :=
  p.workers.forM fun w => w.mail.notify

/-- Stop the workers and wait for their threads to end. -/
def Pool.shutdown (p : Pool) : IO Unit := do
  for w in p.workers do
    w.stop.set true
    -- a value, not only `notify`: a worker that is between its last poll and
    -- its wait has not published its promise yet, and would block for good
    let old ← w.mail.val.swap none
    w.mail.put (old.getD [])
  for t in p.threads do
    let _ ← IO.wait t

/-! ## Jobs with results -/

/-- A result to wait for: a cell that a pool job writes, or a task of the
    Lean pool. -/
inductive Handle (α : Type) where
  | cell (c : Cell α)
  | task (t : Task α)

/-- Run `act` on worker `i mod size`; its result (or its error) goes to the
    handle's cell. -/
def Pool.spawnOn {α : Type} (p : Pool) (i : Nat) (act : IO α) : IO (Handle (Except IO.Error α)) := do
  let c ← Cell.new
  p.postTo i (do c.put (← act.toBaseIO))
  return .cell c

/-- Wait for a handle: a cell is polled for at most `spinNs` nanoseconds,
    then the thread blocks. -/
def Handle.await {α : Type} (h : Handle α) (spinNs : Nat) : IO α :=
  match h with
  | .cell c => c.take spinNs
  | .task t => IO.wait t

/-- Run `jobs[0]` on the calling thread and `jobs[i]` for `i ≥ 1` on worker
    `i - 1` (mod the pool size), and return the results in job order. With
    an empty pool every job runs on the caller. An error of a job is returned
    in its slot. -/
def Pool.runAll {α : Type} (p : Pool) (jobs : Array (IO α)) : IO (Array (Except IO.Error α)) := do
  if p.size == 0 || jobs.size ≤ 1 then
    return ← jobs.mapM fun j => j.toBaseIO
  let mut hs : Array (Handle (Except IO.Error α)) := #[]
  for i in [1:jobs.size] do
    hs := hs.push (← p.spawnOn (i - 1) jobs[i]!)
  let r0 ← jobs[0]!.toBaseIO
  let mut out := #[r0]
  for h in hs do
    out := out.push (← h.await p.spinNs)
  return out

end Harness.WorkerPool
