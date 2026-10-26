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
  promise out of `waiter`. `IO.Ref.set` and `swap` on a ref that two threads
  reach are each one atomic exchange in the runtime, so either the reader
  sees the value or the writer finds the promise and resolves it.

  Two families of ref operations (Lean 4.33.1 runtime, `lean_st_ref_*`, read
  from the disassembly; issue https://github.com/danbri/factoidal/issues/981):
  `set` and `swap` are one exchange each. `get`, `take`, and `modify` and
  `modifyGet` (a `take`, then a `set`) first exchange the value for null,
  spin while they find null, and put a value back with a second exchange. A
  `set` or `swap` by another thread between the two exchanges is lost: `get`
  puts the old value back and frees the new one, `modify` overwrites it, and
  a `swap` that finds null returns its own argument. So every ref of this
  file that two threads reach uses one family only: the cells `set` and
  `swap`, the stop flag `get` and `modify`. Before issue 981 the stop flag
  was read with `get` and written with `set`: a worker that read the flag
  at the moment `shutdown` wrote it kept `false`, blocked on its mailbox, and
  `shutdown` waited for its thread for good (`ids-path-star-nested` at 4
  threads in `tests/sbm11/threads.sh`, stage 1m; `l4pool-bench stress`
  hangs within 20,000 start-stop cycles).

  Each worker thread makes a value of its own when it starts (`start`'s
  `mk`, run on the worker thread) and passes it to every job it runs: an
  object that only that thread reaches, so the Lean runtime keeps it
  single-threaded (plain reference counts, updates in place) for the life of
  the pool. The SBM11 harness keeps a worker's dictionary page cache there,
  so that the pages a worker copied stay with it from one query to the next
  (stage 1h of the record).

  The jobs are closures. A job and what it captures become shared
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

/-- Take the value, blocking as often as needed. A loop, not a recursion: it
    ends when a writer puts a value, an outside event with no termination
    measure, and it keeps one frame however often `notify` wakes it empty. -/
def Cell.take {α : Type} (c : Cell α) (spinNs : Nat) : IO α := do
  repeat
    if let some a ← c.take? spinNs then return a
  throw (IO.userError "WorkerPool.Cell.take: loop ended without a value")

/-! ## The pool -/

/-- One pool thread: its mailbox (jobs, newest first) and its stop flag. A
    job takes the worker's own value (`start`'s `mk`). -/
structure Worker (σ : Type) where
  mail : Cell (List (σ → IO Unit))
  stop : IO.Ref Bool

/-- A pool of `workers.size` threads (`Task.Priority.dedicated`), each with a
    value of type `σ` that its thread made and only its thread reads. -/
structure Pool (σ : Type) where
  workers : Array (Worker σ)
  threads : Array (Task (Except IO.Error Unit))
  spinNs : Nat

/-- The loop of one worker thread: run the jobs of the mailbox in the order
    they were posted; an error that escapes a job is dropped, so the worker
    stays up (`spawnOn` gives each job a cell for its own result). -/
-- A loop that ends when the stop flag is set (an outside event), in one frame.
def workerLoop {σ : Type} (w : Worker σ) (st : σ) (spinNs : Nat) : IO Unit := do
  repeat
    if ← w.stop.get then return
    if let some js ← w.mail.take? spinNs then
      js.reverse.forM fun j => do let _ ← (j st).toBaseIO

/-- Start `n` worker threads that poll for `spinNs` nanoseconds before they
    block. Each thread first runs `mk` and keeps its value for its jobs. -/
def start {σ : Type} (n : Nat) (spinNs : Nat := 1000000) (mk : IO σ) : IO (Pool σ) := do
  let mut ws := #[]
  let mut ts := #[]
  for _ in [0:n] do
    let w : Worker σ := { mail := ← Cell.new, stop := ← IO.mkRef false }
    let t ← IO.asTask (do workerLoop w (← mk) spinNs) Task.Priority.dedicated
    ws := ws.push w
    ts := ts.push t
  return { workers := ws, threads := ts, spinNs }

def Pool.size {σ : Type} (p : Pool σ) : Nat := p.workers.size

/-- Give `job` to worker `i mod size` (nothing happens on an empty pool). -/
def Pool.postTo {σ : Type} (p : Pool σ) (i : Nat) (job : σ → IO Unit) : IO Unit := do
  if h : 0 < p.workers.size then
    let c := (p.workers[i % p.workers.size]'(Nat.mod_lt _ h)).mail
    -- `swap` then `put`, not `IO.Ref.modify`: see `Cell.put`
    let old ← c.val.swap none
    c.put (job :: old.getD [])

/-- Make every blocked worker poll again (call when a query starts). -/
def Pool.wake {σ : Type} (p : Pool σ) : IO Unit :=
  p.workers.forM fun w => w.mail.notify

/-- Stop the workers and wait for their threads to end. -/
def Pool.shutdown {σ : Type} (p : Pool σ) : IO Unit := do
  for w in p.workers do
    -- `modify`, not `set`: the worker reads the flag with `get` (one family,
    -- see the module comment; a `set` here was lost, issue 981)
    w.stop.modify fun _ => true
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
def Pool.spawnOn {σ α : Type} (p : Pool σ) (i : Nat) (act : IO α) : IO (Handle (Except IO.Error α)) := do
  let c ← Cell.new
  p.postTo i (fun _ => do c.put (← act.toBaseIO))
  return .cell c

/-- `spawnOn` for a job that takes the worker's own value. -/
def Pool.spawnWith {σ α : Type} (p : Pool σ) (i : Nat) (act : σ → IO α) : IO (Handle (Except IO.Error α)) := do
  let c ← Cell.new
  p.postTo i (fun st => do c.put (← (act st).toBaseIO))
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
def Pool.runAll {σ α : Type} (p : Pool σ) (jobs : Array (IO α)) : IO (Array (Except IO.Error α)) := do
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
