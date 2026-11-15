module

public import Veil

/-!
# The CPU↔GPU protocol of the compute pipeline

A protocol-level model of what the engine and the host do with GPU buffers (core issue 398; the
kernels and the residency plan are `formal/lean4/L4Factoidal/GpuKernel/{Race,Gather,Resident}.lean`
in core PR 473). The per-kernel proofs say a kernel is race-free and in bounds, and
`Resident.plan` says what one frame uploads. This model says how frames follow each other:

- A buffer has CPU content with a version (`cpuVer`, the content hash in `Resident.Entry.ver`) and,
  when resident, the version on the GPU (`gpuVer`).
- A frame names the buffers it needs (`needs`, chosen freely at each submit); every needed buffer
  must be resident at the current version before the submit (no use before upload).
- Submissions are numbered; the GPU finishes them in order (a fence value `completed`).
  At most `maxInFlight` frames are submitted and not finished.
- A buffer used by an unfinished submission is not evicted and not overwritten (no use after
  free, no write while read).
- A readback of a buffer is taken only after the submission that last used it finished.
- An upload happens only for a buffer that is not resident or whose content changed: the
  residency contract. The ghost counters `uploads`, `edits` and `evictions` show its cost:
  `uploads b ≤ edits b + evictions b + 1`.

Invariants proved by `#check_invariants` with SMT proof reconstruction (`veil.smt.trust false`);
`#model_check` on a small instance is test evidence only.
-/

set_option veil.smt.trust false

veil module GpuProtocol

type buf

immutable individual maxInFlight : Nat

relation resident : buf → Bool
function cpuVer : buf → Nat
function gpuVer : buf → Nat
/- The number of the last submission that used the buffer (0: none). -/
function lastUse : buf → Nat
/- The GPU version the last submission that used the buffer was submitted with. -/
function usedVer : buf → Nat
/- Submissions so far (numbered 1, 2, …) and the fence value: those finished. -/
individual submitted : Nat
individual completed : Nat
relation readBack : buf → Bool
-- Ghost counters for the residency cost.
function uploads : buf → Nat
function edits : buf → Nat
function evictions : buf → Nat

#gen_state

assumption [some_frame] maxInFlight ≥ 1

after_init {
  resident B := false
  cpuVer B := 0
  gpuVer B := 0
  lastUse B := 0
  usedVer B := 0
  submitted := 0
  completed := 0
  readBack B := false
  uploads B := 0
  edits B := 0
  evictions B := 0
}

/- The engine changes a buffer's content (a new version). Its GPU copy is now stale. -/
action edit (b : buf) {
  cpuVer b := cpuVer b + 1
  edits b := edits b + 1
}

/- Upload: only when the buffer is not resident or stale, and not while an unfinished
submission reads it. -/
action upload (b : buf) {
  require ¬ resident b ∨ gpuVer b ≠ cpuVer b
  require lastUse b ≤ completed
  resident b := true
  gpuVer b := cpuVer b
  uploads b := uploads b + 1
}

/- Evict a resident buffer that no unfinished submission uses. -/
action evict (b : buf) {
  require resident b
  require lastUse b ≤ completed
  resident b := false
  evictions b := evictions b + 1
}

/- Submit a frame that needs some set of buffers, all resident at their current version. -/
action submit {
  let needs ← pick (buf → Bool)
  require ∀ b, needs b → resident b ∧ gpuVer b = cpuVer b
  require submitted - completed < maxInFlight
  submitted := submitted + 1
  lastUse B := if needs B then submitted else lastUse B
  usedVer B := if needs B then gpuVer B else usedVer B
}

/- The GPU finishes the oldest unfinished submission. -/
action finish {
  require completed < submitted
  completed := completed + 1
}

/- Read a buffer back to the CPU once the submission that last used it has finished. -/
action readback (b : buf) {
  require resident b
  require lastUse b ≤ completed
  readBack b := true
}

safety [fence_order] completed ≤ submitted
safety [frames_bounded] submitted - completed ≤ maxInFlight
invariant [use_numbered] lastUse B ≤ submitted
-- No use after free: a buffer an unfinished submission uses is resident.
safety [in_use_resident] lastUse B > completed → resident B
-- No write while read: an unfinished submission's buffers keep, on the GPU, the version it was
-- submitted with (an edit after the submit moves `cpuVer` on; the GPU copy stays until the
-- submission finishes). No use before upload is the guard of `submit`.
safety [in_use_unchanged] lastUse B > completed → gpuVer B = usedVer B
invariant [gpu_not_ahead] gpuVer B ≤ cpuVer B
-- Residency: every upload is paid for by the first load, an edit or an eviction.
safety [no_reupload] uploads B ≤ edits B + evictions B + 1
-- The credit: a buffer that is not resident, or stale, has an upload in hand.
invariant [credit] ¬ resident B ∨ gpuVer B ≠ cpuVer B → uploads B ≤ edits B + evictions B

-- Model checking only: bound the counters of the finite instance.
state_constraint [small] submitted ≤ 3 ∧ cpuVer B ≤ 2 ∧ evictions B ≤ 1

#gen_spec

#check_invariants

#gen_theorems

#model_check { buf := Fin 2 } { maxInFlight := 2 }

end GpuProtocol
