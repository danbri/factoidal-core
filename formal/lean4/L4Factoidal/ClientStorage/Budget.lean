/-
L4Factoidal.ClientStorage.Budget — how much memory a page's storage may take (everything is
in memory: an origin that wrote without limit would take the machine's memory).

## Decisions

* **One quota for a storage key, all its APIs together** (`keyQuota`, 32 MiB): IndexedDB,
  the origin private file system and the Cache API of a key share it. An API's write is
  checked against the room the others leave (`roomFor`); a write past it is refused with
  `QuotaExceededError` and changes nothing (each API's own check, under the quota given).
* **At most `maxKeys` storage keys hold data in one session** (8): a further key (another
  origin's frame, a storage bucket) gets no room until one is emptied. So a session's
  storage is at most `maxKeys * keyQuota` (256 MiB) whatever its pages do (`session_bound`).
* **One origin cannot take another's share**: the room of a key that already holds data
  depends only on that key's own usage (`roomFor_own`); other keys' use never lowers it.
* **Counts that are not bytes are bounded too**: queued requests of a transaction, open
  cursors, waiting lock requests (`maxPending`): past them a request is refused.
* The constants are the engine's, the same on every machine; none is read from the host.
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Budget

/-- The bytes one storage key may hold, its APIs together: 32 MiB. -/
def keyQuota : Nat := 33554432

/-- The storage keys of one session that may hold data at once. -/
def maxKeys : Nat := 8

/-- Queued requests of one transaction, open cursors, waiting lock requests: at most this
many each. -/
def maxPending : Nat := 100000

/-- The room an API of a key has: `own` what this API holds for the key, `others` what the
key's other APIs hold, `held` how many other keys of the session hold data. A key that holds
nothing yet gets no room while `maxKeys` others do. The API admits a write when its usage
after is at most the room (or does not grow). -/
def roomFor (own others held : Nat) : Nat :=
  if own + others == 0 && held ≥ maxKeys then 0 else keyQuota - others

/-- Kind: resource bound. Says: an API that keeps its usage within the room keeps the key's
total within `keyQuota`. -/
theorem total_le (own' others held : Nat) (h : own' ≤ roomFor 0 others held ∨ own' ≤ roomFor 1 others held) :
    own' + others ≤ keyQuota ∨ own' = 0 := by
  unfold roomFor at h
  rcases h with h | h <;> split at h <;> omega

/-- Kind: isolation (a share no one can take). Says: the room of a key that already holds
data is a function of that key's own usage alone: however much other keys hold, it is
`keyQuota` less what its other APIs hold. -/
theorem roomFor_own (own others held held' : Nat) (h : 0 < own + others) :
    roomFor own others held = roomFor own others held' := by
  unfold roomFor
  have : (own + others == 0) = false := by simp; omega
  simp [this]

theorem sum_filter_pos (l : List Nat) : l.sum = (l.filter (· > 0)).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    by_cases ht : t > 0
    · simp [List.filter_cons, ht, ih]
    · have : t = 0 := by omega
      simp [List.filter_cons, this, ih]

/-- Kind: resource bound. Says: if every key's total is within `keyQuota` and at most
`maxKeys` keys hold data, the session's storage is within `maxKeys * keyQuota`. -/
theorem session_bound (totals : List Nat) (hk : (totals.filter (· > 0)).length ≤ maxKeys)
    (hq : ∀ t ∈ totals, t ≤ keyQuota) : totals.sum ≤ maxKeys * keyQuota := by
  have hsplit : totals.sum = (totals.filter (· > 0)).sum := sum_filter_pos totals
  rw [hsplit]
  have hq' : ∀ t ∈ totals.filter (· > 0), t ≤ keyQuota := fun t ht => hq t (List.mem_filter.mp ht).1
  have : (totals.filter (· > 0)).sum ≤ (totals.filter (· > 0)).length * keyQuota := by
    generalize totals.filter (· > 0) = l at hq'
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.sum_cons, List.length_cons]
      have h1 := hq' x (List.mem_cons_self)
      have h2 := ih (fun y hy => hq' y (List.mem_cons_of_mem _ hy))
      rw [Nat.succ_mul]; omega
  calc (totals.filter (· > 0)).sum ≤ (totals.filter (· > 0)).length * keyQuota := this
    _ ≤ maxKeys * keyQuota := Nat.mul_le_mul_right _ hk

/-- Kind: resource bound. Says: a new key gets no room while `maxKeys` other keys hold data. -/
theorem roomFor_full (held : Nat) (h : held ≥ maxKeys) : roomFor 0 0 held = 0 := by
  simp [roomFor, h]

#guard roomFor 0 0 0 == keyQuota
#guard roomFor 10 20 3 == keyQuota - 20
#guard roomFor 0 0 8 == 0
#guard roomFor 5 0 8 == keyQuota

end L4Factoidal.ClientStorage.Budget
