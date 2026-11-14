/-!
# Streams Standard: the queue of a controller, and the plan of a byte-stream fill

https://streams.spec.whatwg.org/. The classes of the Standard (ReadableStream, WritableStream,
TransformStream and their readers, writers and controllers) are promise plumbing between a
page's callbacks; that part is the page script layer (`tools/wasmvm/quickjs/prelude.js`,
section "Streams Standard"). What decides something is here, as pure functions:

- `SizedQueue`: §8.1 queue-with-sizes (EnqueueValueWithSize, DequeueValue, PeekQueueValue,
  ResetQueue). A controller's chunks wait here; the engine's native `n.streams` holds one in
  an object of the script heap (`JS.Kind.queue`).
- `validSize`, `validHighWaterMark`: §8.1 IsNonNegativeNumber with the finiteness check of
  EnqueueValueWithSize, and §7.4 ExtractHighWaterMark's check.
- `fillPlan`: §4.10.11 ReadableByteStreamControllerFillPullIntoDescriptorFromQueue, steps 1
  to 7: how many bytes of the queue go into a BYOB read's view, and whether the read is then
  ready (the view holds at least its minimum, in whole elements).

Theorems: the queue is first in, first out (`toList_enqueue`, `dequeue_toList`,
`dequeue_none`, `count_eq_length`, the well-formedness lemmas), a chunk with a bad size is
never queued (`enqueue_refuses`), and the fill plan never takes more than the queue holds or
the view has room for, and a ready plan ends on an element boundary at or past the minimum
(`fillPlan_le_queue`, `fillPlan_fits`, `fillPlan_ready`, `fillPlan_not_ready`).
Not proved: anything about the sizes' sum (`total` is a `Float`, as the Standard has it:
double arithmetic, clamped at 0), and nothing about the promise plumbing in the prelude.
-/

namespace L4Factoidal.WHATWG.Streams

/-- A chunk size may be queued (§8.1 EnqueueValueWithSize, steps 2 and 3): a number that is
not NaN, not negative and not +∞. -/
def validSize (s : Float) : Bool := s.isFinite && s ≥ 0

/-- A high water mark is usable (§7.4 ExtractHighWaterMark, step 3): not NaN, not negative.
+∞ is allowed. -/
def validHighWaterMark (h : Float) : Bool := !h.isNaN && h ≥ 0

/-- §8.1 queue-with-sizes: the values with their sizes, oldest first from `head`, and the
total of the sizes (`[[queueTotalSize]]`). The entries before `head` are gone; `dequeue`
drops them from the array once they are half of it. -/
structure SizedQueue (α : Type) where
  items : Array (α × Float) := #[]
  head : Nat := 0
  total : Float := 0

namespace SizedQueue
variable {α : Type}

/-- The queue as the Standard's list: the values with their sizes, oldest first. -/
def toList (q : SizedQueue α) : List (α × Float) := q.items.toList.drop q.head

/-- How many values wait. -/
def count (q : SizedQueue α) : Nat := q.items.size - q.head

/-- `head` is within the array. Every queue made by the functions here has it. -/
def WF (q : SizedQueue α) : Prop := q.head ≤ q.items.size

/-- The total after a value of size `s` leaves (DequeueValue, steps 4 and 5): double
arithmetic, and 0 if rounding made it negative. -/
def subSize (total s : Float) : Float := let t := total - s; if t < 0 then 0 else t

/-- EnqueueValueWithSize: `none` for a size that is not a finite, non-negative number (the
caller throws a RangeError). -/
def enqueue (q : SizedQueue α) (a : α) (s : Float) : Option (SizedQueue α) :=
  if validSize s then some { q with items := q.items.push (a, s), total := q.total + s } else none

/-- DequeueValue: the oldest value and the queue without it; the total goes down by its
size and is 0 if rounding made it negative. `none` on an empty queue. -/
def dequeue (q : SizedQueue α) : Option (α × SizedQueue α) :=
  if h : q.head < q.items.size then
    if (q.head + 1) * 2 ≥ q.items.size then
      some (q.items[q.head].1, { items := q.items.extract (q.head + 1) q.items.size, head := 0, total := subSize q.total q.items[q.head].2 })
    else some (q.items[q.head].1, { q with head := q.head + 1, total := subSize q.total q.items[q.head].2 })
  else none

/-- PeekQueueValue: the oldest value. -/
def peek (q : SizedQueue α) : Option α := (q.items[q.head]?).map (·.1)

/-- ResetQueue. -/
def reset : SizedQueue α := {}

theorem wf_empty : (({} : SizedQueue α)).WF := by simp [WF]

/-- Kind: an invariant. Says: `enqueue` keeps `head` within the array. -/
theorem wf_enqueue (q q' : SizedQueue α) (a : α) (s : Float) (hw : q.WF) (h : q.enqueue a s = some q') : q'.WF := by
  unfold enqueue at h
  split at h
  · injection h with h; subst h; simp [WF] at *; omega
  · simp at h

/-- Kind: a refusal. Says: a chunk whose size is NaN, negative or infinite is not queued: the
queue's answer is `none`, and the caller's RangeError is the only outcome.
Does not say: what `validSize` answers for a given double (`Float` is opaque to proofs; the
`#guard`s below test it). -/
theorem enqueue_refuses (q : SizedQueue α) (a : α) (s : Float) (h : validSize s = false) : q.enqueue a s = none := by
  simp [enqueue, h]

/-- Kind: a specification (first in, first out). Says: a queued value goes to the end of the
list, with its size, and nothing else changes place. -/
theorem toList_enqueue (q q' : SizedQueue α) (a : α) (s : Float) (hw : q.WF) (h : q.enqueue a s = some q') :
    q'.toList = q.toList ++ [(a, s)] := by
  unfold enqueue at h
  split at h
  · injection h with h; subst h
    simp only [toList, Array.toList_push]
    exact List.drop_append_of_le_length (by simpa [WF] using hw)
  · simp at h

/-- Kind: a specification. Says: `count` is the length of the list. -/
theorem count_eq_length (q : SizedQueue α) : q.count = q.toList.length := by
  simp [count, toList]

/-- Kind: a specification (first in, first out). Says: `dequeue` answers the first value of
the list and leaves the rest of it, in order; dropping the used entries from the array
(`extract`) does not change the list.
Does not say: anything about `total`. -/
theorem dequeue_toList (q q' : SizedQueue α) (a : α) (h : q.dequeue = some (a, q')) :
    ∃ s, q.toList = (a, s) :: q'.toList := by
  unfold dequeue at h
  split at h
  · rename_i hlt
    refine ⟨(q.items[q.head]).2, ?_⟩
    have hd : q.toList = q.items[q.head] :: q.items.toList.drop (q.head + 1) := by
      simp only [toList]
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    split at h
    · injection h with h
      injection h with h1 h2
      subst h2
      rw [hd, ← h1]
      simp [toList, Array.toList_extract, List.take_of_length_le]
    · injection h with h
      injection h with h1 h2
      subst h2
      rw [hd, ← h1]
      simp [toList]
  · simp at h

/-- Kind: a specification. Says: `dequeue` answers nothing exactly when nothing waits. -/
theorem dequeue_none (q : SizedQueue α) (hw : q.WF) : q.dequeue = none ↔ q.toList = [] := by
  unfold dequeue toList
  constructor
  · intro h
    split at h
    · split at h <;> simp at h
    · rename_i hge
      simp [List.drop_eq_nil_iff]; omega
  · intro h
    have : q.items.size ≤ q.head := by simpa [List.drop_eq_nil_iff] using h
    simp [show ¬ q.head < q.items.size by omega]

/-- Kind: an invariant. Says: `dequeue` keeps `head` within the array. -/
theorem wf_dequeue (q q' : SizedQueue α) (a : α) (h : q.dequeue = some (a, q')) : q'.WF := by
  unfold dequeue at h
  split at h
  · rename_i hlt
    split at h
    · injection h with h; injection h with _ h2; subst h2; simp [WF]
    · injection h with h; injection h with _ h2; subst h2; simp [WF]; omega
  · simp at h

end SizedQueue

/-- The plan of ReadableByteStreamControllerFillPullIntoDescriptorFromQueue (§4.10.11), steps
1 to 7: `toCopy` bytes go from the queue into the view, and `ready` says the view then holds
at least its minimum fill in whole elements. -/
structure FillPlan where
  toCopy : Nat
  ready : Bool
  deriving Repr, BEq, DecidableEq

/-- The plan for a queue of `queueTotal` bytes and a pull-into descriptor with a view of
`byteLength` bytes, `bytesFilled` of them filled, elements of `elementSize` bytes and a
minimum fill of `minimumFill` bytes. -/
def fillPlan (queueTotal byteLength bytesFilled elementSize minimumFill : Nat) : FillPlan :=
  let maxCopy := min queueTotal (byteLength - bytesFilled)
  let maxFilled := bytesFilled + maxCopy
  let aligned := maxFilled - maxFilled % elementSize
  if aligned ≥ minimumFill then ⟨aligned - bytesFilled, true⟩ else ⟨maxCopy, false⟩

/-- Kind: a bound. Says: the plan never takes more bytes than the queue holds, so the copy
loop that follows it never reads past the queue. -/
theorem fillPlan_le_queue (q len filled e m : Nat) : (fillPlan q len filled e m).toCopy ≤ q := by
  unfold fillPlan
  simp only []
  split <;> simp <;> omega

/-- Kind: a bound (memory safety of the copy). Says: the bytes filled after the plan fit in
the view: the copy never writes past the end of the page's buffer.
Does not say: that the prelude's loop copies exactly `toCopy` bytes (it is written to; that is
read from the code and tested, not proved). -/
theorem fillPlan_fits (q len filled e m : Nat) (h : filled ≤ len) :
    filled + (fillPlan q len filled e m).toCopy ≤ len := by
  unfold fillPlan
  simp only []
  split <;> simp <;> omega

/-- Kind: a specification. Says: a ready plan fills the view to an element boundary, at or
past the minimum fill: a BYOB read never answers part of an element or less than `min`. -/
theorem fillPlan_ready (q len filled e m : Nat) (hm : filled ≤ m)
    (h : (fillPlan q len filled e m).ready = true) :
    (filled + (fillPlan q len filled e m).toCopy) % e = 0 ∧ m ≤ filled + (fillPlan q len filled e m).toCopy := by
  unfold fillPlan at h ⊢
  simp only [] at h ⊢
  split at h
  · rename_i hge
    simp only [if_pos hge]
    have hsub : filled + (filled + min q (len - filled) - (filled + min q (len - filled)) % e - filled) =
        filled + min q (len - filled) - (filled + min q (len - filled)) % e := by omega
    rw [hsub]
    refine ⟨?_, hge⟩
    have hx := Nat.div_add_mod (filled + min q (len - filled)) e
    have : filled + min q (len - filled) - (filled + min q (len - filled)) % e = e * ((filled + min q (len - filled)) / e) := by omega
    rw [this]
    exact Nat.mul_mod_right _ _
  · simp at h

/-- Kind: a specification. Says: a plan that is not ready takes everything the queue has that
the view has room for (the read stays pending with all the bytes there are). -/
theorem fillPlan_not_ready (q len filled e m : Nat) (h : (fillPlan q len filled e m).ready = false) :
    (fillPlan q len filled e m).toCopy = min q (len - filled) := by
  unfold fillPlan at h ⊢
  simp only [] at h ⊢
  split at h
  · simp at h
  · rename_i hlt; simp [hlt]

/-! ## Tests -/

#guard validSize 0 && validSize 1.5 && validSize 1e300 && !validSize (-1) && !validSize (0/0) && !validSize (1/0) && !validSize (-1/0)
#guard validHighWaterMark 0 && validHighWaterMark (1/0) && !validHighWaterMark (-1) && !validHighWaterMark (0/0)

/-- A queue after a list of enqueues, for the tests. -/
def queueOf (xs : List (Nat × Float)) : SizedQueue Nat :=
  xs.foldl (fun q (a, s) => (q.enqueue a s).getD q) {}

/-- Dequeue `k` times: the values, and the queue left. -/
def drain : Nat → SizedQueue Nat → List Nat × SizedQueue Nat
  | 0, q => ([], q)
  | k + 1, q => match q.dequeue with
    | some (a, q') => let (as, q'') := drain k q'; (a :: as, q'')
    | none => ([], q)

#guard (queueOf [(1, 1), (2, 2), (3, 4)]).toList.map (·.1) == [1, 2, 3]
#guard (queueOf [(1, 1), (2, 2), (3, 4)]).total == 7 && (queueOf [(1, 1), (2, 2), (3, 4)]).count == 3
#guard (drain 2 (queueOf [(1, 1), (2, 2), (3, 4)])).1 == [1, 2] && (drain 2 (queueOf [(1, 1), (2, 2), (3, 4)])).2.total == 4
#guard (drain 9 (queueOf [(1, 1), (2, 2), (3, 4)])).1 == [1, 2, 3] && (drain 9 (queueOf [(1, 1), (2, 2), (3, 4)])).2.total == 0
#guard (queueOf [(1, 1), (2, 0/0), (3, -1), (4, 1/0), (5, 0)]).toList.map (·.1) == [1, 5]
#guard (queueOf [(1, 1)]).peek == some 1 && (queueOf []).peek == none && ((queueOf [(1, 1)]).dequeue.map (·.2.peek)) == some none
-- a long queue keeps its order through the array's compaction
#guard (drain 700 (queueOf ((List.range 1000).map fun i => (i, 1)))).1 == List.range 700 &&
  ((drain 700 (queueOf ((List.range 1000).map fun i => (i, 1)))).2.toList.map (·.1)) == (List.range 1000).drop 700
-- the total is double arithmetic and is clamped at 0 (WPT streams/*/floating-point-total-queue-size)
#guard (drain 2 (queueOf [(1, 1e-16), (2, 1)])).2.total == 0

-- WPT streams/readable-byte-streams: a Uint16Array view of 8 bytes, 3 bytes queued: 2 go in
#guard fillPlan 3 8 0 2 2 == ⟨2, true⟩
-- 1 byte queued for a Uint16Array: not ready, the byte goes in
#guard fillPlan 1 8 0 2 2 == ⟨1, false⟩
-- min 3 elements of 2 bytes, 5 bytes queued: not ready, all 5 go in; with 7 queued: 6 go in
#guard fillPlan 5 16 0 2 6 == ⟨5, false⟩ && fillPlan 7 16 0 2 6 == ⟨6, true⟩
-- one byte filled already, 4 queued, Uint32Array: 3 more make a whole element
#guard fillPlan 4 8 1 4 4 == ⟨3, true⟩
-- more queued than the view has room for
#guard fillPlan 100 8 0 1 1 == ⟨8, true⟩

end L4Factoidal.WHATWG.Streams
