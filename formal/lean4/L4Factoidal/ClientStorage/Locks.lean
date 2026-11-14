/-
L4Factoidal.ClientStorage.Locks — the Web Locks API (W3C web-locks): the lock manager of a
storage key: held locks, the queue of requests, `ifAvailable`, `steal`, abort, `query`.

## Decisions

* The lock manager is the shelf of a storage key in the storage core, so a page of one
  origin can neither see nor delay the locks of another (`opFor_noninterference`).
* A request is granted when no held lock of its name conflicts (an exclusive lock conflicts
  with every lock; shared locks do not conflict with each other) and no earlier request of
  its name still waits (`settle`): the queue of a name is first in, first out, so a later
  shared request never overtakes a waiting exclusive one.
* `ifAvailable` never waits: it is granted at once or answered "not available", and the
  queue is as it was (`ifAvailable_no_wait`).
* `steal` releases every held lock of the name (their holders are told) and holds it alone
  (`steal_alone`).
* Mutual exclusion is the invariant `Excl` of the held locks, kept by every command
  (`op_excl`).

Commands (`web_api` op 203): see `op`. In memory; a session's locks end with it.
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Locks

structure Req where
  id : Nat
  name : String
  exclusive : Bool
  client : String
  deriving DecidableEq, Repr, Inhabited

/-- The lock manager of one storage key. -/
structure Shelf where
  held : List Req := []
  /-- Requests that wait, first in first out. -/
  queue : List Req := []
  next : Nat := 1
  deriving Inhabited

/-- Two locks may be held together: other names, or both shared. -/
def together (a b : Req) : Prop := a.name ≠ b.name ∨ (a.exclusive = false ∧ b.exclusive = false)

instance (a b : Req) : Decidable (together a b) := by unfold together; exact inferInstance

/-- `r` conflicts with no held lock. -/
def compatible (held : List Req) (r : Req) : Bool := held.all fun h => decide (together h r)

/-- Mutual exclusion: any two held locks may be held together. -/
def Excl (held : List Req) : Prop := held.Pairwise together

/-- One request of the queue in `settle`: granted when compatible with what is held and no
earlier request of its name was left waiting; else it waits. The state is the held locks,
the requests left waiting (in reverse) and the ids granted (in reverse). -/
def settleStep (st : List Req × List Req × List Nat) (r : Req) : List Req × List Req × List Nat :=
  if compatible st.1 r && !st.2.1.any (·.name == r.name) then (st.1 ++ [r], st.2.1, r.id :: st.2.2)
  else (st.1, r :: st.2.1, st.2.2)

/-- Grant what can be granted, in queue order: the shelf after it and the ids granted. -/
def settle (s : Shelf) : Shelf × List Nat :=
  let r := s.queue.foldl settleStep (s.held, [], [])
  ({ s with held := r.1, queue := r.2.1.reverse }, r.2.2.reverse)

theorem excl_append (held : List Req) (r : Req) (h : Excl held) (hc : compatible held r = true) : Excl (held ++ [r]) := by
  unfold Excl
  rw [List.pairwise_append]
  refine ⟨h, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  have := List.all_eq_true.mp hc a ha
  simpa using this

theorem settleStep_excl (st : List Req × List Req × List Nat) (r : Req) (h : Excl st.1) : Excl (settleStep st r).1 := by
  unfold settleStep
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    exact excl_append _ _ h hc.1
  · exact h

theorem foldl_excl (q : List Req) : ∀ st : List Req × List Req × List Nat, Excl st.1 → Excl (q.foldl settleStep st).1 := by
  induction q with
  | nil => intro st h; exact h
  | cons r rs ih => intro st h; exact ih _ (settleStep_excl st r h)

/-- Kind: invariant (mutual exclusion). Says: granting from the queue keeps mutual
exclusion: an exclusive lock on a name is never held with another lock of that name. -/
theorem settle_excl (s : Shelf) (h : Excl s.held) : Excl (settle s).1.held := foldl_excl s.queue _ h

/-- Kind: fairness law (no overtaking). Says: a request is not granted in a pass while an
earlier request of the same name is left waiting, whatever its mode: a later shared request
does not overtake a waiting exclusive one. -/
theorem settleStep_no_overtake (st : List Req × List Req × List Nat) (r : Req)
    (h : st.2.1.any (·.name == r.name) = true) : settleStep st r = (st.1, r :: st.2.1, st.2.2) := by
  simp [settleStep, h]

/-! ## Commands -/

abbrev Tok := ByteArray
def S (x : String) : Tok := x.toUTF8
def N (n : Nat) : Tok := (toString n).toUTF8
def ok (xs : List Tok := []) : List Tok := S "ok" :: xs
def fail (name : String) : List Tok := [S ("!" ++ name)]
def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""
def natAt (a : Array Tok) (i : Nat) : Nat := (strAt a i).toNat?.getD 0

/-- `steal`: every held lock of the request's name is released, and the request holds. -/
def stealLock (s : Shelf) (r : Req) : Shelf :=
  { s with held := r :: s.held.filter (·.name != r.name), next := s.next + 1 }

/-- `request name mode flags client` (mode `x` exclusive or `s` shared; flags 1 ifAvailable,
2 steal, 4 has a signal). The answer: the request's id, `1` when it is granted now, `0`
when it waits, `none` when `ifAvailable` found it taken; then the ids of the locks a steal
released. -/
def request (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  let name := strAt a 1
  let exclusive := strAt a 2 != "s"
  let flags := natAt a 3
  let ifAvailable := flags % 2 == 1
  let steal := flags / 2 % 2 == 1
  let signal := flags / 4 % 2 == 1
  if name.startsWith "-" then (s, fail "NotSupportedError")
  else if steal && ifAvailable then (s, fail "NotSupportedError")
  else if steal && !exclusive then (s, fail "NotSupportedError")
  else if signal && (steal || ifAvailable) then (s, fail "NotSupportedError")
  else
    let r : Req := { id := s.next, name, exclusive, client := strAt a 4 }
    if steal then
      let stolen := s.held.filter (·.name == name)
      (stealLock s r, ok ([N r.id, S "1"] ++ stolen.map (N ·.id)))
    else if ifAvailable then
      if compatible s.held r && !s.queue.any (·.name == name) then
        ({ s with held := s.held ++ [r], next := s.next + 1 }, ok [N r.id, S "1"])
      else (s, ok [N 0, S "none"])
    else
      let (s', granted) := settle { s with queue := s.queue ++ [r], next := s.next + 1 }
      (s', ok [N r.id, S (if granted.contains r.id then "1" else "0")])

/-- One command of the lock manager. `release id` and `abort id` answer the ids granted by
the pass that follows; `query` answers the held locks then the pending requests, each as
name, mode, client, with `|` between the two lists. -/
def op (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  let row (r : Req) : List Tok := [S r.name, S (if r.exclusive then "exclusive" else "shared"), S r.client]
  match strAt a 0 with
  | "request" => request s a
  | "check" =>
    -- the refusals of `request` alone (the page side reads the signal between the two)
    let r := request s a
    (s, if (r.2.head?.map fun t => (String.fromUTF8? t).getD "") == some "ok" then ok else r.2)
  | "release" =>
    let (s', granted) := settle { s with held := s.held.filter (·.id != natAt a 1) }
    (s', ok (granted.map N))
  | "abort" =>
    let (s', granted) := settle { s with queue := s.queue.filter (·.id != natAt a 1) }
    (s', ok (granted.map N))
  | "query" => (s, ok (s.held.flatMap row ++ [S "|"] ++ s.queue.flatMap row))
  | _ => (s, fail "NotSupportedError")

/-- One command for the context whose storage key is `k`. -/
def opFor (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) : Shed Shelf × List Tok :=
  shed.act k (fun s => op s a) (fail "SecurityError")

/-! ## Theorems -/

theorem excl_filter (held : List Req) (p : Req → Bool) (h : Excl held) : Excl (held.filter p) := List.Pairwise.filter _ h

/-- Kind: invariant (mutual exclusion). Says: every command keeps mutual exclusion: in
every state reached from the empty lock manager, an exclusive lock on a name is the only
lock held on that name, and shared locks are held only with shared locks. Does not say:
that the page side runs a callback only while its lock is held (it holds the lock from
`request`'s grant to its `release`). -/
theorem op_excl (s : Shelf) (a : Array Tok) (h : Excl s.held) : Excl (op s a).1.held := by
  unfold op
  split
  · -- request
    unfold request
    simp only
    repeat' split
    all_goals first
      | exact h
      | exact settle_excl _ h
      | (rename_i hc; rw [Bool.and_eq_true] at hc; exact excl_append _ _ h hc.1)
      | skip
    -- steal: the stealer and the locks of other names
    unfold stealLock Excl
    rw [List.pairwise_cons]
    refine ⟨?_, excl_filter _ _ h⟩
    intro b hb
    have := (List.mem_filter.mp hb).2
    left
    simp at this
    exact fun e => this e.symm
  · exact h
  · exact settle_excl _ (excl_filter _ _ h)
  · exact settle_excl _ h
  · exact h
  · exact h

/-- Kind: functional law. Says: a request with `ifAvailable` never waits: after it the
queue is exactly as it was. -/
theorem ifAvailable_no_wait (s : Shelf) (a : Array Tok) (h : natAt a 3 % 2 = 1) : (request s a).1.queue = s.queue := by
  unfold request
  simp only [h]
  repeat' split
  all_goals first | rfl | simp_all

/-- Kind: functional law. Says: after a `steal`, the stealer is the only held lock of its
name: every earlier holder of that name was released. -/
theorem steal_alone (s : Shelf) (r : Req) : (stealLock s r).held.filter (·.name == r.name) = [r] := by
  have hnil : (s.held.filter (·.name != r.name)).filter (·.name == r.name) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    have := (List.mem_filter.mp hx).2
    simpa using this
  simp [stealLock, hnil]

/-- Kind: security theorem (locks are partitioned by storage key). Says: whatever a context
with one storage key does with locks, the answer another key then gets for any command is
the answer it would have got without it: a lock of one origin is neither listed to another
origin by `query` nor makes its request wait. -/
theorem opFor_noninterference (shed : Shed Shelf) (k k' : ClientStorage.Key) (a a' : Array Tok) (h : k ≠ k') :
    (opFor (opFor shed k a).1 k' a').2 = (opFor shed k' a').2 :=
  act_noninterference Shed.laws shed k k' _ _ _ _ h

/-! ## Checks (WPT web-locks: acquire, held, ifAvailable, steal, mode-exclusive, mode-shared, query) -/

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")
private def answers (cmds : List (List String)) : List String :=
  (cmds.foldl (fun (acc : Shelf × List String) c => let (s, r) := op acc.1 (T c); (s, acc.2 ++ [shown r])) ({}, [])).2

#guard answers [["request", "a", "x", "0", "c"], ["request", "a", "x", "0", "c"], ["request", "b", "x", "0", "c"], ["release", "1"], ["release", "2"]] ==
  ["ok 1 1", "ok 2 0", "ok 3 1", "ok 2", "ok"]
-- shared locks are held together; an exclusive request waits for all of them; a later shared one waits behind it
#guard answers [["request", "a", "s", "0", "c"], ["request", "a", "s", "0", "c"], ["request", "a", "x", "0", "c"], ["request", "a", "s", "0", "c"],
  ["release", "1"], ["release", "2"], ["release", "3"]] == ["ok 1 1", "ok 2 1", "ok 3 0", "ok 4 0", "ok", "ok 3", "ok 4"]
-- ifAvailable: granted or not available, never queued; not available behind a waiting request
#guard answers [["request", "a", "x", "0", "c"], ["request", "a", "x", "1", "c"], ["request", "b", "s", "1", "c"], ["request", "a", "x", "0", "c"],
  ["release", "1"], ["request", "a", "s", "1", "c"], ["query"]] ==
  ["ok 1 1", "ok 0 none", "ok 2 1", "ok 3 0", "ok 3", "ok 0 none", "ok b shared c a exclusive c |"]
-- steal: the holders are released, the stealer holds; the queue keeps waiting behind it
#guard answers [["request", "a", "s", "0", "c"], ["request", "a", "s", "0", "c"], ["request", "a", "x", "0", "c"], ["request", "a", "x", "2", "d"], ["query"],
  ["release", "4"]] == ["ok 1 1", "ok 2 1", "ok 3 0", "ok 4 1 1 2", "ok a exclusive d | a exclusive c", "ok 3"]
-- abort of a waiting request lets the ones behind it through
#guard answers [["request", "a", "s", "0", "c"], ["request", "a", "x", "0", "c"], ["request", "a", "s", "0", "c"], ["abort", "2"]] == ["ok 1 1", "ok 2 0", "ok 3 0", "ok 3"]
-- refusals
#guard answers [["check", "-a", "x", "0", "c"], ["check", "a", "x", "0", "c"], ["query"]] == ["!NotSupportedError", "ok", "ok |"]
#guard answers [["request", "-a", "x", "0", "c"], ["request", "a", "x", "3", "c"], ["request", "a", "s", "2", "c"], ["request", "a", "x", "5", "c"], ["request", "a", "x", "6", "c"]] ==
  ["!NotSupportedError", "!NotSupportedError", "!NotSupportedError", "!NotSupportedError", "!NotSupportedError"]

end L4Factoidal.ClientStorage.Locks
