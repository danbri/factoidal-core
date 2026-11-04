/-
L4Factoidal.XMPP.Held — stanzas held for an account that has no bound session (RFC 6121
section 8.5.2.1.1: a message to an account with no available resource may be stored "for later
delivery"), as a bounded queue with proved limits.

  hold    : Held → bare JID → text → Held × Bool     (false: refused, the queue is full)
  release : Held → bare JID → List text × Held       (the account bound a session)

Bounds: at most `perAccount` stanzas for one account and `total` in all. A refused message is
answered `resource-constraint` by the caller (RFC 6120 section 8.3.3.18); nothing is held past
a bound. Released stanzas are removed: a stanza is delivered once, then it is gone, from memory
and from the next write of the state (`docs/20261102-xmpp-starttls.md`, "Step 6 design").

Fixes https://github.com/danbri/factoidal/issues/1235 (the JS host held without a bound).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.XMPP.Held

structure Held where
  /-- Account → its held stanzas, oldest first. -/
  queues : List (String × List String) := []
  perAccount : Nat := 1000
  total : Nat := 100000
  deriving Repr, Inhabited, DecidableEq

def Held.of (h : Held) (bare : String) : List String :=
  ((h.queues.find? (·.1 == bare)).map (·.2)).getD []

/-- Stanzas held in all. A left fold: tail-recursive in compiled code (the tail-recursion gate). -/
def Held.size (h : Held) : Nat := h.queues.foldl (fun acc q => acc + q.2.length) 0

def Held.put (h : Held) (bare : String) (q : List String) : Held :=
  let others := h.queues.filter (·.1 != bare)
  { h with queues := if q.isEmpty then others else others ++ [(bare, q)] }

/-- Hold one stanza for `bare`, unless a bound would be passed. -/
def hold (h : Held) (bare text : String) : Held × Bool :=
  if (h.of bare).length < h.perAccount ∧ h.size < h.total then (h.put bare (h.of bare ++ [text]), true)
  else (h, false)

/-- Everything held for `bare`, oldest first, and the queue without it. -/
def release (h : Held) (bare : String) : List String × Held :=
  (h.of bare, h.put bare [])

/-! ## Theorems -/

theorem of_put_self (h : Held) (bare : String) (q : List String) :
    (h.put bare q).of bare = q := by
  unfold Held.put Held.of
  cases hq : q.isEmpty
  · simp only [hq, Bool.false_eq_true, ↓reduceIte, List.find?_append]
    rw [List.find?_eq_none.mpr (by intro x hx; simp [List.mem_filter] at hx; simp [hx.2])]
    simp
  · simp only [hq, ↓reduceIte]
    rw [List.find?_eq_none.mpr (by intro x hx; simp [List.mem_filter] at hx; simp [hx.2])]
    simp at hq
    simp [hq]

/-- Holding never puts more than `perAccount` stanzas in the account's queue. -/
theorem hold_perAccount (h : Held) (bare text : String) (hinv : (h.of bare).length ≤ h.perAccount) :
    ((hold h bare text).1.of bare).length ≤ h.perAccount := by
  by_cases hc : (h.of bare).length < h.perAccount ∧ h.size < h.total
  · simp only [hold, hc, and_self, ↓reduceIte, of_put_self, List.length_append, List.length_singleton]
    omega
  · simp only [hold, hc, ↓reduceIte]
    exact hinv

/-- A refusal changes nothing. -/
theorem hold_refused (h : Held) (bare text : String) (hr : (hold h bare text).2 = false) :
    (hold h bare text).1 = h := by
  by_cases hc : (h.of bare).length < h.perAccount ∧ h.size < h.total
  · simp [hold, hc] at hr
  · simp [hold, hc]

/-- Holding keeps the bounds' settings. -/
theorem hold_limits (h : Held) (bare text : String) :
    (hold h bare text).1.perAccount = h.perAccount ∧ (hold h bare text).1.total = h.total := by
  by_cases hc : (h.of bare).length < h.perAccount ∧ h.size < h.total
  · simp [hold, hc, Held.put]
  · simp [hold, hc]

/-- Release empties the account's queue: a delivered stanza is gone. -/
theorem release_empties (h : Held) (bare : String) : (release h bare).2.of bare = [] :=
  of_put_self h bare []

/-- Release hands back exactly what was held, oldest first. -/
theorem release_returns (h : Held) (bare : String) : (release h bare).1 = h.of bare := rfl

/-! ## Checks -/

#guard
  let h0 : Held := { perAccount := 2 }
  let (h1, a) := hold h0 "r@x" "1"
  let (h2, b) := hold h1 "r@x" "2"
  let (h3, c) := hold h2 "r@x" "3"
  a && b && !c && h3.of "r@x" == ["1", "2"] && h3 == h2

#guard
  let h0 : Held := {}
  let (h1, _) := hold h0 "r@x" "1"
  let (h2, _) := hold h1 "s@x" "2"
  let (out, h3) := release h2 "r@x"
  out == ["1"] && h3.of "r@x" == [] && h3.of "s@x" == ["2"] && h3.size == 1

#guard
  let h0 : Held := { total := 1 }
  let (h1, a) := hold h0 "r@x" "1"
  let (_, b) := hold h1 "s@x" "2"
  a && !b

end L4Factoidal.XMPP.Held
