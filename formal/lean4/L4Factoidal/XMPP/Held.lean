/-
L4Factoidal.XMPP.Held — stanzas held for an account that has no bound session (RFC 6121
section 8.5.2.1.1: a message to an account with no available resource may be stored "for later
delivery"), as a bounded queue with proved limits.

  hold    : Held → bare JID → text → Held × Bool     (false: refused, a cap would be passed)
  release : Held → bare JID → List Item × Held       (the account bound a session)
  admit   : hold, for a stanza a session sent: the sender's rate limit first
  restore : Held → Item → Held                       (a start, from the kept state)

Caps (`Caps`): a stanza count and a byte count for one account, and the same two for the server.
A refused message is answered `resource-constraint` by the caller (RFC 6120 section 8.3.3.18);
nothing is held past a cap. The sender's rate limit uses the counters of `Net.LoginLimit`, with
one key per sending account: `Failures.record` counts a held stanza as it counts a failed login.

Each held stanza is one `Item` with a sequence number, so a host that keeps the state writes ONE
small resource per stanza (`StateCodec.heldItemPath`) and never the queue again. Released stanzas
are removed: a stanza is delivered once, then it is gone, from memory and from the state
(`docs/20261102-xmpp-starttls.md`, "Step 6 design").

Fixes https://github.com/danbri/factoidal/issues/1235 (the JS host held without a bound).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Net.LoginLimit

namespace L4Factoidal.XMPP.Held

open L4Factoidal.Net.LoginLimit (Limits Failures)

/-- One held stanza. -/
structure Item where
  /-- The account it waits for. -/
  bare : String
  /-- Its place: the order of an account's stanzas, and its name in the kept state. 0: from a
  state written before items had a number, older than any numbered item. -/
  seq : Nat
  text : String
  deriving Repr, Inhabited, DecidableEq

structure Caps where
  perAccount : Nat := 256
  perAccountBytes : Nat := 4 * 1024 * 1024
  total : Nat := 10000
  totalBytes : Nat := 64 * 1024 * 1024
  deriving Repr, Inhabited, DecidableEq

structure Held where
  /-- Oldest first within each account. -/
  items : List Item := []
  caps : Caps := {}
  /-- The `seq` of the next stanza held. -/
  nextSeq : Nat := 1
  deriving Repr, Inhabited, DecidableEq

/-- The sum of the stanzas' UTF-8 sizes. A left fold: tail-recursive in compiled code (the
tail-recursion gate). -/
def bytesOf (l : List Item) : Nat := l.foldl (fun acc i => acc + i.text.utf8ByteSize) 0

def Held.of (h : Held) (bare : String) : List Item := h.items.filter (·.bare == bare)

/-- The texts held for `bare`, oldest first. -/
def Held.texts (h : Held) (bare : String) : List String := (h.of bare).map (·.text)

/-- Stanzas held in all. -/
def Held.size (h : Held) : Nat := h.items.length

/-- Would one more stanza for `bare` stay inside every cap? -/
def Held.fits (h : Held) (bare text : String) : Bool :=
  decide ((h.of bare).length < h.caps.perAccount) &&
  decide (bytesOf (h.of bare) + text.utf8ByteSize ≤ h.caps.perAccountBytes) &&
  decide (h.size < h.caps.total) &&
  decide (bytesOf h.items + text.utf8ByteSize ≤ h.caps.totalBytes)

/-- Hold one stanza for `bare`, unless a cap would be passed. -/
def hold (h : Held) (bare text : String) : Held × Bool :=
  if h.fits bare text then
    ({ h with items := h.items ++ [⟨bare, h.nextSeq, text⟩], nextSeq := h.nextSeq + 1 }, true)
  else (h, false)

/-- Everything held for `bare`, oldest first, and the queue without it. -/
def release (h : Held) (bare : String) : List Item × Held :=
  (h.of bare, { h with items := h.items.filter (·.bare != bare) })

/-- Put back one item of the kept state, in its place by `seq`, whatever order the items are read
in. A start does not apply the caps: what was held stays held. -/
def restore (h : Held) (i : Item) : Held :=
  { h with items := h.items.filter (·.seq ≤ i.seq) ++ [i] ++ h.items.filter (·.seq > i.seq)
           nextSeq := max h.nextSeq (i.seq + 1) }

/-- The rate-limit key of a sending account. -/
def senderKeys (sender : Option String) : List String := sender.toList.map ("sender:" ++ ·)

/-- What became of a stanza a session sent. -/
inductive Verdict where
  /-- Held, with this `seq`. -/
  | held (seq : Nat)
  /-- Refused: this sender passed its rate. -/
  | tooFast
  /-- Refused: a cap would be passed. -/
  | full
  deriving Repr, DecidableEq, Inhabited

/-- Hold a stanza for `bare`, sent by `sender` (`none`: the server's own, from a MIX or GC3
service, with no rate). `rate` allows `maxFailures` stanzas per sender in `window` seconds. -/
def admit (h : Held) (rate : Limits) (senders : Failures) (now : Nat)
    (sender : Option String) (bare text : String) : Held × Failures × Verdict :=
  let keys := senderKeys sender
  if (senders.check rate now keys).isSome then (h, senders, .tooFast)
  else if h.fits bare text then
    ((hold h bare text).1, senders.record rate now keys, .held h.nextSeq)
  else (h, senders, .full)

/-! ## Theorems -/

theorem bytesOf_snoc (l : List Item) (i : Item) :
    bytesOf (l ++ [i]) = bytesOf l + i.text.utf8ByteSize := by
  simp [bytesOf, List.foldl_append]

/-- What `hold` stores for `bare`. -/
private theorem of_held (h : Held) (bare text : String) (hc : h.fits bare text = true) :
    (hold h bare text).1.of bare = h.of bare ++ [⟨bare, h.nextSeq, text⟩] := by
  simp [hold, hc, Held.of, List.filter_append]

/-- Holding never puts more than `perAccount` stanzas in the account's queue. -/
theorem hold_perAccount (h : Held) (bare text : String) (hinv : (h.of bare).length ≤ h.caps.perAccount) :
    ((hold h bare text).1.of bare).length ≤ h.caps.perAccount := by
  by_cases hc : h.fits bare text = true
  · rw [of_held h bare text hc]
    simp only [Held.fits, Bool.and_eq_true, decide_eq_true_eq] at hc
    have := hc.1.1.1
    simp only [List.length_append, List.length_singleton]
    omega
  · simp only [hold, hc, Bool.false_eq_true, ↓reduceIte]
    exact hinv

/-- Holding never puts more than `perAccountBytes` bytes in the account's queue. -/
theorem hold_perAccountBytes (h : Held) (bare text : String)
    (hinv : bytesOf (h.of bare) ≤ h.caps.perAccountBytes) :
    bytesOf ((hold h bare text).1.of bare) ≤ h.caps.perAccountBytes := by
  by_cases hc : h.fits bare text = true
  · rw [of_held h bare text hc, bytesOf_snoc]
    simp only [Held.fits, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  · simp only [hold, hc, Bool.false_eq_true, ↓reduceIte]
    exact hinv

/-- Holding never holds more than `total` stanzas. -/
theorem hold_total (h : Held) (bare text : String) (hinv : h.size ≤ h.caps.total) :
    (hold h bare text).1.size ≤ h.caps.total := by
  by_cases hc : h.fits bare text = true
  · simp only [hold, hc, ↓reduceIte]
    simp only [Held.fits, Bool.and_eq_true, decide_eq_true_eq] at hc
    have := hc.1.2
    simp only [Held.size, List.length_append, List.length_singleton] at this ⊢
    omega
  · simp only [hold, hc, Bool.false_eq_true, ↓reduceIte]
    exact hinv

/-- Holding never holds more than `totalBytes` bytes. -/
theorem hold_totalBytes (h : Held) (bare text : String) (hinv : bytesOf h.items ≤ h.caps.totalBytes) :
    bytesOf (hold h bare text).1.items ≤ h.caps.totalBytes := by
  by_cases hc : h.fits bare text = true
  · simp only [hold, hc, ↓reduceIte]
    simp only [Held.fits, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [bytesOf_snoc]
    exact hc.2
  · simp only [hold, hc, Bool.false_eq_true, ↓reduceIte]
    exact hinv

/-- A refusal changes nothing. -/
theorem hold_refused (h : Held) (bare text : String) (hr : (hold h bare text).2 = false) :
    (hold h bare text).1 = h := by
  by_cases hc : h.fits bare text = true
  · simp [hold, hc] at hr
  · simp [hold, hc]

/-- Holding keeps the caps. -/
theorem hold_caps (h : Held) (bare text : String) : (hold h bare text).1.caps = h.caps := by
  by_cases hc : h.fits bare text = true <;> simp [hold, hc]

/-- Holding adds exactly one item to the store, at the end: what a host writes is that item, and
no other item changes. -/
theorem hold_appends (h : Held) (bare text : String) (ho : (hold h bare text).2 = true) :
    (hold h bare text).1.items = h.items ++ [⟨bare, h.nextSeq, text⟩] := by
  by_cases hc : h.fits bare text = true
  · simp [hold, hc]
  · simp [hold, hc] at ho

/-- Release empties the account's queue: a delivered stanza is gone. -/
theorem release_empties (h : Held) (bare : String) : (release h bare).2.of bare = [] := by
  simp [release, Held.of, List.filter_filter]

/-- Release hands back exactly what was held, oldest first. -/
theorem release_returns (h : Held) (bare : String) : (release h bare).1 = h.of bare := rfl

/-- Release leaves every other account's queue as it was. -/
theorem release_others (h : Held) (bare other : String) (hne : other ≠ bare) :
    (release h bare).2.of other = h.of other := by
  simp only [release, Held.of, List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases hb : i.bare = other
  · simp [hb, hne]
  · simp [hb]

/-- A sender past its rate changes nothing, and is told so. -/
theorem admit_tooFast (h : Held) (rate : Limits) (senders : Failures) (now : Nat)
    (sender : Option String) (bare text : String)
    (hb : (senders.check rate now (senderKeys sender)).isSome = true) :
    admit h rate senders now sender bare text = (h, senders, .tooFast) := by
  simp [admit, hb]

/-- `admit` holds a stanza only as `hold` does, so every cap theorem above covers it. -/
theorem admit_held (h : Held) (rate : Limits) (senders : Failures) (now : Nat)
    (sender : Option String) (bare text : String) :
    (admit h rate senders now sender bare text).1 = h ∨
    (admit h rate senders now sender bare text).1 = (hold h bare text).1 := by
  unfold admit
  dsimp only
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-! ## Checks -/

#guard
  let h0 : Held := { caps := { perAccount := 2 } }
  let (h1, a) := hold h0 "r@x" "1"
  let (h2, b) := hold h1 "r@x" "2"
  let (h3, c) := hold h2 "r@x" "3"
  a && b && !c && h3.texts "r@x" == ["1", "2"] && h3 == h2

#guard
  let h0 : Held := {}
  let (h1, _) := hold h0 "r@x" "1"
  let (h2, _) := hold h1 "s@x" "2"
  let (out, h3) := release h2 "r@x"
  out.map (·.text) == ["1"] && h3.of "r@x" == [] && h3.texts "s@x" == ["2"] && h3.size == 1

#guard
  let h0 : Held := { caps := { total := 1 } }
  let (h1, a) := hold h0 "r@x" "1"
  let (_, b) := hold h1 "s@x" "2"
  a && !b

-- The byte caps: one account, then the server.
#guard
  let h0 : Held := { caps := { perAccountBytes := 3 } }
  let (h1, a) := hold h0 "r@x" "12"
  let (h2, b) := hold h1 "r@x" "34"
  let (_, c) := hold h2 "s@x" "56"
  a && !b && c
#guard
  let h0 : Held := { caps := { totalBytes := 3 } }
  let (h1, a) := hold h0 "r@x" "12"
  let (_, b) := hold h1 "s@x" "34"
  a && !b

-- A stanza gets the next number; a refused one uses none.
#guard
  let h0 : Held := { caps := { perAccount := 1 } }
  let (h1, _) := hold h0 "r@x" "1"
  let (h2, _) := hold h1 "r@x" "2"
  let (h3, _) := hold h2 "s@x" "3"
  h3.items.map (·.seq) == [1, 2]

-- Items read back in any order take their places; new stanzas number after them.
#guard
  let h0 : Held := {}
  let h1 := restore (restore (restore h0 ⟨"r@x", 10, "c"⟩) ⟨"r@x", 9, "b"⟩) ⟨"r@x", 0, "a"⟩
  let (h2, _) := hold h1 "r@x" "d"
  h2.texts "r@x" == ["a", "b", "c", "d"] && (h2.of "r@x").getLast?.map (·.seq) == some 11

-- Items of an old state, all numbered 0, keep the order they are read in.
#guard
  let h1 := restore (restore ({} : Held) ⟨"r@x", 0, "a"⟩) ⟨"r@x", 0, "b"⟩
  h1.texts "r@x" == ["a", "b"]

-- The sender's rate: two in the window, the third refused, a new window allows again; another
-- sender and the server's own stanzas are not affected.
#guard
  let rate : Limits := { maxFailures := 2, window := 10 }
  let (h1, f1, a) := admit {} rate {} 100 (some "m@x") "r@x" "1"
  let (h2, f2, b) := admit h1 rate f1 101 (some "m@x") "r@x" "2"
  let (h3, f3, c) := admit h2 rate f2 102 (some "m@x") "r@x" "3"
  let (h4, f4, d) := admit h3 rate f3 102 (some "n@x") "r@x" "4"
  let (h5, f5, e) := admit h4 rate f4 102 none "r@x" "5"
  let (h6, _, f) := admit h5 rate f5 110 (some "m@x") "r@x" "6"
  a == .held 1 && b == .held 2 && c == .tooFast && d == .held 3 && e == .held 4 && f == .held 5 &&
  h6.texts "r@x" == ["1", "2", "4", "5", "6"]

-- A full queue is `full`, and does not use the sender's rate.
#guard
  let rate : Limits := { maxFailures := 2, window := 10 }
  let h0 : Held := { caps := { perAccount := 0 } }
  let (_, f1, a) := admit h0 rate {} 100 (some "m@x") "r@x" "1"
  a == .full && f1.counters.isEmpty

end L4Factoidal.XMPP.Held
