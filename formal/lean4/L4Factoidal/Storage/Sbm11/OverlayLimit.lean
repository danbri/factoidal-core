/-
L4Factoidal.Storage.Sbm11.OverlayLimit — the size limit of the delta log of an
SBM11 generation (stage 5,
https://github.com/danbri/factoidal/issues/851).

Every open of a generation replays its log into an overlay held in memory, so
the cost of an open and the memory of a reader grow with the log until
`l4sbm11 compact` folds it into a new generation. A limit makes the writer
refuse a request that would take the log past a size the operator chose, so
that the log does not grow until an open takes minutes or does not fit in
memory. The limit is in log entries, in bytes of the log file, or both. It is
off by default: `Limit` with no field set never refuses (`exceeded_none`).

`exceeded l entries bytes` is true exactly when one set limit is below the
size: a log that holds exactly the limit is within it (`exceeded_iff`). The
writer calls it with the sizes the log WOULD have after the request.

Nothing compacts the log by itself: a refused request is repeated by the caller
after `l4sbm11 compact` and `l4sbm11 activate`
(https://github.com/danbri/factoidal/issues/803 item 4; the expected failure
`xfail-auto-compaction` in tests/sbm11/update_where.sh).
-/
namespace L4Factoidal.Storage.Sbm11.OverlayLimit

/-- At most this many log entries, at most this many bytes of log (`none`: no
    limit on that size). -/
structure Limit where
  maxEntries : Option Nat := none
  maxBytes : Option Nat := none
  deriving Repr, DecidableEq

/-- Is a limit set? -/
def Limit.isSet (l : Limit) : Bool := l.maxEntries.isSome || l.maxBytes.isSome

/-- Do `entries` log entries or `bytes` bytes of log pass a set limit? -/
def Limit.exceeded (l : Limit) (entries bytes : Nat) : Bool :=
  (match l.maxEntries with | some m => decide (m < entries) | none => false) ||
  (match l.maxBytes with | some m => decide (m < bytes) | none => false)

/-- No limit set: no size passes it. -/
theorem exceeded_none (entries bytes : Nat) : ({} : Limit).exceeded entries bytes = false := by
  simp [Limit.exceeded]

/-- A size passes the limit exactly when it is above one of the limits that are
    set. -/
theorem exceeded_iff (l : Limit) (entries bytes : Nat) :
    l.exceeded entries bytes = true ↔
      (∃ m, l.maxEntries = some m ∧ m < entries) ∨ (∃ m, l.maxBytes = some m ∧ m < bytes) := by
  unfold Limit.exceeded
  cases h1 : l.maxEntries <;> cases h2 : l.maxBytes <;> simp

/-- A larger log passes every limit that a smaller log passes. -/
theorem exceeded_mono (l : Limit) {e1 e2 b1 b2 : Nat} (he : e1 ≤ e2) (hb : b1 ≤ b2)
    (h : l.exceeded e1 b1 = true) : l.exceeded e2 b2 = true := by
  rw [exceeded_iff] at h ⊢
  rcases h with ⟨m, hm, hlt⟩ | ⟨m, hm, hlt⟩
  · exact Or.inl ⟨m, hm, by omega⟩
  · exact Or.inr ⟨m, hm, by omega⟩

#guard ({} : Limit).exceeded 1000000 1000000000 == false
#guard ({ maxEntries := some 5 } : Limit).exceeded 5 0 == false
#guard ({ maxEntries := some 5 } : Limit).exceeded 6 0 == true
#guard ({ maxBytes := some 100 } : Limit).exceeded 0 100 == false
#guard ({ maxBytes := some 100 } : Limit).exceeded 0 101 == true
#guard ({ maxEntries := some 5, maxBytes := some 100 } : Limit).exceeded 5 101 == true
#guard ({ maxEntries := some 5, maxBytes := some 100 } : Limit).exceeded 6 100 == true
#guard ({ maxEntries := some 5, maxBytes := some 100 } : Limit).exceeded 5 100 == false
#guard ({ maxEntries := some 0 } : Limit).exceeded 0 0 == false
#guard ({ maxEntries := some 0 } : Limit).exceeded 1 0 == true

#print axioms exceeded_none
#print axioms exceeded_iff
#print axioms exceeded_mono

end L4Factoidal.Storage.Sbm11.OverlayLimit
