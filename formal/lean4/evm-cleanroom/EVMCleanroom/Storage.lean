import Std

/-!
# One-account EVM persistent storage and London/Prague SSTORE metering

This is a **single-account execution-frame slice**, not a world-state trie,
transaction scheduler, or nested-call journal. Keys and values are supplied
by bounded 256-bit EVM words in Core. Original values are immutable for the
whole *transaction*, even when an earlier frame has written the slot.
Warmth is transaction-scoped; a caller must carry it across successful and
reverted child calls according to the fork's rules.

SSTORE constants are those after EIP-2200, EIP-2929 and EIP-3529:
  WARM_STORAGE_READ_COST = 100
  COLD_SLOAD_COST = 2100
  SSTORE_SET_GAS = 20000
  SSTORE_RESET_GAS = 2900
  SSTORE_CLEARS_SCHEDULE = 4800
No negative refund is truncated: EIP-2200 permits a *frame* refund
counter to become negative, so it is an Int.

Sources: https://eips.ethereum.org/EIPS/eip-2200
         https://eips.ethereum.org/EIPS/eip-2929
         https://eips.ethereum.org/EIPS/eip-3529
-/

namespace EVMCleanroom

structure Storage where
  original : Nat → Nat := fun _ => 0
  current : Nat → Nat := fun _ => 0
  warm : Nat → Bool := fun _ => false
  refund : Int := 0
  /-- EIP-1153 transient storage of this account for the current transaction.
      It is journalled with the frame like `current` and starts empty at
      every transaction boundary. -/
  transient : Nat → Nat := fun _ => 0

def Storage.empty : Storage := {}

/-- A fixture entry: the original and current values initially agree. -/
def Storage.withInitial (key value : Nat) : Storage :=
  { original := fun k => if k = key then value else 0
    current := fun k => if k = key then value else 0 }

def Storage.readCost (s : Storage) (key : Nat) : Nat :=
  if s.warm key then 100 else 2100

/-- Warm one slot. Actual execution commits this only after gas validation. -/
def Storage.touch (s : Storage) (key : Nat) : Storage :=
  { s with warm := fun k => if k = key then true else s.warm k }

/-- Change the value and signed refund, retaining transaction-original
    values. Gas and static-mode checks happen before this is committed. -/
def Storage.store (s : Storage) (key value : Nat) (delta : Int) : Storage :=
  { s with
    current := fun k => if k = key then value else s.current k
    warm := fun k => if k = key then true else s.warm k
    refund := s.refund + delta }

structure StoreCharge where
  gas : Nat
  refundDelta : Int
  deriving Repr, DecidableEq

/-- EIP-2200 net-metering adjusted by EIP-2929 and EIP-3529.
    Includes 2100 cold-slot surcharge on SSTORE when not warm.
    The 2300-gas stipend rule is checked by Core *before* this charge. -/
def Storage.storeCharge (s : Storage) (key next : Nat) : StoreCharge :=
  let original := s.original key
  let current := s.current key
  let base : Nat :=
    if current == next then 100
    else if original == current then
      if original == 0 then 20000 else 2900
    else 100
  let delta : Int :=
    if current == next then 0
    else if original == current then
      if original != 0 && next == 0 then 4800 else 0
    else
      (if original != 0 && current == 0 then -4800 else 0) +
      (if original != 0 && next == 0 then 4800 else 0) +
      (if original == next then
        if original == 0 then 19900 else 2800
       else 0)
  { gas := base + (if s.warm key then 0 else 2100)
    refundDelta := delta }

/-- Stores affect only the requested slot, regardless of intervening writes. -/
theorem Storage.store_read_same (s : Storage) (key value : Nat) (delta : Int) :
    (s.store key value delta).current key = value := by
  simp [Storage.store]

theorem Storage.store_read_other (s : Storage) (key other value : Nat)
    (delta : Int) (h : other ≠ key) :
    (s.store key value delta).current other = s.current other := by
  simp [Storage.store, h]

/-- The transaction-original value is immutable under any local store. -/
theorem Storage.store_original (s : Storage) (key other value : Nat)
    (delta : Int) :
    (s.store key value delta).original other = s.original other := rfl

/-- A store always warms its slot; reading it again costs 100 gas. -/
theorem Storage.store_warm_read (s : Storage) (key value : Nat)
    (delta : Int) :
    (s.store key value delta).readCost key = 100 := by
  simp [Storage.store, Storage.readCost]

theorem Storage.touch_warm_read (s : Storage) (key : Nat) :
    (s.touch key).readCost key = 100 := by
  simp [Storage.touch, Storage.readCost]

/-- Warming a slot cannot alter its stored content or prior refund. -/
theorem Storage.touch_current_unchanged (s : Storage) (key other : Nat) :
    (s.touch key).current other = s.current other := rfl

theorem Storage.touch_refund_unchanged (s : Storage) (key : Nat) :
    (s.touch key).refund = s.refund := rfl

/-- A same-value write never changes the signed refund counter. -/
theorem Storage.noop_refund (s : Storage) (key : Nat) :
    (s.storeCharge key (s.current key)).refundDelta = 0 := by
  simp [Storage.storeCharge]

/-- The storage update preserves the exact signed refund increment. -/
theorem Storage.store_refund_exact (s : Storage) (key value : Nat)
    (delta : Int) :
    (s.store key value delta).refund = s.refund + delta := rfl

-- Published EIP-2929 / EIP-3529 pricing examples.
#guard (Storage.empty.readCost 0) == 2100
#guard ((Storage.empty.touch 0).readCost 0) == 100
#guard (Storage.empty.storeCharge 0 1).gas == 22100
#guard (Storage.empty.storeCharge 0 0).gas == 2200
#guard (Storage.empty.storeCharge 0 1).refundDelta == 0
#guard ((Storage.empty.store 0 1 0).storeCharge 0 0).gas == 100
#guard ((Storage.empty.store 0 1 0).storeCharge 0 0).refundDelta == 19900
#guard ((Storage.withInitial 0 7).storeCharge 0 0).gas == 5000
#guard ((Storage.withInitial 0 7).storeCharge 0 0).refundDelta == 4800
#guard (((Storage.withInitial 0 7).store 0 0 4800).storeCharge 0 7).refundDelta == -2000

#print axioms Storage.store_read_same
#print axioms Storage.store_read_other
#print axioms Storage.store_original
#print axioms Storage.store_warm_read
#print axioms Storage.touch_warm_read
#print axioms Storage.noop_refund
#print axioms Storage.store_refund_exact

end EVMCleanroom
