import EthereumConsensus.ForkChoice.ChildSelection

/-!
# Finite stored-child enumeration and fuel-bounded LMD-GHOST traversal

Normative starting point: ethereum/consensus-specs@
d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md, get_head/get_node_children/get_weight.

Unlike the earlier selector, the caller does not hand this operation a list
of children: it enumerates direct children from ONE finite supplied block
inventory. The inventory itself is not authenticated or proved complete
against the network. A supplied viability oracle still represents the
unimplemented justified/finalized checkpoint filter. All such dependencies
are explicit; missing viability, malformed direct parent edges, duplicate
root entries, or unknown weight refuse the operation.

This is a bounded partial get_head, not production beacon fork choice.
-/

namespace EthereumConsensus.ForkChoice

/-- Functional lookup within the caller's finite, explicitly stored blocks.
    Duplicate keys are rejected by the selector before lookup. -/
def lookupStored (root : Nat) :
    List (Nat × BlockPosition) → Option BlockPosition
  | [] => none
  | (key, position) :: rest =>
      if key == root then some position else lookupStored root rest

/-- Scan every stored block for viable direct children of a known parent.
    Missing viability for a direct child is undecidable, not equivalent to
    a negative viability decision. A direct-parent edge with a non-increasing
    slot is malformed and refuses the entire scan. -/
def scanStoredChildren (parent parentSlot : Nat)
    (viable : Nat → Option Bool) :
    List (Nat × BlockPosition) → Option (List Nat)
  | [] => some []
  | (root, position) :: rest =>
      if position.parent == some parent then
        if decide (parentSlot < position.slot) then
          match viable root with
          | none => none
          | some true =>
              (scanStoredChildren parent parentSlot viable rest).map
                (fun children => root :: children)
          | some false => scanStoredChildren parent parentSlot viable rest
        else none
      else scanStoredChildren parent parentSlot viable rest

/-- One LMD-GHOST decision using the complete finite INVENTORY supplied at
    this boundary, rather than trusting a separate children array. The
    viability predicate is still externally supplied and unauthenticated.
    Option (Option Nat): refusal, known leaf, or selected child. -/
def selectStoredChild (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (parent ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) : Option (Option Nat) :=
  if decide ((entries.map Prod.fst).Nodup) then
    match lookupStored parent entries with
    | none => none
    | some position =>
        match scanStoredChildren parent position.slot viable entries with
        | none => none
        | some children =>
            selectCheckedChild store (fun root => lookupStored root entries)
              parent ancestryFuel roster boostRoot totalActiveBalance children
  else none

/-- Bounded iterative LMD-GHOST descent. The traversal budget counts
    decisions, including the final known-leaf decision. Exhaustion refuses.
    This recursion follows only a selected direct child with a higher slot,
    but the block inventory and viability classification are not authenticated. -/
def getHeadStored (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | budget + 1, current =>
      match selectStoredChild store entries viable current ancestryFuel
          roster boostRoot totalActiveBalance with
      | none => none
      | some none => some current
      | some (some child) =>
          getHeadStored store entries viable ancestryFuel roster
            boostRoot totalActiveBalance budget child

/-- The finite scan of an empty inventory is an admitted empty list,
    never a fabricated viable child. -/
theorem scanStored_empty (parent slot : Nat)
    (viable : Nat → Option Bool) :
    scanStoredChildren parent slot viable [] = some [] := by
  rfl

/-- A stored entry with a different parent does not enter this parent's
    candidate inventory. -/
theorem scanStored_non_child (parent slot root : Nat)
    (position : BlockPosition) (rest : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (h : (position.parent == some parent) = false) :
    scanStoredChildren parent slot viable ((root, position) :: rest) =
      scanStoredChildren parent slot viable rest := by
  simp [scanStoredChildren, h]

/-- An edge that claims this parent but does not advance in slot is
    rejected, rather than becoming an ordinary non-child. -/
theorem scanStored_bad_slot (parent slot root : Nat)
    (position : BlockPosition) (rest : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (hParent : (position.parent == some parent) = true)
    (hSlot : decide (slot < position.slot) = false) :
    scanStoredChildren parent slot viable ((root, position) :: rest) =
      none := by
  simp [scanStoredChildren, hParent, hSlot]

/-- Unknown viability of a direct child makes the whole candidate
    inventory indeterminate, not empty. -/
theorem scanStored_unknown_viability (parent slot root : Nat)
    (position : BlockPosition) (rest : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (hParent : (position.parent == some parent) = true)
    (hSlot : decide (slot < position.slot) = true)
    (hUnknown : viable root = none) :
    scanStoredChildren parent slot viable ((root, position) :: rest) =
      none := by
  simp [scanStoredChildren, hParent, hSlot, hUnknown]

/-- Every positively admitted direct child is prepended to the result
    of scanning ALL remaining stored entries. Thus an omitted child cannot
    be caused by a separate caller-supplied child list. This constructor
    theorem is relative to the supplied inventory and viability function. -/
theorem scanStored_includes_viable_head (parent slot root : Nat)
    (position : BlockPosition) (rest : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (hParent : (position.parent == some parent) = true)
    (hSlot : decide (slot < position.slot) = true)
    (hViable : viable root = some true) :
    scanStoredChildren parent slot viable ((root, position) :: rest) =
      (scanStoredChildren parent slot viable rest).map
        (fun children => root :: children) := by
  simp [scanStoredChildren, hParent, hSlot, hViable]

/-- Explicitly negative viability excludes only this entry. -/
theorem scanStored_excludes_unviable_head (parent slot root : Nat)
    (position : BlockPosition) (rest : List (Nat × BlockPosition))
    (viable : Nat → Option Bool)
    (hParent : (position.parent == some parent) = true)
    (hSlot : decide (slot < position.slot) = true)
    (hViable : viable root = some false) :
    scanStoredChildren parent slot viable ((root, position) :: rest) =
      scanStoredChildren parent slot viable rest := by
  simp [scanStoredChildren, hParent, hSlot, hViable]

/-- Duplicate root entries cannot distort the supplied store's lookup,
    children or scores. -/
theorem stored_duplicate_refused (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (parent ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat)
    (h : decide ((entries.map Prod.fst).Nodup) = false) :
    selectStoredChild store entries viable parent ancestryFuel
      roster boostRoot totalActiveBalance = none := by
  simp [selectStoredChild, h]

/-- Even a leaf result needs a known current block in the finite store. -/
theorem stored_unknown_parent_refused (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (parent ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat)
    (h : lookupStored parent entries = none) :
    selectStoredChild store entries viable parent ancestryFuel
      roster boostRoot totalActiveBalance = none := by
  simp [selectStoredChild, h]

/-- A missing viability classification never turns into a completed
    selection, including in an otherwise well-formed block inventory. -/
theorem stored_unknown_scan_refused (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (parent ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) (position : BlockPosition)
    (hLookup : lookupStored parent entries = some position)
    (hScan : scanStoredChildren parent position.slot viable entries = none) :
    selectStoredChild store entries viable parent ancestryFuel
      roster boostRoot totalActiveBalance = none := by
  simp [selectStoredChild, hLookup, hScan]

/-- Refinement bridge to the already executable checked-child implementation:
    once the inventory guards admit, the SAME Lean scorer and selection
    operate on exactly the list generated from the finite stored blocks. -/
theorem stored_selection_bridge (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (parent ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) (position : BlockPosition)
    (children : List Nat)
    (hUnique : decide ((entries.map Prod.fst).Nodup) = true)
    (hLookup : lookupStored parent entries = some position)
    (hScan : scanStoredChildren parent position.slot viable entries =
      some children) :
    selectStoredChild store entries viable parent ancestryFuel
      roster boostRoot totalActiveBalance =
    selectCheckedChild store (fun root => lookupStored root entries)
      parent ancestryFuel roster boostRoot totalActiveBalance children := by
  simp [selectStoredChild, hUnique, hLookup, hScan]

/-- An exhausted descent budget refuses instead of returning a
    partly traversed head. -/
theorem stored_head_zero_budget (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance current : Nat) :
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance 0 current = none := by
  rfl

/-- A confirmed leaf finishes at the current block. -/
theorem stored_head_leaf (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance current budget : Nat)
    (h : selectStoredChild store entries viable current ancestryFuel
      roster boostRoot totalActiveBalance = some none) :
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance (budget + 1) current =
      some current := by
  simp [getHeadStored, h]

/-- An indeterminate one-step selection stops the entire descent. -/
theorem stored_head_unknown (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance current budget : Nat)
    (h : selectStoredChild store entries viable current ancestryFuel
      roster boostRoot totalActiveBalance = none) :
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance (budget + 1) current = none := by
  simp [getHeadStored, h]

/-- A selected child advances by exactly one structural recursion step
    and uses the same finite inventory and LMD scorer. -/
theorem stored_head_child (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance current budget child : Nat)
    (h : selectStoredChild store entries viable current ancestryFuel
      roster boostRoot totalActiveBalance = some (some child)) :
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance (budget + 1) current =
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance budget child := by
  simp [getHeadStored, h]

/-- Refusing an invalid attestation cannot modify the stored-child result;
    no separate, unchecked vote-store copy is used. -/
theorem stored_head_rejected_update (store : VoteStore)
    (entries : List (Nat × BlockPosition))
    (viable : Nat → Option Bool) (ancestryFuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance budget current validator : Nat)
    (candidate : LatestMessage) :
    getHeadStored (updateStore store validator candidate false)
      entries viable ancestryFuel roster boostRoot
      totalActiveBalance budget current =
    getHeadStored store entries viable ancestryFuel roster
      boostRoot totalActiveBalance budget current := by
  rw [invalid_refused]

private def testEntries : List (Nat × BlockPosition) := [
  (0, ⟨0, none⟩),
  (1, ⟨1, some 0⟩),
  (2, ⟨1, some 0⟩),
  (3, ⟨2, some 1⟩)
]

private def testStore : VoteStore := {
  latest := fun _ => none
  equivocating := fun _ => false
}

private def allViable : Nat → Option Bool := fun _ => some true
private def excludeTwo : Nat → Option Bool :=
  fun root => some (root != 2)
private def unknownTwo : Nat → Option Bool :=
  fun root => if root == 2 then none else some true

#guard lookupStored 0 testEntries == some ⟨0, none⟩
#guard lookupStored 3 testEntries == some ⟨2, some 1⟩
#guard lookupStored 99 testEntries == none
#guard scanStoredChildren 0 0 allViable testEntries == some [1, 2]
#guard scanStoredChildren 0 0 excludeTwo testEntries == some [1]
#guard scanStoredChildren 0 0 unknownTwo testEntries == none
#guard scanStoredChildren 1 1 allViable testEntries == some [3]
#guard scanStoredChildren 2 1 allViable testEntries == some []
#guard scanStoredChildren 0 0 allViable
  [(0, ⟨0, none⟩), (1, ⟨0, some 0⟩)] == none
#guard selectStoredChild testStore testEntries allViable 0 4
  [] none 3200 == some (some 2)
#guard selectStoredChild testStore testEntries excludeTwo 0 4
  [] none 3200 == some (some 1)
#guard selectStoredChild testStore testEntries unknownTwo 0 4
  [] none 3200 == none
#guard selectStoredChild testStore testEntries allViable 99 4
  [] none 3200 == none
#guard selectStoredChild testStore
  (testEntries ++ [(2, ⟨10, some 0⟩)]) allViable 0 4
  [] none 3200 == none
#guard getHeadStored testStore testEntries allViable 4 [] none 3200
  0 0 == none
#guard getHeadStored testStore testEntries allViable 4 [] none 3200
  1 0 == none
#guard getHeadStored testStore testEntries allViable 4 [] none 3200
  2 0 == some 2
#guard getHeadStored testStore testEntries excludeTwo 4 [] none 3200
  2 0 == none
#guard getHeadStored testStore testEntries excludeTwo 4 [] none 3200
  3 0 == some 3
#guard getHeadStored testStore testEntries unknownTwo 4 [] none 3200
  5 0 == none
#guard getHeadStored testStore testEntries allViable 4 [] none 3200
  1 2 == some 2
#guard getHeadStored testStore testEntries allViable 4 [] none 3200
  5 99 == none

#print axioms EthereumConsensus.ForkChoice.scanStored_empty
#print axioms EthereumConsensus.ForkChoice.scanStored_non_child
#print axioms EthereumConsensus.ForkChoice.scanStored_bad_slot
#print axioms EthereumConsensus.ForkChoice.scanStored_unknown_viability
#print axioms EthereumConsensus.ForkChoice.scanStored_includes_viable_head
#print axioms EthereumConsensus.ForkChoice.scanStored_excludes_unviable_head
#print axioms EthereumConsensus.ForkChoice.stored_duplicate_refused
#print axioms EthereumConsensus.ForkChoice.stored_unknown_parent_refused
#print axioms EthereumConsensus.ForkChoice.stored_unknown_scan_refused
#print axioms EthereumConsensus.ForkChoice.stored_selection_bridge
#print axioms EthereumConsensus.ForkChoice.stored_head_zero_budget
#print axioms EthereumConsensus.ForkChoice.stored_head_leaf
#print axioms EthereumConsensus.ForkChoice.stored_head_unknown
#print axioms EthereumConsensus.ForkChoice.stored_head_child
#print axioms EthereumConsensus.ForkChoice.stored_head_rejected_update

end EthereumConsensus.ForkChoice
