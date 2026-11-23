import EthereumConsensus.ForkChoice.ProposerScore

/-!
# Bounded, fail-closed fork-choice ancestry from supplied block positions

Normative source: ethereum/consensus-specs@
d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md, get_ancestor, is_ancestor and get_weight.

The spec follows parent_root while slot > target slot, and compares the
resulting node against the proposed ancestor. This executable adapter uses an
explicit traversal budget and rejects absent blocks, dangling parents and
non-decreasing parent slots. Inconclusive ancestry is NONE, not FALSE.
The block lookup, roots, slots, roster and checkpoint balances are trusted
inputs: this is not authenticated SSZ/BLS or a complete beacon Store.
-/

namespace EthereumConsensus.ForkChoice

/-- A supplied fork-choice block position, NOT an authenticated BeaconBlock.
    A missing parent is permitted at an anchor but fails if traversal needs it. -/
structure BlockPosition where
  slot : Nat
  parent : Option Nat
  deriving Repr, BEq

/-- Guarded version of the spec's get_ancestor. Its result is unknown if the
    budget ends, lookup fails, or a traversed parent is not strictly older.
    Nat roots are temporary identifiers; no hash integrity is claimed. -/
def ancestorAtSlot (blocks : Nat → Option BlockPosition)
    (supported targetSlot : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      match blocks supported with
      | none => none
      | some block =>
          if block.slot ≤ targetSlot then some supported
          else
            match block.parent with
            | none => none
            | some parent =>
                match blocks parent with
                | none => none
                | some previous =>
                    if previous.slot < block.slot then
                      ancestorAtSlot blocks parent targetSlot fuel
                    else none

/-- A three-way is_ancestor: some true / some false / none (unresolved).
    The supported descendant is the FIRST argument, candidate ancestor second.
    The candidate block must exist even if its slot would not be traversed. -/
def checkedDescends (blocks : Nat → Option BlockPosition)
    (supported candidate fuel : Nat) : Option Bool :=
  match blocks candidate with
  | none => none
  | some target =>
      (ancestorAtSlot blocks supported target.slot fuel).map
        (fun reached => reached == candidate)

/-- Only ancestry queries which could contribute a validator's balance must
    be resolved. An equivocator or absent vote contributes no ancestry query. -/
def rosterQueriesKnown (store : VoteStore)
    (blocks : Nat → Option BlockPosition) (node fuel : Nat) :
    List EligibleWeight → Bool
  | [] => true
  | (validator, _) :: rest =>
      let known :=
        if store.equivocating validator then true
        else
          match store.latest validator with
          | none => true
          | some message =>
              (checkedDescends blocks message.root node fuel).isSome
      known && rosterQueriesKnown store blocks node fuel rest

/-- Proposer boost requires the same checked ancestry, only if present. -/
def boostQueryKnown (blocks : Nat → Option BlockPosition)
    (node fuel : Nat) : Option Nat → Bool
  | none => true
  | some root => (checkedDescends blocks root node fuel).isSome

/-- Reuses the executable LMD scorer and Lean-computed proposer amount ONLY
    after resolving every relevant ancestry query. In particular, missing
    block witnesses do not become a false vote or a completed zero score. -/
def weightWithCheckedAncestry (store : VoteStore)
    (blocks : Nat → Option BlockPosition) (node fuel : Nat)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) : Option Nat :=
  if uniqueRoster roster then
    if rosterQueriesKnown store blocks node fuel roster &&
        boostQueryKnown blocks node fuel boostRoot then
      weightWithComputedBoost store
        (fun supported candidate =>
          checkedDescends blocks supported candidate fuel == some true)
        node roster boostRoot totalActiveBalance
    else none
  else none

/-- Zero fuel never returns a fabricated known ancestry verdict. -/
theorem checkedDescends_zero_fuel (blocks : Nat → Option BlockPosition)
    (supported candidate : Nat) :
    checkedDescends blocks supported candidate 0 = none := by
  cases h : blocks candidate with
  | none => simp [checkedDescends, h]
  | some position => simp [checkedDescends, h, ancestorAtSlot]

/-- An unknown candidate does not silently count as a non-ancestor. -/
theorem checkedDescends_unknown_candidate
    (blocks : Nat → Option BlockPosition) (supported candidate fuel : Nat)
    (h : blocks candidate = none) :
    checkedDescends blocks supported candidate fuel = none := by
  simp [checkedDescends, h]

/-- When a known supported node is already at or below the requested slot,
    get_ancestor stops there for every positive traversal budget. -/
theorem ancestorAtSlot_at_or_below
    (blocks : Nat → Option BlockPosition)
    (supported target slot fuel : Nat) (parent : Option Nat)
    (h : blocks supported = some ⟨slot, parent⟩)
    (hle : slot ≤ target) :
    ancestorAtSlot blocks supported target (fuel + 1) = some supported := by
  simp [ancestorAtSlot, h, hle]

/-- Every known block is its own ancestor with a positive budget. -/
theorem checkedDescends_self
    (blocks : Nat → Option BlockPosition)
    (node slot fuel : Nat) (parent : Option Nat)
    (h : blocks node = some ⟨slot, parent⟩) :
    checkedDescends blocks node node (fuel + 1) = some true := by
  simp [checkedDescends, ancestorAtSlot, h]

/-- Missing parent on a required traversal is an explicit refusal. -/
theorem ancestorAtSlot_missing_parent
    (blocks : Nat → Option BlockPosition)
    (supported target slot fuel : Nat)
    (h : blocks supported = some ⟨slot, none⟩)
    (hAbove : target < slot) :
    ancestorAtSlot blocks supported target (fuel + 1) = none := by
  simp [ancestorAtSlot, h, Nat.not_le.mpr hAbove]

/-- An equal-slot or forward-slot parent cannot be followed: this is a
    finite rejection of an invalid parent edge, not a proof of its validity. -/
theorem ancestorAtSlot_non_decreasing_parent
    (blocks : Nat → Option BlockPosition)
    (supported parent target slot parentSlot fuel : Nat)
    (next : Option Nat)
    (h : blocks supported = some ⟨slot, some parent⟩)
    (hp : blocks parent = some ⟨parentSlot, next⟩)
    (hAbove : target < slot) (hOrder : slot ≤ parentSlot) :
    ancestorAtSlot blocks supported target (fuel + 1) = none := by
  simp [ancestorAtSlot, h, hp, Nat.not_le.mpr hAbove,
    Nat.not_lt.mpr hOrder]

/-- The guarded bridge retains the existing duplicate-roster refusal. -/
theorem checkedWeight_duplicate_refused
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (node fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (h : uniqueRoster roster = false) :
    weightWithCheckedAncestry store blocks node fuel roster
      boostRoot totalActiveBalance = none := by
  simp [weightWithCheckedAncestry, h]

/-- Missing proposer ancestry never silently drops a potentially positive
    boost and reports a completed score instead. -/
theorem checkedWeight_unknown_boost_refused
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (node fuel : Nat) (roster : List EligibleWeight)
    (boostRoot totalActiveBalance : Nat)
    (h : checkedDescends blocks boostRoot node fuel = none) :
    weightWithCheckedAncestry store blocks node fuel roster
      (some boostRoot) totalActiveBalance = none := by
  simp [weightWithCheckedAncestry, boostQueryKnown, h]

/-- Direct refinement bridge to the EXISTING executable scoring function:
    only the preflight for undecidable ancestry is new. This is not a proof
    that the caller supplied authenticated blocks or correct validator data. -/
theorem checkedWeight_agrees_when_known
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (node fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (hRoster : uniqueRoster roster = true)
    (hVotes : rosterQueriesKnown store blocks node fuel roster = true)
    (hBoost : boostQueryKnown blocks node fuel boostRoot = true) :
    weightWithCheckedAncestry store blocks node fuel roster
      boostRoot totalActiveBalance =
    weightWithComputedBoost store
      (fun supported candidate =>
        checkedDescends blocks supported candidate fuel == some true)
      node roster boostRoot totalActiveBalance := by
  simp [weightWithCheckedAncestry, hRoster, hVotes, hBoost]

/-- A rejected message update cannot modify the guarded score. -/
theorem checkedWeight_rejected_update
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (node fuel validator : Nat) (candidate : LatestMessage)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) :
    weightWithCheckedAncestry
      (updateStore store validator candidate false) blocks node fuel
      roster boostRoot totalActiveBalance =
    weightWithCheckedAncestry store blocks node fuel
      roster boostRoot totalActiveBalance := by
  rw [invalid_refused]

private def chain : Nat → Option BlockPosition
  | 0 => some ⟨0, none⟩
  | 1 => some ⟨1, some 0⟩
  | 2 => some ⟨3, some 1⟩
  | 3 => some ⟨4, some 1⟩
  | _ => none

private def badEdge : Nat → Option BlockPosition
  | 0 => some ⟨0, none⟩
  | 7 => some ⟨7, some 8⟩
  | 8 => some ⟨9, some 0⟩
  | _ => none

private def sampleStore : VoteStore := {
  latest := fun i => if i == 0 then some ⟨1, 2⟩ else none
  equivocating := fun _ => false
}

#guard checkedDescends chain 2 1 3 == some true
#guard checkedDescends chain 2 0 3 == some true
#guard checkedDescends chain 2 3 3 == some false
#guard checkedDescends chain 3 2 3 == some false
#guard checkedDescends chain 3 1 3 == some true
#guard checkedDescends chain 2 1 0 == none
#guard checkedDescends chain 2 0 2 == none
#guard checkedDescends chain 2 7 4 == none
#guard checkedDescends chain 7 1 4 == none
#guard checkedDescends badEdge 7 0 4 == none
#guard checkedDescends chain 1 1 1 == some true
#guard weightWithCheckedAncestry sampleStore chain 1 4
  [(0, 10)] none 3200 == some 10
#guard weightWithCheckedAncestry sampleStore chain 1 4
  [(0, 10)] (some 3) 3200 == some 50
#guard weightWithCheckedAncestry sampleStore chain 1 1
  [(0, 10)] (some 3) 3200 == none
#guard weightWithCheckedAncestry sampleStore chain 1 4
  [(0, 10), (0, 30)] none 3200 == none
#guard weightWithCheckedAncestry sampleStore chain 7 4
  [(0, 10)] none 3200 == none

#print axioms EthereumConsensus.ForkChoice.checkedDescends_zero_fuel
#print axioms EthereumConsensus.ForkChoice.checkedDescends_unknown_candidate
#print axioms EthereumConsensus.ForkChoice.ancestorAtSlot_at_or_below
#print axioms EthereumConsensus.ForkChoice.checkedDescends_self
#print axioms EthereumConsensus.ForkChoice.ancestorAtSlot_missing_parent
#print axioms EthereumConsensus.ForkChoice.ancestorAtSlot_non_decreasing_parent
#print axioms EthereumConsensus.ForkChoice.checkedWeight_duplicate_refused
#print axioms EthereumConsensus.ForkChoice.checkedWeight_unknown_boost_refused
#print axioms EthereumConsensus.ForkChoice.checkedWeight_agrees_when_known
#print axioms EthereumConsensus.ForkChoice.checkedWeight_rejected_update

end EthereumConsensus.ForkChoice
