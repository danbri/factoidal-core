import EthereumConsensus.ForkChoice.CheckedAncestry

/-!
# Finite, fail-closed LMD-GHOST child selection

Pinned normative source: ethereum/consensus-specs@
d2021d2719235f0df4726a1d330502cb15aa8ea3,
specs/phase0/fork-choice.md, get_head: choose the maximum pair
(get_weight(child), child.root) among filtered direct children.

This is ONE selection step, not the complete get_head loop or viability
filter. The caller supplies the entire finite, already filtered set of
viable children and an unauthenticated block lookup, vote store and balance.
For this provisional Nat root representation, larger Nat is used as the
lexicographic tie-break: an eventual 32-byte Root codec must prove the
correspondence to bytewise lexicographic order. A missing weight MUST
refuse the selection rather than silently discard a child.
-/

namespace EthereumConsensus.ForkChoice

/-- Finite maximum of (score, root), with a three-way result:
    none = unknown/refused; some none = empty candidate set;
    some (some (root, score)) = selected candidate. A missing score of
    ANY listed candidate refuses the complete decision. -/
def selectBestScored (getScore : Nat → Option Nat) :
    List Nat → Option (Option (Nat × Nat))
  | [] => some none
  | root :: rest =>
      match getScore root, selectBestScored getScore rest with
      | some score, some none => some (some (root, score))
      | some score, some (some (other, otherScore)) =>
          if otherScore < score ∨
              (otherScore = score ∧ other < root) then
            some (some (root, score))
          else
            some (some (other, otherScore))
      | _, _ => none

/-- A direct-child edge must have both nodes present, a matching parent
    root and a strictly increasing slot. No hash or signature is checked. -/
def checkedDirectChild (blocks : Nat → Option BlockPosition)
    (parent child : Nat) : Bool :=
  match blocks parent, blocks child with
  | some parentBlock, some childBlock =>
      childBlock.parent == some parent &&
        decide (parentBlock.slot < childBlock.slot)
  | _, _ => false

/-- Select one LMD-GHOST step from an externally supplied complete list
    of viable children. Rejects absent parent, duplicate roots, invalid
    edges and unresolved weights. Uses the EXISTING executable checked
    ancestry and proposer-score bridge without duplicating weight rules. -/
def selectCheckedChild (store : VoteStore)
    (blocks : Nat → Option BlockPosition)
    (parent fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (children : List Nat) : Option (Option Nat) :=
  if (blocks parent).isSome &&
      decide children.Nodup &&
      children.all (checkedDirectChild blocks parent) then
    (selectBestScored
      (fun child => weightWithCheckedAncestry store blocks child fuel
        roster boostRoot totalActiveBalance) children).map
      (fun result => result.map Prod.fst)
  else none

/-- Says: the finite max explicitly represents a known empty candidate
    set, unlike an incomplete weight. Does not validate list completeness. -/
theorem bestScored_empty (score : Nat → Option Nat) :
    selectBestScored score [] = some none := by
  rfl

/-- Says: one known candidate is selected by the executable accumulator.
    Does not establish ancestry, viability or authenticated scoring. -/
theorem bestScored_single (score : Nat → Option Nat)
    (root amount : Nat) (h : score root = some amount) :
    selectBestScored score [root] = some (some (root, amount)) := by
  simp [selectBestScored, h]

/-- Says: an unresolved candidate is not silently excluded when comparing
    scores. Does not guarantee that the score oracle itself is complete. -/
theorem bestScored_unknown_refused (score : Nat → Option Nat)
    (root : Nat) (rest : List Nat) (h : score root = none) :
    selectBestScored score (root :: rest) = none := by
  simp [selectBestScored, h]

/-- Says: a missing score for ANY member of the candidate inventory,
    not only the head, makes the complete selection indeterminate.
    Does not establish the completeness of the supplied candidate list. -/
theorem bestScored_any_unknown_refused (score : Nat → Option Nat) :
    ∀ (roots : List Nat) (target : Nat),
      target ∈ roots → score target = none →
      selectBestScored score roots = none := by
  intro roots
  induction roots with
  | nil =>
      intro target hMember _
      cases hMember
  | cons head tail ih =>
      intro target hMember hMissing
      simp only [List.mem_cons] at hMember
      cases hMember with
      | inl hEqual =>
          subst target
          exact bestScored_unknown_refused score head tail hMissing
      | inr hTail =>
          have hRest := ih target hTail hMissing
          cases hHead : score head with
          | none => simp [selectBestScored, hHead]
          | some amount => simp [selectBestScored, hHead, hRest]

/-- Says: equal weights favour the larger abstract root, irrespective of
    list order for this two-child case. Does not prove the Nat/Root codec. -/
theorem bestScored_tie_break (score : Nat → Option Nat)
    (smaller larger amount : Nat) (hlt : smaller < larger)
    (hs : score smaller = some amount)
    (hl : score larger = some amount) :
    selectBestScored score [smaller, larger] =
      some (some (larger, amount)) := by
  have hNot : ¬ larger < smaller := Nat.not_lt.mpr (Nat.le_of_lt hlt)
  simp [selectBestScored, hs, hl, hNot]

/-- Says: an unknown parent refuses a decision, even for an empty list.
    Does not authenticate a known block. -/
theorem checkedChild_unknown_parent_refused
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (parent fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (children : List Nat) (h : blocks parent = none) :
    selectCheckedChild store blocks parent fuel roster boostRoot
      totalActiveBalance children = none := by
  simp [selectCheckedChild, h]

/-- Says: a duplicate advertised child cannot distort the argmax.
    Does not establish a complete list of all viable children. -/
theorem checkedChild_duplicate_refused
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (parent fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (children : List Nat) (h : decide children.Nodup = false) :
    selectCheckedChild store blocks parent fuel roster boostRoot
      totalActiveBalance children = none := by
  simp [selectCheckedChild, h]

/-- Says: an invalid direct-parent/slot edge refuses the whole candidate
    set rather than removing the bad child and changing the winner. -/
theorem checkedChild_invalid_edge_refused
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (parent fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (children : List Nat)
    (h : children.all (checkedDirectChild blocks parent) = false) :
    selectCheckedChild store blocks parent fuel roster boostRoot
      totalActiveBalance children = none := by
  simp [selectCheckedChild, h]

/-- Says: when the explicit admission guards hold, the executable
    selector uses EXACTLY the existing checked LMD weight on every child.
    Does not prove viability or authenticated inputs. -/
theorem checkedChild_agrees_when_admitted
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (parent fuel : Nat) (roster : List EligibleWeight)
    (boostRoot : Option Nat) (totalActiveBalance : Nat)
    (children : List Nat)
    (hParent : (blocks parent).isSome = true)
    (hUnique : decide children.Nodup = true)
    (hEdges : children.all (checkedDirectChild blocks parent) = true) :
    selectCheckedChild store blocks parent fuel roster boostRoot
      totalActiveBalance children =
    (selectBestScored
      (fun child => weightWithCheckedAncestry store blocks child fuel
        roster boostRoot totalActiveBalance) children).map
      (fun result => result.map Prod.fst) := by
  simp [selectCheckedChild, hParent, hUnique, hEdges]

/-- Says: rejecting an unadmitted vote update cannot change the child
    selection. Does not check a positive admission or a valid signature. -/
theorem checkedChild_rejected_update
    (store : VoteStore) (blocks : Nat → Option BlockPosition)
    (parent fuel validator : Nat) (candidate : LatestMessage)
    (roster : List EligibleWeight) (boostRoot : Option Nat)
    (totalActiveBalance : Nat) (children : List Nat) :
    selectCheckedChild (updateStore store validator candidate false)
      blocks parent fuel roster boostRoot totalActiveBalance children =
    selectCheckedChild store blocks parent fuel roster boostRoot
      totalActiveBalance children := by
  rw [invalid_refused]

private def sampleBlocks : Nat → Option BlockPosition
  | 0 => some ⟨0, none⟩
  | 1 => some ⟨1, some 0⟩
  | 2 => some ⟨2, some 0⟩
  | 3 => some ⟨3, some 1⟩
  | 4 => some ⟨4, some 2⟩
  | 7 => some ⟨7, some 8⟩
  | _ => none

private def sampleStore : VoteStore := {
  latest := fun i =>
    if i == 0 then some ⟨1, 3⟩
    else if i == 1 then some ⟨1, 4⟩
    else none
  equivocating := fun _ => false
}
private def sampleRoster : List EligibleWeight := [(0, 10), (1, 10)]

#guard selectBestScored (fun _ => some 10) [] == some none
#guard selectBestScored (fun _ => some 10) [1] == some (some (1, 10))
#guard selectBestScored (fun _ => some 10) [1, 2] == some (some (2, 10))
#guard selectBestScored (fun _ => some 10) [2, 1] == some (some (2, 10))
#guard selectBestScored (fun i => if i == 1 then none else some 10)
  [1, 2] == none
#guard checkedDirectChild sampleBlocks 0 1
#guard checkedDirectChild sampleBlocks 0 2
#guard !(checkedDirectChild sampleBlocks 0 3)
#guard !(checkedDirectChild sampleBlocks 0 7)
#guard !(checkedDirectChild sampleBlocks 0 99)
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  none 3200 [] == some none
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  none 3200 [1, 2] == some (some 2)
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  (some 3) 3200 [1, 2] == some (some 1)
#guard selectCheckedChild sampleStore sampleBlocks 0 0 sampleRoster
  none 3200 [1, 2] == none
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  none 3200 [1, 1] == none
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  none 3200 [1, 3] == none
#guard selectCheckedChild sampleStore sampleBlocks 0 9 sampleRoster
  none 3200 [1, 99] == none
#guard selectCheckedChild sampleStore sampleBlocks 99 9 sampleRoster
  none 3200 [] == none

#print axioms EthereumConsensus.ForkChoice.bestScored_empty
#print axioms EthereumConsensus.ForkChoice.bestScored_single
#print axioms EthereumConsensus.ForkChoice.bestScored_unknown_refused
#print axioms EthereumConsensus.ForkChoice.bestScored_any_unknown_refused
#print axioms EthereumConsensus.ForkChoice.bestScored_tie_break
#print axioms EthereumConsensus.ForkChoice.checkedChild_unknown_parent_refused
#print axioms EthereumConsensus.ForkChoice.checkedChild_duplicate_refused
#print axioms EthereumConsensus.ForkChoice.checkedChild_invalid_edge_refused
#print axioms EthereumConsensus.ForkChoice.checkedChild_agrees_when_admitted
#print axioms EthereumConsensus.ForkChoice.checkedChild_rejected_update

end EthereumConsensus.ForkChoice
