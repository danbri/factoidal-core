import EthereumConsensus.ForkChoice.StoredHead

/-!
Synthetic finite block-inventory fork-choice descent. These are NOT
authenticated beacon blocks or canonical checkpoint viability decisions.
A separate Python implementation reconstructs every row from the seed.
-/

open EthereumConsensus.ForkChoice

private def syntheticEntries (n : Nat) : List (Nat × BlockPosition) := Id.run do
  let root0 : List (Nat × BlockPosition) :=
    if n % 11 == 0 then [] else [(0, ⟨0, none⟩)]
  let one : Nat × BlockPosition :=
    if n % 17 == 0 then (1, ⟨0, some 0⟩)
    else (1, ⟨1, some 0⟩)
  let two : Nat × BlockPosition :=
    if n % 19 == 0 then (2, ⟨1, some 99⟩)
    else (2, ⟨1, some 0⟩)
  let three : Nat × BlockPosition :=
    if n % 23 == 0 then (3, ⟨1, some 1⟩)
    else (3, ⟨2, some 1⟩)
  let base := root0 ++ [one, two, three, (4, ⟨2, some 2⟩)]
  return if n % 13 == 0 then base ++ [(2, ⟨10, some 0⟩)] else base

private def syntheticViability (n root : Nat) : Option Bool :=
  if n % 7 == 0 && root == 2 then none
  else if n % 5 == 0 && root == 2 then some false
  else if n % 29 == 0 && root == 1 then none
  else some true

private def syntheticStore : VoteStore := {
  latest := fun _ => none
  equivocating := fun _ => false
}

private def showScan : Option (List Nat) → String
  | none => "R"
  | some nodes => String.intercalate "," (nodes.map toString)

private def showSelected : Option (Option Nat) → String
  | none => "R"
  | some none => "E"
  | some (some head) => toString head

private def showHead : Option Nat → String
  | none => "R"
  | some head => toString head

def main : IO Unit := do
  for n in [:1024] do
    let entries := syntheticEntries n
    let viable := syntheticViability n
    let start := if n % 31 == 0 then 99 else 0
    let budget := n % 5
    let scan := match lookupStored start entries with
      | none => none
      | some position => scanStoredChildren start position.slot viable entries
    let step := selectStoredChild syntheticStore entries viable start 4
      [] none 3200
    let head := getHeadStored syntheticStore entries viable 4
      [] none 3200 budget start
    let rejected := updateStore syntheticStore 0 ⟨n % 32, n % 7⟩ false
    let afterRefusal := getHeadStored rejected entries viable 4
      [] none 3200 budget start
    IO.println s!"{n}\t{start}\t{budget}\t{showScan scan}\t{showSelected step}\t{showHead head}\t{showHead afterRefusal}"
