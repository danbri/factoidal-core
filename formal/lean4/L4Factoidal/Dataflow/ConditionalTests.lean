import L4Factoidal.Dataflow.Conditional

namespace L4Factoidal.Dataflow.ConditionalTests
open Stage
private instance [BEq α] : BEq (Except String α) where
  beq a b := match a,b with
    | .ok x,.ok y => x == y
    | .error x,.error y => x == y
    | _,_ => false

def P (n : Nat) : Prop := n < 10
instance : DecidablePred P := fun n => inferInstanceAs (Decidable (n < 10))

def admitted : Stage String {n // P n} Nat where
  run n := .ok (n.val + 1)
  contract n out := out = n.val + 1
  sound := by intro n out h; exact Except.ok.inj h.symm

def refused : Stage String {n // ¬ P n} Nat where
  run n := .ok (n.val + 100)
  contract n out := out = n.val + 100
  sound := by intro n out h; exact Except.ok.inj h.symm

def failAccepted : Stage String {n // P n} Nat where
  run _ := .error "accepted error"
  contract _ _ := False
  sound := by intro n out h; cases h

def failRefused : Stage String {n // ¬ P n} Nat where
  run _ := .error "refused error"
  contract _ _ := False
  sound := by intro n out h; cases h

def twice : Stage String Nat Nat where
  run n := .ok (2*n)
  contract n out := out = 2*n
  sound := by intro n out h; exact Except.ok.inj h.symm

-- Successful selected branches survive a failing unselected branch.
#guard (choose P admitted failRefused).run 3 == .ok 4
#guard (choose P failAccepted refused).run 10 == .ok 110
-- Selected failure propagates; it does not fall through to the other branch.
#guard (choose P failAccepted refused).run 3 == .error "accepted error"
#guard (choose P admitted failRefused).run 10 == .error "refused error"
#guard ((choose P admitted refused).comp twice).run 3 == .ok 8
#guard ((choose P admitted refused).comp twice).run 10 == .ok 220
#guard ((runRouted P admitted refused 3).map (fun r => r.admission.accepted)) == .ok true
#guard ((runRouted P admitted refused 10).map (fun r => r.admission.accepted)) == .ok false

example : (choose P admitted refused).contract 3 4 := by
  exact (choose P admitted refused).sound _ _ (by rfl)

example : ((choose P admitted refused).comp twice).contract 10 220 := by
  exact ((choose P admitted refused).comp twice).sound _ _ (by rfl)
end L4Factoidal.Dataflow.ConditionalTests
