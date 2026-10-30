import L4Factoidal.UI.LayoutPolicy

namespace L4Factoidal.UI.LayoutPolicy.Tests
open L4Factoidal.UI.Geometry
private def refused : Except String Config → Bool
  | .error _ => true | .ok _ => false
#guard refused (validate 0 12)
#guard refused (validate 10000 12)
#guard refused (validate 299 12)
#guard refused (validate 701 12)
#guard refused (validate 500 0)
#guard refused (validate 500 1)
#guard refused (validate 500 11)
#guard refused (validate 500 25)
#guard refused (validate 500 120)
#guard !refused (validate 300 12)
#guard !refused (validate 700 24)
#guard !refused (validate 500 12)
private def low : Config := ⟨fullEnvelope,300,12,by decide⟩
private def high : Config := ⟨fullEnvelope,700,24,by decide⟩
#guard withinBudget low 100 3
#guard !withinBudget low 100 4
#guard withinBudget high 100 7
#guard !withinBudget high 100 8
#guard withinBudget defaultConfig 100 5
#guard !withinBudget defaultConfig 100 6
#guard !withinBudget defaultConfig 0 0
#guard certify defaultConfig []
#guard !certify defaultConfig [none]
#guard !certify defaultConfig [some ⟨0,0,0,0⟩]
#guard certify defaultConfig [some ⟨0,0,10,10⟩,some ⟨30,0,40,10⟩]
#guard !certify defaultConfig [some ⟨0,0,10,10⟩,some ⟨0,0,10,10⟩]
#guard overlapSum ⟨0,0,10,10⟩ [⟨0,0,10,10⟩,⟨0,0,10,10⟩] == 200
private def tight : ApplicationPolicy := ⟨300,500,12,16,by decide⟩
private def policyRefused : Except String ApplicationPolicy → Bool
  | .error _ => true | .ok _ => false
#guard policyRefused (validatePolicy 299 500 12 16)
#guard policyRefused (validatePolicy 500 300 12 16)
#guard policyRefused (validatePolicy 300 701 12 16)
#guard policyRefused (validatePolicy 300 500 11 16)
#guard policyRefused (validatePolicy 300 500 16 12)
#guard policyRefused (validatePolicy 300 500 12 25)
#guard refused (validateFor tight 700 12)
#guard refused (validateFor tight 500 24)
#guard !refused (validateFor tight 500 16)
#guard !refused (validateFor tight 300 12)
example (cfg : Config) : cfg.overlapBps ≤ cfg.application.maxOverlapBps := cfg.valid.2.1
example (cfg : Config) : 300 ≤ cfg.overlapBps ∧ cfg.overlapBps ≤ 700 ∧
    12 ≤ cfg.checkHz ∧ cfg.checkHz ≤ 24 := cfg.within_profile
example (cfg : Config) (boxes : List (Option Box)) (h : certify cfg boxes = true) :
    ∀ r ∈ checkFootprints cfg boxes, 0 < r.area ∧ 10000*r.overlapSum ≤ cfg.overlapBps*r.area :=
  (certify_sound cfg boxes h).2
end L4Factoidal.UI.LayoutPolicy.Tests
