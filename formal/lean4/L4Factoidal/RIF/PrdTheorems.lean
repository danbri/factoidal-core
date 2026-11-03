/-
L4Factoidal.RIF.PrdTheorems — how the RIF-PRD 2013 layer (`RIF/Prd.lean`)
relates to RIF Core 2013 (`RIF/Engine.lean`), and properties of the PRD
transition relation (RIF PRD 2013 §3.2) and of `rif:forwardChaining`
(§4.2.5).

The names carry the specification versions: RIF Production Rule Dialect
and RIF Core, W3C Recommendations, Second Edition, 2013-02-05. A later
edition gets new theorems.

What is proved here:

* `prd2013_ofCoreRule_actions`, `prd2013_ofCoreRules_monotone`: a RIF Core
  rule is a PRD rule whose action block is one `Assert` of its head, and a
  rule set of embedded Core rules is monotone (no `Not`, only `Assert`).
* `prd2013_assert_mem`, `prd2013_monotone_step`, `prd2013_runActions_monotone`:
  `Assert` adds its fact; an `Assert` or `Execute` keeps every fact; so does
  a sequence of them, through all the transitional states of one cycle.
  This is what lets `entailsPrd` stop a monotone run as soon as the goal
  holds.
* `prd2013_retract_removes`, `prd2013_retractObj_clears`: after
  `Retract(φ)` no fact with the value of φ is left; after `Retract(o)` no
  frame and no membership with object `o` is left (§3.2, rules 2 and 4).
* `prd2013_modify_single`: `Modify(o[s->v])` is `Retract(o s)` then
  `Assert(o[s->v])` (§3.1.1).
* `prd2013_not_refracted_unfired`, `prd2013_refracted_after_fire`: the
  refraction rule of §4.2.5 never removes an instance that has not fired
  since it entered the conflict set, and removes one that fired in the
  previous state and stayed in the conflict set.

What is measured, not proved: `lake exe l4rif --prd` runs every shared
RIF Core entailment case of the W3C PRD manifest through the PRD engine and
requires the Core verdict (the `PRD against Core` line). The full statement
"on a Core rule set the PRD final state satisfies a goal iff the Core
closure does" is open, tracked in https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RIF.Prd

namespace L4Factoidal.RIF.Prd

open L4Factoidal.RIF

theorem prd2013_ofCoreRule_actions (r : Rule) :
    (ofCoreRule r).actions = [Action.assert r.head] := rfl

theorem prd2013_ofCoreRule_cond (r : Rule) :
    (ofCoreRule r).cond = r.body.map Cond.core := rfl

theorem prd2013_ofCoreRules_monotone (rs : List Rule) :
    rulesMonotone (rs.map ofCoreRule) = true := by
  simp only [rulesMonotone, List.all_map, List.all_eq_true]
  intro r _
  cases h : r.body <;> simp [ofCoreRule, h, Action.monotone, condMonotone]

theorem prd2013_assert_mem (facts : Facts) (f : GAtom) :
    f ∈ applyGAction facts (.assert f) := by
  simp only [applyGAction]
  split
  · simp_all
  · simp

/-- The ground actions that keep every fact: `Assert` and `Execute`. -/
def GAction.monotone : GAction → Bool
  | .assert _ | .execute _ _ => true
  | _ => false

theorem prd2013_monotone_step (facts : Facts) (a : GAction) (h : a.monotone = true)
    (g : GAtom) (hg : g ∈ facts) : g ∈ applyGAction facts a := by
  cases a with
  | assert f =>
      simp only [applyGAction]
      split
      · exact hg
      · exact List.mem_append_left _ hg
  | execute _ _ => exact hg
  | retract _ => simp [GAction.monotone] at h
  | retractSlot _ _ => simp [GAction.monotone] at h
  | retractObj _ => simp [GAction.monotone] at h

theorem prd2013_runActions_monotone (rules : List PRule) (ri : Inst) :
    ∀ (acts : List GAction) (st : St) (first : Bool),
      acts.all GAction.monotone = true →
      ∀ g ∈ st.facts, g ∈ (runActions rules ri st acts first).facts
  | [], st, _, _, g, hg => by simpa [runActions] using hg
  | a :: rest, st, first, h, g, hg => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [runActions]
      exact prd2013_runActions_monotone rules ri rest _ false h.2 g
        (prd2013_monotone_step st.facts a h.1 g hg)

theorem prd2013_retract_removes (facts : Facts) (f g : GAtom)
    (hg : g ∈ applyGAction facts (.retract f)) : gAtomSame g f = false := by
  simp only [applyGAction, List.mem_filter] at hg
  simpa using hg.2

theorem prd2013_retractObj_clears (facts : Facts) (o : GTerm) (g : GAtom)
    (hg : g ∈ applyGAction facts (.retractObj o)) :
    (∀ o' s v, g = .frame o' s v → gEqValue o' o = false) ∧
    (∀ o' c, g = .member o' c → gEqValue o' o = false) := by
  simp only [applyGAction, List.mem_filter] at hg
  refine ⟨fun o' s v e => ?_, fun o' c e => ?_⟩
  · subst e; simpa using hg.2
  · subst e; simpa using hg.2

theorem prd2013_modify_single (o s v : Tm) :
    modifyActions [.frame o s v] = [.retractSlot o s, .assert (.frame o s v)] := rfl

theorem prd2013_not_refracted_unfired (ri : Inst) (n : Nat) :
    refracted { inst := ri, recency := n, lastPicked := none } = false := rfl

theorem prd2013_refracted_after_fire (ri : Inst) (n : Nat) (h : 2 ≤ n) :
    refracted { inst := ri, recency := n, lastPicked := some 1 } = true := by
  simp only [refracted, decide_eq_true_eq]
  omega

#print axioms prd2013_ofCoreRules_monotone
#print axioms prd2013_assert_mem
#print axioms prd2013_runActions_monotone
#print axioms prd2013_retract_removes
#print axioms prd2013_retractObj_clears
#print axioms prd2013_refracted_after_fire

end L4Factoidal.RIF.Prd
