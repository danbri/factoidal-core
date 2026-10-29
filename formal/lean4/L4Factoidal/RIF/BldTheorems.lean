/-
L4Factoidal.RIF.BldTheorems — how the RIF-BLD 2013 layer (`RIF/Bld.lean`)
relates to RIF Core 2013 (`RIF/Engine.lean`).

The names carry the specification versions: RIF BLD and RIF Core,
W3C Recommendations, Second Edition, 2013-02-05. A later edition gets new
theorems.

What is proved here:

* `bld2013_canon_without_equalities`: with no equality, reading a term
  through the classes changes nothing. A Core document has no equality
  in a conclusion, so for it the classes stay empty and the BLD layer
  reads the facts and the goal exactly as the Core engine does.
* `bld2013_assertEq_refl`: `t = t` adds no class.
* `#guard`s (evaluated at build time): the two BLD semantic conditions on
  `#` and `##` (`bldAxioms`) and the three RIF-RDF combination rules are
  safe RIF Core rules and need no universe.
* `bld2013_inconsistent_entails`: a clash of the classes (no model)
  entails every goal.

What is measured, not proved: `lake exe l4rif --bld` also runs every
entailment case of the W3C RIF Core suite through the BLD engine and
requires the Core verdict (the `rif-core under BLD` line). The full
statement "on the Core fragment `entailsBld` equals `entails`" is open,
tracked in https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RIF.Bld

namespace L4Factoidal.RIF.Bld

open L4Factoidal.RIF

theorem rep_nil (t : GTerm) : rep [] t = t := by
  simp [rep]

mutual
theorem canon_nil : (t : GTerm) → canon [] t = t
  | .const _ _ => by simp [canon, rep_nil]
  | .list xs => by simp [canon, rep_nil, canonList_nil xs]
  | .fapp _ _ xs => by simp [canon, rep_nil, canonList_nil xs]

theorem canonList_nil : (ts : List GTerm) → canonList [] ts = ts
  | [] => by simp [canonList]
  | x :: xs => by simp [canonList, canon_nil x, canonList_nil xs]
end

theorem bld2013_canon_without_equalities :
    (∀ t, canon [] t = t) ∧ (∀ ts, canonList [] ts = ts) :=
  ⟨canon_nil, canonList_nil⟩

theorem bld2013_assertEq_refl (cs : Classes) (t : GTerm) : assertEq cs t t = cs := by
  simp [assertEq]

-- Checked by evaluation at build time, not by a kernel proof (`decide`
-- does not reduce through `builtinName` and the string comparisons).
#guard bldAxioms.all ruleSafe
#guard bldAxioms.all (fun r => (unboundVars r).isEmpty)
#guard rdfCombinationRules.all ruleSafe
#guard rdfCombinationRules.all (fun r => (unboundVars r).isEmpty)

theorem bld2013_inconsistent_entails (cfg : Cfg) (rules : List Rule) (facts : Facts)
    (goal : Formula)
    (h : inconsistent (closeEq 32 (run cfg (rules ++ bldAxioms ++
            (if cfg.rdfCombination then rdfCombinationRules else [])) cfg.rounds
            { facts := facts,
              univ := (if (rules ++ bldAxioms ++
                  (if cfg.rdfCombination then rdfCombinationRules else [])).any
                    (fun r => !(unboundVars r).isEmpty) then
                ((facts.flatMap gTermsOfGAtom).flatMap (fun t => reached [] [] (tmOfG t)) ++
                 ((rules ++ bldAxioms ++ (if cfg.rdfCombination then rdfCombinationRules else [])).flatMap
                   tmsOfRule ++ tmsOfFormula goal).flatMap (reached [] [])).eraseDups
                else []).take cfg.univCap }).1.cs) = true) :
    entailsBld cfg rules facts goal = .holds := by
  simp only [entailsBld]
  simp only [h, if_true]

#print axioms bld2013_canon_without_equalities
#print axioms bld2013_assertEq_refl
#print axioms bld2013_inconsistent_entails

end L4Factoidal.RIF.Bld
