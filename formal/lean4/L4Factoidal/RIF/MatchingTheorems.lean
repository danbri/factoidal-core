import L4Factoidal.RIF.Matching

namespace L4Factoidal.RIF

/-- Syntactically identical ground terms always match, independently of
    whether their symbol space has a supported datatype mapping. -/
theorem groundMatch_refl (g : GTerm) : groundMatch g g = .yes := by
  cases g <;> simp [groundMatch]

/-- A known mismatch controls a conjunction without becoming unknown. -/
theorem matchConjunction_no_left (a : Ans) : matchConjunction .no a = .no := by
  cases a <;> rfl

/-- An unresolved comparison cannot produce a successful binding. -/
theorem matchResult_unknown (v : α) : matchResult v .unknown = (none, true) := rfl

#print axioms groundMatch_refl
#print axioms matchConjunction_no_left
#print axioms matchResult_unknown

end L4Factoidal.RIF
