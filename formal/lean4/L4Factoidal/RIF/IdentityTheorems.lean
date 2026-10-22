import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF

/-- The RIF adapter uses the shared XSD identity decision for decoded values. -/
theorem literal_identity_xsd (a b : XSD.Val) :
    LiteralValue.identical (.xsd a) (.xsd b) = XSD.valIdentical a b := rfl

/-- Lists are outside DTS even when the other argument is undecided. -/
theorem literal_not_identical_list_left (xs : List GTerm) (b : GTerm) :
    literalNotIdentical (.list xs) b = .no := by cases b <;> rfl

theorem literal_not_identical_list_right (a : GTerm) (xs : List GTerm) :
    literalNotIdentical a (.list xs) = .no := by cases a <;> rfl

#print axioms literal_identity_xsd
#print axioms literal_not_identical_list_left
#print axioms literal_not_identical_list_right

end L4Factoidal.RIF
