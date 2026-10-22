import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF

/-- Every RIF lexical decision uses the explicit XSD 1.1 profile. This proves
    adapter agreement, not correctness of the shared parser. -/
theorem inLexicalSpace_shared (base lexical : String) :
    inLexicalSpace base lexical = XSD.validLexicalFor .xsd11 base lexical := rfl

/-- Unknown shared datatype names are not guessed valid by RIF. -/
theorem inLexicalSpace_unknown (base lexical : String)
    (h : XSD.builtinOfName? base = none) :
    inLexicalSpace base lexical = none := by
  simp [inLexicalSpace, XSD.validLexicalFor, h]

#print axioms inLexicalSpace_shared
#print axioms inLexicalSpace_unknown

/-- Lists are outside DTS, so no negative datatype guard may succeed on them.
    Unsupported guard names may remain unknown, but can never return yes. -/
theorem negative_guard_list_ne_yes (base : String) (xs : List GTerm) :
    isLiteralNotOf base (.list xs) ≠ .yes := by
  simp only [isLiteralNotOf, literalGuard]
  split <;> decide

#print axioms negative_guard_list_ne_yes

end L4Factoidal.RIF
