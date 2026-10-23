import L4Factoidal.CSVW.Diagnostics

namespace L4Factoidal.CSVW

/-- Unsupported semantics never expose a completed conversion output. -/
theorem finishConversion_unsupported (value : α) (issues : List ConversionIssue)
    (h : issues.any (·.kind == .unsupported) = true) :
    (finishConversion value issues).value? = none := by
  simp [finishConversion, h]

/-- In the absence of unsupported semantics, conversion preserves the output. -/
theorem finishConversion_supported (value : α) (issues : List ConversionIssue)
    (h : issues.any (·.kind == .unsupported) = false) :
    (finishConversion value issues).value? = some value := by
  simp [finishConversion, h]

#print axioms finishConversion_unsupported
#print axioms finishConversion_supported

end L4Factoidal.CSVW
