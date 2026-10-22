/- Conversion diagnostics shared by CSVW's RDF and JSON outputs. -/
namespace L4Factoidal.CSVW

inductive ConversionIssueKind where
  | warning | invalidValue | unsupported
deriving Repr, DecidableEq, Inhabited

structure ConversionIssue where
  kind : ConversionIssueKind
  message : String
  table : String := ""
  row : Nat := 0
  column : String := ""
deriving Repr, DecidableEq, Inhabited

/-- No completed output is exposed when required semantics are unsupported.
    Invalid cell values remain convertible as strings; warnings also permit
    conversion. Neither is confused with missing implementation coverage. -/
structure ConversionResult (α : Type) where
  value? : Option α
  issues : List ConversionIssue
deriving Repr, Inhabited

def finishConversion (value : α) (issues : List ConversionIssue) : ConversionResult α :=
  ⟨if issues.any (·.kind == .unsupported) then none else some value, issues⟩

end L4Factoidal.CSVW
