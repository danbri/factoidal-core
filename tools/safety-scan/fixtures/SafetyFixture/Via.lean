import SafetyFixture.Ext
/-! Expected: reaches-hatch through another module and through an instance. -/
namespace SafetyFixture.Via
class Step (α : Type) where step : α → α
instance : Step Nat := ⟨SafetyFixture.Ext.cfun⟩
def twice [Step α] (a : α) : α := Step.step (Step.step a)
def useIt (n : Nat) : Nat := twice n
end SafetyFixture.Via
