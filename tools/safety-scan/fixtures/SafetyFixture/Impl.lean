/-! Expected: reaches-hatch (`@[implemented_by]` to an `unsafe` definition). -/
namespace SafetyFixture.Impl
unsafe def fastImpl (n : Nat) : Nat := n + 1
@[implemented_by fastImpl] def slow (n : Nat) : Nat := n + 1
end SafetyFixture.Impl
