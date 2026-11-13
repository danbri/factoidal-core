/-! Expected: reaches-hatch (own `@[extern]`). -/
namespace SafetyFixture.Ext
@[extern "safety_fixture_c"] opaque cfun : Nat → Nat
end SafetyFixture.Ext
