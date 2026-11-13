/-! Expected: effect-typed (`initialize` makes an `IO` action that runs at load). -/
namespace SafetyFixture.Init
initialize counter : IO.Ref Nat ← IO.mkRef 0
end SafetyFixture.Init
