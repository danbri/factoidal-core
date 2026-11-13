import SafetyFixture.Clean
import SafetyFixture.Trace
import SafetyFixture.Via
import SafetyFixture.Impl
import SafetyFixture.Init
/-! Expected: effect-typed (`IO` in a type). Imports every fixture so one root reads all. -/
namespace SafetyFixture.Main
def run : IO Unit := IO.println (SafetyFixture.Clean.double 2)
end SafetyFixture.Main
