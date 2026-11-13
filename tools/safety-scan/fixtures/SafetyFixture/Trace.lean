/-! Expected: reaches-hatch (`dbgTrace`, core-effect). A pure type that prints. -/
namespace SafetyFixture.Trace
def leak (secret : String) (n : Nat) : Nat := dbgTrace secret fun _ => n + 1
end SafetyFixture.Trace
