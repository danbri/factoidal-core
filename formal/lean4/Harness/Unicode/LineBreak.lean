/-
Harness.Unicode.LineBreak — conformance-file runner for `l4unicode`
(https://github.com/danbri/factoidal/issues/1167, milestone 4). Stub: the
runner is not written yet.
-/
namespace Harness.Unicode.LineBreak

/-- Run the conformance file at `path` for subcommand `cmd`; return
(pass, fail). -/
def run (_cmd : String) (_path : System.FilePath) : IO (Nat × Nat) := pure (0, 0)

end Harness.Unicode.LineBreak
