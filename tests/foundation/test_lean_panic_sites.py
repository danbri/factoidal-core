"""Tests for tools/lean-panic-sites.py (https://github.com/danbri/factoidal-core/issues/1181).
Run: python3 -I tests/foundation/test_lean_panic_sites.py"""
import importlib.util
import os
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lps", os.path.join(HERE, "..", "..", "tools", "lean-panic-sites.py"))
lps = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lps)

SRC = '''namespace X
/-- `xs[0]!` in a doc comment is not counted. -/
def a (xs : Array Nat) : Nat := xs[0]! + xs.get! 1 + "s!".length
def b (xs : Array Nat) : Array Nat := xs.set! 0 1
partial def c (n : Nat) : Nat := c n
private partial def d (n : Nat) : Nat := d n
theorem t (xs : Array Nat) : xs.get! 0 = xs.get! 0 := rfl
#guard (#[1] : Array Nat)[0]! = 1
def e : Nat := panic! "no"
end X
'''


class SitesTest(unittest.TestCase):
    def test_kinds(self):
        d = tempfile.mkdtemp()
        p = os.path.join(d, "M.lean")
        open(p, "w").write(SRC)
        old = lps.module_path
        lps.module_path = lambda m: p
        try:
            kinds = sorted(k for _, k, _ in lps.sites_of("M"))
        finally:
            lps.module_path = old
        self.assertEqual(kinds, ["bang-call", "index-bang", "panic", "partial-def", "partial-def"])


if __name__ == "__main__":
    unittest.main()
