"""Tests for tools/theorem-count.py (https://github.com/danbri/factoidal-core/issues/1186).
Run: python3 -I tests/foundation/test_theorem_count.py"""
import importlib.util
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("tc", os.path.join(HERE, "..", "..", "tools", "theorem-count.py"))
tc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tc)


class ClosedTest(unittest.TestCase):
    def test_closed(self):
        self.assertTrue(tc.is_closed("theorem t : f 3 = 7", "t"))
        self.assertTrue(tc.is_closed("theorem t : (f 3).length = 7", "t"))

    def test_general(self):
        self.assertFalse(tc.is_closed("theorem t (n : Nat) : n + 0 = n", "t"))
        self.assertFalse(tc.is_closed("theorem t {a : Nat} : a = a", "t"))
        self.assertFalse(tc.is_closed("theorem t : ∀ n, n + 0 = n", "t"))
        self.assertFalse(tc.is_closed("theorem t : p → q", "t"))
        self.assertFalse(tc.is_closed("theorem t : ∃ n, n = 1", "t"))
        self.assertFalse(tc.is_closed("theorem t [inst : Foo] : bar = baz", "t"))


if __name__ == "__main__":
    unittest.main()
