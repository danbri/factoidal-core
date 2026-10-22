#!/usr/bin/env python3
"""Reject suspend and wall-clock jumps that invalidate benchmark windows."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    "snapshot_bench", Path(__file__).with_name("blockengine-snapshot-session-bench.py"))
B = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(B)


class ClockWindowGuards(unittest.TestCase):
    def window(self, wall_end, uptime_end):
        wall = iter([100_000_000_000, wall_end])
        uptime = iter([10_000_000_000, uptime_end])
        return B.ClockWindow(lambda: next(wall), lambda: next(uptime))

    def test_normal_elapsed_time(self):
        result = self.window(105_000_000_000, 15_000_000_000).check()
        self.assertEqual(result["clock_skew_ns"], 0)
        self.assertEqual(result["wall_elapsed_ns"], 5_000_000_000)
        self.assertEqual(result["uptime_elapsed_ns"], 5_000_000_000)

    def test_sleep_excluded_from_uptime_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "clock discontinuity"):
            self.window(705_000_000_000, 15_000_000_000).check()

    def test_large_forward_clock_step_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "clock discontinuity"):
            self.window(110_000_000_000, 15_000_000_000).check()

    def test_large_backward_clock_step_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "clock discontinuity"):
            self.window(101_000_000_000, 15_000_000_000).check()

    def test_subsecond_sampling_and_clock_adjustment_tolerance(self):
        self.assertEqual(self.window(105_100_000_000, 15_000_000_000).check()["clock_skew_ns"],
                         100_000_000)

    def test_one_second_boundary(self):
        self.window(106_000_000_000, 15_000_000_000).check()
        with self.assertRaisesRegex(ValueError, "clock discontinuity"):
            self.window(106_000_000_001, 15_000_000_000).check()


if __name__ == "__main__":
    unittest.main()
