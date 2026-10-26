#!/usr/bin/env python3
"""Small retained negative controls for the complete-result repeat driver."""

import argparse
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import time


SOURCE = Path(__file__).with_name("blockengine-core-repeat.py")
SPEC = importlib.util.spec_from_file_location("core_repeat", SOURCE)
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)


def refused(action):
    try:
        action()
    except (ValueError, AssertionError, argparse.ArgumentTypeError):
        return
    raise AssertionError("negative control unexpectedly passed")


def main():
    with tempfile.TemporaryDirectory(prefix="factoidal-repeat-test-") as temporary:
        directory = Path(temporary)
        answers = directory / "answers.ndjson"
        workloads = {entry["name"]: entry for entry in DRIVER.workloads(20)}
        expected = workloads["subject-join"]["expected"]

        def check(documents, reference=expected, repeats=2):
            answers.write_text("".join(json.dumps(value) + "\n" for value in documents))
            return DRIVER.validate_results(answers, reference, repeats)

        assert check([expected, expected])["documents"] == 2
        wrong = json.loads(json.dumps(expected))
        wrong["results"]["bindings"][-1]["name"]["value"] = "wrong-after-preview"
        refused(lambda: check([expected, wrong]))
        missing = json.loads(json.dumps(expected))
        missing["results"]["bindings"].pop()
        refused(lambda: check([expected, missing]))
        reordered = json.loads(json.dumps(expected))
        reordered["results"]["bindings"].reverse()
        refused(lambda: check([reordered, expected]))
        duplicate = json.loads(json.dumps(expected))
        duplicate["results"]["bindings"][-1] = duplicate["results"]["bindings"][0]
        refused(lambda: check([duplicate, expected]))
        refused(lambda: check([expected]))
        refused(lambda: check([expected, expected, expected]))
        count = workloads["predicate-count"]["expected"]
        wrong_count = json.loads(json.dumps(count))
        wrong_count["results"]["bindings"][0]["count"]["value"] = "19"
        refused(lambda: check([wrong_count], count, 1))
        ask = workloads["ask-present"]["expected"]
        refused(lambda: check([{"head": {}, "boolean": 1}], ask, 1))
        answers.write_text('{"head":{},"boolean":true,"boolean":false}\n')
        refused(lambda: DRIVER.validate_results(answers, ask, 1))
        answers.write_text('{"head":{},"boolean":NaN}\n')
        refused(lambda: DRIVER.validate_results(answers, ask, 1))
        answers.write_text(json.dumps(expected))
        refused(lambda: DRIVER.validate_results(answers, expected, 1))

        budget = DRIVER.Budget(1024, time.monotonic() + 10)
        overflow = DRIVER.capture(
            [sys.executable, "-c", "import os; os.write(1, b'x' * 4096)"],
            directory, "overflow", 2, 1024, budget,
        )
        assert overflow["failure"] == "output budget exceeded", overflow
        assert sum(Path(overflow[key]).stat().st_size for key in
                   ("stdout_file", "stderr_file")) <= 1024
        assert budget.remaining == 0
        timeout = DRIVER.capture(
            [sys.executable, "-c", "import time; time.sleep(2)"],
            directory, "timeout", 0.05, 1024,
            DRIVER.Budget(1024, time.monotonic() + 10),
        )
        assert timeout["failure"] == "timeout", timeout
        assert timeout["wall_ns"] < 2_000_000_000, timeout
        stderr = DRIVER.capture(
            [sys.executable, "-c", "import os; os.write(2, b'e' * 4096)"],
            directory, "stderr-overflow", 2, 1024,
            DRIVER.Budget(1024, time.monotonic() + 10),
        )
        assert stderr["failure"] == "output budget exceeded", stderr
        global_limit = DRIVER.capture(
            [sys.executable, "-c", "import os; os.write(1, b'x' * 4096)"],
            directory, "global-overflow", 2, 8192,
            DRIVER.Budget(512, time.monotonic() + 10),
        )
        assert global_limit["failure"] == "output budget exceeded", global_limit
        assert global_limit["output_bytes"] == 512
        for invalid in ("0", "1001", "9" * 1000):
            refused(lambda: DRIVER.bounded_number(1, 1000)(invalid))
        for invalid in ("NaN", "inf", "0", "121"):
            refused(lambda: DRIVER.bounded_number(0.1, 120, False)(invalid))
        assert DRIVER.fixture_bytes(10).count(b"\n") == 30
        assert DRIVER.load_corpus("scale").fixture_bytes(10) == DRIVER.fixture_bytes(10)
        assert DRIVER.load_corpus("relational").triple_count(10) == 63
        refused(lambda: DRIVER.load_corpus("../untrusted"))
        collection = directory / "collection"
        (collection / "first").mkdir(parents=True)
        (collection / "CURRENT").write_text("first\n")
        (collection / "first/manifest.sbm2").write_bytes(b"manifest")
        baseline = DRIVER.collection_hashes(collection)
        assert len(baseline) == 2
        refused(lambda: DRIVER.collection_hashes(collection, max_bytes=13))
        refused(lambda: DRIVER.collection_hashes(collection, max_files=2))
        assert DRIVER.collection_hashes(collection, max_bytes=14, max_files=3) == baseline
        (collection / "linked").symlink_to(collection / "CURRENT")
        refused(lambda: DRIVER.collection_hashes(collection, max_files=1024))
    print("blockengine-core-repeat-test=pass")


if __name__ == "__main__":
    main()
