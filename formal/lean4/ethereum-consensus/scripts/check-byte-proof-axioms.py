#!/usr/bin/env python3
"""Compare pinned source and actual Lean axiom output with the SSZ claim ledger."""

import argparse
import hashlib
import json
from pathlib import Path
import re


REPOSITORY = Path(__file__).resolve().parents[4]
SCHEMA = "factoidal.ethereum-consensus.byte-proof-claims.v1"
FOUNDATIONS = {"propext", "Quot.sound", "Classical.choice"}
THEOREM_NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"
DECLARATION = re.compile(rf"^[ \t]*#print[ \t]+axioms[ \t]+({THEOREM_NAME})[ \t]*(?:--.*)?$", re.M)
OUTPUT = re.compile(
    rf"^[ \t]*'({THEOREM_NAME})' "
    r"(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))[ \t]*$",
    re.M,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def json_object(pairs: list[tuple[str, object]]) -> dict:
    value = {}
    for key, item in pairs:
        require(key not in value, f"duplicate ledger key {key!r}")
        value[key] = item
    return value


def git_blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def printed_declarations(sources: list[dict], theorem_sources: list[str] | None,
                         expected: set[str]) -> set[str]:
    require(isinstance(sources, list) and bool(sources), "claim ledger has no pinned sources")
    if theorem_sources is not None:
        require(isinstance(theorem_sources, list) and bool(theorem_sources),
                "theorem_sources must be a non-empty list of pinned paths")
        selected = set(theorem_sources)
        require(len(selected) == len(theorem_sources) and selected <= {item["path"] for item in sources},
                "theorem_sources must select distinct pinned paths")
    else:
        selected = {item["path"] for item in sources}

    names = set()
    visited = set()
    for item in sources:
        relative = Path(item["path"])
        path = REPOSITORY / relative
        require(not relative.is_absolute() and path.resolve() == path, f"non-canonical source path {relative}")
        require(path.suffix == ".lean" and path not in visited, f"invalid or repeated source {relative}")
        visited.add(path)
        source = path.read_bytes()
        require(git_blob_sha(source) == item["git_blob_sha"], f"source blob changed: {relative}")
        if item["path"] not in selected:
            continue
        prints = DECLARATION.findall(source.decode("utf-8"))
        for printed in prints:
            matches = {name for name in expected if name == printed or name.endswith("." + printed)}
            require(len(matches) == 1, f"{relative}: {printed} does not identify one ledger theorem")
            name = matches.pop()
            require(name not in names, f"duplicate source axiom print for {name}")
            names.add(name)
    return names


def observed_axioms(text: str) -> dict[str, list[str]]:
    observed = {}
    for name, listed, empty in OUTPUT.findall(text):
        require(name not in observed, f"duplicate Lean axiom print for {name}")
        axioms = [] if empty or not listed.strip() else [axiom.strip() for axiom in listed.split(",")]
        require(len(axioms) == len(set(axioms)), f"Lean repeated an axiom for {name}")
        require(set(axioms) <= FOUNDATIONS, f"Lean reported unpermitted axioms for {name}: {axioms}")
        observed[name] = axioms
    return observed


def check(ledger_path: Path, log_path: Path) -> None:
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"), object_pairs_hook=json_object)
    require(ledger.get("schema") == SCHEMA, "unknown byte-proof claim ledger schema")
    expected = ledger["theorem_axioms"]
    require(isinstance(expected, dict) and bool(expected), "claim ledger has no theorem axioms")
    for name, axioms in expected.items():
        require(re.fullmatch(THEOREM_NAME, name) and "." in name, f"invalid qualified theorem name {name}")
        require(isinstance(axioms, list) and len(axioms) == len(set(axioms)) and set(axioms) <= FOUNDATIONS,
                f"ledger has invalid axioms for {name}: {axioms}")

    declared = printed_declarations(ledger["sources"], ledger.get("theorem_sources"), set(expected))
    require(declared == expected.keys(), f"no source axiom print for {sorted(expected.keys() - declared)}")
    observed = observed_axioms(log_path.read_text(encoding="utf-8"))
    require(observed.keys() == expected.keys(),
            f"Lean theorem inventory differs: missing={sorted(expected.keys() - observed.keys())}, "
            f"extra={sorted(observed.keys() - expected.keys())}")
    for name, axioms in expected.items():
        require(observed[name] == axioms, f"{name}: Lean printed {observed[name]}, ledger records {axioms}")
    empty = sum(not axioms for axioms in observed.values())
    print(f"Byte-proof axiom ledger matched {len(observed)} Lean prints "
          f"({empty} without axioms, {len(observed) - empty} with permitted foundations) "
          f"and checked {len(ledger['sources'])} pinned source blobs")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ledger", type=Path)
    parser.add_argument("lean_output", type=Path)
    args = parser.parse_args()
    try:
        check(args.ledger, args.lean_output)
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
        raise SystemExit(f"Byte-proof axiom audit failed: {error}") from error


if __name__ == "__main__":
    main()
