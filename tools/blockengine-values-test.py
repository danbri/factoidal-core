#!/usr/bin/env python3
"""Independent complete VALUES answers through native fresh and snapshot routes."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile


SPEC = importlib.util.spec_from_file_location(
    "snapshot_tests", Path(__file__).with_name("blockengine-snapshot-session-test.py"))
SNAPSHOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SNAPSHOT)


def cases():
    first, target, last = map(SNAPSHOT.uri, ("urn:a", "urn:b", "urn:c"))
    name = SNAPSHOT.literal("Bee")
    result = SNAPSHOT.bindings
    return [
        ('SELECT ?x WHERE { VALUES ?x { <urn:a> UNDEF <urn:a> } }',
         result(["x"], [{"x": first}, {}, {"x": first}])),
        ('SELECT ?x ?y WHERE { VALUES (?x ?y) { (<urn:a> UNDEF) '
         '(UNDEF <urn:b>) (UNDEF UNDEF) (<urn:a> <urn:b>) } }',
         result(["x", "y"], [{"x": first}, {"y": target}, {}, {"x": first, "y": target}])),
        ('SELECT ?x WHERE { VALUES ?x {} }', result(["x"], [])),
        ('SELECT ?s ?name WHERE { VALUES ?s { <urn:c> <urn:a> <urn:a> UNDEF <urn:none> } '
         '?s <urn:next> ?next . ?next <urn:name> ?name }',
         result(["s", "name"], [{"s": subject, "name": name}
                                 for subject in (last, first, first, first, last)])),
        ('SELECT ?s ?name WHERE { VALUES ?s { <urn:c> <urn:a> <urn:a> UNDEF <urn:none> } '
         '?s <urn:next> ?next . ?next <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 3',
         result(["s", "name"], [{"s": subject, "name": name}
                                 for subject in (first, first, last)])),
        ('SELECT ?s ?name WHERE { VALUES ?s {} '
         '?s <urn:next> ?next . ?next <urn:name> ?name }', result(["s", "name"], [])),
        ('SELECT ?s ?next WHERE { VALUES (?s ?next) { (<urn:a> <urn:c>) '
         '(<urn:a> <urn:b>) (UNDEF <urn:b>) } ?s <urn:next> ?next }',
         result(["s", "next"], [{"s": subject, "next": target}
                                 for subject in (first, first, last)])),
        ('SELECT ?s WHERE { VALUES ?s { <urn:a> <urn:c> } ?s <urn:next> ?s }',
         result(["s"], [])),
        ('SELECT ?s ?name WHERE { ?s <urn:name> ?name '
         'VALUES ?s { <urn:c> <urn:a> <urn:a> } } ORDER BY ?s',
         result(["s", "name"], [{"s": first, "name": SNAPSHOT.literal("Ay")},
                                 {"s": first, "name": SNAPSHOT.literal("Ay")},
                                 {"s": last, "name": SNAPSHOT.literal("See")}])),
        ('SELECT ?x WHERE { VALUES ?x { "word"@en "word"@EN } }',
         result(["x"], [{"x": {"type": "literal", "value": "word", "xml:lang": language}}
                        for language in ("en", "EN")])),
        ('SELECT ?x WHERE { VALUES ?x { "quote\\\"\\nΩ" "" } }',
         result(["x"], [{"x": SNAPSHOT.literal('quote"\nΩ')},
                        {"x": SNAPSHOT.literal("")}])),
        ('ASK { VALUES ?s { <urn:a> } ?s <urn:next> ?next }',
         {"head": {}, "boolean": True}),
        ('ASK { VALUES ?s { <urn:none> } ?s <urn:next> ?next }',
         {"head": {}, "boolean": False}),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output must not exist")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = {"all_checks_passed": False, "binary_sha256": {}, "records": []}
    for name in ("l4block-snapshot-session", "l4block-id-v3-query",
                 "l4block-shard-pack", "l4block-shard-activate"):
        binary = SNAPSHOT.BIN / name
        if not binary.is_file():
            parser.error(f"build the native target first: {name}")
        report["binary_sha256"][name] = hashlib.sha256(binary.read_bytes()).hexdigest()
    try:
        with tempfile.TemporaryDirectory(prefix="shardborough-values-") as temporary:
            directory = Path(temporary)
            fixture, collection = directory / "fixture.ttl", directory / "collection"
            fixture.write_text('<urn:a> <urn:next> <urn:b> ; <urn:name> "Ay" .\n'
                               '<urn:b> <urn:name> "Bee" .\n'
                               '<urn:c> <urn:next> <urn:b> ; <urn:name> "See" .\n')
            SNAPSHOT.command("l4block-shard-pack", fixture, collection / "first", "ibk3")
            SNAPSHOT.command("l4block-shard-activate", collection, "first")
            session = SNAPSHOT.Session(collection, report["records"])
            try:
                for query, expected in cases():
                    session.request(query, expected)
                    actual = json.loads(SNAPSHOT.command(
                        "l4block-id-v3-query", collection, "--json", "--query", query))
                    assert actual == expected, (query, expected, actual)
                    report["records"].append({"fresh-query": query, "response": actual})
            finally:
                session.close()
            report["cases"] = len(cases())
            report["all_checks_passed"] = True
    finally:
        args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Complete snapshot and fresh CLI answers passed: {report['cases']} VALUES cases")


if __name__ == "__main__":
    main()
