#!/usr/bin/env python3
"""Independent complete native GROUP BY answers; no timing claims."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile

SPEC = importlib.util.spec_from_file_location(
    "session_tests", Path(__file__).with_name("blockengine-snapshot-session-test.py"))
S = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(S)


def cases():
    a, b = S.uri("urn:a"), S.uri("urn:b")
    integer = lambda n: {"type": "literal", "value": str(n),
                         "datatype": "http://www.w3.org/2001/XMLSchema#integer"}
    where = 'WHERE { ?s <urn:name> ?name }'
    grouped = where + ' GROUP BY ?s'
    rows = [{"s": a, "n": integer(1)}, {"s": b, "n": integer(2)}]
    return [
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' ORDER BY ?s',
         S.bindings(["s", "n"], rows)),
        ('SELECT ?s (COUNT(DISTINCT ?name) AS ?n) ' + grouped + ' ORDER BY ?s',
         S.bindings(["s", "n"], rows)),
        ('SELECT ?alias (STR(COUNT(?name)) AS ?n) ' + where +
         ' GROUP BY (STR(?s) AS ?alias) ORDER BY ?alias',
         S.bindings(["alias", "n"], [{"alias": S.literal("urn:a"), "n": S.literal("1")},
                                      {"alias": S.literal("urn:b"), "n": S.literal("2")}])),
        ('SELECT ?s ?name (COUNT(*) AS ?n) ' + where +
         ' GROUP BY ?s ?name ORDER BY ?s ?name',
         S.bindings(["s", "name", "n"], [{"s": s, "name": S.literal(name), "n": integer(1)}
                      for s, name in [(a, "Alice"), (b, "Bob"), (b, "Bób")]])),
        ('SELECT ?missing (STR(COUNT(*)) AS ?n) ' + where + ' GROUP BY ?missing',
         S.bindings(["missing", "n"], [{"n": S.literal("3")}])),
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' HAVING(COUNT(*) > 1) ORDER BY ?s',
         S.bindings(["s", "n"], rows[1:])),
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' ORDER BY DESC(?n) OFFSET 1 LIMIT 1',
         S.bindings(["s", "n"], rows[:1])),
        ('SELECT DISTINCT ?s (COUNT(*) AS ?n) ' + grouped + ' ORDER BY ?s',
         S.bindings(["s", "n"], rows)),
        ('SELECT REDUCED ?s (COUNT(*) AS ?n) ' + grouped + ' ORDER BY ?s LIMIT 1',
         S.bindings(["s", "n"], rows[:1])),
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' LIMIT 0', S.bindings(["s", "n"], [])),
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' ORDER BY ?s VALUES ?s { <urn:b> }',
         S.bindings(["s", "n"], rows[1:])),
        ('SELECT ?s (COUNT(*) AS ?n) ' + grouped + ' VALUES ?s {}', S.bindings(["s", "n"], [])),
        ('SELECT ?s (GROUP_CONCAT(?name; SEPARATOR="|") AS ?names) WHERE { '
         '{ SELECT ?s ?name ' + where + ' ORDER BY ?s ?name } } GROUP BY ?s ORDER BY ?s',
         S.bindings(["s", "names"], [{"s": a, "names": S.literal("Alice")},
                                      {"s": b, "names": S.literal("Bob|Bób")}])),
        ('SELECT ?g (STR(COUNT(*)) AS ?n) WHERE { VALUES ?x { 1 1.0 2 } } '
         'GROUP BY (?x AS ?g) ORDER BY ?g',
         S.bindings(["g", "n"], [{"g": integer(1), "n": S.literal("2")},
                                  {"g": integer(2), "n": S.literal("1")}])),
        ('SELECT ?g (STR(COUNT(*)) AS ?n) WHERE { VALUES ?g { "word"@en "word"@EN } } '
         'GROUP BY ?g ORDER BY ?g',
         S.bindings(["g", "n"], [{"g": {"type": "literal", "value": "word", "xml:lang": tag},
                                   "n": S.literal("1")} for tag in ["EN", "en"]])),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output must not exist")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = {"all_checks_passed": False, "binary_sha256": {}, "records": []}
    for name in ["l4block-snapshot-session", "l4block-id-v3-query", "l4block-shard-pack", "l4block-shard-activate"]:
        report["binary_sha256"][name] = hashlib.sha256((S.BIN / name).read_bytes()).hexdigest()
    try:
        with tempfile.TemporaryDirectory(prefix="shardborough-grouping-") as directory:
            work = Path(directory)
            fixture, collection = work / "fixture.ttl", work / "collection"
            fixture.write_text('<urn:a> <urn:type> <urn:Person> ; <urn:name> "Alice" .\n'
                               '<urn:b> <urn:type> <urn:Person> ; <urn:name> "Bob", "Bób" ; '
                               '<urn:member> <urn:team1>, <urn:team2> .\n')
            S.command("l4block-shard-pack", fixture, collection / "first", "ibk3")
            S.command("l4block-shard-activate", collection, "first")
            session = S.Session(collection, report["records"])
            try:
                for query, expected in cases():
                    session.request(query, expected)
                    actual = json.loads(S.command("l4block-id-v3-query", collection, "--json", "--query", query))
                    assert actual == expected, (query, expected, actual)
                    report["records"].append({"fresh-query": query, "response": actual})
            finally:
                session.close()
            report["cases"] = len(cases())
            report["all_checks_passed"] = True
    finally:
        args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Complete snapshot and fresh CLI answers passed: {report['cases']} grouping cases")


if __name__ == "__main__":
    main()
