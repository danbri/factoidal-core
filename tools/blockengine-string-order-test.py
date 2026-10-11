#!/usr/bin/env python3
"""Check compiled native Unicode ordering against complete independent answers."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile

SPEC = importlib.util.spec_from_file_location(
    "snapshot_test", Path(__file__).with_name("blockengine-snapshot-session-test.py"))
T = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(T)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--escaping-controls", action="store_true",
                        help="Also cover every JSON control character, quotes and backslashes")
    args = parser.parse_args()
    records = []
    report = {"all_checks_passed": False, "records": records,
              "test_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "binary_sha256": {name: hashlib.sha256((T.BIN / name).read_bytes()).hexdigest()
                                for name in ("l4block-snapshot-session", "l4block-id-v3-query")}}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    try:
        with tempfile.TemporaryDirectory(prefix="shardborough-string-order-") as directory:
            work = Path(directory)
            values = ["", "a", "ab", "abc", "z", "é", "é", "Ω", "漢", "😀", "Bób", "Bob",
                      "a\x00b", "a\x00c", "\x00", "é", "urn:example:long-prefix:a",
                      "urn:example:long-prefix:b"] + [chr(n) for n in
                      (0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xffff, 0x10000, 0x10ffff)]
            if args.escaping_controls:
                values += [chr(n) for n in range(32)] + ['quote "', "backslash " + chr(92),
                                                        "both " + chr(92) + chr(34)]
            report["fixture_rows"] = len(values)
            # Turtle UCHAR permits scalar values; unlike JSON, surrogate pairs
            # are not Turtle escapes. Emit non-BMP scalars directly.
            def turtle_string(value):
                return '"' + ''.join(f'\\u{ord(c):04x}' if ord(c) < 0x20 or c in '\\"'
                                     else c for c in value) + '"'
            triples = [(f"urn:subject:{i:04d}", value) for i, value in enumerate(values)]
            source = work / "fixture.ttl"
            source.write_text('\n'.join(f'<{subject}> <urn:value> {turtle_string(value)} .'
                                        for subject, value in triples) + '\n')
            collection = work / "collection"
            T.command("l4block-shard-pack", source, collection / "first", "ibk3")
            T.command("l4block-shard-activate", collection, "first")
            report["fixture_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
            session = T.Session(collection, records)
            try:
                for descending in (False, True):
                    ordered = sorted(triples, key=lambda pair: (pair[1], pair[0]), reverse=descending)
                    order = 'DESC(?value) DESC(?subject)' if descending else '?value ?subject'
                    for offset, limit in [(0, None), (0, 0), (0, 7), (3, 7), (26, 8), (100, 3)]:
                        suffix = f' OFFSET {offset}' + ('' if limit is None else f' LIMIT {limit}')
                        query = ('SELECT ?subject ?value WHERE { ?subject <urn:value> ?value } '
                                 f'ORDER BY {order}{suffix}')
                        selected = ordered[offset:] if limit is None else ordered[offset:offset + limit]
                        expected = T.bindings(["subject", "value"], [
                            {"subject": T.uri(subject), "value": T.literal(value)}
                            for subject, value in selected])
                        session.request(query, expected)
                        actual = json.loads(T.command("l4block-id-v3-query", collection,
                                                      "--json", "--query", query))
                        assert actual == expected, (query, expected, actual)
                        records.append({"fresh-query": query, "response": actual})
            finally:
                session.close()
        report["all_checks_passed"] = True
    finally:
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=True) + '\n')
    print("native string order: all Unicode, NUL, tie and slice answers passed")


if __name__ == "__main__":
    main()
