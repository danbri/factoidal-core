#!/usr/bin/env python3
"""Complete native answers and admission/freshness failures; no timing claims."""
import argparse
import hashlib
import json
import pathlib
import selectors
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"


def command(name, *args):
    proc = subprocess.run([str(BIN / name), *map(str, args)], capture_output=True,
                          text=True, timeout=90)
    if proc.returncode:
        raise AssertionError((name, proc.returncode, proc.stdout, proc.stderr))
    return proc.stdout


def uri(value):
    return {"type": "uri", "value": value}


def literal(value):
    return {"type": "literal", "value": value}


def bindings(variables, rows):
    return {"head": {"vars": variables}, "results": {"bindings": rows}}


def count_result(value, alias="n"):
    return bindings([alias], [{alias: {"type": "literal", "value": str(value),
                    "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}])


class Session:
    def __init__(self, root, report):
        self.err = tempfile.TemporaryFile(mode="w+")
        self.proc = subprocess.Popen([str(BIN / "l4block-snapshot-session"), str(root)],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=self.err, text=True)
        self.report = report
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)
        try:
            self.ready = self.read()
            assert self.ready["ready"] is True, self.ready
            assert self.ready["index-builds"] == 1, self.ready
            assert self.ready["hash-index-builds"] == 1, self.ready
            assert self.ready["subject-order-index-builds"] == 1, self.ready
        except BaseException:
            self.proc.kill()
            self.proc.wait()
            self.selector.close()
            self.proc.stdin.close()
            self.proc.stdout.close()
            self.err.close()
            raise
        report.append({"open": self.ready})

    def read(self):
        if not self.selector.select(timeout=90):
            raise AssertionError("session response timed out")
        line = self.proc.stdout.readline()
        assert line, "session closed before responding"
        return json.loads(line)

    def request(self, query, expected=None, error=None, raw=False):
        self.proc.stdin.write((query if raw else json.dumps(query)) + "\n")
        self.proc.stdin.flush()
        actual = self.read()
        if error:
            assert actual.get("error") == error, actual
        else:
            assert actual == expected, (query, expected, actual)
        self.report.append({"query": query, "response": actual})

    def close(self):
        try:
            self.proc.stdin.close()
            assert self.proc.wait(timeout=10) == 0
        finally:
            if self.proc.poll() is None:
                self.proc.kill()
                self.proc.wait()
            self.selector.close()
            self.proc.stdout.close()
            self.err.seek(0)
            self.report.append({"stderr": self.err.read()})
            self.err.close()


def rejected(root, reason, records):
    proc = subprocess.run([str(BIN / "l4block-snapshot-session"), str(root)],
                          input="", capture_output=True, text=True, timeout=90)
    assert proc.returncode == 1 and not proc.stdout, (reason, proc)
    assert reason in proc.stderr, (reason, proc.stderr)
    records.append({"rejection": reason, "stderr": proc.stderr})


def exercise(work, records):
    root = work / "collection"
    source = work / "fixture.ttl"
    source.write_text('<urn:a> <urn:type> <urn:Person> ; <urn:name> "Alice" .\n'
                      '<urn:b> <urn:type> <urn:Person> ; <urn:name> "Bob", "Bób" ; '
                      '<urn:member> <urn:team1>, <urn:team2> .\n')
    command("l4block-shard-pack", source, root / "first", "ibk3")
    rejected(root / "first", "require an activated collection root", records)
    command("l4block-shard-activate", root, "first")
    names = 'SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY ?name'
    original = bindings(["name"], [{"name": literal(n)} for n in ["Alice", "Bob", "Bób"]])
    sessions = []
    try:
        first = Session(root, records)
        sessions.append(first)
        assert first.ready["triples"] == 7, first.ready
        first.request(names, original)
        first.request('SELECT ?name ?team WHERE { ?s <urn:type> <urn:Person> ; '
                      '<urn:name> ?name ; <urn:member> ?team } ORDER BY ?name ?team',
                      bindings(["name", "team"], [{"name": literal(n), "team": uri(t)}
                               for n in ["Bob", "Bób"] for t in ["urn:team1", "urn:team2"]]))
        first.request('SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?name }',
                      bindings(["n"], [{"n": {"type": "literal", "value": "3",
                      "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}]))
        for query, expected in [
            ('SELECT (STR(COUNT(*)) AS ?n) WHERE { ?s ?p ?o }',
             bindings(["n"], [{"n": literal("7")}])),
            ('SELECT (CONCAT("n=", STR(COUNT(?o))) AS ?n) WHERE { ?s <urn:name> ?o }',
             bindings(["n"], [{"n": literal("n=3")}])),
            ('SELECT ?s (STR(COUNT(?o)) AS ?n) WHERE { ?s <urn:name> ?o } GROUP BY ?s ORDER BY ?s',
             bindings(["s", "n"], [{"s": uri("urn:a"), "n": literal("1")},
                                    {"s": uri("urn:b"), "n": literal("2")}])),
            ('SELECT (COUNT(*) AS ?total) WHERE { ?s ?p ?o }', count_result(7, "total")),
            ('SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:absent> ?o }', count_result(0)),
            ('SELECT (COUNT(*) AS ?n) WHERE { _:x <urn:name> ?o }', count_result(3)),
            ('SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?o } OFFSET 1 LIMIT 3',
             bindings(["n"], [])),
            ('SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:member> ?s }', count_result(0)),
            ('SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:type> <urn:Person> }', count_result(2)),
            ('SELECT (COUNT(*) AS ?n) FROM <urn:unavailable> WHERE { ?s ?p ?o }', count_result(0)),
        ]:
            first.request(query, expected)
            actual = json.loads(command("l4block-id-v3-query", root, "--json", "--query", query))
            assert actual == expected, (query, expected, actual)
            records.append({"fresh-query": query, "response": actual})
        all_count = 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
        type_count = 'SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:type> ?o }'
        first.request('ASK { ?s <urn:type> <urn:Person> FILTER EXISTS '
                      '{ ?s <urn:name> "Alice" } }', {"head": {}, "boolean": True})
        first.request('ASK FROM <urn:unavailable> { ?s ?p ?o }', {"head": {}, "boolean": False})
        for query, value in [
            ('ASK { ?s <urn:name> ?name }', True),
            ('ASK { ?s <urn:absent> ?name }', False),
            ('ASK { ?s <urn:member> ?s }', False),
            ('ASK { _:x <urn:name> "Alice" }', True),
            ('ASK { ?s <urn:name> ?name } VALUES ?name { "missing" }', False),
            ('ASK { ?s <urn:name> ?name } VALUES ?s { "invalid subject" }', False),
            ('ASK { ?s <urn:name> ?name } VALUES ?name { UNDEF }', True),
            ('ASK {} VALUES ?x {}', False),
        ]:
            first.request(query, {"head": {}, "boolean": value})
        for query in [
            'ASK FROM <urn:unavailable> { ?s ?p ?o }',
            'ASK FROM NAMED <urn:unavailable> { ?s ?p ?o }',
        ]:
            first.request(query, {"head": {}, "boolean": False})
            actual = json.loads(command("l4block-id-v3-query", root, "--json", "--query", query))
            assert actual == {"head": {}, "boolean": False}, (query, actual)
            records.append({"fresh-query": query, "response": actual})
        for query, expected in [
            ('SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY ?s ?name OFFSET 1 LIMIT 1',
             bindings(["name"], [{"name": literal("Bob")}])),
            ('SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 1',
             bindings(["name"], [{"name": literal("Bob")}])),
            ('SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY DESC(?s) OFFSET 1 LIMIT 2',
             bindings(["name"], [{"name": literal("Bób")}, {"name": literal("Alice")}])),
            ('SELECT DISTINCT ?s WHERE { ?s <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 1',
             bindings(["s"], [{"s": uri("urn:b")}])),
            ('SELECT REDUCED ?s WHERE { ?s <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 1',
             bindings(["s"], [{"s": uri("urn:b")}])),
            ('SELECT ?s (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?name } GROUP BY ?s '
             'HAVING(COUNT(*) > 0) ORDER BY DESC(?n) OFFSET 1 LIMIT 1',
             bindings(["s", "n"], [{"s": uri("urn:a"), "n": {"type": "literal", "value": "1",
                      "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}])),
        ]:
            first.request(query, expected)
            actual = json.loads(command("l4block-id-v3-query", root, "--json", "--query", query))
            assert actual == expected, (query, expected, actual)
            records.append({"fresh-query": query, "response": actual})
        first.request('SELECT ?s FROM <urn:unavailable> WHERE { ?s ?p ?o }', bindings(["s"], []))
        first.request('SELECT ?s WHERE { ?s ?p ?o } LIMIT 0', bindings(["s"], []))
        for query, expected in [
            ('SELECT * WHERE { ?s ?p ?o } LIMIT 0', bindings(["s", "p", "o"], [])),
            ('SELECT * WHERE { ?s <urn:absent> ?o }', bindings(["s", "o"], [])),
            ('SELECT * WHERE {} VALUES (?x ?y) { (UNDEF UNDEF) }', bindings(["x", "y"], [{}])),
            ('SELECT * WHERE { BIND(?outside AS ?made) }', bindings(["made"], [{}])),
        ]:
            first.request(query, expected)
            actual = json.loads(command("l4block-id-v3-query", root, "--json", "--query", query))
            assert actual == expected, (query, expected, actual)
            records.append({"fresh-query": query, "response": actual})
        first.request('not-json', error="invalid-request", raw=True)
        first.request('42', error="invalid-request", raw=True)
        first.request('not a SPARQL query', error="invalid-query")
        first.request('CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }', error="unsupported-form")
        first.request('# Ω\n' + names, original)
        first.request('BASE <http://example.org/base/> SELECT (IRI("child") AS ?iri) WHERE {}',
                      bindings(["iri"], [{"iri": uri("http://example.org/base/child")}]))
        first.request('ASK { FILTER(NOW() = NOW()) }', {"head": {}, "boolean": True})
        command("l4block-delta-log", root, "--update",
                'DELETE DATA { <urn:a> <urn:name> "Alice" } ; '
                'INSERT DATA { <urn:c> <urn:type> <urn:Person> ; <urn:name> "Carol" }')
        first.request(names, original)
        second = Session(root, records)
        sessions.append(second)
        changed = bindings(["name"], [{"name": literal(n)} for n in ["Bob", "Bób", "Carol"]])
        second.request(names, changed)
        first.request(all_count, count_result(7))
        first.request(type_count, count_result(2))
        second.request(all_count, count_result(8))
        second.request(type_count, count_result(3))
        source.write_text('<urn:z> <urn:name> "Zelda" .\n')
        command("l4block-shard-pack", source, root / "second", "ibk3")
        command("l4block-shard-activate", root, "second")
        first.request(names, original)
        second.request(names, changed)
        third = Session(root, records)
        sessions.append(third)
        zelda = bindings(["name"], [{"name": literal("Zelda")}])
        third.request(names, zelda)
        third.request(all_count, count_result(1))
        third.request(type_count, count_result(0))
        first.request(all_count, count_result(7))
        second.request(all_count, count_result(8))
        (root / "second/deltas.dlog").write_bytes(b"torn-invalid-dlog")
        rejected(root, "malformed DLOG sidecar", records)
        third.request(names, zelda)
        (root / "second/deltas.dlog").unlink()
        artifacts = list((root / "second").glob("*.ibk3"))
        assert artifacts, list((root / "second").iterdir())
        artifact = artifacts[0]
        original_bytes = artifact.read_bytes()
        damaged = bytearray(original_bytes)
        damaged[len(damaged) // 2] ^= 1
        artifact.write_bytes(damaged)
        rejected(root, "malformed or unavailable committed artifact", records)
        third.request(names, zelda)
        artifact.write_bytes(original_bytes)
        (root / "CURRENT").write_text("../second")
        rejected(root, "CURRENT", records)
        third.request(names, zelda)
    finally:
        for session in reversed(sessions):
            session.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=pathlib.Path, required=True)
    args = parser.parse_args()
    records = []
    args.report.parent.mkdir(parents=True, exist_ok=True)
    report = {"all_checks_passed": False, "records": records,
        "session_binary_sha256": hashlib.sha256((BIN / "l4block-snapshot-session").read_bytes()).hexdigest(),
        "test_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    try:
        with tempfile.TemporaryDirectory(prefix="shardborough-snapshot-test-") as directory:
            exercise(pathlib.Path(directory), records)
        report["all_checks_passed"] = True
    finally:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("snapshot sessions: complete answers, error recovery, admission and snapshot isolation passed")


if __name__ == "__main__":
    main()
