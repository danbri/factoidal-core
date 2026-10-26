#!/usr/bin/env python3
import collections
import json
import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[1]
BIN = ROOT / "formal/lean4/.lake/build/bin"


def invoke(name, *arguments, success=True):
    result = subprocess.run(
        [str(BIN / name), *map(str, arguments)],
        capture_output=True, text=True, timeout=120,
    )
    if success and result.returncode:
        raise AssertionError(f"{name}: {result.returncode}\n{result.stderr}")
    return result


def bag(rows):
    return collections.Counter(json.dumps(row, sort_keys=True) for row in rows)


def uri(value):
    return {"type": "uri", "value": value}


def literal(value):
    return {"type": "literal", "value": value}


def check_triples():
    with tempfile.TemporaryDirectory(prefix="factoidal-json-") as temporary:
        directory = pathlib.Path(temporary)
        source = directory / "data.ttl"
        source.write_text("".join(
            f'<urn:s:{subject}> <urn:kind> <urn:Person> .\n'
            f'<urn:s:{subject}> <urn:name> "name{subject}" .\n'
            f'<urn:s:{subject}> <urn:name> "other{subject}" .\n'
            f'<urn:s:{subject}> <urn:group> <urn:g:{subject % 4}> .\n'
            for subject in range(24)
        ))
        store = directory / "store"
        invoke("l4block-shard-pack", source, store / "first", "ibk3")
        invoke("l4block-shard-activate", store, "first")

        def query(text):
            result = invoke("l4block-id-v3-query", store, "--json", "--query", text)
            document = json.loads(result.stdout)
            assert "open-mode=" in result.stderr, result.stderr
            return document

        names = [
            {"s": uri(f"urn:s:{subject}"), "name": literal(f"{prefix}{subject}")}
            for subject in range(24) for prefix in ("name", "other")
        ]
        pattern = "?s <urn:kind> <urn:Person> . ?s <urn:name> ?name ."
        actual = query(f"SELECT ?s ?name WHERE {{ {pattern} }}")
        reference = query(f"SELECT ?s ?name WHERE {{ {pattern} FILTER(true) }}")
        assert actual["head"]["vars"] == ["s", "name"]
        assert len(actual["results"]["bindings"]) == 48
        assert bag(actual["results"]["bindings"]) == bag(names)
        assert bag(actual["results"]["bindings"]) == bag(reference["results"]["bindings"])

        three = pattern + " ?s <urn:group> ?group ."
        actual = query(f"SELECT ?s ?name ?group WHERE {{ {three} }}")
        expected = [dict(row, group=uri(f"urn:g:{subject % 4}"))
                    for subject in range(24) for row in names[2 * subject:2 * subject + 2]]
        assert bag(actual["results"]["bindings"]) == bag(expected)

        for modifier in ("ORDER BY ?s ?name OFFSET 3 LIMIT 12", "LIMIT 12", "OFFSET 12 LIMIT 13"):
            actual = query(f"SELECT ?s ?name WHERE {{ {pattern} }} {modifier}")
            reference = query(f"SELECT ?s ?name WHERE {{ {pattern} FILTER(true) }} {modifier}")
            assert actual == reference, modifier

        selected = query("SELECT ?s WHERE { ?s <urn:group> <urn:g:0> }")
        assert bag(selected["results"]["bindings"]) == bag(
            [{"s": uri(f"urn:s:{subject}")} for subject in range(0, 24, 4)])
        star = query("SELECT * WHERE { ?s <urn:name> ?name }")
        assert set(star["head"]["vars"]) == {"s", "name"}
        assert bag(star["results"]["bindings"]) == bag(names)

        unbound = query("SELECT ?s ?missing WHERE { ?s <urn:kind> <urn:Person> }")
        assert unbound["head"]["vars"] == ["s", "missing"]
        assert all(set(row) == {"s"} for row in unbound["results"]["bindings"])
        for text in (
            "SELECT ?s ?missing WHERE { ?s <urn:kind> <urn:Person> } LIMIT 0",
            "SELECT ?s ?missing WHERE { ?s <urn:absent> ?missing }",
        ):
            empty = query(text)
            assert empty == {"head": {"vars": ["s", "missing"]},
                             "results": {"bindings": []}}

        count = query("SELECT (COUNT(*) AS ?count) WHERE { ?s <urn:name> ?name }")
        assert count["head"]["vars"] == ["count"]
        assert count["results"]["bindings"] == [{"count": {
            "type": "literal", "value": "48",
            "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}]
        assert query("ASK { ?s <urn:name> ?name }") == {"head": {}, "boolean": True}
        assert query("ASK { ?s <urn:absent> ?name }") == {"head": {}, "boolean": False}
        assert query("ASK { ?s <urn:group> <urn:g:0> }")["boolean"] is True
        grouped = query("SELECT ?predicate (COUNT(*) AS ?count) "
                        "WHERE { ?s ?predicate ?object } GROUP BY ?predicate ORDER BY ?predicate")
        assert grouped["head"]["vars"] == ["predicate", "count"]
        assert grouped["results"]["bindings"] == [
            {"predicate": uri(f"urn:{predicate}"), "count": {
                "type": "literal", "value": str(amount),
                "datatype": "http://www.w3.org/2001/XMLSchema#integer"}}
            for predicate, amount in (("group", 24), ("kind", 24), ("name", 48))]
        point = query("SELECT ?predicate ?object WHERE { <urn:s:0> ?predicate ?object }")
        assert bag(point["results"]["bindings"]) == bag([
            {"predicate": uri("urn:kind"), "object": uri("urn:Person")},
            {"predicate": uri("urn:name"), "object": literal("name0")},
            {"predicate": uri("urn:name"), "object": literal("other0")},
            {"predicate": uri("urn:group"), "object": uri("urn:g:0")},
        ])
        repeated = invoke("l4block-id-v3-query", store, "--json", "--repeat", "3",
                          "--query", "SELECT ?s WHERE { ?s <urn:kind> <urn:Person> } LIMIT 0")
        assert len(repeated.stdout.splitlines()) == 3
        assert all(json.loads(line)["results"]["bindings"] == []
                   for line in repeated.stdout.splitlines())
        refused = invoke("l4block-id-v3-query", store, "--json", "--query",
                         "CONSTRUCT { ?s <urn:kind> ?o } WHERE { ?s <urn:kind> ?o }",
                         success=False)
        assert refused.returncode == 2 and not refused.stdout
        assert "SELECT and ASK" in refused.stderr
        invoke("l4block-delta-log", store, "--update",
               'INSERT DATA { <urn:new> <urn:name> "new" . }')
        invoke("l4block-delta-log", store, "--update",
               'DELETE DATA { <urn:s:0> <urn:name> "name0" . }')
        overlay = query("SELECT ?s ?name WHERE { ?s <urn:name> ?name }")
        expected = names[1:] + [{"s": uri("urn:new"), "name": literal("new")}]
        assert bag(overlay["results"]["bindings"]) == bag(expected)
        assert query('ASK { <urn:s:0> <urn:name> "name0" }')["boolean"] is False
        assert query("SELECT (COUNT(*) AS ?count) WHERE { ?s <urn:name> ?name }") == count
    print("blockengine-ibk3-json-smoke=pass")


def check_quads(mode):
    with tempfile.TemporaryDirectory(prefix=f"factoidal-json-{mode}-") as temporary:
        directory = pathlib.Path(temporary)
        source = directory / "data.nq"
        source.write_text("".join(
            f'<urn:s:{subject}> <urn:name> "name{subject}" .\n'
            f'<urn:s:{subject}> <urn:name> "name{subject}" <urn:g:{subject % 2}> .\n'
            for subject in range(24)
        ))
        store = directory / "store"
        invoke("l4block-shard-pack", source, store / "first", mode)
        invoke("l4block-shard-activate", store, "first")

        def query(text):
            result = invoke("l4block-quad-query", store, "--json", "--query", text)
            assert "open-mode=" in result.stderr, result.stderr
            return json.loads(result.stdout)

        names = [{"s": uri(f"urn:s:{subject}"), "name": literal(f"name{subject}")}
                 for subject in range(24)]
        default = query("SELECT ?s ?name WHERE { ?s <urn:name> ?name }")
        assert default["head"]["vars"] == ["s", "name"]
        assert bag(default["results"]["bindings"]) == bag(names)
        named = query("SELECT ?g ?s ?name WHERE { GRAPH ?g { ?s <urn:name> ?name } }")
        expected = [dict(row, g=uri(f"urn:g:{subject % 2}"))
                    for subject, row in enumerate(names)]
        assert bag(named["results"]["bindings"]) == bag(expected)
        merged = query("SELECT ?s ?name FROM <urn:g:0> FROM <urn:g:1> "
                       "WHERE { ?s <urn:name> ?name }")
        assert bag(merged["results"]["bindings"]) == bag(names)
        unbound = query("SELECT ?s ?missing WHERE { GRAPH <urn:g:0> { ?s <urn:name> ?name } }")
        assert unbound["head"]["vars"] == ["s", "missing"]
        assert len(unbound["results"]["bindings"]) == 12
        assert all(set(row) == {"s"} for row in unbound["results"]["bindings"])
        empty = query("SELECT ?s ?missing WHERE { GRAPH <urn:absent> { ?s <urn:name> ?name } }")
        assert empty == {"head": {"vars": ["s", "missing"]},
                         "results": {"bindings": []}}
        assert query("SELECT * WHERE { GRAPH ?g { ?s <urn:absent> ?name } }") == {
            "head": {"vars": ["g", "s", "name"]}, "results": {"bindings": []}}
        assert query("SELECT * WHERE {} VALUES (?x ?y) { (UNDEF UNDEF) }") == {
            "head": {"vars": ["x", "y"]}, "results": {"bindings": [{}]}}
        assert query("ASK { GRAPH <urn:g:0> { ?s <urn:name> ?name } }")["boolean"] is True
        assert query("ASK { GRAPH <urn:absent> { ?s <urn:name> ?name } }")["boolean"] is False
        refused = invoke("l4block-quad-query", store, "--json", "--query",
                         "CONSTRUCT { ?s <urn:name> ?name } WHERE { ?s <urn:name> ?name }",
                         success=False)
        assert refused.returncode == 2 and not refused.stdout
        assert "SELECT and ASK" in refused.stderr
    print(f"blockengine-{mode}-json-smoke=pass")


def main():
    check_triples()
    for mode in ("ibk4", "ibk5"):
        check_quads(mode)


if __name__ == "__main__":
    main()
