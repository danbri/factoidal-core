#!/usr/bin/env python3
"""Measure selected original/rewritten catalogue queries on Blazegraph and QLever."""

import argparse
import json
import re
import statistics
import time
from collections import Counter
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

BLAZEGRAPH = "https://query.wikidata.org/sparql"
QLEVER = "https://query-next.wikidata.org/sparql"
HEADERS = {
    "Accept": "application/sparql-results+json",
    "User-Agent": "Factoidal WDQS comparison (https://github.com/danbri/factoidal-core)",
}
XSD = "http://www.w3.org/2001/XMLSchema#"


def result_signature(result, normalize_int=False):
    boolean = result.get("boolean")
    if isinstance(boolean, bool):
        return boolean

    def normal_row(row):
        terms = {}
        for name, term in row.items():
            if term["type"] == "bnode":
                raise ValueError("Blank node identifiers cannot be compared across endpoints")
            term = dict(term)
            if term["type"] in {"literal", "typed-literal"}:
                term["type"] = "literal"
                if term.get("datatype") == XSD + "string":
                    term.pop("datatype")
                if normalize_int and term.get("datatype") == XSD + "int":
                    lexical = term["value"]
                    if re.fullmatch(r"[+-]?[0-9]{1,10}", lexical) and -(2**31) <= int(lexical) < 2**31:
                        term["datatype"] = XSD + "integer"
                if "xml:lang" in term:
                    term["xml:lang"] = term["xml:lang"].lower()
            terms[name] = term
        return json.dumps(terms, sort_keys=True)

    bag = Counter(normal_row(row) for row in result["results"]["bindings"])
    return frozenset(result["head"]["vars"]), bag


def request(endpoint, encoded_query, method, timeout):
    if method == "GET":
        req = Request(f"{endpoint}?{encoded_query}", headers=HEADERS)
    else:
        req = Request(endpoint, data=encoded_query.encode("ascii"), headers=HEADERS)
    start = time.perf_counter()
    with urlopen(req, timeout=timeout) as response:
        data = json.load(response)
    return (time.perf_counter() - start) * 1000, data


def measure(row, rewrite_key, trials, timeout):
    inputs = {"blazegraph": row.get("classic_query"), "qlever": row.get(rewrite_key)}
    if not all(inputs.values()):
        return {"error": "Original or selected rewrite text is unavailable"}
    inputs["qlever"] = inputs["qlever"].split("\n# Original query:\n", 1)[0]
    encoded = {name: urlencode({"query": text}) for name, text in inputs.items()}
    method = "POST" if any(len(query) > 7000 for query in encoded.values()) else "GET"
    endpoints = {"blazegraph": BLAZEGRAPH, "qlever": QLEVER}
    samples = []
    for trial in range(trials):
        order = list(endpoints) if trial % 2 == 0 else list(reversed(endpoints))
        observations = {"order": order}
        results = {}
        for name in order:
            try:
                ms, result = request(endpoints[name], encoded[name], method, timeout)
            except (URLError, TimeoutError, ValueError) as error:
                observations[name] = {"error": str(error)}
                if isinstance(error, HTTPError):
                    status = error.code
                    error.close()
                    if status in {429, 503}:
                        return {"method": method, "trials": samples + [observations],
                                "error": f"{name} requested a backoff (HTTP {status})"}
                continue
            observations[name] = {"ms": round(ms, 2)}
            try:
                signature = result_signature(result)
                results[name] = result
                if isinstance(signature, tuple):
                    observations[name]["rows"] = sum(signature[1].values())
                else:
                    observations[name]["boolean"] = signature
            except (KeyError, TypeError, ValueError) as error:
                observations[name]["comparison_error"] = str(error)
        observations["results_match"] = None
        if len(results) == 2:
            original, rewritten = (results[name] for name in endpoints)
            observations["results_match"] = result_signature(original) == result_signature(rewritten)
            if not observations["results_match"]:
                observations["integer_datatypes_only"] = (
                    result_signature(original, normalize_int=True) == result_signature(rewritten, normalize_int=True)
                )
        samples.append(observations)

    report = {"method": method, "trials": samples}
    if all(trial["results_match"] is True or trial.get("integer_datatypes_only") for trial in samples):
        medians = {name: statistics.median(trial[name]["ms"] for trial in samples) for name in endpoints}
        report["median_ms"] = medians
        if medians["blazegraph"] > 0:
            report["qlever_over_blazegraph"] = round(medians["qlever"] / medians["blazegraph"], 3)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalogue", type=Path)
    parser.add_argument("ids", nargs="+", help="Catalogue query IDs to run")
    parser.add_argument("--rewrite", choices=["lean", "wikimedia"], default="lean")
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=30)
    args = parser.parse_args()
    if args.trials < 1 or not (0 < args.timeout <= 120):
        parser.error("Use a positive trial count and a timeout up to 120 seconds.")
    rows = {row["id"]: row for row in json.loads(args.catalogue.read_text(encoding="utf-8"))["queries"]}
    missing = set(args.ids) - rows.keys()
    if missing:
        parser.error("Unknown query IDs: " + ", ".join(sorted(missing)))
    rewrite_key = "lean_replacement_query" if args.rewrite == "lean" else "replacement_query"
    for ident in dict.fromkeys(args.ids):
        result = measure(rows[ident], rewrite_key, args.trials, args.timeout)
        print(json.dumps({"id": ident, "rewrite": args.rewrite, **result}), flush=True)
        if "requested a backoff" in result.get("error", ""):
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
