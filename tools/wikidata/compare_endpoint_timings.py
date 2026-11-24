#!/usr/bin/env python3
"""Measure selected original/rewritten catalogue queries on Blazegraph and QLever."""

import argparse
from hashlib import sha256
import json
import re
import statistics
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier
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


def request(endpoint, encoded_query, method, timeout, start_pair):
    if method == "GET":
        req = Request(f"{endpoint}?{encoded_query}", headers=HEADERS)
    else:
        req = Request(endpoint, data=encoded_query.encode("ascii"), headers=HEADERS)
    start_pair.wait()
    start = time.perf_counter()
    with urlopen(req, timeout=timeout) as response:
        data = json.load(response)
    return start, (time.perf_counter() - start) * 1000, data


def measure_pair(pool, endpoints, encoded, method, timeout):
    start_pair = Barrier(len(endpoints))
    pending = {
        name: pool.submit(request, endpoint, encoded[name], method, timeout, start_pair)
        for name, endpoint in endpoints.items()
    }
    observations = {"dispatch": "concurrent", "results_match": None}
    signatures = {}
    starts = {}
    backoff = None
    for name, future in pending.items():
        try:
            starts[name], ms, result = future.result()
        except (URLError, TimeoutError, ValueError) as error:
            observations[name] = {"error": str(error)}
            if isinstance(error, HTTPError):
                status = error.code
                observations[name]["http_status"] = status
                error.close()
                if status in {429, 503}:
                    backoff = f"{name} requested a backoff (HTTP {status})"
            continue
        observations[name] = {"ms": round(ms, 2)}
        try:
            signature = result_signature(result)
            signatures[name] = (signature, result)
            if isinstance(signature, tuple):
                observations[name]["rows"] = sum(signature[1].values())
            else:
                observations[name]["boolean"] = signature
        except (KeyError, TypeError, ValueError) as error:
            observations[name]["comparison_error"] = str(error)
    if len(starts) == 2:
        observations["dispatch_skew_ms"] = round((max(starts.values()) - min(starts.values())) * 1000, 3)
    if len(signatures) == 2:
        (original, original_json), (rewritten, rewritten_json) = (signatures[name] for name in endpoints)
        observations["results_match"] = original == rewritten
        if original != rewritten:
            observations["integer_datatypes_only"] = (
                result_signature(original_json, normalize_int=True)
                == result_signature(rewritten_json, normalize_int=True)
            )
            if isinstance(original, tuple) and isinstance(rewritten, tuple):
                original_vars, original_rows = original
                rewritten_vars, rewritten_rows = rewritten
                observations["result_difference"] = {
                    "original_only_columns": sorted(original_vars - rewritten_vars),
                    "rewritten_only_columns": sorted(rewritten_vars - original_vars),
                    "unmatched_original_rows": sum((original_rows - rewritten_rows).values()),
                    "unmatched_rewritten_rows": sum((rewritten_rows - original_rows).values()),
                }
    return observations, backoff


def measure(pool, row, rewrite_key, trials, timeout, pair_delay):
    inputs = {"blazegraph": row.get("classic_query"), "qlever": row.get(rewrite_key)}
    if not all(inputs.values()):
        return {"error": "Original or selected rewrite text is unavailable"}
    inputs["qlever"] = inputs["qlever"].split("\n# Original query:\n", 1)[0]
    encoded = {name: urlencode({"query": text}) for name, text in inputs.items()}
    method = "POST" if any(len(query) > 7000 for query in encoded.values()) else "GET"
    endpoints = {"blazegraph": BLAZEGRAPH, "qlever": QLEVER}
    samples = []
    report = {
        "method": method,
        "query_sha256": {name: sha256(text.encode()).hexdigest() for name, text in inputs.items()},
        "trials": samples,
    }
    for trial in range(trials):
        if trial:
            time.sleep(pair_delay)
        observations, backoff = measure_pair(pool, endpoints, encoded, method, timeout)
        samples.append(observations)
        if backoff:
            return {**report, "error": backoff}

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
    parser.add_argument("--trials", type=int, default=1)
    parser.add_argument("--pair-delay", type=float, default=2, help="Seconds to wait after each completed pair")
    parser.add_argument("--timeout", type=float, default=30)
    args = parser.parse_args()
    if args.trials < 1 or not (0 < args.timeout <= 120) or not (0 <= args.pair_delay < float("inf")):
        parser.error("Use a positive trial count, a timeout up to 120 seconds and a finite nonnegative delay.")
    rows = {row["id"]: row for row in json.loads(args.catalogue.read_text(encoding="utf-8"))["queries"]}
    missing = set(args.ids) - rows.keys()
    if missing:
        parser.error("Unknown query IDs: " + ", ".join(sorted(missing)))
    rewrite_key = "lean_replacement_query" if args.rewrite == "lean" else "replacement_query"
    with ThreadPoolExecutor(max_workers=2) as pool:
        for index, ident in enumerate(dict.fromkeys(args.ids)):
            if index:
                time.sleep(args.pair_delay)
            result = measure(pool, rows[ident], rewrite_key, args.trials, args.timeout, args.pair_delay)
            print(json.dumps({"id": ident, "rewrite": args.rewrite, **result}), flush=True)
            if "requested a backoff" in result.get("error", ""):
                return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
