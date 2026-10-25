#!/usr/bin/env python3
"""Compare the answers of the wasm-dispatch SBM11 ops with `l4sbm11 query`.

https://github.com/danbri/factoidal/issues/1009 KR1. Usage:
compare_ops.py ENVELOPES NAMES DIR

ENVELOPES: the output of `l4wasm-cli callseq`, one envelope per line: the
`sbm11Open` envelope, one `sbm11Query` envelope per name of NAMES (one name
per line), then the `sbm11Close` envelope. DIR/<name>.got holds the answer of
`l4sbm11 query` for that name (SPARQL JSON, or N-Triples lines).

SELECT: multisets of solutions (rows as sorted JSON members); ASK: the
boolean; CONSTRUCT and DESCRIBE: multisets of N-Triples lines. Both answers
come from the same engine, so blank node labels are compared as written.
Prints one line per query and a summary; exit 0 only when every query
matches.
"""
import json
import sys


def norm_select(doc):
    if "boolean" in doc:
        return ("ask", doc["boolean"])
    rows = sorted(json.dumps(r, sort_keys=True) for r in doc["results"]["bindings"])
    return ("select", tuple(doc["head"].get("vars", [])), tuple(rows))


def main():
    env_path, names_path, d = sys.argv[1:4]
    envs = [json.loads(l) for l in open(env_path, encoding="utf-8") if l.strip()]
    names = [n.strip() for n in open(names_path, encoding="utf-8") if n.strip()]
    if len(envs) != len(names) + 2 or not envs[0].get("ok") or not envs[-1].get("ok"):
        print(f"bad envelope stream: {len(envs)} envelopes for {len(names)} queries; open {envs[0] if envs else None}")
        return 1
    passed = failed = 0
    for name, env in zip(names, envs[1:-1]):
        got_native = open(f"{d}/{name}.got", encoding="utf-8").read()
        if not env.get("ok"):
            ok, why = False, f"op refused: {env.get('error')}"
        elif "ntriples" in env:
            a = sorted(l for l in env["ntriples"].split("\n") if l.strip())
            b = sorted(l for l in got_native.split("\n") if l.strip())
            ok, why = a == b, f"{len(a)} lines vs {len(b)}"
        else:
            a = norm_select(env["results"])
            b = norm_select(json.loads(got_native))
            ok, why = a == b, f"{env.get('rows')} rows, path {env.get('path')}"
        print(f"{'ok  ' if ok else 'FAIL'} {name}: {why}")
        passed += ok
        failed += not ok
    print(f"sbm11 ops vs l4sbm11 query: {passed} pass, {failed} fail (out of {len(names)})")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
