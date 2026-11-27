#!/usr/bin/env python3
"""Run the vendored BLS signature vectors (third_party/ethereum-bls-vectors) through `evm-blssig`.

The JSON file is pinned by SHA-256. Each case becomes one line `SUITE NAME EXPECTED ARGS...`
for `evm-blssig --vectors`. Then the control: one expectation per suite is altered and the
binary must report exactly those cases. Prints a JSON summary; non-zero exit on any failure."""
import argparse, hashlib, json, os, subprocess, sys, tempfile

PIN = "b25629059e5a6084fbf426ed9713ff9c81d3fec97b13ead15a83291295e117c2"
EXPECTED = {"verify": 28, "aggregate_verify": 5, "fast_aggregate_verify": 12, "eth_fast_aggregate_verify": 12,
            "eth_aggregate_pubkeys": 8, "deserialization_G1": 13, "deserialization_G2": 15, "hash_to_G2": 4}
HASH_DST = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"

def h(text):
    text = text[2:] if text.startswith("0x") else text
    bytes.fromhex(text)
    return text.lower() or "-"

def hs(items):
    return ",".join(h(i) for i in items) or "-"

def truth(value):
    return "true" if value else "false"

def line(case):
    suite, i, o = case["suite"], case["input"], case["output"]
    if suite == "verify":
        return [truth(o), h(i["pubkey"]), h(i["message"]), h(i["signature"])]
    if suite == "aggregate_verify":
        return [truth(o), hs(i["pubkeys"]), hs(i["messages"]), h(i["signature"])]
    if suite in ("fast_aggregate_verify", "eth_fast_aggregate_verify"):
        return [truth(o), hs(i["pubkeys"]), h(i["message"]), h(i["signature"])]
    if suite == "eth_aggregate_pubkeys":
        return ["null" if o is None else h(o), hs(i)]
    if suite == "deserialization_G1":
        return [truth(o), h(i["pubkey"])]
    if suite == "deserialization_G2":
        return [truth(o), h(i["signature"])]
    if suite == "hash_to_G2":
        x, y = o["x"].split(","), o["y"].split(",")
        return [",".join(h(v) for v in (x[0], x[1], y[0], y[1])), HASH_DST.hex(), i["msg"].encode().hex() or "-"]
    raise SystemExit("unknown suite " + suite)

def alter(expected):
    if expected == "true": return "false"
    if expected == "false": return "true"
    if expected == "null": return "00"
    return ("1" if expected[0] != "1" else "2") + expected[1:]

def run(binary, rows):
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        for row in rows:
            f.write(" ".join(row) + "\n")
    try:
        done = subprocess.run([binary, "--vectors", f.name], capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(f.name)
    mismatches = [l for l in done.stdout.splitlines() if l.startswith("MISMATCH")]
    return done.returncode, mismatches, done.stdout

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True)
    parser.add_argument("--vectors", default=os.path.join(here, "../../../../../third_party/ethereum-bls-vectors/bls-signature.json"))
    args = parser.parse_args()
    raw = open(args.vectors, "rb").read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PIN:
        sys.exit("vector file digest %s is not the pinned %s" % (digest, PIN))
    cases = json.loads(raw)["cases"]
    counts = {}
    rows = []
    for case in cases:
        counts[case["suite"]] = counts.get(case["suite"], 0) + 1
        rows.append([case["suite"], case["name"]] + line(case))
    code, mismatches, out = run(args.binary, rows)
    # Control: alter the expectation of the first case of every suite.
    altered, names, seen = [], [], set()
    for row in rows:
        if row[0] not in seen:
            seen.add(row[0])
            names.append(row[0] + " " + row[1])
            row = row[:2] + [alter(row[2])] + row[3:]
        altered.append(row)
    control_code, control_mismatches, _ = run(args.binary, altered)
    reported = [m.split()[1] + " " + m.split()[2].rstrip(":") for m in control_mismatches]
    control_ok = control_code != 0 and sorted(reported) == sorted(names)
    summary = {
        "status": "pass" if code == 0 and not mismatches and counts == EXPECTED and control_ok else "fail",
        "cases": len(rows), "failed": len(mismatches), "suites": counts,
        "valid": sum(1 for r in rows if r[2] == "true"), "invalidOrFalse": sum(1 for r in rows if r[2] in ("false", "null")),
        "alteredExpectationControls": len(names), "alteredExpectationControlsReported": len(set(reported) & set(names)),
        "vectorFileSha256": digest,
    }
    for m in mismatches[:20]:
        print(m, file=sys.stderr)
    if counts != EXPECTED:
        print("suite counts differ from the expected ones: %r" % counts, file=sys.stderr)
    if not control_ok:
        print("control: exit %d, reported %r, wanted %r" % (control_code, reported, names), file=sys.stderr)
    print(json.dumps(summary))
    sys.exit(0 if summary["status"] == "pass" else 1)

main()
