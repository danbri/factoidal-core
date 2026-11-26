#!/usr/bin/env python3
"""Exercise resource admission before JSON parsing in all transaction CLIs.

The fixed singleton fixture supplies valid byte transports. This is a parser
and transport regression suite, not another signature or consensus oracle.
Only the nine small spelling controls may run on an optional retained
pre-guard build. Deep inputs and large exponents run only on guarded binaries.
"""

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "scripts/fixtures/transaction-list-transport.json"
GUARD_ERRORS = {"json-nesting-limit", "json-number-token-limit", "json-exponent-limit"}
MAX_FILE_BYTES = 16 * 1024 * 1024
DEEP_LEVELS = 3_000_000


def encoded(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fixture_inputs():
    fixture = json.loads(FIXTURE.read_text())
    source, observed = fixture["input"], fixture["expected"]
    entry, receipt = source["transactions"][0], observed["receipts"][0]
    header = source["childHeader"]

    def field(index):
        return str(int(header[index] or "0", 16))

    blob_burn = int(receipt["blobFeeBurn"])
    ordinary_tx = copy.deepcopy(entry["transaction"])
    ordinary_tx["type"] = 2
    ordinary_input = {
        "schemaVersion": 1, "fork": "cancun", "fuel": entry["fuel"],
        "transaction": ordinary_tx, "accounts": copy.deepcopy(source["accounts"]),
        "block": {
            "chainId": "1", "coinbase": field(2), "number": field(8), "timestamp": field(11),
            "gasLimit": field(9), "gasUsedBefore": "0", "baseFee": field(15),
            "prevRandao": field(13), "blobBaseFee": str(blob_burn // int(receipt["blobGasUsed"])),
        },
    }
    blob_input = copy.deepcopy(ordinary_input)
    blob_input.update({
        "transaction": copy.deepcopy(entry["transaction"]),
        "parentHeader": source["parentHeader"], "childHeader": header,
        "blobVersionedHashes": entry["blobVersionedHashes"],
        "maxFeePerBlobGas": entry["maxFeePerBlobGas"], "priorBlobGas": "0",
    })
    inner_receipt = {key: copy.deepcopy(value) for key, value in receipt.items()
                     if key not in ("type", "blobGasUsed", "blobFeeBurn")}
    blob_inner = {
        "schemaVersion": 1, "status": "executed", "keccakOptIn": True,
        **inner_receipt, "accounts": copy.deepcopy(observed["accounts"]),
    }
    blob_expected = {
        "status": "executed", "blobGasUsed": receipt["blobGasUsed"],
        "blobFeeBurn": receipt["blobFeeBurn"], "result": blob_inner,
    }
    ordinary_expected = copy.deepcopy(blob_inner)
    ordinary_expected["returnBytesHex"] = "00" * 32
    sender = ordinary_tx["sender"]
    for account in ordinary_expected["accounts"]:
        if account["address"] == sender:
            account["balance"] = str(int(account["balance"]) + blob_burn)

    list_input = copy.deepcopy(source)
    list_input["transactions"] = [{"fuel": entry["fuel"], "transaction": ordinary_tx}]
    list_input["childHeader"][17] = ""
    list_expected = copy.deepcopy(observed)
    list_expected["blobGasUsed"] = "0"
    list_expected["accounts"] = ordinary_expected["accounts"]
    list_expected["receipts"][0].update({
        "type": 2, "blobGasUsed": "0", "blobFeeBurn": "0", "returnBytesHex": "00" * 32,
    })
    return [
        {"id": "call-transaction", "executable": "evm-call-transaction", "flag": "--call-transaction",
         "input": ordinary_input, "expected": ordinary_expected, "type": 2},
        {"id": "blob-call", "executable": "evm-blob-call", "flag": "--batch",
         "input": blob_input, "expected": blob_expected, "type": 3},
        {"id": "transaction-list", "executable": "evm-transaction-list", "flag": "--transaction-list",
         "input": list_input, "expected": list_expected, "type": 2},
    ]


def cases_for(spec):
    canonical = encoded(spec["input"])
    rows = []

    def add(name, raw, kind="probe", reason=None, baseline=False):
        assert len(raw) < MAX_FILE_BYTES, (name, len(raw))
        rows.append({"id": name, "raw": raw, "kind": kind, "reason": reason, "baseline": baseline})

    def probe(name, value, reason=None):
        add(name, canonical[:-1] + b',"probe":' + value + b"}", "guard" if reason else "probe", reason)

    add("canonical-valid", canonical, "accepted", baseline=True)
    add("empty-object", b"{}", "schema-error")
    # The enclosing request object counts as the first structural level.
    probe("depth-exact-64", b"[" * 63 + b"0" + b"]" * 63)
    probe("depth-one-over-65", b"[" * 64 + b"0" + b"]" * 64, "json-nesting-limit")
    # Match the reproduced depth and 6,000,034-byte size below the file cap.
    deep = b'{"schemaVersion":1,"transaction":' + b"[" * DEEP_LEVELS + b"]" * DEEP_LEVELS + b"}"
    assert len(deep) == 6_000_034
    add("three-million-nested-arrays", deep, "guard", "json-nesting-limit")
    probe("escaped-quote-keeps-lexemes-in-string", encoded('escaped quote " and slash \\ ' +
          "[" * 100 + "9" * 97 + " 1e9999999999999999999 " + "}" * 100))
    probe("unicode-escapes-are-string-data", b'"' + b"\\u005b" * 100 + b"\\u0022" +
          b"\\u0039" * 97 + b"\\u005d" * 100 + b'"')
    # An escaped backslash must not hide the following closing quote and token.
    after_backslash = canonical[:-1] + b',"probe":' + encoded("\\") + b',"numeric":' + b"9" * 97 + b"}"
    add("escaped-backslash-before-large-number", after_backslash, "guard", "json-number-token-limit")
    probe("number-token-exact-96", b"9" * 96)
    probe("number-token-one-over-97", b"9" * 97, "json-number-token-limit")
    probe("negative-token-exact-96", b"-" + b"9" * 95)
    probe("negative-token-one-over-97", b"-" + b"9" * 96, "json-number-token-limit")
    probe("decimal-token-exact-96", b"1." + b"0" * 94)
    probe("decimal-token-one-over-97", b"1." + b"0" * 95, "json-number-token-limit")
    probe("zero-padded-exponent-token-exact-96", b"1e+" + b"0" * 93)
    probe("zero-padded-exponent-token-one-over-97", b"1e+" + b"0" * 94, "json-number-token-limit")
    for spelling, token in [("unsigned", b"1e"), ("positive", b"1e+"), ("negative", b"1e-")]:
        probe("exponent-" + spelling + "-exact-78", token + b"78")
        probe("exponent-" + spelling + "-one-over-79", token + b"79", "json-exponent-limit")
    probe("leading-zero-exponent-exact-78", b"1e+00078")
    probe("leading-zero-exponent-one-over-79", b"1e+00079", "json-exponent-limit")
    probe("uppercase-exponent-exact-78", b"1E+78")
    probe("uppercase-exponent-one-over-79", b"1E+79", "json-exponent-limit")
    probe("compact-huge-positive-exponent", b"1e1000000000", "json-exponent-limit")
    probe("compact-huge-negative-exponent", b"1e-9999999999999999999", "json-exponent-limit")
    assert canonical.count(b'"schemaVersion":1') == 1
    add("schema-version-exponent-spelling", canonical.replace(b'"schemaVersion":1', b'"schemaVersion":1e0'),
        "accepted", baseline=True)
    key = ('"type":' + str(spec["type"])).encode()
    assert canonical.count(key) == 1
    add("integral-transaction-type-decimal-spelling", canonical.replace(key, key + b".0"),
        "schema-error", "Natural number expected", baseline=True)
    assert len(rows) == 30 and len({row["id"] for row in rows}) == 30
    return rows


def child_limits():
    for option, requested in [(resource.RLIMIT_AS, 8 * 1024**3), (resource.RLIMIT_STACK, 64 * 1024**2)]:
        _, hard = resource.getrlimit(option)
        value = requested if hard == resource.RLIM_INFINITY else min(requested, hard)
        resource.setrlimit(option, (value, hard))


def run(executable, spec, raw, path):
    path.write_bytes(raw)
    environment = dict(os.environ, LEAN_NUM_THREADS="1", MIMALLOC_ARENA_RESERVE="64MiB")
    process = subprocess.run([str(executable), "--dangerously-enable-unverified-keccak", spec["flag"], str(path)],
                             capture_output=True, timeout=30, check=False, env=environment, preexec_fn=child_limits)
    assert process.returncode in (0, 2), (spec["id"], process.returncode, process.stderr[:2000])
    assert not process.stderr, (spec["id"], process.stderr[:2000])
    value = json.loads(process.stdout)
    assert isinstance(value, dict)
    return process.returncode, process.stdout, value


def check(bin_dir, baseline_dir=None):
    rows, baseline_rows = [], []
    native_hashes, baseline_hashes = {}, {}
    with tempfile.TemporaryDirectory(prefix="lean-transaction-json-guard-") as temporary:
        path = Path(temporary) / "request.json"
        for spec in fixture_inputs():
            executable = (bin_dir / spec["executable"]).resolve()
            native_hashes[spec["executable"]] = digest(executable.read_bytes())
            if baseline_dir:
                baseline_executable = (baseline_dir / spec["executable"]).resolve()
                baseline_hashes[spec["executable"]] = digest(baseline_executable.read_bytes())
            canonical_stdout = None
            for case in cases_for(spec):
                code, stdout, value = run(executable, spec, case["raw"], path)
                label = spec["id"] + "/" + case["id"]
                expected_kind = case["kind"]
                if expected_kind == "accepted" or expected_kind == "probe" and spec["id"] != "transaction-list":
                    assert code == 0 and value == spec["expected"], (label, code, value)
                    if canonical_stdout is None:
                        canonical_stdout = stdout
                    assert stdout == canonical_stdout, (label, "accepted transport changed exact output bytes")
                else:
                    assert code == 2 and value.get("status") == "inputError", (label, code, value)
                    reason = value.get("reason")
                    assert isinstance(reason, str) and reason, (label, value)
                    assert not any(key in value for key in ("accounts", "receipts", "result", "gasUsed", "blobGasUsed")), (label, value)
                    if expected_kind == "guard":
                        assert reason == case["reason"], (label, value)
                    elif expected_kind == "probe":
                        assert reason == "unexpected field: probe", (label, value)
                    else:
                        assert reason not in GUARD_ERRORS, (label, value)
                        if case["reason"] is not None:
                            assert reason == case["reason"], (label, value)
                rows.append({
                    "id": label, "matched": True, "status": value["status"], "exitCode": code,
                    "reason": value.get("reason"), "inputBytes": len(case["raw"]),
                    "inputSha256": digest(case["raw"]), "outputSha256": digest(stdout),
                    "lexicalGuardRefusal": expected_kind == "guard",
                })
                if baseline_dir and case["baseline"]:
                    # Never send attack-size inputs to the old parser.
                    assert expected_kind in ("accepted", "schema-error") and len(case["raw"]) < 16_384
                    before_code, before_stdout, before_value = run(baseline_executable, spec, case["raw"], path)
                    assert before_code == code and before_stdout == stdout and before_value == value, label
                    baseline_rows.append({"id": label, "matched": True, "status": value["status"],
                                          "outputSha256": digest(stdout)})
    assert len(rows) == 90 and len({row["id"] for row in rows}) == 90
    assert sum(row["lexicalGuardRefusal"] for row in rows) == 42
    assert len(baseline_rows) == (9 if baseline_dir else 0)
    return {
        "kind": "transaction-json-preparse-resource-guards", "cases": len(rows), "matched": len(rows),
        "failed": 0, "failures": [], "lexicalGuardRefusals": 42,
        "perExecutable": {spec["executable"]: 30 for spec in fixture_inputs()},
        "limits": {"depth": 64, "numberTokenBytes": 96, "exponentMagnitude": 78,
                   "virtualMemoryBytes": 8 * 1024**3, "stackBytes": 64 * 1024**2, "timeoutSeconds": 30},
        "baselineParityCases": len(baseline_rows), "baselineParity": baseline_rows,
        "baselineAcceptedParityCases": sum(row["status"] == "executed" for row in baseline_rows),
        "baselineRejectedParityCases": sum(row["status"] == "inputError" for row in baseline_rows),
        "guardedInvocations": len(rows), "baselineInvocations": len(baseline_rows),
        "nativeSha256": native_hashes, "baselineSha256": baseline_hashes,
        "fixtureSha256": digest(FIXTURE.read_bytes()), "rows": rows,
        "scope": "Lexical resource admission and normal-spelling transport parity only. JSON grammar/schema still use the existing parser. Attacks run only on guarded binaries; optional retained builds receive nine small spelling controls. The old schema accepts schemaVersion=1e0 but rejects type=2.0/type=3.0 as Natural number expected; both behaviours are preserved.",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bin-dir", type=Path, default=ROOT / ".lake/build/bin")
    parser.add_argument("--baseline-dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.bin_dir.resolve(), args.baseline_dir.resolve() if args.baseline_dir else None), sort_keys=True))


if __name__ == "__main__":
    main()
