#!/usr/bin/env python3
"""Compare the native Lean precompile router with published vectors and independent oracles.

The oracles are test inputs only: published vector files pinned by SHA-256 in
sources.json (downloaded, never vendored or linked) and the Python standard
library (hashlib, pow) on generated inputs. Nothing here supplies a runtime
answer to the Lean code. The run fails closed: a missing file, a digest
mismatch, an unparsable line or a single disagreement is a failure.

Negative controls: for every vector file one expected output is altered and
the comparator must report it; every vector with a price is re-run with one
gas unit less and must fail.
"""
import argparse
import hashlib
import json
import random
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = json.loads((HERE / "sources.json").read_text())
AMPLE_GAS = 10_000_000_000


def fetch(entry, cache, offline):
    path = cache / entry["file"]
    if not path.is_file():
        if offline:
            raise SystemExit("missing cached vector file: " + entry["file"])
        url = SOURCES["base"] + entry["file"]
        with urllib.request.urlopen(url, timeout=120) as response:
            path.write_bytes(response.read())
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != entry["sha256"]:
        raise SystemExit("digest mismatch for %s: %s" % (entry["file"], digest))
    return json.loads(data)


def run_batch(binary, cases):
    """cases: list of (profile, address, gas, hex input). Returns output lines."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as handle:
        for profile, address, gas, data in cases:
            handle.write("%s %d %d %s\n" % (profile, address, gas, data or "-"))
        name = handle.name
    done = subprocess.run([binary, "--dangerously-enable-unverified-keccak", "--batch", name],
                          capture_output=True, text=True, timeout=3600)
    Path(name).unlink()
    if done.returncode != 0:
        raise SystemExit("precompile binary failed: " + done.stderr[:400])
    lines = done.stdout.splitlines()
    if len(lines) != len(cases):
        raise SystemExit("expected %d result lines, got %d" % (len(cases), len(lines)))
    return lines


def expected_line(kind, gas, output):
    if kind == "fail":
        return "fail"
    return "ok %d %s" % (gas, output.lower())


def agrees(kind, want, got):
    """output-only vectors compare bytes but not the price (a different price rule)."""
    if kind == "output-only":
        return got.startswith("ok ") and got.split(" ")[2:] == want.split(" ")[2:]
    return got == want


def vector_cases(entry, vectors):
    """Yield (label, case, kind, expected line) for one file, with derived gas-shortfall cases."""
    profile, address, kind = entry["profile"], entry["address"], entry["kind"]
    for index, vector in enumerate(vectors):
        label = "%s[%d] %s" % (entry["file"], index, vector.get("Name", ""))
        data = vector["Input"].lower()
        if kind == "fail":
            yield label, (profile, address, AMPLE_GAS, data), "fail", "fail"
            continue
        output = vector["Expected"]
        if kind == "output-only":
            yield label, (profile, address, AMPLE_GAS, data), kind, expected_line("ok", 0, output)
            continue
        gas = int(vector["Gas"])
        yield label, (profile, address, gas, data), "ok", expected_line("ok", gas, output)
        if gas > 0:
            yield label + " (one gas short)", (profile, address, gas - 1, data), "fail", "fail"


def blake2_single_block(message):
    """The F input for a one-block unkeyed BLAKE2b-512 message, and its hashlib digest."""
    iv = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
          0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]
    h = [iv[0] ^ 0x01010040] + iv[1:]
    data = (12).to_bytes(4, "big") + b"".join(x.to_bytes(8, "little") for x in h)
    data += message.ljust(128, b"\0") + len(message).to_bytes(8, "little") + bytes(8) + b"\x01"
    return data.hex(), hashlib.blake2b(message).hexdigest()


def modexp_cases(rng, count):
    def price(rule, blen, elen, mlen, head):
        longest = max(blen, mlen)
        words = (longest + 7) // 8
        bits = max(head.bit_length() - 1, 0)
        if rule == "osaka":
            iterations = bits if elen <= 32 else 16 * (elen - 32) + bits
            complexity = 16 if longest <= 32 else 2 * words * words
            return max(500, complexity * max(iterations, 1))
        iterations = bits if elen <= 32 else 8 * (elen - 32) + bits
        return max(200, words * words * max(iterations, 1) // 3)

    for _ in range(count):
        blen, elen, mlen = (rng.choice([0, 1, 2, 31, 32, 33, 64, 65, 96, 255, 256, rng.randrange(0, 300)])
                            for _ in range(3))
        base = rng.randbytes(blen)
        exponent = rng.choice([rng.randbytes(elen), bytes(elen), bytes(max(elen - 1, 0)) + b"\x01"[:elen]])
        modulus = rng.choice([rng.randbytes(mlen), bytes(mlen), bytes(max(mlen - 1, 0)) + b"\x01"[:mlen]])
        full = b"".join(x.to_bytes(32, "big") for x in (blen, elen, mlen)) + base + exponent + modulus
        cut = rng.choice([len(full), len(full), rng.randrange(0, len(full) + 1)])
        data = full[:cut]
        padded = data + bytes(len(full) - cut)
        # A cut inside the header changes the declared lengths themselves.
        blen, elen, mlen = (int.from_bytes(padded[i:i + 32], "big") for i in (0, 32, 64))
        padded += bytes(96 + blen + elen + mlen)
        b = int.from_bytes(padded[96:96 + blen], "big")
        e = int.from_bytes(padded[96 + blen:96 + blen + elen], "big")
        m = int.from_bytes(padded[96 + blen + elen:96 + blen + elen + mlen], "big")
        head = int.from_bytes(padded[96 + blen:96 + blen + min(32, elen)], "big")
        value = b"" if mlen == 0 else (bytes(mlen) if m == 0 else pow(b, e, m).to_bytes(mlen, "big"))
        for profile in ("shanghaiPlus", "osaka"):
            gas = price(profile, blen, elen, mlen, head)
            if profile == "osaka" and max(blen, elen, mlen) > 1024:
                continue
            yield "modexp/%s" % profile, (profile, 5, gas, data.hex()), "ok", expected_line("ok", gas, value.hex())
            yield "modexp/%s short" % profile, (profile, 5, gas - 1, data.hex()), "fail", "fail"


def kzg_cases():
    """The consensus-specification verify_kzg_proof cases as point-evaluation calls.

    The versioned hash is computed here with hashlib. A true verdict must return the
    constant output for exactly 50000 gas; a false verdict and rejected input must fail.
    """
    path = HERE.parents[3].parent / "third_party/ethereum-kzg-vectors/kzg-verify-proof.json"
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != SOURCES["kzgVectorsSha256"]:
        raise SystemExit("digest mismatch for the KZG proof vectors")
    constant = (4096).to_bytes(32, "big").hex() + \
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    for case in json.loads(data)["cases"]:
        commitment = bytes.fromhex(case["commitment"])
        versioned = "01" + hashlib.sha256(commitment).hexdigest()[2:]
        call = versioned + case["z"] + case["y"] + case["commitment"] + case["proof"]
        label = "kzg " + case["name"]
        if case["output"] is True:
            yield label, ("cancunPlus", 10, 50000, call), "ok", expected_line("ok", 50000, constant)
            yield label + " short", ("cancunPlus", 10, 49999, call), "fail", "fail"
            wrong = ("02" if versioned[:2] == "01" else "01") + versioned[2:]
            yield label + " wrong version byte", ("cancunPlus", 10, 50000, wrong + call[64:]), "fail", "fail"
        else:
            yield label, ("cancunPlus", 10, AMPLE_GAS, call), "fail", "fail"


def differential_cases(seed, count):
    rng = random.Random(seed)
    for _ in range(count):
        size = rng.choice([0, 1, 31, 32, 33, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, rng.randrange(0, 2000)])
        message = rng.randbytes(size)
        words = (size + 31) // 32
        gas = 60 + 12 * words
        yield "sha256", ("shanghaiPlus", 2, gas, message.hex()), "ok", \
            expected_line("ok", gas, hashlib.sha256(message).hexdigest())
        yield "sha256 short", ("shanghaiPlus", 2, gas - 1, message.hex()), "fail", "fail"
        gas = 600 + 120 * words
        digest = hashlib.new("ripemd160", message).hexdigest()
        yield "ripemd160", ("shanghaiPlus", 3, gas, message.hex()), "ok", expected_line("ok", gas, "00" * 12 + digest)
        yield "ripemd160 short", ("shanghaiPlus", 3, gas - 1, message.hex()), "fail", "fail"
        block = rng.randbytes(rng.randrange(1, 129))
        data, digest = blake2_single_block(block)
        yield "blake2f", ("shanghaiPlus", 9, 12, data), "ok", expected_line("ok", 12, digest)
        yield "blake2f short", ("shanghaiPlus", 9, 11, data), "fail", "fail"
    yield from modexp_cases(rng, count)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--differential", type=int, default=300)
    parser.add_argument("--seed", type=int, default=20261127)
    parser.add_argument("--only", help="comma-separated vector file names")
    args = parser.parse_args()
    args.cache.mkdir(parents=True, exist_ok=True)
    try:
        hashlib.new("ripemd160", b"")
    except ValueError:
        raise SystemExit("this Python has no RIPEMD-160; the independent oracle is unavailable")

    only = set(args.only.split(",")) if args.only else None
    labels, cases, kinds, wanted, per_file = [], [], [], [], {}
    for entry in SOURCES["files"]:
        if only and entry["file"] not in only:
            continue
        before = len(cases)
        for label, case, kind, want in vector_cases(entry, fetch(entry, args.cache, args.offline)):
            labels.append(label); cases.append(case); kinds.append(kind); wanted.append(want)
        per_file[entry["file"]] = (before, len(cases))
    if not only or "kzg" in only:
        before = len(cases)
        for label, case, kind, want in kzg_cases():
            labels.append(label); cases.append(case); kinds.append(kind); wanted.append(want)
        per_file["kzg-verify-proof.json"] = (before, len(cases))
    published = len(cases)
    if not only:
        for label, case, kind, want in differential_cases(args.seed, args.differential):
            labels.append(label); cases.append(case); kinds.append(kind); wanted.append(want)

    got = run_batch(args.binary, cases)
    failures = [(labels[i], wanted[i][:160], got[i][:160])
                for i in range(len(cases)) if not agrees(kinds[i], wanted[i], got[i])]

    # Negative controls: an altered expected output must be reported by the same comparison.
    controls = rejected = 0
    for name, (start, stop) in per_file.items():
        for i in range(start, stop):
            if kinds[i] != "fail" and wanted[i].split(" ")[2:] != [""]:
                altered = wanted[i][:-1] + ("0" if wanted[i][-1] != "0" else "1")
                controls += 1
                rejected += not agrees(kinds[i], altered, got[i])
                break
    shortfalls = sum(1 for label in labels if label.endswith("short") or label.endswith("(one gas short)"))

    report = {
        "status": "pass" if not failures and controls == rejected else "fail",
        "source": SOURCES["base"],
        "files": len(per_file),
        "publishedCases": published,
        "differentialCases": len(cases) - published,
        "gasShortfallControls": shortfalls,
        "alteredOutputControls": controls,
        "alteredOutputControlsRejected": rejected,
        "failed": len(failures),
        "failures": failures[:20],
        "perFile": {name: stop - start for name, (start, stop) in per_file.items()},
    }
    print(json.dumps(report, indent=1))
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
