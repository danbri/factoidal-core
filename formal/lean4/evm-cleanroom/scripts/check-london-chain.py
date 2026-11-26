"""Independent formula oracle. Python is not part of the client."""
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

H = 12_965_000
U64 = 1 << 64
U256 = 1 << 256

def reject(reason, indeterminate=False):
    return {"status": "indeterminate" if indeterminate else "error", "reason": reason}

def oracle(row):
    pn, pt, ph, pl, pu, pf, cn, ct, ch, cl, cu, cf = row
    if max(pn, pt, cn, ct) >= U64 or max(ph, ch) >= U256:
        return reject("resource-limit", True)
    if cn < H:
        return reject("earlier-fork", True)
    if cn != pn + 1:
        return reject("number-mismatch")
    if ct <= pt:
        return reject("timestamp-mismatch")
    if ph != ch:
        return reject("parent-hash-mismatch")
    if max(pl, pu, cl, cu) >= U64 or cf >= U256 or (pf is not None and pf >= U256):
        return reject("resource-limit", True)
    if pu > pl:
        return reject("parent-gas-exceeds-limit")
    if cu > cl:
        return reject("child-gas-exceeds-limit")
    ref = 2 * pl if cn == H else pl
    if min(pl, cl) < 5000 or abs(cl - ref) >= ref // 1024:
        return reject("invalid-gas-limit")
    if cn == H:
        if pf is not None:
            return reject("unexpected-parent-fee")
        expected = 10**9
    else:
        if pf is None:
            return reject("missing-parent-fee", True)
        target = pl // 2
        delta = pf * abs(pu - target) // target // 8
        expected = pf + max(1, delta) if pu > target else pf - delta
    if cf != expected:
        return reject("incorrect-base-fee")
    return {"status": "ok", "expectedBaseFee": str(expected)}

def fixture():
    rng = random.Random(850)
    rows = []
    for i in range(1536):
        cn = [H-1, H, H+1, H+100, U64-1][i % 5]
        pn, pt, ph = cn-1, rng.randrange(1, U64-32), rng.getrandbits(256)
        pl = rng.randint(5000, 50_000_000)
        pu = [0, pl//2, pl//2+1, pl][i % 4]
        pf = None if cn <= H else rng.choice([0, 1, 10**9, rng.randrange(1, 10**18)])
        cl = pl * (2 if cn == H else 1)
        if cn == H:
            cf = 10**9
        elif pf is None:
            cf = 0
        else:
            d = pf * abs(pu-pl//2) // (pl//2) // 8
            cf = pf + max(1, d) if pu > pl//2 else pf-d
        row = [pn, pt, ph, pl, pu, pf, cn, pt+12, ph, cl, 0, cf]
        rows.append(row)
        j, value = [(0,pn-1),(7,pt),(8,ph^1),(11,cf+1),(6,U64),(2,U256),
                    (5,None if pf is not None else 1),(9,cl+cl//1024),
                    (4,pl+1),(10,cl+1),(7,U64),(3,U64)][i%12]
        changed = row.copy()
        changed[j] = value
        rows.append(changed)
    return rows

def compare(expected, actual):
    if len(actual) != len(expected):
        raise ValueError("output cardinality mismatch")
    for i, (e, a) in enumerate(zip(expected, actual)):
        if e != a:
            raise ValueError(f"row {i}: expected {e}, actual {a}")

def main():
    exe = str(Path(sys.argv[1]).resolve())
    rows = fixture()
    expected = [oracle(row) for row in rows]
    with tempfile.TemporaryDirectory() as td:
        path = Path(td)/"rows.tsv"
        path.write_text("".join("\t".join("-" if v is None else str(v) for v in row)+"\n" for row in rows))
        result = subprocess.run([exe,"--batch",str(path)], capture_output=True, text=True, check=True, timeout=120)
        actual = [json.loads(line) for line in result.stdout.splitlines()]
        compare(expected, actual)
        malformed = subprocess.run([exe,"bad"], capture_output=True, text=True, timeout=10)
        assert malformed.returncode == 2 and json.loads(malformed.stdout)["status"] == "inputError"
    controls = [actual[:-1], [{"status":"forged"}]+actual[1:], actual.copy()]
    controls[2][0] = {"status":"ok","expectedBaseFee":"0"}
    for c in controls:
        try:
            compare(expected, c)
        except ValueError:
            pass
        else:
            raise AssertionError("mutation not detected")
    counts = {k: sum(x["status"]==k for x in actual) for k in ("ok","error","indeterminate")}
    print(json.dumps({"cases":len(rows),"matched":len(actual),"counts":counts,"mutationsRejected":len(controls),"malformedRejected":True}))

if __name__ == "__main__":
    main()
