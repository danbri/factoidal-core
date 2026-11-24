#!/usr/bin/env python3
"""Independent attester-slashing preparation oracle; no runtime dependency."""
import hashlib
import json
import random
import subprocess
import sys
import time
from collections import Counter

FIELDS = ("slot", "committee_index", "beacon_block_root", "source_epoch",
          "source_root", "target_epoch", "target_root")
MAX = 2**64 - 1

def digest(a, b):
    return hashlib.sha256(a + b).digest()

def u(n):
    return n.to_bytes(32, "little")

def signing(q, d):
    a, b, c = (bytes.fromhex(d[k]) for k in
               ("beacon_block_root", "source_root", "target_root"))
    source = digest(u(d["source_epoch"]), b)
    target = digest(u(d["target_epoch"]), c)
    zero = bytes(32)
    root = digest(digest(digest(u(d["slot"]), u(d["committee_index"])),
                         digest(a, source)),
                  digest(digest(target, zero), digest(zero, zero)))
    version = bytes.fromhex(q["previous_version"] if d["target_epoch"] <
                            q["activation_epoch"] else q["current_version"])
    domain = bytes([1, 0, 0, 0]) + digest(version.ljust(32, b"\0"),
              bytes.fromhex(q["genesis_validators_root"]))[:28]
    return digest(root, domain).hex()

def err(e):
    return {"status": "error", "error": e}

def expected(q):
    a, b = ({k: q[p + k] for k in FIELDS} for p in ("a_", "b_"))
    x, y = q["a_indices"], q["b_indices"]
    if len(x) > 32 or len(y) > 32:
        return err("resource_limit")
    if any(not xs or xs != sorted(set(xs)) for xs in (x, y)):
        return err("bad_indices")
    double = a != b and a["target_epoch"] == b["target_epoch"]
    surround = a["source_epoch"] < b["source_epoch"] and b["target_epoch"] < a["target_epoch"]
    if not (double or surround):
        return err("not_conflicting")
    common = sorted(set(x).intersection(y))
    if not common:
        return err("no_common_indices")
    return dict(status="prepared_not_authenticated", common_indices=common,
                first_signing_root=signing(q, a), second_signing_root=signing(q, b))

def request(a, b, x, y, activation=4):
    q = dict(op="attester_slashing_preflight", previous_version="01020304",
             current_version="05060708", activation_epoch=activation,
             genesis_validators_root="09"*32, a_indices=x, b_indices=y)
    q.update({"a_"+k: a[k] for k in FIELDS})
    q.update({"b_"+k: b[k] for k in FIELDS})
    return q

def corpus():
    a = dict(slot=31, committee_index=5, beacon_block_root=bytes(range(32)).hex(),
             source_epoch=3, source_root="01"*32, target_epoch=4, target_root="02"*32)
    b = dict(a, slot=32)
    first = request(a, b, [0, 1, MAX], [1, MAX])
    assert signing(first, a) == "4af74e8a7bbe68a8300a6f017951b74f9a7e35fd3ec8be32911b455697722b9b"
    rows = [(first, expected(first), "known_answer")]
    def add(q, label, e=None):
        rows.append((q, expected(q) if e is None else e, label))
    add(request(a, a, [1], [1]), "identical")
    for field in FIELDS:
        value = a[field]
        other = dict(a, **{field: value+1 if isinstance(value, int) else "ff"*32})
        add(request(a, other, [1], [1]), "changed_"+field)
    for x, y in [([], [1]), ([1], []), ([1,1], [1]), ([1], [2,1]),
                 ([2,1], [1]), ([1], [1,1]), ([1], [2]),
                 (list(range(32)), [31]), (list(range(33)), [1]),
                 ([1], list(range(33)))]:
        add(request(a,b,x,y), "index_boundary")
    rng = random.Random(87720261124)
    for i in range(1536):
        e = rng.randrange(1, 10000)
        base = dict(a, slot=rng.getrandbits(64), committee_index=rng.getrandbits(64),
                    source_epoch=e, target_epoch=e+4,
                    beacon_block_root=rng.randbytes(32).hex(),
                    source_root=rng.randbytes(32).hex(), target_root=rng.randbytes(32).hex())
        mode = i % 8
        other = dict(base)
        if mode == 0: other["slot"] ^= 1
        if mode == 1: other.update(source_epoch=e+1,target_epoch=e+3)
        if mode == 2: other.update(source_epoch=e-1,target_epoch=e+5)
        if mode == 3: other.update(source_epoch=e,target_epoch=e+3)
        if mode == 4: other.update(source_epoch=e+1,target_epoch=e+4)
        if mode == 5: other["target_epoch"] += 1
        if mode == 6: other["target_root"] = rng.randbytes(32).hex()
        x = sorted(rng.sample(range(32), 1+i%12))
        y = sorted(rng.sample(range(32), 1+(i//8)%12))
        if i%11 == 0: x = [0, MAX]
        if i%13 == 0: y = [0, MAX]
        if i%17 == 0: x = [1,1]
        if i%19 == 0: y = []
        add(request(base, other, x, y, activation=e+4), "generated_"+str(mode))
    for key in ("a_beacon_block_root", "b_source_root", "b_target_root"):
        add(dict(first, **{key:"00"}), "malformed_width", err("invalid_width"))
    add(dict(first,a_indices=[MAX+1]), "uint64_overflow", err("out_of_range"))
    add(dict(first,b_indices=[-1]), "negative_index", err("parse_error"))
    add(dict(first,extra=1), "extra_field", err("parse_error"))
    # Numeric parse errors from getObjValAs? have a library-specific string;
    # negative index is covered separately below without assuming that string.
    rows = [row for row in rows if row[2] != "negative_index"]
    return rows

def compare(actual, wanted):
    if actual != wanted:
        raise AssertionError(f"actual {actual!r} != expected {wanted!r}")

def main():
    rows = corpus()
    first = rows[0][1]
    assert first["status"] == "prepared_not_authenticated"
    mutations = [dict(first,status="ok"), dict(first,common_indices=[0]),
                 dict(first,first_signing_root="00"*32),
                 dict(first,second_signing_root=first["first_signing_root"])]
    for mutant in mutations:
        try: compare(mutant, first)
        except AssertionError: pass
        else: raise AssertionError("missed mutation")
    payload = "".join(json.dumps(q,separators=(",",":"))+"\n" for q,_,_ in rows)
    assert max(map(len,payload.splitlines())) < 2048
    if sys.argv[1:] == ["--oracle-self-test"]:
        print(json.dumps(dict(oracle_cases=len(rows),mutations_detected=len(mutations),
                              native_not_run=len(rows)),sort_keys=True))
        return
    started = time.monotonic()
    run = subprocess.run([sys.argv[1]],input=payload,text=True,capture_output=True,
                         timeout=180,check=True)
    elapsed = time.monotonic()-started
    lines = run.stdout.splitlines()
    assert len(lines) == len(rows), (len(lines), len(rows))
    for line,(q,wanted,label) in zip(lines,rows):
        try: compare(json.loads(line),wanted)
        except AssertionError as error: raise AssertionError((label,q)) from error
    # Refuse a negative index without relying on the standard parser's error wording.
    q = dict(rows[0][0],a_indices=[-1])
    bad = subprocess.run([sys.argv[1]],input=json.dumps(q)+"\n",text=True,
                         capture_output=True,timeout=10,check=True)
    assert json.loads(bad.stdout)["status"] == "error"
    print(json.dumps(dict(total=len(rows),passed=len(rows),failed=0,not_run=0,
        negative_index_refused=1,groups=dict(Counter(label for _,_,label in rows)),
        outcomes=dict(Counter(e.get("error",e["status"]) for _,e,_ in rows)),
        mutations_detected=len(mutations),elapsed_seconds=elapsed),sort_keys=True))

if __name__ == "__main__":
    main()
