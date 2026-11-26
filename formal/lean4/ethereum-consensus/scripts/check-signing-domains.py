#!/usr/bin/env python3
"""Independent hashlib test oracle, not runtime consensus code."""
import hashlib
import json
import random
import subprocess
import sys
from collections import Counter

def h(a, b):
    return hashlib.sha256(a + b).digest()

def tree(leaves):
    leaves = list(leaves)
    leaves += [bytes(32)] * ((1 << (len(leaves)-1).bit_length()) - len(leaves))
    while len(leaves) > 1:
        leaves = [h(a,b) for a,b in zip(leaves[::2], leaves[1::2])]
    return leaves[0]

def domain(c, t, epoch):
    version = bytes.fromhex(c["previous_version" if epoch < c["activation_epoch"]
                              else "current_version"])
    return t + h(version.ljust(32, b"\0"), bytes.fromhex(c["genesis_validators_root"]))[:28]

def root64(n):
    return n.to_bytes(8, "little").ljust(32, b"\0")

def corpus():
    rng = random.Random(84820261123)
    rows = []
    max64 = 2**64-1
    for i in range(640):
        activation = [0, 1, 2, 2**32, max64][i % 5] if i < 200 else rng.getrandbits(64)
        epoch = [max(0,activation-1), activation, min(max64,activation+1), 0, max64][i % 5]
        ctx = dict(previous_version=rng.randbytes(4).hex(), current_version=rng.randbytes(4).hex(),
                   activation_epoch=activation, genesis_validators_root=rng.randbytes(32).hex())
        t = rng.randbytes(4) if i % 7 else bytes(4)
        rows.append((dict(op="signing_domain", domain_type=t.hex(), epoch=epoch, **ctx),
                     dict(status="ok", domain=domain(ctx,t,epoch).hex()), "domain"))
        # Bound transition epochs to the slot-derived epoch range for header tests.
        activation = [0,1,2, max64//32][i % 4] if i < 200 else rng.getrandbits(59)
        ctx = dict(ctx, activation_epoch=activation)
        slot = min(max64, [max(0, activation*32-1), activation*32,
                           activation*32+31, max64][i % 4])
        proposer = rng.getrandbits(64)
        parent,state,body = (rng.randbytes(32) for _ in range(3))
        obj = tree([root64(slot), root64(proposer), parent,state,body])
        d = domain(ctx, bytes(4),slot//32)
        rows.append((dict(op="proposer_header_signing", slot=slot, proposer_index=proposer,
                          parent_root=parent.hex(), state_root=state.hex(),body_root=body.hex(), **ctx),
                     dict(status="ok",object_root=obj.hex(),domain=d.hex(),signing_root=h(obj,d).hex()),"header"))
    for req, _, _ in rows[:16]:
        for key in ("previous_version","current_version","genesis_validators_root"):
            rows.append((dict(req, **{key:"00"}),dict(status="error",error="invalid_width"),"bad_width"))
    req = rows[0][0]
    rows.extend([
        (dict(req,domain_type="00"),dict(status="error",error="invalid_width"),"bad_width"),
        (dict(req,epoch=2**64),dict(status="error",error="out_of_range"),"bad_epoch"),
        (dict(req,extra=0),dict(status="error",error="parse_error"),"extra"),
        ({k:v for k,v in req.items() if k!="previous_version"},
         dict(status="error",error="parse_error"),"missing"),
    ])
    return rows

def compare(actual, expected):
    if actual != expected:
        raise AssertionError(f"actual {actual!r} != expected {expected!r}")

def main():
    rows=corpus()
    result=subprocess.run([sys.argv[1]],input="".join(json.dumps(r)+"\n" for r,_,_ in rows),
                          text=True,capture_output=True,timeout=180,check=True)
    lines=result.stdout.splitlines()
    if len(lines)!=len(rows):
        raise AssertionError("incorrect result count")
    for line,(request,expected,label) in zip(lines,rows):
        try:
            compare(json.loads(line),expected)
        except AssertionError as e:
            raise AssertionError(f"{label}: {request}: {e}") from e
    expected=rows[1][1]
    for k in ("object_root","domain","signing_root"):
        bad=dict(expected,**{k:"ff"*32})
        try:
            compare(bad,expected)
        except AssertionError:
            pass
        else:
            raise AssertionError("comparator accepted corrupted "+k)
    print(json.dumps(dict(total=len(rows),passed=len(rows),failed=0,
                          groups=dict(Counter(x[2] for x in rows)),mutations_detected=3),sort_keys=True))
if __name__=="__main__":
    main()
