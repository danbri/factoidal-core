#!/usr/bin/env python3
"""Independent test-only packing and SHA-256 tree oracle for attester signing."""
import hashlib
import json
import random
import subprocess
import sys
from collections import Counter

def h(a,b):
    return hashlib.sha256(a+b).digest()

def u64(n):
    return n.to_bytes(8,"little")

def pad(b):
    return b.ljust(32,b"\0")

def tree(leaves):
    level=list(leaves)
    level += [bytes(32)]*((1<<(len(level)-1).bit_length())-len(level))
    while len(level)>1:
        level=[h(a,b) for a,b in zip(level[::2],level[1::2])]
    return level[0]

def expected(q):
    slot,index,se,te=(u64(q[k]) for k in ("slot","committee_index","source_epoch","target_epoch"))
    beacon,sr,tr=(bytes.fromhex(q[k]) for k in ("beacon_block_root","source_root","target_root"))
    obj=tree([pad(slot),pad(index),beacon,tree([pad(se),sr]),tree([pad(te),tr])])
    version=bytes.fromhex(q["previous_version" if q["target_epoch"]<q["activation_epoch"] else "current_version"])
    domain=b"\x01\x00\x00\x00"+h(pad(version),bytes.fromhex(q["genesis_validators_root"]))[:28]
    return dict(status="ok",bytes=(slot+index+beacon+se+sr+te+tr).hex(),
                object_root=obj.hex(),domain=domain.hex(),signing_root=h(obj,domain).hex())

def corpus():
    rng=random.Random(86820261124)
    m=2**64-1
    k=dict(op="attester_signing",slot=31,committee_index=5,beacon_block_root=bytes(range(32)).hex(),
           source_epoch=3,source_root="01"*32,target_epoch=4,target_root="02"*32,
           previous_version="01020304",current_version="05060708",activation_epoch=4,
           genesis_validators_root="09"*32)
    e=expected(k)
    # Independently calculated with explicit eight-leaf SHA-256 expression.
    assert e["object_root"]=="da3e6b3c648db1318cf40e5d08b718ad9b971de73171d373311d08983cddd855"
    assert e["domain"]=="010000007aff414db0dee0fee921d1c122189fc1eceb5a3d41f01ee59b528ab2"
    assert e["signing_root"]=="4af74e8a7bbe68a8300a6f017951b74f9a7e35fd3ec8be32911b455697722b9b"
    rows=[(k,e,"known_answer")]
    for i in range(1280):
        activation=[0,1,2,2**32,m][i%5] if i<320 else rng.getrandbits(64)
        target=[max(0,activation-1),activation,min(m,activation+1),0,m][i%5]
        # Deliberately do not infer target epoch from slot: isolate the signing rule.
        q=dict(op="attester_signing",slot=[0,31,32,m][i%4] if i<320 else rng.getrandbits(64),
               committee_index=rng.getrandbits(64),source_epoch=rng.getrandbits(64),
               target_epoch=target,activation_epoch=activation,
               previous_version=rng.randbytes(4).hex(),current_version=rng.randbytes(4).hex(),
               genesis_validators_root=rng.randbytes(32).hex(),
               beacon_block_root=rng.randbytes(32).hex(),source_root=rng.randbytes(32).hex(),
               target_root=rng.randbytes(32).hex())
        rows.append((q,expected(q),"target_previous" if target<activation else "target_current"))
    for key in ("beacon_block_root","source_root","target_root","genesis_validators_root",
                "previous_version","current_version"):
        rows.append((dict(k,**{key:"00"}),dict(status="error",error="invalid_width"),"invalid_width"))
    for key in ("slot","committee_index","source_epoch","target_epoch","activation_epoch"):
        rows.append((dict(k,**{key:2**64}),dict(status="error",error="out_of_range"),"out_of_range"))
    rows += [(dict(k,beacon_block_root="gg"*32),dict(status="error",error="invalid_hex"),"bad_hex"),
             (dict(k,extra=0),dict(status="error",error="parse_error"),"extra"),
             ({a:b for a,b in k.items() if a!="target_epoch"},dict(status="error",error="parse_error"),"missing")]
    return rows

def compare(actual,expect):
    if actual!=expect:
        raise AssertionError(f"actual {actual!r} != expected {expect!r}")

def main():
    rows=corpus()
    payload="".join(json.dumps(q,separators=(",",":"))+"\n" for q,_,_ in rows)
    run=subprocess.run([sys.argv[1]],input=payload,text=True,capture_output=True,timeout=180,check=True)
    lines=run.stdout.splitlines()
    if len(lines)!=len(rows):
        raise AssertionError("wrong response count")
    for line,(q,e,label) in zip(lines,rows):
        try:
            compare(json.loads(line),e)
        except AssertionError as err:
            raise AssertionError(f"{label}: {q}: {err}") from err
    good=rows[0][1]
    for key in ("bytes","object_root","domain","signing_root"):
        try:
            compare(dict(good,**{key:"00"}),good)
        except AssertionError:
            pass
        else:
            raise AssertionError("missed mutation "+key)
    # Domain derived from slot, rather than target, must not pass the KAT.
    wrong=expected(dict(rows[0][0],target_epoch=0))["domain"]
    assert wrong!=good["domain"]
    try:
        compare(dict(good,domain=wrong),good)
    except AssertionError:
        pass
    else:
        raise AssertionError("missed wrong-domain mutation")
    print(json.dumps(dict(total=len(rows),passed=len(rows),failed=0,groups=dict(Counter(x[2] for x in rows)),
                          mutations_detected=5,not_run=0),sort_keys=True))

if __name__=="__main__":
    main()
