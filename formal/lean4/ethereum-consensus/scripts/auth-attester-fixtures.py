"""Independent SSZ oracle with distinct public test scalars 1 through 4."""
import json
import random
import runpy
from pathlib import Path

oracle = runpy.run_path(str(Path(__file__).with_name("check-validator-registry.py")))
P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
G = (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
     0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
def add(a,b):
    if a is None: return b
    x,y=a; u,v=b
    if x==u and (y+v)%P==0: return None
    m=((3*x*x)*pow(2*y,-1,P) if x==u else (v-y)*pow(u-x,-1,P))%P
    X=(m*m-x-u)%P
    return X,(m*(x-X)-y)%P
keys=[]
q=None
for i in range(4):
    q=add(q,G)
    x,y=q
    assert (y*y-x*x*x-4)%P==0
    keys.append((x | ((5 if y>(P-1)//2 else 4)<<381)).to_bytes(48,"big"))
assert len(set(keys))==4
class FixtureRandom(random.Random):
    def __init__(self,*a):
        super().__init__(*a)
        self.key_index=0
    def randbytes(self,n):
        raw=super().randbytes(n)
        if n!=48: return raw
        result=keys[self.key_index%4]
        self.key_index+=1
        return result
# Existing independent SSZ oracle generates exact branches and all noncommon mutations.
original=random.Random
try:
    random.Random=FixtureRandom
    rows=oracle["allsigner_cases"]()
finally:
    random.Random=original
cases=[]
for i in (0,3):
    part=rows[i*33:(i+1)*33]
    line,expected=part[0]
    label,a,b,lk,rk,eligible=expected.split()
    assert label=="prepared_not_authenticated"
    assert lk==",".join(k.hex() for k in keys[:3])
    assert rk==",".join(k.hex() for k in keys[1:])
    cases.append({"line":line.removeprefix("allsigners "),"evidence":[a,b,lk,rk,eligible],"rejections":[[l.removeprefix("allsigners "),e] for l,e in part[1:]]})
print(json.dumps(cases))
