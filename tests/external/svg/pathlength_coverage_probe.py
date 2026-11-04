"""Exact area diagnostic for the admitted pathlength-001 scene, not an SVG parser.

Uses rational union area for axis-aligned opaque black dash rectangles.
No browser-matching tolerance or product sampling rule is changed.
"""
import argparse
import hashlib
import json, math
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import oracle
import suite
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--artifact', type=Path, required=True)
parser.add_argument('--browser-reference', type=Path, required=True)
parser.add_argument('--candidate', action='append', default=[], help='label=PPM path')
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
artifact = json.loads(args.artifact.read_text())
rows=[artifact['data'][i:i+4] for i in range(0,len(artifact['data']),4)]
# This independent fixture-specific area oracle admits only its two black,
# untransformed rectangle primitives with axis-aligned butt dash pieces.
assert artifact['primitiveCount']==2 and rows[:2]==[[5/3,5/3,0,0],[0,0,800,600]]
base=2; boxes=[]
for _ in range(2):
 assert rows[base+1]==[1,0,0,0]
 assert rows[base+2]==[0,0,0,0] and rows[base+3]==[0,0,0,1]
 width,opacity,count,active=rows[base+4]
 assert width==5 and opacity==1 and active==1
 for i in range(count):
  b=base+5+i*5
  assert rows[b+1]==[4,0,0,0] and rows[b+4][0]==5
  x1,y1,x2,y2=map(F,rows[b]);h=F(5,2)
  assert x1==x2 or y1==y2
  if x1==x2:box=(x1-h,min(y1,y2),x1+h,max(y1,y2))
  else:box=(min(x1,x2),y1-h,max(x1,x2),y1+h)
  boxes.append(tuple(v*F(5,3) for v in box))
 base+=5+5*count
assert base==len(rows)
fragments=defaultdict(list)
for x0,y0,x1,y1 in boxes:
 for y in range(max(0,math.floor(y0)),min(600,math.ceil(y1))):
  for x in range(max(0,math.floor(x0)),min(800,math.ceil(x1))):
   fragments[x,y].append((max(x0,x),max(y0,y),min(x1,x+1),min(y1,y+1)))
rgb=bytearray([255])*(800*600*3)
for (x,y),parts in fragments.items():
 cuts=sorted(set(v for p in parts for v in (p[0],p[2])))
 area=F(0)
 for a,b in zip(cuts,cuts[1:]):
  ys=sorted((q[1],q[3]) for q in parts if q[0]<=a and b<=q[2])
  total=F(0);end=None
  for lo,hi in ys:
   if end is None or lo>end:total+=hi-lo;end=hi
   elif hi>end:total+=hi-end;end=hi
  area+=(b-a)*total
 assert 0<=area<=1
 value=round(255*(1-area));offset=(y*800+x)*3;rgb[offset:offset+3]=bytes([value])*3
image = (800,600,bytes(rgb))
args.output.mkdir(parents=True,exist_ok=True)
oracle.write_ppm(args.output/'exact-area.ppm', image)
reference = oracle.png(args.browser_reference)
result=[]
paths = [item.split('=',1) for item in args.candidate]
for name,path in [*paths, ('browser',str(args.browser_reference))]:
    path=Path(path)
    actual=oracle.png(path) if name=='browser' else suite.ppm(path)
    row={'variant':name, 'imageSha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    for label,expected in [('exactArea',image),('browser',reference)]:
        _,detail,_=oracle.metrics(actual,expected,[[0,0],[0,0]])
        detail['sumAbsoluteChannels']=sum(abs(a-b) for a,b in zip(actual[2],expected[2]))
        row[label]=detail
    result.append(row)
report={'scope':'exact area of decoded scene; not independent SVG interpretation',
        'artifactSha256':hashlib.sha256(args.artifact.read_bytes()).hexdigest(),
        'cases':result}
(args.output/'coverage.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
