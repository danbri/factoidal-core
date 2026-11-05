#!/usr/bin/env python3
"""Bounded fresh native Lean CPU images against hash-checked cached WPT oracles.

No browser is launched. Cached independent browser images are expectations only.
All 279 HTML relations remain visible, including unsupported and unavailable rows.
"""
import argparse, collections, hashlib, json, os, subprocess, sys, time
from pathlib import Path
import numpy as np
from PIL import Image

p=argparse.ArgumentParser()
for name in ['corpus','oracle','native','output']: p.add_argument('--'+name,required=True)
p.add_argument('--timeout',type=float,default=5)
a=p.parse_args(); corpus=Path(a.corpus).resolve(); oracle=Path(a.oracle).resolve(); out=Path(a.output).resolve(); out.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
source=json.loads((corpus/'source.json').read_text()); inventory=json.loads((corpus/'inventory.json').read_text())
capture=json.loads((oracle/'capture.json').read_text()); files={f['path']:f for f in source['files']}
assert capture['sourceManifestSha256']==sha((corpus/'source.json').read_bytes())
assert capture['inventorySha256']==sha((corpus/'inventory.json').read_bytes())
assert capture['revision']==source['revision']
assert len(capture['cases'])==len(inventory['cases']), 'Truncated oracle inventory'
def fixture(path):
 b=(corpus/'upstream'/path).read_bytes(); assert sha(b)==files[path]['sha256']; return b
def image(entry):
 assert Path(entry['file']).name==entry['file']; b=(oracle/entry['file']).read_bytes(); assert sha(b)==entry['sha256']
 with Image.open(oracle/entry['file']) as im:
  assert im.size==(800,600); rgba=np.array(im.convert('RGBA'),dtype=np.uint16)
 alpha=rgba[:,:,3:4]; return ((rgba[:,:,:3]*alpha+255*(255-alpha)+127)//255).astype(np.uint8)
def metrics(actual,expected,fuzzy):
 diff=np.abs(actual.astype(np.int16)-expected.astype(np.int16)); maximum=int(diff.max()); different=int(np.count_nonzero(np.any(diff,axis=2)))
 return fuzzy[0][0]<=maximum<=fuzzy[0][1] and fuzzy[1][0]<=different<=fuzzy[1][1],{'maxChannelDifference':maximum,'differentPixels':different}
native=Path(a.native).resolve(); native_sha=sha(native.read_bytes())
report={'format':'factoidal-wpt-native-cpu-v1','startedAt':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'revision':source['revision'],
 'scope':'All HTML relations in pinned SVG subtree, fresh native Lean CPU pixels, cached independent original-browser oracles; default bitmap-font profile, original source, 800x600 viewport.',
 'native':{'path':str(native),'sha256':native_sha},'runnerSha256':sha(Path(__file__).read_bytes()),
 'oracle':{'path':str(oracle),'captureSha256':sha((oracle/'capture.json').read_bytes()),'runtime':capture.get('runtime'),'browser':capture.get('browser')},'cases':[]}
for index,(original,old) in enumerate(zip(inventory['cases'],capture['cases'])):
 if not original['test'].endswith('.html'): continue
 for key in ['test','reference','relation','fuzzy']: assert original[key]==old[key]
 row={**original,'status':'UNAVAILABLE'};report['cases'].append(row)
 try:
  fixture(original['test']); row['sourceSha256']=files[original['test']]['sha256']
  if original['kind']!='reftest-static': row['reason']='Dynamic reference requires browser event-loop integration';continue
  cmd=[str(native),str(corpus/'upstream'/original['test']),'800','600']
  result=subprocess.run(cmd,capture_output=True,timeout=a.timeout,env={'PATH':'/nonexistent'})
  if result.returncode:row.update(status='CRASH',reason=result.stderr.decode(errors='replace')[:1000]);continue
  artifact=json.loads(result.stdout)
  if artifact.get('error'):row.update(status='UNSUPPORTED',reason=artifact['error']);continue
  row['artifactSha256']=sha(result.stdout);row['primitiveCount']=artifact.get('primitiveCount')
  independent=old.get('oracle',{})
  if independent.get('test',{}).get('status')!='captured' or independent.get('reference',{}).get('status')!='captured':row['reason']='No qualified cached original test/reference image';continue
  test=image(independent['test']['image']);reference=image(independent['reference']['image'])
  equal,detail=metrics(test,reference,original['fuzzy'])
  if equal!=(original['relation']=='match'):row['reason']='Cached original browser does not satisfy upstream relation';continue
  row['independentRelation']=detail
  result=subprocess.run(cmd+['--pixels'],capture_output=True,timeout=a.timeout,env={'PATH':'/nonexistent'})
  if result.returncode:row.update(status='CRASH',reason=result.stderr.decode(errors='replace')[:1000]);continue
  pixels=json.loads(result.stdout)
  if pixels.get('error'):row.update(status='UNSUPPORTED',reason=pixels['error']);continue
  assert pixels['width']==800 and pixels['height']==600 and len(pixels['pixels'])==800*600*3
  assert all(type(x) is int and 0<=x<=255 for x in pixels['pixels']), 'Invalid RGB output'
  actual=np.array(pixels['pixels'],dtype=np.uint8).reshape((600,800,3))
  equal,detail=metrics(actual,reference,original['fuzzy']);same_test,test_detail=metrics(actual,test,[[0,0],[0,0]])
  holds=equal==(original['relation']=='match')
  row.update(status='PASS' if holds and (original['relation']=='match' or same_test) else 'NEGATIVE_ONLY' if holds else 'FAIL',againstReference=detail,againstIndependentTest=test_detail)
  name=f'{index:04}-native.png';Image.fromarray(actual).save(out/name,compress_level=9)
  row['image']={'file':name,'sha256':sha((out/name).read_bytes())}
  row['expectedImage']=independent['reference']['image']
  if same_test:
   changed=actual.copy();changed[-1,-1,0]=255-int(changed[-1,-1,0])
   detected=not metrics(changed,test,[[0,0],[0,0]])[0];assert detected
   row['onePixelCorruptionDetected']=detected
 except subprocess.TimeoutExpired:row.update(status='TIMEOUT',reason=f'Native operation exceeded {a.timeout}s')
 except Exception as e:row.update(status='HARNESS_ERROR',reason=str(e))
 if len(report['cases'])%25==0:print(json.dumps({'completed':len(report['cases'])}),flush=True)
 # Compact report is checkpointed; source and runtime bundles are not duplicated.
 (out/'native-reftests.partial.json').write_text(json.dumps(report,indent=2))
assert sha(native.read_bytes())==native_sha
report['finishedAt']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());report['counts']=dict(collections.Counter(x['status'] for x in report['cases']))
(out/'native-reftests.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'total':len(report['cases']),'counts':report['counts'],'report':str(out/'native-reftests.json')}),flush=True)
sys.exit(0 if all(x['status']=='PASS' for x in report['cases']) else 1)
