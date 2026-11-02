#!/usr/bin/env python3
"""Whole-image scoring of original WPT relations, with separate negative controls."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import platform
import sys
import numpy as np
from PIL import Image, __version__ as pillow_version
import corpus

STATES=('match','negative-only','mismatch','unsupported','rejected','unavailable')
def sha(data):return hashlib.sha256(data).hexdigest()
def image(root,entry):
    if Path(entry['file']).name!=entry['file']:raise ValueError('Unsafe image filename')
    path=root/entry['file'];data=path.read_bytes()
    if sha(data)!=entry['sha256']:raise ValueError('Image identity differs')
    with Image.open(path) as im:
        if im.format!='PNG' or im.size!=(800,600):raise ValueError('Expected original full 800x600 PNG')
        im.verify()
    with Image.open(path) as im:rgba=np.array(im.convert('RGBA'),dtype=np.uint16)
    alpha=rgba[:,:,3:4]
    return ((rgba[:,:,:3]*alpha+255*(255-alpha)+127)//255).astype(np.uint8)
def metrics(actual,expected,fuzzy):
    if actual.shape!=(600,800,3) or expected.shape!=actual.shape:raise ValueError('Full image dimensions differ')
    diff=np.abs(actual.astype(np.int16)-expected.astype(np.int16)).astype(np.uint8)
    maximum=int(diff.max());different=int(np.count_nonzero(np.any(diff,axis=2)))
    return fuzzy[0][0]<=maximum<=fuzzy[0][1] and fuzzy[1][0]<=different<=fuzzy[1][1],{'maxChannelDifference':maximum,'differentPixels':different},diff
def save_diff(path,array):Image.fromarray(array).save(path,format='PNG',compress_level=9)
def relation_state(relation,equal_to_reference,exact_test):
    holds=equal_to_reference if relation=='match' else not equal_to_reference
    return ('match' if holds and (relation=='match' or exact_test) else 'negative-only' if holds else 'mismatch'),holds
def score(directory):
    corpus.check();root=Path(directory);capture=json.loads((root/'capture.json').read_text());inventory=json.loads((corpus.ROOT/'inventory.json').read_text())
    if capture['revision']!=corpus.PIN or capture['sourceManifestSha256']!=sha((corpus.ROOT/'source.json').read_bytes()) or capture['inventorySha256']!=sha((corpus.ROOT/'inventory.json').read_bytes()):raise ValueError('Capture source/pin/metadata identity differs')
    if len(capture['cases'])!=601:raise ValueError('Capture denominator is not601')
    cache={};rows=[]
    def raster(entry):
        key=entry['sha256']
        if key not in cache:cache[key]=image(root,entry)
        return cache[key]
    for original,candidate in zip(inventory['cases'],capture['cases']):
        for key in ('test','reference','referenceHref','relation','kind','fuzzy','testRequirements','referenceRequirements','baseline38'):
            if candidate[key]!=original[key]:raise ValueError('Candidate altered original case '+key+': '+original['test'])
        row={**original,'status':'unavailable','candidateStatus':candidate['status']}
        try:
            if candidate.get('sourceSha256')!=sha((corpus.ROOT/'upstream'/original['test']).read_bytes()):raise ValueError('Original candidate input identity differs')
            oracle=candidate['oracle']
            for role in ('test','reference'):
                if oracle[role]['status']!='captured':raise ValueError(oracle[role].get('reason','Original browser image unavailable'))
                target={'path':original['test'],'query':'','fragment':''} if role=='test' else original['reference']
                expected=sha((corpus.ROOT/'upstream'/target['path']).read_bytes()) if target.get('path') else None
                if oracle[role]['target']!=target or oracle[role]['sourceSha256']!=expected:raise ValueError('Independent browser document identity differs')
            if original['fuzzy'] is None:raise ValueError('Original fuzzy reference context unresolved')
            test=raster(oracle['test']['image']);reference=raster(oracle['reference']['image'])
            equal,detail,_=metrics(test,reference,original['fuzzy']);relation_holds=equal if original['relation']=='match' else not equal
            row['independentRelation']={'holds':relation_holds,**detail}
            if not relation_holds:raise ValueError('Independent Chrome disagrees with original upstream relation')
            if candidate['status']!='accepted':row.update(status=candidate['status'],detail=candidate.get('detail',candidate.get('reason','')));rows.append(row);continue
            artifact=candidate['artifact']
            if Path(artifact['file']).name!=artifact['file']:raise ValueError('Unsafe artifact filename')
            payload=gzip.decompress((root/artifact['file']).read_bytes())
            if sha(payload)!=artifact['sha256']:raise ValueError('Generated artifact identity differs')
            a=json.loads(payload)
            if sha(a['wgsl'].encode())!=artifact['wgslSha256'] or candidate['submittedShaderSha256']!=artifact['wgslSha256']:raise ValueError('Submitted GPU shader differs from artifact')
            actual=raster(candidate['image']);equal,detail,diff=metrics(actual,reference,original['fuzzy'])
            exact_test,test_detail,_=metrics(actual,test,[[0,0],[0,0]])
            # A blank candidate can satisfy != accidentally. Keep that official
            # relation fact visible, but do not call it a meaningful image pass.
            state,holds=relation_state(original['relation'],equal,exact_test)
            row.update(status=state,officialCandidateRelationHolds=holds,againstIndependentTest={**test_detail,'exact':exact_test},detail=detail,
              viewportPolicy=candidate.get('viewportPolicy'),outputViewport={'width':candidate['width'],'height':candidate['height']},rootViewport=candidate.get('rootViewport'))
            if state in ('mismatch','negative-only'):
                name=f"{candidate['index']:04}-difference.png";save_diff(root/name,diff);row['differenceImage']=name
            if capture.get('controlsRequested'):
                row['controls']={}
                for name in ('unchangedReplay','gpuFlatMagenta','unsampledReadbackPixel'):
                    control=candidate.get('controls',{}).get(name,{});result={'status':'unavailable'}
                    try:
                        changed=raster(control['image']);same,detail,delta=metrics(changed,test,[[0,0],[0,0]])
                        official_equal,official_detail,_=metrics(changed,reference,original['fuzzy'])
                        result.update(againstIndependentTest=detail,officialRelationStillHolds=official_equal if original['relation']=='match' else not official_equal)
                        if not exact_test:result['reason']='Baseline differs from independent test image; exact sensitivity not established'
                        else:result['status']='pass' if (same if name=='unchangedReplay' else not same) else 'fail'
                        if name!='unchangedReplay':
                            file=f"{candidate['index']:04}-control-{name}-difference.png";save_diff(root/file,delta);result['differenceImage']=file
                    except (KeyError,ValueError,OSError) as error:result['reason']=control.get('unavailable',str(error))
                    row['controls'][name]=result
        except (KeyError,ValueError,OSError) as error:row['reason']=str(error)
        rows.append(row)
    def counts(selected):return {state:sum(row['status']==state for row in selected) for state in STATES}
    control_counts={name:{state:sum(row.get('controls',{}).get(name,{}).get('status','unavailable')==state for row in rows) for state in ('pass','fail','unavailable')} for name in ('unchangedReplay','gpuFlatMagenta','unsampledReadbackPixel')}
    result={'scope':capture['scope'],'revision':corpus.PIN,'total':len(rows),'counts':counts(rows),
      'selectedDiagnostic':{'total':len(capture['selection']),'counts':counts([row for row in rows if row['test'] in capture['selection']])} if capture.get('selection') else None,
      'static':{'total':sum(row['kind']=='reftest-static' for row in rows),'counts':counts([row for row in rows if row['kind']=='reftest-static'])},
      'old38OverlapDiagnostic':{'total':sum(row['baseline38'] for row in rows),'counts':counts([row for row in rows if row['baseline38']])},
      'positiveMatches':sum(row['status']=='match' and row['relation']=='match' for row in rows),
      'negativeRelations':{'total':sum(row['relation']=='mismatch' for row in rows),'qualifiedImageMatches':sum(row['status']=='match' and row['relation']=='mismatch' for row in rows),'relationOnly':sum(row['status']=='negative-only' for row in rows)},
      'controls':{'scope':'Exact independent-test sensitivity, separate from upstream relation/denominator; negative relations alone cannot establish sensitivity','counts':control_counts},
      'runtime':{'python':sys.version,'executable':sys.executable,'pillow':pillow_version,'numpy':np.__version__,'platform':platform.platform()},
      'comparatorSha256':sha(Path(__file__).read_bytes()),'captureSha256':sha((root/'capture.json').read_bytes()),'results':rows}
    (root/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    problems=any(value['fail'] for value in control_counts.values())
    code=2 if capture.get('fatal') or problems else 0 if result['counts']['match']==601 and capture['complete'] else 1
    (root/'comparison.exit').write_text(str(code)+'\n')
    print(json.dumps({k:result[k] for k in ('total','counts','static','negativeRelations','controls')}))
    return code

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');a=p.parse_args();raise SystemExit(score(a.directory))
