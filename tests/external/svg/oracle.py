#!/usr/bin/env python3
"""Full-image candidate comparison with separately captured browser PNGs."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import shutil
import zlib
import suite


def png(path):
    data=Path(path).read_bytes()
    if data[:8]!=b'\x89PNG\r\n\x1a\n': raise ValueError('not PNG')
    offset=8; compressed=bytearray(); header=None; ended=False
    while offset<len(data):
        if offset+12>len(data): raise ValueError('truncated PNG chunk')
        size=struct.unpack('>I',data[offset:offset+4])[0]; kind=data[offset+4:offset+8]
        end=offset+12+size
        if end>len(data): raise ValueError('truncated PNG payload')
        payload=data[offset+8:offset+8+size]
        if zlib.crc32(kind+payload)&0xffffffff!=struct.unpack('>I',data[offset+8+size:end])[0]: raise ValueError('PNG CRC mismatch')
        if kind==b'IHDR': header=struct.unpack('>IIBBBBB',payload)
        elif kind==b'IDAT': compressed.extend(payload)
        elif kind==b'IEND': ended=True; break
        elif kind[0]&32==0 and kind not in (b'PLTE',): raise ValueError('unsupported critical PNG chunk')
        offset=end
    if not header or not ended: raise ValueError('missing PNG header/end')
    w,h,depth,color,compression,filter_method,interlace=header
    if not (1<=w<=4096 and 1<=h<=4096 and depth==8 and color in (2,6) and compression==filter_method==interlace==0): raise ValueError('unsupported PNG format')
    channels=3 if color==2 else 4; stride=w*channels; expected=(stride+1)*h
    decoder=zlib.decompressobj(); raw=decoder.decompress(compressed,expected+1)
    if len(raw)!=expected or not decoder.eof or decoder.unused_data: raise ValueError('invalid/bounded PNG raster')
    previous=bytearray(stride); rgb=bytearray()
    for y in range(h):
        start=y*(stride+1); method=raw[start]; row=bytearray(raw[start+1:start+1+stride])
        if method>4: raise ValueError('invalid PNG filter')
        if method==1:
            for x in range(channels,stride): row[x]=(row[x]+row[x-channels])&255
        elif method==2:
            row=bytearray((value+previous[x])&255 for x,value in enumerate(row))
        elif method in (3,4):
            for x in range(stride):
                a=row[x-channels] if x>=channels else 0; b=previous[x]; c=previous[x-channels] if x>=channels else 0
                if method==3: predictor=(a+b)//2
                else:
                    p=a+b-c;pa,pb,pc=abs(p-a),abs(p-b),abs(p-c)
                    predictor=a if pa<=pb and pa<=pc else b if pb<=pc else c
                row[x]=(row[x]+predictor)&255
        if channels==3: rgb.extend(row)
        else:
            for x in range(0,stride,channels):
                alpha=row[x+3]
                rgb.extend((row[x+i]*alpha+255*(255-alpha)+127)//255 for i in range(3))
        previous=row
    return w,h,bytes(rgb)


def write_ppm(path,image):
    w,h,rgb=image;Path(path).write_bytes(f'P6\n{w} {h}\n255\n'.encode()+rgb)


def metrics(actual,expected,fuzzy):
    aw,ah,a=actual;ew,eh,e=expected
    if (aw,ah)!=(800,600) or (aw,ah)!=(ew,eh): raise ValueError('expected full800x600 images')
    maximum=different=0;diff=bytearray()
    if a==e:
        mr,pr=fuzzy
        return mr[0]<=0<=mr[1] and pr[0]<=0<=pr[1],{'maxChannelDifference':0,'differentPixels':0},(aw,ah,bytes(len(a)))
    for i in range(0,len(a),3):
        d=[abs(a[i+j]-e[i+j]) for j in range(3)];maximum=max(maximum,*d);different+=any(d);diff.extend(d)
    mr,pr=fuzzy
    return mr[0]<=maximum<=mr[1] and pr[0]<=different<=pr[1],{'maxChannelDifference':maximum,'differentPixels':different},(aw,ah,bytes(diff))


def compare_oracle(directory,command=None,output=None,candidate_directory=None):
    root=Path(directory); manifest,errors=suite.fixtures()
    if errors: raise ValueError('; '.join(errors))
    report=json.loads((root/'oracle.json').read_text())
    if report['revision']!=manifest['revision'] or [(x['test'],x['reference']) for x in report['cases']]!=[(x['test'],x['reference']) for x in manifest['cases']]: raise ValueError('oracle inventory/pin mismatch')
    if report.get('viewport')!={'width':800,'height':600,'deviceScaleFactor':1} or report.get('scripts') is not False or report.get('externalFetch') is not False:
        raise ValueError('oracle capture conditions differ')
    capture=None
    if candidate_directory:
        capture=json.loads((Path(candidate_directory)/'candidate.json').read_text())
        if capture['revision']!=manifest['revision'] or [(x['test'],x['reference']) for x in capture['cases']]!=[(x['test'],x['reference']) for x in manifest['cases']]:
            raise ValueError('candidate inventory/pin mismatch')
        if capture.get('backend')!='browser-raw-webgpu' or capture.get('viewport')!={'width':800,'height':600,'deviceScaleFactor':1}:
            raise ValueError('candidate backend/viewport differs')
        if any(not report.get(key) or capture.get(key)!=report[key] for key in ('browserVersion','browserExecutableSha256')):
            raise ValueError('candidate and oracle must use the same browser version and executable bytes')
    out=Path(output or root/'comparison');out.mkdir(parents=True,exist_ok=True)
    results=[];decoded={}
    for i,(case,oracle) in enumerate(zip(manifest['cases'],report['cases'])):
        row={'test':case['test'],'reference':case['reference'],'status':'unavailable'}
        try:
            if case['requiredRuntime'] or oracle['status']!='captured': raise ValueError(oracle.get('reason','required runtime unavailable'))
            images={}
            for role in ('test','reference'):
                image=oracle['images'][role];path=root/image['file']
                if Path(image['file']).name!=image['file']: raise ValueError('unsafe image filename')
                if hashlib.sha256(path.read_bytes()).hexdigest()!=image['sha256']: raise ValueError('oracle image hash mismatch')
                source=suite.ROOT/'upstream'/case[role]
                if hashlib.sha256(source.read_bytes()).hexdigest()!=image['sourceSha256']: raise ValueError('oracle source hash mismatch')
                if image['sha256'] not in decoded: decoded[image['sha256']]=png(path)
                images[role]=decoded[image['sha256']]
            equal,detail,_=metrics(images['test'],images['reference'],case['fuzzy'])
            row['independentRelation']={'matches':equal,**detail}
            if not equal: raise ValueError('independent browser disagrees with original reftest relation')
            actual=out/f'{i:02}-actual.ppm'
            if capture:
                candidate=capture['cases'][i]
                if candidate.get('sourceSha256')!=hashlib.sha256((suite.ROOT/'upstream'/case['test']).read_bytes()).hexdigest(): raise ValueError('candidate source hash mismatch')
                state=candidate['status'];detail=candidate.get('detail',candidate.get('reason',''))
                if state not in ('accepted','unsupported','rejected','unavailable'): raise ValueError('invalid candidate state')
                if state=='accepted':
                    image=candidate['image']
                    if Path(image['file']).name!=image['file']: raise ValueError('unsafe candidate filename')
                    actual=Path(candidate_directory)/image['file']
                    if hashlib.sha256(actual.read_bytes()).hexdigest()!=image['sha256']: raise ValueError('candidate image hash mismatch')
            elif command:
                state,detail=suite.invoke(command,suite.ROOT/'upstream'/case['test'],actual,False,60)
            else: raise ValueError('candidate GPU command/capture not supplied')
            row['candidateLog']=detail
            if state!='accepted': row.update(status=state,detail=detail)
            else:
                equal,detail,diff=metrics(suite.ppm(actual),images['reference'],case['fuzzy'])
                write_ppm(out/f'{i:02}-difference.ppm',diff)
                _,against_test,_=metrics(suite.ppm(actual),images['test'],case['fuzzy'])
                row.update(status='match' if equal else 'mismatch',detail=detail,againstIndependentTest=against_test)
                if capture: row.update(viewportPolicy=candidate.get('viewportPolicy'),svgViewport=candidate.get('svgViewport'))
                if capture and capture.get('controlsRequested'):
                    row['controls']={}
                    for name in ('unchangedReplay','gpuFlatMagenta','unsampledReadbackPixel'):
                        control=candidate.get('controls',{}).get(name,{})
                        result={'status':'unavailable','expected':'identical' if name=='unchangedReplay' else 'different'}
                        try:
                            image=control['image'];path=Path(candidate_directory)/image['file']
                            if Path(image['file']).name!=image['file']: raise ValueError('unsafe control filename')
                            if hashlib.sha256(path.read_bytes()).hexdigest()!=image['sha256']: raise ValueError('control image hash mismatch')
                            pixels=suite.ppm(path)
                            same,vs_candidate,_=metrics(pixels,suite.ppm(actual),[[0,0],[0,0]])
                            oracle_equal,vs_oracle,diff=metrics(pixels,images['reference'],case['fuzzy'])
                            result.update(againstCandidate=vs_candidate,againstIndependentReference=vs_oracle,
                                          oracleMatches=oracle_equal,metadata={k:v for k,v in control.items() if k!='image'})
                            write_ppm(out/f'{i:02}-control-{name}-difference.ppm',diff)
                            if not equal: result['reason']='Baseline does not match independent reference; oracle sensitivity is not established'
                            else: result['status']='pass' if (same and oracle_equal if name=='unchangedReplay' else not same and not oracle_equal) else 'fail'
                        except (ValueError,OSError,KeyError,TypeError) as error: result['reason']=control.get('error',str(error))
                        row['controls'][name]=result
        except (ValueError,OSError,KeyError,TypeError) as error: row['reason']=str(error)
        results.append(row)
    candidate=None
    if command:
        executable=shutil.which(command[0]) or command[0]
        digest=hashlib.sha256()
        with open(executable,'rb') as stream:
            for block in iter(lambda:stream.read(1048576),b''): digest.update(block)
        executable_hash=digest.hexdigest()
        candidate={'command':command,'executableSha256':executable_hash}
    captured_metadata={k:capture.get(k) for k in ('backend','host','browserVersion','browserExecutableSha256','typescript','viewport','viewportPolicy','candidateSources','sourceSnapshot','runtimeAssets','harnessSha256','harnessSources','controlsRequested','adapters')} if capture else None
    result={'candidateCapture':captured_metadata,'candidate':candidate,'oracleCapture':{k:report.get(k) for k in ('browserVersion','browserExecutableSha256','host','fonts','viewport','scripts','externalFetch','scope','capturedAt','harnessSha256','node')},'revision':manifest['revision'],'mode':'independent-browser-full-image','oracleBrowser':report.get('browserVersion'),'total':len(results),'counts':{s:sum(x['status']==s for x in results) for s in suite.STATES},'results':results}
    result['comparatorSha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if capture and capture.get('controlsRequested'):
        result['controls']={'scope':'Sensitivity diagnostics only; no additional WPT cases or passes',
          'counts':{name:{state:sum(row.get('controls',{}).get(name,{}).get('status','unavailable')==state for row in results) for state in ('pass','fail','unavailable')} for name in ('unchangedReplay','gpuFlatMagenta','unsampledReadbackPixel')}}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--oracle',required=True);parser.add_argument('--engine');parser.add_argument('--candidate');parser.add_argument('--output');args=parser.parse_args()
    if args.engine and args.candidate: parser.error('choose --engine or --candidate')
    result=compare_oracle(args.oracle,[str(Path(args.engine).resolve())] if args.engine else None,args.output,args.candidate)
    print(json.dumps({k:result[k] for k in ('total','counts','controls') if k in result}))
    raise SystemExit(0 if result['counts']['match']==result['total'] else 1)
