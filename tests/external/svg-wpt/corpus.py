#!/usr/bin/env python3
"""Inventory original WPT SVG files; metadata is not a rendering result."""
import argparse
import base64
from collections import Counter
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import unquote, urljoin, urlsplit

ROOT=Path(__file__).resolve().parent
BASELINE=ROOT.parent/'svg/manifest.json'
PIN='70dae60789ef6220d9b4e60c92c5b2107b4e2b93'
TREE='e719d1b7247635648362bbbe8611e713db30f3f0'
DOCUMENTS={'.svg','.html','.htm','.xhtml','.xht','.xml'}
TEXT=DOCUMENTS|{'.css','.js','.py','.md','.headers'}

def sha(data): return hashlib.sha256(data).hexdigest()
def blob(data): return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def tree_identity(entries):
    root={}
    for entry in entries:
        if entry['type']!='blob':continue
        node=root;parts=entry['path'].split('/')
        for name in parts[:-1]:node=node.setdefault(name,{})
        node[parts[-1]]=(entry['mode'],entry['sha'])
    def digest(node):
        payload=bytearray()
        for name,value in sorted(node.items(),key=lambda item:(item[0]+('/' if isinstance(item[1],dict) else '')).encode()):
            mode,oid=('40000',digest(value)) if isinstance(value,dict) else value
            payload.extend(mode.encode()+b' '+name.encode()+b'\0'+bytes.fromhex(oid))
        return hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()
    return digest(root)
def resolve(source,href,base=None):
    if href=='about:blank':return {'special':'about:blank','path':None,'query':'','fragment':''}
    try:parsed=urlsplit(urljoin(urljoin('http://wpt.invalid/'+source,base or ''),href))
    except ValueError:return None  # Deliberately invalid URL tests stay inventoried.
    if parsed.scheme not in ('http','https') or parsed.netloc!='wpt.invalid': return None
    path=unquote(parsed.path.lstrip('/'))
    if not path or any(p in ('.','..') for p in path.split('/')) or '\0' in path: return None
    return {'path':path,'query':parsed.query,'fragment':parsed.fragment}

class Metadata(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links=[];self.resources=[];self.scripts=[];self.events=[];self.tags=Counter()
        self.meta=[];self.base=None;self.wait=False;self.anim=False;self.rootDimensions=None;self.xmlBase=False
    def handle_starttag(self,tag,attrs):
        a=dict(attrs);local=tag.rsplit(':',1)[-1];self.tags[local]+=1
        if self.rootDimensions is None and local=='svg': self.rootDimensions={k:a.get(k) for k in ('width','height','viewbox')}
        if local=='base' and a.get('href') and self.base is None:
            try:
                parsed=urlsplit(urljoin('http://wpt.invalid/',a['href']))
                if parsed.scheme not in ('javascript','data'):self.base=a['href']
            except ValueError:pass
        self.xmlBase|='xml:base' in a
        if local=='meta': self.meta.append(a)
        if local=='link':
            rel=(a.get('rel') or '').lower().split()
            for relation in ('match','mismatch'):
                if relation in rel and a.get('href'): self.links.append({'relation':relation,'href':a['href']})
            if any(r in rel for r in ('stylesheet','preload','modulepreload')) and a.get('href'):self.resources.append(a['href'])
        if local=='script':self.scripts.append(a.get('src') or a.get('href') or a.get('xlink:href') or '(inline)')
        if local in ('script','image','img','iframe','object','embed','use','textpath','mpath','feimage','source','audio','video','font-face-uri'):
            for key in ('src','href','xlink:href','data','poster'):
                if a.get(key):self.resources.append(a[key])
        self.events.extend(k for k,v in attrs if k.startswith('on'))
        self.wait|='reftest-wait' in (a.get('class') or '').split()
        self.anim|=local in ('animate','animatetransform','animatemotion','animatecolor','set','discard')
    def handle_startendtag(self,tag,attrs):self.handle_starttag(tag,attrs)

def inspect(path,data):
    text=data.decode('utf-8-sig',errors='replace');p=Metadata();p.feed(text)
    requirements=[]
    if p.scripts or p.events: requirements.append('javascript')
    if p.anim or re.search(r'@keyframes\b|\banimation(?:-name)?\s*:',text,re.I):requirements.append('animation')
    if p.wait:requirements.append('reftest-wait')
    if '.sub.' in path or re.search(r'\{\{(?:host|hosts|ports|domains|location|GET|header)',text):requirements.append('wpt-server-template')
    if re.search(r'\bAhem\b',text,re.I):requirements.append('font-Ahem')
    if re.search(r'@font-face|\.(?:woff2?|ttf|otf)\b',text,re.I):requirements.append('font-resource')
    if re.search(r'\btestdriver\b|test_driver',text):requirements.append('testdriver')
    if path.endswith('.py'):requirements.append('wpt-server-handler')
    if '-print.' in path or '/print/' in path:requirements.append('print-context')
    if p.xmlBase:requirements.append('xml-base-context-unresolved')
    try:data.decode('utf-8-sig')
    except UnicodeDecodeError:requirements.append('non-utf8-source')
    refs=[{**link,'target':resolve(path,link['href'],p.base) if not p.xmlBase or link['href']=='about:blank' else None} for link in p.links]
    urls=list(p.resources)
    urls.extend(m[1] for m in re.findall(r'url\(\s*([\'"]?)([^\)\'"\s]+)\1\s*\)',text,re.I))
    urls.extend(re.findall(r'@import\s+[\'"]([^\'"]+)',text,re.I))
    if Path(path).suffix=='.js':
        urls.extend(re.findall(r'//\s*META:\s*script=(\S+)',text))
        urls.extend(re.findall(r'\b(?:from|import)\s*[\'"]([^\'"]+)[\'"]',text))
    resources=[];external=[]
    for href in urls:
        if href.startswith(('#','data:','blob:','javascript:')):continue
        target=resolve(path,href,p.base) if not p.xmlBase else None
        if target or p.xmlBase:resources.append({'href':href,'target':target})
        else:external.append(href)
    if external:requirements.append('external-origin-resource')
    flags=[m.get('content','') for m in p.meta if m.get('name','').lower()=='flags']
    harness=any('testharness' in script for script in p.scripts)
    manual='-manual.' in path or 'interact' in ' '.join(flags).split()
    dynamic=bool(set(requirements)&{'javascript','animation','reftest-wait','testdriver'})
    kind='reftest-dynamic' if refs and dynamic else 'reftest-static' if refs else 'script-test' if harness or path.endswith(('.window.js','.any.js')) else 'manual' if manual else 'support-or-unclassified'
    return {'path':path,'kind':kind,'references':refs,'requirements':requirements,
      'scripts':p.scripts,'eventAttributes':sorted(set(p.events)),'base':p.base,
      'flags':flags,'rootSVGDimensions':p.rootDimensions,'elements':dict(sorted(p.tags.items())),
      'variants':[m.get('content','') for m in p.meta if m.get('name','').lower()=='variant'],
      'fuzzyMetadata':[m.get('content','') for m in p.meta if m.get('name','').lower()=='fuzzy'],
      'resources':resources,'externalResources':sorted(set(external))}

def fuzzy(metadata,href,source,base=None):
    default=None;specific=None
    for content in metadata:
        value=content
        if ':' in content:
            ref,value=content.rsplit(':',1)
            if resolve(source,ref,base)!=resolve(source,href,base):continue
            specific=value
        else:default=value
    value=specific if specific is not None else default
    if value is None:return [[0,0],[0,0]]
    parts=value.split(';')
    if len(parts)!=2:raise ValueError('Unrecognized upstream fuzzy metadata: '+value)
    result=[]
    for part in parts:
        part=part.split('=',1)[-1].strip()
        if not re.fullmatch(r'\d+(?:-\d+)?',part):raise ValueError('Unrecognized upstream fuzzy bound: '+value)
        numbers=list(map(int,part.split('-')));result.append(numbers if len(numbers)==2 else numbers*2)
    return result

class GitProof:
    """Merkle witnesses bind fetched/absent dependency paths to the exact commit."""
    def __init__(self,snapshot=None,data=None):
        self.snapshot=snapshot;self.cache={}
        if data is None:
            commit=subprocess.check_output(['git','cat-file','commit',PIN],cwd=snapshot)
            self.data={'commit':base64.b64encode(commit).decode(),'trees':{}}
        else:self.data=data;commit=base64.b64decode(data['commit'])
        if hashlib.sha1(b'commit '+str(len(commit)).encode()+b'\0'+commit).hexdigest()!=PIN:raise ValueError('Wrong pinned commit witness')
        self.root=commit.splitlines()[0].split()[1].decode()
    def tree(self,oid):
        if oid in self.cache:return self.cache[oid]
        if oid not in self.data['trees']:
            if self.snapshot is None:raise ValueError('Missing dependency tree witness: '+oid)
            raw=subprocess.check_output(['git','cat-file','tree',oid],cwd=self.snapshot)
            self.data['trees'][oid]=base64.b64encode(raw).decode()
        raw=base64.b64decode(self.data['trees'][oid])
        if hashlib.sha1(b'tree '+str(len(raw)).encode()+b'\0'+raw).hexdigest()!=oid:raise ValueError('Invalid dependency tree witness')
        entries={};offset=0
        while offset<len(raw):
            space=raw.index(b' ',offset);zero=raw.index(b'\0',space)
            entries[raw[space+1:zero].decode()]={'mode':raw[offset:space].decode(),'sha':raw[zero+1:zero+21].hex()};offset=zero+21
        self.cache[oid]=entries;return entries
    def lookup(self,path):
        oid=self.root;parts=path.split('/')
        for index,part in enumerate(parts):
            entry=self.tree(oid).get(part)
            if entry is None:return None
            if index==len(parts)-1:return entry
            if entry['mode']!='40000':return None
            oid=entry['sha']
        return None

RULES='Original rel=match/mismatch; script tags/event attributes, SMIL/CSS animation, reftest-wait and testdriver flag dynamic; exact testharness script marks script-test; -manual filename/interactive flag marks manual. First valid HTML base is used. xml:base contexts remain explicit unavailable. Support/unclassified is explicit.'

def derive(entries,upstream,proof):
    present={e['path'] for e in entries};documents=[];metadata={}
    for entry in sorted(entries,key=lambda e:e['path']):
        if Path(entry['path']).suffix.lower() in TEXT:
            info=inspect(entry['path'],(upstream/entry['path']).read_bytes());metadata[entry['path']]=info
            if entry['scope']=='complete-svg-subtree' and Path(entry['path']).suffix.lower() in DOCUMENTS:documents.append(info)
    header_missing={}
    for name,info in metadata.items():
        candidates=[name+'.headers']+[str(parent/'__dir__.headers') for parent in Path(name).parents]
        info['responseHeaderFiles']=[]
        for path in candidates:
            item=proof.lookup(path)
            if item and item['mode']!='40000':
                info['responseHeaderFiles'].append(path)
                if path not in present:header_missing.setdefault(path,[]).append(name)
                elif 'wpt-server-template' in metadata.get(path,{}).get('requirements',[]):
                    if 'wpt-server-template' not in info['requirements']:info['requirements'].append('wpt-server-template')
    # Server-generated resources require the actual WPT server even in a
    # script-free document. Serving original Python/template bytes is not an oracle.
    for _ in range(len(metadata)+1):
        changed=False
        for info in metadata.values():
            targets=[item.get('target') for item in info['resources']]
            needs=any(target and (('pipe=' in target.get('query','')) or
                set(metadata.get(target.get('path'),{}).get('requirements',[]))&{'wpt-server-handler','wpt-server-template','wpt-server-resource'}) for target in targets)
            if needs and 'wpt-server-resource' not in info['requirements']:info['requirements'].append('wpt-server-resource');changed=True
        if not changed:break
    cases=[]
    for info in documents:
        for reference in info['references']:
            target=reference['target'];ref_info=metadata.get(target['path']) if target else None
            special=target and target.get('special')=='about:blank'
            cases.append({'test':info['path'],'reference':target,'referenceHref':reference['href'],'relation':reference['relation'],
              'kind':info['kind'],'fuzzy':None if 'xml-base-context-unresolved' in info['requirements'] else fuzzy(info['fuzzyMetadata'],reference['href'],info['path'],info['base']),
              'testRequirements':info['requirements'],'referenceRequirements':ref_info['requirements'] if ref_info else [] if special else ['unresolved-reference'],
              'baseline38':False})
    baseline=json.loads(BASELINE.read_text());baseline_set={(c['test'],c['reference']) for c in baseline['cases']}
    for case in cases:case['baseline38']=(case['test'],case['reference']['path'] if case['reference'] else None) in baseline_set
    missing=header_missing
    for info in metadata.values():
        for item in info['resources']+info['references']:
            target=item.get('target')
            if target and target.get('path') and target['path'] not in present:missing.setdefault(target['path'],[]).append(info['path'])
    existing={p:proof.lookup(p) for p in missing};existing={p:e for p,e in existing.items() if e and e['mode']!='40000'}
    script_inputs=[info for name,info in metadata.items() if name.startswith('svg/') and Path(name).suffix=='.js']
    summary={'subtreeFiles':sum(e['scope']=='complete-svg-subtree' for e in entries),'subtreeBytes':sum(e['bytes'] for e in entries if e['scope']=='complete-svg-subtree'),
      'documentKinds':dict(Counter(d['kind'] for d in documents)),'reftestDocuments':len({c['test'] for c in cases}),'reftestRelations':len(cases),
      'relations':dict(Counter(c['relation'] for c in cases)),'reftestKinds':dict(Counter(c['kind'] for c in cases)),
      'scriptInputs':dict(Counter(i['kind'] for i in script_inputs)),'baseline38':sum(c['baseline38'] for c in cases),
      'unfetchedUpstreamDependencies':len(existing),'originallyAbsentDependencyURLs':len(set(missing)-existing.keys())}
    return {'revision':PIN,'classification':RULES,'summary':summary,'documents':documents,'scriptInputs':script_inputs,
      'resourceMetadata':metadata,'cases':cases,'baselineManifestSha256':sha(BASELINE.read_bytes()),
      'unfetchedUpstreamDependencies':{p:{'gitBlob':e['sha'],'referencedBy':missing[p]} for p,e in existing.items()},
      'originallyAbsentDependencyURLs':{p:missing[p] for p in missing if p not in existing}}

def generate(snapshot,tree_path):
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=snapshot,text=True).strip()!=PIN:raise ValueError('Snapshot commit differs from pin')
    tree=json.loads(tree_path.read_text())
    if tree['sha']!=TREE or tree.get('truncated') or tree_identity(tree['tree'])!=TREE:raise ValueError('Wrong, incomplete or truncated SVG subtree')
    shutil.copyfile(tree_path,ROOT/'tree.json');upstream=ROOT/'upstream';upstream.mkdir(exist_ok=True);entries=[]
    for entry in tree['tree']:
        if entry['type']!='blob':continue
        path='svg/'+entry['path'];data=(snapshot/path).read_bytes()
        if blob(data)!=entry['sha'] or len(data)!=entry['size']:raise ValueError('Wrong upstream bytes: '+path)
        target=upstream/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        entries.append({'path':path,'mode':entry['mode'],'bytes':len(data),'gitBlob':entry['sha'],'sha256':sha(data),'scope':'complete-svg-subtree'})
    proof=GitProof(snapshot=snapshot)
    if proof.lookup('svg')['sha']!=TREE:raise ValueError('SVG tree is not bound to commit')
    present={e['path'] for e in entries}
    for path in sorted(snapshot.rglob('*')):
        if not path.is_file() or '.git' in path.relative_to(snapshot).parts:continue
        name=path.relative_to(snapshot).as_posix()
        if name in present:continue
        expected=proof.lookup(name)
        if expected is None:continue
        data=path.read_bytes()
        if blob(data)!=expected['sha']:raise ValueError('Wrong dependency bytes: '+name)
        target=upstream/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        entries.append({'path':name,'mode':expected['mode'],'bytes':len(data),'gitBlob':expected['sha'],'sha256':sha(data),'scope':'license' if name=='LICENSE.md' else 'dependency'})
    entries.sort(key=lambda e:e['path']);inventory=derive(entries,upstream,proof)
    source={'format':'wpt-svg-whole-tree-v1','repository':'https://github.com/web-platform-tests/wpt','revision':PIN,'svgTree':TREE,'treeTruncated':False,
      'scope':'Every blob in the SVG subtree plus discovered pinned original reference/resources and root license; unresolved URI contexts remain explicit. Inventory is not test success.','files':entries}
    (ROOT/'source.json').write_text(json.dumps(source,indent=2)+'\n');(ROOT/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
    (ROOT/'git-proof.json').write_text(json.dumps(proof.data,indent=2)+'\n')
    (ROOT/'.build/required-sparse-checkout').write_text('/svg/\n/LICENSE.md\n'+''.join('/'+p+'\n' for p in inventory['unfetchedUpstreamDependencies']))
    print(json.dumps(inventory['summary']))

def check():
    source=json.loads((ROOT/'source.json').read_text());inventory=json.loads((ROOT/'inventory.json').read_text())
    if source.get('revision')!=PIN or source.get('svgTree')!=TREE or source.get('treeTruncated') is not False:raise ValueError('Corpus pin mismatch')
    tree=json.loads((ROOT/'tree.json').read_text());proof=GitProof(data=json.loads((ROOT/'git-proof.json').read_text()))
    declared={(e['path'][4:],e['mode'],e['gitBlob']) for e in source['files'] if e['scope']=='complete-svg-subtree'}
    if proof.lookup('svg')['sha']!=TREE or tree_identity(tree['tree'])!=TREE or declared!={(e['path'],e['mode'],e['sha']) for e in tree['tree'] if e['type']=='blob'}:raise ValueError('Complete Git subtree identity differs')
    for entry in source['files']:
        data=(ROOT/'upstream'/entry['path']).read_bytes()
        if len(data)!=entry['bytes'] or sha(data)!=entry['sha256'] or blob(data)!=entry['gitBlob']:raise ValueError('Corpus identity mismatch: '+entry['path'])
        if entry['scope']!='complete-svg-subtree':
            expected=proof.lookup(entry['path'])
            if expected is None or expected['sha']!=entry['gitBlob']:raise ValueError('Dependency not bound to pinned commit: '+entry['path'])
    actual=derive(source['files'],ROOT/'upstream',proof)
    if actual!=inventory:
        fields=[k for k in actual if actual.get(k)!=inventory.get(k)]
        raise ValueError('Inventory differs from original bytes: '+', '.join(fields))
    summary=actual['summary']
    if summary['subtreeFiles']!=2452 or summary['reftestRelations']!=601 or summary['baseline38']!=38 or summary['relations']!={'match':595,'mismatch':6}:raise ValueError('Pinned corpus denominator changed')
    if summary['unfetchedUpstreamDependencies']:raise ValueError('Existing pinned dependency bytes not fetched')
    print(json.dumps({'fixtureIntegrity':'PASS','files':len(source['files']),'reftestRelations':len(actual['cases']),'scope':'Integrity only, no renderer passes'}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--snapshot',type=Path);parser.add_argument('--tree',type=Path);parser.add_argument('--check',action='store_true');a=parser.parse_args()
    if a.check:check()
    elif a.snapshot and a.tree:generate(a.snapshot.resolve(),a.tree.resolve())
    else:parser.error('choose --check or --snapshot DIR --tree SVG-TREE.json')
