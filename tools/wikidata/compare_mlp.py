#!/usr/bin/env python3
"""Compare the first N harvested MLP queries with Lean and the Java oracle.

Requires a built Lean parser and Wikimedia's executable JAR. The JAR is passed
explicitly; its SHA-256 is recorded, not assumed to match the source checkout.
Does not execute any query against a SPARQL endpoint.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'formal/lean4'
CORPUS = LEAN / 'Wikidata/corpus/martin-poulter/queries.json'

def run_lean(records, language=None):
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / 'queries.json'
        path.write_text(json.dumps(records), encoding='utf-8')
        command = ['lake', 'env', 'lean', '--run', 'Wikidata/ParseBatch.lean', str(path)]
        if language is not None:
            command.extend(['--rewrite', language])
        p = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, check=True, timeout=300)
    out = [json.loads(line) for line in p.stdout.splitlines()]
    if len(out) != len(records) or [x['id'] for x in out] != [x['id'] for x in records]:
        raise RuntimeError('Lean responses missing, duplicated, or out of order')
    return {x['id']: x for x in out}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jar', required=True, type=Path)
    parser.add_argument('--count', type=int, default=100)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.count <= 0: parser.error('--count must be positive')
    jar = args.jar.resolve()
    corpus_bytes = CORPUS.read_bytes()
    corpus = json.loads(corpus_bytes)['queries']
    if args.count > len(corpus): parser.error('count exceeds available corpus')
    items = corpus[:args.count]
    requests = [{'protocol_version': 1, 'request_id':str(i), 'query_id':str(i), 'query':q['query']} for i,q in enumerate(items)]
    wire = ''.join(json.dumps(x, ensure_ascii=False)+'\n' for x in requests)
    p = subprocess.run(['java','-Xmx512m','-Xss16m','-jar',str(jar)], input=wire, cwd=ROOT, text=True, capture_output=True, check=True, timeout=300)
    results = [json.loads(line) for line in p.stdout.splitlines()]
    if len(results) != len(items): raise RuntimeError('unexpected response count')
    for i, (res, query) in enumerate(zip(results,items)):
        if res.get('status') != 'ok' or res.get('request_id') != str(i) or res.get('query_id') != str(i):
            raise RuntimeError(f'bad oracle response at {i}')
        if res.get('query_sha256') != hashlib.sha256(query['query'].encode()).hexdigest():
            raise RuntimeError(f'query hash mismatch at {i}')
    orig = run_lean([{'id':str(i),'query':q['query']} for i,q in enumerate(items)])
    outputs = [{'id':str(i),'query':r['result']['rewritten_query']} for i,r in enumerate(results) if isinstance(r['result'].get('rewritten_query'),str)]
    converted = run_lean(outputs)
    rows = []
    for i,(q,r) in enumerate(zip(items,results)):
        result=r['result']; ident=str(i)
        rows.append({'index':i+1,'page':q['page'],'section':q['section'],'ordinal':q['ordinal'],'revision_url':q['revision_url'], 'lean_input':orig[ident], 'original_status':result['rewrite_status'], 'original_errors':result.get('errors',[]), 'original_warnings':result.get('warnings',[]), 'original_rewrites':result.get('rewrites',[]), 'lean_output':converted.get(ident)})
    report={'sample':'first records in harvested order; not random', 'count':len(rows), 'jar_sha256':hashlib.sha256(jar.read_bytes()).hexdigest(), 'corpus_sha256':hashlib.sha256(corpus_bytes).hexdigest(), 'lean_mode':'WDQS defaults, SPARQL 1.1', 'results':rows}
    args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('original statuses:',dict(Counter(r['original_status'] for r in rows)))
    print('Lean input:',dict(Counter(r['lean_input']['accepted'] for r in rows)))
    print('Lean outputs:',dict(Counter(r['lean_output']['accepted'] for r in rows if r['lean_output'] is not None)))
if __name__ == '__main__': main()
