#!/usr/bin/env python3
"""Snapshot Wikimedia user pages and extract labelled SPARQL templates."""
import hashlib, json, re, urllib.parse, urllib.request
from pathlib import Path
API = 'https://www.wikidata.org/w/api.php'
ROOT = 'User:MartinPoulter/queries'
DEST = Path(__file__).resolve().parents[2] / 'formal/lean4/Wikidata/corpus/martin-poulter'

def api(**params):
    params.update(action='query', format='json', formatversion='2')
    req = urllib.request.Request(API + '?' + urllib.parse.urlencode(params), headers={'User-Agent':'Factoidal corpus research (https://github.com/danbri/factoidal-core)'})
    with urllib.request.urlopen(req, timeout=90) as r: data = json.load(r)
    if 'error' in data: raise RuntimeError(str(data['error']))
    return data

def main():
    names, cont = [ROOT], {}
    while True:
        data = api(list='allpages', apnamespace=2, apprefix='MartinPoulter/queries/', aplimit='max', **cont)
        names.extend(p['title'] for p in data['query']['allpages'])
        cont = data.get('continue', {})
        if not cont: break
    data = api(titles='|'.join(names), prop='revisions', rvprop='ids|timestamp|content', rvslots='main')
    pages = {p['title']:p for p in data['query']['pages']}
    if set(names) != set(pages) or any('revisions' not in p for p in pages.values()): raise RuntimeError('incomplete fetch')
    records, blocks = [], []
    for title in names:
        rev = pages[title]['revisions'][0]; source = rev['slots']['main']['content']
        link = 'https://www.wikidata.org/w/index.php?' + urllib.parse.urlencode({'title':title,'oldid':rev['revid']})
        history = 'https://www.wikidata.org/w/index.php?' + urllib.parse.urlencode({'title':title,'action':'history'})
        records.append({'title':title,'revision':rev['revid'],'timestamp':rev['timestamp'],'revision_url':link,'history_url':history,'sha256':hashlib.sha256(source.encode()).hexdigest(),'wikitext':source})
        pattern = re.compile(r'\{\{\s*SPARQL2?\s*\|\s*query\s*=([\s\S]*?)(?<!\S)\}\}[ \t]*$',re.I|re.M)
        matches = list(pattern.finditer(source)); starts = re.findall(r'\{\{\s*SPARQL2?\s*\|',source,re.I)
        if len(starts) != len(matches): raise RuntimeError(f'incomplete extraction {title}: {len(matches)}/{len(starts)}')
        for i,m in enumerate(matches,1):
            query=m.group(1)
            if re.search(r'\{\{\s*SPARQL2?\s*\|',query,re.I): raise RuntimeError(f'overlapping templates in {title}')
            sections=list(re.finditer(r'^(={2,6})\s*(.*?)\s*\1\s*$',source[:m.start()],re.M))
            blocks.append({'page':title,'revision':rev['revid'],'revision_url':link,'history_url':history,'section':sections[-1].group(2) if sections else None,'ordinal':i,'query':query})
    DEST.mkdir(parents=True,exist_ok=True)
    (DEST/'pages.json').write_text(json.dumps({'pages':records},ensure_ascii=False,indent=2)+'\n')
    (DEST/'queries.json').write_text(json.dumps({'extraction':'standalone SPARQL/SPARQL2 query templates; wikitext not expanded','queries':blocks},ensure_ascii=False,indent=2)+'\n')
    print(f'{len(records)} pages; {len(blocks)} extracted templates')
if __name__ == '__main__': main()
