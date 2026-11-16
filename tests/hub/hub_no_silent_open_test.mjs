// A link on the Hub never leaves Foafnaut by itself (owner, 2026-11-16). Static checks of the
// Hub hosts: the worker asks the page to open a host tab only while its "Another site" page for
// that very address is shown (a press on that page's button); the page calls window.open only
// for that message; Textnaut's Hub page calls window.open nowhere. Also: the Wikimedia REST
// address of an article, and fetchOutside's order (copy, then a direct read, then nothing).
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';import path from 'node:path';

const root=path.resolve(path.dirname(new URL(import.meta.url).pathname),'../..');
const read=f=>fs.readFileSync(path.join(root,f),'utf8');

test('the worker posts open only from its "Another site" page', () => {
  const lines=read('docs/web/hub/foafnaut/browser-worker.mjs').split('\n').filter(l=>/type:'open'/.test(l));
  assert.ok(lines.length>=1);
  for(const l of lines)assert.match(l,/doc\?\.outside===url/,`unguarded open: ${l.trim()}`);
});

test('browser.mjs calls window.open only for the worker\'s open message', () => {
  const src=read('docs/web/hub/foafnaut/browser.mjs');
  const calls=[...src.matchAll(/window\.open\(/g)].map(m=>m.index);
  assert.equal(calls.length,1);
  const handler=src.lastIndexOf("if(data.type==='open'){",calls[0]);
  assert.ok(handler>=0&&calls[0]-handler<200,'window.open is outside the open handler');
});

test('Textnaut on the Hub calls window.open nowhere', () => {
  for(const f of ['app.mjs','engine-worker.mjs','engine-core.mjs','grid-view.mjs'])
    assert.doesNotMatch(read(`docs/web/hub/textnaut/${f}`),/window\.open\(/,f);
});

test('wikimediaRest maps article addresses, desktop and mobile, and nothing else', async () => {
  const {wikimediaRest}=await import('../../docs/web/hub/foafnaut/copies.mjs');
  assert.equal(wikimediaRest('https://en.wikipedia.org/wiki/World_Wide_Web'),'https://en.wikipedia.org/api/rest_v1/page/html/World_Wide_Web');
  assert.equal(wikimediaRest('https://de.m.wikipedia.org/wiki/Erlk%C3%B6nig?x=1'),'https://de.wikipedia.org/api/rest_v1/page/html/Erlk%C3%B6nig');
  assert.equal(wikimediaRest('https://fr.wikisource.org/wiki/Le_Dormeur_du_val'),'https://fr.wikisource.org/api/rest_v1/page/html/Le_Dormeur_du_val');
  assert.equal(wikimediaRest('https://en.wikipedia.org/w/index.php?title=X'),undefined);
  assert.equal(wikimediaRest('http://en.wikipedia.org/wiki/X'),undefined);
  assert.equal(wikimediaRest('https://wikipedia.org.example/wiki/X'),undefined);
  assert.equal(wikimediaRest('https://example.org/wiki/X'),undefined);
});

test('fetchOutside: copy first, then a direct read, an origin that refuses is not asked again', async () => {
  const real=globalThis.fetch;const asked=[];
  globalThis.fetch=async(url,init)=>{
    const u=String(url);asked.push(u);
    if(u.endsWith('/copies/index.json'))return new Response(JSON.stringify({copies:[],urls:{}}));
    if(u.startsWith('https://en.wikipedia.org/api/rest_v1/')){assert.equal(init?.credentials,'omit');return new Response('<p>wiki</p>',{headers:{'content-type':'text/html'}});}
    if(u.startsWith('https://open.example/'))return new Response('<p>open</p>');
    throw new TypeError('Failed to fetch');
  };
  try{
    const {fetchOutside}=await import('../../docs/web/hub/foafnaut/copies.mjs?outside');
    const wiki=await fetchOutside('https://en.m.wikipedia.org/wiki/Web');
    assert.equal(wiki.url,'https://en.wikipedia.org/wiki/Web');assert.equal(wiki.via,'wikimedia-api');
    assert.equal((await fetchOutside('https://open.example/a')).via,'cors');
    assert.equal(await fetchOutside('https://closed.example/a'),undefined);
    const n=asked.length;
    assert.equal(await fetchOutside('https://closed.example/b'),undefined);
    assert.equal(asked.length,n,'a refusing origin was asked again');
    assert.equal(await fetchOutside('mailto:x@example.org'),undefined);
  }finally{globalThis.fetch=real;}
});
