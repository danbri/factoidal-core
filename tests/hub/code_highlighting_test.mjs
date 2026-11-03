import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import crypto from 'node:crypto';
import {createRequire} from 'node:module';
import {highlight,languages} from '../../third_party/shiki/highlight.mjs';
const require=createRequire(import.meta.url);

test('vendored bundle hash and language/theme choices are pinned',()=>{
 const manifest=JSON.parse(fs.readFileSync(new URL('../../third_party/shiki/manifest.json',import.meta.url)));
 assert.equal(crypto.createHash('sha256').update(fs.readFileSync(new URL('../../third_party/shiki/highlight.mjs',import.meta.url))).digest('hex'),manifest.sha256);
 for(const language of ['javascript','xml','sparql','turtle','json','lean'])assert.ok(languages.includes(language));
 assert.match(highlight('const x = 1;\n','javascript'),/--shiki-dark:/);
 assert.match(highlight('<not executable>','unsupported-language'),/&#x3C;not executable>/);
});

test('real markdown fence renderer preserves executable source, flags and language class',async()=>{
 const MarkdownIt=require('../../docs/node_modules/markdown-it');const md=new MarkdownIt();const before=[];
 const config=new Proxy({on:(name,fn)=>{if(name==='eleventy.before')before.push(fn);},amendLibrary:(name,fn)=>{if(name==='md')fn(md);}}, {get:(o,k)=>k in o?o[k]:()=>{}});
 require('../../docs/.eleventy.js')(config);for(const fn of before)await fn({});
 const source='answer = 1 < 2 ? "<&>" : "no";\n';
 const html=md.render('```observable-js closed title="Answer"\n'+source+'```\n');
 assert.match(html,/language-observable-js/);assert.match(html,/data-hub-cell-flags="closed title=&quot;Answer&quot;"/);
 const body=html.slice(html.indexOf('<code'),html.lastIndexOf('</code>')).replace(/^<code[^>]*>/,'').replace(/<[^>]+>/g,'');
 assert.equal(md.utils.unescapeAll(body).replace(/&lt;/g,'<').replace(/&gt;/g,'>').replace(/&amp;/g,'&').replace(/&quot;/g,'"'),source);
 assert.match(html,/--shiki-dark:/);
});
