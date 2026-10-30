// Standalone browser checks; set PLAYWRIGHT_MODULE to an installed playwright-core entry.
import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import assert from 'node:assert/strict';
const root=fileURLToPath(new URL('../../',import.meta.url));
const {chromium}=await import(process.env.PLAYWRIGHT_MODULE||process.argv[2]||'playwright-core');
const routes={
 '/factoidal/web/hub/assets/code-output.mjs':'docs/web/hub/assets/code-output.mjs',
 '/factoidal/web/hub/assets/code-output.css':'docs/web/hub/assets/code-output.css',
 '/factoidal/vendor/shiki/highlight.mjs':'third_party/shiki/highlight.mjs',
};
const hub=await readFile(resolve(root,'docs/_includes/hub.njk'),'utf8');
const prettySource=hub.slice(hub.indexOf('function prettyShortenIri('),hub.indexOf('// Fixed bindings'));
const source='answer = 1 < 2 ? "<é & >" : "no";\n\n';
const server=createServer(async(req,res)=>{
 try{
  if(req.url==='/pretty-source.mjs'){res.setHeader('Content-Type','text/javascript; charset=utf-8');res.end(prettySource+'\nexport {pretty};');return;}
  if(req.url==='/'){
   res.setHeader('Content-Type','text/html; charset=utf-8');res.end(`<link rel="stylesheet" href="/factoidal/web/hub/assets/code-output.css"><factoidal-code-output id="live"></factoidal-code-output><pre><code class="language-observable-js" data-hub-cell-flags="closed"></code></pre><script type="module">import{enhanceCodeBlocks}from'/factoidal/web/hub/assets/code-output.mjs';import{pretty}from'/pretty-source.mjs';const code=document.querySelector('pre code');code.textContent=${JSON.stringify(source)};enhanceCodeBlocks(document);await document.querySelector('#live').setValue(${JSON.stringify(source)},{language:'javascript',formattedText:${JSON.stringify('engine supplied\nformatted\n')}});const dynamic=pretty(${JSON.stringify(source)},{language:'javascript'});dynamic.id='pretty-live';document.body.append(dynamic);window.ready=true;</script>`);return;
  }
  const path=routes[req.url];if(!path){res.statusCode=404;res.end();return;}
  res.setHeader('Content-Type',path.endsWith('.css')?'text/css':'text/javascript');res.end(await readFile(resolve(root,path)));
 }catch(e){res.statusCode=500;res.end(String(e));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
let browser;
try{
 browser=await chromium.launch({channel:process.env.CHROME_CHANNEL||'chrome',headless:true});
 const context=await browser.newContext({permissions:['clipboard-read','clipboard-write']});
 const page=await context.newPage();const errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto(`http://127.0.0.1:${server.address().port}/`);await page.waitForFunction(()=>window.ready);
 assert.equal(await page.locator('#live code').textContent(),source);
 assert.ok(await page.locator('#live code span[style]').count());
 await page.locator('#live button').filter({hasText:/^Wrap$/}).click();assert.equal(await page.locator('#live .code-wrap').count(),1);
 await page.locator('#live button').filter({hasText:/^Formatted$/}).click();assert.equal(await page.locator('#live code').textContent(),'engine supplied\nformatted\n');
 await page.locator('#live button').filter({hasText:/^Copy$/}).click();assert.equal(await page.evaluate(()=>navigator.clipboard.readText()),source);
 await page.locator('#live button').filter({hasText:/^Raw$/}).click();assert.equal(await page.locator('#live code').textContent(),source);
 const executable=page.locator('code.language-observable-js');assert.equal(await executable.textContent(),source);assert.equal(await executable.getAttribute('data-hub-cell-flags'),'closed');
 assert.equal(await page.evaluate(()=>new Function(document.querySelector('code.language-observable-js').textContent+';return answer;')()),'<é & >');
 await page.emulateMedia({colorScheme:'dark'});assert.equal(await page.locator('#live pre').evaluate(e=>getComputedStyle(e).backgroundColor),'rgb(36, 41, 46)');
 await page.locator('#live').evaluate(e=>e.setValue('a\r\nb\n\n',{language:'json'}));assert.equal(await page.locator('#live code').textContent(),'a\r\nb\n\n');
 assert.equal(await page.locator('#pretty-live code').textContent(),source);
 await page.locator('code.language-observable-js').evaluate(code=>{code.parentElement.hidden=true;});
 assert.equal(await executable.evaluate(code=>getComputedStyle(code.parentElement.previousElementSibling).display),'none');
 await executable.evaluate(code=>{code.parentElement.hidden=false;code.textContent='edited = 42;\n';});
 await executable.evaluate(async code=>{const {enhanceCodeBlocks}=await import('/factoidal/web/hub/assets/code-output.mjs');enhanceCodeBlocks(document);});
 await page.locator('code.language-observable-js').evaluate(code=>code.parentElement.previousElementSibling.querySelector('button').click());
 await page.waitForFunction(()=>document.querySelector('code.language-observable-js').parentElement.previousElementSibling.querySelector('button').textContent==='Copied');
 assert.equal(await page.evaluate(()=>navigator.clipboard.readText()),'edited = 42;\n');
 assert.deepEqual(errors,[]);console.log('PASS: exact text, highlight, Copy/Wrap/Raw/Formatted, executable flags, dark theme, CRLF fallback, actual hub pretty multiline, source hide/edit');
}finally{await browser?.close();await new Promise(r=>server.close(r));}
