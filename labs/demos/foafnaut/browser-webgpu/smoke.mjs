#!/usr/bin/env node
// Optional local integration check: uses an already installed Chrome/Playwright.
import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [origin,playwrightPath,browserPath,screenshot]=process.argv.slice(2);
if(!origin||!playwrightPath||!browserPath)throw Error('Usage: node smoke.mjs URL /absolute/playwright-core/index.mjs /absolute/chrome [screenshot.png]');
const {chromium}=await import(pathToFileURL(playwrightPath).href);
const browser=await chromium.launch({executablePath:browserPath,headless:true});
try{
 const page=await browser.newPage({viewport:{width:1360,height:1050}}),errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 await page.route('**/*',r=>r.request().url().startsWith(origin)?r.continue():r.abort());
 await page.goto(origin);
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with')||document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.match(await page.locator('#status').innerText(),/^Rendered with/);
 assert.equal(await page.locator('#download').isEnabled(),true);
 let evidence=JSON.parse(await page.locator('#evidence').textContent());assert(evidence.primitives>0);assert(evidence.checks>0);assert.equal(evidence.stats.frames,1);
 const initial=await page.locator('#source').inputValue();
 if(screenshot)await page.screenshot({path:screenshot,fullPage:true});
 await page.locator('#fixture').selectOption('affine.svg');
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with')&&!document.querySelector('#render').disabled,{},{timeout:90000});
 evidence=JSON.parse(await page.locator('#evidence').textContent());assert.equal(evidence.width,800);
 await page.locator('#source').fill('<svg xmlns="http://www.w3.org/2000/svg" width="100" height="100"><foreignObject/></svg>');
 assert.equal(await page.locator('#download').isEnabled(),false);assert.equal(await page.locator('#canvas').isVisible(),false);
 await page.locator('#render').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.equal(await page.locator('#canvas').isVisible(),false);
 await page.locator('#source').fill(initial);
 await page.locator('#source').press('Control+Enter');
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with'),{},{timeout:90000});
 assert.equal(await page.locator('#download').isEnabled(),true);
 assert.deepEqual(errors,[]);
 const provenance=await (await page.request.get(origin+'provenance.json')).json();assert(provenance.files.some(f=>f.url.endsWith('svg-engine.wasm')));
 assert.equal((await page.request.get(origin+'lab/SVG.lean')).status(),404);
 assert.equal((await page.request.post(origin)).status(),405);
 console.log(JSON.stringify({status:'PASS',browser:await browser.version(),affineFrame:evidence,checks:['real GPU render','fixture switching','source edit invalidates output','unsupported SVG refusal','keyboard render recovery','provenance','server allowlist','read-only HTTP']},null,2));
}finally{await browser.close();}
