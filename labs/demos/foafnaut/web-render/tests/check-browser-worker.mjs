#!/usr/bin/env node
import assert from 'node:assert/strict';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
const [url,playwrightPath,chrome,out]=process.argv.slice(2);
if(!out)throw Error('usage: check-browser-worker.mjs HARNESS_URL PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIRECTORY');
await mkdir(out,{recursive:true});
const {chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:chrome,headless:true});
let report={status:'RUNNING',scope:'Actual browser Worker/Lean execution and foreground responsiveness; no GPU or conformance claim'};
try{
 const page=await browser.newPage();await page.goto(url);await page.locator('#run').click();
 await page.waitForFunction(()=>['PASS','FAIL'].includes(window.rendererWorkerTest?.status),{},{timeout:30000});
 report={...report,...await page.evaluate(()=>window.rendererWorkerTest)};
 assert.equal(report.status,'PASS',report.failure);assert.equal(report.checks.length,3);assert(report.foregroundTicks>0);
 await page.screenshot({path:resolve(out,'renderer-worker.png')});
}catch(error){report.status='FAIL';report.failure=String(error);throw error;}finally{await browser.close();await writeFile(resolve(out,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
