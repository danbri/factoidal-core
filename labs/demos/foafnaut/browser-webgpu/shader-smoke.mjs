import assert from 'node:assert/strict';import {pathToFileURL} from 'node:url';
const [origin,pw,chrome]=process.argv.slice(2);const {chromium}=await import(pathToFileURL(pw).href);
const browser=await chromium.launch({executablePath:chrome,headless:true});
try{
 const page=await browser.newPage();await page.goto(origin);
 const ready=()=>page.waitForFunction(()=>document.querySelector('#download')?.disabled===false,{},{timeout:90000});await ready();
 const initial=await page.locator('#canvas').evaluate(c=>c.toDataURL());await page.locator('#wgsl-tab').click();
 const original=await page.locator('#wgsl-source').inputValue();assert.equal(await page.locator('#submitted-code').textContent(),original);
 const changed=original.replace('return vec4f(rgb,1.0); }','return vec4f(rgb*(1.0 + (-0.25)),1.0); }');assert.notEqual(changed,original);
 await page.locator('#wgsl-source').fill(changed);assert.equal(await page.locator('#download').isEnabled(),false);
 await page.locator('#shader-apply').click();await ready();assert.match(await page.locator('#status').textContent(),/MANUAL WGSL/);
 assert.equal(await page.locator('#submitted-code').textContent(),changed);assert.notEqual(await page.locator('#canvas').evaluate(c=>c.toDataURL()),initial);
 const first=await page.locator('#canvas').evaluate(c=>c.toDataURL());
 const opt=await page.locator('#scalar-select option').allTextContents();const idx=opt.findIndex(x=>x.includes('· -0.25 ·'));assert(idx>=0);
 await page.locator('#scalar-select').selectOption(String(idx));await page.locator('#scalar-range').fill('-0.75');await page.locator('#scalar-range').dispatchEvent('input');
 await page.waitForTimeout(400);await ready();assert.notEqual(await page.locator('#canvas').evaluate(c=>c.toDataURL()),first);
 assert.match(await page.locator('#submitted-code').textContent(),/rgb\*\(1\.0 \+ \(-0\.75\)\)/);
 await page.locator('#wgsl-source').fill('not WGSL');await page.locator('#shader-apply').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.equal(await page.locator('#canvas').isVisible(),false);assert.equal(await page.locator('#download').isEnabled(),false);
 assert.equal(await page.locator('#submitted-code').textContent(),'not WGSL');assert.match(await page.locator('#shader-diagnostics').textContent(),/compilation failed/);
 await page.locator('#shader-reset').click();await ready();assert.equal(await page.locator('#canvas').evaluate(c=>c.toDataURL()),initial);assert.doesNotMatch(await page.locator('#status').textContent(),/MANUAL/);
 console.log('PASS exact submitted WGSL; edited shader and negative scalar drag change actual GPU pixels; compile failure clears output; reset restores original pixels/evidence');
}finally{await browser.close();}
