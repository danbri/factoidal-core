// Fails when a page costs more paint items or floats than its recorded budget.
// Counts are deterministic, so this gate is exact on a loaded machine.
// Usage: node check-budget.mjs WEB_RENDER_NATIVE
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
const native=process.argv[2];
if(!native)throw Error('usage: check-budget.mjs WEB_RENDER_NATIVE');
const here=dirname(fileURLToPath(import.meta.url));
const budgets={'default.html':{primitives:900,floats:26000},'status.html':{primitives:8700,floats:245000}};
for(const [name,budget] of Object.entries(budgets)){
  const out=execFileSync(native,[resolve(here,'fixtures',name),'800','600'],{maxBuffer:1<<26});
  const a=JSON.parse(out);
  assert.equal(a.error,undefined,name);
  assert(a.primitiveCount<=budget.primitives,`${name}: ${a.primitiveCount} paint items, budget ${budget.primitives}`);
  assert(a.data.length<=budget.floats,`${name}: ${a.data.length} floats, budget ${budget.floats}`);
  console.log(`PASS ${name}: ${a.primitiveCount} paint items, ${a.data.length} floats`);
}
