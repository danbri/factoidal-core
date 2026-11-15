// One source for Textnaut's cell mapping. The terminal program (labs/demos/foafnaut/textnaut/
// textnaut.ts) imports grid.ts; the Hub's Textnaut page and notebook import grid.mjs, which the
// build makes from that same file (docs/web/hub/textnaut/emit-grid.cjs, grid.11ty.js). These
// tests fail if either host gets its own copy, or if the made module stops matching grid.ts.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {ROOT,emitGrid,gridModuleURL} from './_textnaut_host.mjs';

const require=(await import('node:module')).createRequire(import.meta.url);
const {GRID_SOURCE,HEADER}=require(path.join(ROOT,'docs/web/hub/textnaut/emit-grid.cjs'));
const read=f=>fs.readFileSync(path.join(ROOT,f),'utf8');

test('the made module is grid.ts with its types removed, line for line', () => {
  assert.equal(GRID_SOURCE,path.join(ROOT,'labs/demos/foafnaut/textnaut/grid.ts'));
  const source=fs.readFileSync(GRID_SOURCE,'utf8'),made=emitGrid();
  assert.ok(made.startsWith(HEADER));
  const a=source.split('\n'),b=made.slice(HEADER.length).split('\n');
  assert.equal(b.length,a.length,'same number of lines');
  // Each line keeps its code in its columns: types are blanked with spaces, nothing else changes.
  for(const [i,line] of b.entries()){
    assert.equal(line.length,a[i].length,`line ${i+1} keeps its length`);
    for(let c=0;c<line.length;c++)if(line[c]!==' ')assert.equal(line[c],a[i][c],`line ${i+1} column ${c+1}`);
  }
});

test('the made module exports what grid.ts exports', async () => {
  const grid=await import(gridModuleURL());
  const exported=[...read('labs/demos/foafnaut/textnaut/grid.ts').matchAll(/^export (?:const|function) ([A-Za-z0-9_]+)/gm)].map(m=>m[1]).sort();
  assert.deepEqual(Object.keys(grid).sort(),exported);
});

test('no copy of grid.ts is committed for the Hub; both hosts import the one module', () => {
  assert.ok(!fs.existsSync(path.join(ROOT,'docs/web/hub/textnaut/grid.mjs')),'docs/web/hub/textnaut/grid.mjs must not be committed: the build makes it');
  assert.match(read('labs/demos/foafnaut/textnaut/textnaut.ts'),/from "\.\/grid\.ts"/);
  assert.match(read('docs/web/hub/textnaut/engine-worker.mjs'),/import\('\.\/grid\.mjs'\)/);
  assert.match(read('docs/web/hub/textnaut/grid.11ty.js'),/permalink: "\/web\/hub\/textnaut\/grid\.mjs"/);
  assert.match(read('docs/web/hub/textnaut/grid.11ty.js'),/require\("\.\/emit-grid\.cjs"\)/);
  // No other file of the Hub defines the mapping's functions.
  for(const dir of ['docs/web/hub/textnaut','docs/web/hub/notebook'])
    for(const f of fs.readdirSync(path.join(ROOT,dir)).filter(f=>/\.(m?js|cjs)$/.test(f)))
      assert.doesNotMatch(read(`${dir}/${f}`),/function (layoutGrid|readPaint|sanitizeText|cellWidth)\b/,`${dir}/${f} defines a grid function`);
});

test('the made module maps positioned text the same as grid.ts does in the terminal program', async () => {
  const grid=await import(gridModuleURL());
  // Two words and a link, as the engine gives them (glyph rows [id, x, y, advance, start, end]).
  const g=(x,n)=>Array.from({length:n},(_,i)=>[65,x+i*CELL,10,CELL,i,i+1]),CELL=grid.CELL_WIDTH;
  const out=grid.layoutGrid({cols:40,trimLeft:true,
    runs:[{text:'Hello',size:16,glyphs:g(8,5)},{text:'world',size:16,glyphs:g(8+6*CELL,5)},{text:'next',size:16,glyphs:g(8,4).map(r=>[r[0],r[1],r[2]+20,r[3],r[4],r[5]])}],
    links:[[3,'b.html',8,28,4*CELL,19.2]],resolve:h=>new URL(h,'https://hub.test/a/').href});
  assert.deepEqual(grid.dumpText(out).split('\n').slice(0,2),['Hello world','next[1]']);
  assert.deepEqual(out.targets,['https://hub.test/a/b.html']);
  assert.equal(grid.sanitizeText('a\u001b[2Jb‮'),'a�[2Jb');
});
