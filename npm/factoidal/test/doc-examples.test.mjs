// Every ```js example in README.md and API.md is executed here, as an ES
// module that imports the package by its published name. A fence written
// ```js browser needs a page (fetch of a page-relative URL, IndexedDB); it
// is compiled with `node --check` only. Real-browser runs of those
// examples are https://github.com/danbri/factoidal/issues/882 item 7.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, mkdtempSync, mkdirSync, symlinkSync, writeFileSync, rmSync, readdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Worker } from 'node:worker_threads';
import { spawnSync } from 'node:child_process';

const pkg = dirname(dirname(fileURLToPath(import.meta.url)));
const work = mkdtempSync(join(tmpdir(), 'factoidal-doc-examples-'));
mkdirSync(join(work, 'node_modules', '@factoidal'), { recursive: true });
symlinkSync(pkg, join(work, 'node_modules', '@factoidal', 'core'), 'dir');
test.after(() => rmSync(work, { recursive: true, force: true }));

function blocks(file) {
  const text = readFileSync(join(pkg, file), 'utf8');
  const out = [];
  const re = /^```js( browser)?\n([\s\S]*?)^```$/gm;
  let m;
  while ((m = re.exec(text)) !== null) {
    const line = text.slice(0, m.index).split('\n').length;
    out.push({ file, line, browser: !!m[1], code: m[2] });
  }
  return out;
}

const all = [...blocks('README.md'), ...blocks('API.md')];

test('the documents have examples', () => {
  assert.ok(all.length >= 15, `found ${all.length}`);
});

for (const b of all) {
  test(`${b.file}:${b.line}${b.browser ? ' (browser: syntax only)' : ''}`, async (t) => {
    const path = join(work, `${b.file.replace('.', '_')}_${b.line}.mjs`);
    let code = b.code;
    let fixtureHits;
    // The documented deployment URL is a placeholder. Execute the unchanged
    // reader/query logic against real HTTP and committed generation bytes.
    if (code.includes("'https://storage.example/stores/tiny/'")) {
      const fixture = await lwsExampleFixture();
      t.after(() => fixture.worker.terminate());
      fixtureHits = fixture.hits;
      code = code.replace("'https://storage.example/stores/tiny/'", JSON.stringify(fixture.url));
    }
    writeFileSync(path, code);
    const args = b.browser ? ['--check', path] : ['--stack-size=4000', path];
    const r = spawnSync(process.execPath, args, { cwd: work, encoding: 'utf8', timeout: 120000 });
    assert.equal(r.status, 0, `${b.file}:${b.line} exited ${r.status}\n${r.stderr}`);
    if (fixtureHits) {
      assert.ok(Atomics.load(fixtureHits, 0) > 0, 'example made authenticated HTTP reads');
      assert.match(r.stdout, /"value":"7"/, 'example query counts the real seven-triple fixture');
    }
  });
}

async function lwsExampleFixture() {
  const files = {};
  const root = join(pkg, 'test/fixtures/sbm11-tiny/root');
  const collect = (dir, prefix = '') => {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const name = prefix + entry.name;
      if (entry.isDirectory()) collect(join(dir, entry.name), name + '/');
      else files['/stores/tiny/' + name] = readFileSync(join(dir, entry.name));
    }
  };
  collect(root);
  const shared = new SharedArrayBuffer(4), hits = new Int32Array(shared);
  const worker = new Worker(`
    const {parentPort,workerData}=require('node:worker_threads');
    const http=require('node:http');
    const hits=new Int32Array(workerData.shared);
    const server=http.createServer((req,res)=>{
      if(req.headers.authorization!=='Bearer an LWS access token'){res.writeHead(401).end();return;}
      const file=workerData.files[new URL(req.url,'http://localhost').pathname];
      if(!file){res.writeHead(404).end();return;}
      Atomics.add(hits,0,1);
      const bytes=Buffer.from(file);
      // Whole GET fallback is supported by the LWS reader; no RDF logic here.
      res.writeHead(200,{'content-type':'application/octet-stream','content-length':bytes.length,etag:'"fixture-v1"'});
      res.end(bytes);
    });
    server.listen(0,'127.0.0.1',()=>parentPort.postMessage(server.address().port));
  `, { eval: true, workerData: { files, shared } });
  try {
    const port = await new Promise((resolve, reject) => {
      worker.once('message', resolve); worker.once('error', reject);
      worker.once('exit', code => reject(new Error('fixture server exited ' + code)));
    });
    return { worker, hits, url: `http://127.0.0.1:${port}/stores/tiny/` };
  } catch (error) { await worker.terminate(); throw error; }
}
