// browser.mjs — serve /opt/wc and run index.html in headless Chromium.
// Usage: node browser.mjs [query string, e.g. emcc=out/emcc-o3.mjs or jco=jco-trap]
// Prints the page's JSON line.
import { createRequire } from 'node:module';
import { execSync } from 'node:child_process';
// The pre-installed Playwright (global); require() resolves it from npm's global root.
const { chromium } = createRequire(execSync('npm root -g').toString().trim() + '/')('playwright');
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { extname, join } from 'node:path';

const ROOT = process.env.WC_TOOLS ?? '/opt/wc';
const PAGE = new URL('./index.html', import.meta.url);
const types = { '.js': 'text/javascript', '.mjs': 'text/javascript', '.wasm': 'application/wasm', '.html': 'text/html' };
const server = createServer(async (req, res) => {
  const path = decodeURIComponent(new URL(req.url, 'http://x').pathname);
  try {
    const body = path === '/' ? await readFile(PAGE) : await readFile(join(ROOT, path));
    res.writeHead(200, { 'content-type': types[extname(path)] ?? (path === '/' ? 'text/html' : 'text/plain') });
    res.end(body);
  } catch { res.writeHead(404); res.end(); }
}).listen(0);
const port = server.address().port;
const browser = await chromium.launch();
const page = await browser.newPage();
page.on('console', (m) => console.error('console:', m.text()));
page.on('pageerror', (e) => console.error('pageerror:', e.message));
await page.goto(`http://127.0.0.1:${port}/?${process.argv[2] ?? ''}`);
await page.waitForFunction(() => document.getElementById('out').textContent !== 'running', null, { timeout: 120000 });
console.log(await page.textContent('#out'), JSON.stringify({ browser: browser.version() }));
await browser.close();
server.close();
