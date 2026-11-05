#!/usr/bin/env node
// web-render-corpus.mjs: run one web-render engine over the fixtures and print a sha256 per case.
// Two engines are equal when these reports are equal, byte for byte, in every case.
//   node tools/deploy/web-render-corpus.mjs engine.mjs [--timing] [--loader unit-loader.mjs]
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve, dirname } from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';
const here = dirname(fileURLToPath(import.meta.url));
const fx = resolve(here, '../../labs/demos/foafnaut/web-render/fixtures');
const sha = x => createHash('sha256').update(x).digest('hex').slice(0, 16);

export async function corpus(call) {
  const out = {};
  const put = (k, v) => { out[k] = v === null ? null : sha(v) + ':' + v.length; };
  for (const n of ['boxes', 'default', 'flow', 'links', 'status', 'mvp', 'scripted']) {
    const src = await readFile(resolve(fx, n + '.html'), 'utf8');
    put('html/' + n, await call('web_render_call', ['string', 'number', 'number'], [src, 800, 600]));
    put('html120/' + n, await call('web_render_call', ['string', 'number', 'number'], [src, 120, 160]));
    put('fontreq/' + n, await call('web_render_font_requests_call', ['string'], [src]));
  }
  put('refused', await call('web_render_call', ['string', 'number', 'number'], ['<div style="display:grid">x</div>', 120, 160]));
  const nt = await readFile(resolve(fx, 'graph.nt'), 'utf8');
  put('rdf', await call('web_render_rdf_call', ['string', 'number', 'number'], [nt, 380, 340]));
  put('rdf-bad', await call('web_render_rdf_call', ['string', 'number', 'number'], [nt + 'malformed', 380, 340]));
  const doc = '<base href="./assets/"><link rel="stylesheet" href="../css/doc.css"><p id="message">Before</p><a href="../next.html">Next</a>';
  const dc = o => call('web_document_call', ['string', 'string', 'number', 'number'], [doc, JSON.stringify(o), 120, 160]);
  const url = 'https://example.test/a/index.html';
  const insp = await dc({ op: 'inspect', url }); put('doc/inspect', insp);
  const j = JSON.parse(insp);
  const id = j.nodes.find(n => n.attributes.id === 'message').id, sheet = j.stylesheets[0];
  const opts = { url, commands: [{ op: 'setTextContent', nodeId: id, value: 'After' }], resources: [{ nodeId: sheet.nodeId, source: 'body{font-family:monospace;font-size:20px;line-height:24px;margin:0}p{font-size:21px}' }] };
  put('doc/render', await dc({ ...opts, op: 'render' }));
  put('doc/fontreq', await dc({ ...opts, op: 'fontRequests' }));
  put('doc/bad', await dc({ ...opts, op: 'render', commands: [{ op: 'unsupported', nodeId: id, value: 'x' }] }));
  const xml = '<?xml version="1.0"?><?xml-stylesheet type="text/xsl" href="s.xsl"?><r><i>one</i><i>two</i></r>';
  const xc = (s, o) => call('web_document_call', ['string', 'string', 'number', 'number'], [xml, JSON.stringify({ op: 'xslt', url: 'https://example.test/r.xml', stylesheetURL: 'https://example.test/s.xsl', stylesheet: s, ...o }), 320, 200]);
  put('xslt1', await xc('<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/"><html><body><xsl:for-each select="r/i"><p><xsl:value-of select="."/></p></xsl:for-each></body></html></xsl:template></xsl:stylesheet>'));
  put('xslt3', await xc('<xsl:stylesheet version="3.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/"><html><body><xsl:for-each select="r/i"><p><xsl:value-of select="upper-case(.)||string-length(.)"/></p></xsl:for-each></body></html></xsl:template></xsl:stylesheet>'));
  put('pick', await call('web_render_hit', ['string', 'number', 'number', 'number', 'number'], [JSON.stringify([[0, 'https://e.test/', 0, 0, 10, 10]]), 120, 160, 5, 5]));
  return out;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const t0 = performance.now();
  const engine = resolve(process.argv[2]);
  const factory = (await import(pathToFileURL(engine))).default;
  const mod = await factory();
  const t1 = performance.now();
  const call = (name, types, args) => { const p = mod.ccall(name, 'number', types, args); if (!p) return null; try { return mod.UTF8ToString(p); } finally { mod.ccall('web_render_free', null, ['number'], [p]); } };
  const r1 = call('web_render_call', ['string', 'number', 'number'], ['<div style="display:grid">x</div>', 120, 160]);
  const t2 = performance.now();
  let heap = 0; try { heap = mod.HEAPU8.length; } catch { /* not exported under ASSERTIONS */ }
  if (process.argv.includes('--timing')) { console.log(JSON.stringify({ loadMs: +(t1 - t0).toFixed(1), firstCallMs: +(t2 - t1).toFixed(1), heap })); process.exit(0); }
  console.log(JSON.stringify(await corpus(call), null, 0));
}
