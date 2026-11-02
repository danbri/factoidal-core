// tests/dom/diff.mjs — differential test of the Lean DOM arena
// (formal/lean4/L4Factoidal/DOM/Arena.lean) against jsdom 30.1.3
// (https://github.com/danbri/factoidal/issues/1167, milestone 6).
//
//   node tests/dom/diff.mjs L4DOM_BINARY [SCRIPTS] [OPS] [SEED]
//
// Generates SCRIPTS random scripts of OPS DOM operations each. Each script
// starts from an HTML document; jsdom runs every operation as it is generated
// (so a method is only called on a node whose interface has it), and records
// the result. The same scripts go to `l4dom ops`, which runs them on the Lean
// DOM arena. The two outputs must be the same, line by line: the result of each
// operation (`ok`, a value, or the DOMException name) and, at the end, the tree
// of every root node that a handle names. jsdom is the reference
// implementation here, not the specification; a disagreement is read against
// the DOM Standard text (whatwg/dom 3c53f93a) before either side is changed.
//
// jsdom 30.1.3 has no moveBefore(), so `move` is not generated; Lean checks for
// it are in L4Factoidal/DOM/Tests.lean.
import { JSDOM } from 'jsdom';
import { spawnSync } from 'node:child_process';
import { writeFileSync, mkdtempSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const [bin, nScripts = '2000', nOps = '60', seed0 = '1'] = process.argv.slice(2);
if (!bin) { console.error('usage: node diff.mjs L4DOM_BINARY [SCRIPTS] [OPS] [SEED]'); process.exit(2); }

const HTML = 'http://www.w3.org/1999/xhtml';
const SVG = 'http://www.w3.org/2000/svg';
const MATHML = 'http://www.w3.org/1998/Math/MathML';
const XLINK = 'http://www.w3.org/1999/xlink';
const XML = 'http://www.w3.org/XML/1998/namespace';
const XMLNS = 'http://www.w3.org/2000/xmlns/';

// A linear congruential generator, so a seed gives the same scripts on every run.
let state = BigInt(seed0);
function rnd(n) {
  state = (state * 6364136223846793005n + 1442695040888963407n) % 18446744073709551616n;
  return Number((state >> 16n) % BigInt(n));
}
const pick = (a) => a[rnd(a.length)];

const SOURCES = [
  '<!DOCTYPE html><html><head><title>t</title></head><body><p id=a>one <b>two</b> three</p><div id=b><span>x</span>y</div></body></html>',
  '<!DOCTYPE html><table><tr><td>1<td>2</table><template id=t><p>in template</p>text</template><!-- c -->',
  '<p>a<p>b<ul><li>1<li>2</ul><svg viewBox="0 0 1 1"><circle r=1 xlink:href=#x /></svg><math><mi>x</mi></math>',
  '<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd"><body>z<template><template><b>n</b></template></template>',
  '',
  '<div id=x><div id=x>dup</div></div><select><option>o</select>text',
  '<!-- before --><!DOCTYPE html><!-- after --><p>x</p>',
  '<!DOCTYPE html><html><body>x</body></html><!-- end -->',
];
const NAMES = ['div', 'p', 'span', 'template', 'b', 'Ab', 'svg', ':x', '_y', 'a b', '1a', '', 'é', 'x-y', 'DIV', 'a/b'];
const DATA = ['', 'a', 'b c', 'x', 'line\nbreak', 'é€', ' ', 'z'];
const ATTRS = ['id', 'class', 'ID', 'data-x', 'a b', '', 'x:y', 'b=c'];
const PITARGETS = ['x', 'xml-stylesheet', '1a', 'a b', 'p'];
const PIDATA = ['', 'd', 'a ?> b', 'href="s"'];

function hex(s) { return '=' + Buffer.from(s, 'utf8').toString('hex'); }

function elemName(n) {
  if (n.namespaceURI === HTML) return n.localName;
  if (n.namespaceURI === SVG) return 'svg ' + n.localName;
  if (n.namespaceURI === MATHML) return 'math ' + n.localName;
  if (n.namespaceURI === null) return n.localName;
  return '{' + n.namespaceURI + '} ' + n.localName;
}
function attrName(a) {
  if (a.namespaceURI === XLINK) return 'xlink ' + a.localName;
  if (a.namespaceURI === XML) return 'xml ' + a.localName;
  if (a.namespaceURI === XMLNS) return 'xmlns ' + a.localName;
  return a.name;
}
const ind = (d) => '| ' + ' '.repeat(2 * d);
const cmp = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

// The html5lib tree dump of a root (Harness/DomDump.lean, the same format).
function dump(win, root, out) {
  const T = win.HTMLTemplateElement;
  const work = root.nodeType === 9 ? [...root.childNodes].map((c) => [c, 0]) : [[root, 0]];
  while (work.length) {
    const [n, d] = work.shift();
    const i = ind(d);
    let kids = [...n.childNodes].map((c) => [c, d + 1]);
    switch (n.nodeType) {
      case 3: case 4: out.push(i + '"' + n.data + '"'); break;
      case 8: out.push(i + '<!-- ' + n.data + ' -->'); break;
      case 7: out.push(i + '<?' + n.target + ' ' + n.data + '?>'); break;
      case 10: {
        const ids = n.publicId === '' && n.systemId === '' ? '' : ` "${n.publicId}" "${n.systemId}"`;
        out.push(i + '<!DOCTYPE ' + n.name + ids + '>');
        break;
      }
      case 9: out.push(i + '#document'); break;
      case 11: out.push(i + '#document-fragment'); break;
      case 1: {
        out.push(i + '<' + elemName(n) + '>');
        const as = [...n.attributes].map((a) => [attrName(a), a.value]).sort((x, y) => cmp(x[0], y[0]));
        for (const [k, v] of as) out.push(ind(d + 1) + k + '="' + v + '"');
        if (n instanceof T) {
          out.push(ind(d + 1) + 'content');
          kids = [...n.content.childNodes].map((c) => [c, d + 2]).concat(kids);
        }
        break;
      }
    }
    work.unshift(...kids);
  }
}

function errName(e) {
  if (e && e.constructor && e.constructor.name === 'DOMException') return 'err ' + e.name;
  throw e; // a TypeError here is a bug of this generator
}

function genScript(lines, expect) {
  const src = pick(SOURCES);
  const win = new JSDOM(src).window;
  const doc = win.document;
  lines.push('script', 'html ' + hex(src));
  expect.push('script');
  const hs = [doc];
  const tw = doc.createTreeWalker(doc, 0xffffffff);
  while (tw.nextNode()) hs.push(tw.currentNode);
  // one operand in four is the Document or one of the first nodes in tree
  // order (the doctype, the root element), so that the rules for a Document
  // parent (steps 5 to 11 of ensure pre-insert validity) are reached
  const h = () => (rnd(4) === 0 ? rnd(Math.min(4, hs.length)) : rnd(hs.length));
  const run = (line, f) => {
    lines.push(line);
    let r;
    try { r = f(); } catch (e) { r = errName(e); }
    expect.push(r);
  };
  const isChildNode = (n) => [1, 3, 4, 7, 8, 10].includes(n.nodeType);
  const nOpsHere = Number(nOps);
  for (let k = 0; k < nOpsHere; k++) {
    const op = rnd(20);
    if (op < 2) {
      const s = pick(NAMES);
      run('el ' + hex(s), () => { hs.push(doc.createElement(s)); return 'ok'; });
    } else if (op < 3) {
      const s = pick(DATA);
      run('text ' + hex(s), () => { hs.push(doc.createTextNode(s)); return 'ok'; });
    } else if (op === 3) {
      const s = pick(DATA);
      const w = rnd(3);
      if (w === 0) run('comment ' + hex(s), () => { hs.push(doc.createComment(s)); return 'ok'; });
      else if (w === 1) run('frag', () => { hs.push(doc.createDocumentFragment()); return 'ok'; });
      else {
        const nm = pick(['html', 'x', '', 'a b', 'a>b']);
        run('doctype ' + hex(nm), () => { hs.push(doc.implementation.createDocumentType(nm, '', '')); return 'ok'; });
      }
    } else if (op === 4) {
      const t = pick(PITARGETS), s = pick(PIDATA);
      run(`pi ${hex(t)} ${hex(s)}`, () => { hs.push(doc.createProcessingInstruction(t, s)); return 'ok'; });
    } else if (op < 8) {
      const p = h(), c = h();
      run(`append ${p} ${c}`, () => { hs[p].appendChild(hs[c]); return 'ok'; });
    } else if (op < 10) {
      const p = h(), c = h();
      // a reference child among p's children most of the time
      const kids = [...hs[p].childNodes].map((x) => hs.indexOf(x)).filter((i) => i >= 0);
      const r = rnd(4) === 0 || kids.length === 0 ? (rnd(2) ? '-' : String(h())) : String(pick(kids));
      run(`insert ${p} ${c} ${r}`, () => { hs[p].insertBefore(hs[c], r === '-' ? null : hs[Number(r)]); return 'ok'; });
    } else if (op === 10) {
      const p = h(), n = h();
      const kids = [...hs[p].childNodes].map((x) => hs.indexOf(x)).filter((i) => i >= 0);
      const o = kids.length && rnd(4) ? pick(kids) : h();
      run(`replace ${p} ${n} ${o}`, () => { hs[p].replaceChild(hs[n], hs[o]); return 'ok'; });
    } else if (op === 11) {
      const c = h();
      const p = hs[c].parentNode && rnd(4) ? hs.indexOf(hs[c].parentNode) : h();
      if (p < 0) { k--; continue; }
      run(`removechild ${p} ${c}`, () => { hs[p].removeChild(hs[c]); return 'ok'; });
    } else if (op === 12) {
      const c = h();
      if (!isChildNode(hs[c])) { k--; continue; }
      run(`remove ${c}`, () => { hs[c].remove(); return 'ok'; });
    } else if (op === 13) {
      const n = h();
      if (rnd(2)) {
        const s = pick(DATA);
        run(`settext ${n} ${hex(s)}`, () => { hs[n].textContent = s; return 'ok'; });
      } else {
        run(`gettext ${n}`, () => { const v = hs[n].textContent; return v === null ? 'ok null' : 'ok ' + hex(v); });
      }
    } else if (op === 14) {
      const n = h();
      run(`normalize ${n}`, () => { hs[n].normalize(); return 'ok'; });
    } else if (op === 15) {
      const n = h(), deep = rnd(2);
      run(`clone ${n} ${deep}`, () => { hs.push(hs[n].cloneNode(deep === 1)); return 'ok'; });
    } else if (op === 16) {
      const a = h(), b = h();
      if (rnd(2)) run(`equal ${a} ${b}`, () => 'ok ' + hs[a].isEqualNode(hs[b]));
      else run(`contains ${a} ${b}`, () => 'ok ' + hs[a].contains(hs[b]));
    } else if (op === 17) {
      const t = h();
      if (hs[t].nodeType !== 1) { k--; continue; }
      run(`content ${t}`, () => {
        if (hs[t] instanceof win.HTMLTemplateElement) { hs.push(hs[t].content); return 'ok'; }
        return 'ok null';
      });
    } else if (op === 18) {
      const e = h();
      if (hs[e].nodeType !== 1) { k--; continue; }
      const q = pick(ATTRS), v = pick(DATA);
      run(`setattr ${e} ${hex(q)} ${hex(v)}`, () => { hs[e].setAttribute(q, v); return 'ok'; });
    } else {
      const n = h();
      if (hs[n].nodeType !== 9 && hs[n].nodeType !== 11) { k--; continue; }
      const s = pick(['a', 'b', 'x', 't']);
      run(`byid ${n} ${hex(s)}`, () => {
        const r = hs[n].getElementById(s);
        if (r === null) return 'ok null';
        const i = hs.indexOf(r);
        return i >= 0 ? 'ok ' + i : 'ok unnamed';
      });
    }
  }
  lines.push('end');
  expect.push('final');
  const seen = new Set();
  hs.forEach((n, i) => {
    if (n.parentNode === null && !seen.has(n)) {
      seen.add(n);
      expect.push('root ' + i);
      dump(win, n, expect);
    }
  });
  win.close();
}

const lines = [];
const expected = [];
const perScript = [];
for (let s = 0; s < Number(nScripts); s++) {
  const e0 = [];
  genScript(lines, e0);
  // l4dom prints a newline inside text data as a line break
  const e = e0.flatMap((l) => l.split('\n'));
  perScript.push(e);
  expected.push(...e);
}
const dir = mkdtempSync(join(tmpdir(), 'l4dom-'));
const file = join(dir, 'scripts.txt');
writeFileSync(file, lines.join('\n') + '\n');
const r = spawnSync(bin, ['ops', file], { encoding: 'utf8', maxBuffer: 1 << 30 });
if (r.status !== 0 && r.status !== 1) {
  console.error(`l4dom exited ${r.status}: ${r.stderr}`);
  process.exit(1);
}
const got = r.stdout.split('\n');
if (got[got.length - 1] === '') got.pop();
// split the Lean output into scripts
const gotScripts = [];
for (const l of got) {
  if (l === 'script') gotScripts.push([]);
  gotScripts[gotScripts.length - 1].push(l);
}
let agree = 0, disagree = 0, shown = 0;
const tally = {};
for (let i = 0; i < perScript.length; i++) {
  const e = perScript[i], g = gotScripts[i] || [];
  for (const l of e) if (l.startsWith('ok') || l.startsWith('err')) {
    const k = l.startsWith('err') ? l : 'ok';
    tally[k] = (tally[k] || 0) + 1;
  }
  if (e.length === g.length && e.every((l, j) => l === g[j])) { agree++; continue; }
  disagree++;
  if (shown++ < 3) {
    const j = e.findIndex((l, j) => l !== g[j]);
    console.log(`--- script ${i}: first difference at line ${j}`);
    console.log('jsdom: ' + JSON.stringify(e.slice(Math.max(0, j - 3), j + 4)));
    console.log('lean:  ' + JSON.stringify(g.slice(Math.max(0, j - 3), j + 4)));
  }
}
const ops = Object.values(tally).reduce((a, b) => a + b, 0);
console.log(`operation results (jsdom): ${Object.entries(tally).map(([k, v]) => `${k} ${v}`).join(', ')}`);
console.log(`dom differential (jsdom 30.1.3): ${agree} agree, ${disagree} disagree (out of ${agree + disagree} scripts, ${ops} operations)`);
process.exit(disagree === 0 && agree > 0 && r.status === 0 ? 0 : 1);
