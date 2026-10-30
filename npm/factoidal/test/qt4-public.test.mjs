// Public XML adapters: real engine evaluation, with JS limited to marshalling.
// CI uses the shipped WASM. Local low-disk verification may explicitly select
// the native driver of the identical dispatch ABI: FACTOIDAL_QT4_NATIVE=/path.
import test, { after } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import * as published from '../index.mjs';
import { createApi } from '../api.mjs';
import { runQt4, Qt4UsageError } from '../bin/qt4.mjs';

const directory = mkdtempSync(join(tmpdir(), 'factoidal-qt4-public-'));
after(() => rmSync(directory, { recursive: true, force: true }));
let counter = 0;
const native = process.env.FACTOIDAL_QT4_NATIVE;
const cli = fileURLToPath(new URL('../bin/factoidal.mjs', import.meta.url));
const nativeEngine = native ? {
  call(op, args = []) {
    const path = join(directory, `args-${counter++}.json`);
    writeFileSync(path, JSON.stringify(args));
    const result = spawnSync(native, ['call', op, path], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
    assert.equal(result.status, 0, `native dispatch process failed: ${result.stderr}`);
    const value = JSON.parse(result.stdout);
    if (!value.ok) throw Object.assign(new Error(value.error), { envelope: value });
    return value;
  },
} : null;
const f = nativeEngine ? createApi(nativeEngine, { engineName: 'lean4-native-dispatch-test' }) : published;
const engine = () => nativeEngine ?? published.loadEngine();
const XSL = 'http://www.w3.org/1999/XSL/Transform';
const assertSheet = (condition) => `<xsl:stylesheet version='3.0' xmlns:xsl='${XSL}'><xsl:template name='main'><out>ok<xsl:assert test='${condition}'/></out></xsl:template></xsl:stylesheet>`;
const assertQuery = (condition = 'false()', option = '') => `transform(map{'stylesheet-text':"${assertSheet(condition)}",'initial-template':QName('','main')${option}})?output ! string()`;
const textSheet = `<xsl:stylesheet version='3.0' xmlns:xsl='${XSL}'><xsl:output method='text'/><xsl:template match='/'><xsl:result-document href='side.xml'><side/></xsl:result-document><xsl:message>hello</xsl:message><xsl:value-of select='count(//a)'/></xsl:template></xsl:stylesheet>`;

async function command(name, positional, options = {}) {
  const stdout = [], stderr = [];
  const code = await runQt4(name, positional, options, {
    loadEngine: engine, readText: (p) => readFileSync(p, 'utf8'),
    out: (s) => stdout.push(s), err: (s) => stderr.push(s),
  });
  return { code, stdout: stdout.join('\n'), stderr: stderr.join('\n') };
}

test('public node descriptors are bound, tested and explicit serialized-result wires', async () => {
  const stages = new Map((await f.stages()).map((stage) => [stage.name, stage]));
  for (const [name, setting, wireOut] of [['xpath4Eval', 'expression', 'Serialized XDM result'],
      ['xqueryEval', 'query', 'Serialized XDM result'], ['xslt4Transform', 'stylesheet', 'XSLT result']]) {
    const stage = stages.get(name);
    assert.ok(stage, `missing ${name}; stale/missing engine is a failure, not a skip`);
    assert.equal(stage.bound, true); assert.equal(stage.status, 'tested');
    assert.equal(stage.contract, null); assert.equal(stage.wireIn, 'String'); assert.equal(stage.wireOut, wireOut);
    await assert.rejects(f.node(name), /must be a string/);
    await assert.rejects(f.node(name, { [setting]: 1 }), /must be a string/);
    await assert.rejects(f.node(name, { [setting]: 'x', fetch: true }), /unknown setting/);
  }
});

test('XPath/XQuery nodes preserve atomic, map and element result envelopes and evidence', async () => {
  for (const [name, settings, xml, expected] of [
    ['xpath4Eval', { expression: 'count(//a)' }, '<r><a/><a/></r>', '2'],
    ['xqueryEval', { query: 'map{"k":[1,2]}' }, '', null],
    ['xqueryEval', { query: '<out>{count(//a)}</out>' }, '<r><a/></r>', '<out>1</out>'],
  ]) {
    const node = await f.node(name, settings);
    const ordinary = await f.run(node, xml);
    assert.equal(ordinary.proved, false);
    assert.equal(ordinary.evidence.at(-1).checked, false);
    const result = await f.run(node, xml, { unchecked: true });
    assert.equal(result.graph.xml, expected);
    assert.equal(result.evidence.at(-1).status, 'tested');
    assert.equal(result.proved, false);
    assert.equal(result.evidence.at(-1).unchecked, true);
    const direct = name === 'xpath4Eval' ? await f.xpath4Eval(xml, settings.expression) : await f.xqueryEval(settings.query, xml);
    assert.deepEqual(result.graph, direct);
  }
});

test('XSLT node keeps text, secondary results and messages in a non-XML envelope', async () => {
  const node = await f.node('xslt4Transform', { stylesheet: textSheet });
  const result = await f.run(node, '<r><a/><a/></r>', { unchecked: true });
  assert.deepEqual(result.graph, await f.xslt4Transform(textSheet, '<r><a/><a/></r>'));
  assert.equal(result.graph.output, '2'); assert.equal(result.graph.method, 'text');
  assert.equal(result.graph.secondary.length, 1); assert.deepEqual(result.graph.messages, ['hello']);
  const xp = await f.node('xpath4Eval', { expression: '1' });
  const pipeline = f.pipe(node, xp);
  assert.equal(pipeline.check.wellTyped, false);
  await assert.rejects(f.run(pipeline, '<r/>'), /unchecked|wire|proved|contract/i);
});

test('inline fn:transform assertion defaults and explicit toggle reach API, CLI and nodes', async () => {
  const contextStyle = `<xsl:stylesheet version='3.0' xmlns:xsl='${XSL}'><xsl:template match='/'><out><xsl:value-of select='count(//a)'/></out></xsl:template></xsl:stylesheet>`;
  const contextQuery = `transform(map{'stylesheet-text':"${contextStyle}",'source-node':.})?output ! string()`;
  assert.equal((await f.xpath4Eval('<r><a/><a/></r>', contextQuery)).xml, '2');
  const skippedBody = assertQuery().replace("<xsl:assert test='false()'/>",
    "<xsl:assert test='false()'><xsl:sequence select='1 idiv 0'/></xsl:assert>");
  for (const query of [assertQuery(), assertQuery('1 idiv 0 = 1', ",'enable-assertions':false()"), skippedBody]) {
    assert.equal((await f.xpath4Eval('', query)).xml, 'ok');
    assert.equal((await f.xqueryEval(query)).xml, 'ok');
    const node = await f.node('xpath4Eval', { expression: query });
    assert.equal((await f.run(node, '', { unchecked: true })).graph.xml, 'ok');
    const r = await command('xpath4', [query]);
    assert.equal(r.code, 0, r.stderr); assert.equal(JSON.parse(r.stdout).xml, 'ok');
  }
  const enabled = assertQuery('false()', ",'enable-assertions':true()");
  await assert.rejects(f.xpath4Eval('', enabled), (e) => e.qtError?.code === 'XTMM9001');
  const node = await f.node('xqueryEval', { query: enabled });
  await assert.rejects(f.run(node, '', { unchecked: true }), (e) => e.qtError?.code === 'XTMM9001');
  const r = await command('xquery', [enabled]);
  assert.equal(r.code, 1); assert.equal(JSON.parse(r.stderr).qtError.code, 'XTMM9001');
  await assert.rejects(f.xslt4Transform(assertSheet('false()').replace("name='main'", "match='/'"), '<r/>'),
    (e) => e.qtError?.code === 'XTMM9001');
});

test('public element-to-map explicit casts and pure resource refusal retain QT error codes', async () => {
  const query = "element-to-map(<a>bad</a>, {'plan':{'a':{'layout':'simple','type':'boolean'}}})";
  await assert.rejects(f.xqueryEval(query), (e) => e.qtError?.code === 'FOJS0010');
  const savedFetch = globalThis.fetch, fetched = [];
  globalThis.fetch = async (url) => { fetched.push(url); throw new Error('unexpected resource fetch'); };
  try {
    await assert.rejects(f.xpath4Eval('', "doc('https://example.org/not-fetched.xml')"), (e) => e.qtError?.code === 'FODC0002');
    await assert.rejects(f.xpath4Eval('', "transform(map{'stylesheet-location':'https://example.org/not-fetched.xsl'})"),
      (e) => e.qtError?.code === 'FODC0002');
  } finally { globalThis.fetch = savedFetch; }
  assert.deepEqual(fetched, []);
});

test('CLI files and display modes preserve the existing engine result', async () => {
  const xml = join(directory, 'input.xml'), sheet = join(directory, 'sheet.xsl'), query = join(directory, 'query.xq');
  writeFileSync(xml, '<r><a/><a/></r>'); writeFileSync(sheet, textSheet); writeFileSync(query, 'count(//a)');
  const xp = await command('xpath4', ['count(//a)'], { input: xml });
  assert.equal(xp.code, 0, xp.stderr); assert.equal(JSON.parse(xp.stdout).xml, '2');
  const xq = await command('xquery', [], { file: query, input: xml, format: 'adaptive' });
  assert.equal(xq.code, 0, xq.stderr); assert.equal(xq.stdout, '2');
  const xslt = await command('xslt4', [sheet], { input: xml, format: 'output' });
  assert.equal(xslt.code, 0, xslt.stderr); assert.equal(xslt.stdout, '2');
  const unavailable = await command('xpath4', ['map{"k":1}'], { format: 'xml' });
  assert.equal(unavailable.code, 1); assert.match(unavailable.stderr, /no xml serialization/);
  const bad = await command('xpath4', ['1 +']);
  assert.equal(bad.code, 1); assert.equal(JSON.parse(bad.stderr).qtError.code, 'XPST0003');
});

test('CLI usage rejects ambiguous sources and unknown options before loading an engine', async () => {
  await assert.rejects(command('xquery', ['1'], { query: '2' }), Qt4UsageError);
  await assert.rejects(command('xpath4', ['1'], { fetch: true }), Qt4UsageError);
  await assert.rejects(command('xslt4', ['file.xsl'], { format: 'xml' }), Qt4UsageError);
  for (const name of ['xpath4', 'xquery', 'xslt4']) {
    const help = spawnSync(process.execPath, [cli, name, '--help'], { encoding: 'utf8' });
    assert.equal(help.status, 0); assert.match(help.stdout, new RegExp(`factoidal ${name}`));
    const invalid = spawnSync(process.execPath, [cli, name, '--unexpected'], { encoding: 'utf8' });
    assert.equal(invalid.status, 2); assert.match(invalid.stderr, /unknown option/);
  }
});

test('a backend without QT4 operations refuses instead of falling back to another evaluator', async () => {
  const unavailable = createApi({ call(op) {
    assert.equal(op, 'ops', 'an unavailable operation must not be sent to the backend');
    return { ok: true, ops: [], engine: 'full', abiVersion: 'test-unavailable' };
  } });
  for (const invoke of [() => unavailable.xpath4Eval('', '1'), () => unavailable.xqueryEval('1'),
      () => unavailable.xslt4Transform(textSheet, '<r/>')]) {
    await assert.rejects(invoke(), (e) => e.code === 'op.unknown');
  }
});

test('CLI normalizes the raw engine Error.envelope without losing the QT error QName', async () => {
  const qtError = { code: 'XTMM9001', namespace: 'http://www.w3.org/2005/xqt-errors', message: 'assertion failed' };
  const envelope = { ok: false, code: 'xml.failed', error: 'err:XTMM9001: assertion failed', qtError };
  const stderr = [];
  const code = await runQt4('xpath4', ['1'], {}, {
    loadEngine: async () => ({ call() { throw Object.assign(new Error('raw engine failure'), { envelope }); } }),
    readText: () => { throw new Error('no file read expected'); },
    out: () => { throw new Error('a refusal must produce no success output'); }, err: (s) => stderr.push(s),
  });
  assert.equal(code, 1);
  assert.deepEqual(JSON.parse(stderr.join('\n')), {
    error: envelope.error, code: 'xml.failed', qtError,
  });
});

// Native-driver mode measures the exact command helper plus real help/usage
// processes above. A true operational CLI process needs shipped WASM assets;
// the default CI path always defines and runs this additional test. No success
// is fabricated for that different backend when native mode is selected.
if (!native) test('shipped WASM actual CLI process returns success JSON and QT error/nonzero', () => {
  const xml = join(directory, 'cli-input.xml');
  writeFileSync(xml, '<r><a/><a/></r>');
  const success = spawnSync(process.execPath, [cli, 'xpath4', 'count(//a)', '--input', xml], { encoding: 'utf8' });
  assert.equal(success.status, 0, success.stderr);
  assert.equal(JSON.parse(success.stdout).xml, '2');
  const failure = spawnSync(process.execPath, [cli, 'xquery', '1 +'], { encoding: 'utf8' });
  assert.equal(failure.status, 1, failure.stderr);
  assert.equal(JSON.parse(failure.stderr.trim().split('\n').at(-1)).qtError.code, 'XPST0003');
});
