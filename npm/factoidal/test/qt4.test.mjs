// XPath 4.0, XQuery 4.0 and XSLT 4.0 (formal/lean4/Wasm/Ops/Qt4.lean):
// xpath4Eval, xqueryEval, xslt4Transform. The engine evaluates and
// serializes; a QT4 error is a FactoidalError with `qtError`. The engine does
// no I/O: an external document, resource, module or stylesheet module fails
// with the specification's error code, and no request is made.
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  xpath4Eval, xqueryEval, xslt4Transform, xpathEval, xsltTransform, capabilities, FactoidalError,
} from '../index.mjs';
import * as browser from '../browser.js';

const XSL = 'http://www.w3.org/1999/XSL/Transform';
const ERR_NS = 'http://www.w3.org/2005/xqt-errors';

// Reject with a FactoidalError whose qtError has `code`.
async function rejectsWith(p, code) {
  await assert.rejects(p, (e) => {
    assert.ok(e instanceof FactoidalError, String(e));
    assert.equal(e.code, 'xml.failed');
    assert.equal(e.qtError?.code, code, e.message);
    return true;
  });
}

// Any fetch during the call fails the test.
async function withoutFetch(fn) {
  const saved = globalThis.fetch;
  let fetched = [];
  globalThis.fetch = async (u) => { fetched.push(String(u)); throw new Error('fetch called'); };
  try { await fn(); } finally { globalThis.fetch = saved; }
  assert.deepEqual(fetched, []);
}

test('capabilities: xpath4, xquery and xslt4', async () => {
  const c = await capabilities();
  assert.equal(c.xpath4, true);
  assert.equal(c.xquery, true);
  assert.equal(c.xslt4, true);
  assert.equal(typeof browser.xpath4Eval, 'function');
  assert.equal(typeof browser.xqueryEval, 'function');
  assert.equal(typeof browser.xslt4Transform, 'function');
});

test('xpath4Eval: arrow, simple map and typed items', async () => {
  const r = await xpath4Eval('<r><a>1</a><a>2</a><a>3</a></r>', '//a ! (. * 2) => sum()');
  assert.deepEqual(r, { count: 1, items: [{ type: 'xs:double', value: '12' }], adaptive: '12', xml: '12' });
  const s = await xpath4Eval('', '(1 to 3) => string-join("-")');
  assert.deepEqual(s.items, [{ type: 'xs:string', value: '"1-2-3"' }]);
  assert.equal(s.xml, '1-2-3');
});

test('xpath4Eval: nodes, maps and arrays', async () => {
  const n = await xpath4Eval('<r><a x="1"/><b/></r>', '/r/*');
  assert.equal(n.count, 2);
  assert.deepEqual(n.items.map((i) => i.type), ['element()', 'element()']);
  assert.equal(n.xml, '<a x="1"/><b/>');
  const m = await xpath4Eval('', 'map { "k": [1, "two"] }');
  assert.equal(m.items[0].type, 'map(*)');
  assert.equal(m.adaptive, '{"k":[1,"two"]}');
  assert.equal(m.xml, null);
  const a = await xpath4Eval('', 'array { 1, 2 } ?* => count()');
  assert.equal(a.adaptive, '2');
});

test('xpath4Eval: XPath 1.0 xpathEval is unchanged beside it', async () => {
  const r = await xpathEval('<r><a>1</a><a>2</a></r>', 'count(/r/a)');
  assert.equal(r.resultType, 'number');
  assert.equal(String(r.value), '2');
  // `=>` is not XPath 1.0
  await assert.rejects(xpathEval('<r/>', '1 => string()'));
});

test('xpath4Eval: errors carry the QT4 error code', async () => {
  await rejectsWith(xpath4Eval('', '1 +'), 'XPST0003');
  await rejectsWith(xpath4Eval('', '1 div 0'), 'FOAR0001');
  await rejectsWith(xpath4Eval('', 'no-such-function()'), 'XPST0017');
  await rejectsWith(xpath4Eval('<r', '1'), 'FODC0002');
  await assert.rejects(xpath4Eval('', '1 +'), (e) => {
    assert.equal(e.qtError.namespace, ERR_NS);
    assert.match(e.message, /err:XPST0003/);
    return true;
  });
  await assert.rejects(xpath4Eval(1, '1'), TypeError);
});

test('xpath4Eval: no document, resource or file is read or fetched', async () => {
  await withoutFetch(async () => {
    await rejectsWith(xpath4Eval('', "doc('https://example.org/a.xml')"), 'FODC0002');
    await rejectsWith(xpath4Eval('', "doc('file:///etc/passwd')"), 'FODC0002');
    await rejectsWith(xpath4Eval('', "unparsed-text('file:///etc/passwd')"), 'FOUT1170');
    await rejectsWith(xpath4Eval('', "json-doc('https://example.org/a.json')"), 'FOUT1170');
    const r = await xpath4Eval('', "doc-available('https://example.org/a.xml')");
    assert.equal(r.xml, 'false');
    await assert.rejects(
      xpath4Eval('', "Q{http://expath.org/ns/file}read-text('/etc/passwd')"),
      (e) => e.qtError.code === 'io-error' && e.qtError.namespace === 'http://expath.org/ns/file');
  });
});

test('xqueryEval: FLWOR, constructors and the context document', async () => {
  const r = await xqueryEval(
    'for $a in //a order by xs:integer($a) descending return <b n="{$a}"/>',
    '<r><a>1</a><a>3</a><a>2</a></r>');
  assert.equal(r.count, 3);
  assert.equal(r.xml, '<b n="3"/><b n="2"/><b n="1"/>');
  const f = await xqueryEval(
    'declare function local:fact($n) { if ($n le 1) then 1 else $n * local:fact($n - 1) }; local:fact(20)');
  assert.deepEqual(f.items, [{ type: 'xs:integer', value: '2432902008176640000' }]);
  const g = await xqueryEval('for $x in 1 to 6 group by $k := $x mod 2 order by $k return sum($x)', '');
  assert.equal(g.adaptive, '12\n9');
});

test('xqueryEval: errors; a recursion 300 calls deep', async () => {
  await rejectsWith(xqueryEval('for $x in'), 'XPST0003');
  await rejectsWith(xqueryEval('declare variable $x external; $x'), 'XPDY0002');
  const d = await xqueryEval(
    'declare function local:f($n) { if ($n le 0) then 0 else 1 + local:f($n - 1) }; local:f(300)');
  assert.equal(d.xml, '300');
  const caught = await xqueryEval('try { error(xs:QName("err:FOER0000")) } catch * { $err:code }');
  assert.equal(caught.xml, 'err:FOER0000');
});

test('xqueryEval: import module of an external module is refused, no fetch', async () => {
  await withoutFetch(async () => {
    await rejectsWith(xqueryEval(
      "import module namespace m = 'urn:x-m' at 'https://example.org/m.xq'; m:f()"), 'XQST0059');
    await rejectsWith(xqueryEval("doc('https://example.org/a.xml')"), 'FODC0002');
  });
});

test('xslt4Transform: text value templates and the output definition', async () => {
  const ss = `<xsl:stylesheet version="4.0" xmlns:xsl="${XSL}" expand-text="yes">
    <xsl:output method="text"/>
    <xsl:template match="/">{count(//a)} items: {string-join(//a, ",")}</xsl:template>
  </xsl:stylesheet>`;
  const r = await xslt4Transform(ss, '<r><a>x</a><a>y</a></r>');
  assert.deepEqual(r, { output: '2 items: x,y', method: 'text', secondary: [], messages: [] });
});

test('xslt4Transform: xml output, result documents and messages', async () => {
  const ss = `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}">
    <xsl:template match="/">
      <xsl:result-document href="side.xml"><side/></xsl:result-document>
      <xsl:message>hello</xsl:message>
      <out><xsl:apply-templates select="//a"/></out>
    </xsl:template>
    <xsl:template match="a"><b><xsl:value-of select=". * 2"/></b></xsl:template>
  </xsl:stylesheet>`;
  const r = await xslt4Transform(ss, '<r><a>1</a><a>2</a></r>');
  assert.equal(r.method, 'xml');
  assert.equal(r.output, '<?xml version="1.0" encoding="UTF-8"?><out><b>2</b><b>4</b></out>');
  assert.deepEqual(r.secondary, [{ href: 'side.xml', output: '<?xml version="1.0" encoding="UTF-8"?><side/>' }]);
  assert.deepEqual(r.messages, ['hello']);
  // the XSLT 1.0 function beside it is unchanged
  const one = await xsltTransform(
    `<xsl:stylesheet version="1.0" xmlns:xsl="${XSL}"><xsl:template match="/"><o><xsl:value-of select="count(//a)"/></o></xsl:template></xsl:stylesheet>`,
    '<r><a/></r>');
  assert.equal(typeof one, 'string');
  assert.match(one, /<o>1<\/o>/);
});

test('xslt4Transform: no source, initial template', async () => {
  const r = await xslt4Transform(
    `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:template name="xsl:initial-template"><a/></xsl:template></xsl:stylesheet>`, '');
  assert.equal(r.output, '<?xml version="1.0" encoding="UTF-8"?><a/>');
});

test('xslt4Transform: errors carry the QT4 error code', async () => {
  await rejectsWith(xslt4Transform(
    `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:template match="/"><xsl:value-of select="1 +"/></xsl:template></xsl:stylesheet>`,
    '<r/>'), 'XPST0003');
  await rejectsWith(xslt4Transform('<xsl:stylesheet', '<r/>'), 'XTSE0165');
  await rejectsWith(xslt4Transform(
    `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:template match="/"><xsl:sequence select="error(xs:QName('err:XTMM9000'))"/></xsl:template></xsl:stylesheet>`,
    '<r/>'), 'XTMM9000');
});

test('xslt4Transform: xsl:import, xsl:include and fn:doc are refused, no fetch', async () => {
  await withoutFetch(async () => {
    await rejectsWith(xslt4Transform(
      `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:import href="https://example.org/a.xsl"/></xsl:stylesheet>`,
      '<r/>'), 'XTSE0165');
    await rejectsWith(xslt4Transform(
      `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:include href="b.xsl"/></xsl:stylesheet>`,
      '<r/>'), 'XTSE0165');
    await rejectsWith(xslt4Transform(
      `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:template match="/"><xsl:copy-of select="doc('https://example.org/x.xml')"/></xsl:template></xsl:stylesheet>`,
      '<r/>'), 'FODC0002');
  });
});

// Expected failures (CLAUDE.md, "A stated shortfall is a failing test plus an
// open issue"). The XPath 4.0, XQuery 4.0 and XSLT 4.0 engines recurse one
// stack frame per item in places (tools/lean-tail-recursion-allow.txt, PENDING
// https://github.com/danbri/factoidal/issues/1110). In the wasm module the host's
// call stack ends first: the call rejects with "Maximum call stack size
// exceeded" (code op.failed), and the engine answers the next call. `xfail`
// runs the check; if it PASSES, the case FAILS, so the flip to an assertion
// cannot be forgotten.
const STACK_ISSUE = 'https://github.com/danbri/factoidal/issues/1110';
function xfail(name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false;
    try { await fn(t); } catch (error) { failed = true; t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`); }
    assert.ok(failed, `unexpected pass: ${name} now works: flip this xfail to an assertion and close ${issueUrl}`);
  });
}
const siblings = (n) => '<r>' + '<a>1</a>'.repeat(n) + '</r>';

xfail('xpath4Eval over a document of 20,000 sibling elements', STACK_ISSUE, async () => {
  const r = await xpath4Eval(siblings(20000), 'count(//a)');
  assert.equal(r.xml, '20000');
});

xfail('xslt4Transform over a document of 20,000 sibling elements', STACK_ISSUE, async () => {
  const r = await xslt4Transform(
    `<xsl:stylesheet version="3.0" xmlns:xsl="${XSL}"><xsl:output method="text"/><xsl:template match="/"><xsl:value-of select="count(//a)"/></xsl:template></xsl:stylesheet>`,
    siblings(20000));
  assert.equal(r.output, '20000');
});

// Which limit ends a deep recursion first depends on the host's stack: the
// engine's fuel (FOER0000) on a large stack (CI's Node), the host stack
// (op.failed, "Maximum call stack size exceeded") on a small one. Both are
// accepted; nothing else is (https://github.com/danbri/factoidal/issues/1110).
test(`xqueryEval: a recursion deeper than the fuel ends in FOER0000 or a host stack overflow, nothing else (${STACK_ISSUE})`, async (t) => {
  let error;
  try {
    await xqueryEval('declare function local:f($n) { if ($n le 0) then 0 else 1 + local:f($n - 1) }; local:f(100000)');
  } catch (e) { error = e; }
  assert.ok(error, 'a recursion 100,000 calls deep must not succeed under the fuel limit');
  const fuel = error.qtError?.code === 'FOER0000';
  const stack = /Maximum call stack size exceeded/.test(String(error.message));
  t.diagnostic(fuel ? 'ended by the fuel: FOER0000' : 'ended by the host stack');
  assert.ok(fuel || stack, `unexpected error: ${String(error.message).slice(0, 160)}`);
  const r = await xpath4Eval('', '1 + 1');
  assert.equal(r.xml, '2');
});

xfail('xpath4Eval: an expression nested 1,000 parentheses deep', STACK_ISSUE, async () => {
  const r = await xpath4Eval('', '('.repeat(1000) + '1' + ')'.repeat(1000));
  assert.equal(r.xml, '1');
});

test('after a deep call, overflowing or not, the engine answers the next call', async () => {
  await xpath4Eval(siblings(20000), 'count(//a)').catch(() => {});
  const r = await xpath4Eval('', '1 + 1');
  assert.equal(r.xml, '2');
});
