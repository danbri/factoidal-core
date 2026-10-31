import test from 'node:test';
import assert from 'node:assert/strict';
import { runPipeline, DEFAULTS } from '../../docs/web/hub/data-compositor/pipeline.mjs';

// Set this to the installed published 0.27.0 entry to audit the live page.
// The default also checks the current package without pretending it is that pin.
const core = await import(process.env.FACTOIDAL_COMPOSITOR_TEST_ENGINE || '@factoidal/core');
const stylesheet = body => `<xsl:stylesheet version="3.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:output method="html"/><xsl:template match="/">${body}</xsl:template></xsl:stylesheet>`;

const expectedMessages = {
  'turtle': /unterminated string literal/,
  'csvw': /metadataJson is not a decodable CSVW metadata document/,
  'filter': /Minimum score must be a number from 0 to 100/,
  'missing numeric socket': /must contain the \{\{MIN_SCORE\}\} socket/,
  'invalid SPARQL': /query does not parse/,
  'ASK does not supply the SELECT-row wire': /bindings.map is not a function/,
  'malformed stylesheet': /XTSE0165/,
  'non-HTML output method': /Expected XSLT HTML output; got text/,
  'terminating XSLT message': /XTMM9000/,
};
const failures = [
  ['malformed Turtle', {turtle:'<urn:person> <urn:name> "unterminated'}, 'turtle'],
  ['malformed CSVW metadata', {metadata:'{'}, 'csvw'],
  ['missing numeric socket', {query:'SELECT * WHERE { ?s ?p ?o }'}, 'query'],
  ['invalid SPARQL', {query:'SELECT WHERE { {{MIN_SCORE}} }'}, 'query'],
  ['ASK does not supply the SELECT-row wire', {query:'ASK {} # {{MIN_SCORE}}'}, 'query'],
  ...['', '-1', '101', 'NaN', 'Infinity'].map(minScore => [`invalid minimum ${JSON.stringify(minScore)}`, {minScore}, 'filter']),
  ['malformed stylesheet', {stylesheet:'<xsl:stylesheet'}, 'xslt'],
  ['non-HTML output method', {stylesheet:DEFAULTS.stylesheet.replace('method="html"','method="text"')}, 'xslt'],
  ['terminating XSLT message', {stylesheet:stylesheet('<xsl:message terminate="yes">stop</xsl:message>')}, 'xslt'],
];
for (const [name, inputs, stageId] of failures) test(`no HTML completion: ${name}`, async t => {
  const events=[];
  await assert.rejects(runPipeline(core, inputs, e=>events.push(e)), e=>{
    assert.equal(e.stageId,stageId);
    assert.match(e.message,expectedMessages[name] || expectedMessages[stageId]);
    t.diagnostic(`${core.version}: ${e.message}`);
    return true;
  });
  assert.equal(events.at(-1).status,'error');
  assert.equal(events.at(-1).id,stageId);
  assert.ok(!events.some(e=>e.id==='html'));
});

test('zero selected rows still produce an HTML document', async()=>{
  const result=await runPipeline(core,{minScore:'100'});
  assert.equal(result.rows.length,0);
  assert.match(result.html,/<html[ >]/i);
  assert.match(result.html,/0 artists in this cut/);
  assert.equal(result.proved,false);
});

test('absent domain/subclass rules empty the roster but do not block HTML', async()=>{
  const turtle=DEFAULTS.turtle.split('\n').filter(line=>!line.includes(' rdfs:domain ')&&!line.includes(' rdfs:subClassOf ')).join('\n');
  const result=await runPipeline(core,{turtle});
  assert.equal(result.rows.length,0);
  assert.match(result.html,/<html[ >]/i);
});

test('successful HTML-method transform can emit an empty string', async()=>{
  const result=await runPipeline(core,{stylesheet:stylesheet('')});
  assert.equal(result.html,'');
  assert.equal(result.stages.at(-1).id,'report');
});
