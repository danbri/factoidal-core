import test from 'node:test';
import assert from 'node:assert/strict';
import {runPipeline, DEFAULTS} from '../../docs/web/hub/data-compositor/pipeline.mjs';

const core = await import(process.env.FACTOIDAL_COMPOSITOR_TEST_ENGINE || '@factoidal/core');
const ISSUE = 'https://github.com/danbri/factoidal/issues/1215';
const soh = String.fromCodePoint(1);
// The Turtle SOURCE contains six printable escape characters, not a raw SOH.
const turtle = DEFAULTS.turtle.replace('Mina Chen', String.raw`Mina\u0001Chen`);
const unchangedWorkflow = {turtle, query:DEFAULTS.query, stylesheet:DEFAULTS.stylesheet};

async function captureBoundary() {
  const calls=[], events=[];
  // Instrument only: delegate every evaluation/serialization to the real engine.
  const observed = {...core, async queryRaw(...args) {
    const xml = await core.queryRaw(...args);
    calls.push({args,xml});
    return xml;
  }};
  let failure;
  try { await runPipeline(observed,unchangedWorkflow,event=>events.push(event)); }
  catch(error) { failure=error; }
  return {calls,events,failure};
}

test('unchanged default SELECT and stylesheet produce HTML for the positive control', async()=>{
  assert.match(DEFAULTS.query,/\bSELECT\b/);
  assert.ok(turtle.includes(String.raw`\u0001`));
  assert.ok(!turtle.includes(soh));
  const result=await runPipeline(core,{query:DEFAULTS.query,stylesheet:DEFAULTS.stylesheet});
  assert.ok(result.rows.some(row=>row.name==='Mina Chen'));
  assert.match(result.html,/<html[ >]/i);
});

test('accepted Turtle literal crosses the default SELECT then fails XML projection before HTML', async t=>{
  const {calls,events,failure}=await captureBoundary();
  for(const id of ['turtle','csvw','merge','closure','graphs','query'])
    assert.ok(events.some(event=>event.id===id&&event.status==='done'),`${id} must really complete`);
  const query=events.find(event=>event.id==='query'&&event.status==='done');
  assert.ok(query.rows.some(row=>row.name===`Mina${soh}Chen`));
  assert.equal(calls.length,1,'one real filtered SPARQL execution');
  assert.equal(calls[0].args[1],DEFAULTS.query.replaceAll('{{MIN_SCORE}}',String(DEFAULTS.minScore)));
  assert.match(calls[0].xml,/^<\?xml version="1\.0"\?>/);
  assert.ok(calls[0].xml.includes(`Mina${soh}Chen`),'producer returned the unrepresentable code point');
  assert.equal(failure?.stageId,'filter');
  assert.match(failure.message,/FODC0002/);
  assert.match(failure.message,/invalid character in text content/);
  assert.ok(!events.some(event=>event.id==='html'));
  assert.equal(events.at(-1).status,'error');
  t.diagnostic(`${core.version}: accepted RDF → XML-character admission failure; ${ISSUE}`);
});

test(`xfail: XML producer must refuse unrepresentable values or deliver consumable XML (${ISSUE})`,async t=>{
  // Positive desired contract, with only the exact existing failure accepted as
  // XFAIL. An unrelated exception fails the test; a repair is an XPASS to flip.
  const {calls,failure}=await captureBoundary();
  if(calls.length===0) {
    assert.equal(failure?.stageId,'filter');
    assert.equal(failure?.code,'query.failed');
    assert.match(failure.message,/XML|represent|serializ|character/i);
    assert.fail(`unexpected pass: producer refuses unrepresentable XML; flip ${ISSUE}`);
  }
  assert.equal(calls.length,1);
  try { await core.xqueryEval('count(/*)',calls[0].xml); }
  catch(error) {
    assert.match(error.message,/FODC0002/);
    assert.match(error.message,/invalid character in text content/);
    t.diagnostic(`expected serializer-admission defect: ${error.message}`);
    return;
  }
  assert.fail(`unexpected pass: XML is consumable; flip ${ISSUE}`);
});
