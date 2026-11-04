import { loadLayoutPolicy } from "./policy_engine.mjs";
import { loadFoaf } from "./foafnaut_engine.ts";
import { loadFoafTransport } from "./foafnaut_transport.mjs";

function assert(value: unknown, message: string): asserts value { if (!value) throw new Error(message); }
function throws(f: () => unknown) { let caught = false; try { f(); } catch { caught = true; } assert(caught, "expected refusal"); }
const fixture = await Deno.readTextFile(new URL("./foaf/fixtures/people.ttl", import.meta.url));

Deno.test("configuration and model nesting are refused before recursive JSON parsing", async () => {
  const call = await loadFoafTransport(), nested = '['.repeat(4096) + ']'.repeat(4096);
  throws(() => call('foafnaut_init_policy', ['string','number','number','string'], [fixture,1000,700,nested]));
  const valid = call('foafnaut_init', ['string','number','number'], [fixture,1000,700]);
  const config = JSON.stringify(valid.layout.policy);
  throws(() => call('foafnaut_export_svg', ['string','string'], [nested,config]));
  throws(() => call('foafnaut_export_svg', ['string','string'], [valid.model,nested]));
  assert(call('foafnaut_export_svg', ['string','string'], [valid.model,config]).checked, "refusal poisoned the engine");
});

Deno.test("one Lean policy API bounds tuning and retains the application's ceiling", async () => {
  const engine = await loadLayoutPolicy(), defaults = engine.defaults();
  assert(defaults.configuration.overlapBps === 500, "default is not 5%");
  const application = { ...defaults.application, maxOverlapBps: 500, maxCheckHz: 16 };
  const policy = engine.bind(application, defaults.configuration);
  application.maxOverlapBps = 700; // mutation of caller input cannot weaken the bound
  throws(() => policy.retune({ overlapBps: 700, checkHz: 12 }));
  throws(() => policy.retune({ overlapBps: 500, checkHz: 24 }));
  for (const overlapBps of [0, 299, 701, 10000]) throws(() => engine.bind(defaults.application, { overlapBps, checkHz: 12 }));
  for (const checkHz of [0, 1, 11, 25, 120]) throws(() => engine.bind(defaults.application, { overlapBps: 500, checkHz }));
  assert(policy.retune({ overlapBps: 300, checkHz: 16 }).application.maxOverlapBps === 500, "application bound changed");
  const viewport = [0,0,200,100];
  assert(policy.check(viewport, [[0,0,100,100],[95,0,195,100]]).accepted, "5% boundary rejected");
  assert(!policy.check(viewport, [[0,0,100,100],[94,0,194,100]]).accepted, "6% overlap admitted");
  assert(!policy.check(viewport, [null]).accepted, "unknown footprint admitted");
});

Deno.test("Lean-generated SVG and native drawing share admission and authoritative geometry", async () => {
  const engine = await loadFoaf(fixture), frame = engine.initialize();
  const svg = engine.svg(frame.model), picture = engine.checkedSnapshot(frame.model);
  assert(svg.checked && svg.layout.enforced && svg.layout.withinBudget, "SVG lacks admission evidence");
  assert(svg.svg.startsWith('<svg') && svg.svg.includes('<rect'), "missing SVG geometry");
  assert(JSON.stringify(picture.data) === JSON.stringify(frame.data), "checked native geometry changed");
  const policy = await loadLayoutPolicy(), selected = svg.layout.policy;
  const report = policy.bind(selected.application, selected.configuration).check(
    [0,0,svg.width,svg.height], svg.layout.nodes.map(n => n.bounds));
  assert(report.accepted, "portable API disagrees with derived geometry");
  const model = JSON.parse(frame.model);
  model.positions[1] = model.positions[0];
  throws(() => engine.svg(JSON.stringify(model)));
  throws(() => engine.checkedSnapshot(JSON.stringify(model)));
  const tight = { application: { ...selected.application, maxOverlapBps: 500 }, configuration: { overlapBps: 300, checkHz: 24 } };
  const tuned = engine.initialize(1000,700,tight);
  assert(tuned.layout.thresholdBasisPoints === 300 && tuned.layout.targetCheckHz === 24, "Lean ignored tuning");
  throws(() => engine.initialize(1000,700,{ ...tight, configuration: { overlapBps: 700, checkHz: 24 } }));
  const forged = JSON.parse(tuned.model);
  forged.policy.application.maxOverlapBps = 700;
  forged.policy.configuration.overlapBps = 700;
  throws(() => engine.svg(JSON.stringify(forged)));
  throws(() => engine.checkedSnapshot(JSON.stringify(forged)));
  // Even an allowed retune requires an explicit initialization decision.
  forged.policy = JSON.parse(tuned.model).policy;
  forged.policy.configuration.overlapBps = 500;
  throws(() => engine.svg(JSON.stringify(forged)));
  throws(() => engine.checkedSnapshot(JSON.stringify(forged)));
  throws(() => engine.svg(frame.model)); // previous configuration no longer current
  assert(engine.svg(tuned.model).checked, "caller mutation changed retained application policy");
});
