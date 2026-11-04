import { loadFoafLive } from "./foafnaut_live.ts";
import { loadFoafTransport } from "./foafnaut_transport.mjs";

function assert(value: unknown, message: string): asserts value { if (!value) throw new Error(message); }
function equal(a: unknown, b: unknown) { assert(JSON.stringify(a) === JSON.stringify(b), `${JSON.stringify(a)} != ${JSON.stringify(b)}`); }
function throws(f: () => unknown) { let caught = false; try { f(); } catch { caught = true; } assert(caught, "expected refusal"); }
const fixture = await Deno.readTextFile(new URL("./foaf/fixtures/people.ttl", import.meta.url));
const single = '@prefix f: <http://xmlns.com/foaf/0.1/> . <https://example.org/alice> a f:Person; f:name "Alice" .';

Deno.test("live WASM needs display acknowledgment and retains approved geometry on rejection", async () => {
  const live = await loadFoafLive(fixture);
  try {
    const first = live.initialize(1000,700,undefined,1000);
    assert(first.layout.enforced && first.presentation.available, "initial layout was not admitted");
    const ignored = live.step({kind:2,a:500,b:350},1001);
    assert(!ignored.dragging && ignored.selection === 0, "unsubmitted frame accepted a pointer target");
    live.acknowledge(first.presentation.renderToken);
    live.step({kind:2,a:500,b:350},1002);
    const captured = live.present(1084);
    assert(captured.selection === 1 && captured.dragging, "visible center node was not captured");
    live.acknowledge(captured.presentation.renderToken);
    const rejected = live.step({kind:3,a:500,b:110},1168);
    equal(rejected.presentation.status,"rejected");
    equal(rejected.data,captured.data);
    equal(JSON.parse(rejected.model).positions[0],JSON.parse(captured.model).positions[0]);
    assert(rejected.layout.withinBudget && rejected.layout.enforced, "unapproved draw data escaped");
    live.step({kind:4,a:0,b:0},1169);
    live.step({kind:2,a:500,b:350},1170);
    const recovered = live.present(1252);
    equal(recovered.presentation.status,"accepted");
    equal(JSON.parse(recovered.model).positions[0],JSON.parse(first.model).positions[0]);
  } finally { live.dispose(); }
});

Deno.test("accepted but unsubmitted moves and stale acknowledgments cannot change picking", async () => {
  const live = await loadFoafLive(single);
  try {
    const first = live.initialize(1000,700,undefined,1000);
    live.acknowledge(first.presentation.renderToken);
    live.step({kind:2,a:500,b:350},1001);
    const captured = live.present(1084);
    live.acknowledge(captured.presentation.renderToken);
    const moved = live.step({kind:3,a:700,b:450},1168);
    assert(moved.presentation.available && moved.presentation.status === "accepted", "test move must be admitted");
    assert(moved.presentation.renderToken !== captured.presentation.renderToken, "changed render offer reused token");
    live.acknowledge(captured.presentation.renderToken); // stale, must not acknowledge the move
    live.step({kind:2,a:500,b:350},1169); // pointer still sees the old center
    const recovered = live.present(1252);
    equal(recovered.selection,1);
    equal(JSON.parse(recovered.model).positions[0],JSON.parse(first.model).positions[0]);
    live.acknowledge(recovered.presentation.renderToken);
    const next = live.step({kind:3,a:700,b:450},1336);
    live.acknowledge(next.presentation.renderToken);
    live.step({kind:4,a:0,b:0},1337);
    live.step({kind:2,a:500,b:350},1338);
    equal(live.present(1420).selection,0);
  } finally { live.dispose(); }
});

Deno.test("resize invalidates geometry and rollback cannot advance its admission clock", async () => {
  const live = await loadFoafLive(single);
  try {
    const first = live.initialize(1000,700,undefined,1000);
    live.acknowledge(first.presentation.renderToken);
    const resized = live.step({kind:1,a:700,b:500},1001);
    assert(!resized.presentation.available, "resize retained a scene for the old viewport");
    equal(resized.layout.nodes,[]);
    equal(resized.facts.visiblePeople,0);
    equal(resized.width,700); equal(resized.height,500);
    assert(resized.commands.includes("render"), "invalidated surface was not cleared");
    equal(resized.presentation.lastCheckMs,1000);
    const rollback = live.present(999);
    equal(rollback.presentation.status,"clockWentBack");
    equal(rollback.presentation.lastCheckMs,1000);
    assert(!rollback.presentation.available, "clock rollback restored stale geometry");
    equal(live.present(1083).presentation.status,"deferred");
    const accepted = live.present(1084);
    assert(accepted.presentation.available && accepted.presentation.status === "accepted", "resized layout did not recover");
    equal(accepted.width,700); equal(accepted.height,500);
  } finally { live.dispose(); }
});

Deno.test("live policy state is opaque and clipboard effects survive paused presentation", async () => {
  const live = await loadFoafLive(single);
  try {
    const first = live.initialize(1000,700,undefined,1000);
    live.acknowledge(first.presentation.renderToken);
    first.model = '{}'; first.layout.policy.configuration.overlapBps = 10000;
    equal(live.svg().layout.thresholdBasisPoints,500);
    live.step({kind:5,a:49,b:0},1001); // pause physics
    live.step({kind:5,a:37,b:2},1002); // Cmd-L
    live.insertText("https://example.org/é",1003);
    live.step({kind:5,a:0,b:2},1004); // Cmd-A
    const copy = live.step({kind:5,a:8,b:2},1005);
    equal(copy.clipboardWrite,"https://example.org/é");
    assert(!copy.animating, "pause was lost");
    const shown = live.present(1084);
    equal(JSON.parse(shown.model).address,"https://example.org/é");
    assert(shown.presentation.available, "paused application stopped admission retries");
    assert(shown.clipboardWrite === undefined, "clipboard effect repeated on retry");
    throws(() => live.insertText("x\0y",1085));
    assert(live.present(1168).presentation.available, "bad transport input destroyed the session");
    live.step({kind:6,a:0,b:0},1169);
    const closed = live.present(10000);
    assert(closed.closed && closed.commands.length === 0, "closed session kept producing work");
  } finally { live.dispose(); }
});

Deno.test("raw live ABI retains valid state after malformed time and refuses use after disposal", async () => {
  const call = await loadFoafTransport();
  const first = call('foafnaut_live_start',['string','number','number','string','string'],[single,1000,700,'','1000']);
  throws(() => call('foafnaut_live_tick',['string'],['-1']));
  const again = call('foafnaut_live_tick',['string'],['1084']);
  equal(again.layout.policy,first.layout.policy);
  assert(again.presentation.available, "malformed transport poisoned retained controller");
  call('foafnaut_live_dispose',[],[]);
  throws(() => call('foafnaut_live_tick',['string'],['1168']));
});

Deno.test("live initialization cannot replace a session or reuse its render tokens", async () => {
  const call = await loadFoafTransport();
  const start = (policy: string) => call('foafnaut_live_start',
    ['string','number','number','string','string'],[single,1000,700,policy,'1000']);
  const first = start('');
  try {
    throws(() => start('{"configuration":{"overlapBps":10000}}'));
    const retained = call('foafnaut_live_tick',['string'],['1084']);
    equal(retained.data, first.data);
    equal(retained.presentation.renderToken, first.presentation.renderToken);
    throws(() => start(''));
    call('foafnaut_live_acknowledge',['string'],[String(first.presentation.renderToken)]);
    const selected = call('foafnaut_live_event',['number','number','number','string'],[2,500,350,'1168']);
    equal(selected.selection,1);
  } finally { call('foafnaut_live_dispose',[],[]); }
  throws(() => start(''));
});
