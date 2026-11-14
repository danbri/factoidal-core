import { initial, step } from "./state.js";
import { reconcile } from "./diff.js";
import { measure } from "./measure.js";
import { later } from "./schedule.js";
import { status } from "./status.js";
import { plural } from "./format.js";
import { calls } from "./count.js";
const list = document.getElementById("list");
let items = initial(), nodes = reconcile(list, new Map(), [], items), round = 0, read = 0;
read += measure(list);
function tick() {
  const next = step(items);
  nodes = reconcile(list, nodes, items, next);
  items = next;
  read += measure(list);
  status(items.length, ++round);
  if (round < 24) later(tick);
  else console.log("perf-fixture-done " + JSON.stringify({ domCalls: calls.n, items: items.length, rounds: round, read: read > 0, label: plural(round, "round") }));
}
later(tick);
