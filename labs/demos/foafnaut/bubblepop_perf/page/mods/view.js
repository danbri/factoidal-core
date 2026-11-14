import lookup, { table } from "./data.js";
import { sum, Counter } from "./util.js";
import * as U from "./util.js";
export function render(n) { const c = new Counter(); let s = 0; for (let i = 0; i < n; i++) { s += lookup(i) + U.sq(i & 3); c.inc(); } return s + sum(table) + c.n; }
