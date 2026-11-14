import { query, calls } from "./count.js";
// Layout reads between rounds, as pages do to place things: each forces style and layout.
export function measure(list) {
  let h = 0;
  for (let k = 1; k <= 4; k++) {
    const li = query(list, `li:nth-child(${k * 7})`);
    if (li) { calls.n++; h += li.getBoundingClientRect().height; calls.n++; h += getComputedStyle(li).color.length; }
  }
  return h;
}
