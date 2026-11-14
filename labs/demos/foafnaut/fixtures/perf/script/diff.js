import { add, remove } from "./count.js";
import { row, update } from "./view.js";
// A keyed reconcile, as list libraries do: keep, update, move, insert and remove by id.
export function reconcile(parent, nodes, olds, items) {
  const next = new Map();
  const byId = new Map(olds.map((o) => [o.id, o]));
  const wanted = new Set(items.map((i) => i.id));
  for (const [id, li] of nodes) if (!wanted.has(id)) remove(li);
  let cursor = parent.firstElementChild;
  for (const it of items) {
    let li = nodes.get(it.id);
    if (li) { update(li, byId.get(it.id), it); if (li !== cursor) add(parent, li, cursor); else cursor = cursor.nextElementSibling; }
    else { li = row(it); add(parent, li, cursor); }
    next.set(it.id, li);
  }
  return next;
}
