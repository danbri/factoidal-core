import { create, text, attr, add, cls } from "./count.js";
// One row: li > span.title + span.score + button
export function row(it) {
  const li = create("li"); attr(li, "data-id", String(it.id)); cls(li, "row", true); cls(li, "done", it.done);
  const t = create("span"); cls(t, "title", true); text(t, it.title); add(li, t);
  const s = create("span"); cls(s, "score", true); text(s, String(it.score)); add(li, s);
  const b = create("button"); attr(b, "type", "button"); text(b, it.done ? "Undo" : "Done"); add(li, b);
  return li;
}
export function update(li, old, it) {
  if (old.title !== it.title) text(li.children[0], it.title);
  if (old.score !== it.score) text(li.children[1], String(it.score));
  if (old.done !== it.done) { cls(li, "done", it.done); text(li.children[2], it.done ? "Undo" : "Done"); }
}
