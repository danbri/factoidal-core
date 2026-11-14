import { rand } from "./rand.js";
// The items: id, title, score, done. Each round changes some, drops some, adds some and reorders.
const next = rand(0x5C121);
let serial = 0;
const words = ["ka", "lo", "mi", "ren", "tas", "vo", "qui", "bel", "dor", "fen"];
const title = () => words[next() % 10] + words[next() % 10] + " " + words[next() % 10];
export function initial() {
  const items = [];
  for (let i = 0; i < 400; i++) items.push({ id: serial++, title: title(), score: next() % 1000, done: false });
  return items;
}
export function step(items) {
  const out = [];
  for (const it of items) {
    const k = next() % 20;
    if (k === 0) continue;                                       // dropped
    if (k < 5) out.push({ ...it, score: next() % 1000 });      // changed score
    else if (k === 5) out.push({ ...it, done: !it.done });      // toggled
    else if (k === 6) out.push({ ...it, title: title() });     // retitled
    else out.push(it);
  }
  for (let i = 0; i < 15; i++) out.splice(next() % (out.length + 1), 0, { id: serial++, title: title(), score: next() % 1000, done: false });
  if (next() % 2) out.sort((a, b) => b.score - a.score || a.id - b.id);
  return out;
}
