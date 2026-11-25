// The Hub's accessibility mirror (docs/web/hub/foafnaut/accessibility-mirror.mjs): the hidden
// elements a screen reader reads follow the engine's tree in order and nesting, carry only what
// the engine gave (role, aria- attributes, text, box), keep an element across updates, and turn
// an activation into a press at the centre of its box. A small stand-in for the DOM: no browser.
import { createMirror } from "../../../docs/web/hub/foafnaut/accessibility-mirror.mjs";

type Listener = (event: { target: Node }) => void;
class Node {
  parentNode: Node | null = null;
  children: Node[] = [];
  ownerDocument!: Doc;
  get firstChild(): Node | null { return this.children[0] ?? null; }
  get nextSibling(): Node | null {
    const all = this.parentNode?.children ?? [];
    return all[all.indexOf(this) + 1] ?? null;
  }
  remove() {
    const all = this.parentNode?.children;
    if (all) all.splice(all.indexOf(this), 1);
    this.parentNode = null;
  }
  insertBefore(node: Node, before: Node | null) {
    node.remove();
    this.ownerDocument.moves++;
    const at = before ? this.children.indexOf(before) : this.children.length;
    if (at < 0) throw new Error("insertBefore: not a child");
    this.children.splice(at, 0, node);
    node.parentNode = this;
    return node;
  }
}
class Text extends Node { constructor(public data: string) { super(); } }
class Element extends Node {
  attributes = new Map<string, string>();
  style: Record<string, string> = {};
  listeners: Listener[] = [];
  constructor(public tagName: string) { super(); }
  getAttribute(name: string) { return this.attributes.get(name) ?? null; }
  setAttribute(name: string, value: string) { this.ownerDocument.writes++; this.attributes.set(name, value); }
  removeAttribute(name: string) { this.attributes.delete(name); }
  addEventListener(_type: string, listener: Listener) { this.listeners.push(listener); }
}
class Doc {
  moves = 0;
  writes = 0;
  createElement(tag: string) { const el = new Element(tag); el.ownerDocument = this; return el; }
  createTextNode(data: string) { const text = new Text(data); text.ownerDocument = this; return text; }
}
// The tree as text: tag, attributes in name order, box, own text, children.
const show = (node: Node): string => {
  if (node instanceof Text) return JSON.stringify(node.data);
  const el = node as Element;
  const attrs = [...el.attributes].sort().map(([k, v]) => ` ${k}=${JSON.stringify(v)}`).join("");
  const box = el.style.position === "fixed" ? ` @${parseFloat(el.style.left)},${parseFloat(el.style.top)},${parseFloat(el.style.width)},${parseFloat(el.style.height)}` : "";
  return `<${el.tagName}${attrs}${box}>${el.children.map(show).join("")}</${el.tagName}>`;
};
const equal = (got: unknown, want: unknown, what: string) => {
  if (JSON.stringify(got) !== JSON.stringify(want)) throw new Error(`${what}: ${JSON.stringify(got)}, not ${JSON.stringify(want)}`);
};
const page = (button: string, extra: unknown[] = []) => ({ serial: 3, top: 100, scroll: 40, nodes: [
  { id: 1, depth: 0, role: "document", box: [0, 0, 1600, 2000], web: { role: "document", aria: { label: "Title" } } },
  { id: 5, depth: 1, role: "heading", box: [20, 60, 400, 80], web: { role: "heading", aria: { label: "Hi", level: "2" } } },
  { id: 6, depth: 2, role: "text", box: [20, 60, 400, 80], web: { text: "Hi" } },
  { id: 9, depth: 1, role: "button", focusable: true, box: [20, 200, 200, 40], web: { role: "button", aria: { label: button } } },
  { id: 12, depth: 1, role: "textbox", focusable: true, box: [20, 300, 200, 40], web: { role: "textbox", aria: { label: "Name" }, text: "Ada" } },
  ...extra,
] });

Deno.test("the mirror follows the engine's tree: order, nesting, attributes, text and boxes", () => {
  const doc = new Doc(), root = doc.createElement("div");
  const mirror = createMirror(root, () => {});
  equal(mirror.apply(page("Save"), 2), 5, "elements");
  equal(show(root), '<div><div aria-label="Title" role="document" @0,30,800,1000>' +
    '<div aria-label="Hi" aria-level="2" role="heading" @10,60,200,40><span>"Hi"</span></div>' +
    '<div aria-label="Save" role="button" tabindex="-1" @10,130,100,20></div>' +
    '<div aria-label="Name" role="textbox" tabindex="-1" @10,180,100,20>"Ada"</div></div></div>', "the mirror");
});

Deno.test("an update changes only what changed and keeps the elements", () => {
  const doc = new Doc(), root = doc.createElement("div");
  const mirror = createMirror(root, () => {});
  mirror.apply(page("Save"), 2);
  const button = (root.children[0] as Element).children[1];
  doc.moves = 0; doc.writes = 0;
  mirror.apply(page("Save"), 2);
  equal([doc.moves, doc.writes], [0, 0], "the same tree again moved or wrote something");
  mirror.apply(page("Saved"), 2);
  equal([doc.moves, doc.writes], [0, 1], "one label changed");
  if ((root.children[0] as Element).children[1] !== button) throw new Error("the button's element was replaced");
  // A node before the button and one that is gone: one insertion, and the heading's subtree leaves.
  const next = page("Saved", []);
  next.nodes.splice(1, 2, { id: 30, depth: 1, role: "link", box: [0, 0, 10, 10], web: { role: "link", aria: { label: "Skip" } } } as never);
  doc.moves = 0;
  equal(mirror.apply(next, 2), 4, "elements after the change");
  equal(doc.moves, 1, "insertions");
  equal(show(root).includes("heading") || show(root).includes('"Hi"'), false, "the dropped heading is still there");
  if ((root.children[0] as Element).children[1] !== button) throw new Error("the button's element was replaced by the reorder");
  mirror.clear();
  equal([mirror.size, root.children.length], [0, 0], "clear");
});

Deno.test("a scroll moves the elements, and an activation is a press at the centre of the box", () => {
  const doc = new Doc(), root = doc.createElement("div"), presses: number[][] = [];
  const mirror = createMirror(root, (x: number, y: number) => presses.push([x, y]));
  mirror.apply(page("Save"), 2);
  mirror.move(100, 140, 2);
  equal(((root.children[0] as Element).children[1] as Element).style.top, "80px", "the button after a scroll of 100 frame pixels");
  // A node of the chrome is in window pixels and does not scroll.
  mirror.apply({ top: 100, scroll: 500, nodes: [{ id: 1073741825, depth: 0, role: "button", fixed: true, box: [8, 20, 56, 56], web: { role: "button", aria: { label: "Back" } } },
    ...page("Save").nodes] }, 2);
  equal((root.children[0] as Element).style.top, "10px", "the chrome's button");
  root.listeners[0]({ target: root.children[0] });
  equal(presses.splice(0), [[36, 48]], "a press on the chrome's button");
  mirror.apply(page("Save"), 2);mirror.move(100, 140, 2);
  const heading = (root.children[0] as Element).children[0] as Element;
  // A click on the heading's text is a press on the nearest element with a box: the heading.
  for (const target of [(root.children[0] as Element).children[1], heading.children[0]]) root.listeners[0]({ target });
  equal(presses, [[120, 180], [220, 60]], "presses in frame pixels of the window");
});

Deno.test("nothing but role, tabindex, aria- names of letters and text reaches the host page", () => {
  const doc = new Doc(), root = doc.createElement("div");
  const mirror = createMirror(root, () => {});
  mirror.apply({ top: 0, scroll: 0, nodes: [
    { id: 2, depth: 0, role: "x", box: [0, 0, "9", 1], onclick: "alert(1)",
      web: { role: "button", href: "javascript:alert(1)", aria: { "label": "ok", "x onclick": "alert(1)", "Label": "no", "live": 4, "": "e" },
        text: "<img src=x onerror=alert(1)>" } },
    { id: 2, depth: 0, role: "button", web: { role: "link" } },
    { id: 2.5, depth: 0 }, null, "node", { depth: 0 },
    { id: 3, depth: 7, role: "text", web: { text: "deep" } },
  ] }, 0);
  equal(show(root), '<div><div aria-label="ok" role="button">"<img src=x onerror=alert(1)>"<span>"deep"</span></div></div>', "the mirror of a hostile tree");
});
