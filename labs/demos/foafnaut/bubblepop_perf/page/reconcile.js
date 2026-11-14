// A framework-style reconcile loop: render a virtual tree from state, diff it against the
// previous one by key, and apply the changes to the DOM (create, update text and attributes,
// remove, reorder), over many state updates.
function h(tag, props, children) { return { tag, props: props || {}, children: children || [], el: null }; }
function view(state) {
  return h("ul", { class: "list" }, state.items.map(it =>
    h("li", { key: it.id, class: it.done ? "done" : "todo", "data-n": String(it.n) }, [String(it.label + " " + it.n)])));
}
function create(v) {
  if (typeof v === "string") return document.createTextNode(v);
  const el = document.createElement(v.tag);
  for (const k in v.props) if (k !== "key") el.setAttribute(k, v.props[k]);
  for (const c of v.children) el.appendChild(create(c));
  v.el = el;
  return el;
}
function patch(parent, old, v) {
  const el = (v.el = old.el);
  for (const k in v.props) if (k !== "key" && old.props[k] !== v.props[k]) el.setAttribute(k, v.props[k]);
  const byKey = new Map();
  for (const c of old.children) byKey.set(c.props.key, c);
  let ops = 0;
  v.children.forEach((c, i) => {
    const o = byKey.get(c.props.key);
    if (o) {
      byKey.delete(c.props.key);
      c.el = o.el;
      for (const k in c.props) if (k !== "key" && o.props[k] !== c.props[k]) { c.el.setAttribute(k, c.props[k]); ops++; }
      if (o.children[0] !== c.children[0]) { c.el.firstChild.data = c.children[0]; ops++; }
      if (el.childNodes[i] !== c.el) { el.insertBefore(c.el, el.childNodes[i] || null); ops++; }
    } else { el.insertBefore(create(c), el.childNodes[i] || null); ops++; }
  });
  byKey.forEach(o => { el.removeChild(o.el); ops++; });
  return ops;
}
function run(n, rounds) {
  const state = { items: [] };
  for (let i = 0; i < n; i++) state.items.push({ id: i, label: "task", n: 0, done: false });
  let tree = view(state);
  document.getElementById("root").appendChild(create(tree));
  let ops = 0;
  for (let r = 0; r < rounds; r++) {
    for (let i = r % 7; i < state.items.length; i += 7) state.items[i] = { ...state.items[i], n: state.items[i].n + 1, done: !state.items[i].done };
    if (r % 5 === 4) state.items.push({ id: n + r, label: "new", n: 0, done: false });
    if (r % 5 === 2) state.items.splice(r % state.items.length, 1);
    const next = view(state);
    ops += patch(tree.el.parentNode, tree, next);
    tree = next;
  }
  return ops + tree.el.childNodes.length;
}
RESULT = run(SCALE * 100, 30);
