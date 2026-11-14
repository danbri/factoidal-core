// Every DOM call of the fixture goes through these, so the number of calls is known.
export const calls = { n: 0 };
export const create = (tag) => { calls.n++; return document.createElement(tag); };
export const text = (el, t) => { calls.n++; el.textContent = t; };
export const attr = (el, k, v) => { calls.n++; el.setAttribute(k, v); };
export const add = (parent, child, before) => { calls.n++; return before ? parent.insertBefore(child, before) : parent.appendChild(child); };
export const remove = (el) => { calls.n++; el.remove(); };
export const cls = (el, c, on) => { calls.n++; el.classList.toggle(c, on); };
export const query = (root, sel) => { calls.n++; return root.querySelector(sel); };
