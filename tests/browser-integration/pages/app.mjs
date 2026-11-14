// The module script of integrated.html: a module graph of two, a fetch of JSON, and a DOM
// update from the answer. It reports to the classic script's test (moduleDone).
import { listItem, moduleValue } from './util.mjs';

const response = await fetch('data.json');
const data = await response.json();
const list = document.getElementById('list');
for (const text of data.items) list.appendChild(listItem(text));
globalThis.moduleDone({ imported: moduleValue, items: data.items });
