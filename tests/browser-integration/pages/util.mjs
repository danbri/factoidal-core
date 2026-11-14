// A second module of the graph: the page's module imports it.
export function listItem(text) {
  const li = document.createElement('li');
  li.textContent = text;
  return li;
}
export const moduleValue = 42;
