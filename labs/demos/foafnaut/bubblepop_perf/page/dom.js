// A DOM-heavy loop: create elements, set attributes and classes, append, query, read style
// and attributes back, change text. Each iteration makes about a dozen DOM calls.
function run(n) {
  const root = document.getElementById("root");
  let acc = 0;
  for (let i = 0; i < n; i++) {
    const li = document.createElement("li");
    li.setAttribute("data-id", String(i));
    li.className = i % 2 ? "odd item" : "even item";
    li.textContent = "Item " + i;
    if (i % 3 === 0) li.classList.add("third");
    root.appendChild(li);
    acc += li.getAttribute("data-id").length;
    if (i % 10 === 0) acc += root.querySelectorAll("li.third").length;
    if (i % 25 === 0) { const s = getComputedStyle(li); acc += s.display.length; }
    acc += li.style.color.length;
    li.style.color = i % 2 ? "red" : "blue";
  }
  acc += root.children.length + root.firstElementChild.textContent.length;
  return acc;
}
RESULT = run(SCALE * 300);
