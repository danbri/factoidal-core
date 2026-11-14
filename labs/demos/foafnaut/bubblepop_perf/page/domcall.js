// The cost of one call across the script/engine boundary, per DOM operation: the same loop
// with the operation (OP) and with a plain property read in its place (OP = "base").
const root = document.getElementById("root");
const el = document.createElement("div");
el.setAttribute("title", "t");
root.appendChild(el);
for (let i = 0; i < 50; i++) { const c = document.createElement("span"); c.className = "c" + (i % 5); root.appendChild(c); }
const plain = { title: "t" };
let acc = 0;
const N = SCALE * 2000;
switch (OP) {
  case "base": for (let i = 0; i < N; i++) acc += plain.title.length; break;
  case "getAttribute": for (let i = 0; i < N; i++) acc += el.getAttribute("title").length; break;
  case "setAttribute": for (let i = 0; i < N; i++) { el.setAttribute("title", "t"); acc++; } break;
  case "createElement": for (let i = 0; i < N; i++) { document.createElement("p"); acc++; } break;
  case "appendChild": for (let i = 0; i < N; i++) { el.appendChild(document.createTextNode("x")); acc++; } break;
  case "querySelector": for (let i = 0; i < N; i++) acc += root.querySelector(".c3") ? 1 : 0; break;
  case "styleRead": for (let i = 0; i < N; i++) acc += el.style.color.length + 1; break;
  case "textContent": for (let i = 0; i < N; i++) { el.textContent = "x"; acc++; } break;
  case "classList": for (let i = 0; i < N; i++) { el.classList.toggle("on"); acc++; } break;
  case "parentNode": for (let i = 0; i < N; i++) acc += el.parentNode === root ? 1 : 0; break;
}
RESULT = acc;
