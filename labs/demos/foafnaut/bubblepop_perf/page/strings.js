// String building and regular expressions: concatenation in a loop, template literals,
// split/join, replace with a regexp and a function, test, match, toLowerCase, padStart.
function run(n) {
  let html = "";
  for (let i = 0; i < n; i++) {
    html += `<li class="item ${i % 2 ? "odd" : "even"}" data-id="${i}">Item ${String(i).padStart(4, "0")}</li>`;
  }
  const parts = html.split("</li>");
  let acc = parts.length;
  const re = /data-id="(\d+)"/;
  for (let i = 0; i < parts.length; i += 7) { const m = re.exec(parts[i]); if (m) acc += Number(m[1]) % 13; }
  const words = "The quick brown fox jumps over the lazy dog while CSS and HTML parse".split(" ");
  let text = "";
  for (let i = 0; i < n; i++) text += words[i % words.length] + (i % 9 === 0 ? ". " : " ");
  const camel = text.slice(0, 4000).replace(/\s+(\w)/g, (_, c) => c.toUpperCase());
  acc += camel.length;
  acc += (text.match(/the/gi) || []).length;
  let n2 = 0;
  for (let i = 0; i < words.length * 50; i++) if (/^[A-Z]/.test(words[i % words.length])) n2++;
  acc += n2 + text.toLowerCase().indexOf("lazy") + parts.slice(0, 100).join("|").length;
  return acc;
}
RESULT = run(SCALE * 3000);
