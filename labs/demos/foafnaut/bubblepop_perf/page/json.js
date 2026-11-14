// JSON: stringify and parse of a mid-sized nested document, as data-driven pages do with
// their embedded state and API answers.
function make(n) {
  const rows = [];
  for (let i = 0; i < n; i++)
    rows.push({ id: i, name: "row " + i, ok: i % 3 === 0, score: i * 1.5, tags: ["a", "b" + (i % 4)], nested: { depth: 1, at: [i, i + 1] } });
  return { version: 3, title: "results", rows };
}
function run(n) {
  const doc = make(n);
  let acc = 0;
  for (let r = 0; r < 4; r++) {
    const text = JSON.stringify(doc);
    acc += text.length;
    const back = JSON.parse(text);
    acc += back.rows.length + back.rows[n - 1].nested.at[1];
  }
  acc += JSON.stringify(doc.rows.slice(0, 50), null, 2).length;
  return acc;
}
RESULT = run(SCALE * 1000);
