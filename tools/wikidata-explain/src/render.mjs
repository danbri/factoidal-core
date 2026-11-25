// Render a record as L1 "precise" text (SPEC §7). Every line comes from the
// record; nothing is added here except headings and joining words.

const SEV_ORDER = { changes_answer: 0, scope: 1, display: 2 };

export function renderL1(rec, depth = 0) {
  const ind = '  '.repeat(depth);
  const L = [];
  const push = (s) => L.push(ind + s);
  if (!depth) {
    push(rec.id);
    push(`Original title: ${rec.title}`);
    if (rec.title_directive && rec.title_directive !== rec.title) push(`Query's #title: ${rec.title_directive}`);
    push('');
  }
  if (rec.row?.text) push(rec.row.text);
  if (rec.columns.length) {
    push('Columns:');
    for (const c of rec.columns) {
      let t = c.text;
      if (!t) t = c.never_bound ? 'never has a value' : (c.may_be_blank ? 'may be blank' : 'always has a value');
      push(`  ?${c.var}: ${t}`);
    }
  }
  if (rec.required.length) { push('Conditions (all must hold):'); for (const r of rec.required) push(`  - ${r.text}  [${r.rule}]`); }
  if (rec.filters.length) for (const f of rec.filters) push(`  - ${f.text}  [${f.rule}]`);
  if (rec.optional.length) { push('Optional:'); for (const o of rec.optional) push(`  - ${o.text}  [${o.rule}]`); }
  if (rec.excluded.length) { push('Excluded:'); for (const x of rec.excluded) push(`  - ${x.text}  [${x.rule}]`); }
  if (rec.grouping) {
    const g = rec.grouping;
    push(`Grouping: ${g.keys.length ? 'by ' + g.keys.map(k => '?' + k).join(', ') : 'all rows form one group'}.`);
  }
  if (rec.ordering.length) push(`Order: ${rec.ordering.map(o => `${o.key} ${o.dir === 'desc' ? 'descending' : 'ascending'}`).join(', then ')}.`);
  if (rec.distinct) push('Rows are deduplicated (DISTINCT).');
  if (rec.limit != null) push(`Limit: ${rec.limit} rows${rec.offset ? `, skipping the first ${rec.offset}` : ''}.`);
  rec.subqueries.forEach((s, i) => { push(`Subquery ${i + 1}:`); L.push(...renderL1(s, depth + 1).split('\n')); });
  if (!depth) {
    const cs = [...rec.caveats].sort((a, b) => SEV_ORDER[a.severity] - SEV_ORDER[b.severity]);
    if (cs.length) { push('Caveats:'); for (const c of cs) push(`  * [${c.severity}] ${c.precise}  (${c.rule}${c.in_subquery ? `, subquery ${c.in_subquery}` : ''})`); }
    if (rec.labels.length) push(`Labels: ${rec.labels.map(l => `?${l.column ?? l.subject + 'Label'} from ${l.label_languages.join(' → ')} → ID`).join('; ')}.`);
    if (rec.display) push(`Display: ${rec.display.view}${rec.display.options ? ' ' + JSON.stringify(rec.display.options) : ''}.  [R-VIEW]`);
    if (rec.author_comments.length) { push('Author notes:'); for (const c of rec.author_comments) push(`  "${c.text}"${c.content === 'code' ? ' (commented-out code)' : ''}${c.after ? `  — after: ${c.after.trim()}` : ''}`); }
    if (rec.translation_notes.length) push(`Translation: ${rec.translation_notes.map(t => t.text || t.rule).join('; ')}.`);
    if (rec.unexplained.length) push(`UNEXPLAINED: ${rec.unexplained.map(u => u.what).join(', ')}`);
  }
  let text = L.join('\n');
  // First mention of each item carries its English description (label cache).
  if (!depth && rec.glossary) {
    const done = new Set();
    text = text.replace(/\((Q\d+)\)/g, (m, id) => {
      if (done.has(id) || !rec.glossary[id]) return m;
      done.add(id);
      return `(${id} — ${rec.glossary[id]})`;
    });
  }
  return text;
}
