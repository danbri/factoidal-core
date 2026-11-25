// Extract comments and WDQS directives from SPARQL source text, with offsets.
//
// SPARQL comments run from '#' to end of line, except where '#' is inside an
// IRI reference (<...#...>) or a string literal ("C#", '''...#...'''). This is
// a lexical scan only: it needs no parser, and offsets are UTF-16 code-unit
// indices into the input string (JavaScript string indices).
//
// WDQS directives are comments of the form '#name:value' with name among
// DIRECTIVES; their value is kept raw, and parsed where the form is known.

const DIRECTIVES = new Set(['title', 'defaultView', 'TEMPLATE']);

// SPARQL 1.1 grammar [139] IRIREF: '<' ([^<>"{}|^`\]-[#x00-#x20])* '>'
const IRIREF_BODY = /^[^<>"{}|^`\\\u0000- ]*>/;

/**
 * @param {string} text SPARQL source
 * @returns {Array<{kind:'directive'|'comment', start:number, end:number,
 *   line:number, column:number, text:string, standalone:boolean,
 *   codeBefore:string, name?:string, value?:string, parsed?:object}>}
 *   start..end covers '#' to end of line (excluding the newline); line and
 *   column are 1-based; text excludes the leading '#'.
 */
export function extractComments(text) {
  const out = [];
  let i = 0, line = 1, lineStart = 0;
  const n = text.length;
  while (i < n) {
    const c = text[i];
    if (c === '\n') { i++; line++; lineStart = i; continue; }
    // String literals: long forms first.
    if (c === '"' || c === "'") {
      const long = text.startsWith(c.repeat(3), i);
      const delim = long ? c.repeat(3) : c;
      let j = i + delim.length;
      while (j < n) {
        if (text[j] === '\\') { j += 2; continue; }
        if (text.startsWith(delim, j)) { j += delim.length; break; }
        if (!long && text[j] === '\n') break; // unterminated short string: stop at EOL
        if (text[j] === '\n') { line++; lineStart = j + 1; }
        j++;
      }
      i = j;
      continue;
    }
    if (c === '<') {
      const m = IRIREF_BODY.exec(text.slice(i + 1, i + 1 + 4096));
      if (m) { i += 1 + m[0].length; continue; } // an IRI; otherwise '<' is an operator
      i++;
      continue;
    }
    if (c === '#') {
      let j = text.indexOf('\n', i);
      if (j < 0) j = n;
      let end = j;
      if (end > i && text[end - 1] === '\r') end--;
      const body = text.slice(i + 1, end);
      const codeBefore = text.slice(lineStart, i);
      const rec = {
        kind: 'comment', start: i, end, line, column: i - lineStart + 1,
        text: body, standalone: codeBefore.trim() === '', codeBefore: codeBefore.trimEnd(),
      };
      rec.content = looksLikeCode(body) ? 'code' : 'note';
      const d = /^([A-Za-z]+):(.*)$/s.exec(body);
      if (d && DIRECTIVES.has(d[1]) && rec.standalone) {
        rec.kind = 'directive';
        delete rec.content;
        rec.name = d[1];
        rec.value = d[2].trim();
        const parsed = parseDirective(rec.name, rec.value);
        if (parsed) rec.parsed = parsed;
      }
      out.push(rec);
      i = j;
      continue;
    }
    i++;
  }
  return out;
}

// A comment is classed 'code' (commented-out SPARQL) when it starts with a
// SPARQL keyword or brace, or when every token is SPARQL-shaped (variables,
// prefixed names, IRIs, literals, punctuation). Prose that merely mentions a
// variable ("?work is a poem") stays a 'note'. Heuristic: the class is a hint
// for presentation, never a claim about the query.
const CODE_START = /^\s*(OPTIONAL|MINUS|UNION|FILTER|BIND|SERVICE|VALUES|SELECT|WHERE|GROUP\s+BY|ORDER\s+BY|LIMIT)\b|^\s*[{}]/i;
const CODE_TOKEN = /^([?$]\w+|[A-Za-z][\w-]*:[\w-]*\*?|<[^>\s]*>|"[^"]*"(@[\w-]+|\^\^\S+)?|\d+|[{}.;,()[\]=!<>|/*+^]+|a)$/;
function looksLikeCode(body) {
  const t = body.trim();
  if (!t) return false;
  if (CODE_START.test(t)) return true;
  const toks = t.split(/\s+/);
  return toks.every(x => CODE_TOKEN.test(x)) && toks.some(x => /[:?$<]/.test(x));
}

/** defaultView:'Map{"hide":["?x"]}' -> {view:'Map', options:{hide:[...]}}. */
function parseDirective(name, value) {
  if (name !== 'defaultView') return null;
  const m = /^([A-Za-z]+)\s*(\{.*\})?\s*$/s.exec(value);
  if (!m) return { view: null, error: 'unrecognised defaultView form' };
  const r = { view: m[1] };
  if (m[2]) {
    try { r.options = JSON.parse(m[2]); } catch (e) { r.optionsRaw = m[2]; r.error = 'options are not valid JSON'; }
  }
  return r;
}
