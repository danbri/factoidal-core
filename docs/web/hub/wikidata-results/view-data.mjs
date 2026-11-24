// View directives and term mappings follow the WDQS Result Views documentation.
// https://www.wikidata.org/wiki/Wikidata:SPARQL_query_service/Wikidata_Query_Help/Result_Views
export const viewNames = Object.freeze({
  Table: 'Table',
  Graph: 'Graph',
  GraphBuilder: 'Graph builder',
  Map: 'Map',
  ImageGrid: 'Image grid',
  Timeline: 'Timeline',
  Tree: 'Tree',
  TreeMap: 'Tree map',
  Dimensions: 'Dimensions',
  BarChart: 'Bar chart',
  LineChart: 'Line chart',
  ScatterChart: 'Scatter chart',
  AreaChart: 'Area chart',
  BubbleChart: 'Bubble chart',
});

const viewIds = new Map(Object.keys(viewNames).map(id => [id.toLowerCase(), id]));
const queryTokens = /"""(?:\\[\s\S]|(?!""")[\s\S])*"""|'''(?:\\[\s\S]|(?!''')[\s\S])*'''|"(?:\\.|[^"\\\r\n])*"|'(?:\\.|[^'\\\r\n])*'|<[^<>"{}|^\x60\\\s]*>|#[^\r\n]*/g;

const editorTokens = new RegExp(queryTokens.source +
  String.raw`|[?$][\p{L}\p{N}_][\p{L}\p{N}\p{M}_]*|\b(?:SELECT|ASK|CONSTRUCT|DESCRIBE|PREFIX|BASE|WHERE|FROM|NAMED|OPTIONAL|FILTER|UNION|MINUS|SERVICE|SILENT|BIND|VALUES|UNDEF|GROUP|HAVING|ORDER|LIMIT|OFFSET|BY|ASC|DESC|AS|DISTINCT|REDUCED|GRAPH|EXISTS|NOT|WITH|INCLUDE)\b|\b[A-Za-z_][\w-]*:[\w-]+`, 'giu');

export function highlightTokens(query) {
  return Array.from(query.matchAll(editorTokens), match => {
    const [text] = match;
    let kind = 'keyword';
    if (text.startsWith('#')) kind = 'comment';
    else if (/^["']/.test(text)) kind = 'string';
    else if (/^[?$]/.test(text)) kind = 'variable';
    else if (text.startsWith('<') || text.includes(':')) kind = 'iri';
    return { at: match.index, text, kind };
  });
}

export function viewDirectives(query) {
  const options = new Map();
  let defaultView = 'Table';
  let unknownView = '';
  let hasDefaultView = false;
  let title = '';
  let invalidOptions = false;
  for (const [token] of query.matchAll(queryTokens)) {
    if (!token.startsWith('#')) continue;
    const heading = /^#\s*title\s*:\s*(.*)$/i.exec(token);
    if (heading) {
      title = heading[1].trim();
      continue;
    }
    const directive = /^#\s*(defaultView|view)\s*:\s*([a-z][\w-]*)\s*(.*)$/i.exec(token);
    if (!directive) continue;
    const [, kind, name, json] = directive;
    const id = viewIds.get(name.toLowerCase());
    if (kind.toLowerCase() === 'defaultview') {
      hasDefaultView = true;
      defaultView = id ?? 'Table';
      unknownView = id ? '' : name;
    }
    if (!json || !id) continue;
    try {
      const parsed = JSON.parse(json);
      if (!parsed || Array.isArray(parsed) || typeof parsed !== 'object') {
        invalidOptions = true;
        continue;
      }
      options.set(id, { ...options.get(id), ...parsed });
    } catch {
      invalidOptions = true;
    }
  }
  return { title, defaultView, hasDefaultView, unknownView, options, invalidOptions };
}

export function optionVars(value) {
  return (Array.isArray(value) ? value : [value]).filter(name => typeof name === 'string')
    .map(name => name.replace(/^[?$]/, ''));
}

export function displayedVars(vars, options) {
  const hidden = new Set(optionVars(options.hide));
  return vars.filter(name => !hidden.has(name));
}

const xsd = 'http://www.w3.org/2001/XMLSchema#';
const numbers = new Set(['integer', 'decimal', 'float', 'double', 'byte', 'short', 'int', 'long',
  'positiveInteger', 'nonPositiveInteger', 'negativeInteger', 'nonNegativeInteger',
  'unsignedByte', 'unsignedShort', 'unsignedInt', 'unsignedLong'].map(type => xsd + type));

export function numberValue(term) {
  if (!numbers.has(term?.datatype) || !/^[+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?$/i.test(term.value)) return null;
  const value = Number(term.value);
  return Number.isFinite(value) ? value : null;
}

export function dateValue(term) {
  if (term?.datatype !== xsd + 'dateTime' && term?.datatype !== xsd + 'date') return null;
  const value = Date.parse(term.value);
  return Number.isFinite(value) ? value : null;
}

export const isLabel = term => (term?.type === 'literal' || term?.type === 'typed-literal') &&
  (!term.datatype || term.datatype === xsd + 'string' || Boolean(term['xml:lang']));
export const isEntity = term => term?.type === 'uri' &&
  /^https?:\/\/www\.wikidata\.org\/entity\/[QPL]\d+(?:-[FS]\d+)?$/.test(term.value);
export const termLabel = term => isEntity(term) ? term.value.split('/').at(-1) : String(term?.value ?? '');
export const hexColour = (term, fallback) =>
  /^[0-9a-f]{6}$/i.test(term?.value ?? '') ? '#' + term.value : fallback;

export function commonsImage(term) {
  if (term?.type !== 'uri') return null;
  try {
    const url = new URL(term.value);
    if (!['http:', 'https:'].includes(url.protocol) || url.port || url.username || url.password) return null;
    if (url.hostname === 'commons.wikimedia.org' && /^\/wiki\/Special:FilePath\//i.test(url.pathname)) {
      // The thumbnail parameter limits transfer for galleries and node thumbnails.
      url.searchParams.set('width', '480');
    } else if (url.hostname !== 'upload.wikimedia.org' || !url.pathname.startsWith('/wikipedia/commons/')) {
      return null;
    }
    url.protocol = 'https:';
    return url.href;
  } catch {
    return null;
  }
}

export function labelFor(row, name, vars) {
  const explicit = row[name + 'Label'];
  if (isLabel(explicit)) return explicit.value;
  const next = vars.slice(vars.indexOf(name) + 1).find(key => isEntity(row[key]) || isLabel(row[key]));
  return isLabel(row[next]) && next !== 'edgeLabel' ? row[next].value : termLabel(row[name]);
}

export function displayNodes(row, vars, columns) {
  const keys = columns ?? vars.filter(name => isEntity(row[name]));
  return keys.filter(name => row[name]).map(name => {
    const term = row[name];
    const after = vars.slice(vars.indexOf(name) + 1);
    const end = after.findIndex(key => isEntity(row[key]));
    const adjacent = end < 0 ? after : after.slice(0, end);
    const image = [name + 'Image', ...adjacent].map(key => commonsImage(row[key])).find(Boolean);
    const colour = [name + 'Rgb', ...adjacent.filter(key => key === 'rgb')]
      .map(key => hexColour(row[key], null)).find(Boolean);
    const size = [name + 'Size', ...adjacent].map(key => numberValue(row[key])).find(value => value > 0);
    return {
      id: isEntity(term) ? termLabel(term) : JSON.stringify(term),
      label: labelFor(row, name, vars),
      url: isEntity(term) ? term.value.replace(/^http:/, 'https:') : null,
      image,
      colour,
      size,
    };
  });
}

export function graphData(vars, rows, columns, edgeColumn = 'edgeLabel') {
  const nodes = new Map();
  const edges = new Map();
  for (const row of rows) {
    const [root, ...others] = displayNodes(row, vars, columns);
    if (!root) continue;
    for (const node of [root, ...others]) {
      if (!nodes.has(node.id)) nodes.set(node.id, node);
    }
    for (const node of others) {
      const label = termLabel(row[edgeColumn]);
      const key = JSON.stringify([root.id, node.id, label]);
      if (!edges.has(key)) edges.set(key, { source: root.id, target: node.id, label });
    }
  }
  return { nodes: [...nodes.values()], edges: [...edges.values()] };
}

// The GeoSPARQL default CRS (CRS84) uses longitude then latitude.
const wktTypes = new Map([
  ['POINT', ['Point', 0]], ['LINESTRING', ['LineString', 1]], ['POLYGON', ['Polygon', 2]],
  ['MULTIPOINT', ['MultiPoint', 1]], ['MULTILINESTRING', ['MultiLineString', 2]],
  ['MULTIPOLYGON', ['MultiPolygon', 3]],
]);

export function mapGeometry(term) {
  if (term?.datatype !== 'http://www.opengis.net/ont/geosparql#wktLiteral') return null;
  const match = /^(?:<([^>]+)>\s*)?([a-z]+)\s*(?:Z|M|ZM)?\s*(\(.*\))$/is.exec(term.value.trim());
  if (!match || (match[1] && match[1] !== 'http://www.opengis.net/def/crs/OGC/1.3/CRS84')) return null;
  const shape = wktTypes.get(match[2].toUpperCase());
  if (!shape) return null;
  const [type, depth] = shape;
  const tokens = match[3].match(/[^\s(),]+|[(),]/g);
  let index = 0;
  function vertex() {
    const tuple = [];
    while (index < tokens.length && !['(', ')', ','].includes(tokens[index])) {
      const token = tokens[index++];
      if (!/^[+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?$/i.test(token)) return null;
      tuple.push(Number(token));
    }
    if (tuple.length < 2 || tuple.length > 4 || !tuple.every(Number.isFinite) ||
        Math.abs(tuple[0]) > 180 || Math.abs(tuple[1]) > 90) return null;
    return tuple.slice(0, 2);
  }
  function group(level) {
    if (tokens[index++] !== '(') return null;
    if (level === 0) {
      const point = vertex();
      return tokens[index++] === ')' ? point : null;
    }
    const values = [];
    do {
      const value = level > 1 || (type === 'MultiPoint' && tokens[index] === '(')
        ? group(level - 1) : vertex();
      if (!value) return null;
      values.push(value);
    } while (tokens[index++] === ',');
    return tokens[index - 1] === ')' ? values : null;
  }
  const coordinates = group(depth);
  if (!coordinates || index !== tokens.length) return null;
  return { type, coordinates };
}

export function axisColumn(rows, name) {
  const values = rows.map(row => row[name]);
  if (values.some(term => numberValue(term) !== null)) return {
    name, value: numberValue, format: n => Number(n.toPrecision(4)).toLocaleString(),
  };
  if (values.some(term => dateValue(term) !== null)) return {
    name, value: dateValue, format: n => new Date(n).toISOString().slice(0, 10),
  };
  const categories = [...new Set(values.filter(isLabel).map(term => term.value))];
  if (!categories.length) return null;
  const positions = new Map(categories.map((value, index) => [value, index]));
  return {
    name, discrete: true, value: term => isLabel(term) ? positions.get(term.value) ?? null : null,
    format: index => Number.isInteger(index) ? categories[index] ?? '' : '',
  };
}
