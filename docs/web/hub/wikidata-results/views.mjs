import {
  axisColumn, commonsImage, dateValue, displayedVars, displayNodes, graphData, hexColour,
  isEntity, isLabel, mapGeometry, numberValue, optionVars, termLabel, viewNames,
} from './view-data.mjs';

const colours = ['#12614f', '#1f73a5', '#a74625', '#7e448f', '#695900', '#007989'];
const defaultColour = colours[0];

function element(name, text, className) {
  const node = document.createElement(name);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function note(root, text) { root.append(element('p', text, 'view-note')); }

function linkOrText(text, url) {
  const node = element(url ? 'a' : 'span', text);
  if (url) node.href = url;
  return node;
}

function image(url, text) {
  const img = element('img');
  img.src = url;
  img.alt = text;
  img.loading = 'lazy';
  img.referrerPolicy = 'no-referrer';
  return img;
}

function select(label, items, selected, action) {
  const wrapper = element('label', label + ' ');
  const box = element('select');
  for (const [id, text] of items) {
    const option = element('option', text);
    option.value = id;
    box.add(option);
  }
  box.value = selected;
  box.addEventListener('change', () => action(box.value));
  wrapper.append(box);
  return wrapper;
}

function rowDetails(vars, row) {
  const dl = element('dl');
  for (const name of vars) {
    if (!row[name]) continue;
    dl.append(element('dt', '?' + name), element('dd', termLabel(row[name])));
  }
  return dl;
}

function renderTable(root, { vars, rows, options }) {
  const table = element('factoidal-sparql-results');
  table.setAttribute('max-rows', '200');
  table.results = { head: { vars: displayedVars(vars, options) }, results: { bindings: rows } };
  root.append(table);
}

function renderImages(root, { vars, rows, options, thumbnails }) {
  const gallery = element('div', undefined, 'gallery');
  const visible = displayedVars(vars, options);
  for (const row of rows) {
    const name = visible.find(key => isLabel(row[key]));
    const caption = name ? row[name].value : '';
    for (const key of vars) {
      const url = commonsImage(row[key]);
      if (!url) continue;
      const figure = element('figure');
      const file = linkOrText('', url.replace(/\/wiki\/Special:FilePath\/(.+?)(?:\?.*)?$/i, '/wiki/File:$1'));
      const thumbnail = thumbnails?.get(row[key].value);
      file.append(image(thumbnail?.src ?? url, caption || 'Commons image'));
      figure.append(file, element('figcaption', caption || '?' + key));
      if (thumbnail) {
        const credit = element('p', undefined, 'photo-credit');
        credit.append(linkOrText(thumbnail.author + ' / Commons', file.href), ' · ',
          linkOrText('CC BY-SA ' + thumbnail.license, 'https://creativecommons.org/licenses/by-sa/' + thumbnail.license + '/'),
          ' · thumbnail');
        figure.append(credit);
      }
      const details = element('details');
      details.append(element('summary', 'Row details'), rowDetails(visible, row));
      figure.append(details);
      gallery.append(figure);
    }
  }
  if (gallery.childElementCount) root.append(gallery);
  else note(root, 'Image grid needs a Wikimedia Commons media column.');
}

let leaflet;
function loadLeaflet() {
  if (!leaflet) {
    const stylesheet = element('link');
    stylesheet.rel = 'stylesheet';
    stylesheet.href = new URL('../../../vendor/leaflet/leaflet.css', import.meta.url).href;
    document.head.append(stylesheet);
    leaflet = import('../../../vendor/leaflet/leaflet.js').then(() => globalThis.L ?? globalThis.leaflet);
  }
  return leaflet;
}

async function renderMap(root, { vars, rows, options }) {
  const features = rows.flatMap(row => vars.flatMap(name => {
    const geometry = mapGeometry(row[name]);
    return geometry ? [{ type: 'Feature', geometry, properties: { row } }] : [];
  }));
  if (!features.length) {
    note(root, 'Map needs a WKT coordinate or shape in the longitude–latitude coordinate system.');
    return;
  }
  const L = await loadLeaflet();
  if (!root.isConnected) return;
  const target = element('div', undefined, 'result-map');
  root.append(target);
  const map = L.map(target, { scrollWheelZoom: false });
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19, attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
  }).addTo(map);
  const layerVars = optionVars(options.layer);
  const groups = new Map();
  for (const feature of features) {
    const row = feature.properties.row;
    const label = (layerVars.length ? layerVars : ['layerLabel', 'layer'])
      .map(name => termLabel(row[name])).filter(Boolean).join(' · ') || 'Results';
    if (!groups.has(label)) groups.set(label, []);
    groups.get(label).push(feature);
  }
  const layerControl = L.control.layers().addTo(map);
  const bounds = L.latLngBounds();
  for (const [index, [label, items]] of [...groups].entries()) {
    const fallback = colours[index % colours.length];
    const style = feature => ({
      color: hexColour(feature.properties.row.rgb, fallback), radius: 7, fillOpacity: .6,
    });
    const view = L.geoJSON(items, {
      style,
      pointToLayer: (feature, location) => L.circleMarker(location, style(feature)),
      onEachFeature: (feature, layer) => layer.bindPopup(rowDetails(displayedVars(vars, options), feature.properties.row)),
    }).addTo(map);
    // Leaflet takes HTML for layer-control labels. Pass text through the DOM escaper.
    if (groups.size > 1) layerControl.addOverlay(view, element('span', label).outerHTML);
    bounds.extend(view.getBounds());
  }
  if (groups.size === 1) layerControl.remove();
  map.fitBounds(bounds, { padding: [20, 20], maxZoom: 15 });
  return () => map.remove();
}

function canvasOf(root, title, className = 'plot', width = 800, height = 400) {
  const canvas = element('canvas', undefined, className);
  canvas.width = width;
  canvas.height = height;
  canvas.setAttribute('role', 'img');
  canvas.setAttribute('aria-label', title);
  root.append(canvas);
  return canvas.getContext('2d');
}

function showGraph(root, { nodes, edges }) {
  if (!nodes.length) {
    note(root, 'Graph needs a Wikidata item column. Graph builder can choose other columns.');
    return;
  }
  const stage = element('div', undefined, 'graph-stage');
  const inspect = element('div', undefined, 'graph-inspect');
  root.append(stage, inspect);
  const ctx = canvasOf(stage, 'Directed graph. Select a node to read its edges.', '', 800, 470);
  const central = edges.reduce(
    (counts, edge) => counts.set(edge.source, (counts.get(edge.source) ?? 0) + 1), new Map());
  const anchor = nodes.reduce((best, node) => (central.get(node.id) ?? 0) > (central.get(best.id) ?? 0) ? node : best);
  const orbit = nodes.filter(node => node !== anchor);
  const points = new Map([[anchor.id, [400, 235]]]);
  orbit.forEach((node, index) => {
    const angle = index * 2 * Math.PI / orbit.length - Math.PI / 2;
    const outer = orbit.length < 16 || index % 2 === 0;
    const radius = outer ? 1 : .64;
    points.set(node.id, [400 + radius * 306 * Math.cos(angle), 235 + radius * 164 * Math.sin(angle)]);
  });
  const byId = new Map(nodes.map(node => [node.id, node]));
  const buttons = new Map();
  const largest = Math.max(1, ...nodes.map(node => node.size ?? 1));
  function paint(active) {
    ctx.clearRect(0, 0, 800, 470);
    for (const edge of edges) {
      const [ax, ay] = points.get(edge.source);
      const [bx, by] = points.get(edge.target);
      const connected = !active || edge.source === active || edge.target === active;
      const angle = Math.atan2(by - ay, bx - ax);
      ctx.strokeStyle = connected ? '#12614f' : '#b4c9c0';
      ctx.lineWidth = connected ? 2 : 1;
      ctx.beginPath();
      ctx.moveTo(ax, ay);
      if (edge.source === edge.target) {
        ctx.bezierCurveTo(ax + 62, ay - 84, ax - 62, ay - 84, ax, ay);
      } else {
        ctx.lineTo(bx, by);
        const dx = bx - Math.cos(angle) * 32;
        const dy = by - Math.sin(angle) * 32;
        ctx.moveTo(dx - Math.cos(angle - .5) * 10, dy - Math.sin(angle - .5) * 10);
        ctx.lineTo(dx, dy);
        ctx.lineTo(dx - Math.cos(angle + .5) * 10, dy - Math.sin(angle + .5) * 10);
      }
      ctx.stroke();
    }
  }
  function choose(node) {
    for (const [id, button] of buttons) button.setAttribute('aria-pressed', String(id === node.id));
    paint(node.id);
    inspect.replaceChildren(element('h3'));
    inspect.firstElementChild.append(linkOrText(node.label, node.url));
    if (node.image) {
      const thumbnail = image(node.image, node.label);
      thumbnail.width = 120;
      inspect.append(thumbnail);
    }
    const list = element('ul');
    for (const edge of edges) {
      if (edge.source !== node.id && edge.target !== node.id) continue;
      list.append(element('li', `${byId.get(edge.source).label} → ${byId.get(edge.target).label}${edge.label ? ' · ' + edge.label : ''}`));
    }
    inspect.append(list);
  }
  for (const node of nodes) {
    const button = element('button', node.label, 'graph-node');
    button.type = 'button';
    button.title = node.label;
    button.style.left = points.get(node.id)[0] / 8 + '%';
    button.style.top = points.get(node.id)[1] / 4.7 + '%';
    if (node.colour) button.style.borderColor = node.colour;
    if (node.size) button.style.borderWidth = 1 + 4 * Math.sqrt(node.size / largest) + 'px';
    button.addEventListener('click', () => choose(node));
    buttons.set(node.id, button);
    stage.append(button);
  }
  choose(anchor);
}

function renderGraph(root, { vars, rows, options }) {
  renderGraphProjection(root, vars, rows, null, optionVars(options.edgeLabel)[0] ?? 'edgeLabel');
}

function renderGraphBuilder(root, { vars, rows }) {
  if (vars.length < 2) {
    note(root, 'Graph builder needs two result columns.');
    return;
  }
  const entities = vars.filter(name => rows.some(row => isEntity(row[name])));
  let [source, target] = entities.length >= 2 ? entities : vars;
  let edge = vars.includes('edgeLabel') ? 'edgeLabel' : '';
  const tools = element('div', undefined, 'view-tools');
  const graph = element('div');
  const names = vars.map(name => [name, '?' + name]);
  function render() {
    graph.replaceChildren();
    if (source === target) {
      note(graph, 'Choose different source and target columns.');
      return;
    }
    renderGraphProjection(graph, vars, rows, [source, target], edge);
  }
  tools.append(
    select('Source', names, source, value => { source = value; render(); }),
    select('Target', names, target, value => { target = value; render(); }),
    select('Edge label', [['', 'None'], ...names], edge, value => { edge = value; render(); }),
  );
  root.append(tools, graph);
  render();
}

function renderGraphProjection(root, vars, rows, columns, edge) {
  const model = graphData(vars, rows, columns, edge);
  const nodes = model.nodes.slice(0, 40);
  if (nodes.length < model.nodes.length) note(root, `Showing ${nodes.length} of ${model.nodes.length} nodes.`);
  const visible = new Set(nodes.map(node => node.id));
  showGraph(root, { nodes, edges: model.edges.filter(item => visible.has(item.source) && visible.has(item.target)) });
}

function renderTree(root, { vars, rows, options }) {
  const model = new Map();
  for (const row of rows) {
    let level = model;
    for (const node of displayNodes(row, displayedVars(vars, options))) {
      if (!level.has(node.id)) level.set(node.id, { ...node, children: new Map() });
      level = level.get(node.id).children;
    }
  }
  function branch(level) {
    const list = element('ul', undefined, 'tree');
    for (const node of level.values()) {
      const item = element('li');
      if (node.children.size) {
        const details = element('details');
        const label = element('summary', node.label);
        details.open = level === model;
        details.append(label, branch(node.children));
        item.append(details);
      } else item.append(linkOrText(node.label, node.url));
      if (node.image) {
        const thumbnail = image(node.image, node.label);
        thumbnail.width = 32;
        item.append(thumbnail);
      }
      list.append(item);
    }
    return list;
  }
  if (model.size) root.append(branch(model));
  else note(root, 'Tree needs a Wikidata item column.');
}

function renderTimeline(root, { vars, rows, options }) {
  const visible = displayedVars(vars, options);
  const events = rows.flatMap(row => {
    const dates = vars.map(name => row[name]).filter(term => dateValue(term) !== null);
    const label = visible.find(name => isLabel(row[name])) ?? visible.find(name => isEntity(row[name]));
    return dates.length ? [{ dates, label: termLabel(row[label]), row }] : [];
  }).sort((a, b) => dateValue(a.dates[0]) - dateValue(b.dates[0]));
  if (!events.length) {
    note(root, 'Timeline needs a date or dateTime column.');
    return;
  }
  const plotted = events.slice(0, 16);
  const height = 56 + plotted.length * 26;
  const ctx = canvasOf(root, 'Timeline of the first ' + plotted.length + ' events', 'plot', 800, height);
  const dates = plotted.flatMap(event => event.dates.slice(0, 2).map(dateValue));
  const range = scale(dates, 177, 770);
  ctx.font = '15px system-ui';
  ctx.textAlign = 'left';
  ctx.fillStyle = '#29433d';
  ctx.fillText(new Date(Math.min(...dates)).toISOString().slice(0, 10), 177, 24);
  ctx.textAlign = 'right';
  ctx.fillText(new Date(Math.max(...dates)).toISOString().slice(0, 10), 770, 24);
  for (const [index, event] of plotted.entries()) {
    const y = 43 + index * 26;
    const [start, end] = event.dates.slice(0, 2).map(dateValue);
    ctx.fillStyle = '#29433d';
    ctx.fillText(event.label, 160, y + 5, 151);
    ctx.fillStyle = defaultColour;
    if (end !== undefined && end !== start) {
      ctx.fillRect(range.at(Math.min(start, end)), y - 3, Math.abs(range.at(end) - range.at(start)), 6);
    }
    ctx.beginPath();
    ctx.arc(range.at(start), y, 5, 0, 2 * Math.PI);
    ctx.fill();
  }
  const list = element('ol', undefined, 'timeline');
  for (const { dates, label, row } of events) {
    const item = element('li');
    for (const date of dates.slice(0, 2)) {
      if (item.childElementCount) item.append(' – ');
      const time = element('time', date.value.split('T')[0]);
      time.dateTime = date.value;
      item.append(time);
    }
    if (label) item.append(' · ' + label);
    const details = element('details');
    details.append(element('summary', 'Row details'), rowDetails(visible, row));
    const media = vars.map(name => commonsImage(row[name])).find(Boolean);
    if (media) {
      const thumbnail = image(media, label || 'Commons image');
      thumbnail.width = 160;
      details.append(thumbnail);
    }
    item.append(details);
    list.append(item);
  }
  root.append(list);
}

function sizes(vars, rows) {
  return rows.flatMap(row => {
    const labels = vars.filter(name => isLabel(row[name])).map(name => row[name].value);
    const size = vars.map(name => numberValue(row[name])).find(value => value !== null);
    const entity = vars.find(name => isEntity(row[name]));
    const label = labels[0] ?? termLabel(row[entity]);
    if (!(size > 0) || !label) return [];
    return [{ labels: labels.length ? labels : [label], label, size,
      colour: hexColour(row.rgb, null), url: entity ? row[entity].value.replace(/^http:/, 'https:') : null }];
  });
}

function renderBubbles(root, { vars, rows, options }) {
  const points = sizes(displayedVars(vars, options), rows);
  if (!points.length) {
    note(root, 'Bubble chart needs a label or item and a positive size.');
    return;
  }
  const largest = Math.max(...points.map(point => point.size));
  const bubbles = element('div', undefined, 'bubbles');
  for (const [index, point] of points.entries()) {
    const item = element('div', undefined, 'bubble-item');
    const dot = element('span', String(point.size), 'bubble-dot');
    dot.style.width = dot.style.height = Math.max(24, 105 * Math.sqrt(point.size / largest)) + 'px';
    dot.style.backgroundColor = (point.colour ?? colours[index % colours.length]) + '33';
    item.append(dot, linkOrText(point.label, point.url));
    bubbles.append(item);
  }
  root.append(bubbles);
}

function renderTreeMap(root, { vars, rows, options }) {
  const points = sizes(displayedVars(vars, options), rows);
  if (!points.length) {
    note(root, 'Tree map needs labels and a positive size.');
    return;
  }
  const chart = element('div', undefined, 'tree-map');
  const controls = element('div', undefined, 'view-tools');
  const back = element('button', 'Back to all groups');
  const detail = element('p', '', 'view-note');
  back.type = 'button';
  controls.append(back);
  root.append(controls, chart, detail);
  function render(current, depth) {
    const groups = new Map();
    for (const point of current) {
      const key = point.labels[depth] ?? point.label;
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(point);
    }
    const total = current.reduce((sum, point) => sum + point.size, 0);
    chart.replaceChildren();
    back.hidden = depth === 0;
    let offset = 0;
    const vertical = depth % 2 !== 0;
    for (const [index, [label, items]] of [...groups].entries()) {
      const size = items.reduce((sum, point) => sum + point.size, 0);
      const fraction = size * 100 / total;
      const button = element('button', label);
      button.type = 'button';
      button.title = `${label} · ${size}`;
      button.style.backgroundColor = colours[index % colours.length] + '3b';
      button.style.left = vertical ? '0' : offset + '%';
      button.style.top = vertical ? offset + '%' : '0';
      button.style.width = vertical ? '100%' : fraction + '%';
      button.style.height = vertical ? fraction + '%' : '100%';
      button.onclick = () => {
        detail.replaceChildren(linkOrText(`${label} · ${size}`, items.length === 1 ? items[0].url : null));
        if (items.some(item => item.labels.length > depth + 1)) render(items, depth + 1);
      };
      chart.append(button);
      offset += fraction;
    }
  }
  back.onclick = () => { detail.replaceChildren(); render(points, 0); };
  render(points, 0);
}

function scale(values, start, end, includeZero = false) {
  let min = Math.min(...values, ...(includeZero ? [0] : []));
  let max = Math.max(...values, ...(includeZero ? [0] : []));
  if (max === min) { min -= .5; max += .5; }
  return { min, max, at: n => start + (n - min) / (max - min) * (end - start) };
}

function path(ctx, points) {
  ctx.beginPath();
  for (const [index, [x, y]] of points.entries()) {
    if (index === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
}

function axes(ctx, x, y, xScale, yScale, points) {
  ctx.font = '16px system-ui';
  ctx.fillStyle = '#29433d';
  ctx.textBaseline = 'middle';
  ctx.textAlign = 'right';
  const ys = y.discrete ? [...new Set(points.map(point => point[1]))].slice(0, 10)
    : Array.from({ length: 5 }, (_, index) => yScale.min + index * (yScale.max - yScale.min) / 4);
  for (const v of ys) {
    const position = yScale.at(v);
    ctx.fillText(y.format(v), 88, position, 83);
    ctx.strokeStyle = '#c9d8d2';
    path(ctx, [[96, position], [770, position]]);
    ctx.stroke();
  }
  const xs = [...new Set(points.map(point => point[0]))].sort((a, b) => a - b);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  const step = Math.max(1, Math.ceil(xs.length / 7));
  xs.filter((_, index) => index % step === 0)
    .forEach(v => ctx.fillText(x.format(v), xScale.at(v), 362, 110));
}

function renderChart(root, { vars, rows, options }, name) {
  const columns = displayedVars(vars, options).map(key => axisColumn(rows, key)).filter(Boolean);
  if (columns.length < 2) {
    note(root, 'This chart needs two number, date or label columns.');
    return;
  }
  let x = columns.find(column => optionVars(options.x).includes(column.name)) ?? columns[0];
  let y = columns.find(column => optionVars(options.y).includes(column.name)) ?? columns.find(column => column !== x);
  const tools = element('div', undefined, 'view-tools');
  const plot = element('div');
  const names = columns.map(column => [column.name, '?' + column.name]);
  function chart() {
    plot.replaceChildren();
    const points = rows.map(row => [x.value(row[x.name]), y.value(row[y.name])])
      .filter(point => point.every(n => n !== null)).sort((a, b) => a[0] - b[0]);
    if (!points.length || x === y) {
      note(plot, 'Choose two different columns with values on the same rows.');
      return;
    }
    const bars = name === 'BarChart';
    const xScale = scale(points.map(point => point[0]), 145, 725);
    const yScale = scale(points.map(point => point[1]), 348, 24, bars || name === 'AreaChart');
    const ctx = canvasOf(plot, `${viewNames[name]} of ?${y.name} by ?${x.name}`);
    axes(ctx, x, y, xScale, yScale, points);
    const coords = points.map(([a, b]) => [xScale.at(a), yScale.at(b)]);
    ctx.strokeStyle = defaultColour;
    ctx.fillStyle = defaultColour;
    ctx.lineWidth = 3;
    if (bars) {
      const baseline = yScale.at(Math.max(yScale.min, Math.min(yScale.max, 0)));
      const width = Math.min(34, 500 / coords.length);
      for (const [a, b] of coords) ctx.fillRect(a - width / 2, Math.min(b, baseline), width, Math.max(1, Math.abs(b - baseline)));
      return;
    }
    if (name !== 'ScatterChart') {
      path(ctx, coords);
      ctx.stroke();
      if (name === 'AreaChart') {
        ctx.lineTo(coords.at(-1)[0], 348);
        ctx.lineTo(coords[0][0], 348);
        ctx.closePath();
        ctx.fillStyle = defaultColour + '44';
        ctx.fill();
        ctx.fillStyle = defaultColour;
      }
    }
    for (const [a, b] of coords) {
      ctx.beginPath();
      ctx.arc(a, b, 4, 0, 2 * Math.PI);
      ctx.fill();
    }
  }
  tools.append(
    select('X axis', names, x.name, key => { x = columns.find(column => column.name === key); chart(); }),
    select('Y axis', names, y.name, key => { y = columns.find(column => column.name === key); chart(); }),
  );
  root.append(tools, plot);
  chart();
}

function renderDimensions(root, { vars, rows, options }) {
  const columns = displayedVars(vars, options).map(name => axisColumn(rows, name)).filter(Boolean).slice(0, 12);
  if (columns.length < 2) {
    note(root, 'Dimensions needs two or more number, date or label columns.');
    return;
  }
  const tools = element('div', undefined, 'view-tools');
  const plot = element('div');
  const filter = element('select');
  const label = element('label', 'Highlight value ');
  label.append(filter);
  let axis = columns[0];
  root.append(tools, plot);
  function draw() {
    plot.replaceChildren();
    const ctx = canvasOf(plot, 'Parallel coordinates across ' + columns.map(column => '?' + column.name).join(', '));
    const data = columns.map((column, index) => {
      const values = rows.map(row => column.value(row[column.name])).filter(value => value !== null);
      return { column, x: 75 + index * 650 / (columns.length - 1), scale: scale(values, 344, 48) };
    });
    for (const item of data) {
      ctx.strokeStyle = '#9cbdb1';
      path(ctx, [[item.x, 48], [item.x, 344]]);
      ctx.stroke();
      ctx.fillStyle = '#243f37';
      ctx.font = '16px system-ui';
      ctx.textAlign = 'center';
      ctx.fillText('?' + item.column.name, item.x, 32, 620 / columns.length);
    }
    for (const row of rows) {
      const points = data.flatMap(item => {
        const value = item.column.value(row[item.column.name]);
        return value === null ? [] : [[item.x, item.scale.at(value)]];
      });
      const matches = !filter.value || String(axis.value(row[axis.name])) === filter.value;
      ctx.strokeStyle = matches ? '#12614f88' : '#c7d8d288';
      path(ctx, points);
      ctx.stroke();
    }
  }
  function filterValues() {
    filter.replaceChildren();
    const all = element('option', 'All values');
    all.value = '';
    filter.append(all);
    const values = [...new Set(rows.map(row => axis.value(row[axis.name])).filter(value => value !== null))];
    for (const value of values) {
      const option = element('option', axis.format(value));
      option.value = String(value);
      filter.append(option);
    }
    draw();
  }
  tools.append(select('Dimension', columns.map(column => [column.name, '?' + column.name]), axis.name, name => {
    axis = columns.find(column => column.name === name);
    filterValues();
  }), label);
  filter.onchange = draw;
  filterValues();
}

// Every renderer receives the same read-only view context. Async handlers
// can return a cleanup function. Callers can replace or extend the registry.
export function createResultViews(overrides = []) {
  return new Map([
    ['Table', renderTable], ['Graph', renderGraph], ['GraphBuilder', renderGraphBuilder],
    ['Map', renderMap], ['ImageGrid', renderImages], ['Timeline', renderTimeline],
    ['Tree', renderTree], ['TreeMap', renderTreeMap], ['Dimensions', renderDimensions],
    ['BarChart', renderChart], ['LineChart', renderChart], ['ScatterChart', renderChart],
    ['AreaChart', renderChart], ['BubbleChart', renderBubbles],
    ...overrides,
  ]);
}
