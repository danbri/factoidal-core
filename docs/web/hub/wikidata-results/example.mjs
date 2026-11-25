const wd = 'http://www.wikidata.org/entity/';
const wdt = 'http://www.wikidata.org/prop/direct/';
const xsd = 'http://www.w3.org/2001/XMLSchema#';
const rdfs = 'http://www.w3.org/2000/01/rdf-schema#';

const iri = value => ({ type: 'uri', value });
const entity = id => iri(wd + id);
const literal = (value, datatype) => ({ type: 'literal', value: String(value), ...(datatype && { datatype }) });
const english = value => ({ ...literal(value), 'xml:lang': 'en' });
const number = value => literal(value, xsd + (Number.isInteger(value) ? 'integer' : 'decimal'));
const result = (vars, rows) => ({
  kind: 'select',
  data: { head: { vars }, results: { bindings: rows.map(row => Object.fromEntries(vars.map((key, index) => [key, row[index]]))) } },
});
const columns = vars => vars.map(name => '?' + name).join(' ');

const landmarks = [
  ["Q41225","Big Ben","POINT(-0.124570 51.500670)","Elizabeth%20Tower%20and%20the%20north%20front%20of%20the%20Palace%20of%20Westminster%2C%20London.jpg"],
  ["Q42182","Buckingham Palace","POINT(-0.142000 51.501000)","Buckingham%20Palace%2C%20London%20-%20April%202009.jpg"],
  ["Q83125","Tower Bridge","POINT(-0.075278 51.505556)","London%20-%20London%20Tower%20Bridge%20-%20140806%20171049.jpg"],
  ["Q62378","Tower of London","POINT(-0.076198 51.508200)","Tower%20of%20London%20viewed%20from%20the%20River%20Thames.jpg"],
];
const photoCredits = {
  Q41225: ['Christian David', '4.0'],
  Q42182: ['Diliff', '3.0'],
  Q83125: ['Barcex', '3.0'],
  Q62378: ['Bob Collowan', '3.0'],
};
const commonsFile = 'http://commons.wikimedia.org/wiki/Special:FilePath/';
const landmarkThumbnails = new Map(landmarks.map(([id, , , file]) => {
  const [author, license] = photoCredits[id];
  return [commonsFile + file, { src: new URL(`./photos/${id}.jpg`, import.meta.url).href, author, license }];
}));
const londonQuery = `#title:London landmarks
#defaultView:Map{"hide":["?coord","?image"]}
#view:ImageGrid{"hide":["?coord","?image"]}
#view:Table{"hide":["?coord","?image"]}
PREFIX wd: <http://www.wikidata.org/entity/>
PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?placeLabel ?place (SAMPLE(?point) AS ?coord) (SAMPLE(?photo) AS ?image) WHERE {
  VALUES ?place { wd:Q83125 wd:Q62378 wd:Q41225 wd:Q42182 }
  ?place rdfs:label ?placeLabel; wdt:P625 ?point; wdt:P18 ?photo.
  FILTER(LANG(?placeLabel) = "en")
}
GROUP BY ?placeLabel ?place
ORDER BY ?placeLabel`;

const orbitLinks = [
  ['Q525', 'Sun', 'Q2', 'Earth'],
  ['Q525', 'Sun', 'Q111', 'Mars'],
  ['Q525', 'Sun', 'Q319', 'Jupiter'],
  ['Q525', 'Sun', 'Q193', 'Saturn'],
  ['Q2', 'Earth', 'Q405', 'Moon'],
  ['Q319', 'Jupiter', 'Q3123', 'Io'],
  ['Q319', 'Jupiter', 'Q3143', 'Europa'],
  ['Q193', 'Saturn', 'Q2565', 'Titan'],
];
const orbitVars = ['parent', 'parentLabel', 'body', 'bodyLabel', 'edgeLabel'];
const orbitQuery = [
  '#title:What orbits what', '#defaultView:Graph',
  'PREFIX wd: <' + wd + '>', 'PREFIX wdt: <' + wdt + '>', 'PREFIX rdfs: <' + rdfs + '>',
  'SELECT ' + columns(orbitVars) + ' WHERE {',
  '  VALUES (?parent ?body) {',
  ...orbitLinks.map(([parent, , body]) => '    (wd:' + parent + ' wd:' + body + ')'),
  '  }',
  '  ?body wdt:P397 ?parent; rdfs:label ?bodyLabel.',
  '  ?parent rdfs:label ?parentLabel.',
  '  FILTER(LANG(?bodyLabel) = "en" && LANG(?parentLabel) = "en")',
  '  BIND("orbited by" AS ?edgeLabel)', '}',
].join('\n');

// NASA Planetary Fact Sheet (metric). Diameter is equatorial, distance is
// in millions of kilometres and the orbital period is in Earth days.
const planets = [
  ['Rocky planets', 'Mercury', 4879, 57.9, 88],
  ['Rocky planets', 'Venus', 12104, 108.2, 224.7],
  ['Rocky planets', 'Earth', 12756, 149.6, 365.2],
  ['Rocky planets', 'Mars', 6792, 228, 687],
  ['Gas giants', 'Jupiter', 142984, 778.5, 4331],
  ['Gas giants', 'Saturn', 120536, 1432, 10747],
  ['Ice giants', 'Uranus', 51118, 2867, 30589],
  ['Ice giants', 'Neptune', 49528, 4515, 59800],
];
const planetVars = ['family', 'planet', 'diameterKm', 'distanceMillionKm', 'orbitDays'];
const planetQuery = [
  '#title:Eight planets', '#defaultView:BarChart',
  '#view:BarChart{"x":"?planet","y":"?diameterKm"}',
  '#view:ScatterChart{"x":"?distanceMillionKm","y":"?orbitDays"}',
  '#view:Dimensions{"hide":"?family"}',
  '#view:BubbleChart{"hide":"?family"}',
  'SELECT ' + columns(planetVars) + ' WHERE {',
  '  VALUES (' + columns(planetVars) + ') {',
  ...planets.map(([family, planet, ...metrics]) => '    ("' + family + '" "' + planet + '" ' + metrics.join(' ') + ')'),
  '  }', '}', 'ORDER BY ?distanceMillionKm',
].join('\n');

// Rounded lunar surface stays are from NASA's Apollo sample-collection
// comparison. Landing days use UTC.
const apollo = [
  ['Apollo 11', '1969-07-20', 21.5],
  ['Apollo 12', '1969-11-19', 31.5],
  ['Apollo 14', '1971-02-05', 33.5],
  ['Apollo 15', '1971-07-30', 67],
  ['Apollo 16', '1972-04-21', 71],
  ['Apollo 17', '1972-12-11', 75],
];
const apolloVars = ['mission', 'landing', 'surfaceHours'];
const apolloQuery = [
  '#title:Apollo Moon landings', '#defaultView:Timeline',
  '#view:LineChart{"x":"?landing","y":"?surfaceHours"}',
  '#view:AreaChart{"x":"?landing","y":"?surfaceHours"}',
  'PREFIX xsd: <' + xsd + '>',
  'SELECT ' + columns(apolloVars) + ' WHERE {',
  '  VALUES (' + columns(apolloVars) + ') {',
  ...apollo.map(([mission, day, hours]) => '    ("' + mission + '" "' + day + '"^^xsd:date ' + hours + ')'),
  '  }', '}', 'ORDER BY ?landing',
].join('\n');

const moonPattern = '  wd:Q405 wdt:P397 wd:Q2.';
const moonPrefixes = ['PREFIX wd: <' + wd + '>', 'PREFIX wdt: <' + wdt + '>'];
const view = (id, description) => ({ id, description });

export const groups = [
  {
    id: 'london', title: 'London landmarks',
    description: 'Find four landmarks on the map, see their Commons photos, or look up the Wikidata items.',
    query: londonQuery,
    thumbnails: landmarkThumbnails,
    preview: result(['placeLabel', 'place', 'coord', 'image'], landmarks.map(([id, name, point, file]) =>
      [english(name), entity(id), literal(point, 'http://www.opengis.net/ont/geosparql#wktLiteral'),
        iri(commonsFile + file)])),
    views: [view('Map', 'Select a marker to see the landmark.'), view('ImageGrid', 'Open a photo on Wikimedia Commons.'),
      view('Table', 'Each row links to a Wikidata item.')],
  },
  {
    id: 'orbits', title: 'What orbits what',
    description: 'Follow links between the Sun, selected planets, and their moons.',
    query: orbitQuery,
    preview: result(orbitVars, orbitLinks.map(([parent, pLabel, body, bLabel]) =>
      [entity(parent), english(pLabel), entity(body), english(bLabel), literal('orbited by')])),
    views: [view('Graph', 'Select a body to explore its links.'), view('GraphBuilder', 'Choose which result columns become nodes and edges.'),
      view('Tree', 'Expand each parent to see the bodies that orbit it.')],
  },
  {
    id: 'planets', title: 'Eight planets',
    description: 'Compare diameters, distance from the Sun, and the length of each orbit.',
    sources: [['NASA Planetary Fact Sheet', 'https://nssdc.gsfc.nasa.gov/planetary/factsheet/']],
    query: planetQuery,
    preview: result(planetVars, planets.map(([family, planet, ...metrics]) => [literal(family), literal(planet), ...metrics.map(number)])),
    views: [view('BarChart', 'Compare equatorial diameters in kilometres.'), view('ScatterChart', 'See how orbital periods grow with distance.'),
      view('BubbleChart', 'Bubble area represents equatorial diameter.'), view('TreeMap', 'Select a planet family to see its members by diameter.'),
      view('Dimensions', 'Trace each planet across three measures, or highlight a single value.')],
  },
  {
    id: 'apollo', title: 'Apollo Moon landings',
    description: 'Six landings, with their dates and the time each crew spent on the lunar surface.',
    sources: [['NASA landing dates', 'https://nssdc.gsfc.nasa.gov/planetary/lunar/apolloland.html'],
      ['NASA mission stays', 'https://www.nasa.gov/wp-content/uploads/2023/10/20220613-nac-heo-sci-cmte-koerner-chavers-moon-to-mars-architecture-update.pdf']],
    query: apolloQuery,
    preview: result(apolloVars, apollo.map(([mission, day, hours]) => [literal(mission), literal(day, xsd + 'date'), number(hours)])),
    views: [view('Timeline', 'See the missions in landing order.'), view('LineChart', 'Compare surface stays across missions.'),
      view('AreaChart', 'Read each mission’s surface hours against zero.')],
  },
  {
    id: 'ask', title: 'Does the Moon orbit Earth?',
    query: ['#title:Does the Moon orbit Earth?', ...moonPrefixes, 'ASK WHERE {', moonPattern, '}'].join('\n'),
    preview: { kind: 'ask', data: { boolean: true } },
    views: [view('Ask', 'ASK returns a single boolean answer.')],
  },
  {
    id: 'rdf', title: 'The Moon’s orbit as RDF',
    query: ['#title:The Moon’s orbit as RDF', ...moonPrefixes, 'CONSTRUCT {', moonPattern, '} WHERE {', moonPattern, '}'].join('\n'),
    preview: { kind: 'rdf', contentType: 'application/n-triples',
      data: '<' + wd + 'Q405> <' + wdt + 'P397> <' + wd + 'Q2> .\n' },
    views: [view('Rdf', 'CONSTRUCT returns triples that other RDF tools can read.')],
  },
];
