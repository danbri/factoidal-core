const entity = id => ({ type: 'uri', value: `http://www.wikidata.org/entity/${id}` });
const literal = (value, datatype) => ({ type: 'literal', value, ...(datatype ? { datatype } : {}) });
const xsd = 'http://www.w3.org/2001/XMLSchema#';
const wkt = 'http://www.opengis.net/ont/geosparql#wktLiteral';
const cities = [
  ['Q84', 'London', 'Point(-0.128 51.507)', '1801-01-01T00:00:00Z', '4'],
  ['Q24826', 'Liverpool', 'Point(-2.991 53.408)', '1851-01-01T00:00:00Z', '2'],
  ['Q18125', 'Manchester', 'Point(-2.245 53.481)', '1901-01-01T00:00:00Z', '3'],
];
const vars = ['region', 'regionLabel', 'place', 'placeLabel', 'edgeLabel', 'coord', 'year', 'score'];

export const exampleQuery = `#title:Three cities in England
#defaultView:Graph
#view:Map{"hide":"?coord"}
PREFIX wd: <http://www.wikidata.org/entity/>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
PREFIX geo: <http://www.opengis.net/ont/geosparql#>
PREFIX hint: <http://www.bigdata.com/queryHints#>
SELECT ${vars.map(name => '?' + name).join(' ')} WHERE {
  VALUES (?region ?regionLabel ?place ?placeLabel ?edgeLabel ?coord ?year ?score) {
${cities.map(([id, name, point, date, count]) =>
    `    (wd:Q21 "England" wd:${id} "${name}" "contains" "${point}"^^geo:wktLiteral "${date}"^^xsd:dateTime ${count})`
  ).join('\n')}
  }
  hint:Query hint:optimizer "None" .
}`;

export const exampleResults = {
  head: { vars },
  results: {
    bindings: cities.map(([id, name, point, date, count]) => ({
      region: entity('Q21'), regionLabel: literal('England'), place: entity(id), placeLabel: literal(name),
      edgeLabel: literal('contains'), coord: literal(point, wkt), year: literal(date, xsd + 'dateTime'),
      score: literal(count, xsd + 'integer'),
    })),
  },
};
