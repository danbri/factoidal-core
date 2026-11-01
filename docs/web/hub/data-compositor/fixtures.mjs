export const DEFAULTS = Object.freeze({
  turtle: `@prefix ex: <https://studio.example/> .
@prefix person: <https://studio.example/people/> .
@prefix project: <https://studio.example/project/> .
@prefix team: <https://studio.example/team/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

# CSV scores imply Contributor; Contributor implies Person.
ex:score rdfs:domain ex:Contributor .
ex:Contributor rdfs:subClassOf foaf:Person .
ex:worksOn rdfs:range ex:Project .
person:mina foaf:name "Mina Chen" .
person:jonah foaf:name "Jonah Reed" .
person:luz foaf:name "Luz Silva" .
person:nora foaf:name "Nora Patel" .
person:tariq foaf:name "Tariq Hassan" .
project:aurora rdfs:label "Aurora / short film" .
project:atlas rdfs:label "Atlas / motion design" .
project:pulse rdfs:label "Pulse / music video" .
team:lighting rdfs:label "Lighting" .
team:animation rdfs:label "Animation" .
team:compositing rdfs:label "Compositing" .`,
  csv: `id,project,score,team
mina,aurora,94,lighting
jonah,atlas,67,animation
luz,pulse,88,compositing
nora,aurora,76,compositing
tariq,atlas,53,lighting
`,
  metadata: JSON.stringify({
    '@context': 'http://www.w3.org/ns/csvw',
    url: 'https://studio.example/data/scores.csv',
    tableSchema: {
      aboutUrl: 'https://studio.example/people/{id}',
      columns: [
        { name: 'id', suppressOutput: true },
        { name: 'project', propertyUrl: 'https://studio.example/worksOn', valueUrl: 'https://studio.example/project/{project}' },
        { name: 'score', propertyUrl: 'https://studio.example/score', datatype: 'integer' },
        { name: 'team', propertyUrl: 'https://studio.example/team', valueUrl: 'https://studio.example/team/{team}' },
      ],
    },
  }, null, 2),
  query: `PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX ex: <https://studio.example/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?person ?name ?project ?score ?team WHERE {
  GRAPH <urn:studio:turtle> {
    ?person foaf:name ?name .
    ?projectId rdfs:label ?project .
    ?teamId rdfs:label ?team .
  }
  GRAPH <urn:studio:csv> {
    ?person ex:worksOn ?projectId ; ex:score ?score ; ex:team ?teamId .
  }
  GRAPH <urn:studio:derived> { ?person a foaf:Person }
  FILTER (?score >= {{MIN_SCORE}})
}
ORDER BY DESC(?score) ?name`,
  stylesheet: `<xsl:stylesheet version="3.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:s="http://www.w3.org/2005/sparql-results#" exclude-result-prefixes="s">
  <xsl:output method="html" omit-xml-declaration="yes"/>
  <xsl:template match="/">
    <html><head><meta charset="utf-8"/><title>Studio roster</title>
      <style>body{font-family:system-ui;background:#f6f4ef;color:#183139;padding:24px}h1{letter-spacing:-.04em}table{width:100%;border-collapse:collapse;background:white}th,td{text-align:left;padding:12px;border-bottom:1px solid #dae4dd}th{background:#d8f1e2}.score{font-weight:750;color:#127655}.tag{color:#627078}footer{margin-top:20px;color:#627078;font-size:12px}</style>
    </head><body><p class="tag">STUDIO / ELIGIBLE CONTRIBUTORS</p><h1>People behind the pixels</h1>
      <p><xsl:value-of select="count(s:sparql/s:results/s:result)"/> artists in this cut.</p>
      <table><thead><tr><th>Artist</th><th>Project</th><th>Team</th><th>Score</th></tr></thead><tbody>
        <xsl:for-each select="s:sparql/s:results/s:result"><tr>
          <td><xsl:value-of select="s:binding[@name='name']/s:literal"/></td>
          <td><xsl:value-of select="s:binding[@name='project']/s:literal"/></td>
          <td><xsl:value-of select="s:binding[@name='team']/s:literal"/></td>
          <td class="score"><xsl:value-of select="s:binding[@name='score']/s:literal"/></td>
        </tr></xsl:for-each>
      </tbody></table><footer>CSVW → RDF → RDFS → named-graph SPARQL → XML → XSLT. Executed by Factoidal.</footer>
    </body></html>
  </xsl:template>
</xsl:stylesheet>`,
  minScore: '70',
});
