// XML source files -> Lean XSLT4 -> Lean JSON-LD reader -> named RDF
// datasets -> registered Lean SPARQL -> Lean XSLT4 -> HTML.
//
// JavaScript owns file I/O and resource lifetime only. Factoidal owns XML,
// JSON-LD, RDF identity, dataset merge, SPARQL and output formatting.
// The source-retagging transport uses RDF/JS quads and has a separate
// Lean Dataflow contract in Dataflow/XmlSourceGraphStage.lean.
// That formal stage is not yet the Wasm handler called by fromQuads.

export const DEFAULT_EXTRACT_STYLESHEET = `<xsl:stylesheet version="4.0"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:output method="text"/>
  <xsl:template match="/">
    <xsl:value-of select="serialize(map{
      '@context': map{'ex':'https://example.org/records#'},
      '@graph': array {
        for $p in /records/person return
        map {
          '@id': concat('https://example.org/person/',string($p/@id)),
          'ex:name': string($p/name),
          'ex:knows': map {'@id':
            concat('https://example.org/person/',string($p/knows/@ref))}
        }
      }
    },map{'method':'json'})"/>
  </xsl:template>
</xsl:stylesheet>`;

export const DEFAULT_QUERY = `PREFIX ex: <https://example.org/records#>
SELECT ?source ?name ?friendSource ?friendName WHERE {
  GRAPH ?source {
    ?person ex:name ?name .
    ?person ex:knows ?friend .
  }
  GRAPH ?friendSource { ?friend ex:name ?friendName }
}
ORDER BY ?source ?name ?friendName`;

export const DEFAULT_RENDER_STYLESHEET = `<xsl:stylesheet version="4.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:s="http://www.w3.org/2005/sparql-results#"
  exclude-result-prefixes="s">
  <xsl:output method="html" omit-xml-declaration="yes"/>
  <xsl:template match="/">
    <html><head><meta charset="utf-8"/><title>Source-linked people</title>
      <style>body{font:15px system-ui;margin:1.5em;background:#fcfcfc;color:#223}
        table{border-collapse:collapse;width:100%}
        th,td{border-bottom:1px solid #ccc;text-align:left;padding:.6em}
        th{background:#e7f1ed}caption{text-align:left;font-size:1.2em;margin-bottom:.8em}
      </style></head><body>
      <table><caption>People and links across source files</caption>
      <thead><tr><th>Person</th><th>Knows</th><th>Person source</th><th>Friend source</th></tr></thead>
      <tbody>
        <xsl:for-each select="/s:sparql/s:results/s:result">
          <tr>
            <td><xsl:value-of select="s:binding[@name='name']/s:literal"/></td>
            <td><xsl:value-of select="s:binding[@name='friendName']/s:literal"/></td>
            <td><xsl:value-of select="s:binding[@name='source']/s:uri"/></td>
            <td><xsl:value-of select="s:binding[@name='friendSource']/s:uri"/></td>
          </tr>
        </xsl:for-each>
      </tbody></table></body></html>
  </xsl:template>
</xsl:stylesheet>`;

const sourcePath=entry=>String(entry.path||entry.webkitRelativePath||entry.name||"");
const safePath=name=>{
  if(!name||name.includes("\0")||name.includes("\\")||
     name.split("/").some(part=>part==="."||part===".."||!part))
    throw new TypeError("Each XML source needs a safe, unique relative path");
  if(!/\.xml$/i.test(name))throw new TypeError("Only .xml sources admitted: "+name);
  return name;
};
export const sourceGraphIri = relativePath=>
  "urn:pvgraph:source:"+encodeURIComponent(safePath(relativePath));

function step(onStage,id,status,detail={}){
  onStage?.({id,status,...detail});
}
async function bytesAsText(entry){
  if(typeof entry.xml==="string")return entry.xml;
  if(typeof entry.text==="function")return await entry.text();
  throw new TypeError("XML source lacks a text() reader: "+sourcePath(entry));
}
function dispose(dataset){try{dataset?.dispose?.();}catch{}}

/** Stages run in file-name order for deterministic source provenance.
 * Input may be a stream/async iterable of named XML source handles.
 * Bounded parallel XSLT is a future stage implementation; this version
 * makes one bounded batch of sources and merges each incrementally.
 */
export async function runXmlFolder(core,files,{
  extractStylesheet=DEFAULT_EXTRACT_STYLESHEET,
  query=DEFAULT_QUERY,
  renderStylesheet=DEFAULT_RENDER_STYLESHEET,
  onStage=()=>{},
  maxFiles=100,maxFileCharacters=2_000_000
}={}){
  if(!core?.xslt4Transform||!core?.jsonldToRdf||!core?.fromQuads||
     !core?.datasetMerge||!core?.queryRaw||!core?.dataFactory)
    throw new TypeError("Factoidal XML/RDF/SPARQL engine API is required");
  const collected=[];
  for await(const input of files){
    if(collected.length>=maxFiles)throw new RangeError("Too many XML files");
    const path=safePath(sourcePath(input));
    collected.push({path,input,iri:sourceGraphIri(path)});
  }
  if(!collected.length)throw new TypeError("Select at least one .xml file");
  collected.sort((a,b)=>a.path<b.path?-1:a.path>b.path?1:0);
  for(let i=1;i<collected.length;i++)
    if(collected[i-1].path===collected[i].path)
      throw new TypeError("Duplicate source path "+collected[i].path);
  let combined=null;
  const detail=[];
  try{
    for(const {path,input,iri} of collected){
      let parsed=null,scoped=null;
      step(onStage,"xslt4:"+path,"running",{source:iri});
      try{
        const xml=await bytesAsText(input);
        if(xml.length>maxFileCharacters)
          throw new RangeError("XML source exceeds configured bound: "+path);
        const transformed=await core.xslt4Transform(extractStylesheet,xml);
        if(typeof transformed?.output!=="string"||
           transformed.output.length>maxFileCharacters)
          throw new TypeError("XSLT4 did not return bounded JSON-LD text");
        const sourceJsonld=transformed.output;
        // Check host transport syntax; Lean still owns JSON-LD RDF semantics.
        JSON.parse(sourceJsonld);
        step(onStage,"jsonld:"+path,"running",{source:iri});
        parsed=await core.jsonldToRdf(sourceJsonld);
        const quads=[...parsed];
        if(!quads.length)
          throw new TypeError("Empty RDF source has no representable named graph via fromQuads: "+path);
        if(quads.some(q=>q.graph?.termType!=="DefaultGraph"))
          throw new TypeError("Simple-triples profile refuses nested JSON-LD named graphs: "+path);
        scoped=await core.fromQuads(quads.map(q=>
          core.dataFactory.quad(q.subject,q.predicate,q.object,
            core.dataFactory.namedNode(iri))));
        const next=combined?await core.datasetMerge(combined,scoped):scoped;
        if(next!==scoped)dispose(scoped);
        if(combined && combined!==next)dispose(combined);
        combined=next;scoped=null;
        detail.push({path,graph:iri,triples:quads.length});
        step(onStage,"rdf:"+path,"done",{source:iri,triples:quads.length});
      }finally{
        dispose(parsed);dispose(scoped);
      }
    }
    // Preserve named-graph boundaries: never use Graph union or a
    // JavaScript-side SPARQL evaluator. QueryRaw receives canonical TriG.
    const trig=await combined.serialize({format:"trig"});
    step(onStage,"sparql","running",{backend:"lean-indexed"});
    const xmlResult=await core.queryRaw(trig,query,{
      dataFormat:"trig",output:"xml",entail:"none"
    });
    if(typeof xmlResult!=="string"||!xmlResult.trimStart().startsWith("<"))
      throw new TypeError("SPARQL XML result transport rejected");
    step(onStage,"sparql","done",{backend:"lean-indexed"});
    step(onStage,"xslt4:html","running");
    const rendered=await core.xslt4Transform(renderStylesheet,xmlResult);
    if(typeof rendered?.output!=="string")
      throw new TypeError("XSLT4 did not produce HTML text");
    step(onStage,"xslt4:html","done");
    return {html:rendered.output,queryXml:xmlResult,
      graphs:detail,sourceCount:detail.length,backend:"lean-indexed",
      backendNote:"PVGraph BGP GPU offload is not registered in the shipping SPARQL evaluator",
      assurance:"Factoidal engine stages + unproved host file/retagging adapters"};
  }finally{dispose(combined)}
}
