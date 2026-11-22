import test from "node:test";
import assert from "node:assert/strict";
import {runXmlFolder,sourceGraphIri,DEFAULT_QUERY}
  from "../npm/factoidal/lib/xml-rdf-folder.mjs";
import {fixtures} from "../docs/web/hub/xml-rdf/fixtures.mjs";

const source={
  subject:{termType:"NamedNode",value:"https://example.org/person/a"},
  predicate:{termType:"NamedNode",value:"https://example.org/records#name"},
  object:{termType:"Literal",value:"Alice"},
  graph:{termType:"DefaultGraph",value:""}
};
function mockCore({quads=[source]}={}){
  const calls=[],open=new Set();
  const make=rows=>{
    const ds={
      rows,async serialize({format}){
        assert.equal(format,"trig");
        return "TRIG "+rows.map(q=>q.graph.value).join(",");
      },
      *[Symbol.iterator](){yield* rows;},
      dispose(){open.delete(ds)}
    };
    open.add(ds);
    return ds;
  };
  return {
    calls,open,
    core:{
      dataFactory:{
        namedNode(value){return {termType:"NamedNode",value};},
        quad(subject,predicate,object,graph){return {subject,predicate,object,graph};}
      },
      async xslt4Transform(style,xml){
        calls.push(["xslt4Transform",xml]);
        if(xml.startsWith("<records"))
          return {method:"text",output:JSON.stringify({"@context":{},"@graph":[]})};
        return {method:"html",output:"<html><body>Mapped by XSLT</body></html>"};
      },
      async jsonldToRdf(text){calls.push(["jsonldToRdf",JSON.parse(text)]);return make(quads);},
      async fromQuads(qs){calls.push(["fromQuads",qs]);return make(qs);},
      async datasetMerge(a,b){calls.push(["datasetMerge"]);return make([...a.rows,...b.rows]);},
      async query(data,query,opts){
        calls.push(["query",data,query,opts]);
        return "<sparql xmlns='http://www.w3.org/2005/sparql-results#'></sparql>";
      }
    }
  };
}
test("one named RDF graph per XML source and cross-file SPARQL over TriG",async()=>{
  const {core,calls,open}=mockCore();
  const stages=[];
  const result=await runXmlFolder(core,[fixtures[1],fixtures[0]],{
    onStage:e=>stages.push(e)
  });
  assert.equal(result.sourceCount,2);
  assert.equal(result.backend,"lean-indexed");
  assert.deepEqual(result.graphs.map(x=>x.path),
    ["sources/alice.xml","sources/bob.xml"]);
  assert.deepEqual(result.graphs.map(x=>x.triples),[1,1]);
  const tagged=calls.filter(x=>x[0]==="fromQuads");
  assert.equal(tagged.length,2);
  assert.deepEqual(tagged.map(x=>x[1][0].graph.value),
    [sourceGraphIri("sources/alice.xml"),sourceGraphIri("sources/bob.xml")]);
  const queryCall=calls.find(x=>x[0]==="query");
  assert.equal(queryCall[1].rows.length,2);
  assert.ok(queryCall[1].rows.some(q=>q.graph.value.includes("alice.xml")));
  assert.ok(queryCall[1].rows.some(q=>q.graph.value.includes("bob.xml")));
  assert.equal(queryCall[2],DEFAULT_QUERY);
  assert.deepEqual(queryCall[3],{output:"xml",entail:"none"});
  assert.equal(result.html,"<html><body>Mapped by XSLT</body></html>");
  assert.equal(stages.at(-1).id,"xslt4:html");
  assert.equal(open.size,0,"RDF dataset handles are released");
});
test("plain browser File.name falls back when webkitRelativePath is empty",async()=>{
  const {core}=mockCore();
  const result=await runXmlFolder(core,[{name:"a.xml",webkitRelativePath:"",
    async text(){return "<records/>"}}]);
  assert.equal(result.graphs[0].graph,sourceGraphIri("a.xml"));
});
test("blank nodes with accidental source paths are refused",()=>{
  for(const path of ["../foo.xml","folder/../foo.xml","folder//foo.xml",
    "x.txt","", "\\foo.xml"]){
    assert.throws(()=>sourceGraphIri(path));
  }
});
test("nested JSON-LD graph input cannot silently lose graph identity",async()=>{
  const m=mockCore({quads:[{...source,graph:{termType:"NamedNode",value:"urn:nested"}}]});
  await assert.rejects(runXmlFolder(m.core,fixtures.slice(0,1)),/nested JSON-LD named graphs/);
  assert.equal(m.open.size,0);
});
test("empty source cannot fabricate a named graph from zero quads",async()=>{
  const m=mockCore({quads:[]});
  await assert.rejects(runXmlFolder(m.core,fixtures.slice(0,1)),/Empty RDF source/);
  assert.equal(m.open.size,0);
});
test("duplicate source paths refused before any transform or query",async()=>{
  const m=mockCore();
  await assert.rejects(runXmlFolder(m.core,[fixtures[0],fixtures[0]]),/Duplicate/);
  assert.equal(m.calls.length,0);
});
