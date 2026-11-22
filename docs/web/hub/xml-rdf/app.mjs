import * as core from "../../../npm/factoidal/browser.js";
import {runXmlFolder,DEFAULT_QUERY,DEFAULT_EXTRACT_STYLESHEET,
  DEFAULT_RENDER_STYLESHEET}
  from "../../../npm/factoidal/lib/xml-rdf-folder.mjs";
import {fixtures} from "./fixtures.mjs";

const $=id=>document.getElementById(id);
const stages=[];
let selected=fixtures,busy=false;
const setStatus=(msg)=>{$("xml-workflow-status").textContent=msg};
$("xml-sparql").value=DEFAULT_QUERY;
$("xml-extract").value=DEFAULT_EXTRACT_STYLESHEET;
$("xml-render").value=DEFAULT_RENDER_STYLESHEET;
function showFiles(files){
  selected=files;
  $("xml-sources").textContent=files.map(f=>f.path||f.webkitRelativePath||f.name).join("\n");
  setStatus(files.length+" XML files selected");
}
function choose(input){
  const files=[...(input.files||[])];
  if(files.length)showFiles(files);
}
$("xml-folder").addEventListener("change",()=>choose($("xml-folder")));
$("xml-files").addEventListener("change",()=>choose($("xml-files")));
$("xml-fixtures").addEventListener("click",()=>showFiles(fixtures));
$("xml-run").addEventListener("click",async()=>{
  if(busy)return;
  busy=true;
  $("xml-run").disabled=true;
  stages.length=0;
  $("xml-stages").textContent="Running...";
  try{
    await core.ready();
    const result=await runXmlFolder(core,selected,{
      extractStylesheet:$("xml-extract").value,
      query:$("xml-sparql").value,
      renderStylesheet:$("xml-render").value,
      onStage(e){
        const idx=stages.findIndex(s=>s.id===e.id);
        if(idx<0)stages.push(e);else stages[idx]=e;
        $("xml-stages").textContent=stages.map(s=>s.id+": "+s.status).join("\n");
        setStatus(e.id+": "+e.status);
      }
    });
    $("xml-sources").textContent=result.graphs.map(g=>
      g.path+" — "+g.graph+" ("+g.triples+" RDF quads)").join("\n");
    $("xml-sparql-result").textContent=result.queryXml;
    // Sandboxed result: styles allowed, scripts/network/remote resources blocked.
    const csp='<meta http-equiv="Content-Security-Policy" '+
      'content="default-src \'none\'; style-src \'unsafe-inline\'; img-src data:">';
    $("xml-html").srcdoc=csp+result.html;
    $("xml-stages").textContent+=
      "\nSPARQL backend: "+result.backend+
      "\n"+result.backendNote+"\n"+result.assurance;
    setStatus("Completed "+result.sourceCount+" sources; SPARQL result rendered by XSLT 4");
  }catch(e){
    setStatus("Pipeline refused: "+String(e?.message||e));
    $("xml-html").srcdoc="";
  }finally{busy=false;$("xml-run").disabled=false;}
});
showFiles(fixtures);
