// about:foafnaut (`foafnaut:about`): which build this is, and the specifications the
// repository implements in part. The build record is made by build-executables.sh from git
// and npm/factoidal/package.json, and compiled into the program; this file only reads it.

/** The build record compiled into the program (build-info.json). */
export type BuildInfo={commit?:string;commitFull?:string;dirty?:boolean;builtAt?:string;version?:string;release?:boolean};

/** The release number when run from source with no build record: the package's version. */
export async function sourceVersion():Promise<string|undefined>{
  try{return JSON.parse(await Deno.readTextFile(new URL("../../../npm/factoidal/package.json",import.meta.url))).version;}
  catch{return undefined;}
}

/** One line for `foafnaut --version`: the release, whether it is a tagged release build, the commit and the build time. */
export function versionLine(info:BuildInfo,fromSource?:string):string{
  if(!info.commit)return fromSource?`foafnaut ${fromSource} (run from source, no build record)`:"foafnaut: no build record (run from source, or an older build)";
  return `foafnaut ${info.version??"(release unknown)"} (${info.release?"release build":"development build"}), commit ${info.commit}${info.dirty?" (with uncommitted changes)":""}, built ${info.builtAt}`;
}

/** Specifications that this repository implements in part, A to Z by short name. W3C unless
marked; each was checked against the code (formal/lean4/L4Factoidal, labs/demos/foafnaut) on
2026-11-11. A name is listed when code for it exists, not when it is complete. */
export const SPECS:{name:string;url:string;body?:string}[]=[
  {name:"Controlled Identifiers",url:"https://www.w3.org/TR/cid-1.0/"},
  {name:"CSS",url:"https://www.w3.org/Style/CSS/specs.en.html"},
  {name:"CSV on the Web",url:"https://www.w3.org/TR/tabular-data-model/"},
  {name:"Data Cube",url:"https://www.w3.org/TR/vocab-data-cube/"},
  {name:"Data Integrity",url:"https://www.w3.org/TR/vc-data-integrity/"},
  {name:"DOM",url:"https://dom.spec.whatwg.org/",body:"WHATWG"},
  {name:"ECMAScript",url:"https://tc39.es/ecma262/",body:"Ecma"},
  {name:"Encoding",url:"https://encoding.spec.whatwg.org/",body:"WHATWG"},
  {name:"GRDDL",url:"https://www.w3.org/TR/grddl/"},
  {name:"HTML",url:"https://html.spec.whatwg.org/",body:"WHATWG"},
  {name:"JSON-LD",url:"https://www.w3.org/TR/json-ld11/"},
  {name:"Linked Web Storage",url:"https://www.w3.org/groups/wg/lws/"},
  {name:"MathML",url:"https://www.w3.org/TR/mathml-core/"},
  {name:"N-Quads",url:"https://www.w3.org/TR/n-quads/"},
  {name:"N-Triples",url:"https://www.w3.org/TR/n-triples/"},
  {name:"Namespaces in XML",url:"https://www.w3.org/TR/xml-names/"},
  {name:"OWL",url:"https://www.w3.org/TR/owl2-overview/"},
  {name:"PNG",url:"https://www.w3.org/TR/png-3/"},
  {name:"Pointer Events",url:"https://www.w3.org/TR/pointerevents3/"},
  {name:"R2RML",url:"https://www.w3.org/TR/r2rml/"},
  {name:"RDF",url:"https://www.w3.org/TR/rdf11-concepts/"},
  {name:"RDF Canonicalization",url:"https://www.w3.org/TR/rdf-canon/"},
  {name:"RDF Schema",url:"https://www.w3.org/TR/rdf11-schema/"},
  {name:"RDF/XML",url:"https://www.w3.org/TR/rdf-syntax-grammar/"},
  {name:"RIF",url:"https://www.w3.org/TR/rif-overview/"},
  {name:"SHACL",url:"https://www.w3.org/TR/shacl/"},
  {name:"SMIL",url:"https://www.w3.org/TR/smil/"},
  {name:"SPARQL",url:"https://www.w3.org/TR/sparql11-overview/"},
  {name:"SVG",url:"https://www.w3.org/TR/SVG2/"},
  {name:"TriG",url:"https://www.w3.org/TR/trig/"},
  {name:"Turtle",url:"https://www.w3.org/TR/turtle/"},
  {name:"UI Events",url:"https://www.w3.org/TR/uievents/"},
  {name:"URL",url:"https://url.spec.whatwg.org/",body:"WHATWG"},
  {name:"Verifiable Credentials",url:"https://www.w3.org/TR/vc-data-model-2.0/"},
  {name:"Web Annotation",url:"https://www.w3.org/TR/annotation-model/"},
  {name:"WebAssembly",url:"https://www.w3.org/TR/wasm-core-2/"},
  {name:"WebGPU",url:"https://www.w3.org/TR/webgpu/"},
  {name:"WGSL",url:"https://www.w3.org/TR/WGSL/"},
  {name:"XForms",url:"https://www.w3.org/TR/xforms11/"},
  {name:"XML",url:"https://www.w3.org/TR/xml/"},
  {name:"XML Canonicalization",url:"https://www.w3.org/TR/xml-c14n11/"},
  {name:"XML Encryption",url:"https://www.w3.org/TR/xmlenc-core1/"},
  {name:"XML Schema",url:"https://www.w3.org/TR/xmlschema11-1/"},
  {name:"XML Signature",url:"https://www.w3.org/TR/xmldsig-core1/"},
  {name:"XPath",url:"https://www.w3.org/TR/xpath-31/"},
  {name:"XPointer",url:"https://www.w3.org/TR/xptr-framework/"},
  {name:"XQuery",url:"https://www.w3.org/TR/xquery-31/"},
  {name:"XQuery and XPath Full Text",url:"https://www.w3.org/TR/xpath-full-text-30/"},
  {name:"XQuery Update Facility",url:"https://www.w3.org/TR/xquery-update-30/"},
  {name:"XSLT",url:"https://www.w3.org/TR/xslt-30/"},
];

const esc=(t:unknown)=>String(t).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;"}[c]!));

/** The release page of a build on danbri/factoidal-builds (the darwin-arm64 package of the commit). */
export const releaseURL=(info:BuildInfo)=>info.commitFull?`https://github.com/danbri/factoidal-builds/releases/tag/build-${info.commitFull.slice(0,12)}-foafnaut-darwin-arm64`:undefined;

/** The page. `rows` are the facts of this run (engine, scripts, platform), in order. */
export function aboutHTML(info:BuildInfo,rows:[string,string][],fromSource?:string):string{
  const row=(k:string,v:string)=>`<tr><th>${esc(k)}</th><td>${v}</td></tr>`;
  const version=info.version??fromSource;
  const kind=info.commit?(info.release?"release build":"development build"):"run from source";
  const built=info.builtAt?new Date(info.builtAt):undefined;
  const local=built&&!isNaN(built.getTime())?built.toLocaleString("en-GB",{dateStyle:"medium",timeStyle:"short"}):undefined;
  const link=releaseURL(info);
  const specs=[...SPECS].sort((a,b)=>a.name.localeCompare(b.name,"en",{sensitivity:"base"}));
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>About Foafnaut</title><style>body{margin:24px;font-size:15px;line-height:22px;color:#203040;background:white}h1{margin:0 0 12px;font-size:24px;line-height:32px;color:#184078}h2{margin:24px 0 8px;font-size:18px;line-height:26px;color:#184078}th{text-align:left;white-space:nowrap;padding:4px 18px 4px 0;font-weight:normal;color:#5b6876;vertical-align:top}td{padding:4px 0;overflow-wrap:anywhere}ul{margin:0;padding-left:20px}li{margin:2px 0}.body{color:#5b6876}</style></head><body>`+
    `<h1>Foafnaut ${esc(version??"")}</h1><table>`+
    row("Release",esc(version??"unknown")+" ("+esc(kind)+")")+
    row("Build commit",esc(info.commit??"unknown: run from source")+(info.dirty?" (with uncommitted changes)":""))+
    row("Built",info.builtAt?esc(info.builtAt)+(local?` (${esc(local)} local time)`:""):"unknown")+
    (link?row("Release page",`<a href="${esc(link)}">build-${esc(info.commitFull!.slice(0,12))} on factoidal-builds</a>`):"")+
    rows.map(([k,v])=>row(k,esc(v))).join("")+
    `</table><h2>Specifications</h2><p>Implemented in part: the built-in engine has code for each of these, and none is complete.</p><ul>`+
    specs.map(s=>`<li><a href="${esc(s.url)}">${esc(s.name)}</a>${s.body?` <span class="body">(${esc(s.body)})</span>`:""}</li>`).join("")+
    `</ul></body></html>`;
}
