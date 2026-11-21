// GDSL 0.2 -- one canonical, application-neutral typed dataflow graph.
// Graph constructor, S-expression reader/writer, verifier and CPU executor
// all operate on the SAME normalized {version,nodes,links} graph.
// A domain contributes registered operators, not a separate DSL grammar.
// Experimental. This JavaScript checker is not yet proved equivalent to Lean.
//
// Limitations: acyclic, single-assignment graph, scalar<u32> and buffer<u32>
// built-ins. No implicit coercions, side effects, dynamic WGSL compilation,
// graph iteration, network access or RDF-specific execution semantics.

export const GDSL_VERSION="gdsl/0.2";
export const MAX_NODES=128;
export const MAX_LINKS=384;
export const MAX_BUFFER_WORDS=4096;
const ID=/^[A-Za-z][A-Za-z0-9_.-]{0,63}$/;
const OP=/^[a-z][a-z0-9_.-]{1,127}$/;
const TYPES=["scalar<u32>","buffer<u32>"];
const U32_MAX=0xffffffff;
const object=x=>x!==null && typeof x==="object" && !Array.isArray(x);
const has=(x,k)=>Object.prototype.hasOwnProperty.call(x,k);
const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function fail(message){throw new TypeError("GDSL: "+message);}
function assertId(id,where){
  if(typeof id!=="string"||!ID.test(id))fail(where+" requires a valid node/port ID.");
}
function assertU32(v,where){
  if(typeof v!=="number"||!Number.isInteger(v)||v<0||v>U32_MAX)
    fail(where+" must be an exact uint32.");
  return v>>>0;
}
function assertType(type){
  if(typeof type!=="string"||!TYPES.includes(type))
    fail("Unsupported GDSL 0.2 core type: "+String(type));
  return type;
}
function typeKind(type){return type.startsWith("buffer<")?"buffer":"scalar";}
function portType(type){return {kind:typeKind(type),type:type.slice(type.indexOf("<")+1,-1)};}
function stableValue(v,type,where){
  if(type==="scalar<u32>")return assertU32(v,where);
  if(!Array.isArray(v)&&!(v instanceof Uint32Array))
    fail(where+" must be a Uint32Array or an array.");
  if(v.length>MAX_BUFFER_WORDS)fail(where+" exceeds buffer word bound.");
  return Array.from(v,(x,i)=>assertU32(x,where+"["+i+"]"));
}
const freeze=x=>{
  if(Array.isArray(x)){x.forEach(freeze);return Object.freeze(x);}
  if(object(x)){Object.values(x).forEach(freeze);return Object.freeze(x);}
  return x;
};
const builtins=[
  ["u32.map.add",{inputs:{x:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{value:"u32"},
    execute:({x},{value})=>x.map(v=>(v+value)>>>0)}],
  ["u32.map.mul",{inputs:{x:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{value:"u32"},
    execute:({x},{value})=>x.map(v=>Math.imul(v,value)>>>0)}],
  ["u32.map.xor",{inputs:{x:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{value:"u32"},
    execute:({x},{value})=>x.map(v=>(v^value)>>>0)}],
  ["u32.zip.add",{inputs:{a:"buffer<u32>",b:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{},
    execute:({a,b})=>{
      if(a.length!==b.length)fail("zip.add requires equal-length buffers.");
      return a.map((v,i)=>(v+b[i])>>>0);
    }}],
  ["u32.zip.xor",{inputs:{a:"buffer<u32>",b:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{},
    execute:({a,b})=>{
      if(a.length!==b.length)fail("zip.xor requires equal-length buffers.");
      return a.map((v,i)=>(v^b[i])>>>0);
    }}],
  ["u32.scan.sum",{inputs:{x:"buffer<u32>"},outputs:{out:"buffer<u32>"},
    params:{},
    execute:({x})=>{
      let acc=0;
      return x.map(v=>(acc=(acc+v)>>>0));
    }}],
  ["u32.reduce.sum",{inputs:{x:"buffer<u32>"},outputs:{out:"scalar<u32>"},
    params:{},
    execute:({x})=>x.reduce((a,b)=>(a+b)>>>0,0)}],
  ["u32.scalar.const",{inputs:{},outputs:{out:"scalar<u32>"},
    params:{value:"u32"},execute:(_,{value})=>value}],
  ["u32.scalar.add",{inputs:{a:"scalar<u32>",b:"scalar<u32>"},outputs:{out:"scalar<u32>"},
    params:{},execute:({a,b})=>(a+b)>>>0}],
  ["u32.broadcast",{inputs:{value:"scalar<u32>",shape:"buffer<u32>"},
    outputs:{out:"buffer<u32>"},params:{},
    execute:({value,shape})=>Array(shape.length).fill(value)}],
];

export function createOperatorRegistry(extensions=[]){
  if(!Array.isArray(extensions))fail("Operator extensions must be a list.");
  const r=new Map();
  const register=(name,desc)=>{
    if(!OP.test(name)||r.has(name)||name.startsWith("core."))
      fail("Duplicate, reserved or invalid operator: "+String(name));
    if(!object(desc)||!object(desc.inputs)||!object(desc.outputs)||
      !object(desc.params)||typeof desc.execute!=="function")
      fail("Operator "+name+" requires inputs, outputs, params, execute.");
    if(Object.keys(desc.outputs).length!==1||!has(desc.outputs,"out"))
      fail("GDSL 0.2 extension operator must provide an 'out' port.");
    for(const [port,type] of Object.entries({...desc.inputs,...desc.outputs})){
      assertId(port,"Port");assertType(type);
    }
    for(const [p,t] of Object.entries(desc.params)){
      assertId(p,"Parameter");
      if(t!=="u32"&&t!=="string")fail("Unknown parameter type.");
    }
    r.set(name,Object.freeze({inputs:freeze({...desc.inputs}),
      outputs:freeze({...desc.outputs}),params:freeze({...desc.params}),
      execute:desc.execute}));
  };
  for(const [name,desc] of builtins)register(name,desc);
  for(const ext of extensions){
    if(!object(ext))fail("Invalid operator extension.");
    register(ext.name,ext);
  }
  return r;
}
export const CORE_OPERATORS=createOperatorRegistry();

function schema(node,registry){
  if(node.op==="core.input"){
    return {inputs:{},outputs:{out:node.params.type},
      params:{name:"string",type:"type"}};
  }
  if(node.op==="core.output"){
    return {inputs:{in:node.params.type},outputs:{out:node.params.type},
      params:{name:"string",type:"type"}};
  }
  const s=registry.get(node.op);
  if(!s)fail("Unknown operator "+node.op);
  return s;
}
function validateNode(node,registry){
  if(!object(node)||!eq(Object.keys(node).sort(),["id","op","params"]))
    fail("Nodes must contain exactly id, op and params.");
  assertId(node.id,"Node");
  if(typeof node.op!=="string")fail("Missing operator.");
  if(!object(node.params))fail("Node params must be a map.");
  const s=schema(node,registry);
  const expected=Object.keys(s.params).sort();
  if(!eq(Object.keys(node.params).sort(),expected))
    fail("Wrong parameters for "+node.op+" at "+node.id+": expected "+expected.join(", "));
  for(const [name,type] of Object.entries(s.params)){
    const value=node.params[name];
    if(type==="u32")assertU32(value,node.id+"."+name);
    else if(type==="type")assertType(value);
    else if(type==="string"){assertId(value,node.id+"."+name);}
  }
  return s;
}
function ref(r,where){
  if(!object(r)||!eq(Object.keys(r).sort(),["node","port"]))
    fail(where+" must have exactly node and port.");
  assertId(r.node,where+".node");
  assertId(r.port,where+".port");
  return r;
}
function linkFor(from,to,type){
  return {from:{node:from.node,port:from.port},to:{node:to.node,port:to.port},
    ...portType(type)};
}
function copyPVGraph(doc){
  // Copy by projection to avoid prototype/alias tricks, reject unsupported extras.
  if(!object(doc)||!eq(Object.keys(doc).sort(),["links","nodes","version"]))
    fail("Graph must have exactly links, nodes and version.");
  if(doc.version!==GDSL_VERSION)fail("Unsupported document version.");
  if(!Array.isArray(doc.nodes)||!Array.isArray(doc.links))
    fail("Nodes and links must be arrays.");
  if(doc.nodes.length<2||doc.nodes.length>MAX_NODES||
      doc.links.length>MAX_LINKS)
    fail("Graph exceeds node/link limits.");
  const nodes=doc.nodes.map(n=>{
    if(!object(n)||!object(n.params)||
      !eq(Object.keys(n).sort(),["id","op","params"]))
      fail("Node declaration must contain exactly id, op and params.");
    return {id:n.id,op:n.op,params:{...n.params}};
  });
  const links=doc.links.map(l=>{
    if(!object(l)||!object(l.from)||!object(l.to)||
      !eq(Object.keys(l).sort(),["from","kind","to","type"]))
      fail("Link declaration must contain exactly from,to,kind,type.");
    return {from:{...l.from},to:{...l.to},kind:l.kind,type:l.type};
  });
  return {version:doc.version,nodes,links};
}

/** Structural and type admission of the canonical acyclic graph.
  * Links are dataflow edges only: scalar or buffer. Event/effect links
  * require a future profile and cannot silently enter a pure graph.
  * All nodes appear in topological order and are single assignment.
  */
export function checkPVGraph(doc,{registry=CORE_OPERATORS}={}){
  if(!(registry instanceof Map))fail("A typed registry Map is required.");
  const graph=copyPVGraph(doc);
  const nodeMap=new Map(),positions=new Map(),inCounts=new Map(),
    namesIn=new Set(),namesOut=new Set();
  let outputs=0;
  for(const [i,node] of graph.nodes.entries()){
    if(nodeMap.has(node.id))fail("Duplicate node ID "+node.id);
    const s=validateNode(node,registry);
    if(node.op==="core.input"){
      if(namesIn.has(node.params.name))fail("Duplicate graph input name.");
      namesIn.add(node.params.name);
    }
    if(node.op==="core.output"){
      if(namesOut.has(node.params.name))fail("Duplicate graph output name.");
      namesOut.add(node.params.name);outputs++;
    }
    nodeMap.set(node.id,{node,s});positions.set(node.id,i);inCounts.set(node.id,new Set());
  }
  if(outputs===0||namesIn.size===0)
    fail("A graph needs at least one core.input and one core.output.");
  if(graph.nodes.length>MAX_NODES||graph.links.length>MAX_LINKS)
    fail("Graph resource budget exceeded.");
  for(const l of graph.links){
    if(!eq(Object.keys(l).sort(),["from","kind","to","type"]))
      fail("Link must contain exactly from, to, kind and type.");
    ref(l.from,"Link source");ref(l.to,"Link target");
    const from=nodeMap.get(l.from.node),to=nodeMap.get(l.to.node);
    if(!from||!to)fail("Link refers to a missing node.");
    if(positions.get(l.from.node)>=positions.get(l.to.node))
      fail("Dataflow links must point forward (acyclic topological order).");
    const fromT=from.s.outputs[l.from.port],toT=to.s.inputs[l.to.port];
    if(!fromT||!toT)fail("Unknown input or output port on dataflow link.");
    if(fromT!==toT)fail("Link source and destination port types disagree.");
    if(!eq(portType(fromT),{kind:l.kind,type:l.type}))
      fail("Link kind/type disagrees with its ports.");
    const bound=inCounts.get(l.to.node);
    if(bound.has(l.to.port))fail("Input port has more than one incoming link.");
    bound.add(l.to.port);
  }
  for(const node of graph.nodes){
    const {s}=nodeMap.get(node.id);
    const actual=[...inCounts.get(node.id)].sort();
    const expected=Object.keys(s.inputs).sort();
    if(!eq(actual,expected))fail("Wrong inbound port set for "+node.id);
  }
  return freeze(graph);
}

/** Construct the exact shared AST. No hidden domain-specific AST exists. */
export function PVGraph({registry=CORE_OPERATORS}={}){
  const nodes=[],links=[],ids=new Set();
  let next=0;
  const newId=(candidate)=>{
    const id=candidate??("n"+(++next));
    assertId(id,"Node");
    if(ids.has(id))fail("Duplicate node ID "+id);
    ids.add(id);return id;
  };
  const append=(id,op,params)=>{
    nodes.push({id,op,params:{...params}});
  };
  const wire=(source,target,port,type)=>{
    ref(source,"Graph builder reference");
    links.push(linkFor(source,{node:target,port},type));
  };
  const builder={
    input(name,type="buffer<u32>",{id}={}){
      assertId(name,"Input");assertType(type);
      const node=newId(id??name);
      append(node,"core.input",{name,type});
      return freeze({node,port:"out"});
    },
    op(op,inputs={},params={},options={}){
      const s=registry.get(op);
      if(!s||op.startsWith("core."))
        fail("Unknown or reserved operator "+String(op));
      if(!object(inputs)||!object(params)||!object(options))
        fail("Invalid graph builder arguments.");
      const node=newId(options.id);
      append(node,op,params);
      for(const [port,type] of Object.entries(s.inputs)){
        if(!has(inputs,port))fail("Missing port "+port+" for "+op);
        wire(inputs[port],node,port,type);
      }
      if(Object.keys(inputs).length!==Object.keys(s.inputs).length)
        fail("Unexpected input port for "+op);
      return freeze({node,port:"out"});
    },
    output(name,source,type="buffer<u32>",{id}={}){
      assertId(name,"Output");assertType(type);
      const node=newId(id??("result"+(++next)));
      append(node,"core.output",{name,type});
      wire(source,node,"in",type);
      return freeze({node,port:"out"});
    },
    build(){return checkPVGraph({version:GDSL_VERSION,nodes,links},{registry});},
  };
  return builder;
}

/** CPU reference over the exact admitted graph, no implicit GPU/device use. */
export function runPVGraphCPU(doc,bindings,{registry=CORE_OPERATORS}={}){
  const checked=checkPVGraph(doc,{registry});
  if(!object(bindings))fail("Run bindings must be a named object.");
  const supplied=new Map(Object.entries(bindings));
  const actualInputs=checked.nodes.filter(n=>n.op==="core.input");
  if(supplied.size!==actualInputs.length ||
     actualInputs.some(n=>!supplied.has(n.params.name)))
    fail("All and only declared input names must be bound.");
  const values=new Map(),outputs=Object.create(null),trace=[];
  for(const node of checked.nodes){
    const s=schema(node,registry);
    let result;
    if(node.op==="core.input"){
      result=stableValue(supplied.get(node.params.name),node.params.type,node.id);
    }else{
      const args={};
      for(const l of checked.links){
        if(l.to.node!==node.id)continue;
        const upstream=values.get(l.from.node);
        args[l.to.port]=stableValue(upstream[l.from.port],s.inputs[l.to.port],
          node.id+"."+l.to.port);
      }
      if(node.op==="core.output"){
        result=stableValue(args.in,node.params.type,node.id);
      }else{
        result=stableValue(s.execute(args,node.params),s.outputs.out,node.id);
      }
    }
    values.set(node.id,{out:result});
    trace.push({id:node.id,op:node.op,type:s.outputs.out,
      // Safe snapshot for debugging; not hidden host side effects.
      value:Array.isArray(result)?result.slice():result});
    if(node.op==="core.output")outputs[node.params.name]=result;
  }
  return {outputs,trace};
}

/** Minimal bounded S-expression syntax for the *same* graph format.
  * Grammar:
  * (gdsl gdsl/0.2
  *   (node id operator (param key JSON-atomic-value)*)
  *   (link sourceId sourcePort targetId targetPort buffer|scalar u32)*)
  *
  * Link records and node declarations use one vocabulary for every domain.
  */
export function toPVSexpr(doc,{registry=CORE_OPERATORS}={}){
  const d=checkPVGraph(doc,{registry});
  const atom=v=>typeof v==="string"?JSON.stringify(v):String(v);
  const nodes=d.nodes.map(n=>"  (node "+n.id+" "+n.op+
    Object.entries(n.params).map(([name,v])=>" (param "+name+" "+atom(v)+")").join("")+")");
  const links=d.links.map(l=>"  (link "+l.from.node+" "+l.from.port+" "+
    l.to.node+" "+l.to.port+" "+l.kind+" "+l.type+")");
  return "(pvgraph "+GDSL_VERSION+"\n"+[...nodes,...links].join("\n")+"\n)";
}
export function fromPVSexpr(text,{registry=CORE_OPERATORS}={}){
  if(typeof text!=="string"||text.length>65536)fail("Invalid or oversized S-expression.");
  const tokens=text.match(/"(?:\\.|[^"\\])*"|\(|\)|[^\s()]+/g)??[];
  if(tokens.length>6000)fail("S-expression exceeds token limit.");
  let at=0;
  function parse(depth=0){
    if(depth>16)fail("Excessive S-expression nesting.");
    const tok=tokens[at++];
    if(tok==="("){
      const xs=[];
      while(at<tokens.length&&tokens[at]!==")")xs.push(parse(depth+1));
      if(tokens[at++]!==")")fail("Missing ')' in S-expression.");
      return xs;
    }
    if(tok===undefined||tok===")")fail("Unexpected S-expression token.");
    if(tok[0]==='"'){
      try{return JSON.parse(tok);}
      catch{fail("Invalid quoted atom.");}
    }
    if(/^\d+$/.test(tok)){
      const n=Number(tok);
      if(!Number.isSafeInteger(n))fail("Unsafe integer literal.");
      return n;
    }
    if(!/^[A-Za-z0-9_.<>/-]+$/.test(tok))fail("Invalid unquoted atom.");
    return tok;
  }
  const forms=parse();
  if(at!==tokens.length)fail("Unexpected trailing S-expression tokens.");
  if(!Array.isArray(forms)||forms[0]!=="pvgraph"||
    forms[1]!==GDSL_VERSION)fail("Wrong GDSL S-expression header.");
  const nodes=[],links=[];
  for(const form of forms.slice(2)){
    if(!Array.isArray(form))fail("Expected a GDSL graph form.");
    if(form[0]==="node"){
      if(form.length<3||typeof form[1]!=="string"||
        typeof form[2]!=="string")fail("Malformed node form.");
      const params=Object.create(null);
      for(const item of form.slice(3)){
        if(!Array.isArray(item)||item.length!==3||item[0]!=="param"||
          typeof item[1]!=="string"||has(params,item[1]))
          fail("Malformed or duplicate param form.");
        params[item[1]]=item[2];
      }
      nodes.push({id:form[1],op:form[2],params});
    }else if(form[0]==="link"){
      if(form.length!==7)fail("Malformed link form.");
      const [_,src,srcPort,dst,dstPort,kind,type]=form;
      links.push({from:{node:src,port:srcPort},
        to:{node:dst,port:dstPort},kind,type});
    }else fail("Unknown GDSL form "+String(form[0]));
  }
  return checkPVGraph({version:GDSL_VERSION,nodes,links},{registry});
}
