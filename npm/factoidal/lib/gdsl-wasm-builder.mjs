// Thin JavaScript host binding for the Lean 4 PVGraph implementation.
// No operator registry, structural checker or evaluator is implemented here.
// The full Lean/Wasm engine processes the builder commands, admits the exact
// canonical document, and executes reference semantics. In particular the
// resultType on an op is an *untrusted hint* checked by the Lean admission gate.

const fail=message=>{throw new TypeError("PVGraph Wasm: "+message);};

/** Load the existing Factoidal Lean/Wasm engine and create a PVGraph builder.
 * @param {() => Promise<{call:Function}>} loadEngine e.g. browser.js loadEngine
 */
export async function createPVGraphWasm(loadEngine){
  if(typeof loadEngine!=="function")fail("a Lean/Wasm loadEngine callback is required");
  const engine=await loadEngine();
  if(typeof engine?.call!=="function")fail("loaded engine must expose call(op,args)");
  const needed=["pvgraphBuild","pvgraphAdmit","pvgraphEvaluate"];
  const reflected=engine.call("ops",[]);
  const supported=new Set(reflected?.ops||[]);
  for(const op of needed)if(!supported.has(op))
    throw Error("PVGraph Wasm requires a rebuilt Lean engine with "+op);
  const steps=[],known=new WeakSet();
  let counter=0;
  let frozen=false;
  const emit=(step,kind)=>{
    if(frozen)fail("builder already finalized");
    const r=Object.freeze({ref:"r"+(++counter),kind});
    steps.push({...step,ref:r.ref});
    known.add(r);
    return r;
  };
  const wire=(source)=>{
    if(!source||typeof source!=="object"||!known.has(source))
      fail("source must be a wire returned by this builder");
    return source.ref;
  };
  const id=opts=>{
    if(opts?.id!==undefined&&typeof opts.id!=="string")
      fail("id must be a string when supplied");
    return opts?.id??null;
  };
  const checkResult=(op,result,field)=>{
    if(!result||result.ok!==true||!(field in result))
      throw Error("PVGraph Wasm "+op+" refused: "+String(result?.error||"no result"));
    return result[field];
  };
  return Object.freeze({
    input(name,type="buffer<u32>",options={}){
      return emit({cmd:"input",name,type,id:id(options)},type);
    },
    op(opcode,inputs={},params={},options={}){
      if(typeof options.resultType!=="string")
        fail("op requires an explicit resultType; Lean checks it against the opcode");
      const args=Object.entries(inputs).map(([port,source])=>({port,source:wire(source)}));
      return emit({cmd:"op",op:opcode,resultType:options.resultType,
        args,params,id:id(options)},options.resultType);
    },
    output(name,source,options={}){
      if(frozen)fail("builder already finalized");
      steps.push({cmd:"output",name,source:wire(source),id:id(options)});
    },
    async build(){
      if(frozen)fail("builder already finalized");
      frozen=true;
      return checkResult("pvgraphBuild",engine.call("pvgraphBuild",[
        JSON.stringify({steps})]),"pvgraph");
    },
    async admit(pvgraph){
      return checkResult("pvgraphAdmit",engine.call("pvgraphAdmit",[
        JSON.stringify(pvgraph)]),"pvgraph");
    },
    async evaluate(pvgraph,inputs){
      return checkResult("pvgraphEvaluate",engine.call("pvgraphEvaluate",[
        JSON.stringify(pvgraph),JSON.stringify(inputs,(_key,value)=>
          value instanceof Uint32Array?Array.from(value):value)]),"outputs");
    },
  });
}
