import {createEngine} from '/engine.mjs';
const report=document.querySelector('#report'),button=document.querySelector('#run');
const assert=(condition,message)=>{if(!condition)throw Error(message);};
button.onclick=async()=>{
 button.disabled=true;const result={status:'RUNNING',checks:[]};report.textContent=JSON.stringify(result);
 const engine=createEngine({timeoutMs:5000}),html='<p>Browser worker</p>';let heartbeat,ticks=0;
 try{
  const first=await engine.compile(html,200,100);assert(first.abi==='lean-svg-v1','actual Lean artifact missing');
  result.checks.push('actual Lean WASM returns a scene from a browser worker');
  const controller=new AbortController(),began=performance.now();
  heartbeat=setInterval(()=>{document.querySelector('#heartbeat').textContent=String(++ticks);},5);
  const timer=setTimeout(()=>controller.abort('Stop'),30);
  let cancelled=false;
  try{await engine.compile('<p>'+'A'.repeat(900000)+'</p>',200,100,'html',{signal:controller.signal});}
  catch(error){assert(error.name==='AbortError',error.message);cancelled=true;}
  finally{clearTimeout(timer);clearInterval(heartbeat);}
  assert(cancelled&&ticks>0&&performance.now()-began<1500,'foreground was blocked by Lean execution');
  assert(JSON.stringify(await engine.compile(html,200,100))===JSON.stringify(first),'post-Stop artifact changed');
  result.checks.push('foreground heartbeat and Stop interrupt CPU work; fresh worker recovers identical scene');
  let count=0,started=false;
  const timeout=createEngine({timeoutMs:200,workerFactory:()=>{const worker=new Worker(count++===0?'/tests/browser-nonreturning.mjs':'/engine-worker.mjs',{type:'module'});worker.addEventListener('message',event=>{if(event.data.type==='started')started=true;});return worker;}});
  try{
   let failed=false;try{await timeout.compile(html,200,100);}catch(error){assert(error.code==='TIMEOUT',error.message);failed=true;}
   assert(failed&&started,'nonreturning browser worker control did not execute');
   assert(JSON.stringify(await timeout.compile(html,200,100,'html',{timeoutMs:5000}))===JSON.stringify(first),'timeout recovery changed scene');
  }finally{timeout.dispose();}
  result.checks.push('nonreturning browser worker is terminated by deadline and same client recovers with real WASM');
  result.status='PASS';result.foregroundTicks=ticks;
 }catch(error){result.status='FAIL';result.failure=String(error);}
 finally{clearInterval(heartbeat);engine.dispose();report.textContent=JSON.stringify(result,null,2);button.disabled=false;window.rendererWorkerTest=result;}
};
