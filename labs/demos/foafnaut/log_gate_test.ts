// The log gate (docs/web/hub/foafnaut/log-gate.mjs): a flood of lines trips it once, names the
// message, and is summarised instead of written; normal output passes untouched.
import {strict as assert} from "node:assert";
import {createLogGate,gateConsole,messageKey} from "../../../docs/web/hub/foafnaut/log-gate.mjs";

const harness=(options:Record<string,unknown>={})=>{
  let t=0;const out:string[]=[],trips:unknown[]=[];
  const gate=createLogGate({write:(_level:string,args:unknown[])=>out.push(args.map(String).join(" ")),now:()=>t,onTrip:(e:unknown)=>trips.push(e),...options});
  return {gate,out,trips,advance:(ms:number)=>{t+=ms;}};
};

Deno.test("normal output passes untouched", ()=>{
  const {gate,out,trips,advance}=harness();
  for(let i=0;i<40;i++){gate.line("log",[`frame ${i}`]);advance(100);}
  assert.equal(out.length,40);assert.equal(trips.length,0);
  assert.equal(gate.stats().written,40);assert.equal(gate.stats().suppressed,0);
});

Deno.test("trace lines (JSON) are counted, never held back", ()=>{
  const {gate,out}=harness();
  for(let i=0;i<1000;i++)gate.line("log",[JSON.stringify({type:"native-html-frame",t:i})]);
  assert.equal(out.length,1000);assert.equal(gate.stats().traces,1000);assert.equal(gate.stats().tripped,false);
});

Deno.test("a line said again and again is written three times, then counted", ()=>{
  const {gate,out,advance}=harness();
  for(let i=0;i<10;i++){gate.line("error",["same"]);advance(500);}
  gate.line("log",["other"]);
  assert.deepEqual(out.slice(0,3),["same","same","same"]);
  assert.match(out[3],/repeated 7 more times in 3\.5 s/);
  assert.equal(out[4],"other");
});

Deno.test("regression: the 'scriptSession: no session' flood trips the gate once and the summary names it", ()=>{
  const {gate,out,trips,advance}=harness();
  const flood="Native HTML: page script timers failed: Error: Lean HTML: scriptSession: no session";
  // the old timer loop: one failure every 8 ms for 30 s
  for(let i=0;i<3750;i++){gate.line("error",[flood]);advance(8);}
  gate.flush();
  assert.equal(trips.length,1);
  assert.ok(out.length<20,`${out.length} lines written`);
  const warning=out.find(l=>l.includes("LOG FLOOD: more than"));
  assert.ok(warning?.includes("scriptSession: no session"),warning);
  assert.ok(out.filter(l=>l.includes("LOG FLOOD")&&l.includes("held back")).length>=2,"no periodic summary");
  const s=gate.stats();
  assert.equal(s.lines,3750);assert.ok(s.suppressed>3600);assert.equal(s.trips,1);
  assert.equal(s.top[0].message,messageKey(flood));assert.equal(s.top[0].count,3750);
});

Deno.test("many different lines trip it too, and a quiet window ends the flood", ()=>{
  const {gate,out,trips,advance}=harness();
  for(let i=0;i<300;i++){gate.line("log",[`page: item ${i}`]);advance(1);}
  assert.equal(trips.length,1);
  assert.ok(out.some(l=>l.includes('"page: item #"')),"the warning does not name the message shape");
  advance(10000);gate.line("log",["after"]);advance(10000);gate.line("log",["later"]);
  assert.ok(out.some(l=>l.includes("log flood over")));
  assert.equal(out.at(-1),"later");
});

Deno.test("--log-all writes every line", ()=>{
  const {gate,out}=harness({all:true});
  for(let i=0;i<500;i++)gate.line("error",["x"]);
  assert.equal(out.length,500);
});

Deno.test("gateConsole puts the gate in front of a console and back", ()=>{
  const lines:string[]=[];
  const target={log:(...a:unknown[])=>lines.push(a.join(" ")),info:(...a:unknown[])=>lines.push(a.join(" ")),
    warn:(...a:unknown[])=>lines.push(a.join(" ")),error:(...a:unknown[])=>lines.push(a.join(" ")),debug:(...a:unknown[])=>lines.push(a.join(" "))};
  const gate=gateConsole(target as unknown as Console,{now:()=>0});
  for(let i=0;i<100;i++)target.error("again");
  assert.equal(gate.stats().lines,100);assert.ok(lines.length<10);
  gate.restore();target.log("plain");assert.equal(lines.at(-1),"plain");
});
