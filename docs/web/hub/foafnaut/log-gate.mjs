// The log gate: every line the browser writes to a terminal or console goes through one gate,
// so a flood (a failure repeated every pump turn, a page that logs in a loop) never drowns the
// terminal unnoticed. The rule of every host (the native window and its worker, Textnaut, the Hub).
//
// - A line said again and again in a row is written a few times, then counted; the count is
//   written ("… repeated 1234 times in 5.0 s") when another line comes or at the next summary.
// - Beyond the budget (more than `perSecond` lines in a second, or `perWindow` in `windowMs`)
//   the gate trips: ONE warning naming the most said messages and their counts, then a summary
//   every `windowMs` instead of the lines, until a window under budget.
// - Machine trace lines (JSON objects, one per line) are not gated: tools read them, and the
//   frame trace is many lines a second by design. They are counted.
// - `all` (--log-all, FOAFNAUT_LOG=all) writes every line: nothing is lost for debugging.
// - `stats()` gives the counts for --perf-summary and the exit trace; `onTrip` records the event.
//
// Cost when output is normal: one comparison with the last line and two counters a line.

/** The key a message is counted under: digits made `#` (counters, times, ids), at most 160 characters. */
export function messageKey(text) {
  return String(text).slice(0,160).replace(/\d+/g,'#');
}

/**
 * A gate. `write(level,args)` writes a line as the host's console would.
 * @param {{write?:(level:string,args:unknown[])=>void,now?:()=>number,perSecond?:number,perWindow?:number,windowMs?:number,
 *   inARow?:number,all?:boolean,onTrip?:(event:{at:number,top:{message:string,count:number}[],lines:number})=>void,name?:string}} [options]
 */
export function createLogGate({write=(_level,_args)=>{},now=()=>performance.now(),perSecond=50,perWindow=200,windowMs=10000,inARow=3,all=false,onTrip,name='foafnaut'}={}) {
  const stats={lines:0,written:0,suppressed:0,collapsed:0,traces:0,trips:0,tripped:false};
  let last,lastLevel='log',repeats=0,repeatSince=0;
  let secondAt=-Infinity,inSecond=0,windowAt=-Infinity,inWindow=0;
  // the messages of this window by key (`top` names the most said), at most 256 keys
  let counts=new Map(),allCounts=new Map(),windowSuppressed=0;
  const count=(map,key)=>{if(map.has(key)||map.size<256)map.set(key,(map.get(key)??0)+1);};
  const top=(map,n=3)=>[...map].sort((a,b)=>b[1]-a[1]).slice(0,n).map(([message,count])=>({message,count}));
  const said=list=>list.map(t=>`"${t.message.length>100?t.message.slice(0,100)+'…':t.message}" ×${t.count}`).join(', ');
  const flushRepeats=at=>{
    if(repeats>=inARow){
      const n=repeats-inARow+1;
      write(lastLevel,[`${name}: … the line above repeated ${n} more time${n===1?'':'s'} in ${((at-repeatSince)/1000).toFixed(1)} s`]);
    }
    repeats=0;
  };
  const summary=at=>{
    if(windowSuppressed)write('warn',[`${name}: LOG FLOOD: ${windowSuppressed} lines held back in the last ${Math.round(windowMs/1000)} s; most said: ${said(top(counts))} (every line: --log-all or FOAFNAUT_LOG=all)`]);
  };
  const roll=at=>{
    if(at-windowAt<windowMs)return;
    if(stats.tripped){
      summary(at);
      // a window under budget: lines are written again
      if(inWindow<=perWindow){stats.tripped=false;write('warn',[`${name}: log flood over; lines are written again`]);}
    }
    windowAt=at;inWindow=0;windowSuppressed=0;counts=new Map();
  };
  const trip=at=>{
    stats.tripped=true;stats.trips++;
    const offenders=top(counts);
    write('warn',[`${name}: LOG FLOOD: more than ${inSecond>perSecond?`${perSecond} lines in a second`:`${perWindow} lines in ${Math.round(windowMs/1000)} s`}; most said: ${said(offenders)}. A summary every ${Math.round(windowMs/1000)} s follows instead of the lines (every line: --log-all or FOAFNAUT_LOG=all).`]);
    onTrip?.({at,top:offenders,lines:stats.lines});
  };
  /** One line: its level and console arguments. Answers whether it was written. */
  const line=(level,args)=>{
    const text=args.length===1&&typeof args[0]==='string'?args[0]:args.map(a=>typeof a==='string'?a:String(a?.message??a)).join(' ');
    if(all){stats.lines++;stats.written++;write(level,args);return true;}
    if(text.charCodeAt(0)===123&&text.charCodeAt(text.length-1)===125){stats.traces++;write(level,args);return true;}
    stats.lines++;
    const at=now();
    roll(at);
    if(at-secondAt>=1000){secondAt=at;inSecond=0;}
    inSecond++;inWindow++;
    const key=messageKey(text);
    count(counts,key);count(allCounts,key);
    if(!stats.tripped&&(inSecond>perSecond||inWindow>perWindow))trip(at);
    if(stats.tripped){stats.suppressed++;windowSuppressed++;if(text!==last){last=text;repeats=0;}return false;}
    if(text===last){
      repeats++;
      if(repeats===inARow)repeatSince=at;
      if(repeats>=inARow){stats.collapsed++;return false;}
    } else {
      flushRepeats(at);last=text;lastLevel=level;
    }
    stats.written++;write(level,args);return true;
  };
  return {
    line,
    /** Write every line from now (`true`), or gate them again. */
    setAll(on){all=!!on;},
    /** Write what is held (a repeat count, the summary of a flood): at exit. */
    flush(){const at=now();flushRepeats(at);if(stats.tripped)summary(at);windowSuppressed=0;},
    /** The counts: lines, written, held back (suppressed in a flood, collapsed repeats), trips, the most said. */
    stats:()=>({lines:stats.lines,written:stats.written,suppressed:stats.suppressed,collapsed:stats.collapsed,traces:stats.traces,
      trips:stats.trips,tripped:stats.tripped,top:top(allCounts)}),
  };
}

/** Put the gate in front of a console's log, info, warn, error and debug. Answers the gate;
`restore()` puts the console back.
 * @param {Console} [target]
 * @param {Parameters<typeof createLogGate>[0]} [options] */
export function gateConsole(target=console,options={}) {
  const original={};
  for(const level of ['log','info','warn','error','debug'])original[level]=target[level].bind(target);
  const gate=createLogGate({...options,write:(level,args)=>(original[level]??original.log)(...args)});
  for(const level of Object.keys(original))target[level]=(...args)=>{gate.line(level,args);};
  return Object.assign(gate,{restore(){gate.flush();Object.assign(target,original);},original});
}
