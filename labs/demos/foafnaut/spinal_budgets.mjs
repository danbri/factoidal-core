// Budgets of fixtures/spinal-perf/budgets.json (core issue 450), for spinal_perf_test.ts (Deno,
// the native run) and hub_spinal_perf.mjs (Node, the Hub run). Plain JavaScript so that both load it.
//
// A budget is {max} or {min} on a metric named by a dot path into a run's JSON
// ("tick.engine_ms.median"). A known failure is {want_max} or {want_min} that the run does not
// meet today: it is reported, not hidden, and when the run meets it the check fails so that the
// entry moves to the budgets and its issue is updated.

/** The value at a dot path, or undefined. */
export const at=(run,metric)=>metric.split('.').reduce((o,k)=>o==null?undefined:o[k],run);

/** Each budget against the run: [{metric, kind, limit, value, ok}]. A missing value fails. */
export function checkBudgets(budgets,run){
  const out=[];
  for(const [metric,b] of Object.entries(budgets)){
    if(!b||typeof b!=='object')continue;
    const value=at(run,metric);
    for(const kind of ['max','min'])if(typeof b[kind]==='number'){
      const ok=typeof value==='number'&&Number.isFinite(value)&&(kind==='max'?value<=b[kind]:value>=b[kind]);
      out.push({metric,kind,limit:b[kind],value,ok});
    }
  }
  return out;
}

/** Each known failure against the run: [{metric, want, value, stillFails, issue}]. */
export function knownFailures(known,run){
  const out=[];
  for(const [metric,k] of Object.entries(known)){
    const value=at(run,metric);
    const meets=typeof value==='number'&&(typeof k.want_max==='number'?value<=k.want_max:typeof k.want_min==='number'?value>=k.want_min:false);
    out.push({metric,want:typeof k.want_max==='number'?`<= ${k.want_max}`:`>= ${k.want_min}`,value,stillFails:!meets,issue:k.issue});
  }
  return out;
}

/** The ratchet: budgets may only tighten. For each section of `before` (a JSON object of the
file at the merge base) every budget must still be there with a max no higher and a min no
lower, unless the entry's `accepted` text is new (a cost taken on purpose, said why). A known
failure may go only when its metric is now a budget. Returns the violations as text. */
export function ratchet(before,after){
  const bad=[];
  for(const section of ['native','hub']){
    const was=before[section]?.budgets??{},now=after[section]?.budgets??{};
    for(const [metric,b] of Object.entries(was)){
      if(!b||typeof b!=='object'||(typeof b.max!=='number'&&typeof b.min!=='number'))continue;
      const n=now[metric];
      const accepted=n?.accepted&&n.accepted!==b.accepted;
      if(!n){bad.push(`${section} ${metric}: budget removed`);continue;}
      if(typeof b.max==='number'&&!(typeof n.max==='number'&&n.max<=b.max)&&!accepted)bad.push(`${section} ${metric}: max ${b.max} -> ${n.max}`);
      if(typeof b.min==='number'&&!(typeof n.min==='number'&&n.min>=b.min)&&!accepted)bad.push(`${section} ${metric}: min ${b.min} -> ${n.min}`);
    }
    const knownWas=before[section]?.known_failures??{},knownNow=after[section]?.known_failures??{};
    for(const metric of Object.keys(knownWas))
      if(!(metric in knownNow)&&!(metric in now))bad.push(`${section} known failure ${metric} removed without a budget for it`);
  }
  return bad;
}
