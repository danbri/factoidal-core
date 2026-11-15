// One survey against the one before: a Markdown table with the change of each number, the
// regressions, and rows for the trend file. Exit 1 when a page crashed (a crash or an exit of
// the browser is a hard failure); every other regression is a warning.
//
//   deno run --allow-read --allow-write labs/demos/foafnaut/realpages/compare.ts --current summary.json
//     [--previous summary.json] [--markdown OUT.md] [--trend trend.csv] [--run-id ID] [--run-url URL] [--annotate]
//     [--informational]
// --informational (the live survey: the network and the pages change under it): a crash is a
// warning too, and the exit is 0. The offline survey (snapshots) is the gate.
//
// Regressions: a crash or a tripped log gate (exit 1); a verdict worse than before (unreachable, before or now, is not one: it
// is the network); a number over 1.5 times its previous value and more than its noise floor
// above it; layout similarity down by more than 0.05.
import {VERDICT_RANK,type Verdict} from "./metrics.ts";

type Row=Record<string,unknown>&{id:string;verdict:Verdict;state:string};
export type Summary={platform:string;mode?:string;release:string|null;engine:{sha256:string};host:{commit:string|null;shot_at_end:boolean;liberal_report:boolean};
  started:string;totals:Record<string,number>;pages:Row[]};

/** Field, column title, noise floor (an increase below it is never a regression). */
const MAC:[string,string,number][]=[
  ["first_frame_s","First frame s",1],["first_layout_ms","First layout ms",50],["gpu_p50_ms","GPU/frame p50 ms",10],
  ["cpu_idle_pct","Idle CPU %",10],["script_turn_max_ms","Longest script turn ms",100],
  ["scroll_latency_p50_ms","Scroll p50 ms",50],["scroll_latency_p95_ms","Scroll p95 ms",50],["rss_peak_mb","RSS MB",200],
];
const LINUX:[string,string,number][]=[
  ["first_frame_s","First render s",1],["load_ms","Load ms",300],["first_layout_ms","Layout ms",50],["cpu_s","CPU s",1],["rss_peak_mb","RSS MB",200],
];
export const fieldsOf=(platform:string)=>platform==="macos"?MAC:LINUX;

const fmt=(v:unknown)=>v===null||v===undefined?"":typeof v==="number"?(Math.abs(v)>=100?Math.round(v).toLocaleString("en-GB"):String(Math.round(v*10)/10)):String(v);
const delta=(now:unknown,was:unknown)=>{
  if(typeof now!=="number"||typeof was!=="number")return "";
  if(was===0)return now===0?"":" (was 0)";
  const pct=Math.round(100*(now-was)/was);
  return pct===0?"":` (${pct>0?"+":""}${pct}%)`;
};

export type Finding={level:"error"|"warning"|"note";page:string;text:string};
export function findings(cur:Summary,prev?:Summary):Finding[]{
  const out:Finding[]=[];
  const before=new Map((prev?.pages??[]).map(r=>[r.id,r]));
  for(const r of cur.pages){
    const p=before.get(r.id);
    if(r.state==="crash"){out.push({level:"error",page:r.id,text:`crash: ${r.crash_reason??"exit"}`+(p&&p.state==="crash"?" (crashed before too)":p?" (new)":"")});continue;}
    if(r.verdict==="unreachable"){out.push({level:"note",page:r.id,text:`unreachable: ${r.unreachable_reason??""}`});continue;}
    // A tripped log gate (a flood of console lines) is a failure, as a crash is: output that
    // hogs the terminal and the loop is a resource fault (offline; a warning live).
    if(typeof r.log_floods==="number"&&r.log_floods>0)out.push({level:"error",page:r.id,text:`log gate tripped ${r.log_floods} time(s)${r.log_flood_top?`: ${r.log_flood_top}`:""}`});
    if(!p||p.verdict==="unreachable")continue;
    if(VERDICT_RANK[r.verdict]>VERDICT_RANK[p.verdict])out.push({level:"warning",page:r.id,text:`verdict ${p.verdict} -> ${r.verdict}`});
    for(const [k,title,floor] of fieldsOf(cur.platform)){
      const a=r[k],b=p[k];
      if(typeof a==="number"&&typeof b==="number"&&a>1.5*b&&a-b>floor)out.push({level:"warning",page:r.id,text:`${title}: ${fmt(b)} -> ${fmt(a)}`});
    }
    const s=r.layout_similarity,t=p.layout_similarity;
    if(typeof s==="number"&&typeof t==="number"&&t-s>0.05)out.push({level:"warning",page:r.id,text:`layout similarity ${t} -> ${s}`});
  }
  return out;
}

export function markdown(cur:Summary,prev?:Summary):string{
  const before=new Map((prev?.pages??[]).map(r=>[r.id,r]));
  const fields=fieldsOf(cur.platform);
  const extra=cur.platform==="macos"?["Skips","Layout similarity"]:["Rows","Links"];
  const lines=[
    `Real-page survey, ${cur.platform}, ${cur.mode??"live"}, ${cur.release??"engine "+cur.engine.sha256.slice(0,12)} (host ${cur.host.commit?.slice(0,9)??"?"}${cur.platform==="macos"&&!cur.host.shot_at_end?", picture at first idle frame":""}${cur.platform==="macos"&&!cur.host.liberal_report?", skips not reported by this host":""})`+
      (prev?`; changes against ${prev.release??prev.engine.sha256.slice(0,12)}`:"; no previous survey"),"",
    `| Page | Verdict | ${fields.map(f=>f[1]).join(" | ")} | ${extra.join(" | ")} |`,
    `|---|---|${fields.map(()=>"---:").join("|")}|${extra.map(()=>"---:").join("|")}|`,
  ];
  for(const r of cur.pages){
    const p=before.get(r.id);
    const verdict=r.verdict+(p&&p.verdict!==r.verdict?` (was ${p.verdict})`:"");
    const cells=fields.map(([k])=>fmt(r[k])+delta(r[k],p?.[k]));
    const ex=cur.platform==="macos"
      ?[r.skips_count===null||r.skips_count===undefined?"":String(r.skips_count),fmt(r.layout_similarity)+(typeof r.layout_similarity==="number"&&typeof p?.layout_similarity==="number"&&r.layout_similarity!==p.layout_similarity?` (was ${p.layout_similarity})`:"")]
      :[fmt(r.rows),fmt(r.links)];
    lines.push(`| ${r.id} | ${verdict} | ${cells.join(" | ")} | ${ex.join(" | ")} |`);
  }
  const t=cur.totals;
  lines.push("",`Totals: ${t.pages} pages; usable ${t.usable}, slow ${t.slow}, unusable ${t.unusable}, blank ${t.blank}, timeout ${t.timeout}, crash ${t.crash}, unreachable ${t.unreachable}.`);
  const fs=findings(cur,prev);
  if(fs.length){lines.push("","Findings:");for(const f of fs)lines.push(`- ${f.level}: ${f.page}: ${f.text}`);}
  return lines.join("\n")+"\n";
}

export const TREND_COLUMNS=["run_id","run_url","started","platform","mode","release","engine_sha256","host_commit","page","state","verdict",
  "first_frame_s","first_layout_ms","prims","gpu_p50_ms","cpu_idle_pct","script_turn_max_ms","scroll_latency_p50_ms","scroll_latency_p95_ms",
  "rss_peak_mb","skips_count","layout_similarity","load_ms","cpu_s","log_floods","crash_reason"];
export function trendRows(cur:Summary,runId:string,runUrl:string):string[]{
  const q=(v:unknown)=>{const s=v===null||v===undefined?"":String(v);return /[",\n]/.test(s)?`"${s.replaceAll('"','""')}"`:s;};
  return cur.pages.map(r=>TREND_COLUMNS.map(c=>q(({run_id:runId,run_url:runUrl,started:cur.started,platform:cur.platform,mode:cur.mode??"live",release:cur.release,
    engine_sha256:cur.engine.sha256,host_commit:cur.host.commit,page:r.id} as Record<string,unknown>)[c]??r[c])).join(","));
}

if(import.meta.main){
  const a=Deno.args,opt=(n:string)=>{const i=a.indexOf(n);return i<0?undefined:a[i+1];};
  const cur=JSON.parse(await Deno.readTextFile(opt("--current")!)) as Summary;
  const prevPath=opt("--previous");
  let prev:Summary|undefined;
  if(prevPath)try{prev=JSON.parse(await Deno.readTextFile(prevPath));}catch{/* no previous survey */}
  const md=markdown(cur,prev);
  console.log(md);
  if(opt("--markdown"))await Deno.writeTextFile(opt("--markdown")!,md);
  if(opt("--trend")){
    const path=opt("--trend")!;
    const exists=await Deno.stat(path).then(()=>true,()=>false);
    await Deno.writeTextFile(path,(exists?"":TREND_COLUMNS.join(",")+"\n")+trendRows(cur,opt("--run-id")??"local",opt("--run-url")??"").join("\n")+"\n",{append:true});
  }
  const info=a.includes("--informational");
  const fs=findings(cur,prev).map(f=>info&&f.level==="error"?{...f,level:"warning" as const}:f);
  if(a.includes("--annotate"))for(const f of fs)if(f.level!=="note")console.log(`::${f.level}::${cur.mode??"live"} ${f.page}: ${f.text}`);
  if(fs.some(f=>f.level==="error"))Deno.exitCode=1;
}
