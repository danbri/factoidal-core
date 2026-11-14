// Scores a round: per page and engine, the facts and likeness numbers -> results.csv, summary.md, scores.json.
// deno run -A tests/realpages/score.ts --work DIR --round NAME [--threshold 0.5]
const a=Deno.args,opt=(n:string,d?:string)=>{const i=a.indexOf(n);return i<0?d:a[i+1];};
const H=new URL(".",import.meta.url).pathname.replace(/\/$/,"");
// The work folder (scratch; never committed): rounds/<round>/... written by run_all.ts.
const R=opt("--work")??Deno.env.get("REALPAGES_WORK")!;
const round=opt("--round")!,TH=Number(opt("--threshold","0.5"));
const pages:{id:string;url:string;kind:string}[]=JSON.parse(await Deno.readTextFile(`${H}/pages.json`));
const readJ=async(f:string)=>{try{return JSON.parse(await Deno.readTextFile(f));}catch{return undefined;}};
type Facts={w:number;h:number;ocr:{t:string;x:number;y:number;w:number;h:number;c:number}[];grid:{gw:number;gh:number;rgb:number[]}};
// ---- text likeness ----
const words=(s:string)=>s.toLowerCase().normalize("NFKD").replace(/[^\p{L}\p{N}]+/gu," ").trim().split(" ").filter(w=>w.length>=2);
/** T: share of the reference's OCR characters (words of 2+ letters) found in engine OCR lines near the same place
 (top-left within DX/DY px, line height within a factor 1.6). Tany: the same, anywhere in the viewport. */
function textScore(ref:Facts,eng:Facts,DX=64,DY=64){
  const refLines=ref.ocr.filter(l=>l.c>=0.3&&words(l.t).length);
  let total=0,near=0,any=0;
  const allEng=new Map<string,number>();for(const l of eng.ocr)for(const w of words(l.t))allEng.set(w,(allEng.get(w)??0)+1);
  for(const r of refLines){
    const bag=new Map<string,number>();
    for(const e of eng.ocr){
      if(Math.abs(e.y-r.y)>DY)continue;
      const hx=e.x<=r.x+r.w&&e.x+e.w>=r.x; // horizontal overlap
      if(!hx&&Math.abs(e.x-r.x)>DX)continue;
      const hr=Math.max(e.h,1)/Math.max(r.h,1);if(hr>1.6||hr<1/1.6)continue;
      for(const w of words(e.t))bag.set(w,(bag.get(w)??0)+1);
    }
    for(const w of words(r.t)){total+=w.length;
      if((bag.get(w)??0)>0){near+=w.length;bag.set(w,bag.get(w)!-1);}
      if(allEng.has(w))any+=w.length;}
  }
  return total?{T:near/total,Tany:any/total,refChars:total}:{T:null,Tany:null,refChars:0};
}
// ---- links ----
const normURL=(u:string,base?:string)=>{try{const x=new URL(u,base);x.hash="";return x.href.replace(/\/$/,"");}catch{return u;}};
/** L: share of the reference's visible links in the first screen (by URL) that the engine drew as a link region to the
 same URL with its centre within 64 px of the reference's in both directions. */
function linkScore(refLinks:any[],engLinks:any[],bandTop:number,base:string){
  const refs=refLinks.filter(l=>l[3]>2&&l[4]>2&&l[2]>=0&&l[2]<935);
  if(refs.length<3)return {L:null,refLinks:refs.length};
  const eng=engLinks.map(l=>({u:normURL(String(l[0]),base),cx:l[1]+l[3]/2,cy:l[2]+bandTop+l[4]/2}));
  let m=0;
  for(const r of refs){const u=normURL(r[0]),cx=r[1]+r[3]/2,cy=r[2]+r[4]/2;
    if(eng.some(e=>e.u===u&&Math.abs(e.cx-cx)<=64&&Math.abs(e.cy-cy)<=64))m++;}
  return {L:m/refs.length,refLinks:refs.length};
}
// ---- colour ----
const lab=(r:number,g:number,b:number)=>{const f=(c:number)=>{c/=255;return c<=0.04045?c/12.92:((c+0.055)/1.055)**2.4;};
  const [R,G,B]=[f(r),f(g),f(b)],X=(R*0.4124+G*0.3576+B*0.1805)/0.95047,Y=R*0.2126+G*0.7152+B*0.0722,Z=(R*0.0193+G*0.1192+B*0.9505)/1.08883;
  const h=(t:number)=>t>0.008856?Math.cbrt(t):7.787*t+16/116;return [116*h(Y)-16,500*(h(X)-h(Y)),200*(h(Y)-h(Z))];};
/** average the 128-wide grid down by k (cells of 10 px -> 10k px) */
function coarse(g:Facts["grid"],k:number,rows:number){const gw=Math.floor(g.gw/k),gh=Math.min(Math.floor(g.gh/k),rows);const out:number[][]=[];
  for(let y=0;y<gh;y++)for(let x=0;x<gw;x++){let s=[0,0,0];for(let dy=0;dy<k;dy++)for(let dx=0;dx<k;dx++){const i=((y*k+dy)*g.gw+x*k+dx)*3;s[0]+=g.rgb[i];s[1]+=g.rgb[i+1];s[2]+=g.rgb[i+2];}
    out.push(s.map(v=>v/(k*k)));}return out;}
/** C: share of 40 px cells whose mean colour agrees (CIE76 dE <= 15); Cn: the same, rescaled so that a plain page of the
 reference's most common cell colour scores 0 and the reference itself 1 (clamped at 0). */
function colourScore(ref:Facts,eng:Facts){
  const rows=Math.min(Math.floor(ref.grid.gh/4),Math.floor(eng.grid.gh/4));
  const A=coarse(ref.grid,4,rows),B=coarse(eng.grid,4,rows);const n=Math.min(A.length,B.length);if(!n)return {C:null,Cn:null};
  const LA=A.map(c=>lab(c[0],c[1],c[2])),LB=B.map(c=>lab(c[0],c[1],c[2]));
  const dE=(p:number[],q:number[])=>Math.hypot(p[0]-q[0],p[1]-q[1],p[2]-q[2]);
  let agree=0;for(let i=0;i<n;i++)if(dE(LA[i],LB[i])<=15)agree++;
  // the plain page: the commonest reference cell colour (quantised)
  const cnt=new Map<string,{n:number;c:number[]}>();for(const c of LA){const k=c.map(v=>Math.round(v/8)).join(",");const e=cnt.get(k)??{n:0,c};e.n++;cnt.set(k,e);}
  const mode=[...cnt.values()].sort((x,y)=>y.n-x.n)[0].c;let base=0;for(let i=0;i<n;i++)if(dE(LA[i],mode)<=15)base++;
  // Cn (Youden's J): agreement on the cells the reference paints in another colour than its plain one, plus agreement
  // on its plain cells, minus 1. A plain page of the main colour scores 0, the reference 1; n/a when under 3% of cells are not plain.
  let np=0,npOK=0,pl=0,plOK=0;for(let i=0;i<n;i++){const ok=dE(LA[i],LB[i])<=15;if(dE(LA[i],mode)<=15){pl++;if(ok)plOK++;}else{np++;if(ok)npOK++;}}
  const C=agree/n,B0=base/n;return {C,Cn:np<0.03*n||!pl?null:Math.max(0,npOK/np+plOK/pl-1),plain:B0};
}
// ---- plain image similarity: mean SSIM over 8x8 windows of the 10 px grey grid ----
function grey(g:Facts["grid"],rows:number){const o:number[]=[];for(let i=0;i<g.gw*rows;i++)o.push(0.299*g.rgb[i*3]+0.587*g.rgb[i*3+1]+0.114*g.rgb[i*3+2]);return o;}
function ssim(ref:Facts,eng:Facts){
  const rows=Math.min(ref.grid.gh,eng.grid.gh),W=ref.grid.gw,A=grey(ref.grid,rows),B=grey(eng.grid,rows);
  const C1=(0.01*255)**2,C2=(0.03*255)**2;let s=0,n=0;
  for(let y=0;y+8<=rows;y+=4)for(let x=0;x+8<=W;x+=4){let ma=0,mb=0;for(let dy=0;dy<8;dy++)for(let dx=0;dx<8;dx++){ma+=A[(y+dy)*W+x+dx];mb+=B[(y+dy)*W+x+dx];}
    ma/=64;mb/=64;let va=0,vb=0,cv=0;for(let dy=0;dy<8;dy++)for(let dx=0;dx<8;dx++){const p=A[(y+dy)*W+x+dx]-ma,q=B[(y+dy)*W+x+dx]-mb;va+=p*p;vb+=q*q;cv+=p*q;}
    va/=63;vb/=63;cv/=63;s+=((2*ma*mb+C1)*(2*cv+C2))/((ma*ma+mb*mb+C1)*(va+vb+C2));n++;}
  return n?s/n:null;
}
/** share of 10 px cells that changed (grey difference > 12) between two pictures; region: [x0,y0,x1,y1] in px */
function changed(p:Facts,q:Facts,region?:number[]){const rows=Math.min(p.grid.gh,q.grid.gh),W=p.grid.gw,A=grey(p.grid,rows),B=grey(q.grid,rows);
  let c=0,n=0;for(let y=0;y<rows;y++)for(let x=0;x<W;x++){if(region&&(x*10+10<region[0]||x*10>region[2]||y*10+10<region[1]||y*10>region[3]))continue;n++;if(Math.abs(A[y*W+x]-B[y*W+x])>12)c++;}
  return n?c/n:0;}
const med=(v:number[])=>{if(!v.length)return null;const s=[...v].sort((x,y)=>x-y);const m=s.length>>1;return s.length%2?s[m]:(s[m-1]+s[m])/2;};
const engines=new Set<string>();const rows:any[]=[];
for(const p of pages){
  const D=`${R}/rounds/${round}/${p.id}`;const ref=await readJ(`${D}/chrome.json`);
  if(!ref)continue;
  const cf:Record<string,Facts|undefined>={};for(const n of ["load","scroll","pretype","type","link"])cf[n]=await readJ(`${D}/c-${n}.facts.json`);
  for await(const ent of Deno.readDir(D)){if(!ent.isDirectory)continue;const sha=ent.name;const E=`${D}/${sha}`;const ej=await readJ(`${E}/engine.json`);if(!ej)continue;engines.add(sha);
    const ef:Record<string,Facts|undefined>={};for(const n of ["load","scroll","pretype","type","link"])ef[n]=await readJ(`${E}/e-${n}.facts.json`);
    const shot=(n:string)=>ej.shots.find((s:any)=>String(s.file).endsWith(`/e-${n}.png`));
    const load=shot("load");
    // navigation start: the end of the page's own fetch minus its time
    const log=await Deno.readTextFile(`${E}/engine.log`).catch(()=>"");
    const lines=log.split("\n").map(l=>{const m=/^\s*(\d+) (\{.*)$/.exec(l);if(!m)return undefined;try{return {t:Number(m[1]),j:JSON.parse(m[2])};}catch{return undefined;}}).filter(Boolean) as {t:number;j:any}[];
    const fetches=lines.filter(l=>l.j.type==="rp-fetch");
    const navStart=fetches.length?fetches[0].t-fetches[0].j.ms:null;
    const loadFetches=load?fetches.filter(l=>l.t<=load.at):fetches;
    const kind=(f:any)=>/css/.test(f.j.ctype)?"sheet":/^image\//.test(f.j.ctype)?"image":/javascript|ecmascript/.test(f.j.ctype)?"script":/font|woff|ttf|otf/.test(f.j.ctype)?"font":/html/.test(f.j.ctype)?"html":"other";
    const eFetch:Record<string,{ok:number;failed:number}>={};for(const f of loadFetches){const k=kind(f);const e=eFetch[k]??={ok:0,failed:0};if(f.j.status>=200&&f.j.status<400)e.ok++;else e.failed++;}
    // crash: ended by a signal we did not send, or a panic/stack overflow in its output; exitError: the host stopped with an error
    const crashed=(ej.exit.signal!==null&&!ej.exit.killed)||(ej.panic?.length??0)>0;
    const exitError=!crashed&&ej.exit.code!==0&&!ej.exit.killed;
    const cause=crashed?"crash":ej.exit.killed?String(ej.exit.killed):exitError?`host error: ${(ej.stderrSample??[]).find((l:string)=>/Error/.test(l))?.slice(0,120)??"exit "+ej.exit.code}`:"";
    const killedBy=ej.exit.killed as string|null;
    const hung=!!killedBy&&/no picture|total limit/.test(killedBy),mem=!!killedBy&&/memory/.test(killedBy);
    const refused=(ej.refused?.length??0)>0||(ej.firstPictureMs===null&&!killedBy&&ej.exit.code!==0);
    const picture=ej.firstPictureMs!==null&&!!ef.load;
    const loadOK=picture&&!crashed&&!exitError&&!mem&&!refused&&!(killedBy&&!load);
    const partial=!!ef.load?.ocr.some(l=>/partial page/i.test(l.t));
    const ts=cf.load&&ef.load?textScore(cf.load,ef.load):{T:null,Tany:null,refChars:0};
    const ls=load?linkScore(ref.dom?.links??[],load.links??[],load.bandTop??0,load.url??p.url):{L:null,refLinks:0};
    const cs=cf.load&&ef.load?colourScore(cf.load,ef.load):{C:null,Cn:null};
    const S=cf.load&&ef.load?ssim(cf.load,ef.load):null;
    const parts=[ts.T,ls.L,cs.Cn].filter((v):v is number=>v!==null&&v!==undefined);
    const likeness=loadOK&&parts.length?parts.reduce((x,y)=>x+y,0)/parts.length:0;
    // interaction smoke
    const steps:Record<string,string>={};
    const cScrolled=(ref.scrollY??0)>0,eScrollShot=shot("scroll");
    const eScrolled=!!eScrollShot&&eScrollShot.scroll>0&&!!ef.scroll&&!!ef.load&&changed(ef.load,ef.scroll)>0.02;
    steps.scroll=!cScrolled?"n/a":eScrolled?"pass":"fail";
    if(ref.dom?.input){const cT=!!cf.pretype&&!!cf.type&&changed(cf.pretype,cf.type)>0;const b=ref.dom.input.box,reg=[b[0]-40,b[1]-30,b[0]+b[2]+40,b[1]+b[3]+30];
      const eT=!!ef.pretype&&!!ef.type&&changed(ef.pretype,ef.type,reg)>0;steps.type=!cT?"n/a":eT?"pass":"fail";}
    else steps.type="n/a";
    if(ref.dom?.firstLink&&ref.linkNavigated){const lk=ej.link?.[0],nv=ej.nav?.[0];
      const same=normURL(ref.dom.firstLink.href)===normURL(p.url);
      steps.link=!lk?.found?"fail (link not drawn)":same?(ef.link?"pass":"fail (no picture)"):!nv?.moved?"fail (no navigation)":normURL(nv.url)!==normURL(ref.linkUrl)&&normURL(nv.url)!==normURL(ref.dom.firstLink.href)?"fail (other page)":!ef.link?"fail (no picture)":"pass";}
    else steps.link="n/a";
    const smoke=loadOK&&!crashed&&!exitError&&!killedBy&&Object.values(steps).every(s=>s==="pass"||s==="n/a");
    const rel=(t:number|null|undefined)=>t!=null&&navStart!==null?t-navStart:null;
    const lc=load?.console??{};
    rows.push({page:p.id,kind:p.kind,url:p.url,engine:sha,
      loadOK,cause,crashed,exitError,refused,hung,memLimit:mem,killedBy,exitCode:ej.exit.code,partial,picture,
      firstPictureMs:rel(ej.firstPictureMs),settledMs:ej.settled?rel(ej.settledMs):null,settled:ej.settled,peakMiB:ej.peakMiB,
      chromeFirstPictureMs:ref.firstPictureMs,chromeSettledMs:ref.settledMs,
      T:ts.T,Tany:ts.Tany,L:ls.L,refLinks:ls.refLinks,C:cs.C,Cn:cs.Cn,S,likeness,
      smoke,scroll:steps.scroll,type:steps.type,link:steps.link,
      sysErrors:(lc["System:error"]??0),sysWarnings:(lc["System:warning"]??0),pageErrors:(lc["page:error"]??0),pageLogs:Object.entries(lc).filter(([k])=>k.startsWith("page:")&&k!=="page:error").reduce((s,[,v])=>s+(v as number),0),
      chromeConsole:Object.entries(ref.console??{}).map(([k,v])=>`${k}=${v}`).join(" "),
      namedSheets:ref.dom?.named?.sheets??null,namedImages:ref.dom?.named?.images??null,namedScripts:ref.dom?.named?.scripts??null,
      chromeSheets:ref.requests?.Stylesheet?.ok??0,chromeImages:ref.requests?.Image?.ok??0,chromeScripts:ref.requests?.Script?.ok??0,
      engSheets:eFetch.sheet?.ok??0,engSheetsFailed:eFetch.sheet?.failed??0,engImages:eFetch.image?.ok??0,engImagesFailed:eFetch.image?.failed??0,
      engScripts:eFetch.script?.ok??0,engScriptsFailed:eFetch.script?.failed??0,engFonts:eFetch.font?.ok??0,
    });
  }
}
const cols=Object.keys(rows[0]??{});
const csv=(v:unknown)=>{const s=v===null||v===undefined?"":typeof v==="number"?String(Math.round(v*1000)/1000):String(v);return /[",\n]/.test(s)?`"${s.replace(/"/g,'""')}"`:s;};
await Deno.writeTextFile(`${R}/results-${round}.csv`,[cols.join(","),...rows.map(r=>cols.map(c=>csv(r[c])).join(","))].join("\n")+"\n");
await Deno.writeTextFile(`${R}/scores-${round}.json`,JSON.stringify(rows,null,1));
// headline per engine
const LIMIT=180000;const head:string[]=[];
for(const e of engines){const rs=rows.filter(r=>r.engine===e);const n=rs.length;
  const settledAll=rs.map(r=>r.loadOK&&r.settledMs!==null?r.settledMs:LIMIT);
  head.push(`| ${e} | ${n} | ${rs.filter(r=>r.loadOK).length} | ${rs.filter(r=>r.likeness>=TH).length} | ${(med(settledAll)!/1000).toFixed(1)} s | ${rs.filter(r=>r.smoke).length} | ${rs.filter(r=>r.crashed).length} / ${rs.filter(r=>r.exitError).length} / ${rs.filter(r=>r.hung).length} / ${rs.filter(r=>r.memLimit).length} | ${(med(rs.map(r=>r.likeness))??0).toFixed(2)} |`);}
console.log(`| engine | pages | load, no crash or refusal | likeness >= ${TH} | median settled | interaction smoke | crash / host error / limit (time) / memory | median likeness |`);
console.log("|---|---|---|---|---|---|---|---|");console.log(head.join("\n"));
