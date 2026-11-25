// Everyday use in the window (docs/foafnaut-daily-use.md): what a person does first in a new
// browser, run off screen through the window's real event queue against a local site
// (daily_use_server.ts): follow a link, go back, reload; see a server's "not found" page; start
// on an address that does not answer; type in a search box and press Enter; press a form's
// button; post a form; sign in with a cookie, quit and start again still signed in; open a link
// in a new tab; download a file.
//
// Each case is run_html.ts --steps (the sweep language: "tap:X,Y" in page rows, "type:TEXT",
// "title=X", "url:X", "tabs=N:A", key letters as Command shortcuts). A case with a `gap` is a
// shortfall that is open: it must fail today (XFAIL); when it passes (XPASS) the check fails, so
// the gap and its test are closed together (as showcase_gaps_test.ts).
//
// Usage: deno run -A --unstable-ffi --unstable-webgpu daily_use_check.ts [run_html args...]
// (test.sh passes --native-engine when the library is built). `--only NAME` runs one case.
// Exit 0 when every case is PASS or XFAIL.
import {handle} from "./daily_use_server.ts";

const lab=new URL(".",import.meta.url).pathname;
type Case={name:string;start:string;steps:(string|number[])[];gap?:string;
  /** A check after the run, with the downloads folder: a failure's text, or undefined. */
  after?:(downloads:string)=>Promise<string|undefined>};
// The page rows of the local site: the server lays fields out in CSS pixels at fixed places,
// and the window draws pages at two backing pixels to the CSS pixel off screen.
const at=(x:number,y:number)=>`tap:${x*2},${y*2}`;
const field=at(240,60),go=at(520,60);
const cases:Case[]=[
  {name:"link, back, reload",start:"/links.html",steps:[at(75,58),"title=Results: same","[","title=Links","r","title=Links"]},
  {name:"a server's 404 page is shown",start:"/links.html",steps:[at(75,298),"url:/missing","title=Not here"]},
  {name:"a start address that does not answer shows an error page",start:"http://127.0.0.1:9/",steps:["hold","title=Page refused"]},
  {name:"a redirect is followed",start:"/redirect",steps:["title=Results: moved"]},
  {name:"type in a search box with no script, press Enter",start:"/search.html",steps:["hold",field,"hold","type:hello",[5,36,0],"title=Results: hello"]},
  {name:"type in a search box, press its button",start:"/search-scripted.html",steps:["hold",field,"hold","type:two words",go,"title=Results: two words"]},
  {name:"post a form",start:"/post.html",steps:["hold",field,"hold","type:hi",[5,36,0],"title=Results: posted hi"]},
  {name:"sign in: the cookie is kept",start:"/login.html",steps:["hold",field,"hold","type:me",[5,36,0],"title=Signed in"]},
  // the same cookie file as the case before: the program was quit and started again
  {name:"after a restart, still signed in",start:"/me",steps:["title=Signed in"]},
  {name:"a target=_blank link opens a new tab",start:"/links.html",steps:[at(75,138),"hold","tabs=2:1","title=Results: blank"],
    gap:"a link's target is not read by the window: _blank opens in the same tab (docs/foafnaut-daily-use.md)"},
  {name:"a download is saved, the page stays",start:"/links.html",steps:[at(75,218),"hold","hold","hold","url:/links.html","title=Links"],
    after:async dir=>{try{const size=(await Deno.stat(`${dir}/file.bin`)).size;return size===1024?undefined:`file.bin has ${size} bytes`;}catch{return "no file.bin in the downloads folder";}}},
];

const args=[...Deno.args];
const onlyAt=args.indexOf("--only");
const only=onlyAt>=0?args.splice(onlyAt,2)[1]:undefined;
const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},handle);
const origin=`http://127.0.0.1:${server.addr.port}`;
const dir=await Deno.makeTempDir({prefix:"foafnaut-daily-"});
let bad=0;
const results:string[]=[];
for(const c of cases){
  if(only&&c.name!==only)continue;
  const file=`${dir}/steps.json`,downloads=await Deno.makeTempDir({dir,prefix:"downloads-"});
  // one cookie file for the whole check, as one person's browser: the sign-in case sets it,
  // the restart case reads it
  await Deno.writeTextFile(file,JSON.stringify(c.steps));
  const start=c.start.startsWith("http")?c.start:origin+c.start;
  const t0=performance.now();
  const out=await new Deno.Command("perl",{args:["-e","alarm shift; exec @ARGV","60","deno","run","--no-check","--no-config","--no-npm","--node-modules-dir=none",
    "--unstable-webgpu","--unstable-ffi","-A",`${lab}run_html.ts`,"--offscreen","--no-state","--follow-links","--downloads",downloads,"--cookie-file",`${dir}/cookies.txt`,"--url",start,"--steps",file,...args],
    stdout:"piped",stderr:"piped"}).output();
  const ms=Math.round(performance.now()-t0);
  const text=new TextDecoder().decode(out.stdout)+new TextDecoder().decode(out.stderr);
  const failures=text.split("\n").filter(l=>/^Native HTML (steps|sweep|shortcut sweep)/.test(l));
  const afterFailure=out.code===0&&c.after?await c.after(downloads):undefined;
  if(afterFailure)failures.push(afterFailure);
  const passed=out.code===0&&failures.length===0;
  const verdict=passed?(c.gap?"XPASS":"PASS"):(c.gap?"XFAIL":"FAIL");
  if(verdict==="FAIL"||verdict==="XPASS")bad++;
  const why=passed?"":` (${failures[0]??`exit ${out.code}: ${text.split("\n").filter(l=>/rror/.test(l)).slice(0,2).join(" | ")}`})`;
  results.push(`${verdict.padEnd(5)} ${c.name} [${ms} ms]${why}${verdict==="XPASS"?` -- the gap is closed: remove it: ${c.gap}`:verdict==="XFAIL"?` -- gap: ${c.gap}`:""}`);
  console.log(results.at(-1));
}
await server.shutdown();
await Deno.remove(dir,{recursive:true});
if(bad){console.error(`everyday use in the window: ${bad} of ${results.length} cases failed`);Deno.exit(1);}
console.log(`everyday use in the window: ${results.length} cases as expected`);
