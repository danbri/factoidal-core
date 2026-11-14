# Adds measurement steps to a copy of labs/demos/foafnaut/run_html.ts (scratch copies only).
# usage: python3 -I rp_patch.py run_html.ts   (idempotent)
import sys
p = sys.argv[1]; s = open(p).read()
already = "rp-shot:" in s
def sub(old, new, count=1):
    if already: return
    global s
    assert s.count(old) == count, (old, s.count(old)); s = s.replace(old, new)
sub('import {addEntries,consoleRequest,noteDiagnostics} from "./native_console.ts";',
    'import {addEntries,consoleRequest,noteDiagnostics,consoleOf} from "./native_console.ts";')
sub('  // Lean engine for compile: --native-engine PATH,',
    '''  // realpages measurement: steps from RP_STEPS (JSON), and the time of the last frame for rp-quiet.
  if(Deno.env.get("RP_STEPS"))commands=JSON.parse(Deno.env.get("RP_STEPS")!);
  {const log=console.log;console.log=(...a:unknown[])=>{const s=typeof a[0]==="string"?a[0]:"";
    if(s.includes('"native-html-frame"')||s.includes('"native-html-page-canvas"'))(globalThis as Record<string,unknown>).__rpLast=performance.now();log(...a);};}
  // Lean engine for compile: --native-engine PATH,''')
G = '(globalThis as Record<string,any>)'
sub('        else if(step==="settle")', f'''        else if(typeof step==="string"&&step.startsWith("rp-quiet:")){{
          const [q,max]=step.slice(9).split(":").map(Number),now=performance.now();{G}.__rpQ??=now;
          const quietFor=now-({G}.__rpLast??0);
          if((quietFor<q||loading||rendering)&&now-{G}.__rpQ<max){{commands.unshift(step);stepAt=now+100;}}
          else{{trace("rp-quiet",{{waited:Math.round(now-{G}.__rpQ),quiet:quietFor>=q,lastFrameAgo:Math.round(quietFor)}});{G}.__rpQ=undefined;}}
        }}
        else if(typeof step==="string"&&step.startsWith("rp-shot:")){{
          const file=step.slice(8),texture=session?.offscreenTexture;
          if(texture&&device)await Deno.writeFile(file,await pngOf(texture.width,texture.height,await texturePixels(device,texture)));
          const entries=consoleOf(document),counts:Record<string,number>={{}};
          for(const e of entries){{const k=`${{e.source}}:${{e.severity}}`;counts[k]=(counts[k]??0)+1;}}
          trace("rp-shot",{{file,url:document.url,top:current?.layers.layers.top??0,scroll,bandTop:current?.layers.layers.bandTop??0,shownOffset,width,height,
            links:(frame.webRender.links as unknown[][]).slice(0,800).map(l=>[String(l[1]),l[2],l[3],l[4],l[5]]),console:counts,
            consoleSample:entries.filter(e=>e.source==="System"||e.severity==="error").slice(0,60).map(e=>`${{e.source}}/${{e.severity}}/${{e.feature??""}}: ${{String(e.message).slice(0,240)}}`)}});
        }}
        else if(typeof step==="string"&&step.startsWith("rp-scroll:")){{
          const d=Math.round((height-(current?.layers.layers.top??0))*(step==="rp-scroll:down"?1:-1));native.testEvent(11,-d,0);trace("rp-scroll",{{d}});
        }}
        else if(typeof step==="string"&&step.startsWith("rp-click:")){{
          const [x,y]=step.slice(9).split(":").map(Number),wy=Math.round(y+(current?.layers.layers.top??0));
          native.testEvent(2,x,wy);native.testEvent(4,x,wy);trace("rp-click",{{x,y:wy}});
        }}
        else if(typeof step==="string"&&step.startsWith("rp-link:")){{
          const href=step.slice(8),links=frame.webRender.links as unknown[][];
          const link=(href?links.find(l=>{{try{{return String(l[1])===href||new URL(String(l[1]),document.url).href===href;}}catch{{return false;}}}}):undefined)??(step==="rp-link:"?links[0]:undefined);
          {G}.__rpUrl=document.url;
          if(link){{const l=link as number[],x=Math.round(l[2]+l[4]/2),y=Math.round(windowRow(l[3]+l[5]/2));native.testEvent(2,x,y);native.testEvent(4,x,y);
            trace("rp-link",{{found:true,href:String(link[1]),x,y}});}}
          else trace("rp-link",{{found:false,href}});
        }}
        else if(typeof step==="string"&&step.startsWith("rp-nav:")){{
          const max=Number(step.slice(7)),now=performance.now();{G}.__rpN??=now;
          const moved=document.url!=={G}.__rpUrl;
          if((!moved||loading||candidate||rendering||refusing>0)&&now-{G}.__rpN<max){{commands.unshift(step);stepAt=now+100;}}
          else{{trace("rp-nav",{{url:document.url,moved,waited:Math.round(now-{G}.__rpN)}});{G}.__rpN=undefined;}}
        }}
        else if(step==="settle")''')
open(p, "w").write(s); print("patched" if not already else "steps already there", p)
# second part: every fetch of the main thread, by status and content type
s = open(p).read()
if "rp-fetch" not in s:
    old = '  if(Deno.env.get("RP_STEPS"))commands=JSON.parse(Deno.env.get("RP_STEPS")!);'
    assert s.count(old) == 1
    s = s.replace(old, old + '''
  {const f=globalThis.fetch;globalThis.fetch=async(input:RequestInfo|URL,init?:RequestInit)=>{
    const u=input instanceof Request?input.url:String(input),start=performance.now();
    try{const r=await f(input,init);console.log(JSON.stringify({type:"rp-fetch",url:u.slice(0,300),status:r.status,ctype:r.headers.get("content-type")??"",ms:Math.round(performance.now()-start)}));return r;}
    catch(e){console.log(JSON.stringify({type:"rp-fetch",url:u.slice(0,300),status:0,error:String(e).slice(0,200),ms:Math.round(performance.now()-start)}));throw e;}};}''')
    open(p, "w").write(s); print("fetch patched", p)

# third part: the two capture flags of 1063a3684 (--offscreen-size, --text-size), for hosts from before them
s = open(p).read()
if '"--offscreen-size"' not in s:
    def rep(old, new):
        global s
        assert s.count(old) == 1, old; s = s.replace(old, new)
    rep('  let shotFile:string|undefined;\n', '  let shotFile:string|undefined,shotSize:[number,number,number]=[800,500,2],textSize=200;\n')
    rep('    else if(arg==="--shot"){shotFile=args.shift();if(!shotFile)throw new Error("--shot needs a file path");}\n',
        '    else if(arg==="--shot"){shotFile=args.shift();if(!shotFile)throw new Error("--shot needs a file path");}\n'
        '    else if(arg==="--offscreen-size"){const m=/^(\\d+)x(\\d+)(?:@(\\d))?$/.exec(args.shift()??"");\n'
        '      if(!m)throw new Error("--offscreen-size needs WIDTHxHEIGHT[@SCALE]");shotSize=[Number(m[1]),Number(m[2]),Number(m[3]??2)];}\n'
        '    else if(arg==="--text-size"){textSize=Number(args.shift());if(!(textSize>=50&&textSize<=1000))throw new Error("--text-size needs a percentage from 50 to 1000");}\n')
    rep('native.createOffscreen(800,500,2,windowTitle(document))', 'native.createOffscreen(shotSize[0],shotSize[1],shotSize[2],windowTitle(document))')
    rep('view.textScalePercent=Math.max(50,Math.round(200*scale/5)*5)', 'view.textScalePercent=Math.max(50,Math.round(textSize*scale/5)*5)')
    open(p, "w").write(s); print("capture flags backported", p)
