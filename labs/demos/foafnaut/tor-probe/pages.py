#!/usr/bin/env python3
"""Write the probe pages into DIR (argument): tor-probe.html runs every step once and shows the
lines; tor-split.html runs three loads as separate tasks, so the host's native-html-script record
of each task gives its real engine time (leanMs). The wasm is fetched (decoding it from base64 in
page script stops at the BubblePopJS step budget). The page clock is virtual, so the real time
is written into the page when it is generated."""
import sys, time
out = sys.argv[1]
glue = open(f"{out}/torprobe.js").read()
now = int(time.time() * 1000)
load = "const b=await (await fetch('torprobe_bg.wasm')).arrayBuffer();await wasm_bindgen({module_or_path:b});"
log = "const log=m=>{console.log('tor '+m);const o=document.getElementById('o');if(o)o.textContent+='\\n'+m;};"
probe = f"""<!doctype html><meta charset=utf-8><title>Tor components</title>
<h1>Tor components (Arti 0.48) in the built-in wasm engine</h1><pre id=o>running</pre>
<script>{glue}</script><script>{log}
(async()=>{{{load}log('instantiated');
for(const line of wasm_bindgen.run(20,2,{now}).trim().split('\\n'))log(line);log('end');
}})().catch(e=>log('error '+e));</script>"""
split = f"""<!doctype html><meta charset=utf-8><title>Tor components split</title><pre id=o>running</pre>
<script>{glue}</script><script>{log}
const later=f=>new Promise(r=>setTimeout(()=>r(f()),50));
(async()=>{{{load}
await later(()=>log('A onion and consensus: '+wasm_bindgen.run(0,0,{now}).split('\\n').length));
await later(()=>log('B 20 x25519 pairs: '+wasm_bindgen.run(0,20,{now}).split('\\n').length));
await later(()=>log('C 2000 relay cells: '+wasm_bindgen.run(2000,0,{now}).split('\\n').length));
await later(()=>log('end'));
}})().catch(e=>log('error '+e));</script>"""
open(f"{out}/tor-probe.html", "w").write(probe)
open(f"{out}/tor-split.html", "w").write(split)
