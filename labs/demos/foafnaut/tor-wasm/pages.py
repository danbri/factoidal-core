#!/usr/bin/env python3
"""Write tor-bootstrap.html into DIR (argument). The page loads the Arti wasm (fetched, so no
page-script decode loop), gives Date.now() the real time, and runs one bootstrap attempt.

Date.now(): a Foafnaut page clock is virtual and starts near 1970 (Page.lean, "The script
clock"). Arti reads the wall clock directly, so the page sets Date.now() to the real time at
generation plus the page's monotonic time since load. This is an accommodation for a missing
host capability (a real clock for pages), recorded in the design record, section 10."""
import sys, time
out = sys.argv[1]
timeout_ms = int(sys.argv[2]) if len(sys.argv) > 2 else 15000
glue = open(f"{out}/foafnaut_tor_wasm.js").read()
now = int(time.time() * 1000)
page = f"""<!doctype html><meta charset=utf-8><title>Arti 2.8.0 in the built-in wasm engine</title>
<h1>Arti 2.8.0 (Tor) in the built-in wasm engine</h1><pre id=o>running</pre>
<script>
console.log('page clock-raw '+Date.now());
(()=>{{const base={now},p0=performance.now();Date.now=()=>base+Math.floor(performance.now()-p0);}})();
</script>
<script>{glue}</script><script>
const log=m=>{{console.log('page '+m);const o=document.getElementById('o');if(o)o.textContent+='\\n'+m;}};
(async()=>{{
  const b=await (await fetch('foafnaut_tor_wasm_bg.wasm')).arrayBuffer();
  log('fetched '+b.byteLength);
  await wasm_bindgen({{module_or_path:b}});
  log('instantiated');
  const r=await wasm_bindgen.bootstrap({timeout_ms});
  log('end');
}})().catch(e=>log('error '+e+' '+(e&&e.stack||'')));
</script>"""
open(f"{out}/tor-bootstrap.html", "w").write(page)
