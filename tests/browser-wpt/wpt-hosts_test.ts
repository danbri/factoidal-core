// wpt-hosts_test.ts: WPT test mode reaches only WPT's own names on wptserve's ports.
//   deno test tests/browser-wpt/wpt-hosts_test.ts
import {wptDomains,wptFetcher,wptPorts,wptRoute,wptSubdomains,type WptServe} from "./wpt-hosts.ts";

const spec:WptServe={domains:wptDomains,subdomains:wptSubdomains,ports:wptPorts};
const assert=(c:unknown,m:string)=>{if(!c)throw new Error(m);};

Deno.test("WPT names on wptserve's ports go to 127.0.0.1", ()=>{
  for(const [url,port] of [["http://web-platform.test:8000/a.html",8000],["http://www1.web-platform.test:8001/x",8001],
    ["https://web-platform.test:8443/y",8443],["https://xn--lve-6lad.not-web-platform.test:8444/z",8444],
    ["http://www2.not-web-platform.test:8003/",8003]] as [string,number][]){
    const r=wptRoute(url,spec);
    assert(!("refused" in r)&&r.port===port,`${url}: ${JSON.stringify(r)}`);
  }
});

Deno.test("everything else is refused", ()=>{
  for(const url of ["http://example.com/","https://github.com/","http://127.0.0.1:8000/","http://localhost:8000/",
    "http://nonexistent.web-platform.test:8000/","http://web-platform.test/","http://web-platform.test:9999/",
    "https://web-platform.test:8000/","http://web-platform.test.example.com:8000/","http://evil.www.web-platform.test:8000/",
    "file:///etc/hosts","ftp://web-platform.test:8000/","http://user:pw@web-platform.test:8000/","ws://web-platform.test:8888/"]){
    assert("refused" in wptRoute(url,spec),`${url} was not refused`);
  }
});

Deno.test("the fetcher refuses before connecting", async ()=>{
  const f=wptFetcher(spec);
  try{
    for(const url of ["http://example.com/","http://localhost:8000/"]){
      let refused=false;
      try{await f.fetch(url);}catch(e){refused=/WPT test mode refused/.test(String(e));}
      assert(refused,`${url} was not refused`);
    }
  }finally{f.close();}
});
