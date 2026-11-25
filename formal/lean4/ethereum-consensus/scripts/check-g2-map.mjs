// Independent test oracle only. RFC 9380 J.10.1 Q0/Q1, Tonelli-Shanks, direct polynomial evaluation.
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
function rowsForMap(rootFields) {
  const P=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn, Q=P*P;
  const mod=n=>((n%P)+P)%P, F=(a,b=0n)=>[mod(a),mod(b)], zero=F(0n), one=F(1n), eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
  const add=(a,b)=>F(a[0]+b[0],a[1]+b[1]), neg=a=>F(-a[0],-a[1]), mul=(a,b)=>F(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]);
  function pow(a,n){let acc=one; for(;n;n>>=1n,a=mul(a,a))if(n&1n)acc=mul(acc,a);return acc;}
  const inv=a=>eq(a,zero)?zero:pow(a,Q-2n), div=(a,b)=>mul(a,inv(b));
  const Z=F(-2n,-1n), A=F(0n,240n), B=F(1012n,1012n);
  let s=0, t=Q-1n;while(!(t&1n)){s++;t>>=1n;}
  const c0=pow(Z,t);
  if(!eq(pow(Z,(Q-1n)/2n),neg(one)))throw Error("Z");
  function sqrt(a){if(eq(a,zero))return zero;if(!eq(pow(a,(Q-1n)/2n),one))return null;
    let x=pow(a,(t+1n)/2n),v=pow(a,t),c=c0,m=s;
    while(!eq(v,one)){let i=1,b=mul(v,v);while(i<m&&!eq(b,one)){b=mul(b,b);i++;}if(i===m)throw Error("TS");const w=pow(c,1n<<BigInt(m-i-1));x=mul(x,w);c=mul(w,w);v=mul(v,c);m=i;}
    if(!eq(mul(x,x),a))throw Error("sqrt");return x;}
  const sign=a=>Boolean((a[0]===0n?a[1]:a[0])&1n);
  const g=x=>add(add(pow(x,3n),mul(A,x)),B);
  const xn=[
    F(0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6n,0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6n),
    F(0n,0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71an),
    F(0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71en,0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38dn),
    F(0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1n)];
  const xd=[F(0n,-72n),F(12n,-12n),one];
  const yn=[
    F(0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706n,0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706n),
    F(0n,0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97ben),
    F(0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71cn,0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38fn),
    F(0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10n)];
  const yd=[F(-432n,-432n),F(0n,-216n),F(18n,-18n),one];
  const poly=(x,c)=>c.reduce((a,v,i)=>add(a,mul(v,pow(x,BigInt(i)))),zero);
  let first=0,second=0,exception=0;
  function map(u){const w=mul(Z,pow(u,2n)), d=add(pow(w,2n),w);let x;
    if(eq(d,zero)){x=div(B,mul(Z,A));exception++;}else x=div(mul(neg(B),add(d,one)),mul(A,d));
    let y=sqrt(g(x));if(y===null){x=mul(w,x);y=sqrt(g(x));second++;}else first++;
    if(y===null)throw Error("both nonsquare");if(sign(y)!==sign(u))y=neg(y);
    const dx=poly(x,xd),dy=poly(x,yd);if(eq(dx,zero)||eq(dy,zero))return "infinity";
    const X=div(poly(x,xn),dx),Y=mul(y,div(poly(x,yn),dy));
    if(!eq(pow(Y,2n),add(pow(X,3n),F(4n,4n))))throw Error("target");
    return [...X,...Y].join(" ");
  }
  const KAT=[
  ["03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8","05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a",
  "019ad3fc9c72425a998d7ab1ea0e646a1f6093444fc6965f1cad5a3195a7b1e099c050d57f45e3fa191cc6d75ed7458c","171c88b0b0efb5eb2b88913a9e74fe111a4f68867b59db252ce5868af4d1254bfab77ebde5d61cd1a86fb2fe4a5a1c1d","0ba10604e62bdd9eeeb4156652066167b72c8d743b050fb4c1016c31b505129374f76e03fa127d6a156213576910fef3","0eb22c7a543d3d376e9716a49b72e79a89c9bfe9feee8533ed931cbb5373dde1fbcd7411d8052e02693654f71e15410a"],
  ["02f99798e8a5acdeed60d7e18e9120521ba1f47ec090984662846bc825de191b5b7641148c0dbc237726a334473eee94","145a81e418d4010cc027a68f14391b30074e89e60ee7a22f87217b2f6eb0c4b94c9115b436e6fa4607e95a98de30a435",
  "113d2b9cd4bd98aee53470b27abc658d91b47a78a51584f3d4b950677cfb8a3e99c24222c406128c91296ef6b45608be","13855912321c5cb793e9d1e88f6f8d342d49c0b0dbac613ee9e17e3c0b3c97dfbb5a49cc3fb45102fdbaf65e0efe2632","0fd3def0b7574a1d801be44fde617162aa2e89da47f464317d9bb5abc3a7071763ce74180883ad7ad9a723a9afafcdca","056f617902b3c0d0f78a9a8cbda43a26b65f602f8786540b9469b060db7b38417915b413ca65f875c130bebfaa59790c"]];
  const rows=[];
  for(const k of KAT){const n=k.map(x=>BigInt("0x"+x)),a=map(n.slice(0,2));if(a!==n.slice(2).join(" "))throw Error("RFC mismatch "+a);rows.push(["map "+n.slice(0,2).join(" "),"ok "+a]);}
  for(const a of [0n,1n,2n,P-1n,P-2n])for(const b of [0n,1n,2n,P-1n,P-2n])rows.push([`map ${a} ${b}`,"ok "+map([a,b])]);
  let seed=9380n;function rand(){seed=(seed*0x5851f42d4c957f2dn+0x14057b7ef767814fn)&((1n<<512n)-1n);return seed%P;}
  for(let i=0;i<48;i++){const u=[rand(),rand()];rows.push(["map "+u.join(" "),"ok "+map(u)]);}
  for(const [root,fields] of rootFields){const a=fields.map(BigInt);rows.push(["maproot "+root,"ok "+map(a.slice(0,2))+" ; "+map(a.slice(2))]);}
  rows.push([`map ${P} 0`,"error noncanonical"],[`map 0 ${P}`,"error noncanonical"],["map -1 0","error invalid_decimal"],["map 0 x","error invalid_decimal"],["map "+ "9".repeat(117)+" 0","error resource_limit"],["maproot -","error signing_root_width"],["maproot 00","error signing_root_width"],["maproot zz","error invalid_hex"]);
  if(first===0||second===0||exception===0)throw Error("coverage");
  return {rows, first,second,exception};
}
const P=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
const h=b=>createHash('sha256').update(b).digest();
function rootField(root){const dst=Buffer.from('BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_'),dp=Buffer.concat([dst,Buffer.from([dst.length])]);const b0=h(Buffer.concat([Buffer.alloc(64),root,Buffer.from([1,0,0]),dp]));let prev=h(Buffer.concat([b0,Buffer.from([1]),dp]));const blocks=[prev];for(let i=2;i<=8;i++){const x=Buffer.from(b0.map((v,j)=>v^prev[j]));prev=h(Buffer.concat([x,Buffer.from([i]),dp]));blocks.push(prev);}const data=Buffer.concat(blocks);return [0,64,128,192].map(i=>(BigInt('0x'+data.subarray(i,i+64).toString('hex'))%P).toString());}
const roots=[Buffer.alloc(32),Buffer.alloc(32,255),Buffer.from(Array.from({length:32},(_,i)=>i)),...Array.from({length:16},(_,i)=>h(Buffer.from('map root '+i)))];
const {rows,first,second,exception}=rowsForMap(roots.map(root=>[root.toString('hex'),rootField(root)]));
const expected=rows.map(x=>x[1]);
function compare(actual){if(actual.length!==expected.length)throw Error('count');for(let i=0;i<expected.length;i++)if(actual[i]!==expected[i])throw Error('row '+i+': '+actual[i]+' != '+expected[i]);}
compare(expected);const bad=[expected.slice(1),[...expected,'ok'],['ok 0 0 0 0',...expected.slice(1)],[...expected.slice(0,-1),'error noncanonical'],expected.map((x,i)=>i===1?expected[0]:x)];for(const a of bad){let caught=false;try{compare(a);}catch{caught=true;}if(!caught)throw Error('mutation escaped');}
console.log('RFC Q0/Q1 matched; '+rows.length+' rows; '+first+' first / '+second+' second / '+exception+' exceptional; '+bad.length+' controls');
if(process.argv[2]!=='--self-test'){const start=performance.now();const p=spawnSync(process.argv[2],[],{input:rows.map(x=>x[0]).join('\n')+'\n',encoding:'utf8',timeout:120000,maxBuffer:4*1024*1024});if(p.error||p.status!==0)throw Error(String(p.error||p.stderr));compare(p.stdout.trimEnd().split('\n'));console.log('PASS '+rows.length+'/'+rows.length+' native Lean G2 map rows; batch '+(performance.now()-start).toFixed(3)+' ms');}
