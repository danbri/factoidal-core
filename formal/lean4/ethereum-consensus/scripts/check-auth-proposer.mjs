// Independent test oracle only. RFC 9380 J.10.1 Q0/Q1, Tonelli-Shanks, direct polynomial evaluation.
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
function rowsForMap(rootFields,genericFields) {
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

  // Independent affine group oracle, with Euclidean inversion in Fp.
  // Right-to-left scalar accumulation differs from the Lean mixed-Jacobian loop.
  const HE=0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551n;
  const R=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
  function invFp(x){let a=P,b=mod(x),u=0n,v=1n;while(b){const q=a/b;[a,b]=[b,a%b];[u,v]=[v,u-q*v];}if(a!==1n)throw Error("zero inverse");return mod(u);}
  const invAffine=a=>{const d=invFp(a[0]*a[0]+a[1]*a[1]);return F(a[0]*d,-a[1]*d);};
  const sub=(a,b)=>add(a,neg(b));
  function pointAdd(a,b){if(a===null)return b;if(b===null)return a;
    const [x,y]=a,[u,v]=b;
    if(eq(x,u)&&eq(add(y,v),zero))return null;
    const slope=eq(x,u)?mul(mul(F(3n),mul(x,x)),invAffine(mul(F(2n),y))):mul(sub(v,y),invAffine(sub(u,x)));
    const X=sub(sub(mul(slope,slope),x),u);
    return [X,sub(mul(slope,sub(x,X)),y)];
  }
  function scalar(k,q){let acc=null;while(k){if(k&1n)acc=pointAdd(acc,q);q=pointAdd(q,q);k>>=1n;}return acc;}
  function parsePoint(s){if(s==="infinity")return null;const v=s.split(" ").map(BigInt);if(v.length!==4)throw Error("point");return [v.slice(0,2),v.slice(2)];}
  const fmt=q=>q===null?"infinity":q.flat().join(" ");
  const arg=q=>q===null?"-":q.flat().join(",");
  const negPoint=q=>q===null?null:[q[0],neg(q[1])];
  function finish(a,b){const q=scalar(HE,pointAdd(a,b));if(q!==null){
    if(!eq(mul(q[1],q[1]),add(pow(q[0],3n),F(4n,4n))))throw Error("cleared off curve");
    if(scalar(R,q)!==null)throw Error("cleared outside subgroup");
  }return fmt(q);}
  const mapCount=rows.length;
  const qa=parsePoint(rows[0][1].slice(3)),qb=parsePoint(rows[1][1].slice(3));
  for(const [a,b] of [[qa,qb],[qb,qa],[qa,qa],[qa,null],[null,qa],[null,null],[qa,negPoint(qa)]])
    rows.push(["clear "+arg(a)+" "+arg(b),"ok "+finish(a,b)]);
  for(const [root,fields] of rootFields){const a=fields.map(BigInt);rows.push(["curveroot "+root,"ok "+finish(parsePoint(map(a.slice(0,2))),parsePoint(map(a.slice(2))))]);}
  for(const [msg,dst,fields,kat] of genericFields){const a=fields.map(BigInt),out=finish(parsePoint(map(a.slice(0,2))),parsePoint(map(a.slice(2))));
    if(out!==kat.map(x=>BigInt("0x"+x)).join(" "))throw Error("RFC full point mismatch");
    rows.push(["curve "+msg+" "+dst,"ok "+out]);
  }
  rows.push(["clear 0,0,0,0 -","error internal_invariant"],
    ["clear "+P+",0,0,0 -","error internal_invariant"],
    ["clear 0,0,0 -","error operation"],
    ["curveroot -","error signing_root_width"],
    ["curveroot zz","error invalid_hex"],
    ["curve - -","error dst_width"]);
  return {rows, first,second,exception,mapCount};
}
const P=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
const h=b=>createHash('sha256').update(b).digest();
function rootField(root,dst=Buffer.from('BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_')){const dp=Buffer.concat([dst,Buffer.from([dst.length])]);const b0=h(Buffer.concat([Buffer.alloc(64),root,Buffer.from([1,0,0]),dp]));let prev=h(Buffer.concat([b0,Buffer.from([1]),dp]));const blocks=[prev];for(let i=2;i<=8;i++){const x=Buffer.from(b0.map((v,j)=>v^prev[j]));prev=h(Buffer.concat([x,Buffer.from([i]),dp]));blocks.push(prev);}const data=Buffer.concat(blocks);return [0,64,128,192].map(i=>(BigInt('0x'+data.subarray(i,i+64).toString('hex'))%P).toString());}

/* Test-only reuse of the repository's independent RFC oracle; not linked to Lean. */
import {fileURLToPath} from 'node:url';
const fixtureRun=spawnSync('python3',[fileURLToPath(new URL('./auth-proposer-fixtures.py',import.meta.url))],{encoding:'utf8',maxBuffer:4*1024*1024});
if(fixtureRun.error||fixtureRun.status!==0||fixtureRun.stderr)throw Error(String(fixtureRun.error||fixtureRun.stderr));
const fixtures=JSON.parse(fixtureRun.stdout);
const roots=fixtures.flatMap(x=>x.evidence.slice(1));
const {rows:hashRows}=rowsForMap(roots.map(x=>[x,rootField(Buffer.from(x,'hex'))]),[]);
const hashes=new Map(hashRows.filter(([a,b])=>a.startsWith('curveroot ')&&b.startsWith('ok ')).map(([a,b])=>[a.slice(10),b.slice(3).split(' ').map(BigInt)]));
const check=(condition,message)=>{if(!condition)throw Error(message);};
check(hashes.size===4,'four distinct signing roots');
function signature(root,negate=false){
  const q=hashes.get(root);check(q?.length===4,'hash point');
  let [xr,xi,yr,yi]=q;
  if(negate){yr=(P-yr)%P;yi=(P-yi)%P;}
  const sign=(yi===0n?yr:yi)>(P-1n)/2n;
  const hex=n=>n.toString(16).padStart(96,'0');
  return hex(xi|((sign?5n:4n)<<381n))+hex(xr);
}
const rows=[];
function put(a,b,line,expected){rows.push([[a,b,...line].join(' '),expected]);}
for(const fixture of fixtures){
  const {line,evidence,rejections}=fixture,[,a,b]=evidence;
  const sa=signature(a),sb=signature(b);
  put(sa,sb,line,'authenticated_relative_to_commitment '+evidence.join(' '));
  put(sb,sa,line,'error first_mismatch');
  put(sa,sa,line,'error second_mismatch');
  put(signature(a,true),sb,line,'error first_mismatch');
  put(sa,signature(b,true),line,'error second_mismatch');
  put('00',sb,line,'error first_signature_width');
  put(sa,'00',line,'error second_signature_width');
  for(const [bad,expected] of rejections)put(sa,sb,bad,expected);
}
rows.push(['x'.repeat(8705),'error resource_limit']);
// Independent SHA-256 branch-fold oracle for partial validator commitment projection.
// Original witness roots must also reproduce the independently built sparse-tree fixture.
const pair=(a,b)=>h(Buffer.concat([a,b]));
const u64=n=>{const b=Buffer.alloc(32);b.writeBigUInt64LE(BigInt(n));return b;};
const fold=(leaf,index,siblings)=>{let v=leaf;for(const s of siblings){
  v=(index&1n)?pair(s,v):pair(v,s);index>>=1n;
}return v;};
function expectedProjection(line){
  const key=Buffer.from(line[2],'hex'),cred=Buffer.from(line[3],'hex');
  const epoch=BigInt(line[0])/32n, old=BigInt(line[9]);
  const next=old>epoch+8192n?old:epoch+8192n;
  const index=BigInt(line[17]),depth=BigInt(line[0])>=364032n*32n?6:5;
  const member=line.slice(26,66).map(x=>Buffer.from(x,'hex'));
  const state=line.slice(66,66+depth).map(x=>Buffer.from(x,'hex'));
  const keyRoot=pair(key.subarray(0,32),Buffer.concat([key.subarray(32),Buffer.alloc(16)]));
  const leaf=(slashed,withdrawable)=>pair(
    pair(pair(keyRoot,cred),pair(u64(line[4]),u64(slashed))),
    pair(pair(u64(line[6]),u64(line[7])),pair(u64(line[8]),u64(withdrawable))));
  const registry=(v)=>pair(fold(v,index,member),u64(line[1]));
  const stateRoot=(v)=>fold(v,11n,state);
  const before=registry(leaf(line[5],old));
  check(before.toString('hex')===line[14],'old registry witness');
  check(stateRoot(before).toString('hex')===line[15],'old state witness');
  const after=registry(leaf(1,next)), root=stateRoot(after);
  check(!after.equals(before)&&!root.equals(stateRoot(before)),'projection changed both roots');
  return 'partial_validator_projection '+next+' '+after.toString('hex')+' '+root.toString('hex');
}
const retained=rows.slice();
for(const [request,verdict] of retained){
  if(verdict==='error resource_limit')continue;
  const tokens=request.split(' ');
  const value=verdict.startsWith('authenticated_')?expectedProjection(tokens.slice(2)):verdict;
  rows.push(['project '+request,value]);
}
rows.push(['project '+'x'.repeat(8705),'error resource_limit']);
check(rows.filter(x=>x[1].startsWith('partial_validator_projection ')).length===2,'projection fixture count');
const expected=rows.map(r=>r[1]);
function compare(actual){check(actual.length===expected.length,'row count');for(let i=0;i<actual.length;i++)check(actual[i]===expected[i],'row '+i+': '+actual[i]+' != '+expected[i]);}
compare(expected);
const controls=[expected.slice(1),[...expected,'extra'],expected.map((x,i)=>i===0?'error first_mismatch':x),expected.map((x,i)=>i===1?expected[0]:x),expected.map((x,i)=>i===2?expected[0]:x),expected.map(x=>x.startsWith('partial_validator_projection ')?x.replace(/.$/,'z'):x)];
for(const c of controls){let caught=false;try{compare(c);}catch{caught=true;}check(caught,'mutation escaped');}
console.log(JSON.stringify({rows:rows.length,authenticated:expected.filter(x=>x.startsWith('authenticated_')).length,controls:controls.length}));
if(process.argv[2]!=='--self-test'){
  const start=performance.now();
  const proc=spawnSync(process.argv[2],[],{encoding:'utf8',input:rows.map(r=>r[0]).join('\n')+'\n',timeout:240000,maxBuffer:4*1024*1024});
  if(proc.error||proc.status!==0||proc.stderr)throw Error(String(proc.error||proc.stderr||proc.status));
  check(proc.stdout.endsWith('\n'),'final newline');
  compare(proc.stdout.slice(0,-1).split('\n'));
  console.log('PASS '+rows.length+'/'+rows.length+' native authenticated proposer rows; '+(performance.now()-start).toFixed(3)+' ms');
}
