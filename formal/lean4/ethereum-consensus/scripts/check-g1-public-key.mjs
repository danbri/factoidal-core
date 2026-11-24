// Independent test oracle only. Affine slopes use extended Euclid; no projective formulas.
import {spawnSync} from 'node:child_process';
function makeCases(){
  const p=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
  const r=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
  const g=[0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn,0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n];
  const mod=a=>((a%p)+p)%p;
  const check=(x,msg)=>{if(!x)throw Error(msg)};
  function inv(a){
    let x=mod(a), y=p, u=1n, v=0n;
    while(y){let k=x/y; [x,y]=[y,x-k*y]; [u,v]=[v,u-k*v]}
    check(x===1n,"noninvertible");
    return mod(u);
  }
  function pow(a,n){let z=1n; for(const bit of n.toString(2)){z=mod(z*z);if(bit==="1")z=mod(z*a)}return z}
  function add(a,b){
    if(a===null)return b;if(b===null)return a;
    const [x,y]=a,[u,v]=b;
    if(x===u&&mod(y+v)===0n)return null;
    const m=x===u?mod(3n*x*x*inv(2n*y)):mod((v-y)*inv(u-x));
    const t=mod(m*m-x-u);
    return [t,mod(m*(x-t)-y)];
  }
  function mul(k,q){let a=null;while(k){if(k&1n)a=add(a,q);q=add(q,q);k>>=1n}return a}
  const sign=y=>y>(p-1n)/2n;
  const encode=(x,flags)=>((BigInt(flags)<<381n)|x).toString(16).padStart(96,"0");
  const onCurve=([x,y])=>mod(y*y-x*x*x-4n)===0n;
  check(onCurve(g)&&mul(r,g)===null,"generator/order");
  check(encode(g[0],4)==="97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb","generator encoding");
  check(mul(3n,[0n,2n])===null&&mul(r,[0n,2n])!==null,"order-three control");
  function reference(hex){
    if(hex.length%2||hex.length>128||!/^[0-9a-f]*$/.test(hex))return "error invalid_hex";
    if(hex.length!==96)return "error width";
    const flags=parseInt(hex.slice(0,2),16)>>5;
    if(flags<4)return "error not_compressed";
    if(flags>=6)return "error infinity_key";
    const x=BigInt("0x"+(parseInt(hex.slice(0,2),16)&31).toString(16).padStart(2,"0")+hex.slice(2));
    if(x>=p)return "error non_canonical_x";
    const rhs=mod(x*x*x+4n);
    let y=pow(rhs,(p+1n)/4n);
    if(mod(y*y)!==rhs)return "error not_on_curve";
    if(sign(y)!==(flags===5))y=mod(-y);
    if(sign(y)!==(flags===5))return "error not_on_curve";
    if(mul(r,[x,y])!==null)return "error not_subgroup";
    return `ok ${x} ${y}`;
  }
  const cases=[];
  function put(hex,expected){const got=reference(hex); if(expected!==undefined)check(got===expected,`oracle disagreement: ${hex} ${got} vs ${expected}`);cases.push([hex,got])}
  let q=null;
  for(let i=1;i<=64;i++){
    q=add(q,g);check(onCurve(q),"generator multiple off curve");
    const [x,y]=q;put(encode(x,sign(y)?5:4),`ok ${x} ${y}`);
    put(encode(x,sign(y)?4:5),`ok ${x} ${mod(-y)}`);
  }
  for(let i=0n;i<96n;i++){put(encode(i,4));put(encode(i,5))}
  for(const x of [0n,1n,g[0],p-1n,p,(1n<<381n)-1n])
    for(let f=0;f<8;f++)put(encode(x,f));
  for(let i=0n;i<32n;i++){put(encode(p+i,4),"error non_canonical_x");put(encode(p+i,5),"error non_canonical_x")}
  for(const n of [0,1,2,31,32,47,49,63,64])put("00".repeat(n),"error width");
  for(const s of ["0","gg","Z0","00".repeat(65)])put(s,"error invalid_hex");
  put(encode(0n,4),"error not_subgroup");put(encode(0n,5),"error not_subgroup");
  const aggregateCases=[];
  const key=q=>encode(q[0],sign(q[1])?5:4);
  const neg=q=>[q[0],mod(-q[1])];
  const multiples=Array.from({length:64},(_,i)=>mul(BigInt(i+1),g));
  function aggregate(points){
    let sum=null;
    for(const q of points)sum=add(sum,q);
    return sum===null?"error infinity_sum":`ok ${sum[0]} ${sum[1]}`;
  }
  function putAgg(points){
    aggregateCases.push(["agg "+points.map(key).join(" "),aggregate(points)]);
  }
  aggregateCases.push(["agg","error empty_keys"]);
  for(const q of multiples){putAgg([q]);putAgg([q,q]);putAgg([q,neg(q)]);}
  for(let i=0;i<64;i++){
    const a=multiples[i],b=multiples[(i*7+5)%64],c=multiples[(i*11+3)%64];
    putAgg([a,b,c]);putAgg([c,a,b]);putAgg([a,neg(a),b,c]);putAgg([a,b,neg(a),neg(b)]);
  }
  for(const [bad,error] of [[encode(0n,4),"error not_subgroup"],[encode(p,4),"error non_canonical_x"],[encode(0n,6),"error infinity_key"],["00","error width"]]){
    aggregateCases.push(["agg "+bad+" "+key(g),error]);
    aggregateCases.push(["agg "+key(g)+" "+bad,error]);
    aggregateCases.push(["agg "+key(g)+" "+key(neg(g))+" "+bad,error]);
  }
  const cap=2048;
  const capSum=mul(BigInt(cap),g);
  aggregateCases.push(["agg "+Array(cap).fill(key(g)).join(" "),`ok ${capSum[0]} ${capSum[1]}`]);
  aggregateCases.push(["agg "+Array(cap+1).fill(key(g)).join(" "),"error resource_limit"]);
  aggregateCases.push(["agg "+Array(cap+1).fill("00").join(" "),"error resource_limit"]);
  return {cases,aggregateCases};
}
function compare(cases,output){
  if(output.length!==cases.length)throw Error("row count mismatch");
  for(let i=0;i<cases.length;i++)if(output[i]!==cases[i][1])throw Error(`row ${i}: ${cases[i][0]} expected ${cases[i][1]} got ${output[i]}`);
}
function controls(cases){
  const expected=cases.map(row=>row[1]);
  compare(cases,expected);
  const bad=[expected.slice(1),[...expected,"error width"],["ok 1 2",...expected.slice(1)],expected.map((x,i)=>i===128?"ok 0 2":x)];
  for(const b of bad){let refused=false;try{compare(cases,b)}catch{refused=true}if(!refused)throw Error("mutation not detected")}
  return bad.length;
}
const {cases,aggregateCases}=makeCases();
const allCases=[...cases,...aggregateCases];
console.log("Generated",cases.length,"rows;",controls(cases),"comparator controls detected");
console.log("Generated",aggregateCases.length,"aggregate rows;",controls(aggregateCases),"aggregate comparator controls detected");
const counts={};for(const [,out] of cases){const k=out.startsWith("ok ")?"ok":out;counts[k]=(counts[k]||0)+1}
console.log(JSON.stringify(counts));
if(process.argv[2]==="--self-test")process.exit(0);
if(process.argv.length!==3)throw Error("usage: node check-g1-public-key.mjs <native binary>");
const start=process.hrtime.bigint();
const run=spawnSync(process.argv[2],[],{input:allCases.map(r=>r[0]).join("\n")+"\n",encoding:"utf8",timeout:120000,maxBuffer:4*1024*1024});
if(run.error||run.status!==0||run.stderr)throw Error(JSON.stringify({status:run.status,error:String(run.error),stderr:run.stderr}));
if(!run.stdout.endsWith("\n"))throw Error("missing final newline");
const actual=run.stdout.slice(0,-1).split("\n");
compare(allCases,actual);
compare(cases,actual.slice(0,cases.length));
compare(aggregateCases,actual.slice(cases.length));
console.log("PASS "+aggregateCases.length+"/"+aggregateCases.length+" actual Lean G1 aggregate rows");
console.log("PASS "+cases.length+"/"+cases.length+" actual Lean G1 admission rows; combined batch "+Number(process.hrtime.bigint()-start)/1e6+" ms");
