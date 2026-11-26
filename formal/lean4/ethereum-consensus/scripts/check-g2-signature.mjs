import {spawnSync} from 'node:child_process';
// Test-only independent affine Fp2 oracle. Generic Tonelli-Shanks over Fp²,
// unlike the Lean norm-based root recovery. Extended Euclid for inverses.
function makeCases(){
 const p=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
 const r=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
 const g=[[0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8n,0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7en],[0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801n,0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79ben]];
 const check=(v,m)=>{if(!v)throw Error(m)};
 const mod=x=>((x%p)+p)%p, zero=[0n,0n], one=[1n,0n];
 const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
 const add=(a,b)=>[mod(a[0]+b[0]),mod(a[1]+b[1])];
 const neg=a=>[mod(-a[0]),mod(-a[1])];
 const sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>[mod(a[0]*b[0]-a[1]*b[1]),mod(a[0]*b[1]+a[1]*b[0])];
 const sc=(a,k)=>[mod(a[0]*k),mod(a[1]*k)];
 function pow(a,k){let t=one;while(k){if(k&1n)t=mul(t,a);a=mul(a,a);k>>=1n}return t}
 function invBase(a){let x=mod(a),y=p,u=1n,v=0n;while(y){let k=x/y;[x,y]=[y,x-k*y];[u,v]=[v,u-k*v]}check(x===1n,"inverse zero");return mod(u)}
 const inv=a=>sc([a[0],mod(-a[1])],invBase(a[0]*a[0]+a[1]*a[1]));
 const rhs=x=>add(mul(mul(x,x),x),[4n,4n]);
 const sign=y=>(y[1]===0n?y[0]:y[1])>(p-1n)/2n;
 const q=p*p;let odd=q-1n,s=0;
 while(!(odd&1n)){odd>>=1n;s++}
 let z=null;for(let i=0n;i<64n;i++){let a=[i,1n];if(!eq(pow(a,(q-1n)/2n),one)){z=a;break}}
 check(z!==null&&s===3,"Fp2 parameters");
 function sqrt(a){
   if(eq(a,zero))return zero;
   if(!eq(pow(a,(q-1n)/2n),one))return null;
   let c=pow(z,odd), x=pow(a,(odd+1n)/2n), t=pow(a,odd), m=s;
   while(!eq(t,one)){
     let i=1,v=mul(t,t);while(i<m&&!eq(v,one)){v=mul(v,v);i++}
     check(i<m,"Tonelli-Shanks");
     const b=pow(c,1n<<BigInt(m-i-1));x=mul(x,b);c=mul(b,b);t=mul(t,c);m=i;
   }
   check(eq(mul(x,x),a),"root");return x;
 }
 function pointAdd(a,b){
   if(a===null)return b;if(b===null)return a;
   const [x,y]=a,[u,v]=b;
   if(eq(x,u)&&eq(add(y,v),zero))return null;
   const m=eq(x,u)?mul(sc(mul(x,x),3n),inv(sc(y,2n))):mul(sub(v,y),inv(sub(u,x)));
   const t=sub(sub(mul(m,m),x),u);return [t,sub(mul(m,sub(x,t)),y)];
 }
 function pointMul(k,a){let t=null;while(k){if(k&1n)t=pointAdd(t,a);a=pointAdd(a,a);k>>=1n}return t}
 const encode=(x,f)=>((BigInt(f)<<381n)|x[1]).toString(16).padStart(96,"0")+x[0].toString(16).padStart(96,"0");
 const output=(x,y)=>"ok "+[...x,...y].join(" ");
 check(eq(mul(g[1],g[1]),rhs(g[0]))&&pointMul(r,g)===null,"generator order");
 check(encode(g[0],4)==="93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8","generator wire");
 function reference(hex){
   if(hex.length+1>512)return "error resource_limit";
   if(hex.length%2||hex.length>256||!/^[0-9a-f]*$/.test(hex))return "error invalid_hex";
   if(hex.length!==192)return "error width";
   const a=BigInt("0x"+hex.slice(0,96)),b=BigInt("0x"+hex.slice(96)),f=a>>381n;
   if(f<4n)return "error not_compressed";if(f>=6n)return "error infinity_signature";
   const x=[b,a% (1n<<381n)];
   if(x.some(v=>v>=p))return "error non_canonical_x";
   let y=sqrt(rhs(x));if(y===null)return "error not_on_curve";
   if(sign(y)!==(f===5n))y=neg(y);
   if(sign(y)!==(f===5n))return "error not_on_curve";
   if(pointMul(r,[x,y])!==null)return "error not_subgroup";
   return output(x,y);
 }
 const cases=[];
 function put(h,expected){let got=reference(h);if(expected!==undefined)check(got===expected,"unexpected "+h+" "+got+" vs "+expected);cases.push([h,got])}
 let point=null;
 for(let i=1;i<=40;i++){point=pointAdd(point,g);const [x,y]=point;put(encode(x,sign(y)?5:4),output(x,y));put(encode(x,sign(y)?4:5),output(x,neg(y)))}
 for(let i=0n;i<64n;i++){const x=[i,i*i+1n];put(encode(x,4));put(encode(x,5))}
 for(let i=0n;i<16n;i++){put(encode([i,0n],4));put(encode([0n,i],5))}
 for(const x of [[0n,0n],g[0],[p-1n,p-1n],[p,0n],[0n,p]])for(let f=0;f<8;f++)put(encode(x,f));
 for(let i=0n;i<16n;i++){put(encode([p+i,0n],4),"error non_canonical_x");put(encode([0n,p+i],5),"error non_canonical_x")}
 for(const n of [0,1,47,48,95,97,127,128])put("00".repeat(n),"error width");
 for(const h of ["0","gg","FF","00".repeat(129)])put(h,"error invalid_hex");
 put("00".repeat(256),"error resource_limit");
 const counts={};for(const [,v] of cases){let k=v.startsWith("ok ")?"ok":v;counts[k]=(counts[k]||0)+1}
 check(counts.ok>=80&&counts["error not_subgroup"]>0&&counts["error not_on_curve"]>0,"coverage");
 return {cases,counts};
}
function compare(cases,out){
 if(cases.length!==out.length)throw Error("count");
 for(let i=0;i<cases.length;i++)if(out[i]!==cases[i][1])throw Error("row "+i+" expected "+cases[i][1]+" got "+out[i]);
}
function controls(cases){
 const good=cases.map(v=>v[1]);compare(cases,good);
 const bad=[good.slice(1),[...good,"error width"],["ok 1 2 3 4",...good.slice(1)],good.map((v,i)=>i===0?"error not_subgroup":v),good.map((v,i)=>i===80?"ok 0 0 0 0":v)];
 for(const b of bad){let caught=false;try{compare(cases,b)}catch{caught=true}if(!caught)throw Error("escaped comparator control")}
 return bad.length;
}

const {cases,counts}=makeCases();
console.log(JSON.stringify({rows:cases.length,counts,controls:controls(cases)}));
if(process.argv[2]==="--self-test")process.exit(0);
if(process.argv.length!==3)throw Error("usage: check-g2-signature.mjs <native binary>");
const start=process.hrtime.bigint();
const run=spawnSync(process.argv[2],[],{input:cases.map(v=>v[0]).join("\n")+"\n",encoding:"utf8",timeout:120000,maxBuffer:4*1024*1024});
if(run.error||run.status!==0||run.stderr)throw Error(JSON.stringify({status:run.status,error:String(run.error),stderr:run.stderr}));
if(!run.stdout.endsWith("\n"))throw Error("missing final newline");
compare(cases,run.stdout.slice(0,-1).split("\n"));
console.log("PASS "+cases.length+"/"+cases.length+" actual Lean G2 signature admission rows; batch "+Number(process.hrtime.bigint()-start)/1e6+" ms");
