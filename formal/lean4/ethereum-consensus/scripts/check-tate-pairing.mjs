import {spawnSync} from 'node:child_process';
import {performance} from 'node:perf_hooks';

// Independent polynomial field oracle, not a runtime dependency.
// Generator coordinates: CFRG pairing-friendly curves, BLS12-381 parameters.
const p=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
const r=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const E=(p**12n-1n)/r;
const mod=x=>((x%p)+p)%p;
function inv(a){
 let x=mod(a),y=p,s=1n,t=0n;
 while(y){const q=x/y;[x,y]=[y,x%y];[s,t]=[t,s-q*t]}
 if(x!==1n)throw Error("nonunit");
 return mod(s);
}
const zero=()=>Array(12).fill(0n);
const embed=x=>{const a=zero();a[0]=mod(x);return a};
const one=embed(1n);
const eq=(a,b)=>a.every((v,i)=>v===b[i]);
const sub=(a,b)=>a.map((v,i)=>mod(v-b[i]));
function product(a,b){
 const c=Array(23).fill(0n);
 for(let i=0;i<12;i++)for(let j=0;j<12;j++)c[i+j]+=a[i]*b[j];
 for(let k=22;k>=12;k--){const v=mod(c[k]);c[k-6]+=2n*v;c[k-12]-=2n*v;}
 return c.slice(0,12).map(mod);
}
function power(a,e){
 let z=one;
 for(const bit of e.toString(2)){z=product(z,z);if(bit==="1")z=product(z,a)}
 return z;
}
const toTower=a=>Array.from({length:12},(_,i)=>i%2?a[(i-1)/2+6]:mod(a[i/2]+a[i/2+6]));
const g=[0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn,0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n];
const q=[[0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8n,0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7en],[0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801n,0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79ben]];
function affine(a,b){
 if(!a)return b;if(!b)return a;
 const [x,y]=a,[u,v]=b;
 if(x===u&&mod(y+v)===0n)return null;
 const m=x===u?mod(3n*x*x*inv(2n*y)):mod((v-y)*inv(u-x));
 const X=mod(m*m-x-u);
 return [X,mod(m*(x-X)-y)];
}
const w=zero();w[1]=1n;
// Untwist via independent polynomial inversion, not the Lean sparse formula.
const wInv=power(w,p**12n-2n);
if(!eq(product(w,wInv),one))throw Error("w inverse");
const xScale=product(wInv,wInv), yScale=product(xScale,wInv);
function lift2([a,b]){const c=zero();c[0]=mod(a-b);c[6]=b;return c;}
const qx=product(lift2(q[0]),xScale),qy=product(lift2(q[1]),yScale);
if(!eq(product(qy,qy),sub(product(product(qx,qx),qx),embed(-4n))))throw Error("untwist");
if(mod(g[1]*g[1]-g[0]**3n-4n)!==0n)throw Error("G1 generator");
function line(a,b,X,Y){
 const c=affine(a,b);
 if(!a||!b)return [c,one,one];
 const [x,y]=a,[u,v]=b;
 if(!c)return [c,sub(X,embed(x)),one];
 const slope=x===u?mod(3n*x*x*inv(2n*y)):mod((v-y)*inv(u-x));
 // Affine line evaluated as yQ + slope*xP - yP - slope*xQ.
 const n=sub(sub(Y,embed(y-slope*x)),product(embed(slope),X));
 return [c,n,sub(X,embed(c[0]))];
}
function pairing(P,X,Y){
 let t=P,n=one,d=one;
 for(const bit of r.toString(2).slice(1)){
  let [next,l,v]=line(t,t,X,Y);
  n=product(product(n,n),l);d=product(product(d,d),v);t=next;
  if(bit==="1"){[next,l,v]=line(t,P,X,Y);n=product(n,l);d=product(d,v);t=next;}
 }
 if(t!==null||eq(n,zero())||eq(d,zero()))throw Error("Miller invariant");
 // Independently verify that vertical factors disappear after reduction.
 if(!eq(power(d,E),one))throw Error("denominator reduction");
 return power(n,E);
}
const base=pairing(g,qx,qy);
if(eq(base,one)||!eq(power(base,r),one))throw Error("nondegenerate order");
const rows=[];
const ok=a=>"ok "+toTower(a).join(" ");
function add(P,Q,expected){rows.push({input:"tate "+[...P,...Q.flat()].join(" "),expected});}
add(g,q,ok(base));
const g2=affine(g,g),g3=affine(g2,g),neg=[g[0],mod(-g[1])];
for(const [P,k] of [[g2,2n],[g3,3n],[neg,r-1n]]){
 const a=pairing(P,qx,qy);
 if(!eq(a,power(base,k)))throw Error("G1 bilinearity");
 add(P,q,ok(a));
}
const qNeg=[q[0],q[1].map(x=>mod(-x))];
const negY=qy.map(x=>mod(-x));
const qNegResult=pairing(g,qx,negY);
if(!eq(product(base,qNegResult),one))throw Error("G2 inverse");
add(g,qNeg,ok(qNegResult));
add([0n,2n],q,"error g1_not_subgroup");
add([0n,0n],q,"error curve");
add(g,[[0n,0n],[0n,0n]],"error curve");
for(let i=0;i<6;i++){
 const a=[...g,...q.flat()];a[i]=p;
 rows.push({input:"tate "+a.join(" "),expected:"error noncanonical"});
}
rows.push({input:"tate 1 2",expected:"error width"},{input:"tate 1 2 3 4 5 x",expected:"error invalid_decimal"});
function compare(lines){
 if(lines.length!==rows.length)throw Error("count");
 for(let i=0;i<rows.length;i++)if(lines[i]!==rows[i].expected)throw Error("row "+i);
}
const good=rows.map(x=>x.expected);compare(good);
let controls=0;
for(const bad of [good.slice(1),[...good,"ok"],["error curve",...good.slice(1)],[good[1],good[0],...good.slice(2)],good.map((x,i)=>i===5?"error curve":x)]){
 try{compare(bad)}catch{controls++}
}
if(controls!==5)throw Error("mutation escaped");
console.log(JSON.stringify({rows:rows.length,positive:5,controls,nondegenerate:true,bilinearity:true,denominatorReduction:true}));
if(process.argv[2]!=="--self-test"){
 const start=performance.now();
 const run=spawnSync(process.argv[2],[],{input:rows.map(x=>x.input).join("\n")+"\n",encoding:"utf8",timeout:180000,maxBuffer:4*1024*1024});
 if(run.error||run.status!==0)throw Error(String(run.error??run.stderr));
 compare(run.stdout.trimEnd().split("\n"));
 console.log("PASS "+rows.length+"/"+rows.length+" actual Lean Tate rows; batch "+(performance.now()-start)+" ms");
}
