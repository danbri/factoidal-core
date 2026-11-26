import {spawnSync} from 'node:child_process';
import {performance} from 'node:perf_hooks';
function makeRows(){
 const p=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn,r=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
 const mod=x=>((x%p)+p)%p;
 const zero=()=>Array(12).fill(0n);
 const basis=i=>{const a=zero();a[i]=1n;return a};
 // u = w^6 - 1. Oracle uses Fp[w] / (w^12 - 2*w^6 + 2).
 const toPoly=a=>Array.from({length:12},(_,i)=>i<6?mod(a[2*i]-a[2*i+1]):a[2*(i-6)+1]);
 const toTower=a=>Array.from({length:12},(_,i)=>i%2?a[(i-1)/2+6]:mod(a[i/2]+a[i/2+6]));
 function product(a,b){
   const c=Array(23).fill(0n);
   for(let i=0;i<12;i++)for(let j=0;j<12;j++)c[i+j]+=a[i]*b[j];
   for(let k=22;k>=12;k--){let v=mod(c[k]);c[k-6]+=2n*v;c[k-12]-=2n*v;}
   return c.slice(0,12).map(mod);
 }
 function exp(a,e){
   // left-to-right powering, unlike the Lean right-to-left loop.
   let z=basis(0);
   for(const bit of e.toString(2)){z=product(z,z);if(bit==="1")z=product(z,a)}
   return z;
 }
 let state=0xd3c09c4436a7a5d1n;
 function rand(){let n=0n;for(let i=0;i<6;i++){state=(state*6364136223846793005n+1442695040888963407n)&((1n<<64n)-1n);n=(n<<64n)|state}return n%p}
 const dense=()=>Array.from({length:12},rand);
 const rows=[];
 const ok=a=>"ok "+a.join(" ");
 const row=(op,a,b,answer)=>rows.push({input:op==="mul"?`mul ${a.join(" ")} ${b.join(" ")}`:op==="pow"?`pow ${b} ${a.join(" ")}`:`final ${a.join(" ")}`,expected:answer});
 const mul=(a,b)=>row("mul",a,b,ok(toTower(product(toPoly(a),toPoly(b)))));
 for(let i=0;i<12;i++)for(let j=0;j<12;j++)mul(basis(i),basis(j));
 for(let i=0;i<128;i++)mul(dense(),dense());
 for(const a of [zero(),basis(0),Array(12).fill(p-1n)])for(const b of [zero(),basis(0),Array(12).fill(p-1n),dense()])mul(a,b);
 for(const e of [0n,1n,2n,3n,17n,255n,256n,65537n])for(const a of [dense(),basis(11)])row("pow",a,e,ok(toTower(exp(toPoly(a),e))));
 const E=(p**12n-1n)/r;
 if((p**12n-1n)%r!==0n)throw Error("order does not divide target group");
 for(const a of [basis(0),dense(),basis(2)]){
   const z=exp(toPoly(a),E);
   if(exp(z,r).join()!==basis(0).join())throw Error("final exponent order check failed");
   row("final",a,null,ok(toTower(z)));
 }
 row("final",zero(),null,"error zero_final_input");
 row("mul",[p,...zero().slice(1)],basis(0),"error noncanonical");
 row("mul",basis(0),[p,...zero().slice(1)],"error noncanonical");
 row("pow",basis(0),2n**4572n,"error exponent_limit");
 // Exact exponent admission boundary and precedence; expected values independent of Lean.
 row("pow",zero(),0n,ok(basis(0)));
 row("pow",zero(),1n,ok(zero()));
 row("pow",basis(0),2n**4572n-1n,ok(basis(0)));
 row("pow",basis(0),2n**4572n+1n,"error exponent_limit");
 row("pow",[p,...zero().slice(1)],2n**4572n,"error noncanonical");
 row("final",[p,...zero().slice(1)],null,"error noncanonical");
 rows.push({input:"mul 1 2",expected:"error width"},{input:"pow x "+zero().join(" "),expected:"error invalid_decimal"},{input:"final "+Array(12).fill("-1").join(" "),expected:"error invalid_decimal"},{input:"bogus",expected:"error operation"},{input:"x".repeat(4097),expected:"error resource_limit"});
 return rows;
}
function compare(rows,lines){if(rows.length!==lines.length)throw Error("wrong row count");for(let i=0;i<rows.length;i++)if(rows[i].expected!==lines[i])throw Error("row "+i+" mismatch");}
const rows=makeRows(),good=rows.map(x=>x.expected);
compare(rows,good);
let controls=0;
for(const bad of [good.slice(1),[...good,"ok"],["error width",...good.slice(1)],[good[0].replace("ok 1","ok 2"),...good.slice(1)],good.map((s,i)=>i===rows.length-1?"error operation":s)]){try{compare(rows,bad)}catch(e){controls++;}}
if(controls!==5)throw Error("control escaped");
console.log(JSON.stringify({rows:rows.length,controls,valid:good.filter(s=>s.startsWith("ok ")).length}));
if(process.argv[2]!=="--self-test"){
 const start=performance.now();
 const run=spawnSync(process.argv[2],[],{input:rows.map(x=>x.input).join("\n")+"\n",encoding:"utf8",timeout:180000,maxBuffer:4*1024*1024});
 if(run.error||run.status!==0)throw Error(String(run.error??run.stderr));
 compare(rows,run.stdout.trimEnd().split("\n"));
 console.log("PASS "+rows.length+"/"+rows.length+" actual Lean target field rows; batch "+(performance.now()-start)+" ms");
}
