// Independent test oracle only: affine group arithmetic, RFC hash oracle rows.
import {rows as mapRows} from './check-g2-map.mjs';
import {spawnSync} from 'node:child_process';
const p=0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
const r=0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const mod=x=>(x%p+p)%p;
const F=(a,b=0n)=>[mod(a),mod(b)];
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const add=(a,b)=>F(a[0]+b[0],a[1]+b[1]),neg=a=>F(-a[0],-a[1]);
const sub=(a,b)=>add(a,neg(b)),mul=(a,b)=>F(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]);
function invFp(a){let u=mod(a),v=p,x=1n,y=0n;while(v){const k=u/v;[u,v]=[v,u-k*v];[x,y]=[y,x-k*y];}if(u!==1n)throw Error('noninvertible');return mod(x);}
function inv(a){const k=invFp(a[0]*a[0]+a[1]*a[1]);return F(k*a[0],-k*a[1]);}
const z=F(0n);
function pointAdd(a,b){if(a===null)return b;if(b===null)return a;const [x,y]=a,[u,v]=b;
  if(eq(x,u)&&eq(add(y,v),z))return null;
  const s=eq(x,u)?mul(mul(F(3n),mul(x,x)),inv(mul(F(2n),y))):mul(sub(v,y),inv(sub(u,x)));
  const X=sub(sub(mul(s,s),x),u);return [X,sub(mul(s,sub(x,X)),y)];}
function scalar(n,q){let a=null;while(n){if(n&1n)a=pointAdd(a,q);q=pointAdd(q,q);n>>=1n;}return a;}
const g=[F(0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn),F(0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n)];
const onCurve=(q,b)=>eq(mul(q[1],q[1]),add(mul(mul(q[0],q[0]),q[0]),b));
const hex=x=>x.toString(16).padStart(96,'0');
const sign=y=>(y[1]===0n?y[0]:y[1])>(p-1n)/2n;
const key=q=>hex(q[0][0]|((sign(q[1])?5n:4n)<<381n));
const sig=q=>hex(q[0][1]|((sign(q[1])?5n:4n)<<381n))+hex(q[0][0]);
const check=(x,s)=>{if(!x)throw Error(s);};
check(onCurve(g,F(4n))&&scalar(r,g)===null,'G1 generator');
check(key(g)==='97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb','G1 encoding');
const hashes=mapRows.filter(row=>row[0].startsWith('curveroot ')&&row[1].startsWith('ok ')).map(([arg,out])=>{
  const a=out.slice(3).split(' ').map(BigInt);
  const q=[a.slice(0,2),a.slice(2)];check(a.length===4&&onCurve(q,F(4n,4n))&&scalar(r,q)===null,'hash point');
  return [arg.split(' ')[1],q];
});
check(hashes.length===19,'hash root inventory');
const rows=[];
function put(root,s,keys,out){rows.push(['verify '+[root,s,...keys].join(' '),out]);}
const pk=n=>key(scalar(n,g));
for(let i=0;i<6;i++){
  const [root,h]=hashes[i], [other,otherH]=hashes[(i+1)%hashes.length], n=BigInt(i+1), m=n+7n;
  check(!eq(h[0],otherH[0]),'distinct roots hash to distinct x');
  const signature=sig(scalar(n,h)), aggregate=sig(scalar(n+m,h));
  put(root,signature,[pk(n)],'ok true');
  put(root,aggregate,[pk(n),pk(m)],'ok true');
  put(root,aggregate,[pk(m),pk(n)],'ok true');
  put(root,sig(scalar(2n*n,h)),[pk(n),pk(n)],'ok true');
  put(other,signature,[pk(n)],'ok false');
  put(root,signature,[pk(m)],'ok false');
  put(root,sig(scalar(r-n,h)),[pk(n)],'ok false');
  put(root,aggregate,[pk(n)],'ok false');
}
const [root,h]=hashes[0],s=sig(h),k=pk(1n);
put(root,s,[],'error empty_keys');
put(root,s,[k,pk(r-1n)],'error infinity_sum');
put(root,s,['00'],'error key_width');
put(root,s,['c0'+'00'.repeat(47)],'error key_infinity');
put(root,s,[hex((4n<<381n)|p)],'error key_noncanonical');
put(root,s,[hex(4n<<381n)],'error key_subgroup');
put(root,s,[hex(0n)],'error key_not_compressed');
put(root,'00',[k],'error signature_width');
put(root,'c0'+'00'.repeat(95),[k],'error signature_infinity');
put(root,hex((4n<<381n)|p)+hex(0n),[k],'error signature_noncanonical');
put(root,hex(0n)+hex(0n),[k],'error signature_not_compressed');
put('00',s,[k],'error root_width');
put(root,s,Array(2049).fill('00'),'error resource_limit');
put(root,'zz',[k],'error invalid_hex');
const expected=rows.map(x=>x[1]);
function compare(a){check(a.length===expected.length,'count');for(let i=0;i<a.length;i++)check(a[i]===expected[i],'row '+i+': '+a[i]+' != '+expected[i]);}
compare(expected);
const bad=[expected.slice(1),[...expected,'ok true'],expected.map((v,i)=>i===0?'ok false':v),expected.map((v,i)=>i===4?'ok true':v),expected.map((v,i)=>v==='error resource_limit'?'ok false':v)];
for(const b of bad){let caught=false;try{compare(b);}catch{caught=true;}check(caught,'comparator mutation escaped');}
console.log(JSON.stringify({rows:rows.length,true:expected.filter(x=>x==='ok true').length,false:expected.filter(x=>x==='ok false').length,rejections:expected.filter(x=>x.startsWith('error')).length,controls:bad.length}));
if(process.argv[2]!=='--self-test'){
  const start=performance.now();
  const run=spawnSync(process.argv[2],[],{input:rows.map(x=>x[0]).join('\n')+'\n',encoding:'utf8',timeout:180000,maxBuffer:4*1024*1024});
  if(run.error||run.status!==0||run.stderr)throw Error(String(run.error||run.stderr||run.status));
  check(run.stdout.endsWith('\n'),'final newline');compare(run.stdout.slice(0,-1).split('\n'));
  console.log('PASS '+rows.length+'/'+rows.length+' native BLS signing-root verification rows; batch '+(performance.now()-start).toFixed(3)+' ms');
}
