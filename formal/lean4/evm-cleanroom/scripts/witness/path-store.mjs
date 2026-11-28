#!/usr/bin/env node
/** Test-only independent historical-root and current-path comparisons. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { MerklePatriciaTrie, bytes, hex, proofRequest, verifyProofBag, checkSources, keccak, digest, emptyRoot } from './oracle.mjs'

checkSources()
const binary = fileURLToPath(new URL('../../.lake/build/bin/evm-mpt-path-store-probe', import.meta.url))
const opt = '--dangerously-enable-unverified-keccak'
const a = '11'.repeat(31)+'10', b = '21'+'11'.repeat(30)+'10'
const near = '11'.repeat(31)+'11', absent = '33'.repeat(32)
const merge = (...bags) => [...new Set(bags.flat())]
function call(root,key,bag,expectedCode=0,flag=opt) {
  const p = spawnSync(binary,[flag,root,key,...bag],{encoding:'utf8',timeout:60000,maxBuffer:2*1024*1024})
  assert.ifError(p.error)
  assert.equal(p.status,expectedCode,p.stdout+p.stderr)
  assert.equal(p.stderr,'')
  return p.stdout.trimEnd().split('\n')
}
let membership=0, nonmembership=0, beyond128=0, maxBag=0, maxPath=0, refusalControls=0
async function selected(root,key,bag,expected) {
  const lines=call(root,key,bag)
  assert.equal(lines[0],expected===null?'absent':'present:'+expected)
  const proof=lines.slice(1)
  assert(proof.length<=65)
  assert(proof.every(s=>/^(?:[a-f0-9]{2})+$/.test(s)))
  const actual=await verifyProofBag(bytes(key),proof.map(bytes),{root:bytes(root),useKeyHashing:false})
  if(expected===null){assert.equal(actual,null);nonmembership++}
  else {assert.equal(hex(actual),expected);membership++}
  if(bag.length>128)beyond128++
  maxBag=Math.max(maxBag,bag.length)
  maxPath=Math.max(maxPath,proof.length)
  return proof
}
function refuse(root,key,bag,expected) {
  assert.deepEqual(call(root,key,bag),[expected])
  refusalControls++
}
const t=new MerklePatriciaTrie({useKeyHashing:false})
await t.put(bytes(a),bytes('01'))
await t.put(bytes(b),bytes('02'))
const oldA=await proofRequest(t,bytes(a))
let history=merge(oldA.proof,(await proofRequest(t,bytes(b))).proof)
let root=oldA.root
let lastKey=a,lastValue='01'
for(let i=1;i<=72;i++){
  const key=i%2?a:b
  const value=(BigInt(i)+(1n<<248n)).toString(16).padStart(64,'0')
  await t.put(bytes(key),bytes(value))
  const request=await proofRequest(t,bytes(key))
  root=request.root
  history=merge(history,request.proof)
  const path=await selected(root,key,history,value)
  assert.deepEqual(new Set(path),new Set(request.proof),'exact reachable hashed path')
  lastKey=key;lastValue=value
}
assert(history.length>128)
await selected(oldA.root,a,history,'01')
await selected(root,absent,history,null)
const noRoot=history.filter(n=>hex(keccak(bytes(n)))!==root)
refuse(root,lastKey,noRoot,'witness:missing-referenced-node')
const finalProof=(await proofRequest(t,bytes(lastKey))).proof
const noLeaf=history.filter(n=>n!==finalProof.at(-1))
refuse(root,lastKey,noLeaf,'witness:missing-referenced-node')
refuse(root,lastKey,oldA.proof,'witness:missing-referenced-node')
refuse('00',lastKey,history,'witness:root-or-key-width')
refuse(root,lastKey,Array(4097).fill('80'),'resourceLimit')
refuse(root,lastKey,['00'.repeat(4097)],'resourceLimit')
assert.deepEqual(call(root,lastKey,history,2,'--not-opted-in'),['inputError:explicit-experimental-opt-in-required'])
refusalControls++
await selected(emptyRoot,lastKey,[],null)
await selected(emptyRoot,lastKey,Array(4096).fill('80'),null)
const short=new MerklePatriciaTrie({useKeyHashing:false})
await short.put(bytes(a),bytes('01'))
await short.put(bytes(near),bytes('02'))
const s=await proofRequest(short,bytes(a))
const sn=await proofRequest(short,bytes(near))
const sm=await proofRequest(short,bytes(absent))
await selected(s.root,a,merge(s.proof,sn.proof),'01')
await selected(s.root,near,merge(s.proof,sn.proof),'02')
await selected(s.root,absent,sm.proof,null)
assert.equal(membership,75)
assert.equal(nonmembership,4)
assert.equal(refusalControls,7)
assert(beyond128>0)
console.log(JSON.stringify({membership,nonmembership,beyond128,maxBag,maxPath,refusalControls,executableSha256:digest(readFileSync(binary))}))
