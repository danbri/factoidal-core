#!/usr/bin/env node
/**
 * Adversarial controls for ALL six published EELS Prague signed transactions.
 * A fixture mutation is a deliberately false oracle, NOT a real regression.
 * A correct implementation must reject it rather than silently skip it.
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { spawnSync } from 'node:child_process'

const [fixturePath, directory]=process.argv.slice(2)
if(!fixturePath||!directory||process.argv.length!==4)
  throw Error('usage: prague-all-selftest.mjs PUBLISHED_FIXTURE_JSON OUTPUT_DIR')
const original=JSON.parse(readFileSync(fixturePath,'utf8'))
const ids=Object.keys(original)
if(ids.length!==6)throw Error('expected six published Prague cases')
const byType=n=>{
  const id=ids.find(id=>id.endsWith('type_'+n+']'))
  if(!id)throw Error('missing official type '+n)
  return id
}
const type3=byType(3),type4=byType(4)
const clone=()=>JSON.parse(JSON.stringify(original))
const runner=fileURLToPath(new URL('./run-lean-prague-all-types.mjs',import.meta.url))
mkdirSync(directory,{recursive:true})
const tamperHex=(hex)=>{
  if(typeof hex!=='string'||!hex.startsWith('0x'))throw Error('bad mutation input')
  return hex.slice(0,-1)+(hex.at(-1)==='0'?'1':'0')
}
const mutations=[
  {name:'type3-forged-blob-versioned-hash',id:type3,apply:o=>{
    o[type3].transaction.blobVersionedHashes[0]=tamperHex(o[type3].transaction.blobVersionedHashes[0])
  }},
  {name:'type3-fee-cap-mismatch',id:type3,apply:o=>{
    o[type3].transaction.maxFeePerBlobGas='0x02'
  }},
  {name:'type3-forged-state-root',id:type3,apply:o=>{
    const p=o[type3].post.Prague[0];p.hash=tamperHex(p.hash)
  }},
  {name:'type3-fake-excess-fee',id:type3,apply:o=>{
    o[type3].env.currentExcessBlobGas='0x01'
  }},
  {name:'type4-forged-authority-signer',id:type4,apply:o=>{
    o[type4].transaction.authorizationList[0].signer=
      '0x0000000000000000000000000000000000000002'
  }},
  {name:'type4-forged-authority-signature',id:type4,apply:o=>{
    const a=o[type4].transaction.authorizationList[0]
    a.r=tamperHex(a.r)
  }},
  {name:'type4-forged-delegation-code',id:type4,apply:o=>{
    const p=o[type4].post.Prague[0]
    const authority=o[type4].transaction.authorizationList[0].signer
    p.state[authority].code='0xef01000000000000000000000000000000000000000002'
  }},
  {name:'type4-forged-state-root',id:type4,apply:o=>{
    const p=o[type4].post.Prague[0];p.hash=tamperHex(p.hash)
  }},
  {name:'missing-type4-case',id:null,apply:o=>{delete o[type4]}},
]
const checks=[]
for(const m of mutations){
  const fixture=clone();m.apply(fixture)
  const path=resolve(directory,m.name+'.json')
  const output=resolve(directory,m.name+'.report.json')
  writeFileSync(path,JSON.stringify(fixture)+'\n')
  const proc=spawnSync(process.execPath,[runner,'--fixture',path,'--out',output],{
    encoding:'utf8',timeout:120000,maxBuffer:1024*1024})
  if(proc.error||proc.status!==1)
    throw Error('forged fixture was not rejected: '+m.name+' status '+proc.status+
      ' stderr '+proc.stderr)
  const report=JSON.parse(readFileSync(output,'utf8'))
  if(report.status!=='fail' ||
     (m.id ? !(report.cases.some(x=>x.id===m.id&&x.status==='fail')) :
       !(report.passed===5 && report.actualLeanStateTestsExecuted===5)))
    throw Error('mutation not correctly identified: '+m.name+
      ' '+JSON.stringify(report).slice(0,700))
  checks.push({name:m.name,rejected:true})
}
const result={status:'pass',checked:checks.length,checks}
writeFileSync(join(directory,'prague-all-selftest.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
