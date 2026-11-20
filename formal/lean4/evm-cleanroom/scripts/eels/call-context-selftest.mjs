#!/usr/bin/env node
/** Falsification controls for the published EELS Cancun CALL-context replay. */
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { spawnSync } from 'node:child_process'

const path=process.argv[2]
if(!path)throw Error('expected pinned CALL-context fixture JSON')
const original=JSON.parse(readFileSync(path,'utf8'))
const id=Object.keys(original).find(x=>x.includes('fork_Cancun')&&x.endsWith('-call]'))
if(!id)throw Error('missing official Cancun CALL fixture')
const parentAddress=original[id].transaction.to
const childAddress=Object.keys(original[id].pre).find(
  a=>a!==original[id].transaction.sender&&a!==parentAddress)
const cases=[
 ['forged-post-root',x=>{x[id].post.Cancun[0].hash='0x'+'00'.repeat(32)}],
 ['forged-return-data-storage',x=>{x[id].post.Cancun[0].state[parentAddress].storage['0x01']='0x01'}],
 ['forged-signed-sender',x=>{x[id].transaction.sender='0x'+'11'.repeat(20)}],
 ['missing-CALL-test',x=>{delete x[id]}],
 ['altered-child-return-byte',x=>{x[id].pre[childAddress].code='0x600160005360016000f3'}]
]
const folder=mkdtempSync(join(tmpdir(),'lean-call-eels-negative-'))
const results=[]
try{
 for(let i=0;i<cases.length;i++){
   const [name,mutate]=cases[i]
   const altered=structuredClone(original)
   mutate(altered)
   const input=join(folder,'input'+i+'.json'),out=join(folder,'result'+i+'.json')
   writeFileSync(input,JSON.stringify(altered))
   const process=spawnSync('node',['scripts/eels/run-lean-call-context.mjs',
     '--fixture',input,'--out',out],{
     encoding:'utf8',maxBuffer:1024*1024,timeout:120000
   })
   results.push({name,rejected:!process.error&&process.status!==0,exitCode:process.status})
 }
}finally{rmSync(folder,{recursive:true,force:true})}
const summary={
 status:results.every(x=>x.rejected)?'pass':'fail',
 kind:'official-Cancun-CALL-context-negative-controls',checked:results.length,
 cases:results
}
console.log(JSON.stringify(summary))
if(summary.status!=='pass')process.exitCode=1
