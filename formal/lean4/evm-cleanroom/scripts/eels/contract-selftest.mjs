#!/usr/bin/env node
/**
 * Negative controls for the *real Lean contract* EELS post-state comparator.
 * Corrupt official expectations and require the runner to return nonzero.
 * This is a comparator test, not a proof of soundness of the fixture itself.
 */
import { readFileSync, mkdtempSync, writeFileSync, rmSync } from 'node:fs'
import { join } from 'node:path'
import { tmpdir } from 'node:os'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'

const fixturePath=process.argv[2]
if(!fixturePath) throw Error('usage: node scripts/eels/contract-selftest.mjs /path/fixture.json')
const baseline=JSON.parse(readFileSync(fixturePath,'utf8'))
const selection=Object.keys(baseline).filter(x=>x.includes('fork_Cancun-state_test'))
if(selection.length!==6) throw Error('fixture inventory changed')
const id=selection.find(x=>x.endsWith('-key_sstore]'))
if(!id) throw Error('missing key_sstore case')
const testCases=[
  ['tampered-state-root', data=> {data[id].post.Cancun[0].hash='0x'+'00'.repeat(32)}],
  ['tampered-storage-value', data=> {data[id].post.Cancun[0].state[
    data[id].transaction.to].storage['0x00']='0x03'}],
  ['tampered-recovered-signer', data=> {data[id].transaction.sender='0x'+'12'.repeat(20)}],
  ['lost-contract-case', data=> {delete data[id]}],
]
const runner=fileURLToPath(new URL('./run-lean-contract-state-tests.mjs',import.meta.url))
const temp=mkdtempSync(join(tmpdir(),'eels-lean-contract-negative-'))
try {
  const result=[]
  for(let i=0;i<testCases.length;i++){
    const [name,mutate]=testCases[i]
    const changed=structuredClone(baseline)
    mutate(changed)
    const input=join(temp,'fixture-'+i+'.json')
    const out=join(temp,'result-'+i+'.json')
    writeFileSync(input,JSON.stringify(changed))
    const run=spawnSync(process.execPath,[runner,
      '--fixture',input,'--out',out],{
      encoding:'utf8',timeout:120000,maxBuffer:1024*1024
    })
    const rejected=run.status!==0 && !run.error
    result.push({name,rejected,exitCode:run.status,
      detail:rejected ? 'rejected' : run.stderr?.slice(-500)})
  }
  const summary={kind:'eels-lean-contract-comparator-controls',
    status:result.every(r=>r.rejected)?'pass':'fail',
    checked:result.length,controls:result}
  console.log(JSON.stringify(summary))
  if(summary.status!=='pass')process.exitCode=1
} finally {
  rmSync(temp,{recursive:true,force:true})
}
