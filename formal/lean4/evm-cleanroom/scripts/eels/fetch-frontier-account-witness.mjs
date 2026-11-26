#!/usr/bin/env node
/**
 * Acquire an independently verifiable first-mainnet-transaction PRESTATE.
 *
 * It needs an actual archive endpoint that supports historical eth_getProof
 * for 2015 block 46146, not merely eth_getBalance or a recent proof window.
 * No RPC response is trusted until verify-frontier-account-witness.mjs
 * independently checks three EIP-1186 MPT paths and both resulting roots.
 *
 * Usage:
 * node fetch-frontier-account-witness.mjs \
 *   --rpc https://your-archive-rpc --historical evidence/frontier-mainnet-46147.json \
 *   --out .lake/eels/first-frontier-witness.json
 *
 * If proof serving is absent, this exits nonzero with a precise reason;
 * it never generates a fake proof or silently switches to unverified state.
 */
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs'
import { dirname } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
const args=process.argv.slice(2)
function opt(k){const i=args.indexOf(k);return i>=0?args[i+1]:undefined}
const endpoint=opt('--rpc'),historicalPath=opt('--historical'),out=opt('--out')
if(!endpoint||!historicalPath||!out)throw Error('required: --rpc URL --historical JSON --out JSON')
if(!/^https:\/\//.test(endpoint))throw Error('archive endpoint must use HTTPS')
const historical=JSON.parse(readFileSync(historicalPath,'utf8'))
const b=historical.block,d=historical.transaction
const blockBefore='0x'+(BigInt(b.number)-1n).toString(16)
const endpoints=[d.from,d.to,b.miner]
const timeoutMs=20000
let counter=0
async function rpc(method,params){
  const id=++counter
  const response=await fetch(endpoint,{
    method:'POST',
    headers:{'content-type':'application/json'},
    body:JSON.stringify({jsonrpc:'2.0',id,method,params}),
    signal:AbortSignal.timeout(timeoutMs)
  })
  if(!response.ok)throw Error('archive RPC HTTP '+response.status+' on '+method)
  const payload=await response.json()
  if(payload.id!==id || payload.jsonrpc!=='2.0')
    throw Error('invalid JSON-RPC response envelope on '+method)
  if(payload.error)
    throw Error('archive RPC '+method+' rejected historical request: '+
      JSON.stringify(payload.error).slice(0,800))
  if(!payload.result)throw Error('missing RPC result on '+method)
  return payload.result
}
try {
  const parentHeader=await rpc('eth_getBlockByHash',[b.parentHash,false])
  if(parentHeader.number!==blockBefore ||
     parentHeader.hash?.toLowerCase()!==b.parentHash.toLowerCase())
    throw Error('RPC returned wrong pretransaction parent block header')
  const proofs=[]
  for(const address of endpoints){
    const proof=await rpc('eth_getProof',[address,[],blockBefore])
    if(proof.address?.toLowerCase()!==address.toLowerCase() ||
       !Array.isArray(proof.accountProof) || !proof.accountProof.length)
      throw Error('RPC omitted historical EIP-1186 account proof for '+address)
    proofs.push(proof)
  }
  const bundle={
    schemaVersion:1,chainId:1,
    parentHeader,accounts:proofs,
    provenance:{
      method:'eth_getBlockByHash + eth_getProof at exact parent block number',
      blockNumber:blockBefore,
      rpcEndpoint:endpoint,
      collectedAt:new Date().toISOString(),
      verification:'UNTRUSTED-UNTIL-OFFLINE-MPT-AND-STATE-ROOT-REPLAY'
    }
  }
  mkdirSync(dirname(out),{recursive:true})
  writeFileSync(out,JSON.stringify(bundle,null,2)+'\n')
  const verifier=fileURLToPath(new URL('./verify-frontier-account-witness.mjs',import.meta.url))
  const proc=spawnSync(process.execPath,[
    verifier,'--historical',historicalPath,'--witness',out,
  ],{encoding:'utf8',timeout:120000,maxBuffer:1024*1024})
  if(proc.error||proc.status!==0)
    throw Error('archive witness failed INDEPENDENT MPT and Lean replay: '+
      String(proc.error??proc.stderr).slice(-3000))
  const verified=JSON.parse(proc.stdout.trim().split('\n').at(-1))
  if(verified.status!=='full-historical-three-account-root-replay-pass')
    throw Error('witness validation returned incomplete status')
  console.log(JSON.stringify({status:'verified-real-mainnet-state-root-replay',
    block:46147,proofs:proofs.length,
    derivedIntermediateStateRoot:verified.derivedIntermediateStateRoot,
    derivedFinalBlockStateRoot:verified.derivedFinalBlockStateRoot,
    bundleFile:out}))
}catch(e){
  console.error('Cannot claim authenticated historical replay: '+String(e))
  process.exitCode=1
}
