#!/usr/bin/env node
/**
 * Independent pinned EthereumJS Cancun parent CALL bytecode vs the actual
 * Lean bytecode CALL dispatcher (OpcodeCall.run).
 *
 * No synthetic CALL-plan bypass: both engines run the identical full parent
 * bytecode containing opcode 0xf1, and the same contract bytecode. The Lean
 * scope deliberately excludes calldata/value, precompiles, returndata and
 * reentrant / deeper-than-one calls.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const parent = createAddressFromString('0x00000000000000000000000000000000000000c1')
const child = createAddressFromString('0x00000000000000000000000000000000000000c3')
const origin = createAddressFromString('0x00000000000000000000000000000000000000c2')
const parentHex = '5f5f5f5f5f60c3617530f100'
const parentInvalidHex = '5f5f5f5f5f60c3617530f1fe'
const parentGas = 50000n
const examples = [
  {name:'store-and-stop', childHex:'600160005500', parentHex, flag:'1', slot0:'1', status:'stopped'},
  {name:'store-then-revert', childHex:'600160005560006000fd', parentHex, flag:'0', slot0:'0', status:'stopped'},
  {name:'store-then-invalid', childHex:'6001600055fe', parentHex, flag:'0', slot0:'0', status:'stopped'},
  {name:'empty-child', childHex:'00', parentHex, flag:'1', slot0:'0', status:'stopped'},
  {name:'parent-fails-after-child-success', childHex:'600160005500',
    parentHex:parentInvalidHex, flag:null, slot0:'0', status:'exceptional'},
]
const common = new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const disagreements=[]
for (const c of examples) {
  const lean = spawnSync('lake', ['exe','evm-subset','--call-opcode',
    c.parentHex,c.childHex,'195',String(parentGas),'30','30'],{
    encoding:'utf8',timeout:60000,maxBuffer:2*1024*1024
  })
  if(lean.error||lean.status!==0)throw Error('Lean executable failed: '+String(lean.error??lean.stderr))
  const actual = JSON.parse(lean.stdout.trim().split('\n').at(-1))
  if(actual.status==='unsupported'||actual.status==='inputError')
    throw Error('Lean rejected declared case '+c.name+': '+JSON.stringify(actual))
  const evm = await createEVM({common})
  await evm.stateManager.putAccount(parent,new Account())
  await evm.stateManager.putAccount(child,new Account())
  await evm.stateManager.putCode(parent,hexToBytes('0x'+c.parentHex))
  await evm.stateManager.putCode(child,hexToBytes('0x'+c.childHex))
  const result=await evm.runCall({to:parent,caller:origin,gasLimit:parentGas})
  const exec=result.execResult
  const err=String(exec.exceptionError?.error??'')
  const exceptional=Boolean(err)&&!err.toLowerCase().includes('revert')
  const expected={status:exceptional?'exceptional':'stopped'}
  const data=await evm.stateManager.getStorage(child,new Uint8Array(32))
  expected.slot0=data.length?BigInt('0x'+Buffer.from(data).toString('hex')).toString():'0'
  if(exceptional){
    expected.gasRemaining='0'
  }else{
    expected.gasRemaining=(parentGas-exec.executionGasUsed).toString()
    const stack=exec.runState?.stack?.getStack()
    if(!Array.isArray(stack)||stack.length!==1)
      throw Error('independent EthereumJS parent did not expose the CALL result flag')
    expected.flag=stack[0].toString()
  }
  const differing=Object.keys(expected).filter(k=>actual[k]!==expected[k])
  if(expected.status!==c.status||expected.slot0!==c.slot0||
    (c.flag!==null&&expected.flag!==c.flag))differing.push('reference-vs-declared-expectation')
  if(differing.length)disagreements.push({id:c.name,differing,expected,actual,referenceException:err})
}
const report={
 kind:'real-lean-call-opcode-vs-independent-ethereumjs-cancun',
 comparison:'identical complete parent bytecode containing 0xf1, identical child code',
 count:examples.length,passed:examples.length-disagreements.length,
 mismatches:disagreements.length,
 scope:'one-level zero-value CALL, zero calldata/memory, no precompile, expected stack/exception outcome, gas and storage',
 firstMismatches:disagreements.slice(0,5)
}
console.log(JSON.stringify(report))
if(disagreements.length)process.exitCode=1
