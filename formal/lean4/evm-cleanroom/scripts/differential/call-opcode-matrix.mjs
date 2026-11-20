#!/usr/bin/env node
/**
 * Deterministic boundary matrix for actual Lean opcode F1 versus independently
 * executing the same parent and child bytes in EthereumJS Cancun.
 *
 * 6 parent gas limits × 5 requested child gas amounts × 4 child outcomes =
 * 120 distinct inputs. Full parent code includes opcode CALL, *not* the
 * separate WorldCall scheduler API. Fail closed on reference errors,
 * unexpected/unsupported Lean outcomes, or any changed observable.
 */
import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const paddr = createAddressFromString('0x00000000000000000000000000000000000000c1')
const target = createAddressFromString('0x00000000000000000000000000000000000000c3')
const origin = createAddressFromString('0x00000000000000000000000000000000000000c2')
const common = new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const parents=[2615,2616,2617,3000,5000,50000]
const requests=[0,1,100,10000,60000]
const children=[
  {name:'stop',hex:'00'},
  {name:'sstore',hex:'600160005500'},
  {name:'store-revert',hex:'600160005560006000fd'},
  {name:'store-invalid',hex:'6001600055fe'},
]
const hex16=n=>n.toString(16).padStart(4,'0')
const cases=[]
for(const gas of parents)for(const request of requests)for(const child of children)
  cases.push({gas,request,child:child.name,childHex:child.hex,
    parentHex:'5f5f5f5f5f60c361'+hex16(request)+'f100'})
if(cases.length!==120)throw Error('incorrect fixture count')
const raw=cases.map(c=>JSON.stringify(c)).join('\n')+'\n'
const sha256=createHash('sha256').update(raw).digest('hex')
const failures=[]
for(let i=0;i<cases.length;i++){
  const c=cases[i]
  const lean=spawnSync('lake',['exe','evm-subset','--call-opcode',
    c.parentHex,c.childHex,'195',String(c.gas),'30','30'],{
    encoding:'utf8',timeout:60000,maxBuffer:1024*1024
  })
  if(lean.error || lean.status!==0) throw Error('Lean invocation failed for '+i+': '+
    String(lean.error??lean.stderr))
  let actual
  try {actual=JSON.parse(lean.stdout.trim().split('\n').at(-1))}
  catch {throw Error('non-JSON Lean result for '+i)}
  if(actual.status!=='stopped'&&actual.status!=='exceptional')
    throw Error('unexpected Lean unsupported/error input '+i+': '+JSON.stringify(actual))
  const evm=await createEVM({common})
  await evm.stateManager.putAccount(paddr,new Account())
  await evm.stateManager.putAccount(target,new Account())
  await evm.stateManager.putCode(paddr,hexToBytes('0x'+c.parentHex))
  await evm.stateManager.putCode(target,hexToBytes('0x'+c.childHex))
  let result
  try{result=await evm.runCall({to:paddr,caller:origin,gasLimit:BigInt(c.gas)})}
  catch(e){throw Error('independent reference error for '+i+': '+e)}
  const ex=result.execResult
  const exception=Boolean(ex.exceptionError)
  const post=await evm.stateManager.getStorage(target,new Uint8Array(32))
  const expected={
    status:exception?'exceptional':'stopped',
    gasRemaining:exception?'0':(BigInt(c.gas)-ex.executionGasUsed).toString(),
    slot0:post.length ? BigInt('0x'+Buffer.from(post).toString('hex')).toString():'0'
  }
  if(!exception){
    const stack=ex.runState?.stack?.getStack()
    if(!Array.isArray(stack)||stack.length!==1)
      throw Error('reference missing exactly one CALL status word at '+i)
    expected.flag=stack[0].toString()
  }
  const mismatch=Object.keys(expected).filter(k=>actual[k]!==expected[k])
  if(mismatch.length)failures.push({index:i,input:c,mismatch,expected,actual,
    referenceException:String(ex.exceptionError?.error??'')})
}
const summary={
 kind:'Lean-real-CALL-EIP150-boundary-matrix',fork:'Cancun',
 reference:'@ethereumjs/evm@10.1.3',
 corpusSha256:sha256,
 parentGasValues:parents,requestedGasValues:requests,
 childScenarios:children.map(x=>x.name),
 compared:cases.length,passed:cases.length-failures.length,
 mismatches:failures.length,unsupported:0,
 comparedFields:['status','gasRemaining','slot0','flag on success'],
 firstFailures:failures.slice(0,6)
}
console.log(JSON.stringify(summary))
if(failures.length)process.exitCode=1
