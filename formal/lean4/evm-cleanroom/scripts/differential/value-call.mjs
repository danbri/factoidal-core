#!/usr/bin/env node
/**
 * EVM CALL(0xf1) with nonzero ETH transfer against a real EthereumJS Cancun EVM.
 *
 * The actual seven-argument parent bytecode is IDENTICAL in both runtimes,
 * including real value, gas, CALL success bit and STOP / REVERT / INVALID.
 * Compare exact gas, caller/target balances, target slot zero, and success
 * bits. This is not a made-up value-transfer oracle.
 *
 * The next protocol slice still needs nested CALL, arbitrary calldata,
 * return-data copying, static mode, precompiles, and transaction receipts.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const parentAddress=createAddressFromString('0x00000000000000000000000000000000000000c1')
const childAddress=createAddressFromString('0x00000000000000000000000000000000000000c3')
const callerAddress=createAddressFromString('0x00000000000000000000000000000000000000c2')
const common=new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const CHILDREN=[
  {name:'existing-stop',code:'00',balance:0n,nonce:0n},
  {name:'existing-write',code:'600160005500',balance:0n,nonce:0n},
  {name:'existing-revert',code:'600160005560006000fd',balance:0n,nonce:0n},
  {name:'existing-invalid',code:'6001600055fe',balance:0n,nonce:0n},
  {name:'existing-return',code:'60006000f3',balance:7n,nonce:0n},
  {name:'existing-noop-nonce',code:'',balance:0n,nonce:1n},
]
const GAS=[
  [11599,0],[11600,0],[11601,0],[11601,1],
  [13900,0],[17000,65535],[20000,65535],
  [35000,30000],[50000,30000],[50000,0],
  [100000,65535],
]
const ENDINGS=[{name:'STOP',code:'00',status:'stopped'},
               {name:'REVERT',code:'5f5ffd',status:'reverted'},
               {name:'INVALID',code:'fe',status:'exceptional'}]
const REQUESTS_DOUBLE=[[50000,30000],[120000,65535]]
function instruction(request,value) {
  if(request<0||request>65535||value<1||value>65535)
    throw Error('input outside PUSH2 domain')
  // 4 PUSH0: outSize,outOffset,inSize,inOffset. Then PUSH2(value),
  // PUSH1(to), PUSH2(gas), CALL; 4*2+3+3+3 = 17 gas per setup.
  return '5f5f5f5f61'+value.toString(16).padStart(4,'0')+
    '60c361'+request.toString(16).padStart(4,'0')+'f1'
}
function parentProgram(request,value,end='00',calls=1) {
  return instruction(request,value).repeat(calls)+end
}
function lean(parent,child,gas,parentBalance,childBalance,childNonce) {
  const p=spawnSync('lake',[
    'exe','evm-subset','--call-opcode',parent,child,
    String(gas),'100',String(parentBalance),String(childBalance),String(childNonce),
  ],{encoding:'utf8',timeout:60000,maxBuffer:1024*1024})
  if(p.error||p.status!==0)
    throw Error('Lean 0xf1 program failed: '+String(p.error??p.stderr))
  const out=JSON.parse(p.stdout.trim().split('\n').at(-1))
  if(['indeterminate','inputError'].includes(out.status))
    throw Error('unexpected incomplete CALL slice: '+JSON.stringify(out))
  return out
}
async function reference(parent,child,gas,parentBalance,childBalance,childNonce) {
  const evm=await createEVM({common})
  await evm.stateManager.putAccount(parentAddress,new Account(0n,parentBalance))
  await evm.stateManager.putAccount(childAddress,new Account(childNonce,childBalance))
  await evm.stateManager.putCode(parentAddress,hexToBytes('0x'+parent))
  if(child.length) await evm.stateManager.putCode(childAddress,hexToBytes('0x'+child))
  const {execResult:out}=await evm.runCall({
    caller:callerAddress,to:parentAddress,gasLimit:BigInt(gas),
  })
  let status='stopped'
  if(out.exceptionError) {
    const err=String(out.exceptionError.error??out.exceptionError)
    status=/revert/i.test(err)?'reverted':'exceptional'
  }
  const code=await evm.stateManager.getStorage(childAddress,new Uint8Array(32))
  const slot0=code.length?BigInt('0x'+Buffer.from(code).toString('hex')).toString():'0'
  const pa=await evm.stateManager.getAccount(parentAddress)
  const ca=await evm.stateManager.getAccount(childAddress)
  const stack=out.runState?.stack?.getStack()
  if(status==='stopped' && (!Array.isArray(stack)||stack.length<1))
    throw Error('EthereumJS did not expose real parent result stack')
  return {
    status,
    gasRemaining:(BigInt(gas)-out.executionGasUsed).toString(),
    parentBalance:(pa?.balance??0n).toString(),
    childBalance:(ca?.balance??0n).toString(),
    childNonce:(ca?.nonce??0n).toString(),
    slot0,stack:Array.isArray(stack)?stack.map(String).reverse():[],
  }
}
const cases=[]
for(const child of CHILDREN)
  for(const [gas,request] of GAS)
    for(const funded of [false,true])
      for(const ending of ENDINGS)
        cases.push({
          name:child.name+':'+gas+':'+request+':'+(funded?'funded':'unfunded')+':'+ending.name,
          child,request,gas:gas+17,amount:2,
          funded,ending:ending.code,calls:1,
        })
// Uncreated target: the EIP-161 new-account 25k charge matters.
for(const [gas,request]of [[36599,0],[36600,0],[36601,0],[40000,30000],[50000,65535]])
  for(const funded of [false,true])
    for(const ending of ENDINGS)
      cases.push({
        name:'new-empty:'+gas+':'+request+':'+funded+':'+ending.name,
        child:{name:'new-empty',code:'',balance:0n,nonce:0n},
        request,gas:gas+17,amount:2,funded,ending:ending.code,calls:1,
      })
// Warm second CALL must be charged 100 rather than 2600, and independent
// balance transfer/rollback is observed after both calls.
for(const child of [CHILDREN[0],CHILDREN[1],CHILDREN[2],CHILDREN[3],
                    CHILDREN[4],CHILDREN[5]])
  for(const [gas,request]of REQUESTS_DOUBLE)
    for(const funded of [false,true])
      cases.push({
        name:child.name+':double:'+gas+':'+request+':'+funded,
        child,request,gas:gas+34,amount:2,funded,ending:'00',calls:2,
      })

const failures=[]
let parentsReverted=0,parentsExceptional=0,childFailures=0,childSuccesses=0
let comparisonMutationCaught=false
for(const c of cases) {
  try {
    const parentBalance=c.funded?1000n:0n
    const parent=parentProgram(c.request,c.amount,c.ending,c.calls)
    const exp=await reference(parent,c.child.code,c.gas,parentBalance,
      c.child.balance,c.child.nonce)
    const act=lean(parent,c.child.code,c.gas,parentBalance,c.child.balance,c.child.nonce)
    const mismatch=[]
    for(const field of ['status','gasRemaining','parentBalance','childBalance',
                        'childNonce','slot0'])
      if(act[field]!==exp[field])mismatch.push(field)
    if(exp.status==='stopped'){
      if(JSON.stringify(act.stack)!==JSON.stringify(exp.stack))
        mismatch.push('parent-success-bit-stack')
      for(const bit of exp.stack){
        if(bit==='1')childSuccesses++
        if(bit==='0')childFailures++
      }
    }
    if(exp.status==='reverted')parentsReverted++
    if(exp.status==='exceptional')parentsExceptional++
    if(!comparisonMutationCaught && act.gasRemaining===exp.gasRemaining)
      comparisonMutationCaught =
        act.gasRemaining!==(BigInt(exp.gasRemaining)+1n).toString()
    if(mismatch.length)failures.push({case:c.name,mismatch,exp,act})
  }catch(err) {
    failures.push({case:c.name,error:String(err)})
  }
}
const report={
  kind:'EVM 0xf1 actual value transfer and stipend differential',
  fork:'Cancun',oracle:'@ethereumjs/evm@10.1.3 real parent bytecode',
  compared:cases.length,matched:cases.length-failures.length,
  mismatches:failures.length,parentsReverted,parentsExceptional,
  childFailures,childSuccesses,comparisonMutationCaught,
  comparedFields:['parent/child balances','parent actual CALL success bits',
    'exact gas','child storage','child account nonce','parent revert/exception'],
  limits:'Nonzero value 0xf1, small concrete accounts; no calldata, returndata, nested calls, precompiles, static mode or full transaction/receipt',
  firstFailures:failures.slice(0,8),
}
console.log(JSON.stringify(report))
if(failures.length||!comparisonMutationCaught||childFailures===0||childSuccesses===0||
   parentsReverted===0||parentsExceptional===0) process.exitCode=1
