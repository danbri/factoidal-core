#!/usr/bin/env node
/**
 * Actual EVM context opcodes across actual parent -> child CALL 0xf1.
 *
 * Test CALLVALUE (0x34), SELFBALANCE (0x47), ADDRESS (0x30), CALLER (0x33) in a child
 * with zero/nonzero value transfer, and SELFBALANCE in the parent AFTER
 * CALL. Both interpreters execute the *same* parent and child bytecode.
 *
 * This is zero calldata / return-length and one child depth only. No
 * Solidity-to-Lean or JavaScript EVM emulation is used for actual values.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const [executable, ...prefix] = process.argv[2] ? [process.argv[2]] : ['lake', 'exe', 'evm-subset']

const common = new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const P = createAddressFromString('0x00000000000000000000000000000000000000c1')
const C = createAddressFromString('0x00000000000000000000000000000000000000c3')
const X = createAddressFromString('0x00000000000000000000000000000000000000c2')
const children = [
  {name:'CALLVALUE',code:'3460005500'},
  {name:'SELFBALANCE',code:'4760005500'},
  {name:'ADDRESS',code:'3060005500'},
  {name:'CALLER',code:'3360005500'},
  {name:'CALLVALUE+SELFBALANCE',code:'34470160005500'},
]
function program(amount,requested,parentSelfBalance) {
  // outLen=0, outOffset=0, inLen=0, inOffset=0;
  // value=0 -> PUSH0, value>0 -> PUSH2.
  const valuePush = amount===0 ? '5f' : '610002'
  const setup = '5f5f5f5f'+valuePush+'60c361'+requested.toString(16).padStart(4,'0')+'f1'
  const setupGas = amount===0 ? 16 : 17
  const ending = parentSelfBalance ? '4700' : '00'
  return {code:setup+ending,setupGas}
}
function lean(parent,child,gas,parentBalance,childBalance) {
  const p=spawnSync(executable,[
    ...prefix,'--call-opcode',parent,child,String(gas),'80',
    String(parentBalance),String(childBalance),'0',
  ],{encoding:'utf8',timeout:60000,maxBuffer:1024*1024})
  if(p.error||p.status!==0)throw Error('Lean EVM CLI failed '+String(p.error??p.stderr))
  const x=JSON.parse(p.stdout.trim().split('\n').at(-1))
  if(x.status==='inputError'||x.status==='indeterminate')
    throw Error('unsupported claimed CALL context fixture: '+JSON.stringify(x))
  return x
}
async function reference(parent,child,gas,parentBalance,childBalance) {
  const evm=await createEVM({common})
  await evm.stateManager.putAccount(P,new Account(0n,BigInt(parentBalance)))
  await evm.stateManager.putAccount(C,new Account(0n,BigInt(childBalance)))
  await evm.stateManager.putCode(P,hexToBytes('0x'+parent))
  await evm.stateManager.putCode(C,hexToBytes('0x'+child))
  const r=await evm.runCall({caller:X,to:P,gasLimit:BigInt(gas)})
  const output=r.execResult
  const error=String(output.exceptionError?.error??'')
  const status=error?(/revert/i.test(error)?'reverted':'exceptional'):'stopped'
  const pa=await evm.stateManager.getAccount(P)
  const ca=await evm.stateManager.getAccount(C)
  const stored=await evm.stateManager.getStorage(C,new Uint8Array(32))
  const stack=output.runState?.stack?.getStack()
  if(status==='stopped' && (!Array.isArray(stack)||stack.length<1))
    throw Error('EthereumJS missing executed parent CALL stack')
  return {
    status,gasRemaining:(BigInt(gas)-output.executionGasUsed).toString(),
    parentBalance:(pa?.balance??0n).toString(),
    childBalance:(ca?.balance??0n).toString(),
    slot0:stored.length?BigInt('0x'+Buffer.from(stored).toString('hex')).toString():'0',
    stack:Array.isArray(stack)?stack.map(String).reverse():[],
  }
}

const failures=[]
let tested=0,childCommitted=0,childFailed=0,observedParentBalance=0
let mutatedGasRejected=false
for(const child of children) {
  for(const amount of [0,2]) {
    for(const childBalance of [0n,7n]) {
      for(const funded of [false,true]) {
        const parentBalance=funded?1000n:0n
        for(const parentSelfBalance of [false,true]){
          for(const requested of [0,30000]){
            const {code,setupGas}=program(amount,requested,parentSelfBalance)
            const gas=90000+setupGas
            const id=[child.name,amount,childBalance,funded,parentSelfBalance,requested].join(':')
            tested++
            try{
              const expected=await reference(code,child.code,gas,parentBalance,childBalance)
              const actual=lean(code,child.code,gas,parentBalance,childBalance)
              const diffs=[]
              for(const field of ['status','gasRemaining','parentBalance','childBalance','slot0']){
                if(actual[field]!==expected[field])diffs.push(field)
              }
              if(expected.status==='stopped'&&
                 JSON.stringify(actual.stack)!==JSON.stringify(expected.stack))
                diffs.push('full-parent-result-stack')
              if(parentSelfBalance)observedParentBalance++
              if(expected.stack?.includes('1'))childCommitted++
              if(expected.stack?.includes('0'))childFailed++
              if(!mutatedGasRejected && actual.gasRemaining===expected.gasRemaining)
                mutatedGasRejected =
                  actual.gasRemaining!==(BigInt(expected.gasRemaining)+1n).toString()
              if(diffs.length)failures.push({id,diffs,expected,actual})
            }catch(e){failures.push({id,error:String(e)})}
          }
        }
      }
    }
  }
}
const report={
  kind:'nonzero EVM CALL context actual-bytecode differential',
  fork:'Cancun',oracle:'@ethereumjs/evm@10.1.3',
  compared:tested,passed:tested-failures.length,failed:failures.length,
  childCommitted,childFailed,observedParentBalance,mutatedGasRejected,
  oracleFields:['stack including parent post-CALL SELFBALANCE','gas',
    'actual child CALLVALUE/SELFBALANCE/ADDRESS storage','both balances','status'],
  limitations:'one child depth, no calldata/returndata/precompiles/CREATE',
  firstFailures:failures.slice(0,5),
}
console.log(JSON.stringify(report))
if(tested!==160||failures.length||!mutatedGasRejected||
   childCommitted===0||childFailed===0||observedParentBalance===0)
  process.exitCode=1
