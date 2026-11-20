#!/usr/bin/env node
/**
 * Differential check of the deliberately scoped WorldCall.callZeroValue API
 * against a REAL EthereumJS Cancun parent bytecode program containing 0xF1.
 *
 * The Lean API does NOT execute the CALL opcode: subtract the 16 gas used
 * by the independent reference parent's argument PUSH instructions before
 * supplying its parentGas parameter. We compare exactly the child outcome,
 * parent gas remaining and persistent child storage.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const TARGET = 0xc3
const parentAddress = createAddressFromString('0x00000000000000000000000000000000000000c1')
const childAddress = createAddressFromString('0x00000000000000000000000000000000000000c3')
const callerAddress = createAddressFromString('0x00000000000000000000000000000000000000c2')
// PUSH0 ×5 (out-size, out-offset, in-size, in-offset, value),
// PUSH1 0xc3, PUSH2 0x7530 (30000 gas), CALL, STOP.
// The first seven pushes consume 5*2 + 3 + 3 = 16 gas.
const parentCode = hexToBytes('0x5f5f5f5f5f60c3617530f100')
const parentGas = 50000
const pushGas = 16
const requested = 30000
const cases = [
  {name:'store-and-stop', code:'600160005500', status:'success'},
  {name:'store-then-revert', code:'600160005560006000fd', status:'revert'},
  {name:'store-then-invalid', code:'6001600055fe', status:'exception'},
  {name:'empty-stop', code:'00', status:'success'}
]
const common = new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const failures=[]
const records=[]
for(const c of cases){
  const lean = spawnSync('lake',[
    'exe','evm-subset','--call-slice',c.code,String(TARGET),
    String(parentGas-pushGas),String(requested),'50'
  ],{encoding:'utf8',timeout:60000,maxBuffer:1024*1024})
  if(lean.error || lean.status!==0) throw Error('Lean call slice failed: '+String(lean.error??lean.stderr))
  const actual=JSON.parse(lean.stdout.trim().split('\n').at(-1))
  if(actual.status==='unsupported'||actual.status==='inputError')
    throw Error('Lean returned unsupported in declared test '+c.name)
  const evm=await createEVM({common})
  await evm.stateManager.putAccount(parentAddress,new Account())
  await evm.stateManager.putAccount(childAddress,new Account())
  await evm.stateManager.putCode(parentAddress,parentCode)
  await evm.stateManager.putCode(childAddress,hexToBytes('0x'+c.code))
  const result=await evm.runCall({
    caller:callerAddress,to:parentAddress,gasLimit:BigInt(parentGas)
  })
  const execution=result.execResult
  if(execution.exceptionError) throw Error('independent parent failed: '+
    String(execution.exceptionError.error??execution.exceptionError))
  const stack=execution.runState?.stack?.getStack()
  if(!Array.isArray(stack)||stack.length!==1)
    throw Error('reference parent result stack not available/one item')
  const successFlag=stack[0]===1n
  const storage=await evm.stateManager.getStorage(childAddress,new Uint8Array(32))
  const current=storage.length
    ? BigInt('0x'+Buffer.from(storage).toString('hex')).toString() : '0'
  const expected={
    status:successFlag?'success':(c.status==='revert'?'revert':'exception'),
    gasRemaining:(BigInt(parentGas)-execution.executionGasUsed).toString(),
    slot0:current
  }
  const different=Object.keys(expected).filter(k=>actual[k]!==expected[k])
  records.push({name:c.name,expected,actual,different})
  if(different.length||expected.status!==c.status)
    failures.push(records.at(-1))
}
const report={
  kind:'independent-real-call-opcode-vs-Lean-child-API',
  fork:'Cancun',oracle:'@ethereumjs/evm@10.1.3 runCall',
  compared:cases.length,passed:cases.length-failures.length,
  failed:failures.length,comparisonFields:['status','gasRemaining','slot0'],
  scope:'zero-value, no calldata/returndata, one-level calls to existing contract; Lean scheduler API, NOT Lean CALL instruction',
  firstFailures:failures.slice(0,4)
}
console.log(JSON.stringify(report))
if(failures.length)process.exitCode=1
