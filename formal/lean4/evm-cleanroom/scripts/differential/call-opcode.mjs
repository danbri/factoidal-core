#!/usr/bin/env node
/**
 * Actual CALL 0xf1 Lean opcode execution versus independent EthereumJS Cancun.
 *
 * Not the old --call-slice API: this submits the IDENTICAL assembled parent
 * bytecode to the Lean interpreter and the EthereumJS EVM, observing
 * parent CALL success-bit stack, gas, committed child storage and rollback.
 * Covers parent STOP/REVERT/INVALID and warm second CALL in one parent frame.
 *
 * The legacy corpus uses zero-value, empty-window, single-depth CALLs.
 * Nonempty input, actual identity precompile and a still-unimplemented precompile are checked separately.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const parentAddress = createAddressFromString('0x00000000000000000000000000000000000000c1')
const childAddress = createAddressFromString('0x00000000000000000000000000000000000000c3')
const callerAddress = createAddressFromString('0x00000000000000000000000000000000000000c2')
const common = new Common({chain: Mainnet, hardfork: Hardfork.Cancun})
const executable = process.argv[2]
const children = [
  {name: 'stop', code: '00'},
  {name: 'write-and-stop', code: '600160005500'},
  {name: 'write-and-revert', code: '600160005560006000fd'},
  {name: 'write-and-invalid', code: '6001600055fe'},
  {name: 'return-empty', code: '60006000f3'},
  {name: 'arithmetic', code: '600260030100'},
]
const budgets = [
  [2599,0],[2600,0],[2600,65535],[2601,1],[2663,65535],
  [2664,65535],[2665,65535],[3100,500],[3100,65535],
  [7400,30000],[9900,30000],[25055,65535],[25056,65535],
  [25057,65535],[47400,30000],[47400,65535],[197400,65535],
]
const endings = [
  {name: 'parent-stop', hex: '00'},
  {name: 'parent-revert', hex: '5f5ffd'},
  {name: 'parent-invalid', hex: 'fe'},
]
function opcode(requested) {
  if (!Number.isInteger(requested) || requested<0 || requested>65535)
    throw Error('requested gas exceeds PUSH2 boundary')
  return '5f5f5f5f5f60c361' + requested.toString(16).padStart(4,'0') + 'f1'
}
function program(requested, ending, calls=1) {
  return opcode(requested).repeat(calls) + ending
}
function leanOutcome(parent, child, totalGas) {
  const args = ['--call-opcode',parent,child,String(totalGas),'100']
  const proc = spawnSync(executable ?? 'lake', executable ? args : ['exe','evm-subset',...args],
    {encoding:'utf8',timeout:60000,maxBuffer:1024*1024})
  if (proc.error || proc.status!==0)
    throw Error('Lean real-opcode executable failed '+String(proc.error??proc.stderr))
  return JSON.parse(proc.stdout.trim().split('\n').at(-1))
}
function lean(parent, child, totalGas) {
  const json = leanOutcome(parent, child, totalGas)
  if (json.status==='indeterminate' || json.status==='inputError')
    throw Error('Lean admitted no supported outcome: '+JSON.stringify(json))
  return json
}
async function ethereumjs(parent, child, totalGas) {
  const evm=await createEVM({common})
  await evm.stateManager.putAccount(parentAddress,new Account())
  await evm.stateManager.putAccount(childAddress,new Account())
  await evm.stateManager.putCode(parentAddress,hexToBytes('0x'+parent))
  await evm.stateManager.putCode(childAddress,hexToBytes('0x'+child))
  const result=await evm.runCall({
    caller:callerAddress,to:parentAddress,gasLimit:BigInt(totalGas),
  })
  const ex=result.execResult
  const e=String(ex.exceptionError?.error??'')
  const status=e ? (/revert/i.test(e)?'reverted':'exceptional') :
    parent.endsWith('5f5ff3')?'returned':'stopped'
  const storage=await evm.stateManager.getStorage(childAddress,new Uint8Array(32))
  const slot0=storage.length ? BigInt('0x'+Buffer.from(storage).toString('hex')).toString():'0'
  const stack=ex.runState?.stack?.getStack()
  if (status==='stopped' && (!Array.isArray(stack) || stack.length<1))
    throw Error('reference parent stack unavailable')
  return {status,
    gasRemaining:(BigInt(totalGas)-ex.executionGasUsed).toString(),
    slot0,stack:Array.isArray(stack)?stack.map(String).reverse():[],
  }
}
const records = []
const failures = []
let parentReverts=0, parentExceptions=0, childSuccesses=0, childFailures=0
let gasMutationRejected=false
async function check(name,parent,child,totalGas,compareStack=true) {
  try {
    const expected=await ethereumjs(parent,child,totalGas)
    const actual=lean(parent,child,totalGas)
    const mismatches=[]
    if(actual.status!==expected.status)mismatches.push('parent-status')
    if(actual.gasRemaining!==expected.gasRemaining)mismatches.push('parent-gas')
    if(actual.slot0!==expected.slot0)mismatches.push('child-slot0')
    if (compareStack && expected.status==='stopped' &&
       JSON.stringify(actual.stack)!==JSON.stringify(expected.stack))
      mismatches.push('actual-parent-CALL-success-bits')
    if(expected.status==='reverted')parentReverts++
    if(expected.status==='exceptional')parentExceptions++
    if(expected.status==='stopped' && expected.stack?.[0]==='1') childSuccesses++
    if(expected.status==='stopped' && expected.stack?.[0]==='0') childFailures++
    if(!gasMutationRejected && actual.gasRemaining===expected.gasRemaining)
      gasMutationRejected =
        actual.gasRemaining!==(BigInt(expected.gasRemaining)+1n).toString()
    const item={name,expected,actual,mismatches}
    records.push(item)
    if(mismatches.length)failures.push(item)
  }catch(error){
    const item={name,error:String(error)}
    records.push(item)
    failures.push(item)
  }
}
for(const child of children) {
  for(const [available,requested] of budgets) {
    for(const ending of endings) {
      const name=[child.name,available,requested,ending.name].join(':')
      await check(name,program(requested,ending.hex),child.code,available+16)
    }
  }
}
for(const child of children) {
  for(const [available,requested] of [
    [50000,30000],[3000,100],[25000,65535],[197400,65535],
  ]) {
    await check(child.name+':two-CALLs:'+available+':'+requested,
      program(requested,'00',2),child.code,available+16*2)
  }
}
// The parent writes one input byte. Both engines must load and store it in the child.
const nonemptyInput='602a5f535f5f60015f5f60c3617530f100'
const inputReadingChild='5f355f5500'
const validReference=await ethereumjs(nonemptyInput,inputReadingChild,50000)
const forwarded=lean(nonemptyInput,inputReadingChild,50000)
const nonemptyInputPassed=validReference.status==='stopped' &&
  validReference.stack.length===1 && validReference.stack[0]==='1' &&
  validReference.slot0===(0x2an<<248n).toString() &&
  Object.keys(validReference).every(key=>JSON.stringify(forwarded[key])===JSON.stringify(validReference[key]))
const identityCall='5f5f5f5f5f6004617530f100'
const identityReference=await ethereumjs(identityCall,'',50000)
const identityActual=leanOutcome(identityCall,'',50000)
const identityMismatchedFields=Object.keys(identityReference).filter(
  key=>JSON.stringify(identityActual[key])!==JSON.stringify(identityReference[key]))
const identityPrecompileMatched=identityReference.status==='stopped' &&
  JSON.stringify(identityReference.stack)===JSON.stringify(['1']) &&
  identityMismatchedFields.length === 0
// Other reserved precompiles must not be executed as arbitrary empty bytecode.
const otherPrecompile='5f5f5f5f5f6001617530f100'
const otherReference=await ethereumjs(otherPrecompile,'',50000)
const outOfScope=leanOutcome(otherPrecompile,'',50000)
const precompileScopeRefused=otherReference.status==='stopped' &&
  JSON.stringify(otherReference.stack)===JSON.stringify(['1']) &&
  outOfScope.status==='indeterminate' &&
  outOfScope.reason==='unsupportedFork'

const report={
  kind:'Lean actual-opcode-0xf1-vs-independent-EthereumJS-real-parent-bytecode',
  oracle:'@ethereumjs/evm@10.1.3 Hardfork.Cancun',
  compared:records.length,matched:records.length-failures.length,
  mismatches:failures.length,parentReverts,parentExceptions,
  childSuccesses,childFailures,gasMutationRejected,nonemptyInputPassed,identityPrecompileMatched,
  identityProbe: {mismatchedFields: identityMismatchedFields,
    ...(identityPrecompileMatched ? {} : {expected: identityReference, actual: identityActual})},
  precompileScopeRefused,
  comparedFields:['parent outcome','gas','child storage','actual CALL success bit'],
  scope:'Zero value, empty input/output, one child frame, parent rollback and successive CALLs. Nonempty input, executable identity and unimplemented ECRECOVER precompile are separate controls.',
  firstFailures:failures.slice(0,6),
}
console.log(JSON.stringify(report))
if(failures.length || records.length!==330 || !gasMutationRejected ||
   !nonemptyInputPassed || !identityPrecompileMatched || !precompileScopeRefused || parentReverts===0 || parentExceptions===0 ||
   childSuccesses===0 || childFailures===0)process.exitCode=1
