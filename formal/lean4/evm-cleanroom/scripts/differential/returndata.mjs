#!/usr/bin/env node
/**
 * Actual child RETURN/REVERT → parent EIP-211 data operations.
 * Both Lean and EthereumJS execute identical complete parent and child
 * bytecode. This does not implement generalized nested EVM call contexts.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const paddr=createAddressFromString('0x00000000000000000000000000000000000000c1')
const caddr=createAddressFromString('0x00000000000000000000000000000000000000c3')
const caller=createAddressFromString('0x00000000000000000000000000000000000000c2')
const common=new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const callPrefix='5f5f5f5f5f60c3617530f1'
const copyAndStore='600055600160005560016000601f3e60005160015500'
const parentCopy=callPrefix+copyAndStore
const childReturn='60ff60005360016000f3'
const childRevert='60ff60005360016000fd'
const cases=[
 {name:'child-return-copied-to-storage',parent:parentCopy,child:childReturn},
 {name:'child-revert-data-still-copyable',parent:parentCopy,child:childRevert},
 {name:'empty-data-copy-is-exceptional',parent:parentCopy,child:'00'},
 {name:'invalid-child-clears-data-buffer',parent:parentCopy,child:'fe'},
 {name:'return-data-size-after-call',parent:callPrefix+'3d00',child:childReturn}
]
const failed=[]
for(const c of cases){
 const lean=spawnSync('lake',['exe','evm-subset','--call-opcode',c.parent,c.child,
   '195','100000','80','80'],{encoding:'utf8',maxBuffer:2*1024*1024,timeout:60000})
 if(lean.error||lean.status!==0)throw Error('Lean binary failed '+c.name+': '+String(lean.error??lean.stderr))
 const actual=JSON.parse(lean.stdout.trim().split('\n').at(-1))
 if(actual.status==='unsupported'||actual.status==='inputError')
   throw Error('Lean classified declared case unsupported: '+c.name+' '+JSON.stringify(actual))
 const evm=await createEVM({common})
 await evm.stateManager.putAccount(paddr,new Account())
 await evm.stateManager.putAccount(caddr,new Account())
 await evm.stateManager.putCode(paddr,hexToBytes('0x'+c.parent))
 await evm.stateManager.putCode(caddr,hexToBytes('0x'+c.child))
 const res=await evm.runCall({to:paddr,caller,gasLimit:100000n})
 const ex=res.execResult
 const exceptional=Boolean(ex.exceptionError)
 const storage=async slot=>{
   const key=new Uint8Array(32)
   key[31]=slot
   const bytes=await evm.stateManager.getStorage(paddr,key)
   return bytes.length?BigInt('0x'+Buffer.from(bytes).toString('hex')).toString():'0'
 }
 const expected={
   status:exceptional?'exceptional':'stopped',
   gasRemaining:exceptional?'0':(100000n-ex.executionGasUsed).toString(),
   parentSlot0:await storage(0),parentSlot1:await storage(1)
 }
 if(!exceptional){
   const stack=ex.runState?.stack?.getStack()
   if(!Array.isArray(stack))throw Error('independent reference stack unavailable')
   expected.flag=stack.length?stack.at(-1).toString():null
   expected.parentMemoryByte31=BigInt(ex.runState.memoryWordCount)*32n>31n ?
     (ex.runState.memory.read(31,1)[0]??0).toString() : '0'
 }
 const different=Object.keys(expected).filter(k=>expected[k]!==actual[k])
 if(different.length)failed.push({case:c.name,different,expected,actual,
   exception:String(ex.exceptionError?.error??'')})
}
const report={kind:'real-EIP211-returndata-differential',fork:'Cancun',
 oracle:'@ethereumjs/evm@10.1.3',count:cases.length,
 matched:cases.length-failed.length,mismatches:failed.length,
 cases:cases.map(c=>c.name),
 compared:['status','gasRemaining','parentSlot0','parentSlot1','flag','parentMemoryByte31'],
 firstMismatches:failed.slice(0,5)}
console.log(JSON.stringify(report))
if(failed.length) process.exitCode=1
