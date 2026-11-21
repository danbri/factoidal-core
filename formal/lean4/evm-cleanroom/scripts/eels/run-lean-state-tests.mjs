#!/usr/bin/env node
/**
 * Narrow ACTUAL EELS state-test execution using the Lean EVM for the
 * no-contract-code execution phase, plus an explicit restricted transaction
 * state transition and EthereumJS's Merkle-state serializer.
 *
 * Supported:
 *   Prague, valid signed type-0/1/2 tx, no target code, no value,
 *   one sender account and no storage, empty data or calldata.
 *   Fee floor from EIP-7623; transaction nonces and fee redistribution.
 *
 * Unsupported cases are counted, NOT reported as passed.
 * EthereumJS is used here for signature/envelope parsing and trie
 * serialization, NOT to execute the transaction. This trust boundary is
 * explicit and the reference EthereumJS runTx test is a separate gate.
 *
 * node scripts/eels/run-lean-state-tests.mjs
 *    --fixture /tmp/test_eip_7623.json --out .lake/eels/results.json
 */
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { Common, Hardfork, Mainnet } from '@ethereumjs/common';
import { createTxFromRLP } from '@ethereumjs/tx';
import { bytesToHex, createAccount, createAddressFromString, hexToBytes } from '@ethereumjs/util';
import { createVM } from '@ethereumjs/vm';

function flags(args) {
  const o={};
  for(let i=0;i<args.length;i+=2){
    if(!args[i]?.startsWith('--') || args[i+1]===undefined)
      throw Error('expected --fixture FILE --out FILE');
    o[args[i].slice(2)]=args[i+1];
  }
  if(!o.fixture||!o.out) throw Error('expected --fixture FILE --out FILE');
  return o;
}
const opt=flags(process.argv.slice(2));
const fixtureBytes=readFileSync(opt.fixture);
const fixtureHash=createHash('sha256').update(fixtureBytes).digest('hex');
const data=JSON.parse(fixtureBytes.toString('utf8'));
if(!data||Array.isArray(data)||typeof data!=='object'||Object.keys(data).length===0)
  throw Error('no state test fixtures');
const official={source:'EELS-generated fixtures (EthereumJS mirror)',
  sha256:fixtureHash,format:'state_test'};
const emptyLogHash='0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347';
const cases=[];
let passed=0,unsupported=0,failed=0;
const common=new Common({chain:Mainnet,hardfork:Hardfork.Prague});
function reject(id,reason) {unsupported++;cases.push({id,status:'unsupported',reason});}
function parseHexInt(s,label) {
  if(typeof s!=='string'||!/^(0x[0-9a-fA-F]+)$/.test(s)) throw Error(label+' expected a hex integer, received '+String(s));
  return BigInt(s);
}
function isHash(s){return typeof s==='string' && /^0x[0-9a-fA-F]{64}$/.test(s);}
function sameBytes(a,b){return bytesToHex(a).toLowerCase()===String(b).toLowerCase();}
const eligible=[];
for(const [id,record] of Object.entries(data)){
  const entry=record?.post?.Prague?.[0];
  if(!id.includes('fork_Prague-state_test') || !entry || record.post.Prague.length!==1 ||
     !entry.state || !isHash(entry.hash) || !isHash(entry.logs)){
    reject(id,'not-single-Prague-state-test-vector');continue;
  }
  // The host transition defined below is deliberately NOT a general
  // Ethereum transaction processor. Only positive type-0/1/2 EIP-7623
  // tests enter. No silent fallback to EthereumJS runTx.
  if(!id.endsWith('type_0_protected]') && !id.endsWith('type_0_unprotected]') &&
     !id.endsWith('type_1]') && !id.endsWith('type_2]')){
    reject(id,'transaction-family-not-yet-modelled');continue;
  }
  const tx=record.transaction,pre=record.pre,env=record.env;
  if(!tx||!pre||!env||Object.keys(pre).length!==1 ||
     !Array.isArray(tx.gasLimit)||tx.gasLimit.length!==1||
     !Array.isArray(tx.data)||tx.data.length!==1||
     !Array.isArray(tx.value)||tx.value.length!==1||
     !/^0x[0-9a-fA-F]{40}$/.test(tx.to||'')||
     !/^0x[0-9a-fA-F]{40}$/.test(tx.sender||'')){
    reject(id,'unsupported-transaction-structure');continue;
  }
  const a=Object.entries(pre)[0];
  if(a[0].toLowerCase()!==tx.sender.toLowerCase()||
    a[1].code!=='0x' || Object.keys(a[1].storage||{}).length!==0 ||
    parseHexInt(tx.value[0],'value')!==0n ||
    (Object.keys(entry.state).length<1 || Object.keys(entry.state).length>2) ||
    !(tx.sender.toLowerCase() in Object.fromEntries(Object.keys(entry.state).map(k=>[k.toLowerCase(),true])))){
    reject(id,'requires-nonempty-code-or-storage-or-unsupported-account-set');continue;
  }
  eligible.push({id,record,post:entry});
}
for(const {id,record,post} of eligible){
  try{
    const {transaction:fixtureTx,env,pre}=record;
    const addr=fixtureTx.sender.toLowerCase();
    const account=Object.values(pre)[0];
    const miner=env.currentCoinbase.toLowerCase();
    if(miner===addr || !/^0x[0-9a-f]{40}$/.test(miner))
      throw Error('unexpected miner address');
    const txBytes=post.txbytes;
    if(typeof txBytes!=='string' || !/^0x[0-9a-fA-F]+$/.test(txBytes))
      throw Error('missing signed transaction bytes');
    const parsed=createTxFromRLP(hexToBytes(txBytes),{common});
    const recovered=parsed.getSenderAddress().toString().toLowerCase();
    if(recovered!==addr)throw Error('signature recovered wrong sender');
    if(![0,1,2].includes(parsed.type))throw Error('unsupported signed transaction type');
    const accessList=parsed.accessList??[];
    if(!Array.isArray(accessList))throw Error('invalid EIP-2930 access list representation');
    let storageKeys=0;
    for(const item of accessList){
      if(!Array.isArray(item) || item.length!==2 ||
         !(item[0] instanceof Uint8Array) || !Array.isArray(item[1]) ||
         item[0].length!==20 || item[1].some(key=>!(key instanceof Uint8Array) || key.length!==32))
        throw Error('unsupported EIP-2930 access list shape');
      storageKeys+=item[1].length;
    }
    const accessListGas=2400n*BigInt(accessList.length)+1900n*BigInt(storageKeys);
    if(parsed.to?.toString().toLowerCase()!==fixtureTx.to.toLowerCase())
      throw Error('signed destination differs from fixture');
    if(parsed.nonce!==parseHexInt(fixtureTx.nonce,'nonce')||
       parsed.gasLimit!==parseHexInt(fixtureTx.gasLimit[0],'gasLimit')||
       ((parsed.type<=1 && parsed.gasPrice!==parseHexInt(fixtureTx.gasPrice,'gasPrice')) ||
        (parsed.type===2 && (parsed.maxFeePerGas!==parseHexInt(fixtureTx.maxFeePerGas,'maxFeePerGas') ||
          parsed.maxPriorityFeePerGas!==parseHexInt(fixtureTx.maxPriorityFeePerGas,'maxPriorityFeePerGas'))))||
       parsed.value!==0n||
       !sameBytes(parsed.data,fixtureTx.data[0])){
      throw Error('signed transaction bytes disagree with fixture metadata');
    }
    if(!Array.isArray(fixtureTx.data)||!Array.isArray(fixtureTx.value))
      throw Error('unsupported fixture arrays');
    const calldata=parsed.data;
    const zeroCount=calldata.reduce((n,b)=>n+(b===0?1:0),0);
    const nonzeroCount=calldata.length-zeroCount;
    const startingBalance=parseHexInt(account.balance,'balance');
    const startingNonce=parseHexInt(account.nonce,'nonce');
    if(startingNonce!==parsed.nonce)throw Error('invalid sender nonce');
    const baseFee=parseHexInt(env.currentBaseFee,'baseFee');
    const cap=parsed.type===2 ? parsed.maxFeePerGas : parsed.gasPrice;
    const priority=parsed.type===2 ? parsed.maxPriorityFeePerGas : 0n;

    // Execute the actual Lean EVM first. With no destination code, one STOP
    // step has zero execution-gas cost; this property is machine-checked in
    // EVMCleanroom/EELSBridge.lean for every starting gas amount.
    const frameGas=parsed.gasLimit;
    const lean=spawnSync('lake',['exe','evm-subset','',frameGas.toString(),'1'],{
      encoding:'utf8',timeout:30000,maxBuffer:1024*1024
    });
    if(lean.error || lean.status!==0)
      throw Error('Lean executable error: '+String(lean.error||lean.stderr));
    const vmResult=JSON.parse(lean.stdout.trim().split('\n').at(-1));
    if(vmResult.status!=='ok' || vmResult.halted!==true ||
       vmResult.gasRemaining!==frameGas.toString() ||
       vmResult.stack?.length!==0 || vmResult.memorySizeBytes!=='0')
      throw Error('Lean does not stop without changing empty EVM frame');
    const executionGas=frameGas-BigInt(vmResult.gasRemaining);

    // The actual transaction fee/nonce transition ALSO comes from Lean.
    // JS only supplies decoded, independently checked transaction fields.
    const inputs=[
      zeroCount,nonzeroCount,accessList.length,storageKeys,
      parsed.gasLimit.toString(),cap.toString(),priority.toString(),
      baseFee.toString(),startingBalance.toString(),startingNonce.toString(),
      executionGas.toString(),parsed.type===2?'1':'0'
    ].map(String);
    const feeProcess=spawnSync('lake',['exe','evm-subset','--tx-fee',...inputs],{
      encoding:'utf8',timeout:30000,maxBuffer:1024*1024
    });
    if(feeProcess.error || feeProcess.status!==0)
      throw Error('Lean settlement executable error: '+String(feeProcess.error||feeProcess.stderr));
    const settlement=JSON.parse(feeProcess.stdout.trim().split('\n').at(-1));
    if(settlement.status!=='ok')
      throw Error('Lean settlement refused the signed transaction: '+JSON.stringify(settlement));
    const intrinsic=BigInt(settlement.intrinsicGas);
    const floor=BigInt(settlement.floorGas);
    const charged=BigInt(settlement.chargedGas);
    const price=BigInt(settlement.effectivePrice);
    const afterBalance=BigInt(settlement.senderAfterBalance);
    const afterNonce=BigInt(settlement.senderAfterNonce);
    const minerFee=BigInt(settlement.minerReward);
    const baseFeeBurn=BigInt(settlement.baseFeeBurn);
    // A second implementation checks the calldata/access-list gas schedule;
    // official state-root comparison below is the stronger external check.
    const independentIntrinsic=21000n+4n*BigInt(zeroCount)+
      16n*BigInt(nonzeroCount)+accessListGas;
    if(intrinsic!==independentIntrinsic || afterNonce!==startingNonce+1n ||
       minerFee+baseFeeBurn!==charged*price || charged>parsed.gasLimit)
      throw Error('Lean settlement violates the independently computed input accounting constraints');
    // Build the state root from the Lean-derived gas outcome and independently
    // specified fee/nonce transitions. EthereumJS does NOT execute this tx:
    // it provides only Account serialization and the MPT state-root primitive.
    const stateVM=await createVM({common});
    const senderAddress=createAddressFromString(addr);
    const minerAddress=createAddressFromString(miner);
    await stateVM.stateManager.putAccount(senderAddress,
      createAccount({nonce:startingNonce,balance:startingBalance}));
    await stateVM.stateManager.putAccount(senderAddress,
      createAccount({nonce:afterNonce,balance:afterBalance}));
    if(minerFee>0n){
      await stateVM.stateManager.putAccount(minerAddress,
        createAccount({nonce:0n,balance:minerFee}));
    }
    const root=bytesToHex(await stateVM.stateManager.getStateRoot());
    const postSender=Object.entries(post.state).find(([k])=>k.toLowerCase()===addr)?.[1];
    const postMiner=Object.entries(post.state).find(([k])=>k.toLowerCase()===miner)?.[1];
    if(!postSender || (minerFee>0n)!==Boolean(postMiner) ||
       Object.keys(post.state).length!==(minerFee>0n ? 2 : 1))
      throw Error('post account set mismatch');
    const accountsMatch=BigInt(postSender.balance)===afterBalance &&
      BigInt(postSender.nonce)===afterNonce &&
      (!postMiner || (BigInt(postMiner.balance)===minerFee && BigInt(postMiner.nonce)===0n &&
        postMiner.code==='0x' && !Object.keys(postMiner.storage||{}).length)) &&
      postSender.code==='0x' && !Object.keys(postSender.storage||{}).length;
    if(root.toLowerCase()!==post.hash.toLowerCase()||
       post.logs.toLowerCase()!==emptyLogHash||!accountsMatch)
      throw Error('official post-state mismatch: root='+root+
        ', expected='+post.hash+', accountsMatch='+accountsMatch);
    passed++;
    cases.push({id,status:'pass',fork:'Prague',transactionType:parsed.type,
      gasLimit:parsed.gasLimit.toString(),intrinsicGas:intrinsic.toString(),
      calldataFloorGas:floor.toString(),accessListGas:accessListGas.toString(),chargedGas:charged.toString(),
      baseFeeBurn:baseFeeBurn.toString(),
      leanExecutionGas:executionGas.toString(),coinbaseReward:minerFee.toString(),
      expectedStateRoot:post.hash,computedStateRoot:root,
      observedLogsHash:emptyLogHash,
      proofBoundary:'Lean empty bytecode execution AND Lean fee/nonce settlement; JS decodes signed transaction and serializes EthereumJS Merkle state roots.'});
  }catch(e){
    failed++;
    cases.push({id,status:'fail',reason:String(e)});
  }
}
const total=Object.keys(data).length;
const results={
  schemaVersion:1,
  kind:'EELS-state-test-real-execution-restricted-Lean',
  status:failed?'fail':(passed?'pass':'unsupported-only'),
  provenance:{...official,totalFixtureCases:total,pragueFork:true},
  actualLeanStateTestsExecuted:passed+failed,
  passed,failed,unsupported,
  cases,
  limits:{
    notGeneralEVM:true,
    supported:'Prague EIP-7623 valid signed type-0/1/2 zero-value no-code transactions; Lean fee/nonce/account-balance settlement',
    trusted:['EthereumJS RLP/signature recovery','EthereumJS account/Merkle Patricia trie serializer','JS host transaction field extraction','Lean interpreter/runtime/compiler'],
    notVerified:['signature recovery','EIP-7623 host fee formula','MPT hashing','post state root encoding','full EVM/transaction semantics']
  }
};
mkdirSync(dirname(opt.out),{recursive:true});
writeFileSync(opt.out,JSON.stringify(results,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status:results.status,actualLeanStateTestsExecuted:passed+failed,passed,failed,unsupported,total,
  fixtureSha256:fixtureHash,report:opt.out,
  firstFailure:cases.find(x=>x.status==='fail')||null
})+'\n');
if(failed>0||passed===0||passed+failed+unsupported!==total)process.exit(1);
