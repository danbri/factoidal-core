#!/usr/bin/env node
/**
 * All SIX genuine EELS Prague EIP-7623 state-test vectors, including
 * signed EIP-4844 blob type 3 and EIP-7702 authorization type 4.
 * Lean executes the empty destination frame, validates fork-scoped envelope
 * accounting (intrinsic, floor, blob burn, sender debit) and constructs the
 * authorized EOA delegation code/nonce. Signed RLP and secp256k1 recovery,
 * account serialization and Merkle trie hashing are explicit trusted JS.
 *
 * This is a narrow, falsifiable six-fixture gate, NOT arbitrary mainnet tx
 * conformance or a general EVM state-test interpreter. Every omitted case
 * fails CI rather than being counted as a pass.
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
import { bytesToBigInt, bytesToHex, createAccount, createAddressFromString,
  eoaCode7702RecoverAuthority, hexToBytes, SECP256K1_ORDER_DIV_2 } from '@ethereumjs/util';
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
const EXPECTED_TYPES=new Set([0,1,2,3,4]);
const common=new Common({chain:Mainnet,hardfork:Hardfork.Prague});
// The state-test signed type-3 envelope contains versioned hashes but NO
// blob sidecars or KZG commitments/proofs. EthereumJS's 4844 constructor
// nevertheless requires a KZG object. This fail-closed sentinel *throws*
// on every KZG method access: no fake proof can make an invalid sidecar
// pass. Sidecar validation is explicitly outside this signed-envelope gate.
const forbiddenKzg=new Proxy({}, {get(_target,operation){
  throw Error('KZG sidecar operation not permitted in this fixture gate: '+String(operation));
}});
const blobCommon=new Common({chain:Mainnet,hardfork:Hardfork.Prague,
  customCrypto:{kzg:forbiddenKzg}});
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
  // Every one of the six published vectors is expected and must execute.
  // Unknown family/inventory is an explicit gate failure, never a success.
  const expectedType=Number(id.match(/type_([0-4])(?:_(?:unprotected|protected))?\]$/)?.[1]);
  if(!EXPECTED_TYPES.has(expectedType)){
    reject(id,'unexpected-transaction-family');continue;
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
    (Object.keys(entry.state).length<1 || Object.keys(entry.state).length>3) ||
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
    const parsed=createTxFromRLP(hexToBytes(txBytes),{
      common: txBytes.slice(0,4).toLowerCase()==='0x03' ? blobCommon : common
    });
    const recovered=parsed.getSenderAddress().toString().toLowerCase();
    if(recovered!==addr)throw Error('signature recovered wrong sender');
    if(!EXPECTED_TYPES.has(parsed.type) ||
       parsed.type!==Number(id.match(/type_([0-4])(?:_(?:unprotected|protected))?\]$/)?.[1]))
      throw Error('signed transaction type disagrees with official fixture ID');
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
        (parsed.type>=2 && (parsed.maxFeePerGas!==parseHexInt(fixtureTx.maxFeePerGas,'maxFeePerGas') ||
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
    // Independently validate the signed EIP-4844 blob envelope, including
    // exact versioned hashes and fee cap; only excessBlobGas=0 is admitted
    // by the precisely scoped Lean blob-fee model.
    const blobHashes=parsed.type===3 ? parsed.blobVersionedHashes : [];
    if(!Array.isArray(blobHashes) ||
       (parsed.type===3 && (blobHashes.length<1 ||
          parsed.maxFeePerBlobGas!==parseHexInt(fixtureTx.maxFeePerBlobGas,'blob cap') ||
          blobHashes.length!==fixtureTx.blobVersionedHashes?.length ||
          blobHashes.some((hash,i)=>
            typeof hash!=='string' || !/^0x01[0-9a-fA-F]{62}$/.test(hash) ||
            hash.toLowerCase()!==fixtureTx.blobVersionedHashes[i]?.toLowerCase()))) ||
       (parsed.type!==3 && fixtureTx.blobVersionedHashes!==undefined))
      throw Error('signed EIP-4844 blob envelope/hash does not match fixture');
    const excessBlobGas=parseHexInt(env.currentExcessBlobGas,'excessBlobGas');
    if(excessBlobGas!==0n)throw Error('fixture outside separately proved zero-excess blob-fee domain');

    // Independently recover the EIP-7702 authorization signer from the
    // 0x05 || RLP tuple signature; the recovered address, not fixture
    // prose, determines which authority account Lean is asked to change.
    const authorizations=parsed.type===4 ? parsed.authorizationList : [];
    if(!Array.isArray(authorizations) ||
       (parsed.type===4 && (authorizations.length!==1 ||
          fixtureTx.authorizationList?.length!==authorizations.length)) ||
       (parsed.type!==4 && fixtureTx.authorizationList!==undefined))
      throw Error('unexpected EIP-7702 authorization inventory');
    const authorizedAccounts=[];
    for(let i=0;i<authorizations.length;i++){
      const auth=authorizations[i], metadata=fixtureTx.authorizationList[i];
      if(!Array.isArray(auth)||auth.length!==6 ||
         auth.some(part=>!(part instanceof Uint8Array))||
         !metadata)throw Error('bad signed authorization tuple');
      const [chain,delegate,nonce,parity,r,sigS]=auth;
      if(delegate.length!==20 ||
         bytesToBigInt(chain)!==parseHexInt(metadata.chainId,'auth chain') ||
         !sameBytes(delegate,metadata.address) ||
         bytesToBigInt(nonce)!==parseHexInt(metadata.nonce,'auth nonce') ||
         bytesToBigInt(parity)!==parseHexInt(metadata.yParity,'auth yParity') ||
         bytesToBigInt(r)!==parseHexInt(metadata.r,'auth r') ||
         bytesToBigInt(sigS)!==parseHexInt(metadata.s,'auth s') ||
         bytesToBigInt(sigS)>SECP256K1_ORDER_DIV_2)
        throw Error('signed authorization does not match fixture tuple or low-s');
      const authority=eoaCode7702RecoverAuthority(auth).toString().toLowerCase();
      if(authority!==metadata.signer.toLowerCase() ||
         !/^0x[0-9a-f]{40}$/.test(authority) ||
         [addr,miner,fixtureTx.to.toLowerCase()].includes(authority) ||
         pre[authority]!==undefined)
        throw Error('invalid recovered signer or unexpected existing authority');
      const leanAuth=spawnSync('lake',['exe','evm-subset','--prague-authorize',
        bytesToBigInt(chain).toString(),'1',
        bytesToBigInt(nonce).toString(),'0',
        bytesToBigInt(delegate).toString(),'1','1','0'],{
        encoding:'utf8',timeout:30000,maxBuffer:1024*1024});
      if(leanAuth.error||leanAuth.status!==0)
        throw Error('Lean authorization error: '+String(leanAuth.error??leanAuth.stderr));
      const applied=JSON.parse(leanAuth.stdout.trim().split('\n').at(-1));
      if(applied.status!=='ok' || applied.nonce!=='1' ||
         applied.refundGas!=='0'||applied.alreadyExisted!==false ||
         !/^0xef0100[0-9a-f]{40}$/.test(applied.codeHex) ||
         applied.codeHex!=='0xef0100'+bytesToHex(delegate).slice(2).toLowerCase())
        throw Error('Lean EIP-7702 authority transition invalid');
      authorizedAccounts.push({address:authority,nonce:BigInt(applied.nonce),
        code:applied.codeHex,refund:BigInt(applied.refundGas)});
    }
    const startingBalance=parseHexInt(account.balance,'balance');
    const startingNonce=parseHexInt(account.nonce,'nonce');
    if(startingNonce!==parsed.nonce)throw Error('invalid sender nonce');
    const baseFee=parseHexInt(env.currentBaseFee,'baseFee');
    const cap=parsed.type>=2 ? parsed.maxFeePerGas : parsed.gasPrice;
    const priority=parsed.type>=2 ? parsed.maxPriorityFeePerGas : 0n;

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
      executionGas.toString(),parsed.type,
      blobHashes.length,parsed.type===3?parsed.maxFeePerBlobGas.toString():0,
      excessBlobGas.toString(),authorizedAccounts.length,0
    ].map(String);
    const feeProcess=spawnSync('lake',['exe','evm-subset','--prague-tx-fee',...inputs],{
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
    const blobBurn=BigInt(settlement.blobFeeBurn);
    const blobGas=BigInt(settlement.blobGasUsed);
    // A second implementation checks the calldata/access-list gas schedule;
    // official state-root comparison below is the stronger external check.
    const independentIntrinsic=21000n+4n*BigInt(zeroCount)+
      16n*BigInt(nonzeroCount)+accessListGas+
      25000n*BigInt(authorizedAccounts.length);
    const expectedBlobGas=BigInt(blobHashes.length)*131072n;
    const expectedBlobBurn=expectedBlobGas; // zero excess => blob base fee 1
    const tokens=BigInt(zeroCount)+4n*BigInt(nonzeroCount);
    const independentFloor=21000n+10n*tokens;
    if(intrinsic!==independentIntrinsic || floor!==independentFloor ||
       afterNonce!==startingNonce+1n ||
       minerFee+baseFeeBurn+blobBurn!==charged*price+blobBurn ||
       blobGas!==expectedBlobGas || blobBurn!==expectedBlobBurn ||
       charged!== (independentIntrinsic>independentFloor?independentIntrinsic:independentFloor) ||
       charged>parsed.gasLimit ||
       startingBalance-afterBalance!==charged*price+blobBurn)
      throw Error('Lean settlement violates independent Prague accounting bounds');
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
    for(const a of authorizedAccounts){
      const address=createAddressFromString(a.address);
      await stateVM.stateManager.putAccount(address,
        createAccount({nonce:a.nonce,balance:0n}));
      await stateVM.stateManager.putCode(address,hexToBytes(a.code));
    }
    const root=bytesToHex(await stateVM.stateManager.getStateRoot());
    const postAccounts=Object.fromEntries(Object.entries(post.state)
      .map(([key,record])=>[key.toLowerCase(),record]));
    const postSender=postAccounts[addr];
    const postMiner=postAccounts[miner];
    const expectedSet=new Set([addr,...(minerFee>0n?[miner]:[]),
      ...authorizedAccounts.map(a=>a.address)]);
    if(!postSender || (minerFee>0n)!==Boolean(postMiner) ||
       Object.keys(postAccounts).length!==expectedSet.size ||
       Object.keys(postAccounts).some(a=>!expectedSet.has(a)))
      throw Error('post account set mismatch');
    const accountsMatch=BigInt(postSender.balance)===afterBalance &&
      BigInt(postSender.nonce)===afterNonce &&
      (!postMiner || (BigInt(postMiner.balance)===minerFee && BigInt(postMiner.nonce)===0n &&
        postMiner.code==='0x' && !Object.keys(postMiner.storage||{}).length)) &&
      postSender.code==='0x' && !Object.keys(postSender.storage||{}).length &&
      authorizedAccounts.every(a=>{
        const expected=postAccounts[a.address];
        return expected && BigInt(expected.balance)===0n &&
          BigInt(expected.nonce)===a.nonce &&
          expected.code.toLowerCase()===a.code &&
          !Object.keys(expected.storage||{}).length;
      });
    if(root.toLowerCase()!==post.hash.toLowerCase()||
       post.logs.toLowerCase()!==emptyLogHash||!accountsMatch)
      throw Error('official post-state mismatch: root='+root+
        ', expected='+post.hash+', accountsMatch='+accountsMatch);
    passed++;
    cases.push({id,status:'pass',fork:'Prague',transactionType:parsed.type,
      gasLimit:parsed.gasLimit.toString(),intrinsicGas:intrinsic.toString(),
      calldataFloorGas:floor.toString(),accessListGas:accessListGas.toString(),chargedGas:charged.toString(),
      baseFeeBurn:baseFeeBurn.toString(),blobFeeBurn:blobBurn.toString(),
      blobGasUsed:blobGas.toString(),authorizationAccounts:authorizedAccounts.map(a=>({
        address:a.address,nonce:a.nonce.toString(),code:a.code,
        refund:a.refund.toString()})),
      leanExecutionGas:executionGas.toString(),coinbaseReward:minerFee.toString(),
      expectedStateRoot:post.hash,computedStateRoot:root,
      observedLogsHash:emptyLogHash,
      proofBoundary:'Lean empty bytecode, typed Prague envelope fees and EIP-7702 code/nonce transition; trusted EthereumJS RLP/secp256k1 and MPT/Keccak serialization.'});
  }catch(e){
    failed++;
    cases.push({id,status:'fail',reason:String(e)});
  }
}
const total=Object.keys(data).length;
const results={
  schemaVersion:1,
  kind:'EELS-state-test-real-execution-restricted-Lean',
  status:failed||unsupported||passed!==6?'fail':'pass',
  provenance:{...official,totalFixtureCases:total,pragueFork:true},
  actualLeanStateTestsExecuted:passed+failed,
  passed,failed,unsupported,
  cases,
  limits:{
    notGeneralEVM:true,
    supported:'Six official Prague EIP-7623 signed type-0..4 no-destination-code cases: 4844 one blob and 7702 one new authorization; Lean typed fees, authority delegation code and nonces',
    trusted:['EthereumJS RLP and secp256k1 signer/authorization recovery','EIP-4844 KZG sidecars absent and fail-closed (no proof verification claimed)','EthereumJS account/Merkle Patricia trie serializer','JS host transaction field extraction','Lean interpreter/runtime/compiler'],
    notVerified:['independent signature recovery','general EIP-4844 nonzero-excess blob fee','all EIP-7702 authorization permutations','MPT hashing','full EVM/transaction semantics']
  }
};
mkdirSync(dirname(opt.out),{recursive:true});
writeFileSync(opt.out,JSON.stringify(results,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status:results.status,actualLeanStateTestsExecuted:passed+failed,passed,failed,unsupported,total,
  fixtureSha256:fixtureHash,report:opt.out,
  firstFailure:cases.find(x=>x.status==='fail')||null
})+'\n');
if(failed>0||unsupported>0||passed!==6||total!==6||passed+failed+unsupported!==total)process.exit(1);
