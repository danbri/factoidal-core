import test from "node:test";
import assert from "node:assert/strict";
import {createHash} from "node:crypto";
import {createSnapshotRequest,executeIfCurrent,leaseEqual}
  from "../tools/gssl-sbm11-snapshot.mjs";
import {splitId,packTriples64} from "../tools/gssl-sbm11-webgpu.mjs";

const IRI=0x2000000000000000n;
const BLANK=0x1000000000000000n;
const TRIPLE=0x9000000000000000n;
const KP=IRI+100n,WP=IRI+101n,ATLAS=IRI+102n;
const queryText="PREFIX ex: <http://example.org/> SELECT ?person ?colleague WHERE { ?person ex:knows ?colleague . ?colleague ex:worksOn ex:Atlas }";
const codebookDigest="ab".repeat(32);
const base = () => ({
  sourceId:"sbm11-session-1",
  generation:"generation-7",
  graphId:0n,
  codebookDigest,
  requestNumber:47,
  layout:"direct64Lanes",
  triples:[
    [IRI+1n,KP,BLANK+20n],
    [BLANK+20n,WP,ATLAS],
    [TRIPLE+20n,KP,IRI+1n],
  ],
  queryConstants:{knows:KP,works:WP,atlas:ATLAS},
  queryText,
});
const digest=bytes=>createHash("sha256").update(bytes).digest("hex");
const leWords=values=>{
  const out=Buffer.alloc(values.length*4);
  for(let i=0;i<values.length;i++)out.writeUInt32LE(values[i],i*4);
  return out;
};

test("hashes immutable, exact 64-bit graph words and exact query source",async()=>{
  const props=base(), request=await createSnapshotRequest(props);
  assert.equal(Object.isFrozen(request),true);
  assert.equal(Object.isFrozen(request.lease),true);
  assert.equal(Object.isFrozen(request.graph),true);
  assert.equal(Object.isFrozen(request.graph[0]),true);
  assert.equal(request.graph[0][0],IRI+1n);
  assert.equal(request.lease.graphId,"0");
  assert.equal(request.lease.requestNumber,47);
  assert.equal(request.lease.layout,"direct64Lanes");

  const words=packTriples64(props.triples).words;
  assert.equal(request.lease.graphDigest,digest(leWords(words)));

  const constants=[KP,WP,ATLAS].flatMap(splitId);
  const queryUTF8=Buffer.from(queryText,"utf8");
  const textLength=Buffer.alloc(4);textLength.writeUInt32LE(queryUTF8.length);
  assert.equal(request.lease.queryDigest,digest(Buffer.concat([
    textLength,queryUTF8,leWords(constants),
  ])));

  const graphDigest=request.lease.graphDigest;
  props.triples[0][0]=IRI+999n;
  props.queryConstants.knows=IRI+999n;
  assert.equal(request.graph[0][0],IRI+1n);
  assert.equal(request.query.knows,KP);
  assert.equal(request.lease.graphDigest,graphDigest);
});

test("query text, active graph, codebook, generation and request identity all matter",async()=>{
  const request=await createSnapshotRequest(base());
  const same=await createSnapshotRequest(base());
  assert.equal(leaseEqual(request.lease,same.lease),true);
  for(const [field,replacement] of Object.entries({
    sourceId:"other-source",generation:"generation-8",graphId:"1",
    codebookDigest:"cd".repeat(32),graphDigest:"ef".repeat(32),
    queryDigest:"dd".repeat(32),requestNumber:48,
    layout:"dense32Snapshot",
  })){
    assert.equal(leaseEqual(request.lease,{...request.lease,[field]:replacement}),false,field);
  }
  const differentQuery=await createSnapshotRequest({...base(),queryText:queryText+" ORDER BY ?person"});
  assert.notEqual(request.lease.queryDigest,differentQuery.lease.queryDigest);
  const differentGraph=base();differentGraph.triples[0][0]=IRI+500n;
  const changed=await createSnapshotRequest(differentGraph);
  assert.notEqual(request.lease.graphDigest,changed.lease.graphDigest);
  const differentCodebook=await createSnapshotRequest({...base(),codebookDigest:"cd".repeat(32)});
  assert.notEqual(request.lease.codebookDigest,differentCodebook.lease.codebookDigest);
  const differentGraphId=await createSnapshotRequest({...base(),graphId:IRI+777n});
  assert.notEqual(request.lease.graphId,differentGraphId.lease.graphId);
  assert.equal(leaseEqual(null,request.lease),false);
});

test("admission refuses unspecified or out-of-range inputs",async()=>{
  const bad=[
    {...base(),sourceId:""},
    {...base(),generation:""},
    {...base(),queryText:""},
    {...base(),codebookDigest:"opaque"},
    {...base(),requestNumber:0},
    {...base(),requestNumber:1.2},
    {...base(),layout:"native-u64-wgsl"},
    {...base(),graphId:-1n},
    {...base(),triples:[[1n,2n]]},
    {...base(),triples:[base().triples[0],base().triples[0]]},
  ];
  for(const props of bad)await assert.rejects(createSnapshotRequest(props));
});

test("fresh observed result is clearly NOT a proof certificate",async()=>{
  const request=await createSnapshotRequest(base());
  let called=0;
  const result=await executeIfCurrent(request,{
    current:()=>request.lease,
    execute:async(graph,query,lease)=>{
      called++;
      assert.equal(graph.length,3);
      assert.equal(query.knows,KP);
      assert.equal(lease.requestNumber,47);
      return {gpuWords:[12,13]};
    },
  });
  assert.equal(called,1);
  assert.equal(result.status,"observed-not-certified");
  assert.deepEqual(result.result,{gpuWords:[12,13]});
  assert.equal(leaseEqual(result.lease,request.lease),true);
});

test("stale pre-dispatch and stale post-readback cannot be accepted",async()=>{
  const request=await createSnapshotRequest(base());
  let called=0;
  const before=await executeIfCurrent(request,{
    current:()=>({...request.lease,requestNumber:48}),
    execute:async()=>{called++;return {};},
  });
  assert.equal(before.status,"fallback");
  assert.equal(before.reason,"stale-before-dispatch");
  assert.equal(called,0);

  let current=request.lease;
  const after=await executeIfCurrent(request,{
    current:()=>current,
    execute:async()=>{called++;current={...current,generation:"generation-8"};return {gpuWords:[1]};},
  });
  assert.equal(after.status,"fallback");
  assert.equal(after.reason,"stale-after-readback");
  assert.equal(called,1);
});

test("cancellation, failure, missing output return explicit fallback, not success",async()=>{
  const request=await createSnapshotRequest(base());
  const aborted=new AbortController();aborted.abort();
  let called=0;
  const cancelled=await executeIfCurrent(request,{
    signal:aborted.signal,current:()=>request.lease,
    execute:async()=>{called++;return {};},
  });
  assert.equal(cancelled.reason,"cancelled");
  assert.equal(called,0);

  const during=new AbortController();
  const after=await executeIfCurrent(request,{
    signal:during.signal,current:()=>request.lease,
    execute:async()=>{during.abort();return {gpuWords:[1]};},
  });
  assert.equal(after.reason,"cancelled");

  const broken=await executeIfCurrent(request,{
    current:()=>request.lease,execute:async()=>{throw Error("device lost");},
  });
  assert.match(broken.reason,/device-failed: device lost/);
  assert.equal(broken.result,null);
  const missing=await executeIfCurrent(request,{
    current:()=>request.lease,execute:async()=>null,
  });
  assert.equal(missing.reason,"missing-device-readback");
  assert.equal(missing.result,null);
});
