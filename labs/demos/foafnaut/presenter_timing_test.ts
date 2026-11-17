import {distribution,parseRecords,percentile,samples,spread} from "./presenter_timing.ts";
function equal(actual:unknown,expected:unknown){
  if(JSON.stringify(actual)!==JSON.stringify(expected))throw new Error(JSON.stringify({actual,expected}));
}
Deno.test("nearest-rank percentiles do not average per-run percentiles",()=>{
  equal(percentile([9,1,4,2],.5),2);
  equal(percentile([9,1,4,2],.95),9);
  equal(distribution([]),{count:0,p50Ms:null,p95Ms:null,p99Ms:null,maxMs:null});
  equal(distribution([1,2,3]).p99Ms,null);
  equal(distribution(Array.from({length:100},(_,i)=>i+1)).p99Ms,99);
});
Deno.test("input samples exclude non-scroll traces and retain actual input epoch",()=>{
  const records=parseRecords('diagnostic\n{"type":"native-html-input-latency","kind":"scroll","t":900,"ms":750,"inputEpochMs":1234}\n'+
    '{"type":"native-html-input-latency","kind":"key","t":800,"ms":10}\n'+
    '{"type":"native-html-scroll","ms":3}\n');
  equal(samples(records),[{ms:750,end:900,start:150,inputEpochMs:1234}]);
});
Deno.test("spread retains a bad tail and states run-to-run variation",()=>{
  const result=spread([10,10,10,10,50]);
  equal([result.runs,result.medianMs,result.worstMs,result.minMs],[5,10,50,10]);
  if(result.cv===null||Math.abs(result.cv-16/18)>1e-12)throw new Error("wrong population CV");
});
