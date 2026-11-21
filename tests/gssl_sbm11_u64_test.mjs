import test from "node:test";
import assert from "node:assert/strict";
import {
  parseId,splitId,joinId,isSbm11TaggedId,packTriples64,unpackTriples64,
  referenceBgp64,compareExactRows,compareBags64,COUNT,SCAN,EMIT,
} from "../tools/gssl-sbm11-webgpu.mjs";
import {denseRemap64,decodeDensePairs} from "../tools/gssl-sbm11-dense-u32.mjs";

const IRI=0x2000000000000000n;
const BNODE=0x1000000000000000n;
const LITERAL=0x3000000000000000n;
const TRIPLE=0x9000000000000000n;
const KP=IRI+0x101n, WP=IRI+0x102n, ATLAS=IRI+0x103n;
const CONST={knows:KP,works:WP,atlas:ATLAS};

test("full UInt64 range and exact high/low lanes",()=>{
  const vectors=[0n,1n,0xffffffffn,0x100000000n,
    0x12345678abcdef01n,TRIPLE+1n,(1n<<64n)-1n];
  for(const v of vectors) assert.equal(joinId(...splitId(v)),v);
  assert.deepEqual(splitId(0x12345678abcdef01n),[0xabcdef01,0x12345678]);
  assert.equal(parseId("0x9000000000000003"),TRIPLE+3n);
  assert.equal(parseId("18446744073709551615"),(1n<<64n)-1n);
  assert.equal(splitId(IRI+7n)[0],splitId(TRIPLE+7n)[0]);
  assert.notEqual(splitId(IRI+7n)[1],splitId(TRIPLE+7n)[1]);
  for(const tag of [1n,2n,3n,4n,5n,9n])
    assert.equal(isSbm11TaggedId((tag<<60n)+1n),true);
  assert.equal(isSbm11TaggedId(0n),false);
  for(const v of [12,Number.MAX_SAFE_INTEGER,-1n,1n<<64n,"1.0","1e15","-1",1.5,{},null])
    assert.throws(()=>parseId(v));
  assert.throws(()=>joinId(-1,1));
  assert.throws(()=>joinId(1,0x100000000));
});

test("exact six-word triple stride, including blank nodes and quoted triple IDs",()=>{
  const graph=[
    [IRI+1n,KP,BNODE+123n],
    [BNODE+123n,WP,ATLAS],
    [TRIPLE+3n,KP,IRI+1n],
    [IRI+1n,IRI+0x106n,LITERAL+77n],
  ];
  const {words,triples}=packTriples64(graph);
  assert.equal(words.length,24);
  assert.deepEqual(triples,graph);
  assert.deepEqual(unpackTriples64(words),graph);
  assert.throws(()=>unpackTriples64(new Uint32Array(5)));
  assert.throws(()=>packTriples64([...graph,graph[0]]),/set/);
  assert.throws(()=>packTriples64([[1n,2n]]),/triple/);
  assert.throws(()=>packTriples64([["99999999999999999999999999999","2","3"]]),/range/);
});

test("BGP reference joins by both lanes, never only the low word",()=>{
  const sameLowDifferentTag=TRIPLE+123n, bob=BNODE+123n, alice=IRI+1n;
  const graph=[
    [alice,KP,bob],
    [IRI+2n,KP,sameLowDifferentTag],
    [bob,WP,ATLAS],
    [sameLowDifferentTag,WP,IRI+0x104n],
    [IRI+3n,KP,bob],
  ];
  const expected=[[alice,bob],[IRI+3n,bob]];
  assert.deepEqual(referenceBgp64(graph,CONST),expected);
  assert.equal(compareBags64(expected,expected.slice().reverse()),true);
  assert.equal(compareExactRows(expected,expected.slice().reverse()),false);
  assert.equal(compareBags64(expected,[expected[0],expected[0]]),false);
});

test("independent count/scan/emit WGSL source addresses six-word triples and four-word results",()=>{
  assert.match(COUNT,/let a=6u\*i/);
  assert.match(COUNT,/triples\[b\+1u\]==hi/);
  assert.match(SCAN,/offsets\[cfg\.n\]=sum/);
  assert.match(EMIT,/let dst=4u\*\(offsets\[i\]\+local\)/);
  for(const shader of [COUNT,SCAN,EMIT]){
    assert.doesNotMatch(shader,/\bu64\b/i);
    assert.match(shader,/@compute/);
  }
});

test("full-size fixture retains exact global high-tag IDs",()=>{
  const graph=[];
  for(let i=0n;i<1024n;i++){
    const person=IRI+0x1000n+i;
    const friend=IRI+0x1000n+((i+1n)%1024n);
    graph.push([person,KP,friend]);
    graph.push([person,WP,i%4n===0n?ATLAS:IRI+0x104n]);
  }
  const {words}=packTriples64(graph);
  assert.equal(words.length,graph.length*6);
  const result=referenceBgp64(graph,CONST);
  assert.equal(result.length,256);
});

test("query-local dense remapping is reversible for full-width SBM11 IDs",()=>{
  const high1=0x200000000000002an, high2=0x900000000000002an;
  const graph=[
    [high1,KP,high2],
    [high2,WP,ATLAS],
    [high1,IRI+0x105n,LITERAL+0xabcdefn],
  ];
  const dense=denseRemap64(graph,CONST);
  assert.notEqual(dense.codeOf(high1),dense.codeOf(high2));
  assert.equal(dense.decode(dense.codeOf(high1)),high1);
  assert.equal(dense.decode(dense.codeOf(high2)),high2);
  assert.deepEqual(dense.triples[0],[
    dense.codeOf(high1),dense.codeOf(KP),dense.codeOf(high2)]);
  assert.deepEqual(decodeDensePairs([[dense.codeOf(high1),dense.codeOf(high2)]],dense),
    [[high1,high2]]);
  assert.throws(()=>dense.decode(0),/unbound/);
  assert.throws(()=>dense.decode(0xffffffff),/Unrecognized/);
  assert.throws(()=>denseRemap64(graph,CONST,{maxTerms:2}),/capacity/);
});
