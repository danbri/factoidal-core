// Cross-front-end evidence for GDSL 0.2:
// Native Lean *constructs* the PVGraph canonical JSON with typed do-notation;
// JavaScript independently constructs the same graphs; S-expressions round-trip.
// This is finite differential testing, not a parser/compiler refinement proof.
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {PVGraph,checkPVGraph,runPVGraphCPU,toPVSexpr,fromPVSexpr}
  from "../npm/factoidal/lib/gdsl-graph.mjs";

const builders={
  glyph(){
    const g=PVGraph();
    const advances=g.input("advances");
    const spaced=g.op("u32.map.add",{x:advances},{value:1},{id:"spacing"});
    const pens=g.op("u32.scan.sum",{x:spaced},{},{id:"penPositions"});
    const width=g.op("u32.reduce.sum",{x:spaced},{},{id:"lineWidth"});
    g.output("penPositions",pens,"buffer<u32>",{id:"penOut"});
    g.output("lineWidth",width,"scalar<u32>",{id:"widthOut"});
    return g.build();
  },
  motion(){
    const g=PVGraph();
    const positions=g.input("positions");
    const velocities=g.input("velocities");
    const delta=g.op("u32.map.mul",{x:velocities},{value:4},{id:"delta"});
    const next=g.op("u32.zip.add",{a:positions,b:delta},{},{id:"next"});
    const total=g.op("u32.reduce.sum",{x:next},{},{id:"total"});
    g.output("positionsAfterStep",next,"buffer<u32>",{id:"positionsOut"});
    g.output("positionChecksum",total,"scalar<u32>",{id:"checksumOut"});
    return g.build();
  },
  basic(){
    const g=PVGraph();
    const template=g.input("template");
    const constant=g.op("u32.scalar.const",{},{value:29},{id:"constant"});
    const broadcast=g.op("u32.broadcast",{value:constant,shape:template},
      {},{id:"broadcast"});
    const offset=g.op("u32.zip.add",{a:template,b:broadcast},{},{id:"offset"});
    g.output("result",offset,"buffer<u32>",{id:"resultOut"});
    return g.build();
  },
  generic(){
    const g=PVGraph();
    const pixels=g.input("pixels");
    const masked=g.op("u32.map.xor",{x:pixels},{value:16711935},{id:"mask"});
    const checksum=g.op("u32.reduce.sum",{x:masked},{},{id:"checksum"});
    g.output("rgbaWords",masked,"buffer<u32>",{id:"rgbaOut"});
    g.output("checksum",checksum,"scalar<u32>",{id:"checksumOut"});
    return g.build();
  },
  generated(){
    const g=PVGraph();
    const samples=g.input("samples");
    const adjusted=g.op("u32.map.mul",{x:samples},{value:3});
    const total=g.op("u32.reduce.sum",{x:adjusted},{});
    g.output("adjusted",adjusted);
    g.output("sum",total,"scalar<u32>");
    return g.build();
  },
};

const path=process.argv[2];
if(!path)throw Error("Usage: node tools/pvgraph-lean-builder-diff.mjs lean-results.jsonl");
const lines=readFileSync(path,"utf8").trim().split(/\r?\n/);
const observed=lines.filter(Boolean).map(line=>JSON.parse(line));
assert.equal(observed.length,Object.keys(builders).length);
const seen=new Set();
for(const record of observed){
  const id=record.case;
  assert.equal(typeof builders[id],"function",`unknown fixture ${id}`);
  assert(!seen.has(id),`duplicate fixture ${id}`);
  seen.add(id);
  const built=builders[id]();
  assert.deepStrictEqual(record.pvgraph,built,`${id}: Lean and JS differ in canonical IR`);
  assert.deepStrictEqual(checkPVGraph(record.pvgraph),built,`${id}: JS rejected Lean IR`);
  const sexpr=toPVSexpr(built);
  assert.deepStrictEqual(fromPVSexpr(sexpr),record.pvgraph,
    `${id}: S-expression failed to round-trip Lean IR`);
  const result=runPVGraphCPU(record.pvgraph,record.bindings);
  assert.deepStrictEqual({...result.outputs},record.outputs,
    `${id}: Lean and JS evaluation diverged`);
}
console.log(JSON.stringify({status:"pass",cases:[...seen],
  checks:["Lean authored JSON equals JS authored JSON",
    "S-expression round-trip", "JS and Lean CPU results agree"],
  limitations:"finite fixtures, not universal compiler/parser or WGSL refinement"}));
