// Compare actual Lean SPARQL bindings with actual WebGPU join outputs.
// SPARQL solution sequences may be ORDER BY sorted; BGP semantics are a
// multiset. Never compare unordered GPU output against SPARQL row positions.
const strictWord = x => Number.isInteger(x) && x >= 0 && x <= 0xffffffff;
function tally(pairs) {
  const found = new Map();
  for (const pair of pairs) {
    if (!Array.isArray(pair) || pair.length !== 2 || !pair.every(strictWord))
      throw new TypeError("A result must contain two unsigned 32-bit word IDs.");
    const key = pair[0] + ":" + pair[1];
    found.set(key, (found.get(key) || 0) + 1);
  }
  return found;
}

export function compareBGPResults(leanBindings, gpuPairs) {
  if (!Array.isArray(leanBindings) || !Array.isArray(gpuPairs))
    throw new TypeError("Only actual complete CPU and GPU outputs may be compared.");
  const cpu = tally(leanBindings.map(r => [r.personId, r.colleagueId]));
  const gpu = tally(gpuPairs);
  const keys = [...new Set([...cpu.keys(), ...gpu.keys()])]
    .sort((a,b) => {
      const aa=a.split(":").map(Number), bb=b.split(":").map(Number);
      return aa[0]-bb[0] || aa[1]-bb[1];
    });
  const differences = keys.filter(k => (cpu.get(k)||0)!==(gpu.get(k)||0))
    .map(key => ({pair: key.split(":").map(Number),
      lean: cpu.get(key)||0, gpu: gpu.get(key)||0}));
  const equal = differences.length === 0 && leanBindings.length === gpuPairs.length;
  return {
    equal, cpuRows: leanBindings.length, gpuRows: gpuPairs.length,
    distinctCpuPairs: cpu.size, distinctGpuPairs: gpu.size, differingPairs: differences,
    summary: equal
      ? "Exact SPARQL bag equivalence: " + gpuPairs.length +
        " CPU and GPU bindings, including multiplicities. Output order is not compared."
      : "DIFFERENCE: Lean " + leanBindings.length + " rows, GPU " +
        gpuPairs.length + " rows; " + differences.length + " pair multiplicities disagree.",
  };
}

export function makeBgpTrace(cpu, gpu) {
  const cpuStages = [
    {title: "Parse lexical RDF", observed: Boolean(cpu),
      note: cpu ? cpu.input.tripleCount+" triples parsed by the full Lean SPARQL runtime." : "Awaiting Lean."},
    {title: "Pattern 1: knows", observed: Boolean(cpu),
      note: cpu ? cpu.scans.knows.count+" actual Lean bindings; first: "+
        JSON.stringify(cpu.scans.knows.preview.slice(0,3)) : "Awaiting Lean."},
    {title: "Pattern 2: worksOn Atlas", observed: Boolean(cpu),
      note: cpu ? cpu.scans.atlas.count+" actual Lean bindings; first: "+
        JSON.stringify(cpu.scans.atlas.preview.slice(0,3)) : "Awaiting Lean."},
    {title: "Join BGP + ORDER BY", observed: Boolean(cpu),
      note: cpu ? cpu.bgp.count+" complete Lean SPARQL result bindings. "+
        JSON.stringify(cpu.bindings.slice(0,5)) : "Awaiting Lean."},
  ];
  const result = gpu?.result ?? null;
  const compacted = gpu?.plan === "compacted";
  const readback = {title: "GPU readback vs Lean SPARQL",
    observed: Boolean(result && gpu?.comparison),
    note: gpu?.comparison?.summary ??
      (gpu?.error ? "GPU unavailable/refused: "+gpu.error :
        "No GPU query result has been read back.")};
  const counts = {title: "GPU join predicate and match counts",
    observed: Boolean(result),
    note: result ? "Read back "+result.counts.length+" actual GPU counts. First 24: "+
      JSON.stringify(result.counts.slice(0,24)) : "No GPU counts returned."};
  const offsets = {title: "GPU exclusive join-prefix scan",
    observed: Boolean(result),
    note: result ? "Read back "+result.offsets.length+" offsets, terminal total "+
      result.offsets.at(-1)+". First 24: "+JSON.stringify(result.offsets.slice(0,24))
      : "No GPU offsets returned."};
  const header = {title: "Encode and upload input triples", observed: Boolean(result),
    note: cpu ? cpu.input.integerGraph.length+" distinct u32 input triples from "+
      "the lexical RDF source. "+(result ? "WebGPU query returned." : "GPU has not executed yet.")
      : "Awaiting matching lexical RDF source."};
  const gpuStages = compacted ? [
    header,
    {title: "GPU pattern flags and projection scans", observed: Boolean(result),
      note: result ? "Actual GPU-compacted relation sizes: "+
        result.leftCount+" knows pairs, "+result.rightCount+" Atlas subjects. "+
        "Left starts: "+JSON.stringify(result.projectionOffsets.knows.slice(0,15))+
        "; right starts: "+JSON.stringify(result.projectionOffsets.atlas.slice(0,15))
        : "No GPU projection flags or offsets returned."},
    {title: "GPU stable scatter of selected triples", observed: Boolean(result),
      note: result ? "Actual GPU knows bindings, first 10: "+
        JSON.stringify(result.leftRows.slice(0,10))+
        "; Atlas subject IDs, first 10: "+JSON.stringify(result.rightRows.slice(0,10))
        : "No GPU pattern-projection buffers returned."},
    counts, offsets,
    {title: "GPU join emit: compacted rows", observed: Boolean(result),
      note: result ? result.solutionCount+" actual GPU BGP bindings from "+
        result.leftCount+"×"+result.rightCount+" candidate comparisons."
        : "No GPU BGP emission returned."},
    readback,
  ] : [
    header,counts,offsets,
    {title: "GPU fused join probe and emit", observed: Boolean(result),
      note: result ? result.solutionCount+" pairs emitted by GPU, "+
        "probing original source triples. The two patterns were fused." :
        "No GPU-emitted bindings returned."},
    readback,
  ];
  return {cpuStages,gpuStages};
}
