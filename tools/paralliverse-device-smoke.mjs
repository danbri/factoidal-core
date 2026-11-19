import { connectGpu } from "../docs/web/hub/paralliverse/gpu.mjs";

const [fixturePath, sourceCommit] = Deno.args;
if (!fixturePath || !/^[0-9a-f]{40}$/.test(sourceCommit ?? "")) {
  throw new Error("Usage: paralliverse-device-smoke.mjs FIXTURES.jsonl SOURCE_COMMIT");
}

async function sha256(bytes) {
  const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return Array.from(digest, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function assertMatches(name, actual, expected) {
  if (actual.byteLength !== expected.byteLength) {
    throw new Error(`${name}: read ${actual.byteLength} bytes, expected ${expected.byteLength}`);
  }
  for (let index = 0; index < expected.byteLength; index++) {
    if (actual[index] !== expected[index]) {
      throw new Error(`${name}: byte ${index} was ${actual[index]}, expected ${expected[index]}`);
    }
  }
}

const evidence = {
  format: "paralliverse-device-smoke-v1",
  status: "fail",
  sourceCommit,
  denoVersion: Deno.version.deno,
  reference: "Native Lean PackWire and StaticPack.packSpec",
  cases: [],
};

try {
  const jsonl = await Deno.readTextFile(fixturePath);
  const [header, ...fixtures] = jsonl.trim().split("\n").map((line) => JSON.parse(line));
  if (header.kind !== "shaders" || !Array.isArray(header.sources) || header.sources.length !== 3 ||
      fixtures.length === 0 || fixtures.length !== header.caseCount) {
    throw new Error("The native Lean fixture file is incomplete.");
  }

  const encoder = new TextEncoder();
  evidence.shaders = await Promise.all(["count", "scan", "scatter"].map(async (stage, index) => ({
    stage,
    sha256: await sha256(encoder.encode(header.sources[index])),
  })));

  const runner = await connectGpu(header.sources);
  try {
    evidence.adapter = runner.adapter;
    evidence.isFallbackAdapter = runner.isFallbackAdapter;
    evidence.initMs = runner.initMs;
    evidence.timingSource = runner.deviceTimestamps;
    for (const fixture of fixtures) {
      if (fixture.kind !== "fixture") throw new Error("Expected a native Lean fixture record.");
      const packet = Uint8Array.from(fixture.packet);
      const expected = Uint8Array.from(fixture.expected);
      const { packed, ...timings } = await runner.run(packet);
      assertMatches(fixture.case, packed, expected);
      evidence.cases.push({
        case: fixture.case,
        rows: fixture.rows,
        packetBytes: packet.byteLength,
        matchedBytes: packed.byteLength,
        outputSha256: await sha256(packed),
        ...timings,
      });
    }
  } finally {
    runner.close();
  }
  evidence.status = "pass";
} catch (error) {
  evidence.error = error instanceof Error ? error.message : String(error);
  console.error(error);
  Deno.exitCode = 1;
}

console.log(JSON.stringify(evidence, null, 2));
