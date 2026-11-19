const source = document.querySelector("#source");
const example = document.querySelector("#example");
const run = document.querySelector("#run");
const inputStatus = document.querySelector("#input-status");
const cpuStatus = document.querySelector("#cpu-status");
const gpuStatus = document.querySelector("#gpu-status");
const cpuOutput = document.querySelector("#cpu-output");
const gpuOutput = document.querySelector("#gpu-output");
const comparison = document.querySelector("#comparison-status");
const runtimeData = document.querySelector("#runtime-data");

const examples = {mixed: source.value, empty: "[[], [], []]", none: "[]"};
const duration = value => `${value.toFixed(2)} ms`;
let generation = 0;
let editorLimit = 0;
let cpuUnavailable = false;
let gpuState = "checking";
let timer;

function clearResult() {
  cpuOutput.textContent = "—";
  gpuOutput.textContent = "—";
  comparison.textContent = "";
  comparison.removeAttribute("data-match");
  cpuStatus.textContent = "Waiting for input.";
  if (gpuState === "ready") gpuStatus.textContent = "Waiting for input.";
}

function createWorker() {
  try {
    return new Worker(new URL("./worker.mjs", import.meta.url), {type: "module"});
  } catch (error) {
    unavailable(error.message);
    gpuStatus.textContent = "WebGPU status unavailable because the worker could not start.";
    return null;
  }
}

function unavailable(message) {
  editorLimit = 0;
  cpuUnavailable = true;
  run.disabled = true;
  clearTimeout(timer);
  clearResult();
  inputStatus.textContent = `CPU runtime unavailable. ${message}`;
}

const worker = createWorker();

function schedule(delay = 150) {
  const id = ++generation;
  clearTimeout(timer);
  if (!editorLimit) {
    if (!cpuUnavailable) inputStatus.textContent = "Waiting for the CPU runtime. Your edited rows will run when it is ready.";
    return;
  }
  clearResult();
  inputStatus.textContent = "Checking input…";
  timer = setTimeout(() => {
    if (source.value.length > editorLimit) {
      inputStatus.textContent = `Input limit. Use at most ${editorLimit} UTF-8 bytes.`;
      return;
    }
    worker.postMessage({id, source: source.value});
  }, delay);
}

function showProvenance({sourceCommit, bytes, fetchMs, initMs}) {
  const sourceLink = document.createElement("a");
  sourceLink.href = `https://github.com/danbri/factoidal-core/commit/${sourceCommit}`;
  sourceLink.textContent = sourceCommit.slice(0, 12);
  const entries = [
    ["Source commit", sourceLink],
    ["Wasm size", `${bytes.toLocaleString()} bytes`],
    ["Asset load", duration(fetchMs)],
    ["Wasm and Lean initialisation", duration(initMs)],
  ];
  for (const [label, value] of entries) {
    const term = document.createElement("dt");
    const definition = document.createElement("dd");
    term.textContent = label;
    definition.append(value);
    runtimeData.append(term, definition);
  }
  runtimeData.hidden = false;
}

function showWords(output, packed) {
  if (packed.byteLength % 4 !== 0) throw new Error("The packed output has an invalid word length.");
  const result = new DataView(packed.buffer, packed.byteOffset, packed.byteLength);
  const count = packed.byteLength / 4;
  const words = Array.from({length: count}, (_, index) => result.getUint32(index * 4, true));
  output.textContent = `[${words.join(", ")}]`;
  return count;
}

function showResult({packed, prepareMs, cpuMs}) {
  const count = showWords(cpuOutput, packed);
  cpuStatus.textContent = `${count} ${count === 1 ? "word" : "words"} · ${duration(cpuMs)} CPU call`;
  inputStatus.textContent = `Input prepared in ${duration(prepareMs)}. One untimed warm-up precedes each measured CPU/GPU sample.`;
  if (gpuState === "ready") gpuStatus.textContent = "Computing and reading back…";
}

function showGpuResult({packed, matches, endToEndMs, encodeSubmitMs, queueAndTerminalMs, payloadReadbackMs}) {
  const count = showWords(gpuOutput, packed);
  gpuStatus.textContent = `${count} ${count === 1 ? "word" : "words"} · ${duration(endToEndMs)} GPU end to end. ` +
    `Upload/encode/submit ${duration(encodeSubmitMs)}; queue and terminal ${duration(queueAndTerminalMs)}; payload readback ${duration(payloadReadbackMs)}.`;
  comparison.textContent = matches ? "Exact CPU/GPU byte match." : "CPU/GPU mismatch. The two actual results are shown above.";
  comparison.dataset.match = String(matches);
}

function showGpuProvenance(data) {
  const entries = [
    ["GPU adapter", data.adapter],
    ["Fallback adapter", data.isFallbackAdapter === null ? "Not reported" : String(data.isFallbackAdapter)],
    ["GPU initialisation", duration(data.initMs)],
    ["Device timestamps", data.deviceTimestamps],
    ...data.sourceHashes.map((hash, index) => [["Count", "Scan", "Scatter"][index] + " source SHA-256", hash]),
  ];
  for (const [label, value] of entries) {
    const term = document.createElement("dt");
    const definition = document.createElement("dd");
    term.textContent = label;
    definition.textContent = value;
    runtimeData.append(term, definition);
  }
}

if (worker) {
  worker.addEventListener("message", ({data}) => {
    switch (data.type) {
      case "gpu":
        gpuState = data.state;
        if (data.state === "ready") {
          showGpuProvenance(data);
          gpuStatus.textContent = "Ready to compute with the Lean-exported shader program.";
        } else if (data.state === "checking") {
          gpuStatus.textContent = "Initialising WebGPU and compiling the Lean-exported shaders…";
        } else {
          gpuOutput.textContent = "—";
          comparison.textContent = "";
          comparison.removeAttribute("data-match");
          gpuStatus.textContent = data.message || "The GPU program is unavailable.";
        }
        break;
      case "gpu-result":
        if (data.id === generation) showGpuResult(data);
        break;
      case "ready":
        editorLimit = data.editorLimit;
        run.disabled = false;
        showProvenance(data.provenance);
        schedule(0);
        break;
      case "unavailable":
        unavailable(data.message);
        break;
      case "result":
        if (data.id === generation) showResult(data);
        break;
      case "failure":
        if (data.id !== generation) break;
        if (data.kind === "invalid" || data.kind === "limit") {
          inputStatus.textContent = `${data.kind === "limit" ? "Input limit" : "Invalid input"}. ${data.message}`;
        } else {
          unavailable(data.message);
        }
        break;
    }
  });
  worker.addEventListener("error", error => {
    unavailable(error.message || "The worker stopped.");
    if (gpuStatus.textContent.startsWith("Checking")) gpuStatus.textContent = "WebGPU status unavailable.";
  });
  source.addEventListener("input", () => {
    example.value = "custom";
    schedule();
  });
  source.addEventListener("change", () => {
    example.value = "custom";
    schedule(0);
  });
  run.addEventListener("click", () => {
    example.value = "custom";
    schedule(0);
  });
  example.addEventListener("change", () => {
    source.value = examples[example.value];
    schedule(0);
  });
}
