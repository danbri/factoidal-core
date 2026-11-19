const source = document.querySelector("#source");
const example = document.querySelector("#example");
const inputStatus = document.querySelector("#input-status");
const cpuStatus = document.querySelector("#cpu-status");
const gpuStatus = document.querySelector("#gpu-status");
const cpuOutput = document.querySelector("#cpu-output");
const runtimeData = document.querySelector("#runtime-data");

const examples = {mixed: source.value, empty: "[[], [], []]", none: "[]"};
const duration = value => `${value.toFixed(2)} ms`;
let generation = 0;
let editorLimit = 0;
let timer;

function clearResult() {
  cpuOutput.textContent = "—";
  cpuStatus.textContent = "Waiting for input.";
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
  clearTimeout(timer);
  clearResult();
  inputStatus.textContent = `CPU runtime unavailable. ${message}`;
}

const worker = createWorker();

function schedule(delay = 150) {
  const id = ++generation;
  clearTimeout(timer);
  if (!editorLimit) return;
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

function showResult({packed, prepareMs, cpuMs}) {
  if (packed.byteLength % 4 !== 0) {
    unavailable("The packed output has an invalid word length.");
    return;
  }
  const result = new DataView(packed.buffer, packed.byteOffset, packed.byteLength);
  const count = packed.byteLength / 4;
  const words = Array.from({length: count}, (_, index) => result.getUint32(index * 4, true));
  cpuOutput.textContent = `[${words.join(", ")}]`;
  cpuStatus.textContent = `${count} ${count === 1 ? "word" : "words"} · ${duration(cpuMs)} CPU call`;
  inputStatus.textContent = `Input prepared in ${duration(prepareMs)}.`;
}

if (worker) {
  worker.addEventListener("message", ({data}) => {
    switch (data.type) {
      case "gpu":
        gpuStatus.textContent = data.state === "api-unavailable"
          ? "WebGPU is unavailable in this browser."
          : "The Lean-generated GPU program is unavailable in this build.";
        break;
      case "ready":
        editorLimit = data.editorLimit;
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
  example.addEventListener("change", () => {
    source.value = examples[example.value];
    schedule(0);
  });
}
