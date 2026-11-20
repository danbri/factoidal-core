import {mountExecutionStepper} from "./execution-stepper.mjs";
import {mountBgpStudio} from "./bgp-studio.mjs";

const $ = id => document.getElementById(id);
const executionStepper = mountExecutionStepper();
const source = $("source");
const program = $("program");
const example = $("example");
const cityLab = $("city-lab");
const cityChecks = [...cityLab.querySelectorAll("input[data-city-tile]")];
const run = $("run");
const live = $("live");
const inputStatus = $("input-status");
const cpuStatus = $("cpu-status");
const gpuStatus = $("gpu-status");
const cpuOutput = $("cpu-output");
const gpuOutput = $("gpu-output");
const comparison = $("comparison-status");
const runtimeData = $("runtime-data");
const initialPackInput = source.value;
const examples = {mixed: initialPackInput, empty: "[[], [], []]", none: "[]",
  city: "[[1, 3], [1, 2], [3]]"};
// These are literal input fixtures. Transformation and preparation happen in Lean.
const presets = {
  signal: {
    program: "map multiply 257\nmap add 31",
    source: "[\n  0, 4, 8, 12, 16, 20, 24, 28,\n  32, 36, 40, 44, 48, 52, 56, 60,\n  64, 68, 72, 76, 80, 84, 88, 92,\n  96, 100, 104, 108, 112, 116, 120, 124,\n  128, 132, 136, 140, 144, 148, 152, 156,\n  160, 164, 168, 172, 176, 180, 184, 188,\n  192, 196, 200, 204, 208, 212, 216, 220,\n  224, 228, 232, 236, 240, 244, 248, 252\n]",
  },
  wrap: {
    program: "map multiply 3\nmap add 1",
    source: "[0, 1, 2, 1431655765, 2147483647, 2147483648, 4294967294, 4294967295]",
  },
  duplicates: {
    program: "map multiply 7\nmap add 3",
    source: "[7, 7, 7, 0, 0, 4, 4, 7, 4294967295, 4294967295, 4, 0, 7, 4, 0, 7]",
  },
  empty: {program: "map multiply 3\nmap add 1", source: "[]"},
};
const inputs = {pack: initialPackInput, studio: presets.signal.source};
const duration = value => Number.isFinite(value) ? `${value.toFixed(2)} ms` : "not reported";
const encoder = new TextEncoder();
const maxWords = 1024;
const shareLimit = 16384;
let mode = "pack";
let generation = 0;
let editorLimit = 0;
let studioLimit = 0;
let programLimit = 0;
let cpuUnavailable = false;
const gpuStates = {pack: "checking", studio: "checking"};
const gpuMessages = {pack: null, studio: null};
let timer;
let lastStudioResult = null;
let pendingShare = null;
let requestedSharedMode = false;
let visualTarget = "cpu";
let lastCPUWords = null;
let lastGPUWords = null;
let signalRun = null;
let signalTimer;
let nextSignalPhase = 0;

function setPill(id, text, state) {
  const pill = $(id);
  const dot = document.createElement("i");
  dot.setAttribute("aria-hidden", "true");
  pill.replaceChildren(dot, document.createTextNode(text));
  pill.dataset.state = state;
}

function readyForMode() {
  return !cpuUnavailable && editorLimit > 0 && (mode === "pack" || studioLimit > 0);
}

function updateRunButton() {
  run.disabled = !readyForMode();
}

function markPreset(name) {
  for (const button of document.querySelectorAll("[data-preset]")) {
    button.setAttribute("aria-pressed", String(button.dataset.preset === name));
  }
}

function setEmptyView(message = "Actual output appears here.", detail = "Every cell represents one returned word.") {
  const text = document.createElement("p");
  text.append(message, document.createElement("br"));
  const note = document.createElement("span");
  note.textContent = detail;
  text.append(note);
  $("word-grid").replaceChildren(text);
  $("word-grid").removeAttribute("data-density");
  $("word-grid").setAttribute("aria-label", `${message} ${detail}`);
  $("visual-surface").dataset.state = "waiting";
}

function clearResult() {
  executionStepper.reset(mode, gpuStates[mode]);
  lastCPUWords = null;
  lastGPUWords = null;
  cpuOutput.textContent = "—";
  gpuOutput.textContent = "—";
  comparison.textContent = "";
  comparison.removeAttribute("data-match");
  cpuStatus.textContent = "Waiting for input.";
  if (gpuStates[mode] === "ready") gpuStatus.textContent = "Waiting for input.";
  $("word-count").textContent = "—";
  $("pass-count").textContent = "—";
  $("frame-status").textContent = "Waiting";
  lastStudioResult = null;
  $("copy-lean").disabled = true;
  $("download-lean").disabled = true;
  $("source-ir").textContent = mode === "studio" ? "Waiting for Lean to prepare the program…" : "Stable packing · Count → Scan → Scatter";
  $("optimized-ir").textContent = mode === "studio" ? "The source and fused tree will appear after checking." : "The packing program has a fixed three-stage GPU plan.";
  $("gpu-plan").textContent = "No prepared word-program plan for this input.";
  renderSelectedWordView();
}

function unavailable(message) {
  stopSignal("Playback stopped because the CPU runtime is unavailable.");
  editorLimit = 0;
  studioLimit = 0;
  cpuUnavailable = true;
  clearTimeout(timer);
  clearResult();
  updateRunButton();
  inputStatus.textContent = `CPU runtime unavailable. ${message}`;
  setPill("runtime-pill", "CPU unavailable", "unavailable");
  $("mode-studio").disabled = true;
  for (const button of document.querySelectorAll("[data-needs-studio]")) button.disabled = true;
  syncSignalControls();
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

function showCurrentGpuState() {
  const data = gpuMessages[mode];
  const state = gpuStates[mode];
  if (state === "ready") {
    setPill("adapter-pill", "WebGPU ready", "ready");
    gpuStatus.textContent = "Ready to compute with the Lean-exported shader program.";
  } else if (state === "checking") {
    setPill("adapter-pill", "Checking WebGPU", "checking");
    gpuStatus.textContent = "Initialising WebGPU and compiling the Lean-exported shaders…";
  } else {
    setPill("adapter-pill", "WebGPU unavailable", "unavailable");
    gpuStatus.textContent = data?.message || "The GPU program is unavailable.";
  }
  if (mode === "studio" && lastStudioResult && !lastStudioResult.gpuEligible) {
    gpuStatus.textContent = lastStudioResult.refusal || "This program is not in the supported GPU fragment.";
  }
  syncSignalControls();
}

function selectMode(next, {scheduleRun = true, preserveInput = false} = {}) {
  if (next !== "pack" && next !== "studio") return;
  cityLab.hidden = true;
  if (next !== mode) {
    stopSignal("Playback stopped when the experiment changed.");
    inputs[mode] = source.value;
    mode = next;
    if (!preserveInput) source.value = inputs[mode];
  }
  $("workspace").dataset.mode = mode;
  $("mode-pack").setAttribute("aria-pressed", String(mode === "pack"));
  $("mode-studio").setAttribute("aria-pressed", String(mode === "studio"));
  $("program-panel").hidden = mode !== "studio";
  $("pack-examples").hidden = mode !== "pack";
  $("input-heading").textContent = mode === "studio" ? "Input words" : "Input rows";
  $("input-help").textContent = mode === "studio"
    ? "A JSON array of up to 1,024 unsigned 32-bit decimal integers, from 0 to 4294967295. Lean validates the complete input."
    : "JSON rows of unsigned 32-bit decimal integers. Up to 128 rows and 1,024 words. Empty rows are skipped in the packed result; duplicates retain their positions.";
  showCurrentGpuState();
  updateRunButton();
  if (scheduleRun) schedule(0);
}

function schedule(delay = 150, manual = false, signalFrame = false) {
  if (!signalFrame) stopSignal("Playback stopped for a new request.");
  const id = ++generation;
  clearTimeout(timer);
  clearResult();
  if (!readyForMode()) {
    if (signalFrame) stopSignal("Playback stopped because the runtime is unavailable.");
    if (!cpuUnavailable) {
      inputStatus.textContent = editorLimit && mode === "studio"
        ? "This runtime supports packing. Word studio needs the extended runtime."
        : "Waiting for the CPU runtime. Your edits will run when it is ready.";
    }
    return id;
  }
  if (!manual && !live.checked) {
    inputStatus.textContent = "Edits are ready. Choose Run CPU + GPU, or press Command/Control + Enter.";
    return id;
  }
  inputStatus.textContent = "Checking input…";
  timer = setTimeout(() => {
    const limit = mode === "studio" ? studioLimit : editorLimit;
    if (source.value.length > limit) {
      inputStatus.textContent = `Input limit. Use at most ${limit} UTF-8 bytes.`;
      if (signalFrame) stopSignal("Playback stopped at the input limit.");
      return;
    }
    if (mode === "studio" && (program.value.length > programLimit || encoder.encode(program.value).byteLength > programLimit)) {
      inputStatus.textContent = `Program limit. Use at most ${programLimit} UTF-8 bytes.`;
      if (signalFrame) stopSignal("Playback stopped at the program limit.");
      return;
    }
    worker.postMessage(mode === "studio"
      ? {id, mode: "studio", program: program.value, source: source.value}
      : {id, source: source.value});
  }, delay);
  return id;
}

function edit() {
  cityLab.hidden = true;
  inputs[mode] = source.value;
  example.value = "custom";
  markPreset(null);
  schedule();
}

function setProvenance(label, value) {
  let term = Array.from(runtimeData.querySelectorAll("dt")).find(node => node.textContent === label);
  if (!term) {
    term = document.createElement("dt");
    term.textContent = label;
    runtimeData.append(term, document.createElement("dd"));
  }
  term.nextElementSibling.replaceChildren(value instanceof Node ? value : document.createTextNode(String(value)));
}

function showProvenance({sourceCommit, bytes, fetchMs, initMs}) {
  const sourceLink = document.createElement("a");
  sourceLink.href = `https://github.com/danbri/factoidal-core/commit/${sourceCommit}`;
  sourceLink.textContent = sourceCommit.slice(0, 12);
  for (const [label, value] of [
    ["Source commit", sourceLink], ["Wasm size", `${bytes.toLocaleString()} bytes`],
    ["Asset load", duration(fetchMs)], ["Wasm and Lean initialisation", duration(initMs)],
  ]) setProvenance(label, value);
  runtimeData.hidden = false;
}

function validateWords(words) {
  if (!Array.isArray(words) || words.length > maxWords ||
      words.some(word => !Number.isInteger(word) || word < 0 || word > 0xFFFFFFFF)) {
    throw new Error("The runtime returned an invalid word array.");
  }
  return words;
}

function unpackWords(packed) {
  if (!(packed instanceof Uint8Array) || packed.byteLength % 4 !== 0 || packed.byteLength > maxWords * 4) {
    throw new Error("The output has an invalid word length.");
  }
  const view = new DataView(packed.buffer, packed.byteOffset, packed.byteLength);
  return Array.from({length: packed.byteLength / 4}, (_, index) => view.getUint32(index * 4, true));
}

function showWords(output, words) {
  output.textContent = `[${words.join(", ")}]`;
  return words.length;
}

function showWordView(words) {
  const grid = $("word-grid");
  $("word-count").textContent = words.length.toLocaleString();
  if (!words.length) {
    setEmptyView("An empty result.", "Zero returned words. This is a successful computation.");
    $("visual-surface").dataset.state = "empty";
    return;
  }
  const columns = Math.min(32, Math.max(4, Math.ceil(Math.sqrt(words.length))));
  grid.style.setProperty("--columns", columns);
  grid.dataset.density = words.length > 256 ? "high" : "normal";
  const cells = document.createDocumentFragment();
  words.forEach((word, index) => {
    const cell = document.createElement("span");
    cell.className = "word-cell";
    // A colour mapping of a returned value, solely for its presentation.
    cell.style.setProperty("--word-hue", 70 + word % 150);
    cell.style.setProperty("--word-light", `${53 + word % 27}%`);
    cell.textContent = word.toString(16).slice(-2).padStart(2, "0");
    cell.title = `Index ${index}: ${word} (0x${word.toString(16).padStart(8, "0")})`;
    cell.setAttribute("aria-hidden", "true");
    cells.append(cell);
  });
  grid.replaceChildren(cells);
  grid.setAttribute("aria-label", `${words.length} ${visualTarget.toUpperCase()} output words, shown as coloured cells. The complete numeric result follows in the ${visualTarget.toUpperCase()} output.`);
  $("visual-surface").dataset.state = "filled";
}

function renderSelectedWordView() {
  const words = visualTarget === "gpu" ? lastGPUWords : lastCPUWords;
  $("view-cpu").setAttribute("aria-pressed", String(visualTarget === "cpu"));
  $("view-gpu").setAttribute("aria-pressed", String(visualTarget === "gpu"));
  $("visual-surface").dataset.target = visualTarget;
  $("visual-source").textContent = visualTarget === "gpu" ? "Actual GPU readback" : "Actual CPU output";
  $("visual-caption").textContent = visualTarget === "gpu"
    ? "This view uses actual GPU readback. Colour is a display mapping of the returned words. Full numeric results are below."
    : "This view uses the CPU result. Colour is a display mapping of the returned words. Full numeric results are below.";
  if (words !== null) {
    showWordView(words);
  } else {
    $("word-count").textContent = "—";
    if (visualTarget === "gpu" && mode === "studio" && lastStudioResult && !lastStudioResult.gpuEligible) {
      setEmptyView("No GPU result for this program.", lastStudioResult.refusal || "The GPU selector declined this source.");
    } else if (visualTarget === "gpu" && !["checking", "ready"].includes(gpuStates[mode])) {
      setEmptyView("GPU readback is unavailable.", "The CPU result remains available in its own view.");
    } else {
      setEmptyView(visualTarget === "gpu" ? "Waiting for actual GPU readback." : "Waiting for actual CPU output.", "Every cell will represent one returned word.");
    }
  }
}

function chooseVisualTarget(target) {
  if (target !== "cpu" && target !== "gpu") return;
  visualTarget = target;
  renderSelectedWordView();
}

function signalAvailable() {
  return !cpuUnavailable && studioLimit > 0 && gpuStates.studio === "ready";
}

function syncSignalControls() {
  $("signal-play").disabled = !signalAvailable() || signalRun !== null;
  $("signal-step").disabled = !signalAvailable() || signalRun !== null;
  $("signal-stop").disabled = signalRun === null;
}

function stopSignal(message, {cancelPending = false} = {}) {
  clearTimeout(signalTimer);
  signalTimer = undefined;
  if (!signalRun) return;
  const stopped = signalRun;
  signalRun = null;
  if (cancelPending) clearTimeout(timer);
  $("signal-phase").textContent = `Stopped · ${stopped.completed} / ${stopped.limit} frames`;
  $("signal-status").textContent = message || "Playback stopped.";
  syncSignalControls();
}

function submitSignalFrame() {
  const active = signalRun;
  if (!active || active.awaiting) return;
  if (!signalAvailable() || mode !== "studio") {
    stopSignal("Playback stopped because the word GPU is unavailable.");
    return;
  }
  // This changes requested input parameters only. Lean computes every output.
  program.value = `map multiply 257\nmap add ${active.phase}`;
  active.awaiting = true;
  active.id = schedule(0, true, true);
  $("signal-phase").textContent = `${active.completed} / ${active.limit} matched · phase ${active.phase}`;
  $("signal-phase").dataset.phase = String(active.phase);
}

function startSignal(kind) {
  if (!signalAvailable()) return;
  stopSignal("Playback restarted.", {cancelPending: true});
  clearTimeout(timer);
  inputs.studio = presets.signal.source;
  selectMode("studio", {scheduleRun: false});
  source.value = presets.signal.source;
  inputs.studio = source.value;
  markPreset("signal");
  chooseVisualTarget("gpu");
  signalRun = {kind, limit: kind === "play" ? 32 : 1, completed: 0,
    phase: kind === "play" ? 0 : nextSignalPhase, awaiting: false, id: 0};
  $("signal-phase").dataset.completed = "0";
  $("signal-status").textContent = kind === "play"
    ? "Playing up to 32 frames. Each next phase waits for a matching GPU readback."
    : "Requesting one frame and comparing the actual GPU result.";
  syncSignalControls();
  submitSignalFrame();
}

function acknowledgeSignalFrame(data) {
  const active = signalRun;
  if (!active || !active.awaiting) return;
  if (active.id !== generation || mode !== "studio") {
    stopSignal("Playback stopped when the current request changed.");
    return;
  }
  if (data.id !== active.id) return;
  if (data.matches !== true) {
    stopSignal("Playback stopped because the CPU and GPU results did not match.");
    return;
  }
  active.awaiting = false;
  active.completed += 1;
  nextSignalPhase = (active.phase + 8) % 256;
  $("signal-phase").dataset.completed = String(active.completed);
  $("signal-phase").textContent = `${active.completed} / ${active.limit} matched · phase ${active.phase}`;
  if (active.completed === active.limit) {
    signalRun = null;
    $("signal-status").textContent = active.kind === "play"
      ? "All 32 frames completed with matching GPU readbacks."
      : "One frame completed with a matching GPU readback.";
    syncSignalControls();
    return;
  }
  active.phase = nextSignalPhase;
  signalTimer = setTimeout(() => {
    signalTimer = undefined;
    if (signalRun !== active) return;
    if (active.id !== generation) {
      stopSignal("Playback stopped when the current request changed.");
      return;
    }
    submitSignalFrame();
  }, 80);
}

function showResult({packed, prepareMs, cpuMs}) {
  const words = unpackWords(packed);
  const count = showWords(cpuOutput, words);
  lastCPUWords = words;
  executionStepper.cpuPack(words);
  renderSelectedWordView();
  cpuStatus.textContent = `${count} ${count === 1 ? "word" : "words"} · ${duration(cpuMs)} CPU call`;
  inputStatus.textContent = `Input prepared in ${duration(prepareMs)}. One untimed warm-up precedes each measured CPU/GPU sample.`;
  $("pass-count").textContent = "3";
  $("frame-status").textContent = "Payload check";
  if (gpuStates[mode] === "ready") gpuStatus.textContent = "Computing and reading back…";
}

function showStudioResult({result, cpuMs}) {
  if (result?.schemaVersion !== 1) throw new Error("The studio response version is unsupported.");
  const words = validateWords(result.output);
  validateWords(result.input);
  if (typeof result.sourceIR !== "string" || typeof result.optimizedIR !== "string" || typeof result.leanSource !== "string") {
    throw new Error("The studio response has no typed program description.");
  }
  const count = showWords(cpuOutput, words);
  lastCPUWords = words;
  cpuStatus.textContent = `${count} ${count === 1 ? "word" : "words"} · ${duration(cpuMs)} Lean parse + CPU evaluation`;
  $("source-ir").textContent = result.sourceIR;
  $("optimized-ir").textContent = result.optimizedIR;
  $("gpu-plan").textContent = result.executionPlan === null
    ? (result.refusal || "The GPU selector declined this program.")
    : JSON.stringify(result.executionPlan, null, 2);
  lastStudioResult = result;
  executionStepper.cpuStudio(result);
  renderSelectedWordView();
  $("copy-lean").disabled = false;
  $("download-lean").disabled = false;
  if (result.gpuEligible) {
    $("pass-count").textContent = String(result.executionPlan?.passes?.length ?? "—");
    $("frame-status").textContent = "Awaiting readback";
    inputStatus.textContent = "Lean prepared the typed program and CPU result. The source and fused trees are shown below.";
    if (gpuStates[mode] === "ready") gpuStatus.textContent = "Computing the Lean-selected plan and reading back…";
  } else {
    stopSignal("Playback stopped because the GPU selector declined the program.");
    $("pass-count").textContent = "CPU only";
    $("frame-status").textContent = "Not submitted";
    inputStatus.textContent = "Lean evaluated this program on the CPU. The GPU selector declined it.";
    gpuStatus.textContent = result.refusal || "This program is not in the supported GPU fragment.";
    comparison.textContent = "CPU result available. No GPU result was produced for this program.";
  }
}

function showGpuResult(data) {
  const words = unpackWords(data.packed);
  const count = showWords(gpuOutput, words);
  lastGPUWords = words;
  executionStepper.gpu(words, data);
  renderSelectedWordView();
  const timing = `${count} ${count === 1 ? "word" : "words"} · ${duration(data.endToEndMs)} GPU end to end.`;
  gpuStatus.textContent = timing + (mode === "pack"
    ? ` Upload/encode/submit ${duration(data.encodeSubmitMs)}; queue and terminal ${duration(data.queueAndTerminalMs)}; payload readback ${duration(data.payloadReadbackMs)}.`
    : ` ${data.passCount ?? "Selected"} passes. Final payload and buffer-frame checks are reported below.`);
  const payloadMatches = data.matches === true;
  const fullFrameMatches = mode !== "studio" || (data.fullMatches === true && data.canariesMatch === true);
  const completeMatch = payloadMatches && fullFrameMatches;
  comparison.textContent = completeMatch
    ? (mode === "studio" ? "Exact CPU/GPU payload and complete GPU buffer-frame match." : "Exact CPU/GPU byte match.")
    : payloadMatches && !fullFrameMatches
      ? "CPU/GPU payloads match, but the full GPU buffer frame (header or tail) does not. See the stepper."
      : "CPU/GPU mismatch. The two actual results are shown above.";
  comparison.dataset.match = String(completeMatch);
  if (mode === "studio") {
    $("frame-status").textContent = data.fullMatches === true && data.canariesMatch === true
      ? "Header + tail match"
      : data.fullMatches === false || data.canariesMatch === false ? "Frame mismatch" : "Not reported";
  } else {
    $("frame-status").textContent = data.matches ? "Payload matched" : "Payload mismatch";
  }
}

function showGpuProvenance(data) {
  const labels = data.sourceNames || ["Count", "Scan", "Scatter", "Add", "Multiply"];
  const prefix = data.mode === "studio" ? "Word " : "";
  for (const [label, value] of [
    [prefix + "GPU adapter", data.adapter],
    [prefix + "Fallback adapter", data.isFallbackAdapter === null ? "Not reported" : String(data.isFallbackAdapter)],
    [prefix + "GPU initialisation", duration(data.initMs)],
    [prefix + "Device timestamps", data.deviceTimestamps],
    ...(data.sourceHashes || []).map((hash, index) => [`${labels[index] || `Shader ${index}`} source SHA-256`, hash]),
  ]) setProvenance(label, value);
}

function applyPreset(name) {
  if (name === "pack" || name === "city") {
    const fixture = name === "city" ? examples.city : examples.mixed;
    inputs.pack = fixture;
    selectMode("pack", {scheduleRun: false});
    source.value = fixture;
    example.value = name === "city" ? "custom" : "mixed";
    if (name === "city") {
      const initial = [[1, 3], [1, 2], [3]];
      for (const item of cityChecks) {
        item.checked = initial[Number(item.dataset.cityTile)].includes(Number(item.value));
      }
      cityLab.hidden = false;
    }
  } else {
    const preset = presets[name];
    if (!preset || !studioLimit) return;
    inputs.studio = preset.source;
    selectMode("studio", {scheduleRun: false});
    source.value = preset.source;
    program.value = preset.program;
  }
  inputs[mode] = source.value;
  markPreset(name);
  schedule(0, true);
}

async function copyText(text, success, fallback = false) {
  try {
    if (!navigator.clipboard?.writeText) throw new Error("Clipboard access is unavailable.");
    await navigator.clipboard.writeText(text);
    $("action-status").textContent = success;
    $("share-fallback").hidden = true;
  } catch {
    if (fallback) {
      $("share-link").value = text;
      $("share-fallback").hidden = false;
      $("share-link").focus();
      $("share-link").select();
      $("action-status").textContent = "Select and copy the experiment link below.";
    } else {
      $("action-status").textContent = "Clipboard access is unavailable. Use Download .lean instead.";
    }
  }
}

function shareExperiment() {
  // Bound the editor strings before JSON and UTF-8 copies, including unrun input.
  if (program.value.length + source.value.length > shareLimit) {
    $("action-status").textContent = "The experiment exceeds the 16 KiB share-link limit. Shorten the input or download the checked Lean source.";
    return;
  }
  const state = JSON.stringify({version: 1, mode, program: program.value, source: source.value});
  const bytes = encoder.encode(state);
  if (bytes.byteLength > shareLimit) {
    $("action-status").textContent = "The experiment exceeds the 16 KiB share-link limit. Shorten the input or download the checked Lean source.";
    return;
  }
  const url = new URL(location.href);
  url.hash = "pv=" + btoa(String.fromCharCode(...bytes));
  copyText(url.href, "Experiment link copied. It includes the editable program and input.", true);
}

function readSharedExperiment() {
  if (!location.hash.startsWith("#pv=")) return false;
  try {
    const encoded = location.hash.slice(4);
    if (encoded.length > Math.ceil(shareLimit / 3) * 4) throw new Error("The shared experiment is too large.");
    const bytes = Uint8Array.from(atob(encoded), c => c.charCodeAt(0));
    if (bytes.byteLength > shareLimit) throw new Error("The shared experiment is too large.");
    const shared = JSON.parse(new TextDecoder("utf-8", {fatal: true}).decode(bytes));
    if (shared.version !== 1 || !["pack", "studio"].includes(shared.mode) ||
        typeof shared.program !== "string" || typeof shared.source !== "string") {
      throw new Error("The shared experiment format is unsupported.");
    }
    pendingShare = shared;
    requestedSharedMode = true;
    selectMode(shared.mode, {scheduleRun: false});
    source.value = shared.source;
    program.value = shared.program;
    inputs[mode] = shared.source;
    example.value = "custom";
    markPreset(null);
    $("action-status").textContent = "Shared experiment loaded. Lean will check its program and input before execution.";
    return true;
  } catch (error) {
    $("action-status").textContent = `Could not open this experiment link. ${error.message}`;
    return false;
  }
}

readSharedExperiment();
const worker = createWorker();

window.addEventListener("hashchange", () => {
  if (readSharedExperiment()) {
    stopSignal("Playback stopped when a shared experiment opened.");
    schedule(0, true);
  }
});

if (worker) {
  worker.addEventListener("message", ({data}) => {
    try {
      switch (data.type) {
        case "gpu":
          gpuStates[data.mode || "pack"] = data.state;
          gpuMessages[data.mode || "pack"] = data;
          if (data.mode === "studio" && data.state !== "ready") {
            stopSignal("Playback stopped because the word GPU is unavailable.");
          }
          syncSignalControls();
          if (data.state === "ready") {
            showGpuProvenance(data);
          }
          // A late device event for another mode cannot erase the current result.
          if ((data.mode || "pack") !== mode) break;
          executionStepper.gpuState(data.state);
          showCurrentGpuState();
          if (data.state !== "ready" && data.state !== "checking") {
            lastGPUWords = null;
            executionStepper.invalidateGpu();
            gpuOutput.textContent = "—";
            comparison.textContent = "";
            comparison.removeAttribute("data-match");
            if (mode === "studio") $("frame-status").textContent = "Not submitted";
            renderSelectedWordView();
          }
          break;
        case "gpu-result":
          if (data.id === generation && (data.mode || "pack") === mode) {
            showGpuResult(data);
            if (mode === "studio") acknowledgeSignalFrame(data);
          }
          break;
        case "ready":
          editorLimit = data.editorLimit;
          studioLimit = data.studioLimit || 0;
          programLimit = data.programLimit || 512;
          updateRunButton();
          syncSignalControls();
          $("mode-studio").disabled = !studioLimit;
          for (const button of document.querySelectorAll("[data-needs-studio]")) button.disabled = !studioLimit;
          $("studio-capability").textContent = studioLimit
            ? "Word studio is ready. Try an example, or write your own pipeline."
            : "This published runtime supports stable packing. Word studio requires the extended runtime.";
          setPill("runtime-pill", studioLimit ? "Typed runtime ready" : "Packing runtime ready", "ready");
          showProvenance(data.provenance);
          if (requestedSharedMode && pendingShare?.mode === "studio" && mode === "studio" && !studioLimit) {
            inputStatus.textContent = "This shared word program needs the extended runtime. Stable packing remains available.";
          } else schedule(0, true);
          break;
        case "unavailable":
          unavailable(data.message);
          break;
        case "result":
          if (data.id === generation && mode === "pack") showResult(data);
          break;
        case "studio-result":
          if (data.id === generation && mode === "studio") showStudioResult(data);
          break;
        case "failure":
          if (data.id !== generation) break;
          stopSignal("Playback stopped because the current request failed.");
          if (data.kind === "invalid" || data.kind === "limit") {
            inputStatus.textContent = `${data.kind === "limit" ? "Input limit" : "Invalid input"}. ${data.message}`;
            setEmptyView("The input was not accepted.", "Edit the program or input, then run again.");
          } else unavailable(data.message);
          break;
      }
    } catch (error) {
      unavailable(error.message || "The runtime response could not be displayed.");
    }
  });
  worker.addEventListener("error", error => {
    unavailable(error.message || "The worker stopped.");
    gpuStatus.textContent = "WebGPU status unavailable because the worker stopped.";
    setPill("adapter-pill", "WebGPU unavailable", "unavailable");
  });
  cityLab.addEventListener("change", event => {
    if (!event.target.matches("input[data-city-tile]")) return;
    const rows = [0, 1, 2].map(tile => cityChecks
      .filter(item => Number(item.dataset.cityTile) === tile && item.checked)
      .map(item => Number(item.value)));
    source.value = JSON.stringify(rows);
    inputs.pack = source.value;
    example.value = "custom";
    markPreset("city");
    schedule(0, true);
  });
  source.addEventListener("input", edit);
  source.addEventListener("change", () => { cityLab.hidden = true; inputs[mode] = source.value; example.value = "custom"; markPreset(null); schedule(0); });
  program.addEventListener("input", edit);
  program.addEventListener("change", () => { markPreset(null); schedule(0); });
  run.addEventListener("click", () => { example.value = "custom"; schedule(0, true); });
  live.addEventListener("change", () => {
    if (live.checked) schedule(0, true);
    else {
      stopSignal("Playback stopped when live updates were paused.", {cancelPending: true});
      clearTimeout(timer);
      inputStatus.textContent = "Live updates paused. Choose Run CPU + GPU to execute your edits.";
    }
  });
  example.addEventListener("change", () => {
    if (!(example.value in examples)) return;
    source.value = examples[example.value];
    inputs.pack = source.value;
    markPreset(example.value === "mixed" ? "pack" : null);
    schedule(0, true);
  });
  $("mode-pack").addEventListener("click", () => { markPreset(null); selectMode("pack"); });
  $("mode-studio").addEventListener("click", () => { markPreset(null); selectMode("studio"); });
  for (const button of document.querySelectorAll("[data-preset]")) {
    button.addEventListener("click", () => applyPreset(button.dataset.preset));
  }
  document.addEventListener("keydown", event => {
    if (event.key === "Enter" && (event.metaKey || event.ctrlKey)) {
      event.preventDefault();
      if (!run.disabled) { example.value = "custom"; schedule(0, true); }
    }
  });
}

$("view-cpu").addEventListener("click", () => chooseVisualTarget("cpu"));
$("view-gpu").addEventListener("click", () => chooseVisualTarget("gpu"));
$("signal-play").addEventListener("click", () => startSignal("play"));
$("signal-step").addEventListener("click", () => startSignal("step"));
$("signal-stop").addEventListener("click", () => {
  stopSignal("Playback stopped. A submitted frame can finish.", {cancelPending: true});
  inputStatus.textContent = "Playback stopped. Choose Run CPU + GPU to execute the current input.";
  if (cpuOutput.textContent === "—") cpuStatus.textContent = "Playback stopped.";
  if (gpuOutput.textContent === "—") gpuStatus.textContent = "Playback stopped.";
});

$("copy-lean").addEventListener("click", () => {
  if (lastStudioResult) copyText(lastStudioResult.leanSource, "Lean source copied from the runtime response.");
});
$("download-lean").addEventListener("click", () => {
  if (!lastStudioResult) return;
  const url = URL.createObjectURL(new Blob([lastStudioResult.leanSource], {type: "text/plain;charset=utf-8"}));
  const link = document.createElement("a");
  link.href = url;
  link.download = "ParalliverseExperiment.lean";
  document.body.append(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
  $("action-status").textContent = "Downloaded the Lean source returned by this runtime.";
});
$("share").addEventListener("click", shareExperiment);


// The BGP runs in two independent backends. The full Lean SPARQL runtime
// is the lexical oracle; WebGPU performs integer triple filtering and joins.
mountBgpStudio();
