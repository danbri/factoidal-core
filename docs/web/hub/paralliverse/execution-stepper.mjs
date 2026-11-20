// Recorded-execution navigator: it never invents intermediate CPU/GPU buffers.
// CPU outputs come from compiled Lean Wasm; GPU outputs come from real readback.
// Step navigation is a REPLAY of the returned execution and Lean plan, not a
// pause or single-step interface to an active GPU dispatch.
export function buildExecutionTrace({mode = "pack", cpuWords = null, studio = null,
  gpuWords = null, gpuMeta = null, gpuState = "checking"}) {
  const cpu = Array.isArray(cpuWords) ? cpuWords : null;
  const gpu = Array.isArray(gpuWords) ? gpuWords : null;
  const cpuPresent = cpu !== null;
  const gpuPresent = gpu !== null;
  const stage = (title, detail, status, source) => ({title, detail, status, source});
  const cpuSteps = [], gpuSteps = [];
  if (mode === "studio") {
    cpuSteps.push(stage("Read and type-check Lean program",
      studio ? "The runtime returned the typed source IR: " + studio.sourceIR
        : "Awaiting the compiled Lean runtime.", cpuPresent ? "recorded" : "pending", "Lean/Wasm"));
    cpuSteps.push(stage("Pure map fusion",
      studio ? "The runtime returned its optimized IR: " + studio.optimizedIR
        : "No optimized IR has been returned.", cpuPresent ? "recorded" : "pending", "Lean/Wasm"));
    cpuSteps.push(stage("CPU task-based interpretation",
      studio ? String(studio.steps.length) + " source map(s), fused before interpretation. Intermediate values were not individually recorded."
        : "Waiting for the Lean CPU result.", cpuPresent ? "recorded" : "pending", "Lean/Wasm"));
    cpuSteps.push(stage("Actual CPU output",
      cpuPresent ? JSON.stringify(cpu) : "No CPU result yet.",
      cpuPresent ? "observed" : "pending", "Lean/Wasm"));
    if (studio && studio.gpuEligible === false) {
      gpuSteps.push(stage("GPU selector declined this program",
        studio.refusal || "Unsupported GPU source program.", "refused", "Lean selector"));
    } else {
      gpuSteps.push(stage("Lean GPU plan and input buffers",
        studio && studio.executionPlan
          ? String(studio.executionPlan.wordCount) + " words; " +
            String(studio.executionPlan.workgroups) + " workgroups per pass; " +
            String(studio.executionPlan.buffers.length) + " initial buffer descriptions."
          : "Awaiting a selected GPU plan.", studio?.executionPlan ? "planned" : "pending", "Lean plan"));
      for (const [i, pass] of (studio?.executionPlan?.passes || []).entries()) {
        const detail = "Source buffer " + pass.sourceBuffer + " → destination buffer " +
          pass.destinationBuffer + "; shader selector " + pass.shaderSelector +
          "; " + pass.kernel + " " + pass.operand + ". " +
          "Intermediate GPU data is not read back by this demo.";
        gpuSteps.push(stage("GPU pass " + (i + 1) + ": " + pass.kernel,
          detail, gpuPresent ? "submitted" : "planned", "WebGPU"));
      }
      gpuSteps.push(stage("Actual GPU readback",
        gpuPresent ? JSON.stringify(gpu) : "No GPU payload has been returned. Status: " + gpuState + ".",
        gpuPresent ? "observed" : "pending", "WebGPU"));
    }
  } else {
    cpuSteps.push(stage("Lean packet preparation",
      "Input rows are validated and serialized into a reordered, padded word packet by Lean.",
      cpuPresent ? "recorded" : "pending", "Lean/Wasm"));
    cpuSteps.push(stage("Lean sequential specification",
      "The compiled CPU path calls StaticPack.packSpec on decoded rows. The count/scan/scatter GPU model is not re-executed here.",
      cpuPresent ? "recorded" : "pending", "Lean/Wasm"));
    cpuSteps.push(stage("Actual CPU output",
      cpuPresent ? JSON.stringify(cpu) : "No CPU result yet.", cpuPresent ? "observed" : "pending", "Lean/Wasm"));
    for (const [title, detail] of [
      ["Upload prepared packet", "Host uploads the Lean-prepared binary packet into its GPU storage buffer."],
      ["Count", "64-lane WGSL workgroups write one count per input row."],
      ["Scan", "One invocation computes the exclusive offsets and terminal total; this is not yet a parallel prefix scan."],
      ["Stable scatter", "WGSL invocations copy each row into disjoint destination ranges, preserving order."],
      ["Actual GPU readback", gpuPresent ? JSON.stringify(gpu) : "No GPU payload has been returned. Status: " + gpuState + "."],
    ]) gpuSteps.push(stage(title, detail, gpuPresent ? (title === "Actual GPU readback" ? "observed" : "submitted") : "planned",
      "WebGPU"));
  }

  let difference = "CPU and GPU must both return before their output words can be compared.";
  let matches = null;
  let mismatches = [];
  if (cpu && gpu) {
    const max = Math.max(cpu.length, gpu.length);
    for (let i = 0; i < max; i++) {
      if (cpu[i] !== gpu[i]) {
        mismatches.push({index: i, cpu: i < cpu.length ? cpu[i] : null,
          gpu: i < gpu.length ? gpu[i] : null});
      }
    }
    const payloadMatches = mismatches.length === 0;
    const frameMismatch = mode === "studio" && gpuMeta &&
      (gpuMeta.fullMatches === false || gpuMeta.canariesMatch === false);
    matches = payloadMatches && !frameMismatch;
    difference = !payloadMatches
      ? String(mismatches.length) + " differing payload positions; first at word " +
        mismatches[0].index + " (CPU " + mismatches[0].cpu + "; GPU " + mismatches[0].gpu + ")."
      : "Exact payload equality: " + cpu.length + " words returned by each actual backend.";
    if (frameMismatch) {
      difference += " WARNING: The actual GPU's complete buffer frame differs from Lean's expected headers, payload or untouched tail.";
    }
  } else if (studio && studio.gpuEligible === false) {
    difference = "No GPU comparison: Lean explicitly refused this source program.";
  } else if (gpuState !== "checking" && gpuState !== "ready" && gpuState !== "initialising") {
    difference = "GPU unavailable (" + gpuState + "); CPU results remain accessible.";
  }
  return {cpuSteps, gpuSteps, matches, mismatches, difference};
}

export function mountExecutionStepper() {
  const $ = id => document.getElementById(id);
  const list = $("step-list");
  const status = $("step-status");
  const detail = $("step-observation");
  const diff = $("step-difference");
  const previous = $("step-prev");
  const next = $("step-next");
  const buttons = [...document.querySelectorAll("[data-step-target]")];
  if (!list || !status || !detail || !diff || !previous || !next || buttons.length !== 2) {
    throw new Error("Execution stepper markup is incomplete.");
  }
  const state = {mode: "pack", cpuWords: null, studio: null, gpuWords: null,
    gpuMeta: null, gpuState: "checking", target: "cpu", position: 0};
  const render = () => {
    const trace = buildExecutionTrace(state);
    const steps = state.target === "cpu" ? trace.cpuSteps : trace.gpuSteps;
    state.position = Math.min(state.position, Math.max(0, steps.length - 1));
    for (const button of buttons) {
      button.setAttribute("aria-pressed", String(button.dataset.stepTarget === state.target));
    }
    previous.disabled = state.position === 0;
    next.disabled = state.position >= steps.length - 1;
    list.replaceChildren();
    for (const [i, step] of steps.entries()) {
      const item = document.createElement("li");
      const button = document.createElement("button");
      button.type = "button";
      button.className = "step-item";
      if (i === state.position) button.classList.add("active");
      button.setAttribute("aria-current", i === state.position ? "step" : "false");
      button.textContent = (i + 1) + ". " + step.title;
      button.addEventListener("click", () => {state.position = i; render();});
      item.append(button);
      list.append(item);
    }
    const step = steps[state.position];
    status.textContent = (state.target === "cpu" ? "CPU · Lean/Wasm" : "GPU · WebGPU") +
      " — step " + (state.position + 1) + " of " + steps.length +
      " · " + step.status + " · " + step.source;
    detail.textContent = step.detail;
    diff.textContent = trace.difference;
    diff.dataset.match = trace.matches === null ? "pending" : String(trace.matches);
  };
  for (const button of buttons) {
    button.addEventListener("click", () => {
      state.target = button.dataset.stepTarget;
      state.position = 0;
      render();
    });
  }
  previous.addEventListener("click", () => {state.position--; render();});
  next.addEventListener("click", () => {state.position++; render();});
  const update = patch => {Object.assign(state, patch); render();};
  render();
  return {
    reset(mode, gpuState = "checking") {update({mode, gpuState, cpuWords: null, studio: null, gpuWords: null, gpuMeta: null, position: 0});},
    cpuPack(words) {update({mode: "pack", cpuWords: words, studio: null});},
    cpuStudio(report) {update({mode: "studio", cpuWords: report.output, studio: report});},
    gpu(words, metadata) {update({gpuWords: words, gpuMeta: metadata});},
    gpuState(value) {update({gpuState: value});},
    invalidateGpu() {update({gpuWords: null, gpuMeta: null});},
  };
}
