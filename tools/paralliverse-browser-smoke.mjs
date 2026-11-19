import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { once } from "node:events";
import { constants } from "node:fs";
import { access, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { delimiter, extname, join, resolve, sep } from "node:path";
import { setTimeout as sleep } from "node:timers/promises";

const [siteDir, evidenceDir, sourceCommit] = process.argv.slice(2);
assert(siteDir && evidenceDir && /^[0-9a-f]{40}$/.test(sourceCommit ?? ""),
  "Usage: paralliverse-browser-smoke.mjs SITE_DIR EVIDENCE_DIR SOURCE_COMMIT");

const prefix = "/factoidal/";
const route = "web/hub/paralliverse/";
const assetDir = join(siteDir, "web/hub/assets/l4/paralliverse");
const deadlineMs = 30_000;
const contentTypes = {
  ".html": "text/html; charset=utf-8", ".css": "text/css", ".mjs": "text/javascript",
  ".js": "text/javascript", ".json": "application/json", ".wasm": "application/wasm",
};
const sha256 = bytes => createHash("sha256").update(bytes).digest("hex");
const report = {
  format: "paralliverse-browser-smoke-v1", status: "fail", sourceCommit,
  cases: [], pageErrors: [], console: [], networkFailures: [],
};

async function findChrome() {
  if (process.env.CHROME_BIN) return process.env.CHROME_BIN;
  for (const name of ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"]) {
    for (const dir of (process.env.PATH ?? "").split(delimiter).filter(Boolean)) {
      const candidate = join(dir, name);
      if (await access(candidate, constants.X_OK).then(() => true, () => false)) return candidate;
    }
  }
  throw new Error("Chrome or Chromium is required. Set CHROME_BIN to its executable.");
}

function serveSite(root) {
  return createServer(async (request, response) => {
    try {
      const pathname = decodeURIComponent(new URL(request.url, "http://127.0.0.1").pathname);
      const suffix = pathname.endsWith("/") ? "index.html" : "";
      const path = resolve(root, pathname.slice(prefix.length), suffix);
      if (!pathname.startsWith(prefix) || !path.startsWith(root + sep)) {
        response.writeHead(404).end();
        return;
      }
      const bytes = await readFile(path);
      response.writeHead(200, {
        "content-type": contentTypes[extname(path)] ?? "application/octet-stream",
        "cache-control": "no-store",
      }).end(bytes);
    } catch (error) {
      const missing = error.code === "ENOENT" || error.code === "EISDIR";
      response.writeHead(missing ? 404 : 500).end();
    }
  });
}

async function connectDevTools(url, onEvent) {
  const socket = new WebSocket(url);
  try {
    await once(socket, "open", {signal: AbortSignal.timeout(5_000)});
  } catch (error) {
    socket.close();
    throw error;
  }
  let nextId = 0;
  const pending = new Map();
  socket.addEventListener("message", ({data}) => {
    const message = JSON.parse(data);
    if (!message.id) {
      onEvent(message);
      return;
    }
    const finish = pending.get(message.id);
    if (finish) finish(message);
  });
  return {
    close: () => socket.close(),
    call(method, params = {}, sessionId, timeoutMs = 5_000) {
      return new Promise((resolveCall, rejectCall) => {
        const id = ++nextId;
        const timer = setTimeout(() => {
          pending.delete(id);
          rejectCall(new Error(`Timed out waiting for CDP ${method}.`));
        }, timeoutMs);
        pending.set(id, message => {
          clearTimeout(timer);
          pending.delete(id);
          if (message.error) rejectCall(new Error(`${method}: ${message.error.message}`));
          else resolveCall(message.result);
        });
        socket.send(JSON.stringify({id, method, params, sessionId}));
      });
    },
  };
}

function pageState() {
  const get = id => document.getElementById(id);
  const text = id => get(id)?.textContent ?? "";
  const runtime = Object.fromEntries(Array.from(document.querySelectorAll("#runtime-data dt"),
    term => [term.textContent, term.nextElementSibling.textContent]));
  return {
    title: document.title, example: get("example")?.value, input: get("source")?.value,
    inputStatus: text("input-status"), cpuStatus: text("cpu-status"), gpuStatus: text("gpu-status"),
    cpu: text("cpu-output"), gpu: text("gpu-output"), comparison: text("comparison-status"),
    match: get("comparison-status")?.dataset.match,
    runtimeCommit: document.querySelector("#runtime-data dd a")?.href.split("/").at(-1),
    runtime,
  };
}

async function observeCase(evaluate, name, example, expected) {
  const deadline = Date.now() + deadlineMs;
  let state;
  while (Date.now() < deadline) {
    state = await evaluate(`(${pageState.toString()})()`, Math.min(5_000, deadline - Date.now()));
    if (state.match !== undefined) break;
    if (state.inputStatus.startsWith("CPU runtime unavailable.")) break;
    await sleep(100);
  }
  report.cases.push({name, expected, ...state});
  assert.equal(state?.example, example, name);
  assert.equal(state?.match, "true", `${name}: ${state?.inputStatus} ${state?.gpuStatus} ${state?.comparison}`);
  assert.equal(state.comparison, "Exact CPU/GPU byte match.", name);
  assert.equal(state.cpu, expected, `${name} CPU output`);
  assert.equal(state.gpu, expected, `${name} GPU output`);
  assert.match(state.cpuStatus, / CPU call$/, name);
  assert.match(state.gpuStatus, / GPU end to end\./, name);
  return state;
}

let server, chrome, chromeClosed, profile, devtools, page;
let chromeLog = "";
let pageLoaded = false;
const requests = new Map();
async function screenshot(name) {
  const {data} = await page("Page.captureScreenshot", {format: "png", captureBeyondViewport: true});
  await writeFile(join(evidenceDir, name), Buffer.from(data, "base64"));
}

await mkdir(evidenceDir, {recursive: true});
try {
  const manifestBytes = await readFile(join(assetDir, "manifest.json"));
  const manifest = JSON.parse(manifestBytes);
  assert.match(manifest.sourceCommit ?? "", /^[0-9a-f]{40}$/);
  if (process.env.REQUIRE_EXACT_PARALLIVERSE_RUNTIME === "1") {
    assert.equal(manifest.sourceCommit, sourceCommit, "Exact freshly built Studio source");
  }
  report.manifest = {sourceCommit: manifest.sourceCommit, sha256: sha256(manifestBytes), files: manifest.files};
  for (const name of ["paralliverse.mjs", "paralliverse.wasm"]) {
    const bytes = await readFile(join(assetDir, name));
    assert.equal(bytes.length, manifest.files?.[name]?.bytes, `${name} size`);
    assert.equal(sha256(bytes), manifest.files?.[name]?.sha256, `${name} SHA-256`);
  }

  profile = await mkdtemp(join(tmpdir(), "paralliverse-chrome-"));
  server = serveSite(resolve(siteDir));
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  report.url = `http://127.0.0.1:${server.address().port}${prefix}${route}`;
  const chromeBin = await findChrome();
  // Chromium's WebGPU tests explicitly select the SwiftShader adapter for software execution.
  const flags = [
    "--headless=new", "--no-sandbox", "--no-first-run", "--disable-background-networking",
    "--remote-debugging-address=127.0.0.1", "--remote-debugging-port=0",
    "--enable-unsafe-webgpu", "--enable-unsafe-swiftshader", "--use-webgpu-adapter=swiftshader",
    "--use-angle=swiftshader", "--use-vulkan=swiftshader", "--disable-vulkan-surface",
  ];
  report.launch = {executable: chromeBin, flags};
  chrome = spawn(chromeBin, [...flags, `--user-data-dir=${profile}`, "about:blank"],
    {stdio: ["ignore", "pipe", "pipe"]});
  chromeClosed = new Promise(resolveClose => {
    chrome.once("exit", resolveClose);
    chrome.once("error", error => {
      chromeLog += `${error.message}\n`;
      resolveClose();
    });
  });
  for (const stream of [chrome.stdout, chrome.stderr]) {
    stream.on("data", bytes => { chromeLog = (chromeLog + bytes).slice(-65_536); });
  }

  let debuggerUrl;
  const startDeadline = Date.now() + deadlineMs;
  while (Date.now() < startDeadline && chrome.exitCode === null && chrome.pid) {
    const [port, path] = (await readFile(join(profile, "DevToolsActivePort"), "utf8")
      .catch(() => "")).trim().split("\n");
    if (/^\d+$/.test(port) && path?.startsWith("/devtools/")) {
      debuggerUrl = `ws://127.0.0.1:${port}${path}`;
      break;
    }
    await sleep(100);
  }
  assert(debuggerUrl, "Chrome did not open its DevTools connection within 30 seconds.");

  devtools = await connectDevTools(debuggerUrl, ({method, params, sessionId}) => {
    const key = `${sessionId}/${params?.requestId}`;
    switch (method) {
      case "Target.attachedToTarget":
        if (params.waitingForDebugger) {
          const workerId = params.sessionId;
          Promise.all([
            devtools.call("Runtime.enable", {}, workerId),
            devtools.call("Network.enable", {}, workerId),
          ]).catch(error => report.pageErrors.push(error.message))
            .finally(() => devtools.call("Runtime.runIfWaitingForDebugger", {}, workerId))
            .catch(error => report.pageErrors.push(error.message));
        }
        break;
      case "Runtime.exceptionThrown":
        report.pageErrors.push(params.exceptionDetails.exception?.description ?? params.exceptionDetails.text);
        break;
      case "Runtime.consoleAPICalled":
        report.console.push({level: params.type, source: sessionId, text: params.args.map(
          arg => arg.value ?? arg.description ?? arg.type)});
        break;
      case "Log.entryAdded":
        report.console.push({level: params.entry.level, source: params.entry.source, text: params.entry.text});
        break;
      case "Page.loadEventFired":
        pageLoaded = true;
        break;
      case "Network.requestWillBeSent":
        requests.set(key, params.request.url);
        break;
      case "Network.responseReceived":
        if (params.response.status >= 400) {
          report.networkFailures.push({url: params.response.url, status: params.response.status});
        }
        break;
      case "Network.loadingFailed":
        report.networkFailures.push({url: requests.get(key), error: params.errorText, canceled: params.canceled});
        requests.delete(key);
        break;
      case "Network.loadingFinished":
        requests.delete(key);
        break;
    }
  });
  report.browser = await devtools.call("Browser.getVersion");
  const {targetId} = await devtools.call("Target.createTarget", {url: "about:blank"});
  const {sessionId} = await devtools.call("Target.attachToTarget", {targetId, flatten: true});
  page = (method, params, timeoutMs) => devtools.call(method, params, sessionId, timeoutMs);
  await Promise.all(["Page", "Runtime", "Log", "Network"].map(domain => page(`${domain}.enable`)));
  await page("Target.setAutoAttach", {autoAttach: true, waitForDebuggerOnStart: true, flatten: true});
  await page("Emulation.setDeviceMetricsOverride", {width: 1440, height: 1250, deviceScaleFactor: 1, mobile: false});
  pageLoaded = false;
  const navigationDeadline = Date.now() + deadlineMs;
  const navigation = await page("Page.navigate", {url: report.url}, deadlineMs);
  assert(!navigation.errorText, navigation.errorText);
  while (!pageLoaded && Date.now() < navigationDeadline) await sleep(100);
  assert(pageLoaded, "The Hub page did not finish loading within 30 seconds.");

  const evaluate = async (expression, timeoutMs) => {
    const {result, exceptionDetails} = await page("Runtime.evaluate", {expression, returnByValue: true}, timeoutMs);
    assert(!exceptionDetails, exceptionDetails?.exception?.description ?? exceptionDetails?.text);
    return result.value;
  };
  const mixed = await observeCase(evaluate, "mixed", "mixed", "[8, 3, 8, 0, 4294967295, 3]");
  assert.equal(mixed.runtimeCommit, manifest.sourceCommit, "Page source provenance");
  assert(mixed.runtime["GPU adapter"], "The page did not report the selected WebGPU adapter.");
  assert(mixed.runtime["Fallback adapter"], "The page did not report the adapter fallback status.");
  for (const stage of ["Count", "Scan", "Scatter"]) {
    assert.match(mixed.runtime[`${stage} source SHA-256`] ?? "", /^[0-9a-f]{64}$/);
  }
  report.runtime = mixed.runtime;
  const {gpu: browserGpu} = await devtools.call("SystemInfo.getInfo");
  report.browserGraphics = {
    devices: browserGpu.devices, webgpuStatus: browserGpu.featureStatus?.webgpu,
    renderer: browserGpu.auxAttributes?.glRenderer,
  };
  const edit = (id, value, event) => evaluate(`(() => {
    const control = document.getElementById(${JSON.stringify(id)});
    control.value = ${JSON.stringify(value)};
    control.dispatchEvent(new Event(${JSON.stringify(event)}, {bubbles: true}));
  })()`);
  const changed = "[[4294967295], [0, 3, 8], [], [], [256, 256]]";
  const changedOutput = "[4294967295, 0, 3, 8, 256, 256]";
  await edit("source", changed, "input");
  await observeCase(evaluate, "changed", "custom", changedOutput);
  await edit("example", "none", "change");
  await observeCase(evaluate, "zero", "none", "[]");
  await edit("source", changed, "input");
  await observeCase(evaluate, "changed-after-zero", "custom", changedOutput);

  // The visible Run button submits the current editor value even without an input event.
  const submitted = "[[17], [], [23, 17]]";
  await evaluate(`(() => {
    const run = document.querySelector("#run");
    if (!run || run.disabled || !run.textContent.includes("Run CPU + GPU")) {
      throw new Error("The visible Run CPU + GPU control is unavailable.");
    }
    document.querySelector("#source").value = ${JSON.stringify(submitted)};
    run.click();
  })()`);
  await observeCase(evaluate, "manual-run", "custom", "[17, 23, 17]");
  await edit("source", changed, "input");
  await observeCase(evaluate, "automatic-after-manual", "custom", changedOutput);

  const studioAvailable = await evaluate('Boolean(document.querySelector("#mode-studio") && !document.querySelector("#mode-studio").disabled)');
  if (process.env.REQUIRE_PARALLIVERSE_STUDIO === "1") assert(studioAvailable, "The actual Studio runtime must be enabled");
  if (studioAvailable) {
    async function studioState() {
      return evaluate(`(() => ({...(${pageState.toString()})(),
        mode:document.querySelector('#workspace').dataset.mode,
        program:document.querySelector('#program').value,
        sourceIR:document.querySelector('#source-ir').textContent,
        optimizedIR:document.querySelector('#optimized-ir').textContent,
        frame:document.querySelector('#frame-status').textContent,
        cells:document.querySelectorAll('#word-grid .word-cell').length,
        copyEnabled:!document.querySelector('#copy-lean').disabled,
        plan:document.querySelector('#gpu-plan').textContent}))()`);
    }
    async function studioCase(name, expected, cells) {
      const deadline = Date.now() + deadlineMs;
      let state;
      do {
        state = await studioState();
        if (state.match !== undefined || state.inputStatus.startsWith("CPU runtime unavailable.")) break;
        await sleep(100);
      } while (Date.now() < deadline);
      report.cases.push({name, expected, ...state});
      assert.equal(state.mode, "studio", name);
      assert.equal(state.match, "true", `${name}: ${state.inputStatus} ${state.gpuStatus}`);
      assert.equal(state.cpu, expected, `${name}: CPU result`);
      assert.equal(state.gpu, expected, `${name}: actual GPU result`);
      assert.equal(state.frame, "Header + tail match", `${name}: complete buffer frame`);
      assert.equal(state.cells, cells, `${name}: returned-word visualization`);
      assert.equal(state.copyEnabled, true, `${name}: Lean source export`);
      assert.match(state.cpuStatus, /Lean parse \+ CPU evaluation$/, name);
      return state;
    }
    await evaluate('document.querySelector("[data-preset=wrap]").click()');
    const wrap = await studioCase("studio-wrap", "[1, 4, 7, 0, 2147483646, 2147483649, 4294967291, 4294967294]", 8);
    assert.match(wrap.sourceIR, /\.seq \(\.map/);
    assert.match(wrap.optimizedIR, /^\(\.map \(\.seq/);
    const plan = JSON.parse(wrap.plan);
    assert.deepEqual(plan.passes.map(p => p.shaderSelector), [4, 3]);
    assert.equal(plan.passes[0].destinationBuffer, plan.passes[1].sourceBuffer, "Direct GPU intermediate binding");
    await evaluate('document.querySelector("[data-preset=empty]").click()');
    await studioCase("studio-empty", "[]", 0);
    await evaluate(`(() => {
      const live=document.querySelector('#live'); live.checked=false; live.dispatchEvent(new Event('change'));
      document.querySelector('#program').value='map add 1';
      document.querySelector('#source').value='[4294967295,0,5,5]';
      document.querySelector('#program').dispatchEvent(new Event('input',{bubbles:true}));
    })()`);
    assert.equal((await studioState()).cpu, "—", "Paused edits clear stale results");
    await evaluate(`document.querySelector('#program').dispatchEvent(new KeyboardEvent('keydown',
      {key:'Enter',ctrlKey:true,bubbles:true}))`);
    await studioCase("studio-keyboard-paused", "[0, 1, 6, 6]", 4);
    await evaluate(`(() => {
      document.querySelector('#program').value=${JSON.stringify("map multiply 3\nmap add 1\nmap multiply 2")};
      document.querySelector('#source').value='[2,2]'; document.querySelector('#run').click();
    })()`);
    let refused;
    const refusalDeadline = Date.now() + deadlineMs;
    do {
      refused = await studioState();
      if (refused.cpu === "[14, 14]") break;
      await sleep(100);
    } while (Date.now() < refusalDeadline);
    assert.equal(refused.cpu, "[14, 14]", "CPU-only accepted program");
    assert.equal(refused.gpu, "—", "GPU refusal produces no fabricated result");
    assert.equal(refused.match, undefined, "Refusal is not a byte-match success");
    assert.match(refused.gpuStatus, /supports one or two source maps/);
    report.cases.push({name: "studio-cpu-only", ...refused});
    await edit("program", "map add 01", "input");
    await evaluate('document.querySelector("#run").click()');
    const invalidDeadline = Date.now() + deadlineMs;
    let invalid;
    do {
      invalid = await studioState();
      if (invalid.inputStatus.startsWith("Invalid input.")) break;
      await sleep(100);
    } while (Date.now() < invalidDeadline);
    assert.match(invalid.inputStatus, /^Invalid input\./, "Lean syntax diagnostic");
    assert.equal(invalid.cpu, "—", "Invalid input clears old CPU result");
    assert.equal(invalid.match, undefined, "Invalid input clears old success");
    report.cases.push({name: "studio-malformed", ...invalid});
    await evaluate('document.querySelector("[data-preset=wrap]").click()');
    await studioCase("studio-recovery", "[1, 4, 7, 0, 2147483646, 2147483649, 4294967291, 4294967294]", 8);
    if (await evaluate('Boolean(document.querySelector("#signal-play"))')) {
      await evaluate('document.querySelector("#signal-play").click()');
      const animationDeadline = Date.now() + deadlineMs;
      let frames;
      do {
        frames = await evaluate(`({completed:Number(document.querySelector('#signal-phase').dataset.completed),
          status:document.querySelector('#signal-status').textContent,
          target:document.querySelector('#visual-surface').dataset.target,
          program:document.querySelector('#program').value,
          stopped:document.querySelector('#signal-stop').disabled})`);
        if (frames.completed === 32 || frames.status.startsWith("Playback stopped")) break;
        await sleep(100);
      } while (Date.now() < animationDeadline);
      assert.equal(frames.completed, 32, `Bounded signal playback: ${frames.status}`);
      assert.equal(frames.target, "gpu", "Signal view uses the actual GPU readback");
      assert.equal(frames.program, "map multiply 257\nmap add 248", "Only acknowledged phases advance");
      assert.equal(frames.stopped, true, "Playback ends after its finite frame budget");
      const animated = await studioState();
      assert.equal(animated.match, "true", "Last animated CPU/GPU comparison");
      assert.equal(animated.gpu, animated.cpu, "Last animated physical result");
      assert.equal(animated.cells, 64, "Animation renders the returned GPU words");
      assert.equal(animated.frame, "Header + tail match", "Animation preserves full buffer frames");
      report.cases.push({name: "studio-signal-32-frames", frames, ...animated});
      await screenshot("paralliverse-studio-signal.png");
      await evaluate('document.querySelector("#signal-step").click()');
      const stepDeadline = Date.now() + deadlineMs;
      let step;
      do {
        step = await evaluate('Number(document.querySelector("#signal-phase").dataset.completed)');
        if (step === 1) break;
        await sleep(100);
      } while (Date.now() < stepDeadline);
      assert.equal(step, 1, "Single step waits for one matching GPU readback");
      await evaluate('document.querySelector("#view-cpu").click()');
      assert.equal(await evaluate('document.querySelector("#visual-surface").dataset.target'), "cpu");
      await evaluate('document.querySelector("#view-gpu").click()');
      assert.equal(await evaluate('document.querySelector("#visual-surface").dataset.target'), "gpu");
      await evaluate('document.querySelector("[data-preset=wrap]").click()');
      await studioCase("studio-after-playback", "[1, 4, 7, 0, 2147483646, 2147483649, 4294967291, 4294967294]", 8);
    }
    await evaluate(`(() => {
      Object.defineProperty(navigator,'clipboard',{configurable:true,value:{writeText:async text=>{window.__studioClipboard=text;}}});
      document.querySelector('#copy-lean').click();
    })()`);
    const copied = await evaluate('window.__studioClipboard');
    assert.match(copied, /^import L4Factoidal\.Paralliverse\.StudioProgram\n/);
    await evaluate('document.querySelector("#share").click()');
    let shared;
    const shareDeadline = Date.now() + 5000;
    do {
      shared = await evaluate('window.__studioClipboard');
      if (shared?.startsWith(report.url)) break;
      await sleep(50);
    } while (Date.now() < shareDeadline);
    assert(shared?.includes("#pv="), "Share control emits a complete experiment link");
    await screenshot("paralliverse-studio-desktop.png");
    await page("Emulation.setDeviceMetricsOverride", {width: 390, height: 844, deviceScaleFactor: 1, mobile: true});
    pageLoaded = false;
    await page("Page.navigate", {url: shared}, deadlineMs);
    const sharedLoadDeadline = Date.now() + deadlineMs;
    while (!pageLoaded && Date.now() < sharedLoadDeadline) await sleep(100);
    assert(pageLoaded, "The shared Studio page did not finish loading.");
    const restored = await studioCase("studio-shared-mobile", "[1, 4, 7, 0, 2147483646, 2147483649, 4294967291, 4294967294]", 8);
    assert.equal(restored.program, "map multiply 3\nmap add 1", "Shared source restores unchanged");
    const layout = await evaluate('({viewport:innerWidth,width:document.documentElement.scrollWidth})');
    assert(layout.width <= layout.viewport + 1, "Studio layout overflows the mobile viewport");
    await screenshot("paralliverse-studio-mobile.png");
    await page("Emulation.setDeviceMetricsOverride", {width: 1440, height: 1250, deviceScaleFactor: 1, mobile: false});
  }

  await evaluate('document.querySelector("#runtime").open = true');
  await screenshot("paralliverse.png");
  assert.deepEqual(report.pageErrors, [], "Uncaught browser or worker errors");
  assert.deepEqual(report.networkFailures.filter(failure => !failure.canceled), [], "Failed browser requests");
  report.status = "pass";
} catch (error) {
  report.error = error.stack ?? String(error);
  process.exitCode = 1;
  if (page) await screenshot("paralliverse-failure.png").catch(() => {});
} finally {
  devtools?.close();
  if (chrome?.pid && chrome.exitCode === null && chrome.signalCode === null) {
    chrome.kill();
    await Promise.race([chromeClosed, sleep(3_000)]);
    if (chrome.exitCode === null && chrome.signalCode === null) chrome.kill("SIGKILL");
  }
  server?.close();
  server?.closeAllConnections();
  await writeFile(join(evidenceDir, "chrome.log"), chromeLog);
  await writeFile(join(evidenceDir, "browser.json"), JSON.stringify(report, null, 2) + "\n");
  // Chrome's subprocesses may briefly finish writing after its main process exits.
  if (profile) await rm(profile, {recursive: true, force: true, maxRetries: 5, retryDelay: 100});
}

if (report.error) console.error(report.error);
else console.log(`Matched ${report.cases.length} cases in ${report.browser.product} on ${report.runtime["GPU adapter"]}`);
