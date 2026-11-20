// UI for a real Lean/Wasm BGP. Formatting only; no JavaScript SPARQL join.
import {QUERY, PATTERN_KNOWS, PATTERN_ATLAS, SIZES} from "./bgp-fixtures.mjs";

export function mountBgpStudio({onPack}) {
  const $ = id => document.getElementById(id);
  const pane = $("bgp-studio");
  const scale = $("bgp-size");
  const button = $("bgp-run");
  const pack = $("bgp-pack");
  const status = $("bgp-status");
  const preview = $("bgp-sample");
  const left = $("bgp-left");
  const right = $("bgp-right");
  const answers = $("bgp-answers");
  const prev = $("bgp-prev");
  const next = $("bgp-next");
  const pageStatus = $("bgp-page-status");
  const ledger = $("bgp-ledger");
  const idBridge = $("bgp-id-bridge");
  const sizes = $("bgp-stats");
  const context = $("bgp-context");
  $("bgp-query").textContent = QUERY;
  $("bgp-pattern-one").textContent = PATTERN_KNOWS;
  $("bgp-pattern-two").textContent = PATTERN_ATLAS;

  const state = {worker: null, id: 0, result: null, page: 0};
  const PAGE_SIZE = 20;
  let messages = [];
  const log = message => {
    messages.push(message);
    ledger.textContent = messages.map((s, i) => String(i + 1) + ". " + s).join("\n");
  };
  const renderTable = (target, rows, columns, start, total) => {
    const table = document.createElement("table");
    const caption = document.createElement("caption");
    caption.textContent = "Lean-returned bindings " + (start + 1) + "–" + (start + rows.length) + " of " + total;
    table.append(caption);
    const head = document.createElement("thead"), tr = document.createElement("tr");
    for (const column of columns) {
      const th = document.createElement("th");
      th.scope = "col"; th.textContent = column; tr.append(th);
    }
    head.append(tr);
    table.append(head);
    const body = document.createElement("tbody");
    for (const row of rows) {
      const item = document.createElement("tr");
      for (const column of columns) {
        const cell = document.createElement("td");
        cell.textContent = row[column] == null ? "—" : String(row[column]);
        item.append(cell);
      }
      body.append(item);
    }
    table.append(body);
    target.replaceChildren(table);
  };

  function showPage() {
    const all = state.result?.bindings;
    if (!Array.isArray(all)) return;
    const start = state.page * PAGE_SIZE;
    renderTable(answers, all.slice(start, start + PAGE_SIZE),
      ["ordinal", "person", "colleague", "personId", "colleagueId"],
      start, all.length);
    pageStatus.textContent = "Page " + (state.page + 1) + " of " +
      Math.max(1, Math.ceil(all.length / PAGE_SIZE)) +
      " · " + all.length + " complete Lean bindings";
    prev.disabled = state.page === 0;
    next.disabled = start + PAGE_SIZE >= all.length;
  }

  const reset = () => {
    state.id++;
    state.result = null;
    state.page = 0;
    prev.disabled = true;
    next.disabled = true;
    pageStatus.textContent = "No bindings yet";
    pack.disabled = true;
    button.disabled = false;
    messages = [];
    ledger.textContent = "No Lean query has run yet.";
    preview.textContent = "Awaiting generated RDF source data…";
    sizes.textContent = "The input dataset, selected patterns and intermediate binding sizes appear after execution.";
    left.textContent = "Awaiting actual Lean bindings…";
    right.textContent = "Awaiting actual Lean bindings…";
    answers.replaceChildren();
    idBridge.textContent = "The GPU does not run SPARQL; after a Lean query, an optional word-packing bridge maps fixture person IRIs injectively to u32 IDs.";
    context.textContent = "BGP evaluation: Lean/Wasm CPU. The ID packing demo uses Lean/Wasm CPU and WebGPU, and is a different computation.";
  };

  function finish(result) {
    if (result?.schemaVersion !== 1 || !Array.isArray(result.bindings) ||
        result.bindings.length !== result.bgp?.count || result.bindings.length > 512) {
      throw new Error("Incompatible or incomplete Lean BGP response.");
    }
    state.result = result;
    status.textContent = "Lean/Wasm completed " + result.input.tripleCount.toLocaleString() +
      " triples; " + result.bgp.count + " BGP solution mappings.";
    sizes.textContent = result.input.blocks.map(b => b.name + ": " + b.triples.toLocaleString() + " triples").join(" · ") +
      " · " + result.scans.knows.count + " knows bindings · " +
      result.scans.atlas.count + " Atlas bindings · " + result.bgp.count + " BGP solutions.";
    preview.textContent = result.input.sample.join("\n");
    left.textContent = result.scans.knows.preview.map(r => r.person + " → " + r.colleague).join("\n");
    right.textContent = result.scans.atlas.preview.map(r => r.colleague).join("\n");
    state.page = 0;
    showPage();
    idBridge.textContent = "Fixture-only bijective term mapping: " + result.pack.mapping +
      ". These are NOT SBM11 64-bit dictionary IDs. " +
      result.pack.sourcePairs + " binding pairs become " + result.pack.words +
      " u32 words in " + result.pack.packedRows.length +
      " packing rows (at most 128 rows / 1,024 words).";
    context.textContent = "Execution: " + result.engine + " · " +
      result.execution + ". Query time includes storage/parsing. " +
      result.timing.totalMs.toFixed(1) + " ms worker wall time. " +
      "GPU SPARQL: unavailable; WebGPU packing: separate, optional.";
    pack.disabled = false;
    button.disabled = false;
    log("Actual Lean BGP result returned. No GPU query was run.");
  }

  function start() {
    const n = Number(scale.value);
    if (!SIZES.includes(n)) {status.textContent = "Select an admitted dataset size."; return;}
    const id = ++state.id;
    messages = [];
    state.result = null;
    state.page = 0;
    prev.disabled = true;
    next.disabled = true;
    pageStatus.textContent = "Running…";
    answers.replaceChildren();
    pack.disabled = true;
    button.disabled = true;
    status.textContent = "Preparing " + n + " people (" + (n * 4) + " generated RDF triples)…";
    if (!state.worker) {
      try {
        state.worker = new Worker(new URL("./bgp-worker.mjs", import.meta.url), {type: "module"});
      } catch (error) {
        status.textContent = "Cannot start SPARQL worker: " + (error?.message || String(error));
        button.disabled = false;
        return;
      }
      state.worker.addEventListener("message", ({data}) => {
        if (data.id !== state.id) return;
        if (data.type === "bgp-phase") {
          status.textContent = data.detail;
          log(data.detail);
        } else if (data.type === "bgp-result") {
          finish(data.result);
        } else if (data.type === "bgp-error") {
          status.textContent = "Lean query failed: " + data.message;
          log("Failed: " + data.message);
          button.disabled = false;
        }
      });
      state.worker.addEventListener("error", error => {
        status.textContent = "SPARQL worker failed: " + (error.message || "Module load error.");
        button.disabled = false;
        pack.disabled = true;
        state.worker?.terminate();
        state.worker = null;
      });
    }
    state.worker.postMessage({id, people: n});
  }

  const open = $("bgp-open");
  open.addEventListener("click", () => {
    pane.scrollIntoView({block: "start", behavior: "auto"});
    button.focus({preventScroll: true});
  });
  prev.addEventListener("click", () => {
    if (state.result && state.page > 0) { state.page--; showPage(); }
  });
  next.addEventListener("click", () => {
    if (state.result && (state.page + 1) * PAGE_SIZE < state.result.bindings.length) {
      state.page++; showPage();
    }
  });
  button.addEventListener("click", start);
  scale.addEventListener("change", () => {
    reset();
    status.textContent = "Dataset size changed. Run the Lean BGP to obtain new bindings.";
  });
  pack.addEventListener("click", () => {
    if (!state.result) return;
    const selected = state.result;
    pack.disabled = true;
    try {
      onPack({rows: selected.pack.packedRows, querySize: selected.input.people,
        bindings: selected.bgp.count});
      pack.disabled = false;
      log("Submitted " + selected.pack.words + " fixture-mapped u32 words to the *separate* Paralliverse stable-packing CPU/GPU experiment.");
    } catch (error) {
      pack.disabled = false;
      status.textContent = "Packing handoff failed: " + error.message;
    }
  });
  reset();
  return {start, reset, pane};
}
