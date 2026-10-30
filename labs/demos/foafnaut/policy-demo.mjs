import { loadFoafTransport } from './foafnaut_transport.mjs';
import { loadLayoutPolicy } from './policy_engine.mjs';

// DOM/input/file transport. Lean owns RDF parsing, layout, the admission
// decision, geometry and SVG serialization. This page presents static frames;
// no timer or browser rendering equivalence is claimed.
class FoafNautSVGLab extends HTMLElement {
  #root = this.attachShadow({mode:'closed'});
  #call; #policy; #defaults; #svg; #ticket = 0;
  async connectedCallback() {
    this.#root.innerHTML = `<style>
      :host{display:block}*{box-sizing:border-box}header{display:flex;justify-content:space-between;align-items:end;gap:20px;margin-bottom:24px}
      h1{font-size:clamp(26px,4vw,46px);letter-spacing:-.035em;margin:6px 0}p{line-height:1.55;color:#9db6be;margin:8px 0}
      .eyebrow{color:#69e3cb;font:12px ui-monospace,monospace;letter-spacing:.16em}.chip{border:1px solid #37565b;border-radius:20px;padding:8px 13px;white-space:nowrap;font-size:12px}
      .toolbar{display:flex;gap:16px;flex-wrap:wrap;align-items:end;background:#10212c;border:1px solid #29434e;padding:16px;border-radius:12px 12px 0 0}
      label{display:grid;gap:6px;color:#acc4ca;font-size:12px}button,select{font:inherit;padding:9px 13px;border:1px solid #42616b;border-radius:6px;color:#deeeee;background:#16303c}
      button{cursor:pointer}button.primary{background:#8ae8cf;color:#072a28;border-color:#8ae8cf;font-weight:650}button:disabled{opacity:.45;cursor:default}
      .stage{min-height:180px;background:#09141d;border:1px solid #29434e;border-top:0;overflow:auto}.stage svg{display:block;width:100%;height:auto}
      .status{padding:16px;background:#10212c;border:1px solid #29434e;border-top:0;border-radius:0 0 12px 12px;color:#8ae8cf}
      .status[data-error=true]{color:#ffbb9e}.notes{display:grid;grid-template-columns:1fr 1fr;gap:28px;margin:22px 0}h2{font-size:15px;font-weight:600}
      details{border-top:1px solid #29434e;padding-top:18px}summary{cursor:pointer}textarea{display:block;width:100%;min-height:240px;margin:16px 0;background:#0e202b;color:#d7eeee;border:1px solid #35515b;padding:16px;border-radius:8px;font:13px/1.5 ui-monospace,monospace}
      code{font-size:12px;color:#a9dece}pre{white-space:pre-wrap;overflow-wrap:anywhere}a{color:#8ae8cf}@media(max-width:680px){.notes{grid-template-columns:1fr}header{display:block}.chip{display:inline-block}}
    </style>
    <header><div><span class="eyebrow">FACTOIDAL / GRAPHICS LAB</span><h1>One scene. One policy.</h1><p>FOAF data → Lean geometry → checked SVG → your renderer.</p></div><span class="chip">EXPERIMENTAL · STATIC FRAMES</span></header>
    <div class="toolbar"><label>Overlap budget<select id="overlap"><option value="300">3%</option><option value="500" selected>5%</option><option value="700">7%</option></select></label>
      <label>Target checks / second<select id="hz"><option value="12">12 Hz</option><option value="24">24 Hz</option></select></label>
      <button class="primary" id="render" disabled>Check & render</button><button id="download" disabled>Download this SVG</button></div>
    <div class="stage" id="stage"></div><div class="status" id="status" role="status" aria-live="polite">Loading the Lean WASM engines…</div>
    <div class="notes"><section><h2>The same checked scene</h2><p>This browser displays SVG produced by Lean. The native WebGPU demo can read that exact file through Factoidal’s XML and SVG parsers.</p></section>
      <section><h2>What is established</h2><p>The checker bounds summed overlap of viewport-clipped node bounding boxes. It does not prove pixel equivalence or usability. Parameter limits are an experimental human design. The cadence is recorded; this static view checks on request.</p></section></div>
    <details><summary>Edit the RDF source</summary><textarea id="rdf" aria-label="FOAF Turtle source" spellcheck="false"></textarea></details>
    <details><summary>Policy result and native command</summary><pre id="report"></pre><pre><code>deno run --allow-read --allow-write --allow-run=open --unstable-webgpu \
  labs/demos/foafnaut/run_foaf_svg.ts people.ttl checked.svg checked.ppm</code></pre></details>`;
    const q = id => this.#root.getElementById(id);
    q('render').addEventListener('click', () => this.#render());
    q('download').addEventListener('click', () => {
      if (!this.#svg) return;
      const url = URL.createObjectURL(new Blob([this.#svg], {type:'image/svg+xml'}));
      const link = document.createElement('a'); link.href = url; link.download = 'foafnaut-checked.svg'; link.click();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    });
    try {
      const [call, policy, response] = await Promise.all([
        loadFoafTransport(), loadLayoutPolicy(), fetch(new URL('./foaf/fixtures/people.ttl', import.meta.url)),
      ]);
      if (!response.ok) throw new Error(`RDF fixture HTTP ${response.status}`);
      this.#call = call; this.#policy = policy; this.#defaults = policy.defaults();
      q('rdf').value = await response.text(); q('render').disabled = false;
      await this.#render();
    } catch (error) { q('status').dataset.error = 'true'; q('status').textContent = error.message; }
  }
  async #render() {
    const q = id => this.#root.getElementById(id), ticket = ++this.#ticket;
    // Invalidate the previously displayed scene before admitting a replacement.
    q('stage').replaceChildren(); this.#svg = undefined; q('download').disabled = true;
    q('status').dataset.error = 'false'; q('status').textContent = 'Checking the candidate in Lean…';
    try {
      const policy = this.#policy.bind(this.#defaults.application, {
        overlapBps:Number(q('overlap').value), checkHz:Number(q('hz').value),
      });
      const config = JSON.stringify({application:policy.application,configuration:policy.configuration});
      const frame = this.#call('foafnaut_init_policy', ['string','number','number','string'], [q('rdf').value,1000,700,config]);
      const checked = this.#call('foafnaut_export_svg', ['string','string'], [frame.model,config]);
      if (!checked.checked) throw new Error('Lean did not return a checked scene');
      if (ticket !== this.#ticket || !this.isConnected) return;
      const documentSVG = new DOMParser().parseFromString(checked.svg, 'image/svg+xml');
      if (documentSVG.querySelector('parsererror')) throw new Error('Browser refused the generated SVG');
      q('stage').replaceChildren(document.importNode(documentSVG.documentElement,true));
      this.#svg = checked.svg; q('download').disabled = false;
      q('status').textContent = `Accepted by Lean · ${checked.layout.nodes.length} nodes · ${checked.layout.thresholdBasisPoints} basis points · static frame`;
      q('report').textContent = JSON.stringify(checked.layout,null,2);
    } catch (error) {
      q('status').dataset.error = 'true'; q('status').textContent = error.message;
      q('report').textContent = error.report ? JSON.stringify(error.report,null,2) : '';
    }
  }
}
customElements.define('foafnaut-svg-lab', FoafNautSVGLab);
