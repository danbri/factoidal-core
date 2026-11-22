const input = document.querySelector("#book");
const sample = document.querySelector("#sample");
const status = document.querySelector("#status");
const reader = document.querySelector("#reader");
const maxBookBytes = 8 * 1024 * 1024;
let worker;
let frameTicket = 0;
let loading = false;

const readerHead = `<!doctype html>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src data:; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'">
<style>
body { margin: 2rem auto !important; max-width: 42rem !important; padding: 0 1.25rem; color: #19312f;
  background: #fffef9; font: 1.1rem/1.65 Georgia, serif; overflow-wrap: anywhere; }
a { color: #145e53; }
pre { background: #eff3eb; padding: .7rem; }
nav { border-block: 1px solid #cad7ce; padding-block: .35rem; }
</style>`;

function showChapter(engine, source, anchor, chapter) {
  const ticket = ++frameTicket;
  reader.addEventListener("load", () => {
    if (engine !== worker || ticket !== frameTicket) return;
    const doc = reader.contentDocument;
    if (!doc) {
      loading = false;
      status.textContent = "Could not display this chapter.";
      return;
    }
    reader.hidden = false;
    doc.getElementById(anchor)?.scrollIntoView();
    doc.addEventListener("click", event => {
      const link = event.target.closest?.("a");
      if (!link?.hasAttribute("href")) return;
      event.preventDefault();
      if (loading) return;
      const href = link.getAttribute("href");
      const match = /^(?:\?epubChapter=([1-9]\d{0,2}))?(?:#(.*))?$/.exec(href);
      if (!match || (!match[1] && match[2] === undefined)) return;
      const [, number, target] = match;
      const next = number ? Number(number) - 1 : chapter;
      if (next === chapter) {
        if (target) doc.getElementById(target)?.scrollIntoView();
        else doc.defaultView.scrollTo(0, 0);
      } else {
        loading = true;
        status.textContent = "Loading chapter…";
        engine.postMessage({chapter: next, anchor: target ?? ""});
      }
    });
    loading = false;
    status.textContent = "";
  }, {once: true});
  reader.srcdoc = source.replace(/^<!doctype html>/i, readerHead);
}

function openBook(file) {
  worker?.terminate();
  worker = undefined;
  frameTicket++;
  reader.hidden = true;
  loading = false;
  if (file.size > maxBookBytes) {
    status.textContent = "This EPUB exceeds the 8 MiB file limit.";
    return;
  }
  loading = true;
  status.textContent = "Opening the EPUB in Lean…";
  const engine = new Worker(new URL("./worker.mjs", import.meta.url), {type: "module"});
  worker = engine;
  engine.onmessage = ({data}) => {
    if (engine !== worker) return;
    if (data.error) {
      loading = false;
      status.textContent = data.error;
      return;
    }
    showChapter(engine, data.source, data.anchor, data.chapter);
  };
  engine.onerror = () => {
    if (engine !== worker) return;
    loading = false;
    status.textContent = "Could not start the EPUB reader.";
  };
  engine.postMessage({file, chapter: 0, anchor: ""});
}

input.addEventListener("change", () => {
  if (input.files[0]) openBook(input.files[0]);
  input.value = "";
});
sample.addEventListener("click", async () => {
  sample.disabled = true;
  const current = frameTicket;
  try {
    const response = await fetch(new URL("./sample.epub", import.meta.url));
    if (!response.ok) throw new Error("Sample missing");
    const book = await response.blob();
    if (current === frameTicket) openBook(book);
  } catch {
    if (current === frameTicket) status.textContent = "Could not load the bundled sample.";
  } finally {
    sample.disabled = false;
  }
});
