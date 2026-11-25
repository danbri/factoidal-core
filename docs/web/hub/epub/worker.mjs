const encoder = new TextEncoder();
let archive;
let runtime;

async function loadRuntime() {
  try {
    const {default: createModule} = await import("../html-webgpu/runtime/web-render.mjs");
    return await createModule();
  } catch {
    throw new Error("The Hub’s Lean EPUB runtime is unavailable.");
  }
}

function chapterFrom(module, archive, chapter) {
  const request = JSON.stringify({op: "epubReader", epubChapter: chapter});
  // Emscripten copies string arguments onto its stack. An EPUB can be larger.
  const input = module._malloc(archive.length + 1);
  if (!input) throw new Error("Could not allocate memory for this EPUB.");
  try {
    module.HEAPU8.set(archive, input);
    module.HEAPU8[input + archive.length] = 0;
    const result = module.ccall("web_document_call", "number",
      ["number", "string", "number", "number"], [input, request, 1, 1]);
    if (!result) throw new Error("The EPUB reader returned no chapter.");
    try {
      const answer = JSON.parse(module.UTF8ToString(result));
      if (answer.error) throw new Error(answer.error);
      if (typeof answer.source !== "string") throw new Error("The Hub runtime has no EPUB reader.");
      return answer.source;
    } finally {
      module.ccall("web_render_free", null, ["number"], [result]);
    }
  } finally {
    module._free(input);
  }
}

self.onmessage = async ({data: {file, chapter, anchor}}) => {
  try {
    if (file) {
      if (file.size > 8 * 1024 * 1024) throw new Error("This EPUB exceeds the 8 MiB file limit.");
      const bytes = new Uint8Array(await file.arrayBuffer());
      let binary = "";
      for (let i = 0; i < bytes.length; i += 32768) {
        binary += String.fromCharCode(...bytes.subarray(i, i + 32768));
      }
      archive = encoder.encode(btoa(binary));
    }
    if (!archive) throw new Error("Choose an EPUB first.");
    runtime ??= loadRuntime();
    const source = chapterFrom(await runtime, archive, chapter);
    self.postMessage({source, chapter, anchor});
  } catch (error) {
    self.postMessage({error: error.message ?? "Could not read this EPUB."});
  }
};
